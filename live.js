/* JomOutKL live places — nearby food & wellness from OpenStreetMap, re-queried as the visitor moves.
   No server, no API key, no cost. Data © OpenStreetMap contributors (ODbL). */
(function () {
  'use strict';
  var root = (typeof window !== 'undefined') ? window : globalThis;
  var DEFAULT_POS = { lat: 3.1466, lng: 101.7110 };
  var ENDPOINTS = [
    'https://overpass-api.de/api/interpreter',
    'https://overpass.kumi.systems/api/interpreter',
    'https://overpass.private.coffee/api/interpreter'
  ];
  var RADIUS_M = 1200, DENSE_RADIUS_M = 500, LIMIT = 300;
  var MOVE_KM = 0.5;
  var MIN_GAP_MS = 3000;
  var CACHE_TTL = 6 * 3600 * 1000, CACHE_MAX = 8, CELL = 0.005;
  var KEEP_TAGS = ['name', 'amenity', 'shop', 'leisure', 'sport', 'cuisine', 'opening_hours', 'phone',
    'contact:phone', 'contact:mobile', 'mobile', 'website', 'contact:website', 'diet:halal',
    'diet:vegetarian', 'diet:vegan', 'reservation', 'addr:street', 'addr:suburb', 'addr:city', 'addr:neighbourhood'];

  var S = {
    pos: null, usingDefault: false, qPos: null, qAt: 0, busy: false, pending: null, timer: null,
    status: 'idle', err: '', els: null, radius: RADIUS_M, food: [], well: [], updated: null
  };

  function esc(s) {
    return String(s == null ? '' : s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }
  function hav(lat1, lng1, lat2, lng2) {
    var R = 6371, dLat = (lat2 - lat1) * Math.PI / 180, dLng = (lng2 - lng1) * Math.PI / 180;
    var a = Math.sin(dLat / 2) * Math.sin(dLat / 2) + Math.cos(lat1 * Math.PI / 180) * Math.cos(lat2 * Math.PI / 180) * Math.sin(dLng / 2) * Math.sin(dLng / 2);
    return R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  }
  function fmtDist(km) { return km < 1 ? Math.max(10, Math.round(km * 100) * 10) + ' m' : km.toFixed(1) + ' km'; }
  function fmtTime(min) {
    var h = Math.floor(min / 60) % 24, m = min % 60, ap = h >= 12 ? 'PM' : 'AM', h12 = h % 12 === 0 ? 12 : h % 12;
    return h12 + ':' + (m < 10 ? '0' : '') + m + ' ' + ap;
  }

  var DAYIDX = { Mo: 0, Tu: 1, We: 2, Th: 3, Fr: 4, Sa: 5, Su: 6 };
  function expandDays(spec) {
    var out = [], parts = spec.split(','), i, m, a, b, d, g;
    for (i = 0; i < parts.length; i++) {
      m = parts[i].trim().match(/^(Mo|Tu|We|Th|Fr|Sa|Su)(?:-(Mo|Tu|We|Th|Fr|Sa|Su))?$/);
      if (!m) return null;
      a = DAYIDX[m[1]]; b = m[2] ? DAYIDX[m[2]] : a; d = a;
      for (g = 0; g < 8; g++) { out[d] = true; if (d === b) break; d = (d + 1) % 7; }
    }
    return out;
  }
  function parseRanges(spec) {
    var parts = spec.split(','), res = [], i, m, o, c;
    for (i = 0; i < parts.length; i++) {
      m = parts[i].trim().match(/^(\d{1,2}):(\d{2})\s*-\s*(\d{1,2}):(\d{2})$/);
      if (!m) return null;
      if (+m[1] > 24 || +m[3] > 24 || +m[2] > 59 || +m[4] > 59) return null;
      o = +m[1] * 60 + (+m[2]); c = +m[3] * 60 + (+m[4]);
      if (c <= o) c += 1440;
      res.push([o, c]);
    }
    return res;
  }
  function parseOH(str) {
    if (!str) return null;
    var s = String(str).trim();
    if (/^24\/7$/i.test(s)) return { always: true };
    var days = [[], [], [], [], [], [], []], seen = false;
    var rules = s.split(';'), i, r, m, dayset, rest, ranges, d;
    for (i = 0; i < rules.length; i++) {
      r = rules[i].trim();
      if (!r) continue;
      if (/^(PH|SH)\b/.test(r)) continue;
      r = r.replace(/,\s*(PH|SH)\b/g, '');
      if (/\b(PH|SH|sunrise|sunset|dawn|dusk|week|month|easter)\b|\[|\+/i.test(r)) return null;
      if (/^\d/.test(r)) { dayset = [true, true, true, true, true, true, true]; rest = r; }
      else {
        m = r.match(/^([A-Za-z][A-Za-z,\- ]*?)\s+(\d.*|off|closed)$/i);
        if (!m) return null;
        dayset = expandDays(m[1].replace(/\s+/g, ''));
        if (!dayset) return null;
        rest = m[2];
      }
      if (/^(off|closed)$/i.test(rest)) ranges = [];
      else { ranges = parseRanges(rest); if (!ranges) return null; }
      for (d = 0; d < 7; d++) if (dayset[d]) { days[d] = ranges; seen = true; }
    }
    return seen ? { days: days } : null;
  }
  function openStateAt(oh, day, cur) {
    if (!oh) return { open: null };
    if (oh.always) return { open: true, always: true };
    var tr = oh.days[day], yr = oh.days[(day + 6) % 7], i;
    for (i = 0; i < tr.length; i++) if (cur >= tr[i][0] && cur < tr[i][1]) return { open: true, until: tr[i][1] % 1440 };
    for (i = 0; i < yr.length; i++) if (yr[i][1] > 1440 && cur < yr[i][1] - 1440) return { open: true, until: yr[i][1] - 1440 };
    return { open: false };
  }

  function normPhone(raw) {
    if (!raw) return null;
    var first = String(raw).split(/[;,\/]/)[0];
    var digits = first.replace(/[^\d]/g, '');
    if (!digits) return null;
    if (digits.indexOf('60') === 0) { }
    else if (digits.charAt(0) === '0') digits = '60' + digits.slice(1);
    else return null;
    if (digits.length < 10 || digits.length > 12) return null;
    return { tel: '+' + digits, wa: digits.charAt(2) === '1' ? digits : null };
  }
  function cleanUrl(u) {
    if (!u) return null;
    u = String(u).trim().split(/[;\s]/)[0];
    if (!/^https?:\/\//i.test(u)) {
      if (/^[\w.-]+\.[a-z]{2,}(\/|$)/i.test(u)) u = 'https://' + u; else return null;
    }
    if (/["'<>`\\]/.test(u)) return null;
    return u.slice(0, 300);
  }

  var FOODAM = { restaurant: 1, cafe: 1, fast_food: 1, food_court: 1, ice_cream: 1 };
  var AMLABEL = { restaurant: 'Restaurant', cafe: 'Cafe', fast_food: 'Fast food', food_court: 'Food court / hawker', ice_cream: 'Ice cream' };
  var ADULT = /brothel|stripclub|swingerclub|love_hotel|sex/i;
  function kindOf(t) {
    if (ADULT.test((t.amenity || '') + ' ' + (t.shop || '')) || /florist|flower/i.test((t.shop || '') + ' ' + (t.name || ''))) return null;
    if (/sports? ?toto|magnum 4d|da ?ma ?cai|\b4d\b|lottery|karaoke|\bktv\b|\bpub\b|lounge bar/i.test(t.name || '')) return null;
    if (t.amenity && FOODAM[t.amenity]) return 'food';
    if (t.shop === 'massage' && t.amenity !== 'spa' && !/spa|reflex|foot|thai|wellness|therap|physio|traditional|urut|tui ?na/i.test(t.name || '')) return null;
    if (t.shop === 'massage' || t.amenity === 'spa' || t.leisure === 'sauna' || t.leisure === 'fitness_centre' || t.sport === 'yoga' || t.leisure === 'yoga') return 'wellness';
    return null;
  }
  function wellType(t) {
    if (t.shop === 'massage') return 'Massage';
    if (t.amenity === 'spa') return 'Spa';
    if (t.leisure === 'sauna') return 'Sauna';
    if (t.sport === 'yoga' || t.leisure === 'yoga') return 'Yoga';
    return 'Gym';
  }
  function prettyCuisine(c) {
    return String(c || '').split(';').slice(0, 3).map(function (x) {
      x = x.trim().replace(/_/g, ' '); return x.charAt(0).toUpperCase() + x.slice(1);
    }).filter(Boolean).join(' · ');
  }
  var BFAST = /kopitiam|kopi ?tiam|dim ?sum|nasi lemak|roti canai|roti|bakery|bakehouse|boulangerie|breakfast|brunch|bak kut teh|congee|porridge|chee cheong fun|cheong fun|toast|kaya|half.boiled|pau\b|yong tau foo/;
  var HAWKER = /medan selera|food ?court|hawker|gerai|warung|stall|pasar|kedai makan|mamak|nasi kandar|char kuey|kuey teow|laksa|satay|food centre|food center|street food|hutong|ikan bakar|lok lok/;
  var LUNCH = /nasi campur|economy rice|mixed rice|chap fan|chicken rice|banana leaf|nasi padang|nasi kerabu|curry house|claypot|wantan|wan tan|noodle|mee|pan mee|lunch|bento|biryani|thali|vegetarian buffet|set meal/;
  function foodTabs(t, oh, day, chain) {
    var known = !!oh, a = t.amenity, txt = ((t.name || '') + ' ' + (t.cuisine || '')).toLowerCase();
    var b = openStateAt(oh, day, 510).open, l = openStateAt(oh, day, 780).open, d = openStateAt(oh, day, 1170).open;
    if (a === 'fast_food' || chain) return a === 'cafe' || a === 'ice_cream' ? ['cafe'] : [];   // chains/fast food: never in curated tabs (cafe chains only under Cafe)
    if (BFAST.test(txt) && !(known && b === false)) return ['breakfast'];
    if (a === 'food_court' || HAWKER.test(txt)) return ['street_food'];
    if (a === 'cafe' || a === 'ice_cream') return /brunch|breakfast/.test(txt) && !(known && b === false) ? ['breakfast'] : ['cafe'];
    if (known && l && d === false) return ['lunch'];
    if (known && d && l === false) return ['dinner'];
    if (LUNCH.test(txt)) return ['lunch'];
    return ['dinner'];
  }
  function makeItem(el, now) {
    var t = el.tags || {};
    if (!t.name) return null;
    var lat = el.lat != null ? el.lat : (el.center && el.center.lat);
    var lon = el.lon != null ? el.lon : (el.center && el.center.lon);
    if (typeof lat !== 'number' || typeof lon !== 'number') return null;
    var kind = kindOf(t);
    if (!kind) return null;
    var day = (now.getDay() + 6) % 7, cur = now.getHours() * 60 + now.getMinutes();
    var oh = parseOH(t.opening_hours), st = openStateAt(oh, day, cur);
    var ph = normPhone(t.phone || t['contact:phone'] || t['contact:mobile'] || t.mobile);
    var openText = st.open === true ? (st.always ? 'Open 24 hours' : (st.until != null ? 'Open until ' + fmtTime(st.until) : 'Open now'))
      : st.open === false ? 'Closed now' : 'Hours not listed';
    var it = {
      kind: kind, name: String(t.name).slice(0, 120), latitude: lat, longitude: lon,
      area: [t['addr:street'], t['addr:suburb'] || t['addr:neighbourhood'] || t['addr:city']].filter(Boolean).join(', ').slice(0, 120),
      open_now: st.open, openText: openText, hours: '',
      phone: ph ? ph.tel : null, wa: ph ? ph.wa : null,
      website: cleanUrl(t.website || t['contact:website']),
      reservation: String(t.reservation || '').toLowerCase(),
      price_range: '', rating: null
    };
    if (kind === 'food') {
      it.chain = isChain(t.name);
      it.tabs = foodTabs(t, oh, day, it.chain);
      it.type = it.tabs[0] || 'quick_bite';
      var bits = [AMLABEL[t.amenity] || 'Food'];
      var cu = prettyCuisine(t.cuisine); if (cu) bits.push(cu);
      if (t['diet:halal'] === 'yes') bits.push('Halal');
      if (t['diet:vegetarian'] === 'only' || t['diet:vegan'] === 'only') bits.push('Vegetarian');
      it.vibe = bits.join(' · ');
    } else {
      it.type = wellType(t);
      it.vibe = '';
    }
    it.why_now = it.openText;
    return it;
  }
  function build(els, pos, now, real) {
    var seen = {}, food = [], well = [], i, it, k;
    for (i = 0; i < els.length; i++) {
      it = makeItem(els[i], now);
      if (!it) continue;
      k = it.name.toLowerCase().replace(/\s+/g, ' ').trim() + '|' + it.latitude.toFixed(3) + '|' + it.longitude.toFixed(3);
      if (seen[k]) continue; seen[k] = 1;
      it._d = hav(pos.lat, pos.lng, it.latitude, it.longitude);
      it._dist = real ? Math.round(it._d * 10) / 10 : null;
      (it.kind === 'food' ? food : well).push(it);
    }
    function rank(a, b) {
      var ra = a.open_now === true ? 0 : a.open_now === null ? 1 : 2, rb = b.open_now === true ? 0 : b.open_now === null ? 1 : 2;
      return (a.chain ? 1 : 0) - (b.chain ? 1 : 0) || ra - rb || a._d - b._d;
    }
    food.sort(rank); well.sort(rank);
    return { food: food, well: well };
  }

  function buildQuery(pos, r) {
    var a = '(around:' + r + ',' + pos.lat.toFixed(5) + ',' + pos.lng.toFixed(5) + ')';
    return '[out:json][timeout:20];(' +
      'nwr' + a + '[amenity~"^(restaurant|cafe|fast_food|food_court|ice_cream)$"][name];' +
      'nwr' + a + '[shop=massage][name];nwr' + a + '[amenity=spa][name];' +
      'nwr' + a + '[leisure~"^(fitness_centre|sauna|yoga)$"][name];nwr' + a + '[sport=yoga][name];' +
      ');out tags center ' + LIMIT + ';';
  }
  function fetchElsOverpass(pos, r) {
    var q = buildQuery(pos, r), i = 0;
    function next(lastErr) {
      if (i >= ENDPOINTS.length) return Promise.reject(lastErr || new Error('all map servers failed'));
      var url = ENDPOINTS[i++], ctl = (typeof AbortController !== 'undefined') ? new AbortController() : null;
      var to = setTimeout(function () { if (ctl) ctl.abort(); }, 15000);
      return fetch(url, {
        method: 'POST', headers: { 'Content-Type': 'application/x-www-form-urlencoded;charset=UTF-8' },
        body: 'data=' + encodeURIComponent(q), signal: ctl ? ctl.signal : undefined
      }).then(function (r) { clearTimeout(to); if (!r.ok) throw new Error('HTTP ' + r.status); return r.json(); })
        .then(function (j) {
          if (!j || !Array.isArray(j.elements)) throw new Error('bad response');
          if (!j.elements.length && j.remark) throw new Error(j.remark);
          return j.elements;
        }).catch(function (e) { clearTimeout(to); return next(e); });
    }
    return next();
  }
  var ALLP = null, CHAINS = {};
  function isChain(n) { return (CHAINS[String(n || '').toLowerCase().trim()] || 0) >= 4; }
  function placesUrl() {
    var d = ''; try { d = new Date().toLocaleDateString('en-CA', { timeZone: 'Asia/Kuala_Lumpur' }); } catch (e) {}
    return 'places.tsv?d=' + d;
  }
  function parseTSV(txt) {
    var lines = String(txt).split('\n'), head = lines[0].split('\t'), out = [], i, j, c, t, lat, lon;
    if (head[0] !== '@lat') throw new Error('bad places file');
    for (i = 1; i < lines.length; i++) {
      c = lines[i].split('\t'); if (c.length < 3) continue;
      lat = parseFloat(c[0]); lon = parseFloat(c[1]); if (isNaN(lat) || isNaN(lon)) continue;
      t = {}; for (j = 2; j < head.length; j++) if (c[j]) t[head[j]] = c[j].replace(/\r$/, '');
      if (t.name) { var kn = t.name.toLowerCase().trim(); CHAINS[kn] = (CHAINS[kn] || 0) + 1; }
      out.push({ lat: lat, lon: lon, tags: t });
    }
    return out;
  }
  function loadAllPlaces() {
    if (ALLP) return ALLP;
    var ctl = (typeof AbortController !== 'undefined') ? new AbortController() : null;
    var to = setTimeout(function () { if (ctl) ctl.abort(); }, 20000);
    ALLP = fetch(placesUrl(), { signal: ctl ? ctl.signal : undefined })
      .then(function (r) { clearTimeout(to); if (!r.ok) throw new Error('HTTP ' + r.status); return r.text(); })
      .then(parseTSV)
      .catch(function (e) { clearTimeout(to); ALLP = null; throw e; });
    return ALLP;
  }
  function fetchEls(pos, r) {
    var km = r / 1000, dLat = km / 111, dLng = km / (111 * Math.cos(pos.lat * Math.PI / 180));
    return loadAllPlaces().then(function (all) {
      return all.filter(function (e) {
        return Math.abs(e.lat - pos.lat) <= dLat && Math.abs(e.lon - pos.lng) <= dLng && hav(pos.lat, pos.lng, e.lat, e.lon) <= km;
      });
    });
  }
  function slim(els) {
    return els.map(function (e) {
      var t = {}, k, i;
      for (i = 0; i < KEEP_TAGS.length; i++) { k = KEEP_TAGS[i]; if (e.tags && e.tags[k] != null) t[k] = e.tags[k]; }
      return { lat: e.lat != null ? e.lat : (e.center && e.center.lat), lon: e.lon != null ? e.lon : (e.center && e.center.lon), tags: t };
    });
  }
  function cellKey(p) { return 'jomlive:' + Math.round(p.lat / CELL) + ',' + Math.round(p.lng / CELL); }
  function cacheGet(p) {
    try {
      var raw = localStorage.getItem(cellKey(p)); if (!raw) return null;
      var c = JSON.parse(raw); if (!c || Date.now() - c.ts > CACHE_TTL) return null; return c;
    } catch (e) { return null; }
  }
  function cachePut(p, els, radius) {
    try {
      var key = cellKey(p), idx = JSON.parse(localStorage.getItem('jomlive:idx') || '[]');
      idx = idx.filter(function (k) { return k !== key; }); idx.push(key);
      while (idx.length > CACHE_MAX) localStorage.removeItem(idx.shift());
      localStorage.setItem(key, JSON.stringify({ ts: Date.now(), radius: radius, els: els }));
      localStorage.setItem('jomlive:idx', JSON.stringify(idx));
    } catch (e) { }
  }

  function rebuild() {
    if (!S.els || !S.pos) return;
    var r = build(S.els, S.pos, new Date(), !S.usingDefault);
    S.food = r.food; S.well = r.well;
  }
  function load(pos, force) {
    var now = Date.now();
    if (S.busy) { S.pending = { pos: pos, force: force }; return; }
    if (!force && S.qAt && (now - S.qAt) < MIN_GAP_MS) {
      clearTimeout(S.timer);
      S.timer = setTimeout(function () { load(S.pos || pos, true); }, MIN_GAP_MS - (now - S.qAt));
      return;
    }
    if (!force) {
      var c = null;
      if (c) {
        S.els = c.els; S.radius = c.radius; S.qPos = { lat: pos.lat, lng: pos.lng }; S.qAt = now;
        S.status = 'ok'; S.updated = c.ts; rebuild(); renderAll(); return;
      }
    }
    S.busy = true; S.status = 'loading'; S.err = ''; S.qPos = { lat: pos.lat, lng: pos.lng }; S.qAt = now;
    if (!force) { S.food = []; S.well = []; S.els = null; }
    renderAll();
    fetchEls(pos, RADIUS_M).then(function (els) {
      if (els.length >= LIMIT) return fetchEls(pos, DENSE_RADIUS_M).then(function (e2) { return { els: e2, radius: DENSE_RADIUS_M }; });
      return { els: els, radius: RADIUS_M };
    }).then(function (res) {
      S.els = slim(res.els); S.radius = res.radius; S.status = 'ok'; S.updated = Date.now();
      cachePut(pos, S.els, S.radius); rebuild();
    }).catch(function (e) {
      S.status = 'error'; S.err = (e && e.message) || 'failed';
    }).then(function () {
      S.busy = false; renderAll();
      if (S.pending) { var p = S.pending; S.pending = null; load(p.pos, p.force); }
    });
  }
  function setGlobals(lat, lng) {
    try { root.userLat = lat; root.userLng = lng; root.USER_LAT = lat; root.USER_LNG = lng; } catch (e) {}
  }
  function onFix(lat, lng) {
    S.usingDefault = false; S.pos = { lat: lat, lng: lng }; setGlobals(lat, lng);
    var moved = S.qPos ? hav(S.qPos.lat, S.qPos.lng, lat, lng) : Infinity;
    if (moved >= MOVE_KM || (S.status === 'error' && Date.now() - S.qAt > 20000)) load(S.pos, false);
    else { rebuild(); renderAll(); }
  }
  function useDefault() {
    if (S.pos) return;
    S.usingDefault = true; S.pos = { lat: DEFAULT_POS.lat, lng: DEFAULT_POS.lng };
    load(S.pos, false);
  }
  function refresh() { if (S.pos) load(S.pos, true); else useDefault(); }

  function $(id) { return document.getElementById(id); }
  function bar() {
    var txt;
    if (S.status === 'loading') txt = 'Finding places near you…';
    else if (S.usingDefault) txt = 'Showing central KL — turn on location for places near you';
    else txt = 'Within ' + (S.radius / 1000).toFixed(1).replace(/\.0$/, '') + ' km of you · ' + (S.food.length + S.well.length) + ' places';
    var upd = S.updated ? ' · updated ' + new Date(S.updated).toLocaleTimeString('en-MY', { hour: 'numeric', minute: '2-digit', hour12: true }) : '';
    return '<div class="live-bar"><span>📍 ' + esc(txt + upd) + '</span><button class="live-refresh" onclick="JomLive.refresh()">🔄 Refresh</button></div>';
  }
  var ATTR = '<div class="osm-attr">Places from OpenStreetMap contributors. Hours and phone numbers are volunteer-maintained — call to confirm before you go.</div>';
  function actions(it) {
    var h = [], q = encodeURIComponent(it.name + ' ' + (it.area || '') + ' Kuala Lumpur');
    if (it.phone) h.push('<a class="act-btn act-call" href="tel:' + esc(it.phone) + '">📞 Call</a>');
    else if (it.website) h.push('<a class="act-btn" href="' + esc(it.website) + '" target="_blank" rel="noopener">🔗 Website</a>');
    else h.push('<a class="act-btn" href="https://www.google.com/maps/search/?api=1&query=' + q + '" target="_blank" rel="noopener">🗺 Maps</a>');
    h.push('<a class="act-btn act-dir" href="https://www.google.com/maps/dir/?api=1&destination=' + it.latitude.toFixed(6) + ',' + it.longitude.toFixed(6) + '" target="_blank" rel="noopener">🧭 Directions</a>');
    h.push('<button class="act-btn act-g" onclick="JomLive.gcheck(this)" data-n="' + esc(it.name) + '" data-la="' + it.latitude + '" data-lo="' + it.longitude + '">🕒 Check hours</button>');
    var wa = it.wa ? '<a class="wa-link" href="https://wa.me/' + esc(it.wa) + '" target="_blank" rel="noopener">💬 WhatsApp to reserve</a>' : '';
    return '<div class="act-row">' + h.join('') + '</div>' + wa;
  }

  function pill(it) {
    if (it.open_now === true) return '<span class="open-pill">Open</span>';
    if (it.open_now === false) return '<span class="closed-pill">Closed</span>';
    return '';
  }
  function resBadge(it) {
    if (it.reservation === 'required') return '<span class="pc-badge" style="background:rgba(232,85,85,.1);color:#a33;">Reservation required</span>';
    if (it.reservation === 'yes' || it.reservation === 'recommended') return '<span class="pc-badge" style="background:rgba(45,158,92,.12);color:#1a5c35;">Reservations accepted</span>';
    return '';
  }
  function dist(it) { return it._dist != null ? '<div class="pc-dist">📍 ' + fmtDist(it._d) + '</div>' : (it.area ? '<div class="pc-dist">📍 ' + esc(it.area) + '</div>' : ''); }
  function foodCard(it) {
    var rb = resBadge(it);
    return '<div class="pc"><div class="pc-header"><div class="pc-name">' + esc(it.name) + '</div>' + dist(it) + '</div>' +
      (rb ? '<div class="pc-badges">' + rb + '</div>' : '') +
      (it.area && it._dist != null ? '<div class="pc-area">' + esc(it.area) + '</div>' : '') +
      '<div class="pc-vibe">' + esc(it.vibe) + '</div>' +
      '<div class="pc-meta">' + pill(it) + '<span class="price-lbl">' + esc(it.openText) + '</span></div>' + actions(it) + '</div>';
  }
  function wellCard(it) {
    return '<div class="well-card"><div class="well-head"><div class="well-name">' + esc(it.name) + '</div>' +
      (it._dist != null ? '<span class="pc-dist">📍 ' + fmtDist(it._d) + '</span>' : '') + '</div>' +
      (it.area ? '<div class="well-area">📍 ' + esc(it.area) + '</div>' : '') +
      '<span class="well-type">' + esc(it.type) + '</span>' +
      '<div style="font-size:.72rem;color:var(--muted);margin-top:5px">' + pill(it) + ' ' + esc(it.openText) + '</div>' + actions(it) + '</div>';
  }
  function msgBox(emoji, title, sub) {
    return '<div class="nodata"><div class="nodata-emoji">' + emoji + '</div><div class="nodata-msg">' + esc(title) + '</div>' +
      (sub ? '<div style="font-size:.8rem;color:var(--muted);margin-top:8px">' + esc(sub) + '</div>' : '') + '</div>';
  }
  var TABLABEL = { breakfast: 'breakfast', cafe: 'cafe', lunch: 'lunch', dinner: 'dinner', street_food: 'hawker / food court' };
  var PM = [
    { n: 'Bangsar Baru Sunday Market', d: 0, a: 'Jalan Telawi area, Bangsar Baru', h: 'about 4:30 PM – 9 PM', la: 3.1322, lo: 101.6712, src: 'https://www.loopme.my/post/best-pasar-malam-kl/' },
    { n: 'Pasar Malam TTDI', d: 0, a: 'Jalan Tun Mohd Fuad, Taman Tun Dr Ismail', h: 'Sunday evening', la: 3.1407, lo: 101.6294, src: 'https://www.loopme.my/post/best-pasar-malam-kl/' },
    { n: 'Pasar Malam SS2', d: 1, a: 'Jalan SS 2/60–2/64, SS2, Petaling Jaya', h: 'about 5 PM – 10 PM', la: 3.1185, lo: 101.6211, src: 'https://klfoodie.com/night-market-kl-klang-valley/' },
    { n: 'Pasar Malam Sri Petaling', d: 2, a: 'Jalan Radin Anum, Bandar Baru Sri Petaling', h: 'about 5 PM – 10:30 PM', la: 3.0691, lo: 101.6920, src: 'https://klfoodie.com/night-market-kl-klang-valley/' },
    { n: 'Pasar Malam Taman Connaught', d: 3, a: 'Jalan Cerdas, Taman Connaught, Cheras', h: 'about 5 PM – late (KL’s biggest)', la: 3.0769, lo: 101.7420, src: 'https://www.timeout.com/kuala-lumpur/shops/taman-connaught-night-market' },
    { n: 'Pasar Malam OUG', d: 4, a: 'Jalan Hujan Emas / Hujan Rahmat, Taman OUG', h: 'about 5 PM – midnight', la: 3.0710, lo: 101.6771, src: 'https://erisgoesto.com/2022/06/12/pasar-malam-oug-oug-night-market-kuala-lumpur/' },
    { n: 'Pasar Malam Lorong TAR', d: 6, a: 'Lorong Tuanku Abdul Rahman, City Centre', h: 'about 5 PM – late', la: 3.1605, lo: 101.6973, src: 'https://www.thestar.com.my/metro/metro-news/2024/01/13/saturday-night-fever-in-the-city' },
    { n: 'Pasar Malam Setia Alam', d: 6, a: 'Jalan Setia Prima A U13/A, Setia Alam, Shah Alam', h: 'about 5 PM – 10 PM', la: null, lo: null, src: 'https://klfoodie.com/night-market-kl-klang-valley/' }
  ];
  var DAYN = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
  function pmList(onlyTonight) {
    var now = new Date(), today = now.getDay(), late = now.getHours() >= 23;
    var arr = PM.map(function (p) {
      var inDays = (p.d - today + 7) % 7; if (inDays === 0 && late) inDays = 7;
      var dist = (S.pos && !S.usingDefault && p.la != null) ? hav(S.pos.lat, S.pos.lng, p.la, p.lo) : null;
      return { p: p, inDays: inDays, dist: dist };
    }).filter(function (x) { return !onlyTonight || x.inDays === 0; });
    arr.sort(function (a, b) { return a.inDays - b.inDays || (a.dist == null ? 99 : a.dist) - (b.dist == null ? 99 : b.dist); });
    return arr;
  }
  function pmCard(x) {
    var p = x.p, when = x.inDays === 0 ? '<span class="pm-tonight">TONIGHT</span>' : x.inDays === 1 ? '<span class="pm-soon">Tomorrow</span>' : '<span class="pm-day">' + DAYN[p.d] + '</span>';
    var q = encodeURIComponent(p.n + ' ' + p.a);
    return '<div class="pc pm-card"><div class="pc-header"><div class="pc-name">🏮 ' + esc(p.n) + '</div>' + (x.dist != null ? '<div class="pc-dist">📍 ' + fmtDist(x.dist) + '</div>' : '') + '</div>' +
      '<div class="pc-area">' + esc(p.a) + '</div>' +
      '<div class="pc-meta">' + when + '<span class="price-lbl">Every ' + DAYN[p.d] + ' · ' + esc(p.h) + '</span></div>' +
      '<div class="act-row"><a class="act-btn act-call" href="https://www.google.com/maps/search/?api=1&query=' + q + '" target="_blank" rel="noopener">📍 Map</a>' +
      '<a class="act-btn act-dir" href="https://www.google.com/maps/dir/?api=1&destination=' + q + '" target="_blank" rel="noopener">🧭 Directions</a>' +
      '<a class="act-btn act-g" href="' + esc(p.src) + '" target="_blank" rel="noopener">ℹ️ Source</a></div></div>';
  }
  function pmSection(onlyTonight) {
    var arr = pmList(onlyTonight); if (!arr.length) return '';
    return '<div class="pm-head">🏮 ' + (onlyTonight ? 'Pasar malam tonight' : 'Pasar malam this week') + '</div>' + arr.map(pmCard).join('') +
      '<div class="osm-attr">Weekly schedules from Time Out KL, KL Foodie, LoopMe and others. Markets can close on public holidays or in heavy rain — check before going.</div>';
  }
  function renderFoodLive() {
    var all = $('fd-all'); if (!all) return;
    var ids = ['breakfast', 'cafe', 'lunch', 'dinner', 'street_food'];
    var html;
    if (S.status === 'error' && !S.food.length) {
      html = msgBox('🛰', 'Couldn\'t load nearby places', 'The free map server is busy. Tap Refresh in a moment.') + bar();
      all.innerHTML = html; ids.forEach(function (t) { var e = $('fd-' + t); if (e) e.innerHTML = html; }); return;
    }
    if (S.status === 'loading' && !S.food.length) {
      html = msgBox('🍜', 'Finding places near you…', '');
      all.innerHTML = html; ids.forEach(function (t) { var e = $('fd-' + t); if (e) e.innerHTML = html; }); return;
    }
    if (S.status === 'idle') return;
    all.innerHTML = bar() + pmSection(true) + (S.food.length ? S.food.slice(0, 40).map(foodCard).join('') : msgBox('🍽', 'No food places mapped within ' + (S.radius / 1000) + ' km', 'Try Refresh after moving.')) + ATTR;
    ids.forEach(function (t) {
      var e = $('fd-' + t); if (!e) return;
      var f = S.food.filter(function (i) { return i.tabs.indexOf(t) > -1; }).slice(0, 25);
      e.innerHTML = bar() + (t === 'street_food' ? pmSection(false) + '<div class="pm-head">🍢 Hawkers & food courts near you</div>' : '') + (f.length ? f.map(foodCard).join('') : msgBox('🍽', 'No ' + TABLABEL[t] + ' spots nearby', 'Try another tab or move a little.')) + ATTR;
    });
  }
  var origWell = null;
  function renderWellLive(staticItems) {
    var el = $('well-all'); if (!el) return;
    if (S.status === 'idle' || (S.status === 'error' && !S.well.length) || (S.status === 'loading' && !S.well.length && !S.els)) {
      if (origWell && staticItems && S.status !== 'loading') origWell(staticItems);
      else if (S.status === 'loading') el.innerHTML = msgBox('🧘', 'Finding wellness spots near you…', '');
      return;
    }
    el.innerHTML = bar() + (S.well.length ? S.well.slice(0, 20).map(wellCard).join('') : msgBox('🧘', 'No gyms, spas or massage places mapped within ' + (S.radius / 1000) + ' km', '')) + ATTR;
  }
  function syncData() {
    try { if (root.DATA && root.DATA.modules && S.food.length) root.DATA.modules.food = S.food; } catch (e) {}
  }
  function renderAll() {
    syncData();
    renderFoodLive();
    renderWellLive(root.STATIC_WELLNESS);
    try { if (!S.usingDefault && S.food.length && typeof root.renderNearYou === 'function') root.renderNearYou(S.food); } catch (e) {}
    var ls = $('locStatus');
    if (ls) {
      ls.textContent = S.status === 'loading' ? '📍 Finding places near you…'
        : S.status === 'error' && !S.food.length ? '📍 Couldn\'t load nearby places'
        : S.usingDefault ? '📍 Central KL (location off)'
        : '📍 Near you · ' + (S.food.length + S.well.length) + ' places';
    }
  }

  var ISO = /^\d{4}-\d{2}-\d{2}$/;
  function klToday() {
    try { return new Date().toLocaleDateString('en-CA', { timeZone: 'Asia/Kuala_Lumpur' }); }
    catch (e) { var d = new Date(); return d.getFullYear() + '-' + ('0' + (d.getMonth() + 1)).slice(-2) + '-' + ('0' + d.getDate()).slice(-2); }
  }
  function eventBucket(it, fallback) {
    if (it && ISO.test(it.date_iso || '')) {
      var today = klToday(), start = it.date_iso, end = ISO.test(it.end_iso || '') ? it.end_iso : start;
      if (end < today) return 'past';
      if (start <= today) return 'now';
      var days = Math.round((Date.parse(start) - Date.parse(today)) / 86400000);
      return days <= 7 ? 'week' : 'upcoming';
    }
    return fallback ? fallback(it) : 'week';
  }

  function start() {
    var origBucket = root.evBucketOf;
    root.evBucketOf = function (it) { return eventBucket(it, origBucket); };
    origWell = root.renderWellness;
    root.renderFood = function () { renderAll(); };
    root.renderWellness = function (items) { renderWellLive(items); };
    setInterval(function () { if (S.els) { rebuild(); renderAll(); } }, 60000);

    if (!navigator.geolocation) { useDefault(); return; }
    var got = false;
    function ok(p) { got = true; onFix(p.coords.latitude, p.coords.longitude); }
    function bad() { if (!got) useDefault(); }
    setTimeout(function () { if (!got) useDefault(); }, 9000);
    navigator.geolocation.getCurrentPosition(ok, bad, { enableHighAccuracy: false, timeout: 8000, maximumAge: 300000 });
    navigator.geolocation.watchPosition(ok, function () {}, { enableHighAccuracy: false, maximumAge: 60000, timeout: 30000 });
    document.addEventListener('visibilitychange', function () {
      if (!document.hidden) navigator.geolocation.getCurrentPosition(ok, function () {}, { enableHighAccuracy: false, timeout: 8000, maximumAge: 60000 });
    });
  }

  root.JomLive = { refresh: refresh, _t: { parseOH: parseOH, openStateAt: openStateAt, normPhone: normPhone, cleanUrl: cleanUrl, makeItem: makeItem, build: build, eventBucket: eventBucket, esc: esc, foodCard: foodCard, wellCard: wellCard, buildQuery: buildQuery, _S: S } };
  if (typeof document !== 'undefined' && document.getElementById) start();
})();

(function(){
  var st=document.createElement('style');st.textContent=".act-row{display:flex;gap:8px;margin-top:10px;flex-wrap:wrap}.act-btn{flex:1 1 0;min-width:84px;text-align:center;padding:9px 10px;border-radius:12px;font-size:.78rem;font-weight:700;text-decoration:none;border:1px solid var(--border);background:var(--card);color:var(--text);font-family:inherit}.act-call{background:var(--orange);border-color:var(--orange);color:#fff}.act-wa{background:#25D366;border-color:#25D366;color:#fff}.act-dir{background:var(--card);color:var(--orange);border-color:var(--orange)}.nophone{font-size:.68rem;color:var(--muted);align-self:center;padding:0 4px}.live-bar{display:flex;justify-content:space-between;align-items:center;gap:8px;font-size:.7rem;color:var(--muted);margin:0 0 10px}body.night .live-bar{color:#E8D5F0}.live-refresh{border:1px solid var(--border);background:var(--card);color:var(--orange);border-radius:100px;padding:5px 12px;font-size:.7rem;font-weight:700;cursor:pointer;font-family:inherit}.osm-attr{font-size:.62rem;color:var(--muted);margin-top:10px;text-align:center}.osm-attr a{color:inherit}";document.head.appendChild(st);
  function e(x){return String(x==null?'':x).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');}
  var oN=window.renderNearYou;
  window.renderNearYou=function(items){
    try{
      if(!window.USER_LAT||!window.USER_LNG||!items||!items.length)return;
      var el=document.getElementById('nearYouList'),sec=document.getElementById('nearYouSection');if(!el||!sec)return;
      var arr=items.filter(function(f){return f.latitude&&f.longitude&&!f.chain&&f.open_now!==false&&f.type!=='quick_bite';}).map(function(f){return{f:f,d:haversine(window.USER_LAT,window.USER_LNG,f.latitude,f.longitude)};}).sort(function(a,b){return a.d-b.d;}).slice(0,3);
      if(!arr.length)return;
      el.innerHTML=arr.map(function(o){var f=o.f,d=o.d;var dist=d<1?(d*1000).toFixed(0)+'m':d.toFixed(1)+'km';
        var q='https://www.google.com/maps/dir/?api=1&destination='+encodeURIComponent(f.latitude+','+f.longitude);
        return '<div class="near-card"><div class="near-card-char">🍴</div><div class="near-card-name">'+e(f.name)+'</div><div class="near-card-dist">📍 '+dist+' away</div><div class="near-card-area">'+e(f.area)+'</div><a class="act-btn act-dir" style="display:block;margin-top:6px" target="_blank" rel="noopener" href="'+q+'">Directions</a></div>';}).join('');
      sec.style.display='block';
    }catch(x){if(oN)try{oN(items);}catch(y){} }
  };
  (function(){
    var GKEY='AIzaSyBONZvoOhh9WlwgTyaCVqaX0Ek-YN0o1ZU', DAYMAX=5;
    var st2=document.createElement('style');
    st2.textContent='.act-g{background:#fff;color:#1a73e8;border-color:#1a73e8;cursor:pointer}.act-g[disabled]{opacity:.6}.gres{margin-top:8px;padding:9px 11px;border-radius:10px;background:rgba(26,115,232,.07);border:1px solid rgba(26,115,232,.2);font-size:.74rem;color:var(--text);line-height:1.45}.gres a{color:#1a73e8;font-weight:700}.gsrc{font-size:.62rem;color:var(--muted);margin-top:4px}.tlive{display:flex;gap:8px;margin-top:10px;flex-wrap:wrap}.tnote{font-size:.68rem;color:var(--muted);margin-top:6px}.act-row{display:grid!important;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px}.act-row .act-btn{min-width:0;padding:10px 4px;font-size:.74rem;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;text-align:center}.act-row .act-dir,.act-row .act-g{background:var(--card);color:var(--text);border:1px solid var(--border)}.wa-link{display:inline-block;margin-top:8px;font-size:.74rem;color:#128C7E;font-weight:700;text-decoration:none}.nophone{display:none}';
    document.head.appendChild(st2);
    function klDay(){try{return new Date().toLocaleDateString('en-CA',{timeZone:'Asia/Kuala_Lumpur'});}catch(x){return 'd';} }
    function takeQuota(){try{var k='jomg:'+klDay(),n=+(localStorage.getItem(k)||0);if(n>=DAYMAX)return false;localStorage.setItem(k,String(n+1));return true;}catch(x){return true;} }
    function box(card){var o=card.querySelector('.gres');if(!o){o=document.createElement('div');o.className='gres';card.appendChild(o);}return o;}
    window.JomLive.gcheck=function(btn){
      var card=btn.closest?btn.closest('.pc,.well-card'):btn.parentNode.parentNode, out=box(card);
      if(!takeQuota()){out.innerHTML='Live check limit reached for today on this phone — call to confirm.';return;}
      btn.disabled=true; out.textContent='Checking Google Maps…';
      fetch('https://places.googleapis.com/v1/places:searchText',{method:'POST',
        headers:{'Content-Type':'application/json','X-Goog-Api-Key':GKEY,
          'X-Goog-FieldMask':'places.displayName,places.businessStatus,places.currentOpeningHours.openNow,places.currentOpeningHours.weekdayDescriptions,places.nationalPhoneNumber,places.googleMapsUri'},
        body:JSON.stringify({textQuery:btn.getAttribute('data-n'),maxResultCount:1,
          locationBias:{circle:{center:{latitude:+btn.getAttribute('data-la'),longitude:+btn.getAttribute('data-lo')},radius:200} } })
      }).then(function(r){return r.json().then(function(j){return {ok:r.ok,j:j};});})
      .then(function(res){
        btn.disabled=false;
        if(!res.ok){out.innerHTML='Live check unavailable right now — call to confirm.';return;}
        var p=res.j&&res.j.places&&res.j.places[0];
        if(!p){out.innerHTML='Not found on Google Maps — call to confirm.';return;}
        var h=[], bs=p.businessStatus, oh=p.currentOpeningHours;
        h.push('<b>'+e(p.displayName&&p.displayName.text)+'</b>');
        if(bs==='CLOSED_PERMANENTLY')h.push('⛔ <b>Permanently closed</b>');
        else if(bs==='CLOSED_TEMPORARILY')h.push('⚠️ <b>Temporarily closed</b>');
        else if(oh&&oh.openNow===true)h.push('✅ <b>Open now</b>');
        else if(oh&&oh.openNow===false)h.push('❌ <b>Closed now</b>');
        else h.push('Hours not listed on Google');
        if(oh&&oh.weekdayDescriptions&&bs!=='CLOSED_PERMANENTLY'){var di=(new Date().getDay()+6)%7;if(oh.weekdayDescriptions[di])h.push('Today: '+e(oh.weekdayDescriptions[di].replace(/^[^:]+:\s*/,'')));}
        if(p.nationalPhoneNumber)h.push('📞 <a href="tel:'+e(p.nationalPhoneNumber.replace(/[^\d+]/g,''))+'">'+e(p.nationalPhoneNumber)+'</a>');
        if(p.googleMapsUri&&/^https:\/\//.test(p.googleMapsUri))h.push('<a href="'+e(p.googleMapsUri)+'" target="_blank" rel="noopener">Open in Google Maps ↗</a>');
        out.innerHTML=h.join('<br>')+'<div class="gsrc">Source: Google Maps</div>';
      }).catch(function(){btn.disabled=false;out.innerHTML='Live check unavailable right now — call to confirm.';});
    };
    function transitLinks(){
      var cards=document.querySelectorAll('.transit-card'),i,c,nm,ktm,html;
      for(i=0;i<cards.length;i++){c=cards[i]; if(c.querySelector('.tlive'))continue;
        nm=(c.querySelector('.tc-name')||{}).textContent||''; ktm=/ktm|komuter|ets/i.test(nm);
        html='<div class="tnote">Based on this morning’s news check — not live. Tap for official updates.</div><div class="tlive">'+
          (ktm?'<a class="act-btn act-dir" href="https://www.ktmb.com.my/" target="_blank" rel="noopener">🚆 KTMB official ↗</a>'
              :'<a class="act-btn act-dir" href="https://myrapid.com.my/" target="_blank" rel="noopener">🚇 MyRapid official ↗</a><a class="act-btn" href="https://x.com/MyRapidKL" target="_blank" rel="noopener">Live alerts on X ↗</a>')+'</div>';
        c.insertAdjacentHTML('beforeend',html);}
    }
    var wazeAt=null;
    function wazeCenter(){
      var S=window.JomLive._t._S; if(!S.pos||S.usingDefault)return;
      if(wazeAt&&hv(wazeAt.lat,wazeAt.lng,S.pos.lat,S.pos.lng)<1)return;
      var f=document.querySelector('iframe[src*="embed.waze.com"]'); if(!f)return;
      f.src='https://embed.waze.com/iframe?zoom=14&lat='+S.pos.lat.toFixed(5)+'&lon='+S.pos.lng.toFixed(5)+'&ct=livemap&pin=1';
      wazeAt={lat:S.pos.lat,lng:S.pos.lng};
    }
    function hv(a,b,c,d){var R=6371,p=Math.PI/180,x=Math.sin((c-a)*p/2),y=Math.sin((d-b)*p/2);return 2*R*Math.asin(Math.sqrt(x*x+Math.cos(a*p)*Math.cos(c*p)*y*y));}
    setInterval(function(){try{transitLinks();}catch(x){}try{wazeCenter();}catch(x){} },3000);
  })();
  function parseKL(str){if(!str)return null;var m=String(str).match(/^(\d{4}-\d{2}-\d{2})[ T](\d{2}):(\d{2})/);if(!m)return null;var d=new Date(m[1]+'T'+m[2]+':'+m[3]+':00+08:00');return isNaN(d.getTime())?null:d;}
  function klDateStr(d){try{return d.toLocaleDateString('en-MY',{weekday:'short',day:'numeric',month:'short',timeZone:'Asia/Kuala_Lumpur'})+', '+d.toLocaleTimeString('en-MY',{hour:'numeric',minute:'2-digit',hour12:true,timeZone:'Asia/Kuala_Lumpur'});}catch(x){return '';} }
  function klToday2(){try{return new Date().toLocaleDateString('en-CA',{timeZone:'Asia/Kuala_Lumpur'});}catch(x){return '';} }
  function guideAgeH(d){var g=parseKL(d&&d.generated_at);return g?(Date.now()-g.getTime())/3600000:999;}
  function sanitize(d){
    if(!d||!d.modules)return d;var m=d.modules,today=klToday2(),stale=guideAgeH(d)>20;
    m.events=(m.events||[]).filter(function(ev){if(/genting|resorts world|arena of stars|singapore|penang|johor|melaka|ipoh/i.test((ev.venue||'')+' '+(ev.title||'')))return false;var end=(ev.end_iso||ev.date_iso||'');return /^https?:\/\//.test(ev.link||'')&&(!end||end>=today);});
    m.events.forEach(function(ev){ev.time=ev.time||'See link';ev.price=ev.price||'See link';ev.verified=true;ev.verdict=ev.verdict||'Worth it';if(!ev.source){ev.source=/klconcert/.test(ev.link)?'KL Concert':/allevents/.test(ev.link)?'AllEvents':'Listing';}var a=ev.date_iso,b=ev.end_iso||a;if(!/^\d{4}-\d{2}-\d{2}$/.test(a||''))return;var f=function(x,o){return new Date(x+'T12:00:00+08:00').toLocaleDateString('en-GB',o);};var tz='Asia/Kuala_Lumpur';ev.date=(a===b)?f(a,{weekday:'short',day:'numeric',month:'short',timeZone:tz}):(f(a,{weekday:'short',day:'numeric',month:'short',timeZone:tz})+' – '+f(b,{weekday:'short',day:'numeric',month:'short',timeZone:tz}));});
    m.news=stale?[]:(m.news||[]).filter(function(n){return /^https?:\/\//.test(n.url||'');});
    (m.transit||[]).forEach(function(t){if(stale||!/^https?:\/\//.test(t.url||'')){t.status='No disruption reported';t.verdict='';} });
    if(d.quality_check)d.quality_check.warnings=[];
    d._stale=stale;return d;
  }
  var oRA=window.renderAll;
  if(oRA){window.renderAll=function(d){try{sanitize(d);}catch(x){}oRA(d);try{afterRender(d);}catch(x){} };}
  function afterRender(d){
    var qc=document.getElementById('qcConf');if(qc){var card=qc.closest?qc.closest('div[class*="qc"],.card,section'):null;var p=qc.parentNode&&qc.parentNode.parentNode;(card||p).style.display='none';}
    var ab=document.getElementById('alertBanner');if(ab&&d&&d._stale)ab.style.display='none';
    applyWx();
  }
  setInterval(function(){try{var d=window.DATA,t=document.getElementById('updatedText'),b=document.getElementById('updatedBadge');if(!d||!t)return;var g=parseKL(d.events_checked_at||d.generated_at);if(!g)return;var s=(d._stale?'⚠️ Last updated ':'Events checked ')+klDateStr(g);if(t.textContent!==s)t.textContent=s;if(b){b.style.background=d._stale?'rgba(232,85,85,.15)':'';} }catch(x){} },1000);
  /* live weather from Open-Meteo (free, no key) */
  var WX=null,WMO={0:['☀️','Clear sky'],1:['🌤','Mainly clear'],2:['⛅','Partly cloudy'],3:['☁️','Overcast'],45:['🌫','Fog'],48:['🌫','Fog'],51:['🌦','Light drizzle'],53:['🌦','Drizzle'],55:['🌧','Heavy drizzle'],61:['🌦','Light rain'],63:['🌧','Rain'],65:['🌧','Heavy rain'],80:['🌦','Rain showers'],81:['🌧','Rain showers'],82:['⛈','Violent showers'],95:['⛈','Thunderstorm'],96:['⛈','Thunderstorm, hail'],99:['⛈','Thunderstorm, hail']};
  function wmo(c,night){var w=WMO[c]||['☁️','Cloudy'];if(night&&(c<=2))return['🌙',w[1]];return w;}
  function aqiLbl(a){return a<=50?'Good':a<=100?'Moderate':a<=150?'Unhealthy (sensitive)':a<=200?'Unhealthy':'Very unhealthy';}
  function hm(iso){var m=String(iso).match(/T(\d{2}):(\d{2})/);if(!m)return'';var h=+m[1],ap=h>=12?'PM':'AM';return ((h%12)||12)+':'+m[2]+' '+ap;}
  function loadWx(){
    var la=3.1390,lo=101.6869;try{var S=window.JomLive._t._S;if(S.pos&&!S.usingDefault){la=S.pos.lat;lo=S.pos.lng;} }catch(x){}
    var f='https://api.open-meteo.com/v1/forecast?latitude='+la.toFixed(3)+'&longitude='+lo.toFixed(3)+'&current=temperature_2m,apparent_temperature,relative_humidity_2m,weather_code,wind_speed_10m,is_day&hourly=temperature_2m,weather_code&daily=sunrise,sunset&timezone=Asia%2FKuala_Lumpur&forecast_days=2';
    var a='https://air-quality-api.open-meteo.com/v1/air-quality?latitude='+la.toFixed(3)+'&longitude='+lo.toFixed(3)+'&current=us_aqi,uv_index&timezone=Asia%2FKuala_Lumpur';
    Promise.all([fetch(f).then(function(r){return r.ok?r.json():null;}).catch(function(){return null;}),fetch(a).then(function(r){return r.ok?r.json():null;}).catch(function(){return null;})]).then(function(r){if(r[0]&&r[0].current){WX={f:r[0],a:r[1]};applyWx();} });
  }
  function applyWx(){
    if(!WX)return;var c=WX.f.current,night=!c.is_day,w=wmo(c.weather_code,night),$=function(id){return document.getElementById(id);};
    if($('wxIco'))$('wxIco').textContent=w[0];
    if($('wxTemp'))$('wxTemp').innerHTML=Math.round(c.temperature_2m)+'°<span style="font-size:1.5rem;font-weight:400">c</span>';
    if($('wxFeels'))$('wxFeels').textContent='Feels like '+Math.round(c.apparent_temperature)+'°C';
    if($('wxCond'))$('wxCond').textContent=w[1];
    if($('ws0'))$('ws0').innerHTML='💧 '+Math.round(c.relative_humidity_2m)+'%';
    if($('ws1'))$('ws1').innerHTML='🌬 '+Math.round(c.wind_speed_10m)+' km/h';
    var ac=WX.a&&WX.a.current;
    if(ac&&$('ws2')&&ac.uv_index!=null)$('ws2').innerHTML='☀️ UV '+Math.round(ac.uv_index);
    if(ac&&$('ws3')&&ac.us_aqi!=null)$('ws3').innerHTML='<span class="aqi">AQI '+Math.round(ac.us_aqi)+' · '+aqiLbl(ac.us_aqi)+'</span>';
    var dl=WX.f.daily;if(dl&&$('ws4'))$('ws4').innerHTML='🌅 '+hm(dl.sunrise[0])+' · 🌇 '+hm(dl.sunset[0]);
    var hr=WX.f.hourly,he=$('wxHourly');
    if(hr&&he){var nowIso=c.time,start=0,i,out=[];for(i=0;i<hr.time.length;i++){if(hr.time[i]>=nowIso.slice(0,13)){start=i;break;} }
      for(i=start;i<hr.time.length&&out.length<6;i+=3){var h=+hr.time[i].slice(11,13),nt=h<7||h>=19,ww=wmo(hr.weather_code[i],nt);out.push('<div class="wx-hr"><div class="wx-hr-t">'+(((h%12)||12)+(h>=12?'PM':'AM'))+'</div><div class="wx-hr-i">'+ww[0]+'</div><div class="wx-hr-d">'+Math.round(hr.temperature_2m[i])+'°</div></div>');}
      he.innerHTML=out.join('');}
    if($('wxAdvisory')&&$('wxAdvisory').getAttribute('data-live')!=='1'){$('wxAdvisory').setAttribute('data-live','1');$('wxAdvisory').textContent='Live weather for your area · Open-Meteo';}
  }
  setTimeout(loadWx,1500);setInterval(loadWx,20*60000);
  var st3=document.createElement('style');st3.textContent='.pm-head{font-size:.72rem;font-weight:800;letter-spacing:1px;text-transform:uppercase;color:var(--muted);margin:14px 2px 8px}.pm-card{border-left-color:#7c3aed!important}.pm-tonight{background:#7c3aed;color:#fff;border-radius:100px;padding:3px 10px;font-size:.66rem;font-weight:800;letter-spacing:.5px}.pm-soon{background:rgba(124,58,237,.12);color:#5b21b6;border-radius:100px;padding:3px 10px;font-size:.66rem;font-weight:700}.pm-day{background:var(--bg2,#f2ece6);color:var(--muted);border-radius:100px;padding:3px 10px;font-size:.66rem;font-weight:700}';document.head.appendChild(st3);
})();
