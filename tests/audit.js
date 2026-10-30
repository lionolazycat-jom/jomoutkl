// JomOutKL automatic site audit. Run: node tests/audit.js  (needs: npm i playwright)
const {chromium}=require('playwright');const http=require('http'),fs=require('fs'),path=require('path');
const root=path.resolve(__dirname,'..');
const srv=http.createServer((q,r)=>{let f=q.url.split('?')[0];if(f.endsWith('/'))f+='index.html';try{r.end(fs.readFileSync(root+f))}catch(e){r.statusCode=404;r.end()}}).listen(0);
const fails=[];const F=(m)=>{fails.push(m);console.log('FAIL',m)};
const kl=new Date(Date.now()+8*3600e3).toISOString().slice(0,10);
const TIMES=[kl+'T08:00',kl+'T14:30',kl+'T23:30'];
const BAD=/undefined|NaN|\[object|Invalid Date|\bnull\b/;
const BANNED=/genting|casino|toto|magnum|betting|lottery/i;
(async()=>{const b=await chromium.launch();
for(const when of TIMES){
 const c=await b.newContext({geolocation:{latitude:3.1337,longitude:101.7120},permissions:['geolocation'],viewport:{width:390,height:844},timezoneId:'Asia/Kuala_Lumpur'});
 const p=await c.newPage();const L='['+when.slice(11)+'] ';
 p.on('pageerror',e=>F(L+'page error: '+e.message));
 p.on('console',m=>{if(m.type()==='error'&&!/zgo|waze|fonts|ERR_|Failed to load resource/.test(m.text()))F(L+'console error: '+m.text().slice(0,120))});
 const d=when.slice(0,10),H=+when.slice(11,13);
 await p.route(/open-meteo/,rt=>{const air=rt.request().url().includes('air-quality');const T=[],P=[],W=[],TT=[];for(let i=0;i<168;i++){T.push(new Date(Date.parse(d+'T00:00:00Z')+i*3600e3).toISOString().slice(0,13)+':00');P.push(10);W.push(2);TT.push(29);}
  const days=[...Array(7)].map((_,i)=>new Date(Date.parse(d)+i*864e5).toISOString().slice(0,10));
  rt.fulfill({status:200,contentType:'application/json',headers:{'access-control-allow-origin':'*'},body:JSON.stringify(air?{current:{us_aqi:62,uv_index:5}}:{current:{temperature_2m:31,apparent_temperature:37,weather_code:2,relative_humidity_2m:70,wind_speed_10m:8},hourly:{time:T,temperature_2m:TT,precipitation_probability:P,weather_code:W,apparent_temperature:TT},daily:{time:days,sunrise:days.map(x=>x+'T07:08'),sunset:days.map(x=>x+'T19:06'),weather_code:days.map(_=>2),temperature_2m_max:days.map(_=>33),temperature_2m_min:days.map(_=>25),precipitation_probability_max:days.map(_=>40)}})})});
 await p.route(/fonts\.|zgo\.at|waze/,rt=>rt.abort());
 await p.clock.install({time:new Date(when+'+08:00')});
 await p.goto('http://localhost:'+srv.address().port+'/');await p.clock.runFor(3000);await p.waitForTimeout(1500);
 const gen=async(label)=>{const r=await p.evaluate(()=>({t:document.body.innerText,ov:document.documentElement.scrollWidth>innerWidth+1,imgs:[...document.images].filter(i=>i.complete&&i.naturalWidth===0).length}));
  if(BAD.test(r.t))F(L+label+': shows "'+(r.t.match(BAD)||[])[0]+'"');if(r.ov)F(L+label+': sideways scroll');if(r.imgs)F(L+label+': '+r.imgs+' broken image(s)');if(BANNED.test(r.t))F(L+label+': banned word on page: '+(r.t.match(BANNED)||[])[0]);};
 await gen('landing');
 for(const t of ['about','food','events','transit','explore']){const el=await p.$('#tabs [data-tab="'+t+'"]');if(!el){F(L+'missing tab '+t);continue;}await el.click();await p.waitForTimeout(300);await gen('tab '+t);}
 // events: every card has a time tag; at least one event overall
 await p.click('#tabs [data-tab="events"]');await p.waitForTimeout(300);
 const evc=await p.$$eval('#p-events .card.it',x=>x.map(e=>({n:e.querySelector('.n').textContent,tags:e.querySelector('.tags').textContent})));
 if(evc.length<1)F(L+'no events shown');evc.forEach(e=>{if(!/\d{1,2}:\d\d|Time:/i.test(e.tags))F(L+'event without time label: '+e.n)});
 // food: every meal list has no duplicate names, late night has no unconfirmed hours
 await p.click('#tabs [data-tab="food"]');
 for(const m of await p.$$eval('#meals .chip',x=>x.map(e=>e.dataset.m))){await p.click('#meals [data-m="'+m+'"]');await p.waitForTimeout(250);await gen('meal '+m);
  if(['markets','tourist'].includes(m))continue;
  const names=await p.$$eval('#eat .card.it',x=>x.map(e=>e.querySelector('.n').textContent.trim().toLowerCase()));
  names.forEach((n,i)=>{if(names.indexOf(n)!==i)F(L+m+': duplicate '+n)});
  if(m==='supper'){const hn=await p.$$eval('#eat .card.it',x=>x.filter(e=>/Hours not listed/i.test(e.querySelector('.tags').textContent)&&!/mamak|nasi kandar|24|lok lok|bak kut teh|tomyam|satay|steamboat|dim sum|roti/i.test(e.textContent)).map(e=>e.querySelector('.n').textContent));
   hn.forEach(n=>F(L+'late night shows unconfirmed hours: '+n));}}
 // tourist picks count
 await p.click('#meals [data-m="tourist"]');await p.waitForTimeout(250);const tc=await p.$$eval('#tour .card.it',x=>x.length);if(tc<25)F(L+'tourist picks only '+tc);
 await c.close();}
await b.close();srv.close();
// data.json sanity
try{let s=fs.readFileSync(root+'/data.json','utf8').trim().replace(/^```json/,'').replace(/```$/,'');const j=JSON.parse(s);const ev=(j.modules||{}).events||[];
 if(ev.length<5)F('data.json has only '+ev.length+' events');
 const ageH=(Date.now()-Date.parse(j.events_checked_at||j.generated_at||0))/36e5;if(!(ageH<30))F('data.json is '+Math.round(ageH)+' hours old (daily run may have failed)');}catch(e){F('data.json unreadable: '+e.message)}
console.log(fails.length?fails.length+' problem(s)':'All checks passed');process.exit(fails.length?1:0);})();
