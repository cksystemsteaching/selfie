/* ============================================================
   The selfie class decks — shared engine
   One deck is one index.html holding nothing but its slides:

     <link rel="stylesheet" href="../../deck/deck.css">
     <div id="stage"><div id="deck" tabindex="0"
          data-title="ICS 02 · Size" data-figures="../../../figures/">
       <section class="slide" data-act="0" data-mins="1"> … </section>
       <section class="slide" data-act="I" data-actname="Size" …> … </section>
     </div></div>
     <script src="../../deck/deck.js"></script>

   The engine supplies the rest: the rail with the act name and the clock,
   the progress bar, the footer, the nav buttons, the notes panel and the
   key list. Act names are read off the slides (the first slide of an act
   that carries data-actname), the title off #deck, and the per-slide
   minute budget in data-mins is what the clock counts down.

   Figures: <div class="fig grow" data-fig="bits"><span class="cap">…</span></div>
   fetches docs/figures/bits.svg, strips its standalone stylesheet so the
   deck's tokens apply, and inlines it. Groups marked <g class="f"
   data-step="n"> inside the figure build with the slide's other fragments.
   If the file cannot be fetched (a file:// URL in a browser that forbids
   it) the figure is shown as an <img> instead, complete but unbuilt.

   index.html?print lays the deck out as pages for make-pdf.sh, and
   ?theme=light|dark fixes the theme.
   ============================================================ */
(() => {
"use strict";
const $  = (s,r=document)=>r.querySelector(s);
const $$ = (s,r=document)=>[...r.querySelectorAll(s)];
const deck = $("#deck"), stage = $("#stage");
const slides = $$(".slide");
const reduce = matchMedia("(prefers-reduced-motion: reduce)").matches;
const TITLE = deck.dataset.title || document.title || "";
const FIG = deck.dataset.figures || "../../../figures/";
const esc = s => s.replace(/&/g,"&amp;").replace(/</g,"&lt;");

/* ---------- chrome: injected, so a deck file holds only its slides ---------- */
deck.insertAdjacentHTML("afterbegin",
  '<div id="rail" aria-hidden="true"><span id="actname"></span><span class="sp"></span><span id="clock">—</span></div>'+
  '<div id="bar" aria-hidden="true"></div>'+
  '<div id="foot" aria-hidden="true"><span>'+esc(TITLE)+'</span><span id="pageno"></span><span class="sp"></span></div>');
deck.insertAdjacentHTML("beforeend",
  '<div class="nav">'+
  '<button id="bPrev" title="Previous (←)">←</button>'+
  '<button id="bNext" title="Next (→ or space)">→</button>'+
  '<button id="bNotes" title="Speaker notes (n)">notes</button>'+
  '<button id="bHelp" title="Keys (?)">?</button></div>');
document.body.insertAdjacentHTML("beforeend",
  '<div id="notes" aria-live="polite"><h5>Speaker notes</h5><div id="notesBody"></div></div>'+
  '<div id="help"><div class="box"><h5>Keys</h5><dl>'+
  '<dt>→ · space</dt><dd>next step / slide</dd>'+
  '<dt>←</dt><dd>back</dd>'+
  '<dt>↓ · ↑</dt><dd>next / previous slide, skipping steps</dd>'+
  '<dt>home · end</dt><dd>first / last slide</dd>'+
  '<dt>n</dt><dd>speaker notes</dd>'+
  '<dt>t</dt><dd>start / pause the clock</dd>'+
  '<dt>r</dt><dd>reset the clock</dd>'+
  '<dt>d</dt><dd>toggle light / dark</dd>'+
  '<dt>? · esc</dt><dd>this panel</dd>'+
  '</dl></div></div>');

/* ---------- unit fitting: 1u = deck width / 100 ---------- */
function fit(){
  if(deck.classList.contains("printing")) return;   /* pages, not a viewport */
  const pad = 0.985;
  const w = stage.clientWidth*pad, h = stage.clientHeight*pad;
  const u = Math.min(w/100, h/56.25);
  deck.style.setProperty("--u0", u+"px");
  sizeCanvases();
}

/* Slides are authored on a fixed 100 x 56.25 u grid, but how tall the text
   actually runs depends on which of the fallback fonts a machine has. Where a
   slide would overflow its bottom padding — printing over the progress bar and
   the footer — shrink that one slide's unit until it fits. Every length in a
   slide is a multiple of --u, so this is a pure scale: nothing re-wraps. */
function autofit(){
  deck.classList.add("measuring");
  slides.forEach(s=>{
    s.style.removeProperty("--k");
    let k = 1;
    for(let pass=0; pass<5; pass++){
      const cs = getComputedStyle(s), r = s.getBoundingClientRect();
      const top = r.top + parseFloat(cs.paddingTop), limit = r.bottom - parseFloat(cs.paddingBottom);
      let bottom = top;
      (function walk(node){               /* in-flow content only */
        for(const e of node.children){
          if(e instanceof SVGElement) continue;   /* a figure's box is what counts, not its parts */
          const es = getComputedStyle(e);
          if(es.position === "absolute" || es.position === "fixed" || es.display === "none") continue;
          const b = e.getBoundingClientRect();
          if(b.height > .5 && b.bottom > bottom) bottom = b.bottom;
          walk(e);
        }
      })(s);
      const need = bottom - top, avail = limit - top;
      if(need <= avail + .5) break;
      k = Math.max(.7, k * avail/need * .996);
      s.style.setProperty("--k", k.toFixed(4));
    }
  });
  deck.classList.remove("measuring");
}

let refit = null;
addEventListener("resize", ()=>{
  fit();
  clearTimeout(refit);
  refit = setTimeout(()=>{ autofit(); sizeCanvases(); }, 180);
});

/* ---------- theme-aware palette for the one canvas figure ---------- */
let C = {};
function palette(){
  const cs = getComputedStyle(deck);
  const g = n => cs.getPropertyValue(n).trim();
  C = { ink:g("--ink"), ink2:g("--ink-2"), muted:g("--muted"), line:g("--line"),
        syn:g("--syn"), sem:g("--sem"), bad:g("--bad"), panel:g("--panel"),
        ground:g("--ground"), mono:g("--mono") };
}
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", palette);
new MutationObserver(palette).observe(document.documentElement,{attributes:true,attributeFilter:["data-theme"]});

/* ---------- steps ---------- */
function steps(){
  slides.forEach(s=>{
    const st = $$(".f",s).map(f=>+(f.dataset.step||1));
    s._max = st.length ? Math.max(...st) : 0;
    if(s._step === undefined) s._step = 0;
    if(s._step > s._max) s._step = s._max;
  });
}
steps();
let cur = 0;

function paint(){
  const s = slides[cur];
  $$(".f",s).forEach(f=>f.classList.toggle("shown", (+(f.dataset.step||1)) <= s._step));
}
let hideT = null;
function show(i, dir=1){
  i = Math.max(0, Math.min(slides.length-1, i));
  if(i===cur){ paint(); return; }
  const old = slides[cur];
  old.classList.remove("on"); old.classList.toggle("out", dir>0);
  cur = i;
  const s = slides[cur];
  s.classList.remove("out", "gone"); s.classList.add("on");
  clearTimeout(hideT);
  hideT = setTimeout(()=>slides.forEach(x=>{ if(x!==slides[cur]) x.classList.add("gone"); }), 340);
  if(s._step===0 && s._max>0 && reduce) s._step = s._max;
  paint(); chrome(); startAnims();
}
function next(){
  const s = slides[cur];
  if(s._step < s._max && !reduce){ s._step++; paint(); return; }
  if(cur < slides.length-1) show(cur+1,1);
}
function prev(){
  const s = slides[cur];
  if(s._step > 0 && !reduce){ s._step--; paint(); return; }
  if(cur > 0){ const t = slides[cur-1]; t._step = t._max; show(cur-1,-1); }
}

/* ---------- chrome: acts, bar, notes, clock ---------- */
const ACTS = [];
slides.forEach(s=>{
  const a = s.dataset.act; if(a === undefined) return;
  let e = ACTS.find(x=>x[0]===a);
  if(!e){ e = [a, a==="0" ? "Prologue" : ""]; ACTS.push(e); }
  if(!e[1] && s.dataset.actname) e[1] = s.dataset.actname;
});
const actOf = s => s.dataset.act;
const bar = $("#bar");
ACTS.forEach(([id])=>{
  const n = slides.filter(s=>actOf(s)===id).length || 1;
  const seg = document.createElement("div");
  seg.className = "seg"; seg.style.flex = n; seg.dataset.act = id;
  seg.innerHTML = "<i></i>"; bar.appendChild(seg);
});
const actLabel = a => {
  const meta = ACTS.find(x=>x[0]===a) || ["",""];
  return a==="0" ? esc(meta[1]||"Prologue") : esc(a)+" <b>·</b> "+esc(meta[1]);
};
function chrome(){
  const s = slides[cur], a = actOf(s);
  $("#actname").innerHTML = a===undefined ? "" : actLabel(a);
  $("#pageno").textContent = String(cur+1).padStart(2,"0")+" / "+slides.length;
  $$("#bar .seg").forEach(seg=>{
    const list = slides.filter(x=>actOf(x)===seg.dataset.act);
    const idx = list.indexOf(s);
    const done = slides.indexOf(list[list.length-1]) < cur;
    seg.classList.toggle("cur", idx>=0);
    seg.querySelector("i").style.transform =
      "scaleX("+(done?1:(idx>=0 ? (idx+1)/list.length : 0))+")";
  });
  const n = $(".notes", s);
  $("#notesBody").innerHTML = n ? n.innerHTML : "<p>—</p>";
}

/* clock: the deck is not pinned to a fixed length. The target is whatever the
   per-slide data-mins budget adds up to, so slides can be added or cut and the
   clock — and the pace warnings — follow the plan instead of contradicting it. */
let t0=null, acc=0, running=false;
const plan = slides.map(s=>+(s.dataset.mins||1));
const cumPlan = plan.reduce((a,v)=>(a.push((a[a.length-1]||0)+v),a),[]);
const TOTAL = (cumPlan[cumPlan.length-1]||0)*60;
function elapsed(){ return acc + (running && t0!==null ? (performance.now()-t0)/1000 : 0); }
function tick(){
  const e = elapsed(), left = TOTAL - e, el = $("#clock");
  const m = Math.floor(Math.abs(left)/60), s = Math.floor(Math.abs(left)%60);
  el.textContent = (left<0?"-":"") + m + ":" + String(s).padStart(2,"0");
  const target = (cumPlan[cur]||0)*60;
  el.classList.toggle("warn", running && e > target + 60);
  el.classList.toggle("late", running && e > target + 180);
}
const clockTimer = setInterval(tick, 500); tick();

/* ---------- input ---------- */
const KEY = {
  ArrowRight:next, " ":next, PageDown:next, Enter:next,
  ArrowLeft:prev, PageUp:prev, Backspace:prev,
  ArrowDown:()=>show(cur+1,1), ArrowUp:()=>show(cur-1,-1),
  Home:()=>show(0,-1), End:()=>show(slides.length-1,1),
  n:()=>$("#notes").classList.toggle("on"),
  t:()=>{ if(running){ acc=elapsed(); running=false; t0=null; } else { t0=performance.now(); running=true; } tick(); },
  r:()=>{ acc=0; t0=running?performance.now():null; tick(); },
  d:()=>{ const r=document.documentElement;
          const dark = getComputedStyle(deck).getPropertyValue("--ink").trim().startsWith("#E");
          r.dataset.theme = dark ? "light" : "dark"; },
  "?":()=>$("#help").classList.toggle("on"),
  Escape:()=>{ $("#help").classList.remove("on"); }
};
addEventListener("keydown", e=>{
  const f = KEY[e.key];
  if(f){ e.preventDefault(); f(); }
}, {passive:false});
$("#bNext").onclick = next; $("#bPrev").onclick = prev;
$("#bNotes").onclick = ()=>$("#notes").classList.toggle("on");
$("#bHelp").onclick  = ()=>$("#help").classList.toggle("on");
$("#help").onclick   = ()=>$("#help").classList.remove("on");
deck.addEventListener("click", e=>{ if(e.target.closest("button")) return;
  const r = deck.getBoundingClientRect();
  (e.clientX - r.left)/r.width < .22 ? prev() : next(); });
deck.focus();

/* ---------- figures: SVG files, fetched and inlined ---------- */
const figLoads = [];
$$(".fig[data-fig]").forEach(f=>{
  const name = f.dataset.fig, url = FIG + name + ".svg";
  const place = el => f.insertBefore(el, f.firstChild);
  const p = fetch(url)
    .then(r=>{ if(!r.ok) throw new Error(r.status); return r.text(); })
    .then(text=>{
      const doc = new DOMParser().parseFromString(text, "image/svg+xml");
      const svg = doc.documentElement;
      if(svg.nodeName !== "svg") throw new Error("not svg");
      $$("style", svg).forEach(x=>x.remove());
      svg.removeAttribute("width"); svg.removeAttribute("height");
      svg.setAttribute("preserveAspectRatio", "xMidYMid meet");
      svg.setAttribute("role", "img");
      place(document.importNode(svg, true));
    })
    .catch(()=>{
      const img = document.createElement("img");
      img.src = url; img.alt = name; place(img);
    });
  figLoads.push(p);
});
const figuresReady = Promise.all(figLoads).then(()=>{ steps(); paint(); autofit(); });

/* ================= the one canvas figure: the ambient title ================= */
const ANIM = {};
const canvases = ()=>$$("canvas[data-anim]", slides[cur]);
function sizeCanvases(){
  const printing = deck.classList.contains("printing");
  $$("canvas[data-anim]").forEach(c=>{
    const dpr = printing ? 2 : Math.min(2, devicePixelRatio||1);
    const w = c.clientWidth, h = c.clientHeight;
    if(!w||!h) return;
    c.width = Math.round(w*dpr); c.height = Math.round(h*dpr);
    c._dpr = dpr;
  });
}
let raf=null, tStart=0;
function startAnims(){
  tStart = performance.now();
  if(raf) cancelAnimationFrame(raf);
  sizeCanvases();
  const loop = ()=>{
    const s = slides[cur], t = (performance.now()-tStart)/1000;
    canvases().forEach(c=>{
      const fn = ANIM[c.dataset.anim]; if(!fn) return;
      const ctx = c.getContext("2d"), d = c._dpr||1;
      ctx.setTransform(d,0,0,d,0,0);
      ctx.clearRect(0,0,c.clientWidth,c.clientHeight);
      ctx.globalAlpha = 1;
      try{ fn(ctx, c.clientWidth, c.clientHeight, s._step, reduce?3:t); }
      catch(err){ /* a bad frame must never take the deck down */ }
    });
    raf = requestAnimationFrame(loop);
  };
  loop();
}
const rnd = seed => ()=> (seed = (seed*1103515245 + 12345) & 0x7fffffff)/0x7fffffff;
function txt(ctx, s, x, y, {size=13, col=C.muted, font=C.mono, align="left"}={}){
  ctx.fillStyle=col; ctx.textAlign=align; ctx.textBaseline="middle";
  ctx.font = "400 "+size+"px "+font; ctx.fillText(s,x,y);
}
/* drifting bits and a diagonal sweep, for a title or closing slide */
ANIM.ambient = (ctx,w,h,st,t)=>{
  const r = rnd(7), N = 150;
  for(let i=0;i<N;i++){
    const bx = r()*w, by = r()*h, sp = .12+r()*.5, ph = r()*10;
    const y = (by + t*sp*14) % (h+20) - 10;
    ctx.globalAlpha = .07 + .16*(0.5+0.5*Math.sin(t*.7+ph));
    txt(ctx, r()>.5?"1":"0", bx, y, {size: 9+r()*7, col: C.sem});
  }
  ctx.globalAlpha = 1;
  const cl = v => v<0?0 : v>1?1 : v;
  const p = (t*.11)%1.6 - .3;
  const g = ctx.createLinearGradient(0,0,w,h);
  g.addColorStop(cl(p-.14),"transparent");
  g.addColorStop(cl(p), C.sem);
  g.addColorStop(cl(p+.14),"transparent");
  ctx.globalAlpha=.13; ctx.strokeStyle=g; ctx.lineWidth=1;
  for(let k=-1;k<2;k++){ ctx.beginPath(); ctx.moveTo(0, h*k); ctx.lineTo(w, h*(k+1)); ctx.stroke(); }
  ctx.globalAlpha=1;
};

/* ---------- print layout ---------- */
function printLayout(){
  if(raf) cancelAnimationFrame(raf);
  clearInterval(clockTimer);
  deck.classList.add("printing");
  deck.classList.remove("measuring");
  deck.style.setProperty("--u0", "16px");
  slides.forEach((s,i)=>{
    s.classList.remove("on","out","gone");
    s._step = s._max;
    const a = actOf(s);
    const top = document.createElement("div");
    top.className = "pchrome top";
    top.innerHTML = (a===undefined ? "" : actLabel(a)) + '<span class="sp"></span>';
    const bot = document.createElement("div");
    bot.className = "pchrome bot";
    bot.innerHTML = esc(TITLE)+'<span class="n">· '+
      String(i+1).padStart(2,"0")+" / "+slides.length+'</span><span class="sp"></span>';
    s.append(top, bot);
    $$(".f", s).forEach(f=>f.classList.add("shown"));
  });
  autofit();
  sizeCanvases();
  $$("canvas[data-anim]").forEach(c=>{
    const fn = ANIM[c.dataset.anim]; if(!fn) return;
    const ctx = c.getContext("2d"), d = c._dpr||1;
    ctx.setTransform(d,0,0,d,0,0);
    ctx.clearRect(0,0,c.clientWidth,c.clientHeight);
    const s = c.closest(".slide");
    try{ fn(ctx, c.clientWidth, c.clientHeight, s ? s._max : 0, 3); }catch(err){}
  });
  document.documentElement.dataset.printReady = "1";
}

/* ---------- boot ---------- */
palette(); fit(); autofit(); sizeCanvases();
slides.forEach((s,i)=>{ s.classList.toggle("on", i===0); s.classList.toggle("gone", i!==0); });
if(reduce) slides.forEach(s=>s._step=s._max);
chrome(); paint(); startAnims(); tick();
window.__deck = {show, next, prev, slides, printLayout, ANIM, figuresReady};
const q = new URLSearchParams(location.search);
if(q.has("theme")) document.documentElement.dataset.theme = q.get("theme");
if(q.has("print")) figuresReady.then(printLayout);
})();
