/* Home page: featured problems, the pipeline figure, BibTeX. */
function drawThumbs() {
  document.querySelectorAll("canvas[data-thumb]").forEach(async c => {
    const p = PROBLEMS.find(x => x.id === c.dataset.thumb); if (!p) return;
    const d = await getDag(p), w = c.clientWidth, h = c.clientHeight, dpr = devicePixelRatio || 1;
    if (!w) return;
    c.width = w * dpr; c.height = h * dpr; const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0);
    let slot = 0; const live = [];
    const walk = n => { live.push(n); const ks = n.tk.filter(k => !k.ab); if (!ks.length) n._hx = slot++; else { ks.forEach(walk); n._hx = (ks[0]._hx + ks[ks.length - 1]._hx) / 2; } };
    walk(d.root);
    const sx = (w - 24) / Math.max(1, slot - 1), sy = (h - 20) / Math.max(1, d.stats.depth);
    const X = n => 12 + n._hx * sx, Y = n => 10 + n.depth * sy;
    g.lineWidth = .6; g.globalAlpha = .35;
    for (const n of live) if (n.tp) { g.strokeStyle = branchColor(n); g.beginPath(); g.moveTo(X(n.tp), Y(n.tp)); g.lineTo(X(n), Y(n)); g.stroke(); }
    g.globalAlpha = 1;
    for (const n of live) { g.fillStyle = branchColor(n); g.beginPath(); g.arc(X(n), Y(n), n === d.root ? 3.5 : n.kind === "composite" ? 1.6 : 1.1, 0, 7); g.fill(); }
  });
}
addEventListener("resize", () => { clearTimeout(drawThumbs.t); drawThumbs.t = setTimeout(drawThumbs, 200); });
/* ---------- copy bibtex ---------- */
$("#copyBib").addEventListener("click", async () => {
  const b = $("#copyBib");
  try { await navigator.clipboard.writeText($("#bibtex").textContent); b.textContent = "Copied"; }
  catch (e) { const r = document.createRange(); r.selectNodeContents($("#bibtex")); const s = getSelection(); s.removeAllRanges(); s.addRange(r); b.textContent = "Selected"; }
  setTimeout(() => b.textContent = "Copy", 1600);
});


/* ---------- how-it-works figure ---------- */
// Each step lists the highlighted parts, the active edges, how many copies of a subagent run,
// and DAG node states (applied cumulatively). Plain CSS transitions, no moving parts.
const PIPE = [
  { on: ["cli"], dag: { T: "open" }, cap: "LEAP-CLI holds the proof DAG. It starts with one open node: the theorem." },
  { on: ["orch", "cli"], ed: ["e-claim"], dag: { T: "proc" }, cap: "The orchestrator claims the next open work from the CLI." },
  { on: ["orch", "inf"], ed: ["e-l1"], par: { inf: 1 }, cap: "It launches an informal prover, which writes a proof sketch and the lemmas it needs." },
  { on: ["inf", "gate"], ed: ["e-s1"], dag: { A: "open", B: "open", C: "open" }, cap: "The sketch is submitted to the CLI. It passes the Lean compiler gate, and its lemmas enter the DAG." },
  { on: ["orch", "frm"], ed: ["e-claim", "e-l2"], par: { frm: 3 }, dag: { A: "proc", B: "proc", C: "proc" }, cap: "The orchestrator claims all three lemmas and launches three formal provers at once." },
  { on: ["frm", "gate"], ed: ["e-s2"], par: { frm: 3 }, dag: { A: "ok", C: "ok", B: "open", GX: "on" }, cap: "Each proof is submitted. Two compile and enter the graph. One does not, and the gate turns it away." },
  { on: ["orch", "inf", "frm", "gate"], ed: ["e-l1", "e-l2", "e-s1", "e-s2"], par: { inf: 1, frm: 2 }, dag: { GX: "off", B: "ok", B1: "ok", B2: "ok" }, cap: "The failed lemma is tried again with a smaller split. Both new lemmas pass the gate." },
  { on: ["orch", "rev", "gate"], ed: ["e-l3", "e-s3"], par: { rev: 1 }, dag: { C: "redo" }, cap: "A reviewer re-checks what is already in the graph. It finds base_case too weak, so that node is reopened." },
  { on: ["frm", "gate", "cli"], ed: ["e-l2", "e-s2"], par: { frm: 1 }, dag: { C: "ok", T: "ok" }, cap: "base_case is proved again, every node is closed, and the full proof compiles." }
];
const pipe = { i: 0, timer: 0, started: false };
function pipeShow(k) {
  pipe.i = (k + PIPE.length) % PIPE.length;
  const st = PIPE[pipe.i], dag = {};
  for (let s = 0; s <= pipe.i; s++) Object.assign(dag, PIPE[s].dag || {});
  const ed = new Set(st.ed || []), par = st.par || {};
  document.querySelectorAll("#pipe .st").forEach(g => g.classList.toggle("on", st.on.includes(g.dataset.st)));
  document.querySelectorAll("#pipe .ed").forEach(p => p.classList.toggle("on", ed.has(p.id)));
  document.querySelectorAll("#pipe [data-par]").forEach(t => { const n = par[t.dataset.par]; t.textContent = n ? `×${n} running` : ""; });
  document.querySelectorAll("#pipe .sub").forEach(g => g.classList.toggle("multi", (par[g.dataset.st] || 0) > 1));
  document.querySelectorAll("#pipe [data-d]").forEach(g => g.setAttribute("class", "dn " + (dag[g.dataset.d] || "off")));
  $("#pCap").innerHTML = `<span class="pn">${pipe.i + 1} / ${PIPE.length}</span>${st.cap}`;
  $("#pDots").innerHTML = PIPE.map((_, j) => `<button type="button" aria-label="Step ${j + 1}" class="${j === pipe.i ? "on" : ""}" data-p="${j}"></button>`).join("");
}
// Each step holds 3.2 s; the last one holds 5 s longer before the next round starts.
function pipeRun(on) {
  clearTimeout(pipe.timer);
  if (!on || reduced()) return;
  const wait = pipe.i === PIPE.length - 1 ? 8200 : 3200;
  pipe.timer = setTimeout(() => { pipeShow(pipe.i + 1); pipeRun(true); }, wait);
}
function initPipeline() {
  pipeShow(0);
  $("#pDots").addEventListener("click", e => { const b = e.target.closest("[data-p]"); if (b) { pipeShow(+b.dataset.p); pipeRun(true); } });
  // Play only while the figure is on screen.
  if ("IntersectionObserver" in window) {
    new IntersectionObserver(([en]) => {
      if (en.isIntersecting) { if (!pipe.started) { pipe.started = true; pipeShow(0); } pipeRun(true); }
      else pipeRun(false);
    }, { threshold: .55 }).observe($("#pipe"));
  }
}

/* ---------- headline sentence, computed from the problem files ---------- */
function renderHeadline() {
  const maxLoc = Math.max(0, ...PROBLEMS.map(p => p.loc || 0));
  const maxDag = Math.max(0, ...PROBLEMS.map(p => p.dag_lemmas || 0));
  const num = (v, unit) => `<span class="hn">${v}</span> ${unit}`;
  const parts = [num(PROBLEMS.length, "open problems solved")];
  if (maxLoc) parts.push(num(maxLoc >= 20000 ? kloc(maxLoc) : fmt(maxLoc), "lines in the longest proof"));
  if (maxDag) parts.push(num(fmt(maxDag), "lemmas in the largest proof DAG"));
  $("#headline").innerHTML = parts.map(x => `<span class="hp">${x}</span>`).join("");
}

/* ---------- featured problems, with the rest one click away ---------- */
function cardHTML(p, small) {
  return `<a class="fcard${small ? " small" : ""}" href="${problemUrl(p)}">
    ${small ? "" : `<canvas data-thumb="${esc(p.id)}" aria-hidden="true"></canvas>`}
    <div class="fb"><div class="fa">${esc(p.area || p.collection)}</div><div class="ft">${titleHTML(p)}</div>${p.subtitle && !small ? `<div class="fs">${esc(p.subtitle)}</div>` : ""}
    <p class="fsum">${md(p.summary)}</p>
    <div class="ff"><span class="loc">${p.loc ? (p.loc >= 20000 ? "~" + kloc(p.loc) : fmt(p.loc)) : ""}<small>${p.loc ? "lines of Lean" : ""}</small></span><span class="go">Open →</span></div></div></a>`;
}
/* Every featured problem goes in the carousel; three are in view at a time. */
function renderFeatured() {
  const f = PROBLEMS.filter(p => p.featured), track = $("#feat");
  track.innerHTML = f.map(p => cardHTML(p)).join("");
  $("#carDots").innerHTML = f.map((p, i) => `<button type="button" data-i="${i}" aria-label="Show ${esc(p.title)}"></button>`).join("");
  drawThumbs(); syncCar();
}
function carStep() { const c = $("#feat").children[0]; return c ? c.getBoundingClientRect().width + 14 : 0; }
function syncCar() {
  const t = $("#feat"), max = t.scrollWidth - t.clientWidth - 2;
  $("#carPrev").disabled = t.scrollLeft <= 2; $("#carNext").disabled = t.scrollLeft >= max;
  $("#car").classList.toggle("static", max <= 0);
  const first = Math.round(t.scrollLeft / (carStep() || 1));
  const shown = Math.max(1, Math.round(t.clientWidth / (carStep() || 1)));
  [...$("#carDots").children].forEach((d, i) => d.classList.toggle("on", i >= first && i < first + shown));
}
$("#carPrev").addEventListener("click", () => $("#feat").scrollBy({ left: -carStep(), behavior: reduced() ? "auto" : "smooth" }));
$("#carNext").addEventListener("click", () => $("#feat").scrollBy({ left: carStep(), behavior: reduced() ? "auto" : "smooth" }));
$("#feat").addEventListener("scroll", () => requestAnimationFrame(syncCar), { passive: true });
$("#carDots").addEventListener("click", e => { const b = e.target.closest("[data-i]"); if (b) $("#feat").scrollTo({ left: +b.dataset.i * carStep(), behavior: reduced() ? "auto" : "smooth" }); });
addEventListener("resize", () => syncCar());
document.addEventListener("leap:theme", drawThumbs);

boot(() => { renderHeadline(); renderFeatured(); enableDrawer(); });
initPipeline();

/* copy buttons in "Run it" */
document.addEventListener("click", async e => {
  const b = e.target.closest(".cmd .copy"); if (!b) return;
  const text = b.parentElement.querySelector("pre").textContent;
  try { await navigator.clipboard.writeText(text); b.textContent = "Copied"; }
  catch (err) { const r = document.createRange(); r.selectNodeContents(b.parentElement.querySelector("pre")); getSelection().removeAllRanges(); getSelection().addRange(r); b.textContent = "Selected"; }
  setTimeout(() => b.textContent = "Copy", 1500);
});
