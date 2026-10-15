/* Problem page: the problem, its informal proof, Lean proof and proof DAG explorer. */
function setSTab(s) {
  document.querySelectorAll(".stab").forEach(b => b.setAttribute("aria-selected", b.dataset.s === s));
  $("#sDag").hidden = s !== "dag"; $("#sInformal").hidden = s !== "informal"; $("#sLean").hidden = s !== "lean";
  if (s === "dag") resize();
}
/* Informal proof: Markdown with LaTeX. Math is protected from the Markdown parser, then typeset by KaTeX. */
function renderMarkdown(src) {
  const math = [];
  const keep = s => `@@MATH${math.push(s) - 1}@@`;
  src = src.replace(/\$\$[\s\S]+?\$\$/g, keep).replace(/\\\[[\s\S]+?\\\]/g, keep).replace(/(^|[^\\$])\$(?!\s)([^$\n]+?)\$/g, (m, a, b) => a + keep("$" + b + "$"));
  let html = window.marked ? marked.parse(src) : `<pre>${esc(src)}</pre>`;
  html = html.replace(/@@MATH(\d+)@@/g, (m, i) => esc(math[+i]));
  return html;
}
async function renderInformal(p) {
  const box = $("#sInformal");
  if (!hasInformal(p)) { box.innerHTML = `<div class="empty"><b>The informal proof will be published here.</b>It is still being written up for this problem.</div>`; return; }
  box.innerHTML = `<div class="empty">Loading the informal proof…</div>`;
  try {
    const src = await getText(p, "informal"); if (CUR !== p) return;
    box.innerHTML = `<div class="doc-head"><span class="mono">${esc(p.files.informal)}</span><span>${fmt(src.split("\n").length)} lines</span><a href="${esc(fileUrl(p, "informal"))}" target="_blank" rel="noopener">Open the Markdown ↗</a></div><article class="prose">${renderMarkdown(src)}</article>`;
    if (window.renderMathInElement) renderMathInElement(box.querySelector(".prose"), { delimiters: [{ left: "$$", right: "$$", display: true }, { left: "\\[", right: "\\]", display: true }, { left: "$", right: "$", display: false }], throwOnError: false });
  } catch (e) { box.innerHTML = `<div class="err">Could not load ${esc(fileUrl(p, "informal"))}.</div>`; }
}
/* Full proof: numbered, highlighted, with a jump menu built from its `theorem` lines. */
let proofIndex = null;
async function renderLean(p) {
  const box = $("#sLean"); proofIndex = null;
  if (!hasLean(p)) { box.innerHTML = `<div class="empty"><b>The Lean proof will be published here.</b>It is verified and being prepared for release.</div>`; return; }
  box.innerHTML = `<div class="empty">Loading the Lean files…</div>`;
  try {
    const stmt = p.files.statement ? await getText(p, "statement") : null;
    const proof = p.files.proof ? await getText(p, "proof") : null; if (CUR !== p) return;
    const lines = proof ? proof.split("\n") : [];
    proofIndex = new Map();
    lines.forEach((l, i) => { const m = l.match(/^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([^\s(:{\[]+)/); if (m && !proofIndex.has(m[1])) proofIndex.set(m[1], i); });
    const opts = [...proofIndex.keys()].map(k => `<option value="${esc(k)}">${esc(k)}</option>`).join("");
    box.innerHTML = (stmt ? `<h4 class="lh">The statement</h4><pre class="lean">${hl(stmt, false)}</pre>` : "") +
      (proof ? `<h4 class="lh">The verified proof <span>${fmt(lines.length)} lines · ${proofIndex.size} theorems · no sorry</span></h4>
        <div class="proof-bar"><label class="mono" for="jump">Jump to</label><select id="jump"><option value="">a theorem…</option>${opts}</select><span class="sp"></span><a class="btn" href="${esc(fileUrl(p, "proof"))}" download>Download ${esc(p.files.proof)}</a></div>
        <div class="code-view" id="proofView"></div>` : "");
    if (proof) {
      const view = $("#proofView");
      // render in chunks so a 10K-line file never blocks the page
      let i = 0; const CH = 800;
      const pump = () => { if (CUR !== p) return; const end = Math.min(lines.length, i + CH); let html = ""; for (; i < end; i++) html += `<div class="cl" id="L${i + 1}"><i>${i + 1}</i><span>${hl(lines[i], "span") || " "}</span></div>`; view.insertAdjacentHTML("beforeend", html); if (i < lines.length) requestAnimationFrame(pump); else if (pendingFind) { const n = pendingFind; pendingFind = null; findInProof(n); } };
      pump();
      $("#jump").addEventListener("change", e => { if (e.target.value) findInProof(e.target.value); });
    }
    renderSide();
  } catch (err) { box.innerHTML = `<div class="err">Could not load the Lean files for this problem.</div>`; }
}
let pendingFind = null;
function findInProof(name) {
  if (!proofIndex || !proofIndex.has(name)) return;
  closeCode(); setSTab("lean");
  const line = proofIndex.get(name) + 1, el = document.getElementById("L" + line);
  if (!el) { pendingFind = name; return; }
  const view = $("#proofView");
  view.querySelectorAll(".cl.hit").forEach(x => x.classList.remove("hit"));
  // highlight the declaration up to the next top-level line
  for (let k = line; k < line + 2000; k++) {
    const r = document.getElementById("L" + k); if (!r) break;
    const t = r.querySelector("span").textContent;
    if (k > line && t.trim() && !/^\s/.test(t) && !/^(by\b|:=|\|)/.test(t)) break;
    r.classList.add("hit");
  }
  view.scrollTop = el.offsetTop - 12;
  $("#sLean").scrollIntoView({ block: "start", behavior: reduced() ? "auto" : "smooth" });
  const j = $("#jump"); if (j) j.value = name;
}
$("#sLean").addEventListener("click", e => {
  if (e.target.closest("[data-goto]")) { setSTab("dag"); setView("outline"); return; }
  const l = e.target.closest(".ll[data-n]"); if (l && S.dag) { setSTab("dag"); select(nodeAt(l.dataset.n)); }
});

/* ---------- explorer state ---------- */
const S = { dag: null, sel: null, view: "dag", showAb: false, matches: new Set(), mlist: [], mi: 0 };
const vis = n => S.showAb || !n.ab;
const weight = n => S.showAb ? n.sca : n.sc;
const kids = n => n.tk.filter(vis);
const pathTo = n => { const p = []; for (let c = n; c; c = c.tp) p.unshift(c); return p; };
const nodeAt = i => S.dag.byI[+i];
const preview = n => n.prop || (n.statement || "").split(/:\s*\n/).pop().trim();

function loadDag(d) {
  S.dag = d; S.sel = d.root; S.matches = new Set(); S.mlist = []; $("#nsearch").value = ""; $("#nfound").textContent = "";
  popCache.clear(); expanded.clear(); bp.reset();
  const st = d.stats;
  $("#nDag").textContent = fmt(st.lemmas) + " lemmas";
  $("#xstats").innerHTML = `<span><b>${fmt(st.lemmas)}</b> lemmas</span><span><b>${fmt(st.leaves)}</b> closed directly</span><span><b>${fmt(st.shared)}</b> shared</span><span><b>${fmt(st.rejected)}</b> rejected</span><span>max depth <b>${st.depth}</b></span><span><b>${fmt(st.lines)}</b> Lean lines</span>${d.sample ? '<span class="sample">sample data</span>' : ""}`;
  bp.relayout(false); redraw(); renderSide();
}
$("#abChk").addEventListener("change", e => { if (!S.dag) return; S.showAb = e.target.checked; if (!S.showAb && S.sel && S.sel.ab) S.sel = S.sel.tp; popCache.clear(); bp.relayout(true); redraw(); renderSide(); });
document.querySelectorAll(".vtab").forEach(b => b.addEventListener("click", () => setView(b.dataset.v)));
function setView(v) {
  S.view = v; hidePop();
  document.querySelectorAll(".vtab").forEach(b => b.setAttribute("aria-selected", b.dataset.v === v));
  const dag = v === "dag";
  cv.hidden = !dag; mini.hidden = !dag; $("#dtools").hidden = !dag; $("#zoomctl").hidden = !dag; $("#hint").hidden = !dag;
  $("#outlinePane").hidden = dag;
  if (!dag && S.sel) expandPath(S.sel);
  if (dag) { resize(); if (S.dag && S.sel && S.sel !== S.dag.root) bp.focus(S.sel, true); } else redraw();
}
function select(n, from) {
  if (!n) return;
  if (n.ab && !S.showAb) { S.showAb = true; $("#abChk").checked = true; bp.relayout(false); }
  S.sel = n;
  if (S.view === "outline") expandPath(n);
  if (S.view === "dag" && from !== "dag") bp.focus(n, true);
  redraw(); renderSide();
}
$("#nsearch").addEventListener("input", e => {
  const q = e.target.value.trim().toLowerCase();
  S.mlist = q.length < 2 || !S.dag ? [] : S.dag.nodes.filter(n => vis(n) && n.name.toLowerCase().includes(q));
  S.matches = new Set(S.mlist.map(n => n.i)); S.mi = 0;
  $("#nfound").textContent = q.length < 2 ? "" : S.mlist.length ? `${S.mlist.length} found · Enter to step` : "no match";
  redraw();
});
$("#nsearch").addEventListener("keydown", e => { if (e.key === "Enter" && S.mlist.length) { e.preventDefault(); select(S.mlist[S.mi % S.mlist.length]); S.mi++; } });

/* ---------- Lean highlighting ---------- */
const KW = new Set("theorem lemma def by have exact obtain intro intros fun calc show from at with using refine apply rcases rintro constructor use cases induction let if then else match do return rfl sorry zero succ".split(" "));
const TAC = new Set("simp simp_all simpa omega norm_num linarith nlinarith ring ring_nf decide positivity aesop ext funext field_simp rw gcongr exact_mod_cast push_cast trivial only interval_cases fun_prop".split(" "));
function hl(code, links, self) {
  const re = /(--[^\n]*)|([A-Za-z_][A-Za-z0-9_.'₀-₉]*)|(\d+)|([ℕℤℝℚ]|𝓞)|([\s\S])/gu; let out = "", m;
  while ((m = re.exec(code))) {
    if (m[1]) out += `<span class="lc">${esc(m[1])}</span>`;
    else if (m[2]) {
      const w = m[2], n = S.dag && S.dag.byName.get(w);
      if (w === self) out += `<span class="lself">${esc(w)}</span>`;
      else if (n) out += links === "span" ? `<span class="ll" data-n="${n.i}">${esc(w)}</span>` : links ? `<button type="button" class="ll" data-n="${n.i}">${esc(w)}</button>` : `<span class="ll">${esc(w)}</span>`;
      else if (KW.has(w)) out += `<span class="lk">${w}</span>`;
      else if (TAC.has(w)) out += `<span class="lt">${w}</span>`;
      else if (/^[A-Z]/.test(w)) out += `<span class="ly">${esc(w)}</span>`;
      else out += esc(w);
    } else if (m[3]) out += `<span class="ln">${m[3]}</span>`;
    else if (m[4]) out += `<span class="ly">${m[4]}</span>`;
    else out += esc(m[5]);
  }
  return out;
}
const codeOf = n => n.code || n.statement || `theorem ${n.name} …`;
const stmtOf = n => n.statement || codeOf(n).split(/:=\s*by\b/)[0];
const proofLines = n => Math.max(0, codeOf(n).split("\n").length - stmtOf(n).split("\n").length);
function numbered(code, self, links = "span") {
  return code.split("\n").map((l, i) => `<div class="cl"><i>${i + 1}</i><span>${hl(l, links, self) || " "}</span></div>`).join("");
}
const codeLabel = n => n.ab ? "Rejected lemma" : n.kind === "leaf" ? "Statement and proof" : `Linking proof · compiles once its ${n.children.length} lemmas are proved`;
function badges(n) {
  const k = n.ab ? '<span class="bdg ab">rejected attempt</span>' : n.kind === "leaf" ? '<span class="bdg leaf">closed directly</span>' : '<span class="bdg">decomposed</span>';
  return k + (n.parents.length > 1 ? `<span class="bdg sh">shared · used by ${n.parents.length}</span>` : "");
}

/* ---------- hover card ---------- */
const pop = $("#pop"), popCache = new Map();
let popFor = null;
function popHTML(n) {
  if (popCache.has(n.i)) return popCache.get(n.i);
  const lines = stmtOf(n).split("\n"), MAX = 12;
  const st = lines.length > MAX ? lines.slice(0, MAX).join("\n") + "\n  …" : lines.join("\n");
  const pl = proofLines(n);
  const meta = n.ab ? "" : n.kind === "leaf" ? `${pl} proof lines` : `${fmt(n.sc - 1)} lemmas below`;
  const h = `<div class="pop-h"><span class="pop-n">${esc(n.name)}</span>${badges(n)}<span class="bdg">depth ${n.depth}</span>${meta ? `<span class="bdg">${meta}</span>` : ""}</div>
    <div class="pop-l">Statement</div><pre class="lean">${hl(st, false, n.name)}</pre>
    <div class="pop-f2">${n.ab ? esc(n.reason || "Rejected attempt") : `Click to select · ${pl} lines of ${n.kind === "leaf" ? "proof" : "sketch"} in the side panel`}</div>
    ${S.dag.sample ? '<div class="pop-f">Sample Lean. The real statement and sketch come from the export.</div>' : ""}`;
  popCache.set(n.i, h); return h;
}
function showPop(n, cx, cy) {
  if (popFor !== n) { pop.innerHTML = popHTML(n); popFor = n; }
  pop.hidden = false;
  const w = pop.offsetWidth, h = pop.offsetHeight, vw = innerWidth, vh = innerHeight;
  let x = cx + 18, y = cy + 18;
  if (x + w > vw - 8) x = cx - w - 18; if (x < 8) x = 8;
  if (y + h > vh - 8) y = cy - h - 14; if (y < 8) y = Math.max(8, vh - h - 8);
  pop.style.left = x + "px"; pop.style.top = y + "px";
}
function hidePop() { pop.hidden = true; popFor = null; }
const stage = $("#stage");
$("#outlinePane").addEventListener("pointermove", e => {
  if (e.pointerType === "touch") return;
  const g = e.target.closest("[data-n]"); if (g && S.dag) showPop(nodeAt(g.dataset.n), e.clientX, e.clientY); else hidePop();
});
stage.addEventListener("pointerleave", hidePop);
addEventListener("scroll", hidePop, { passive: true });

/* ---------- side panel ---------- */
const nodeBtn = n => `<li><button type="button" data-n="${n.i}" class="${n.ab ? "ab" : ""}">${esc(n.name)}</button></li>`;
function renderSide() {
  const n = S.sel; if (!n || !S.dag) return;
  const ch = n.children, path = pathTo(n), pl = proofLines(n), body = codeOf(n).split("\n").slice(stmtOf(n).split("\n").length);
  const kindWord = n.kind === "leaf" ? "Proof" : "Sketch";
  $("#side").innerHTML = `
    <div class="kicker">${n === S.dag.root ? "Root theorem" : "Lemma"}</div>
    <div class="nm">${esc(n.name)}</div>
    <div class="badges">${badges(n)}</div>
    <h5>Statement</h5><pre class="lean wrap">${hl(stmtOf(n), true, n.name)}</pre>
    ${n.ab && n.reason ? `<p style="font-size:12.5px;color:var(--del);margin:8px 0 0">${esc(n.reason)}</p>` : ""}
    ${pl ? `<h5>${kindWord} · ${fmt(pl)} lines${n.kind === "composite" ? ` · uses ${n.children.length} lemmas` : ""}</h5>
      <div class="peek-code"><pre class="lean">${hl(body.slice(0, 8).join("\n"), true, n.name)}</pre></div>
      <div class="side-act"><button type="button" class="btn primary" id="readCode">Read the full code</button>${proofIndex ? `<button type="button" class="btn" id="findProof">Find in the full proof</button>` : ""}</div>` : ""}
    ${n.defs ? `<details class="defs"><summary>Definitions used by this node</summary><pre class="lean wrap">${hl(n.defs, true)}</pre></details>` : ""}
    ${S.dag.sample ? '<p class="mono" style="font-size:11px;color:var(--warn);margin:8px 0 0">Sample Lean. Underlined names are lemmas you can click.</p>' : ""}
    <h5>Numbers</h5>
    <dl class="kv"><dt>Depth</dt><dd>${n.depth}</dd><dt>${kindWord} lines</dt><dd>${fmt(pl)}</dd>
    ${n.kind === "composite" ? `<dt>Lemmas below</dt><dd>${fmt(n.sc - 1)}</dd><dt>Lines below</dt><dd>${fmt(n.sl)}</dd>` : ""}
    ${n.rejected.length ? `<dt>Rejected lemmas</dt><dd>${n.rejected.length}</dd>` : ""}</dl>
    ${path.length > 1 ? `<h5>Path from root</h5><ul class="nlist">${path.slice(0, -1).map(nodeBtn).join("")}</ul>` : ""}
    ${ch.length ? `<h5>Needs (${ch.length})</h5><ul class="nlist">${ch.slice(0, 30).map(nodeBtn).join("")}</ul>` : ""}
    ${n.parents.length > 1 ? `<h5>Used by (${n.parents.length})</h5><ul class="nlist">${n.parents.map(nodeBtn).join("")}</ul>` : ""}
    ${n.rejected.length && S.showAb ? `<h5>Rejected lemmas</h5><ul class="nlist">${n.rejected.map(nodeBtn).join("")}</ul>` : ""}`;
  if (cview.open) openCode(n);
}
$("#side").addEventListener("click", e => {
  if (e.target.closest("#readCode")) return openCode(S.sel);
  if (e.target.closest("#findProof")) return findInProof(S.sel.name);
  const b = e.target.closest("[data-n]"); if (b) select(nodeAt(b.dataset.n));
});

/* ---------- full-code viewer over the explorer ---------- */
const cview = { open: false };
function openCode(n) {
  const v = $("#cview"); cview.open = true; v.hidden = false;
  const pl = proofLines(n);
  $("#cvHead").innerHTML = `<div class="cv-t"><span class="kicker">${n.kind === "leaf" ? "Proof" : "Sketch"} · ${fmt(codeOf(n).split("\n").length)} lines</span><span class="nm">${esc(n.name)}</span></div>
    <div class="cv-b">${badges(n)}</div>
    <div class="cv-a">${proofIndex ? '<button type="button" class="btn" data-cv="find">Find in the full proof</button>' : ""}<button type="button" class="btn" data-cv="copy">Copy</button><button type="button" class="drawer-x" data-cv="close" aria-label="Close code">×</button></div>`;
  $("#cvBody").innerHTML = (n.defs ? `<div class="cv-defs"><div class="kicker">Definitions</div>${numbered(n.defs, n.name)}</div>` : "") + numbered(codeOf(n), n.name);
  $("#cvBody").scrollTop = 0;
}
function closeCode() { cview.open = false; $("#cview").hidden = true; }
$("#cview").addEventListener("click", async e => {
  const b = e.target.closest("[data-cv]");
  if (b && b.dataset.cv === "close") return closeCode();
  if (b && b.dataset.cv === "find") return findInProof(S.sel.name);
  if (b && b.dataset.cv === "copy") { try { await navigator.clipboard.writeText(codeOf(S.sel)); b.textContent = "Copied"; } catch (err) { b.textContent = "Copy failed"; } setTimeout(() => b.textContent = "Copy", 1400); return; }
  const l = e.target.closest(".ll[data-n]"); if (l) select(nodeAt(l.dataset.n));
});
addEventListener("keydown", e => { if (e.key === "Escape" && cview.open) closeCode(); });

/* ---------- canvas ---------- */
const cv = $("#cv"), ctx = cv.getContext("2d"), mini = $("#mini"), mctx = mini.getContext("2d");
let W = 0, H = 0;
const MONO = () => getComputedStyle(document.body).getPropertyValue("--mono");
function resize() {
  if (cv.hidden || $("#sDag").hidden) return;
  const dpr = window.devicePixelRatio || 1;
  const w = stage.clientWidth, h = stage.clientHeight; if (!w) return;
  if (w !== W || h !== H) { W = w; H = h; if (!bp.userMoved) bp.fitted = false; }
  cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr); cv.style.width = W + "px"; cv.style.height = H + "px";
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  mini.width = 200 * dpr; mini.height = 100 * dpr; mctx.setTransform(dpr, 0, 0, dpr, 0, 0); bp.miniDirty = true;
  redraw();
}
new ResizeObserver(() => resize()).observe(stage);
function redraw() {
  if (!S.dag) return;
  if (S.view === "outline") return renderOutline();
  if (!W) return;
  ctx.clearRect(0, 0, W, H); bp.draw(); bp.drawMini(); renderLegend();
}
let pend = false;
function requestDraw() { if (pend) return; pend = true; requestAnimationFrame(() => { pend = false; redraw(); }); }
function trunc(text, px) {
  if (ctx.measureText(text).width <= px) return text;
  let lo = 0, hi = text.length;
  while (lo < hi) { const m = (lo + hi + 1) >> 1; ctx.measureText(text.slice(0, m) + "…").width <= px ? lo = m : hi = m - 1; }
  return lo < 3 ? "" : text.slice(0, lo) + "…";
}

/* ---------- DAG view: the full layered graph with semantic zoom ---------- */
const NW = 168, NH = 46, SX = 184, SY = 120;
const bp = {
  fold: new Set(), list: [], kx: 1, ky: 1, kyBase: 1, x: 0, y: 0, fitted: false, userMoved: false, anim: 0, camAnim: 0, W0: 1, H0: 1, hover: null, miniDirty: true, miniImg: null, miniMap: null,
  reset() { this.fold = new Set(); this.list = []; this.fitted = false; this.userMoved = false; this.hover = null; },
  layout() {
    let slot = 0, md = 0; const list = [];
    const walk = n => {
      list.push(n); md = Math.max(md, n.depth);
      const ks = this.fold.has(n.i) ? [] : kids(n); n._bk = ks;
      if (!ks.length) n._tx = slot++ * SX; else { ks.forEach(walk); n._tx = (ks[0]._tx + ks[ks.length - 1]._tx) / 2; }
      n._ty = n.depth * SY;
    };
    walk(S.dag.root); this.list = list; this.W0 = Math.max(1, slot) * SX - (SX - NW); this.H0 = md * SY + NH; this.miniDirty = true;
  },
  relayout(anim) {
    if (!S.dag) return;
    const prev = new Set(this.list.map(n => n.i)); this.layout();
    const from = new Map();
    for (const n of this.list) {
      if (!prev.has(n.i) || n._x === undefined) { const p = n.tp; const ok = p && prev.has(p.i) && p._x !== undefined; n._x = ok ? p._x : n._tx; n._y = ok ? p._y : n._ty; }
      from.set(n, [n._x, n._y]);
    }
    cancelAnimationFrame(this.anim);
    if (!anim || reduced() || !prev.size) { for (const n of this.list) { n._x = n._tx; n._y = n._ty; } return; }
    const t0 = performance.now();
    const stepF = now => { const u = ease(Math.min(1, (now - t0) / 450)); for (const [n, f] of from) { n._x = f[0] + (n._tx - f[0]) * u; n._y = f[1] + (n._ty - f[1]) * u; } requestDraw(); if (u < 1) this.anim = requestAnimationFrame(stepF); };
    this.anim = requestAnimationFrame(stepF);
  },
  fit() {
    const pw = W - 40, ph = H - 80;
    this.kx = Math.min(1, pw / this.W0); this.kyBase = Math.min(1, ph / Math.max(1, this.H0)); this.ky = Math.max(this.kx, this.kyBase);
    this.x = 20 + Math.max(0, (pw - this.W0 * this.kx) / 2); this.y = 54; this.fitted = true; this.userMoved = false;
  },
  setK(kx) { kx = Math.max(.002, Math.min(kx, 2.5)); return [kx, Math.max(kx, this.kyBase)]; },
  zoom(px, py, f) { const [kx, ky] = this.setK(this.kx * f); this.x = px - (px - this.x) * kx / this.kx; this.y = py - (py - this.y) * ky / this.ky; this.kx = kx; this.ky = ky; this.userMoved = true; requestDraw(); },
  pan(dx, dy) { this.x += dx; this.y += dy; this.userMoved = true; requestDraw(); },
  focus(n, anim) {
    if (!W || !this.list.length) return;
    let changed = false; for (const a of pathTo(n).slice(0, -1)) if (this.fold.delete(a.i)) changed = true;
    if (changed) this.relayout(false);
    if (!this.fitted) this.fit();
    const [kx, ky] = this.setK(Math.max(this.kx, .85));
    const tx = W / 2 - (n._tx + NW / 2) * kx, ty = H / 2 - (n._ty + NH / 2) * ky;
    const s = { x: this.x, y: this.y, kx: this.kx, ky: this.ky }; this.userMoved = true;
    cancelAnimationFrame(this.camAnim);
    if (!anim || reduced()) { Object.assign(this, { x: tx, y: ty, kx, ky }); requestDraw(); return; }
    const t0 = performance.now();
    const stepF = now => { const u = ease(Math.min(1, (now - t0) / 550)); this.x = s.x + (tx - s.x) * u; this.y = s.y + (ty - s.y) * u; this.kx = s.kx + (kx - s.kx) * u; this.ky = s.ky + (ky - s.ky) * u; requestDraw(); if (u < 1) this.camAnim = requestAnimationFrame(stepF); };
    this.camAnim = requestAnimationFrame(stepF);
  },
  mode() { return this.kx >= .62 ? "full" : this.kx >= .2 ? "box" : "dot"; },
  cx(n) { return this.x + (n._x + NW / 2) * this.kx; }, cy(n) { return this.y + (n._y + NH / 2) * this.ky; },
  draw() {
    if (!this.list.length) return;
    if (!this.fitted) this.fit();
    const mode = this.mode(), s = this.kx, bw = NW * s, bh = mode === "dot" ? 0 : NH * s, dark = isDark();
    ctx.font = "10px " + MONO(); ctx.textBaseline = "middle";
    const D = Math.round((this.H0 - NH) / SY);
    for (let d = 0; d <= D; d++) {
      const y = this.y + (d * SY + NH / 2) * this.ky; if (y < -10 || y > H + 10) continue;
      ctx.strokeStyle = TK.line; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke();
      if (SY * this.ky > 16) { ctx.fillStyle = TK.muted; ctx.fillText("depth " + d, 8, y - 8); }
    }
    const off = (x1, y1, x2, y2) => (x1 < -60 && x2 < -60) || (x1 > W + 60 && x2 > W + 60) || (y1 < -60 && y2 < -60) || (y1 > H + 60 && y2 > H + 60);
    const curve = (p, a, b) => { const x1 = this.cx(a), y1 = this.cy(a) + bh / 2, x2 = this.cx(b), y2 = this.cy(b) - bh / 2; if (off(x1, y1, x2, y2)) return; const my = (y1 + y2) / 2; p.moveTo(x1, y1); p.bezierCurveTo(x1, my, x2, my, x2, y2); };
    const by = new Map();
    for (const n of this.list) for (const c of n._bk) { const col = c.ab ? TK.del : branchColor(c); if (!by.has(col)) by.set(col, new Path2D()); curve(by.get(col), n, c); }
    ctx.lineWidth = mode === "dot" ? .8 : 1.3; ctx.globalAlpha = dark ? .5 : .55;
    for (const [col, p] of by) { ctx.strokeStyle = col; ctx.stroke(p); }
    const shared = new Path2D(), shown = new Set(this.list.map(n => n.i));
    for (const c of this.list) for (let j = 1; j < c.parents.length; j++) if (shown.has(c.parents[j].i)) curve(shared, c.parents[j], c);
    ctx.strokeStyle = TK.warn; ctx.globalAlpha = .75; ctx.setLineDash([4, 4]); ctx.stroke(shared); ctx.setLineDash([]); ctx.globalAlpha = 1;
    const hot = new Path2D(), sel = S.sel, path = pathTo(sel);
    for (let i = 1; i < path.length; i++) if (shown.has(path[i].i)) curve(hot, path[i - 1], path[i]);
    if (shown.has(sel.i)) (sel._bk || []).forEach(c => curve(hot, sel, c));
    const hv = this.hover; if (hv && shown.has(hv.i)) { (hv._bk || []).forEach(c => curve(hot, hv, c)); hv.parents.forEach(p => { if (shown.has(p.i)) curve(hot, p, hv); }); }
    ctx.strokeStyle = TK.accent; ctx.lineWidth = mode === "dot" ? 1.6 : 2.4; ctx.stroke(hot);
    const font1 = Math.max(9, Math.min(13, 11.5 * s)), font2 = Math.max(8.5, Math.min(12, 10.5 * s)), mono = MONO();
    for (const n of this.list) {
      const x = this.cx(n), y = this.cy(n);
      if (x < -bw - 10 || x > W + bw + 10 || y < -bh - 10 || y > H + bh + 10) continue;
      const folded = this.fold.has(n.i) && kids(n).length > 0, m = S.matches.has(n.i);
      if (mode === "dot") {
        const r = n === S.dag.root ? 5.5 : n.kind === "composite" ? 3 : 2.1;
        ctx.beginPath(); ctx.arc(x, y, folded ? r + 1.5 : r, 0, 7);
        if (n.ab) { ctx.strokeStyle = TK.del; ctx.lineWidth = 1; ctx.stroke(); } else { ctx.fillStyle = branchColor(n); ctx.fill(); }
        if (n.parents.length > 1) { ctx.strokeStyle = TK.warn; ctx.lineWidth = 1.1; ctx.beginPath(); ctx.arc(x, y, r + 2.2, 0, 7); ctx.stroke(); }
        if (m) { ctx.strokeStyle = TK.warn; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(x, y, r + 5, 0, 7); ctx.stroke(); }
        continue;
      }
      const x0 = x - bw / 2, y0 = y - bh / 2, rr = Math.min(10, 10 * s);
      const rect = (dx, dy) => { ctx.beginPath(); if (ctx.roundRect) ctx.roundRect(x0 + dx, y0 + dy, bw, bh, rr); else ctx.rect(x0 + dx, y0 + dy, bw, bh); };
      if (folded) for (const o of [7, 3.5]) { rect(o * s, o * s); ctx.fillStyle = TK.surface; ctx.fill(); ctx.strokeStyle = TK["line-2"]; ctx.lineWidth = 1; ctx.stroke(); }
      rect(0, 0);
      ctx.fillStyle = m ? TK["warn-soft"] : n === S.sel ? TK["accent-soft"] : n.ab ? TK["del-bg"] : n.kind === "leaf" ? TK["pos-soft"] : TK.surface; ctx.fill();
      ctx.strokeStyle = n === S.sel ? TK.accent : m ? TK.warn : n.ab ? TK.del : TK.pos; ctx.lineWidth = n === S.sel ? 2.6 : n === this.hover ? 2.2 : 1.3;
      if (n.ab) ctx.setLineDash([4, 3]); ctx.stroke(); ctx.setLineDash([]);
      if (n.parents.length > 1) { ctx.fillStyle = TK.warn; ctx.beginPath(); ctx.arc(x0 + bw - 8 * s, y0 + 8 * s, 3.2 * s, 0, 7); ctx.fill(); }
      if (mode === "full") {
        ctx.fillStyle = branchColor(n); ctx.beginPath(); ctx.arc(x0 + 14 * s, y0 + 16 * s, 4.5 * s, 0, 7); ctx.fill();
        ctx.textBaseline = "middle"; ctx.font = `600 ${font1}px ${mono}`; ctx.fillStyle = TK.ink;
        ctx.fillText(trunc(n.name, bw - 32 * s), x0 + 25 * s, y0 + 16 * s);
        ctx.font = `${font2}px ${mono}`; ctx.fillStyle = folded ? TK["accent-ink"] : TK.muted;
        const meta = n.ab ? "rejected" : folded ? `+${fmt(weight(n) - 1)} lemmas, folded` : n.kind === "leaf" ? `closed · ${n.lines} lines` : `${kids(n).length} lemmas · ${fmt(n.sc - 1)} below`;
        ctx.fillText(trunc(meta, bw - 20 * s), x0 + 12 * s, y0 + 33 * s);
      }
    }
    if (mode === "dot") {
      const pinned = new Set([S.dag.root, S.sel, this.hover, ...S.mlist.slice(0, 20)]);
      // Small DAGs: name every node with a slanted label so the whole proof reads at full view.
      if (this.list.length <= 150) {
        const ang = .62, room = Math.max(40, (SY * this.ky - 18) / Math.sin(ang));
        ctx.font = "500 10.5px " + mono; ctx.textBaseline = "middle"; ctx.fillStyle = TK["ink-2"];
        for (const n of this.list) {
          if (pinned.has(n)) continue;
          const x = this.cx(n), y = this.cy(n); if (x < -20 || x > W + 20 || y < -20 || y > H + 20) continue;
          ctx.save(); ctx.translate(x + 5, y + 6); ctx.rotate(ang); ctx.fillText(trunc(n.name, room), 0, 0); ctx.restore();
        }
      }
      ctx.font = "600 11px " + mono; ctx.textBaseline = "middle";
      for (const n of pinned) {
        if (!n || !shown.has(n.i)) continue; const x = this.cx(n) + 8, y = this.cy(n) - 10;
        ctx.fillStyle = TK.bg; ctx.globalAlpha = .82; ctx.fillRect(x - 3, y - 8, ctx.measureText(n.name).width + 6, 16); ctx.globalAlpha = 1;
        ctx.fillStyle = n === S.sel ? TK["accent-ink"] : TK.ink; ctx.fillText(n.name, x, y);
      }
      if (shown.has(sel.i)) { ctx.strokeStyle = TK.accent; ctx.lineWidth = 2.4; ctx.beginPath(); ctx.arc(this.cx(sel), this.cy(sel), 8, 0, 7); ctx.stroke(); }
    }
  },
  drawMini() {
    if (mini.hidden || !this.list.length) return;
    const w = 200, h = 100, pad = 6, sx = (w - 2 * pad) / this.W0, sy = (h - 2 * pad) / Math.max(1, this.H0);
    if (this.miniDirty) {
      const c = this.miniImg || (this.miniImg = document.createElement("canvas")), dpr = devicePixelRatio || 1;
      c.width = w * dpr; c.height = h * dpr; const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);
      for (const n of this.list) { g.fillStyle = n.ab ? TK.del : branchColor(n); g.fillRect(pad + (n._tx + NW / 2) * sx - .75, pad + (n._ty + NH / 2) * sy - .75, 1.5, 1.5); }
      this.miniDirty = false;
    }
    mctx.clearRect(0, 0, w, h); mctx.drawImage(this.miniImg, 0, 0, w, h);
    const vx0 = -this.x / this.kx, vx1 = (W - this.x) / this.kx, vy0 = -this.y / this.ky, vy1 = (H - this.y) / this.ky;
    const r = [pad + vx0 * sx, pad + vy0 * sy, (vx1 - vx0) * sx, (vy1 - vy0) * sy];
    mctx.fillStyle = TK.accent; mctx.globalAlpha = .12; mctx.fillRect(...r); mctx.globalAlpha = 1;
    mctx.strokeStyle = TK.accent; mctx.lineWidth = 1.5; mctx.strokeRect(...r);
    this.miniMap = { pad, sx, sy };
  },
  hit(px, py) {
    if (this.mode() === "dot") { let best = null, bd = 100; for (const n of this.list) { const dx = this.cx(n) - px, dy = this.cy(n) - py, d = dx * dx + dy * dy; if (d < bd) { bd = d; best = n; } } return best; }
    const bw = NW * this.kx, bh = NH * this.kx;
    for (let i = this.list.length - 1; i >= 0; i--) { const n = this.list[i], x = this.cx(n), y = this.cy(n); if (Math.abs(px - x) <= bw / 2 && Math.abs(py - y) <= bh / 2) return n; }
    return null;
  },
  toggle(n) { if (!kids(n).length) return; this.fold.has(n.i) ? this.fold.delete(n.i) : this.fold.add(n.i); this.relayout(true); }
};
let drag = null;
cv.addEventListener("pointerdown", e => { drag = { x: e.offsetX, y: e.offsetY, moved: false }; cv.setPointerCapture(e.pointerId); hidePop(); });
cv.addEventListener("pointermove", e => {
  if (!S.dag) return;
  if (drag) { const dx = e.offsetX - drag.x, dy = e.offsetY - drag.y; if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true; if (drag.moved) { bp.pan(dx, dy); drag.x = e.offsetX; drag.y = e.offsetY; } return; }
  const n = bp.hit(e.offsetX, e.offsetY);
  if (n !== bp.hover) { bp.hover = n; requestDraw(); }
  cv.style.cursor = n ? "pointer" : "grab";
  if (n && e.pointerType !== "touch") showPop(n, e.clientX, e.clientY); else hidePop();
});
cv.addEventListener("pointerup", e => { if (drag && !drag.moved && S.dag) { const n = bp.hit(e.offsetX, e.offsetY); if (n) select(n, "dag"); } drag = null; });
cv.addEventListener("dblclick", e => { if (!S.dag) return; const n = bp.hit(e.offsetX, e.offsetY); if (n) bp.toggle(n); });
cv.addEventListener("pointerleave", () => { hidePop(); if (bp.hover) { bp.hover = null; requestDraw(); } });
cv.addEventListener("wheel", e => { if (!(e.ctrlKey || e.metaKey)) return; e.preventDefault(); bp.zoom(e.offsetX, e.offsetY, Math.exp(-e.deltaY * .004)); }, { passive: false });
$("#zoomctl").addEventListener("click", e => {
  const b = e.target.closest("[data-z]"); if (!b) return;
  if (b.dataset.z === "fit") { bp.fitted = false; requestDraw(); } else bp.zoom(W / 2, H / 2, b.dataset.z === "in" ? 1.6 : 1 / 1.6);
});
$("#bFold").addEventListener("click", () => { if (!S.dag) return; bp.fold = new Set(S.dag.nodes.filter(n => n.depth === 2).map(n => n.i)); bp.relayout(true); bp.fitted = false; requestDraw(); });
$("#bUnfold").addEventListener("click", () => { if (!S.dag) return; bp.fold.clear(); bp.relayout(true); bp.fitted = false; requestDraw(); });
let miniDrag = false;
const miniGo = e => {
  if (!bp.miniMap) return; const { pad, sx, sy } = bp.miniMap;
  const wx = (e.offsetX - pad) / sx, wy = (e.offsetY - pad) / sy;
  bp.x = W / 2 - wx * bp.kx; bp.y = H / 2 - wy * bp.ky; bp.userMoved = true; requestDraw();
};
mini.addEventListener("pointerdown", e => { miniDrag = true; mini.setPointerCapture(e.pointerId); miniGo(e); });
mini.addEventListener("pointermove", e => { if (miniDrag) miniGo(e); });
mini.addEventListener("pointerup", () => { miniDrag = false; });

/* ---------- outline ---------- */
const expanded = new Set();
function expandPath(n) { if (!n) return; pathTo(n).forEach(p => expanded.add(p.i)); }
function renderOutline() {
  if (!expanded.size) expanded.add(S.dag.root.i);
  const out = [`<div class="ohead"><span>Lemma and statement</span><span class="hb" style="width:64px">share</span><span style="width:140px;text-align:right">size</span></div>`];
  const walk = n => {
    const ks = kids(n), open = expanded.has(n.i), cls = (n === S.sel ? " sel" : "") + (n.ab ? " ab" : "") + (S.matches.has(n.i) ? " match" : "");
    const meta = n.ab ? "rejected" : n.kind === "leaf" ? `${n.lines} lines` : `${fmt(n.sc - 1)} below · ${fmt(n.sl)} ln`;
    const share = n.tp ? Math.max(2, Math.round(100 * weight(n) / Math.max(1, weight(n.tp)))) : 100;
    const col = n.ab ? "var(--del)" : branchVar(n);
    out.push(`<div class="orow${cls}" role="treeitem" aria-level="${n.depth + 1}" ${ks.length ? `aria-expanded="${open}"` : ""} data-n="${n.i}">
      ${'<span class="ig"></span>'.repeat(n.depth)}
      <button type="button" class="tg" data-t="${n.i}" ${ks.length ? "" : "disabled"} aria-label="${open ? "Collapse" : "Expand"}">${ks.length ? (open ? "▾" : "▸") : ""}</button>
      <span class="dot${n.kind === "composite" ? " comp" : ""}" style="background:${col};border-color:${col}"></span>
      <span class="oc"><span class="on">${esc(n.name)}</span><span class="os">${esc(preview(n))}</span></span>
      ${n.parents.length > 1 ? `<span class="bdg sh">×${n.parents.length}</span>` : ""}
      <span class="obar"><i style="width:${share}%;background:${col}"></i></span>
      <span class="om">${meta}</span></div>`);
    if (open) ks.forEach(walk);
  };
  walk(S.dag.root);
  $("#outlinePane").innerHTML = out.join("");
  const sel = $("#outlinePane .orow.sel"); if (sel) { const p = $("#outlinePane"); if (sel.offsetTop < p.scrollTop + 30 || sel.offsetTop > p.scrollTop + p.clientHeight - 40) p.scrollTop = sel.offsetTop - 100; }
  renderLegend();
}
$("#outlinePane").addEventListener("click", e => {
  const t = e.target.closest("[data-t]");
  if (t) { const i = +t.dataset.t; expanded.has(i) ? expanded.delete(i) : expanded.add(i); renderOutline(); return; }
  const r = e.target.closest("[data-n]"); if (r) select(nodeAt(r.dataset.n));
});

/* ---------- legend ---------- */
function renderLegend() {
  const it = [];
  if (S.view === "dag") it.push('<span><i class="sq" style="background:var(--surface);border:1.5px solid var(--pos)"></i>decomposed</span>', '<span><i class="sq" style="background:var(--pos-soft);border:1.5px solid var(--pos)"></i>closed directly</span>', '<span><i class="sq" style="background:var(--surface);border:1.5px solid var(--line-2);box-shadow:3px 3px 0 var(--line-2)"></i>folded</span>', '<span><i class="sq" style="background:var(--warn);height:2px;width:14px;vertical-align:3px"></i>shared lemma</span>');
  else it.push('<span><i style="background:transparent;border:2.5px solid var(--ink-2)"></i>decomposed</span>', '<span><i style="background:var(--ink-2)"></i>closed directly</span>');
  if (S.showAb) it.push('<span><i class="sq" style="background:var(--del-bg);border:1.5px dashed var(--del)"></i>rejected attempt</span>');
  it.push('<span style="margin-left:auto;color:var(--muted)">color = top-level lemma · hover for Lean</span>');
  $("#legend").innerHTML = it.join("");
}


/* ---------- page ---------- */
let CUR = null;
function renderProblemPage(p) {
  CUR = p;
  document.title = `${p.title} · LEAP`;
  if (EMBED && parent !== window) try { parent.postMessage({ type: "leap:problem", id: p.id }, location.origin); } catch (e) {}
  const i = PROBLEMS.indexOf(p), prev = PROBLEMS[(i - 1 + PROBLEMS.length) % PROBLEMS.length], next = PROBLEMS[(i + 1) % PROBLEMS.length];
  $("#crumb").innerHTML = `<a href="problems.html">Solved problems</a><span>›</span><span>${esc(p.title)}</span>`;
  const link = q => problemUrl(q) + (EMBED ? "&embed=1" : "");
  $("#pager").innerHTML = `<a class="btn" href="${link(prev)}" title="${esc(prev.title)}">← Previous</a><a class="btn" href="${link(next)}" title="${esc(next.title)}">Next →</a>`;
  $("#dTitle").innerHTML = titleHTML(p);
  $("#dSub").textContent = p.subtitle || "";
  $("#dBadges").innerHTML = [p.featured ? '<span class="bdg sh">★ featured</span>' : "", p.area ? `<span class="bdg">${esc(p.area)}</span>` : "", `<span class="bdg">${esc(p.collection)}</span>`, p.credit ? `<span class="bdg acc">${esc(p.credit)}</span>` : "", '<span class="bdg leaf">verified in Lean</span>'].join("");
  $("#dLoc").textContent = p.loc ? (p.loc >= 20000 ? "~" + kloc(p.loc) : fmt(p.loc)) : "";
  $("#dLocL").textContent = p.loc ? "lines of Lean" : "";
  $("#dProb").innerHTML = (p.problem || []).map(t => `<p>${md(t)}</p>`).join("") + (p.statement ? `<div class="stmt">${esc(p.statement)}</div>` : "") +
    (p.notes || []).map(n => `<div class="note${/todo/i.test(n.title) ? " todo-n" : ""}"><h4>${esc(n.title)}</h4><p>${md(n.text)}</p></div>`).join("");
  const L = p.lean || {};
  $("#dSide").innerHTML = `<h4>Result</h4><dl class="kv">
      <dt>Variant</dt><dd>${esc(p.variant || "main statement")}</dd>
      <dt>Lean</dt><dd>${p.loc ? fmt(p.loc) + " lines" : "—"}</dd>
      <dt>Root</dt><dd>${esc(L.root || "—")}</dd>
      <dt>Added</dt><dd>${esc(p.added || "—")}</dd></dl>
    ${(p.links || []).map(l => `<a class="btn" href="${esc(l.url)}" target="_blank" rel="noopener">${esc(l.label)} ↗</a>`).join("")}
    ${p.files.proof ? `<a class="btn" href="${esc(fileUrl(p, "proof"))}" download>Download the Lean proof</a>` : ""}
    ${p.files.statement ? `<a class="btn" href="${esc(fileUrl(p, "statement"))}" target="_blank" rel="noopener">Lean statement ↗</a>` : ""}`;
  renderInformal(p); renderLean(p);
  $("#xstats").textContent = "Loading proof DAG…";
  getDag(p).then(d => { if (CUR === p) loadDag(d); });
}
document.querySelectorAll(".stab").forEach(b => b.addEventListener("click", () => { setSTab(b.dataset.s); try { history.replaceState(null, "", "#" + b.dataset.s); } catch (e) {} }));
document.addEventListener("leap:theme", () => { bp.miniDirty = true; redraw(); });

boot(() => {
  const id = new URLSearchParams(location.search).get("id");
  const p = PROBLEMS.find(x => x.id === id);
  if (!p) {
    $("#dTitle").textContent = "Problem not found";
    $("#dSub").innerHTML = `There is no problem with id <code>${esc(id || "")}</code>. <a href="problems.html">See all solved problems</a>.`;
    $("#sol").hidden = true; return;
  }
  setView("dag");
  const tab = location.hash.slice(1);
  if (["informal", "lean", "dag"].includes(tab)) setSTab(tab);
  renderProblemPage(p);
});
// Inside the drawer, previous/next replace the frame's history entry so closing the drawer returns to the list.
if (EMBED) $("#pager").addEventListener("click", e => { const a = e.target.closest("a"); if (!a || e.metaKey || e.ctrlKey) return; e.preventDefault(); location.replace(a.href); });
