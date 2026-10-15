/* Shared by every page: helpers, theme, problem data, DAG model. */
const $ = s => document.querySelector(s);
const esc = s => String(s ?? "").replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
const fmt = n => n.toLocaleString("en-US");
const kloc = n => n >= 1e6 ? (n / 1e6).toFixed(1).replace(/\.0$/, "") + "M" : n >= 1000 ? Math.round(n / 1000) + "K" : String(n);
const reduced = () => matchMedia("(prefers-reduced-motion: reduce)").matches;
const ease = u => u < .5 ? 4 * u * u * u : 1 - Math.pow(-2 * u + 2, 3) / 2;
/* tiny inline markup for JSON text: `code`, **bold**, [label](https://url) */
function md(t) {
  return esc(t).replace(/`([^`]+)`/g, "<code>$1</code>").replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
    .replace(/\[([^\]]+)\]\((https?:[^)\s]+)\)/g, '<a href="$2" target="_blank" rel="noopener">$1</a>');
}

/* ---------- theme ---------- */
const themeBtn = $("#themeBtn");
let themeMode = "light";
try { themeMode = localStorage.getItem("leap-theme") || "light"; } catch (e) {}
let TK = {};
function readTokens() {
  const cs = getComputedStyle(document.documentElement);
  ["bg","surface","surface-2","ink","ink-2","muted","line","line-2","accent","accent-ink","accent-soft","accent-2","warn","warn-soft","del","del-bg","pos","pos-soft","c1","c2","c3","c4","c5","c6","c7","c8"].forEach(k => TK[k] = cs.getPropertyValue("--" + k).trim());
}
function themeChanged() { readTokens(); document.dispatchEvent(new Event("leap:theme")); }
function applyTheme() {
  if (themeMode === "auto") document.documentElement.removeAttribute("data-theme");
  else document.documentElement.setAttribute("data-theme", themeMode);
  themeBtn.textContent = "Theme · " + themeMode;
  themeChanged();
}
themeBtn.addEventListener("click", () => {
  themeMode = { light: "dark", dark: "auto", auto: "light" }[themeMode];
  try { localStorage.setItem("leap-theme", themeMode); } catch (e) {}
  applyTheme();
});
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", themeChanged);

/* ---------- problem data (problems/index.json + problems/<id>/meta.json) ---------- */
let PROBLEMS = [];
async function loadProblems() {
  try {
    const idx = await (await fetch("problems/index.json")).json();
    PROBLEMS = await Promise.all(idx.order.map(id => fetch(`problems/${id}/meta.json`).then(r => { if (!r.ok) throw new Error(id); return r.json(); }).then(m => ({ ...m, id, base: `problems/${id}/`, files: m.files || {} }))));
  } catch (e) {
    const box = $("#loadErr");
    if (box) { box.hidden = false; box.innerHTML = `<div class="err">Could not load the problem files (${esc(e.message)}). Serve the site over HTTP and check that <code>problems/index.json</code> and every <code>problems/&lt;id&gt;/meta.json</code> exist.</div>`; }
    return false;
  }
  return true;
}
const hasInformal = p => !!p.files.informal;
const hasLean = p => !!(p.files.proof || p.files.statement);
const hasDag = p => !!p.files.dag;
const fileUrl = (p, k) => p.base + p.files[k];
const textCache = new Map();
async function getText(p, k) {
  const u = fileUrl(p, k);
  if (!textCache.has(u)) textCache.set(u, fetch(u).then(r => { if (!r.ok) throw new Error(u); return r.text(); }));
  return textCache.get(u);
}
/* LEAP-CLI writes proof_graph.json: nodes keyed by id, each with and_nodes (decomposition attempts). */
// proof_graph.json stores most signatures without the `theorem <name>` header; rebuild it the way answer.lean declares it.
function leanHeader(name, s) {
  s = (s || "").trim();
  if (/^(theorem|lemma|def|abbrev)\b/.test(s)) return s;
  if (startsWithBinder(s)) return `theorem ${name} ${s}`;
  return `theorem ${name} :\n    ${s}`;
}
// A binder group is a bracketed `names : type` that is followed by another binder or by the colon before the type.
function startsWithBinder(s) {
  if (!/^[\(\{\[⦃]\s*[A-Za-z_Ͱ-Ͽἀ-῿][^\s:()]*(\s+[^\s:()]+)*\s*:/.test(s) || /^[\(\{\[⦃]\s*(fun|λ|∀|∃)\b/.test(s)) return false;
  const close = { "(": ")", "{": "}", "[": "]", "⦃": "⦄" };
  let depth = 0, i = 0;
  for (; i < s.length; i++) {
    const ch = s[i];
    if ("({[⦃".includes(ch)) depth++;
    else if (")}]⦄".includes(ch)) { depth--; if (depth === 0) break; }
  }
  const rest = s.slice(i + 1).trimStart();
  return rest.startsWith(":") || /^[\(\{\[⦃]/.test(rest);
}
function fromLeapGraph(g) {
  const nodes = [], edges = [];
  Object.keys(g.nodes).forEach((id, t) => {
    const n = g.nodes[id], f = n.formal_theorem || n.formal_sketch, sig = f && f.signature;
    const statement = leanHeader((sig && sig.name) || id, (sig && sig.statement) || (n.informal_problem && n.informal_problem.statement) || "");
    const tac = (f && f.proof && f.proof.tactics) || "";
    const ands = n.and_nodes || [];
    const live = ands.filter(a => !a.failed && (a.dependency_ids || []).length);
    nodes.push({ id, name: id, statement, code: tac ? `${statement} := ${tac.trim()}` : statement, defs: (n.definitions || "").trim() || null, kind: live.length ? "composite" : "leaf", lines: tac ? tac.trim().split("\n").length : 0, t });
    ands.forEach(a => (a.dependency_ids || []).forEach(dep => edges.push({ from: id, to: dep, attempt: a.failed ? "rejected" : "accepted" })));
  });
  return { nodes, edges };
}
const titleHTML = p => `${esc(p.title)}${p.marks ? `<span class="mk">${esc(p.marks)}</span>` : ""}${p.variant ? `<span class="pv">${esc(p.variant)}</span>` : ""}`;
const dagCache = new Map();
function sampleCfg(p) {
  let h = 7; for (const c of p.id) h = (h * 31 + c.charCodeAt(0)) >>> 0;
  const size = Math.max(500, Math.min(6500, Math.round((p.loc || 30000) / 110)));
  const a = p.area || "";
  const vocab = /combinator/i.test(a) ? "comb" : /number|totient/i.test(a) ? "nt" : /PDE|analysis/i.test(a) ? "pde" : "generic";
  return { seed: h, size, vocab, root: (p.lean && p.lean.root) || p.id.replace(/-/g, "_") };
}
async function getDag(p) {
  if (dagCache.has(p.id)) return dagCache.get(p.id);
  let raw = null, sample = true;
  if (hasDag(p)) { try { const j = JSON.parse(await getText(p, "dag")); raw = Array.isArray(j.nodes) ? j : fromLeapGraph(j); sample = false; } catch (e) { console.error(e); raw = null; } }
  if (!raw) raw = genDag(sampleCfg(p));
  const d = buildDag(raw); d.sample = sample; dagCache.set(p.id, d); return d;
}
/* ---------- sample DAG generator (placeholder until real exports exist) ---------- */
function rng(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
const VOCAB = {
  comb: { a: ["path","edge","len","perm","walk","seq","lab","vert","swap","glue","block","tail","cycle","shift"], b: ["realize","hamiltonian","length","multiset","card","injective","append","reverse","concat","count","distinct","covers"], c: ["aux","base","succ","le","lt","eq","of_ge","pos","iff","even","odd"],
    bind: "(y k a b c : ℕ) (hk : 1 ≤ k) (hky : 2 * k < y) (ha : y ≤ a)", args: "y k a b c hk hky ha",
    props: ["LinearRealization (ms y k a b c)", "(path y k a b c).length = a + b + c + 1", "(path y k a b c).Nodup", "∀ i < a + b + c, edgeLen (path y k a b c) i ∈ ({1, y - k, y} : Finset ℕ)", "Multiset.count 1 (lengths (path y k a b c)) = a", "(glue p q).IsHamiltonian ↔ p.IsHamiltonian ∧ q.IsHamiltonian", "∀ v < a + b + c + 1, v ∈ path y k a b c"],
    leaf: ["simp [path, List.length_append]\n  omega", "decide", "intro i hi\n  interval_cases i <;> simp_all [edgeLen]", "exact List.nodup_append.mpr ⟨h₁, h₂, by simpa using hdisj⟩", "omega"] },
  nt: { a: ["prime","div","lcm","consec","fac","pow","gap","pfac","count","sieve","val","prod","smooth","totient"], b: ["bound","dvd","coprime","le","card","exists","mono","window","large","split","pair","max","image"], c: ["aux","of_lt","pos","nat","sq","two","iff","ne_zero","succ","base"],
    bind: "(n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k)", args: "n k hn hk",
    props: ["∃ p, p.Prime ∧ p ∣ n + k ∧ k < p", "Nat.Coprime (n + k) (n + k + 1)", "k ≤ (∏ i ∈ Finset.range k, (n + i)).primeFactors.card", "(n + k).factorization 2 ≤ Nat.log 2 (n + k)", "∀ p ∈ (n + k).primeFactors, p ≤ n + k", "k.factorial ∣ ∏ i ∈ Finset.range k, (n + i)", "Nat.log 2 n < n", "(Finset.filter Nat.Prime (Finset.Icc n (n + k))).card ≤ k + 1", "Nat.totient n ≤ n - 1"],
    leaf: ["simp [Nat.factorization_le_iff_dvd]\n  omega", "positivity", "induction k with\n  | zero => simp\n  | succ k ih => simp [Finset.prod_range_succ, ih]; ring", "nlinarith [Nat.log_lt_self 2 (by omega : n ≠ 0)]", "exact Nat.le_of_dvd (by omega) (Nat.dvd_refl _)"] },
  pde: { a: ["kdv","flow","energy","sobolev","fourier","duhamel","lax","alpha","resolvent","commut","tail","approx"], b: ["bound","cont","conserv","equicont","decay","limit","local","global","unique","embed","trace","est"], c: ["aux","Hm1","small","large","low","high","base","uniform","pos"],
    bind: "(κ : ℝ) (hκ : 1 ≤ κ) (q : ℝ → ℝ) (hq : q ∈ Hm1)", args: "κ hκ q hq",
    props: ["‖kdvFlow t q‖_{H⁻¹} ≤ C * ‖q‖_{H⁻¹}", "Continuous (fun t => kdvFlow t q)", "α κ (kdvFlow t q) = α κ q", "∀ ε > 0, ∃ R, ∫ x in {x | R < |x|}, |q x| ^ 2 ≤ ε", "‖R κ q‖_{op} ≤ κ⁻¹ * ‖q‖_{H⁻¹}", "Tendsto (fun N => ‖kdvN N t q - kdvFlow t q‖) atTop (𝓝 0)"],
    leaf: ["gcongr\n  exact norm_nonneg _", "simpa [α, integral_add] using h", "positivity", "nlinarith [sq_nonneg κ, hκ]", "exact continuous_id.comp (by fun_prop)"] },
  generic: { a: ["lem","goal","bound","key","step","case","sub","main","red","ind","aux","est","field","norm","ring"], b: ["mono","pos","le","eq","card","sum","exists","unique","bound","split","comp","inj","defin","integral"], c: ["aux","base","succ","iff","lt","ne","zero","one","two","mod"],
    bind: "(K : Type*) [Field K] [NumberField K] (x : 𝓞 K)", args: "K x",
    props: ["DiophantineSet (Set.range (algebraMap ℤ (𝓞 K)))", "∃ f : Polynomial ℤ, f.eval x = 0", "Diophantine {y : 𝓞 K | y ≠ 0}", "IsDiophantine (fun n : ℕ => (n : 𝓞 K))", "Module.finrank ℚ K ≤ 2 * Module.finrank ℚ L", "¬ Decidable (HasSolution (𝓞 K))"],
    leaf: ["simp [Diophantine, Set.mem_range]\n  aesop", "exact ⟨_, rfl⟩", "aesop", "norm_num [Module.finrank_mul_finrank]"] }
};
const CLOSERS = ["omega", "simpa [h₁] using h₂", "exact le_trans h₁ h₂", "linarith [h₁, h₂]", "exact ⟨h₁, h₂⟩", "nlinarith [h₁, h₂]", "exact h₂.trans h₁"];
const REASONS = ["Reviewer: the lemma restates the parent goal.", "Reviewer: the split is not simpler than the parent.", "Compiler: the sketch body did not typecheck.", "Reviewer: a lemma is unlikely to be provable as stated."];
const SUB = d => String(d).replace(/\d/g, c => "₀₁₂₃₄₅₆₇₈₉"[c]);
function genDag(cfg) {
  const R = rng(cfg.seed), V = VOCAB[cfg.vocab], nodes = [], edges = [], used = new Set(), pool = [];
  const pick = a => a[Math.floor(R() * a.length)];
  function name() {
    for (let i = 0; i < 24; i++) { const s = pick(V.a) + "_" + pick(V.b) + (R() < .65 ? "_" + pick(V.c) : ""); if (!used.has(s)) { used.add(s); return s; } }
    let s; do { s = pick(V.a) + "_" + pick(V.b) + "_" + nodes.length; } while (used.has(s)); used.add(s); return s;
  }
  function mk(nm) { const n = { id: "n" + nodes.length, name: nm, kind: "leaf", lines: 0, t: nodes.length, prop: pick(V.props) }; n.statement = `theorem ${nm} ${V.bind} :\n    ${n.prop}`; nodes.push(n); return n; }
  function solve(n, budget, depth) {
    if (depth > 0 && (budget <= 1 || depth >= 14 || (budget < 5 && R() < .4))) { n.kind = "leaf"; n.lines = 2 + Math.round(Math.exp(R() * 2.4) + R() * 4); n.code = n.statement + " := by\n  " + pick(V.leaf); pool.push(n); return; }
    const rej = R() < (depth < 3 ? .55 : .22) ? 1 + (R() < .35 ? 1 : 0) : 0;
    for (let r = 0; r < rej; r++) { const k = 2 + Math.floor(R() * 3), why = pick(REASONS); for (let i = 0; i < k; i++) { const c = mk(name()); c.reason = why; c.code = c.statement + " := by\n  sorry  -- never attempted: split rejected"; edges.push({ from: n.id, to: c.id, attempt: "rejected" }); } }
    const maxK = depth === 0 ? 8 : 6;
    const k = Math.max(depth === 0 ? 6 : 2, Math.min(maxK, budget - 1, 2 + Math.floor(R() * R() * maxK)));
    const w = []; for (let i = 0; i < k; i++) w.push(Math.pow(R(), 1.7) + .05);
    const sw = w.reduce((a, b) => a + b, 0), rest = Math.max(0, budget - 1 - k), mine = [];
    n.kind = "composite"; n.lines = 6 + 3 * k + Math.floor(R() * 10);
    for (let i = 0; i < k; i++) {
      if (pool.length > 8 && R() < .07) { const c = pool[Math.floor(R() * pool.length)]; if (!mine.includes(c)) { mine.push(c); edges.push({ from: n.id, to: c.id, attempt: "accepted" }); continue; } }
      const c = mk(name()); mine.push(c); edges.push({ from: n.id, to: c.id, attempt: "accepted" });
      solve(c, 1 + Math.floor(rest * w[i] / sw), depth + 1);
    }
    n.code = n.statement + " := by\n  -- blueprint: " + mine.length + " lemmas\n" + mine.map((c, i) => `  have h${SUB(i + 1)} := ${c.name} ${V.args}`).join("\n") + "\n  " + pick(CLOSERS);
    pool.push(n);
  }
  solve(mk(cfg.root), cfg.size, 0);
  return { nodes, edges };
}

/* ---------- DAG model ---------- */
function buildDag(raw) {
  const byId = new Map(), byName = new Map();
  const nodes = raw.nodes.map((r, i) => {
    const n = { i, id: r.id, name: r.name, statement: r.statement || null, code: r.code || r.statement || null, defs: r.defs || null, prop: r.prop || null, reason: r.reason || null, kind: r.kind || "leaf", lines: r.lines || 0, t: r.t ?? i, ab: false, parents: [], children: [], rejected: [], tk: [], tp: null, depth: 0 };
    byId.set(r.id, n); byName.set(r.name, n); return n;
  });
  // A lemma counts as rejected only when no accepted decomposition uses it.
  raw.edges.forEach(e => { const p = byId.get(e.from), c = byId.get(e.to); if (!p || !c || p === c) return; if (e.attempt === "rejected") { p.rejected.push(c); (c.rp ||= []).push(p); } else { p.children.push(c); c.parents.push(p); } });
  nodes.forEach(n => { if (!n.parents.length && n.rp) { n.ab = true; n.parents = n.rp; } });
  const root = nodes.find(n => !n.parents.length) || nodes[0];
  nodes.forEach(n => { n.tp = n.parents[0] || null; if (n.tp) n.tp.tk.push(n); });
  nodes.forEach(n => n.tk.sort((a, b) => a.t - b.t));
  const pre = [], st = [root]; root.depth = 0; root.br = -1;
  while (st.length) { const n = st.pop(); pre.push(n); for (let j = n.tk.length - 1; j >= 0; j--) { const c = n.tk[j]; c.depth = n.depth + 1; c.br = n === root ? j : n.br; st.push(c); } }
  for (let j = pre.length - 1; j >= 0; j--) {
    const n = pre[j];
    n.sc = n.ab ? 0 : 1; n.sca = 1; n.sl = n.ab ? 0 : n.lines; n.md = n.depth; n.mda = n.depth;
    n.tk.forEach(c => { n.sca += c.sca; n.mda = Math.max(n.mda, c.mda); if (!c.ab) { n.sc += c.sc; n.sl += c.sl; n.md = Math.max(n.md, c.md); } });
  }
  const live = pre.filter(n => !n.ab);
  return { nodes: pre, byI: nodes, byName, root, stats: { lemmas: live.length, rejected: pre.length - live.length, shared: live.filter(n => n.parents.length > 1).length, depth: root.md, lines: root.sl, leaves: live.filter(n => n.kind === "leaf").length } };
}

/* branch colors: each top-level lemma of the root owns one hue */
const branchColor = n => n.br < 0 ? TK.muted : TK["c" + (n.br % 8 + 1)];
const branchVar = n => n.br < 0 ? "var(--muted)" : `var(--c${n.br % 8 + 1})`;
const isDark = () => parseInt((TK.bg || "#fff").replace("#", "").slice(0, 2), 16) < 100;
const problemUrl = p => `problem.html?id=${encodeURIComponent(p.id)}`;
function boot(fn) { readTokens(); applyTheme(); loadProblems().then(ok => ok && fn()); }


/* ---------- problem drawer: problem pages slide in from the right ---------- */
const EMBED = new URLSearchParams(location.search).has("embed");
if (EMBED) document.documentElement.classList.add("embed");
// Keep embedded pages in step with the host's theme (same origin, so storage events reach the iframe).
addEventListener("storage", e => { if (e.key === "leap-theme" && e.newValue) { themeMode = e.newValue; applyTheme(); } });

const drawer = { el: null, id: null, last: null };
function drawerEl() {
  if (drawer.el) return drawer.el;
  const d = document.createElement("div");
  d.className = "drawer"; d.hidden = true;
  d.innerHTML = `<div class="drawer-scrim" data-close></div>
    <section class="drawer-panel" role="dialog" aria-modal="true" aria-labelledby="drawerTitle">
      <header class="drawer-bar">
        <button type="button" class="drawer-x" data-close aria-label="Close">×</button>
        <div class="drawer-t"><span class="kicker">Solved problem</span><span id="drawerTitle"></span></div>
        <a class="btn" id="drawerFull" href="#" target="_blank" rel="noopener">Open as page ↗</a>
      </header>
      <iframe class="drawer-frame" title="Problem"></iframe>
    </section>`;
  document.body.appendChild(d);
  d.addEventListener("click", e => { if (e.target.closest("[data-close]")) closeProblem(); });
  drawer.el = d; return d;
}
function openProblem(id) {
  const p = PROBLEMS.find(x => x.id === id); if (!p) return;
  const d = drawerEl(), frame = d.querySelector("iframe");
  drawer.id = id; drawer.last = document.activeElement;
  $("#drawerTitle").innerHTML = titleHTML(p);
  $("#drawerFull").href = problemUrl(p);
  const src = problemUrl(p) + "&embed=1";
  if (!frame.src.endsWith(src)) frame.src = src;
  d.hidden = false; document.documentElement.classList.add("drawer-on");
  d.offsetWidth; // start the slide from the closed position
  d.classList.add("open");
  d.querySelector(".drawer-x").focus({ preventScroll: true });
}
function closeProblem() {
  const d = drawer.el; if (!d || d.hidden) return;
  d.classList.remove("open"); document.documentElement.classList.remove("drawer-on");
  setTimeout(() => { if (!d.classList.contains("open")) d.hidden = true; }, reduced() ? 0 : 560);
  drawer.id = null;
  if (drawer.last && drawer.last.focus) drawer.last.focus({ preventScroll: true });
}
addEventListener("keydown", e => { if (e.key === "Escape" && drawer.id) closeProblem(); });
// The embedded page reports which problem it shows (previous/next navigate inside the drawer).
addEventListener("message", e => {
  if (e.origin !== location.origin || !e.data || e.data.type !== "leap:problem" || !drawer.id) return;
  const p = PROBLEMS.find(x => x.id === e.data.id); if (!p) return;
  drawer.id = p.id; $("#drawerTitle").innerHTML = titleHTML(p); $("#drawerFull").href = problemUrl(p);
});
// On list pages, links to a problem open the drawer (modifier clicks still open a new tab).
function enableDrawer() {
  document.addEventListener("click", e => {
    const a = e.target.closest('a[href^="problem.html?id="]');
    if (!a || a.closest(".drawer") || e.defaultPrevented || e.button !== 0 || e.metaKey || e.ctrlKey || e.shiftKey || e.altKey) return;
    e.preventDefault(); openProblem(new URLSearchParams(a.getAttribute("href").split("?")[1]).get("id"));
  });
}
