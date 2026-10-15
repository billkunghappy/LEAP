/* Solved problems page: the full, filterable list. Each row opens the problem page. */
const T = { filter: "all", q: "" };
function renderChips() {
  const cols = [...new Set(PROBLEMS.map(p => p.collection))];
  const opts = [["all", "All", PROBLEMS.length], ["featured", "Featured", PROBLEMS.filter(p => p.featured).length], ...cols.map(c => [c, c, PROBLEMS.filter(p => p.collection === c).length])];
  $("#chips").innerHTML = opts.map(([k, l, n]) => `<button type="button" class="chip" data-f="${esc(k)}" aria-pressed="${T.filter === k}">${esc(l)} · ${n}</button>`).join("");
}
$("#chips").addEventListener("click", e => { const b = e.target.closest("[data-f]"); if (!b) return; T.filter = b.dataset.f; renderChips(); renderTable(); });
$("#psearch").addEventListener("input", e => { T.q = e.target.value.toLowerCase(); renderTable(); });
function renderTable() {
  const list = PROBLEMS.filter(p => (T.filter === "all" || (T.filter === "featured" ? p.featured : p.collection === T.filter)) &&
    (!T.q || [p.title, p.subtitle, p.area, p.summary, p.variant, ...(p.problem || [])].join(" ").toLowerCase().includes(T.q)));
  if (!list.length) { $("#ptbody").innerHTML = `<tr><td colspan="5" style="padding:18px;color:var(--muted);font-size:13px">No problems match this filter.</td></tr>`; return; }
  $("#ptbody").innerHTML = list.map(p => {
    const av = `<span class="avail"><span class="av${hasInformal(p) ? " on" : ""}" title="Informal proof">INF</span><span class="av${hasLean(p) ? " on" : ""}" title="Lean proof">LEAN</span><span class="av${hasDag(p) ? " on" : ""}" title="Proof DAG">DAG</span></span>`;
    return `<tr class="prow" data-href="${problemUrl(p)}">
      <td><a class="pt" href="${problemUrl(p)}">${p.featured ? '<span class="star" title="Featured">★</span>' : ""}${titleHTML(p)}</a><div class="ps">${md(p.summary)}</div></td>
      <td class="hide-sm">${esc(p.area || "—")}</td>
      <td class="num">${p.loc ? (p.loc >= 20000 ? "~" + kloc(p.loc) : fmt(p.loc)) : "—"}</td>
      <td class="hide-sm">${av}</td>
      <td class="hide-sm num">${esc(p.added || "")}</td></tr>`;
  }).join("");
}
$("#ptbody").addEventListener("click", e => { if (e.target.closest("a")) return; const r = e.target.closest("[data-href]"); if (r) r.querySelector("a.pt").click(); });
boot(() => { $("#pCount").textContent = PROBLEMS.length; renderChips(); renderTable(); enableDrawer(); });
