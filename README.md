# LEAP web

The project page for LEAP and LEAP-CLI: the framework, the problems it has
solved, and an explorer for each proof (problem statement, informal proof,
Lean proof and proof DAG).

It is a static site with no build step. Problems are data files under
`problems/`, so adding a result never touches the page code.

## Run it locally

The page loads its data with `fetch`, so serve it over HTTP rather than opening
`index.html` from disk:

```bash
cd ~/Sites/LEAP_WEB
python3 -m http.server 8000
```

Then open <http://localhost:8000>.

## Layout

```
index.html              home: intro, featured problems, how LEAP works, run it, cite
problems.html           every solved problem, with filters and search
problem.html?id=<id>    one problem: statement, proof DAG, informal proof, Lean proof
assets/css/site.css     styles (light by default, dark via the theme button)
assets/js/common.js     shared: theme, problem loading, DAG model and sample generator
assets/js/home.js       featured cards, headline sentence, pipeline animation
assets/js/problems.js   the results table
assets/js/problem.js    the problem page and the DAG / outline explorer
problems/index.json     display order: {"order": ["hilbert-10", ...]}
problems/<id>/meta.json text and metadata for one problem
problems/<id>/*         the files from a LEAP-CLI run (see below)
scripts/import_run.py   copies those files out of a run directory
```

On the home page and the problem list, clicking a problem slides its page in
from the right (an iframe of `problem.html?id=<id>&embed=1`, which hides the site
header). Escape, the close button or the backdrop closes it. The panel does not
change the page URL.

Problem pages also work on their own, including a tab:
`problem.html?id=erdos-289#informal` (also `#lean`, `#dag`).

The headline sentence on the home page is computed from the data: the number of
problems, the largest `loc`, and the largest `dag_lemmas` (set by
`import_run.py` from `proof_graph.json`).

## Adding a solved problem

### 1. Copy the run files

A LEAP-CLI run directory holds about 10 MB, mostly per-node logs and scratch
work. The site needs four files from it:

| File in the run | Copied to | Shown as |
| --- | --- | --- |
| `problem.lean` | `problems/<id>/problem.lean` | The Lean statement |
| `proof_graph.json` | `problems/<id>/proof_graph.json` | The proof DAG, with each lemma's statement and Lean code |
| `solution/answer.lean` | `problems/<id>/answer.lean` | The full verified proof, downloadable |
| `reference/*_proof_playbook.md` | `problems/<id>/informal.md` | The informal proof (Markdown with LaTeX) |

Everything else is not used: `nodes/`, `orchestrator_log.md`,
`ORIGINAL_REQUEST.md` (it contains internal paths), `proof_graph.dot`,
`proof_graph.svg`, `assembled/` (same as `solution/answer.lean`) and the
`.lock` file.

The script copies the four files, fills in `files`, `loc` and `lean.root` in
`meta.json`, and adds the id to `problems/index.json`:

```bash
python3 scripts/import_run.py /path/to/runs/erdos289_le05 erdos-289
# use a different informal proof:
python3 scripts/import_run.py /path/to/run erdos-289 --informal notes/erdos289.md
```

It warns if a copied file appears to contain a local path.

### 2. Write the text in `meta.json`

```json
{
  "title": "Erdős Problem #289",
  "subtitle": null,
  "collection": "Erdős problems",
  "number": 289,
  "variant": null,
  "marks": "",
  "featured": false,
  "area": "Number theory · Egyptian fractions",
  "loc": 9544,
  "credit": null,
  "added": "2026-10",
  "summary": "One or two sentences for the table and the featured card.",
  "problem": ["Paragraphs describing the problem."],
  "statement": "Optional display line, e.g. 1 = ∑ᵢ ∑_{n ∈ Iᵢ} 1/n",
  "notes": [{ "title": "Formalization note", "text": "…" }],
  "links": [{ "label": "erdosproblems.com/289", "url": "https://www.erdosproblems.com/289" }],
  "lean": { "repo": "https://github.com/…", "root": "erdos_289" },
  "files": {
    "statement": "problem.lean",
    "dag": "proof_graph.json",
    "proof": "answer.lean",
    "informal": "informal.md"
  }
}
```

- `featured: true` puts the problem in the featured carousel on the home page.
  Every featured problem is shown, three at a time; around five works best.
- `collection` drives the filter chips (for example "Erdős problems").
- `variant` and `marks` are shown after the title, for example `hegyvari` and `*`.
- Text in `summary`, `problem` and `notes` accepts `` `code` ``, `**bold**` and `[links](https://…)`.
- Any entry in `files` can be left out. The page then shows a "will be published
  here" note for that tab, and a problem without a `dag` file shows a generated
  sample DAG that is marked as sample data.

### 3. Check it

Reload the local server and open `http://localhost:8000/problem.html?id=<id>`. Check the three
tabs: Proof DAG, Informal proof and Lean proof.

## The DAG format

The explorer reads `proof_graph.json` exactly as LEAP-CLI writes it: `nodes` is
an object keyed by lemma id, and each node's `and_nodes` lists its
decomposition attempts (`dependency_ids`, `failed`). A lemma's code comes from
`formal_theorem` (a full proof) or `formal_sketch` (a sketch whose `have`
statements are its children).

It also accepts a smaller hand-written format:

```json
{
  "nodes": [{ "id": "n0", "name": "main_thm", "statement": "theorem main_thm …", "code": "…", "kind": "composite", "lines": 12, "t": 0 }],
  "edges": [{ "from": "n0", "to": "n1", "attempt": "accepted" }]
}
```

## Editing the page

- Theme colors are tokens at the top of `assets/css/site.css`. Light is the
  default, and the theme button cycles light, dark and auto.
- The pipeline figure is the SVG in the `#how` section of `index.html`. Its
  steps (highlighted stages, DAG states and captions) are the `PIPE` array in
  `assets/js/home.js`.
- External code comes from jsDelivr: KaTeX and marked render the informal proofs.
