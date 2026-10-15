#!/usr/bin/env python3
"""Copy the files the site needs from a finished LEAP-CLI run into problems/<id>/.

Usage:
  python3 scripts/import_run.py <run_dir> <problem_id> [--informal path/to/proof.md]

From <run_dir> it copies only:
  problem.lean               -> problems/<id>/problem.lean     (the statement)
  proof_graph.json           -> problems/<id>/proof_graph.json (the proof DAG)
  solution/answer.lean       -> problems/<id>/answer.lean      (the verified proof)
  reference/*.md or --informal -> problems/<id>/informal.md    (the informal proof)

Everything else in a run (nodes/, logs, .dot/.svg renders, orchestrator logs) is
not used by the site. meta.json is created if missing and its "files", "loc",
"dag_lemmas" and "lean.root" fields are updated; the id is appended to problems/index.json.
"""

import argparse
import glob
import json
import pathlib
import re
import shutil
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PROBLEMS = ROOT / "problems"
PRIVATE = re.compile(r"/usr/local/google|/home/[a-z]|/Users/[A-Za-z]")


def main() -> None:
  ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
  ap.add_argument("run_dir", type=pathlib.Path)
  ap.add_argument("problem_id")
  ap.add_argument("--informal", type=pathlib.Path, help="Markdown informal proof (default: the run's reference/*.md)")
  args = ap.parse_args()

  run, pid = args.run_dir, args.problem_id
  out = PROBLEMS / pid
  out.mkdir(parents=True, exist_ok=True)
  files = {}

  def take(src: pathlib.Path | None, name: str, key: str) -> None:
    if src and src.is_file():
      shutil.copyfile(src, out / name)
      files[key] = name
      text = (out / name).read_text(errors="ignore")
      if PRIVATE.search(text):
        print(f"warning: {name} contains what looks like a local path; check it before publishing", file=sys.stderr)
    else:
      print(f"note: no {key} file found ({src})", file=sys.stderr)

  take(run / "problem.lean", "problem.lean", "statement")
  take(run / "proof_graph.json", "proof_graph.json", "dag")
  proof = run / "solution" / "answer.lean"
  take(proof if proof.is_file() else run / "assembled" / "final_proof.lean", "answer.lean", "proof")
  refs = sorted(glob.glob(str(run / "reference" / "*.md")))
  take(args.informal or (pathlib.Path(refs[0]) if refs else None), "informal.md", "informal")

  meta_path = out / "meta.json"
  meta = json.loads(meta_path.read_text()) if meta_path.exists() else {
      "title": pid, "subtitle": None, "collection": "Classic problems", "variant": None, "marks": "",
      "featured": False, "area": None, "credit": None, "added": None, "summary": "", "problem": [],
      "statement": None, "notes": [], "links": [], "lean": {}}
  meta["files"] = files
  if "proof" in files:
    meta["loc"] = sum(1 for _ in open(out / "answer.lean", encoding="utf-8", errors="ignore"))
  if "dag" in files:
    graph = json.loads((out / "proof_graph.json").read_text())
    meta.setdefault("lean", {})["root"] = next(iter(graph["nodes"]))
    meta["dag_lemmas"] = len(graph["nodes"])
  meta_path.write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n")

  index_path = PROBLEMS / "index.json"
  index = json.loads(index_path.read_text())
  if pid not in index["order"]:
    index["order"].append(pid)
    index_path.write_text(json.dumps(index, indent=2) + "\n")

  size = sum(f.stat().st_size for f in out.iterdir()) / 1e6
  print(f"problems/{pid}: {', '.join(files.values())} ({size:.1f} MB). Fill in the text fields of meta.json.")


if __name__ == "__main__":
  main()
