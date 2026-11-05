#!/usr/bin/env python3
"""Build the theorem catalogue as a Hugging Face dataset, and upload it if asked.

Without `--push` this only writes `catalogue.jsonl`, `formalization.yaml` and a dataset card to `--out`, and
touches nothing remote. With `--push REPO` it uploads that directory to the dataset `REPO`, using the token in
the environment variable HF_TOKEN; it needs the package `huggingface_hub`.

Usage: python3 scripts/publish_dataset.py [--out DIR] [--push REPO] [--tag TAG]
"""

import argparse
import json
import os
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import catalogue as cat  # noqa: E402

CARD = """---
license: apache-2.0
pretty_name: Extreme Value Theory in Lean, theorem catalogue
tags:
- lean4
- formal-verification
- theorem-proving
- extreme-value-theory
- mathematics
configs:
- config_name: default
  data_files: catalogue.jsonl
---

# Extreme Value Theory in Lean: theorem catalogue

The headline results of the [Lean 4 library]({repository}) ({version}, DOI
[{doi}](https://doi.org/{doi})), one record per theorem, with its statement as Lean reports it.

Each record has an `area`, an `id`, a `name`, the `source` (book or paper and theorem number, as cited by the
library), the `lean_name` and `file`, the `statement`, a `status`, a `scope_note` saying what is left out, and
the `axioms` of the proof.

- `full`: the statement is the claim ({full}).
- `wrapper`: it restates Mathlib ({wrapper}).
- `reduced`: weaker than the result it is named after: a special case, an extra hypothesis, or part of the
  conclusion assumed ({reduced}).

The proofs are checked by Lean's kernel. **The statements, tests, audits, statuses and scope notes were written
by AI, and no human expert has reviewed them.** A `full` status is that judgement, not a guarantee. Theorem
numbers were not re-checked against the books. See `formalization.yaml` for the provenance.
"""


def build(out):
    catalogue = cat.load()
    errors = cat.schema_errors(catalogue)
    if errors:
        sys.exit("catalogue: invalid:\n" + "\n".join(errors))
    out.mkdir(parents=True, exist_ok=True)
    with (out / "catalogue.jsonl").open("w", encoding="utf-8") as f:
        for area, entries in catalogue.items():
            for e in entries:
                f.write(json.dumps({"area": area, **e}, ensure_ascii=False) + "\n")
    shutil.copy(cat.PROVENANCE, out / "formalization.yaml")
    citation = (cat.ROOT / "CITATION.cff").read_text(encoding="utf-8")
    field = lambda name: next(l.split(":", 1)[1].strip().strip('"') for l in citation.splitlines()
                              if l.startswith(name + ":"))
    _, totals = cat.status_counts(catalogue)
    card = CARD.format(repository=field("repository-code"), version="v" + field("version"), doi=field("doi"),
                       **{s: totals[s] for s in cat.STATUSES})
    (out / "README.md").write_text(card, encoding="utf-8")
    print(f"wrote {sum(totals.values())} entries to {out}")


def push(out, repo, tag):
    token = os.environ.get("HF_TOKEN")
    if not token:
        sys.exit("publish: HF_TOKEN is not set")
    from huggingface_hub import HfApi

    api = HfApi(token=token)
    api.create_repo(repo, repo_type="dataset", exist_ok=True)
    api.upload_folder(repo_id=repo, repo_type="dataset", folder_path=str(out),
                      commit_message=f"Catalogue at {tag}" if tag else "Update the catalogue")
    if tag:
        api.create_tag(repo, repo_type="dataset", tag=tag, exist_ok=True)
    print(f"published to https://huggingface.co/datasets/{repo}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, default=Path("dist/dataset"))
    parser.add_argument("--push", metavar="REPO", help="upload to this Hugging Face dataset")
    parser.add_argument("--tag", help="the release tag, recorded on the dataset")
    args = parser.parse_args()
    build(args.out)
    if args.push:
        push(args.out, args.push, args.tag)


if __name__ == "__main__":
    main()
