#!/usr/bin/env python3
"""The theorem catalogue: what the library claims, checked against what Lean reports.

`catalogue/<area>.json` is a list of entries, each with:

    id, name          a stable identifier and a human name
    source            the book or paper and theorem number, as cited by the library
    lean_name, file   the declaration, and the file it lives in
    statement         its signature as `#check` prints it, never typed by hand
    status            full     the statement is the claim
                      wrapper  it restates Mathlib
                      reduced  weaker than the result it is named after: a special case, an extra
                               hypothesis, or part of the conclusion assumed
    scope_note        what is left out, and for `reduced` why
    axioms            the axioms the proof depends on
    input_hash        a hash of everything the entry was last checked under

The hash covers the entry's own fields, the toolchain, the Mathlib revision, and the statement's type
together with every library definition it reaches. So changing a definition, or bumping Mathlib, makes the
entry stale even when the statement prints the same.

Commands:

    check                compare every entry with Lean, apply the gate, and fail if anything is stale
    stamp ID... | --all  take the statement from Lean and record the hash; do this only after rereading the
                         statement and its status
    report               counts by status and area (no Lean needed)
    provenance           write formalization.yaml from the catalogue

The gate: an entry with status `full` cannot rest on a theorem proved by `rfl` or by unfolding a definition.
`scripts/CatalogueProbe.lean` decides that (see `triviality` there); this script enforces it.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CATALOGUE = ROOT / "catalogue"
PROVENANCE = ROOT / "formalization.yaml"
PROBE = "scripts/CatalogueProbe.lean"

AREAS = ["classical", "domains", "regular-variation", "pot", "stable", "heavy-tails", "statistics",
         "likelihood", "dependence", "multivariate", "processes", "new-results"]
STATUSES = ["full", "wrapper", "reduced"]
FIELDS = ["id", "name", "source", "lean_name", "file", "statement", "status", "scope_note", "axioms",
          "input_hash"]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

SOURCES = {
    "BDM02": "Basrak, Davis, Mikosch, A characterization of multivariate regular variation, Ann. Appl. Probab. (2002)",
    "BDM16": "Buraczewski, Damek, Mikosch, Stochastic Models with Power-Law Tails (2016)",
    "BGT": "Bingham, Goldie, Teugels, Regular Variation (1987)",
    "BKW": "Bai, Kulik, Wang, arXiv:2409.17966 (2024)",
    "BS09": "Basrak, Segers, Regularly varying multivariate time series, Stoch. Proc. Appl. (2009)",
    "Billingsley": "Billingsley, Convergence of Probability Measures, 2nd ed. (1999)",
    "Breiman": "Breiman, On some limit theorems similar to the arc-sin law, Theory Probab. Appl. (1965)",
    "Coles": "Coles, An Introduction to Statistical Modeling of Extreme Values (2001)",
    "DR85": "Davis, Resnick, Limit theory for moving averages of random variables with regularly varying tail "
            "probabilities, Ann. Probab. (1985)",
    "EGV": "Embrechts, Goldie, Veraverbeke, Subexponentiality and infinite divisibility, Z. Wahrsch. (1979)",
    "EKM": "Embrechts, Klüppelberg, Mikosch, Modelling Extremal Events (1997)",
    "Einmahl": "Einmahl, Limit theorems for tail processes with application to intermediate quantile estimation, "
               "J. Statist. Plann. Inference (1992)",
    "Feller": "Feller, An Introduction to Probability Theory and Its Applications, Vol. II, 2nd ed. (1971)",
    "Ferro-Segers": "Ferro, Segers, Inference for clusters of extreme values, J. R. Stat. Soc. B (2003)",
    "GK": "Gnedenko, Kolmogorov, Limit Distributions for Sums of Independent Random Variables (1954)",
    "HWW": "Hosking, Wallis, Wood, Estimation of the generalized extreme-value distribution by the method of "
           "probability-weighted moments, Technometrics (1985)",
    "Hosking": "Hosking, L-moments, J. R. Stat. Soc. B (1990)",
    "Hosking-Wallis": "Hosking, Wallis, Parameter and quantile estimation for the generalized Pareto distribution, "
                      "Technometrics (1987)",
    "Hult-Lindskog": "Hult, Lindskog, Regular variation for measures on metric spaces, Publ. Inst. Math. (2006)",
    "JM": "Jessen, Mikosch, Regularly varying functions, Publ. Inst. Math. (2006)",
    "Klüppelberg": "Klüppelberg, Subexponential distributions and integrated tails, J. Appl. Probab. (1988)",
    "KS20": "Kulik, Soulier, Heavy-Tailed Time Series (2020)",
    "LLR": "Leadbetter, Lindgren, Rootzén, Extremes and Related Properties of Random Sequences and Processes (1983)",
    "Pickands": "Pickands, Multivariate extreme value distributions, Bull. Int. Statist. Inst. (1981)",
    "Res07": "Resnick, Heavy-Tail Phenomena (2007)",
    "Res87": "Resnick, Extreme Values, Regular Variation, and Point Processes (1987)",
    "RT06": "Rootzén, Tajvidi, Multivariate generalized Pareto distributions, Bernoulli (2006)",
    "ST": "Samorodnitsky, Taqqu, Stable Non-Gaussian Random Processes (1994)",
    "Smith": "Smith, Maximum likelihood estimation in a class of nonregular cases, Biometrika (1985)",
    "Wald": "Wald, Note on the consistency of the maximum likelihood estimate, Ann. Math. Statist. (1949)",
    "Weissman": "Weissman, Estimation of parameters and large quantiles based on the k largest observations, "
                "J. Amer. Statist. Assoc. (1978)",
    "dHF": "de Haan, Ferreira, Extreme Value Theory: An Introduction (2006)",
    "Bücher-Segers": "Bücher, Segers, On the maximum likelihood estimator for the generalized extreme-value "
                     "distribution, Extremes (2017)",
    "Goldie": "Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. (1991)",
    "Hsing": "Hsing, On tail index estimation using dependent data, Ann. Statist. (1991)",
    "Janssen-Segers": "Janssen, Segers, Markov tail chains, J. Appl. Probab. (2014)",
    "Kallenberg": "Kallenberg, Random Measures, Theory and Applications (2017)",
    "Kesten": "Kesten, Random difference equations and renewal theory for products of random matrices, Acta Math. (1973)",
    "Mason": "Mason, Laws of large numbers for sums of extreme values, Ann. Probab. (1982)",
    "Mikosch-Stărică": "Mikosch, Stărică, Limit theory for the sample autocorrelations and extremes of a GARCH(1,1) "
                       "process, Ann. Statist. (2000)",
    "Perfekt": "Perfekt, Extremal behaviour of stationary Markov chains, Ann. Appl. Probab. (1994)",
    "Prescott-Walden": "Prescott, Walden, Maximum likelihood estimation of the parameters of the generalized "
                       "extreme-value distribution, Biometrika (1980)",
    "Resnick-Stărică": "Resnick, Stărică, Consistency of Hill's estimator for dependent data, J. Appl. Probab. (1995)",
    "Rootzén-Leadbetter-de Haan": "Rootzén, Leadbetter, de Haan, On the distribution of tail array sums for strongly "
                                  "mixing stationary sequences, Ann. Appl. Probab. (1998)",
    "Smith-Weissman": "Smith, Weissman, Estimating the extremal index, J. R. Stat. Soc. B (1994)",
    "Weissman-Novak": "Weissman, Novak, On blocks and runs estimators of the extremal index, J. Statist. Plann. "
                      "Inference (1998)",
    "de Haan": "de Haan, A spectral representation for max-stable processes, Ann. Probab. (1984)",
}


def load():
    """All entries, as a dict from area to its list of entries, in file order."""
    return {area: json.loads((CATALOGUE / f"{area}.json").read_text(encoding="utf-8")) for area in AREAS}


def save(catalogue):
    for area, entries in catalogue.items():
        ordered = [{k: e[k] for k in FIELDS} for e in entries]
        text = json.dumps(ordered, ensure_ascii=False, indent=2) + "\n"
        (CATALOGUE / f"{area}.json").write_text(text, encoding="utf-8")


def all_entries(catalogue):
    return [e for entries in catalogue.values() for e in entries]


def schema_errors(catalogue):
    """What can be wrong without asking Lean."""
    errors, seen = [], Counter()
    for e in all_entries(catalogue):
        where = e.get("id", "<no id>")
        for field in FIELDS:
            if field not in e:
                errors.append(f"{where}: missing field `{field}`")
        unknown = set(e) - set(FIELDS)
        if unknown:
            errors.append(f"{where}: unknown fields {sorted(unknown)}")
        if e.get("status") not in STATUSES:
            errors.append(f"{where}: status `{e.get('status')}` is not one of {STATUSES}")
        for field in ["name", "source", "lean_name", "scope_note"]:
            if not e.get(field):
                errors.append(f"{where}: `{field}` is empty")
        seen["id:" + str(e.get("id"))] += 1
        seen["lean_name:" + str(e.get("lean_name"))] += 1
    errors += [f"duplicate {key}" for key, n in seen.items() if n > 1]
    return errors


def ask_lean(names):
    """What `scripts/CatalogueProbe.lean` reports for each name."""
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    with tempfile.TemporaryDirectory() as scratch:
        names_file, out_file = Path(scratch) / "names.txt", Path(scratch) / "out.json"
        names_file.write_text("\n".join(names) + "\n", encoding="utf-8")
        env = dict(os.environ, CATALOGUE_NAMES=str(names_file), CATALOGUE_OUT=str(out_file))
        run = subprocess.run([lake, "env", "lean", PROBE], cwd=ROOT, env=env, capture_output=True, text=True)
        if run.returncode != 0 or not out_file.exists():
            sys.exit(f"catalogue: Lean failed:\n{run.stdout}{run.stderr}")
        return {r["name"]: r for r in json.loads(out_file.read_text(encoding="utf-8"))}


def environment():
    """The toolchain and the Mathlib revision: inputs to every entry."""
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    return {"toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(), "mathlib": mathlib["rev"]}


def source_file(module):
    return module.replace(".", "/") + ".lean"


def input_hash(entry, closure, env):
    inputs = {k: entry[k] for k in FIELDS if k != "input_hash"}
    inputs.update(closure=closure, **env)
    blob = json.dumps(inputs, sort_keys=True, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()[:32]


def entry_errors(e, info, env):
    """Why an entry disagrees with Lean, one message per problem."""
    where = e["id"]
    if not info["found"]:
        return [f"{where}: `{e['lean_name']}` does not resolve"]
    errors = []
    if info["deprecated"]:
        errors.append(f"{where}: `{e['lean_name']}` is deprecated; use the current name")
    if not info["is_theorem"]:
        errors.append(f"{where}: `{e['lean_name']}` is not a theorem")
    if source_file(info["module"]) != e["file"]:
        errors.append(f"{where}: file is {e['file']}, Lean says {source_file(info['module'])}")
    if info["statement"] != e["statement"]:
        errors.append(f"{where}: the stored statement differs from Lean's:\n  stored: {e['statement']}\n  Lean:   "
                      f"{info['statement']}")
    if sorted(info["axioms"]) != sorted(e["axioms"]):
        errors.append(f"{where}: axioms are {sorted(e['axioms'])}, Lean says {sorted(info['axioms'])}")
    if set(info["axioms"]) - STANDARD_AXIOMS:
        errors.append(f"{where}: uses non-standard axioms {sorted(set(info['axioms']) - STANDARD_AXIOMS)}")
    if e["status"] == "full" and info["trivial"]:
        errors.append(f"{where}: GATE: status is `full`, but the theorem is trivial ({info['trivial']}: "
                      f"its proof rests on `rfl` or on unfolding a definition). Mark it `reduced` or `wrapper`, "
                      f"or point the entry at the theorem with the content.")
    if input_hash(e, info["closure"], env) != e["input_hash"]:
        errors.append(f"{where}: stale. An input changed since the entry was checked (its own fields, a definition "
                      f"its statement reaches, the toolchain or Mathlib). Reread the statement and its status, then "
                      f"run `scripts/catalogue.py stamp {where}`.")
    return errors


def cmd_check(_):
    catalogue = load()
    errors = schema_errors(catalogue)
    if errors:
        sys.exit("catalogue: invalid:\n" + "\n".join(errors))
    entries = all_entries(catalogue)
    answers = ask_lean([e["lean_name"] for e in entries])
    env = environment()
    for e in entries:
        errors += entry_errors(e, answers[e["lean_name"]], env)
    if not PROVENANCE.exists() or PROVENANCE.read_text(encoding="utf-8") != provenance_text(catalogue):
        errors.append("formalization.yaml is out of date: run `scripts/catalogue.py provenance`")
    if errors:
        print("\n".join(errors))
        sys.exit(f"catalogue: {len(errors)} problems in {len(entries)} entries")
    print(f"catalogue: {len(entries)} entries match Lean; no `full` entry rests on a trivial proof")


def cmd_stamp(args):
    catalogue = load()
    errors = schema_errors({a: [{**e, "statement": "", "file": "", "axioms": [], "input_hash": ""} for e in es]
                            for a, es in catalogue.items()})
    if errors:
        sys.exit("catalogue: invalid:\n" + "\n".join(errors))
    entries = all_entries(catalogue)
    targets = [e for e in entries if args.all or e["id"] in args.ids]
    missing = set(args.ids) - {e["id"] for e in entries}
    if missing or not targets:
        sys.exit(f"catalogue: nothing to stamp; unknown ids: {sorted(missing)}")
    answers = ask_lean([e["lean_name"] for e in targets])
    env = environment()
    failed = 0
    for e in targets:
        info = answers[e["lean_name"]]
        if not info["found"]:
            print(f"{e['id']}: `{e['lean_name']}` does not resolve")
            failed += 1
            continue
        if e["statement"] and e["statement"] != info["statement"]:
            print(f"{e['id']}: the statement changed; reread it and its status:\n{info['statement']}")
        e["statement"], e["file"], e["axioms"] = info["statement"], source_file(info["module"]), sorted(info["axioms"])
        e["input_hash"] = input_hash(e, info["closure"], env)
    save(catalogue)
    PROVENANCE.write_text(provenance_text(catalogue), encoding="utf-8")
    print(f"catalogue: stamped {len(targets) - failed} entries")
    if failed:
        sys.exit(1)


def status_counts(catalogue):
    counts = {area: Counter(e["status"] for e in entries) for area, entries in catalogue.items()}
    totals = Counter()
    for c in counts.values():
        totals.update(c)
    return counts, totals


def cmd_report(_):
    catalogue = load()
    errors = schema_errors(catalogue)
    if errors:
        sys.exit("catalogue: invalid:\n" + "\n".join(errors))
    counts, totals = status_counts(catalogue)
    print("| area | " + " | ".join(STATUSES) + " | total |")
    print("|---|" + "---|" * (len(STATUSES) + 1))
    for area in AREAS:
        cells = [str(counts[area][s]) for s in STATUSES]
        print(f"| {area} | " + " | ".join(cells) + f" | {sum(counts[area].values())} |")
    cells = [str(totals[s]) for s in STATUSES]
    print("| **all** | " + " | ".join(cells) + f" | {sum(totals.values())} |")


def to_yaml(value, indent=0):
    """Enough YAML for the provenance file: JSON scalars are valid YAML, and PyYAML is not a dependency."""
    pad = " " * indent
    if isinstance(value, dict):
        lines = []
        for k, v in value.items():
            if isinstance(v, (dict, list)) and v:
                lines.append(f"{pad}{k}:\n{to_yaml(v, indent + 2)}")
            else:
                lines.append(f"{pad}{k}: {to_yaml(v)}")
        return "\n".join(lines)
    if isinstance(value, list) and value:
        lines = []
        for v in value:
            if isinstance(v, dict):
                body = to_yaml(v, indent + 2)
                lines.append(f"{pad}- {body[indent + 2:]}")
            else:
                lines.append(f"{pad}- {to_yaml(v)}")
        return "\n".join(lines)
    return json.dumps(value, ensure_ascii=False)


def provenance_text(catalogue):
    citation = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    field = lambda name: re.search(rf"^{name}:\s*\"?([^\"\n]+)\"?$", citation, re.M).group(1).strip()
    env = environment()
    entries = all_entries(catalogue)
    counts, totals = status_counts(catalogue)
    cited = sorted(key for key in SOURCES if any(re.search(rf"(?<![\w-]){re.escape(key)}(?![\w-])", e["source"])
                                                 for e in entries))
    data = {
        "name": field("title"),
        "repository": field("repository-code"),
        "license": field("license"),
        "version": "v" + field("version"),
        "doi": field("doi"),
        "lean": env["toolchain"],
        "mathlib_rev": env["mathlib"],
        "derived_from": {
            "project": "ExtremeValueProject, by Kalle Kytölä and the participants of the Aalto University course "
                       "MS-EV0029",
            "url": "https://github.com/kkytola/ExtremeValueProject",
            "commit": "f7c9a8ce260d5cd526bb7f868010dee5afa7f746",
            "parts": "the Fisher-Tippett-Gnedenko development and its blueprint; see NOTICE",
        },
        "sources": {
            "note": "Theorem numbers are as cited in the library's docstrings and FAITHFULNESS.md. They were not "
                    "re-checked against the books when this catalogue was written.",
            "cited": [{"key": key, "reference": SOURCES[key]} for key in cited],
        },
        "ai_written": {
            "note": "The statements, tests and audits were written by AI. So were the status and scope note of "
                    "every catalogue entry. The written audit is therefore not independent.",
            "parts": ["theorem statements", "specification tests in Test/", "the audits in FAITHFULNESS.md",
                      "catalogue statuses and scope notes"],
        },
        "human_reviewed": {
            "note": "None yet: no human expert has reviewed the statements.",
            "parts": [],
        },
        "machine_checked": {
            "note": "Lean's kernel checks the proofs on every build, and CI re-checks the exported environment with "
                    "an independent checker. This says the proofs are correct, not that the statements are the "
                    "intended ones.",
            "workflows": [".github/workflows/build.yml", ".github/workflows/kernel-check.yml"],
        },
        "axioms": {
            "used_by_catalogue": sorted({a for e in entries for a in e["axioms"]}),
            "audit": "Test/AxiomAudit.lean fails the build if any declaration of the library uses another axiom",
        },
        "catalogue": {
            "entries": len(entries),
            "by_status": {s: totals[s] for s in STATUSES},
            "by_area": {area: {s: counts[area][s] for s in STATUSES} for area in AREAS},
        },
    }
    header = "# Generated by `scripts/catalogue.py provenance`; do not edit by hand. `check` fails if it is stale.\n"
    return header + to_yaml(data) + "\n"


def cmd_provenance(_):
    PROVENANCE.write_text(provenance_text(load()), encoding="utf-8")
    print(f"wrote {PROVENANCE.relative_to(ROOT)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("check").set_defaults(run=cmd_check)
    stamp = commands.add_parser("stamp")
    stamp.add_argument("ids", nargs="*")
    stamp.add_argument("--all", action="store_true")
    stamp.set_defaults(run=cmd_stamp)
    commands.add_parser("report").set_defaults(run=cmd_report)
    commands.add_parser("provenance").set_defaults(run=cmd_provenance)
    args = parser.parse_args()
    args.run(args)


if __name__ == "__main__":
    main()
