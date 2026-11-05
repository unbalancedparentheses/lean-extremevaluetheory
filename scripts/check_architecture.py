#!/usr/bin/env python3
"""Checks on the shape of the library, run in CI.

* `ForMathlib/` imports only Mathlib and `ForMathlib/`, so that it can be upstreamed.
* Review deadline: the library has at most `margin` more theorems than at the last audit, recorded in
  `Test/AUDIT_BASELINE`. A script cannot judge an audit, only notice that one is due.

With `--duplicates`, after a build: definitions with the same body, found on elaborated terms by
`scripts/DuplicateDefinitions.lean`. This only reports for now, because PR #4 is removing the ones
it finds; add `--strict` to fail on them. It first checks that it catches a bad definition.

`--self-test` runs the first two on temporary bad files, and the source check's `sorry` exemption too.

Usage: python3 scripts/check_architecture.py [--self-test | --count | --duplicates [--strict]]
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from check_source import check as check_source_file
from check_source import strip_comments_and_strings

LIBRARY = Path("ExtremeValueTheory")
BASELINE = Path("Test/AUDIT_BASELINE")
FAITHFULNESS = Path("FAITHFULNESS.md")

IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)", re.MULTILINE)
THEOREM = re.compile(r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec)\s+)*theorem\s", re.MULTILINE)
DUPLICATES_SCRIPT = Path("scripts/DuplicateDefinitions.lean")
DUPLICATE_LINE = re.compile(r"duplicate definitions: (.*)")


def code(path: Path) -> str:
    return strip_comments_and_strings(path.read_text(encoding="utf-8"))


def lean_files(root: Path) -> list[Path]:
    return sorted((root / LIBRARY).rglob("*.lean"))


def formathlib_imports(root: Path) -> list[str]:
    """Imports in `ForMathlib/` of anything but Mathlib and `ForMathlib/`."""
    allowed = re.compile(r"(?:Mathlib|ExtremeValueTheory\.ForMathlib)(?:\.|$)")
    return [
        f"{f}: imports {m}, but ForMathlib/ may import only Mathlib and ForMathlib/"
        for f in sorted((root / LIBRARY / "ForMathlib").rglob("*.lean"))
        for m in IMPORT.findall(code(f))
        if not allowed.match(m)
    ]


def duplicate_definitions(script: Path) -> list[list[str]]:
    """Groups of definitions with the same body, as reported by the Lean script."""
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    run = subprocess.run([lake, "env", "lean", str(script)], capture_output=True, text=True)
    if run.returncode != 0:
        raise RuntimeError(f"{script} failed:\n{run.stdout}{run.stderr}")
    return [m[1].split(", ") for m in DUPLICATE_LINE.finditer(run.stdout)]


def duplicates(strict: bool) -> int:
    with tempfile.TemporaryDirectory() as d:
        bad = Path(d) / "Bad.lean"
        marker = "open Lean Elab Command Meta\n"
        bad.write_text(
            DUPLICATES_SCRIPT.read_text(encoding="utf-8").replace(
                marker,
                "noncomputable def BadA (x : ℝ) : ℝ := Real.exp x + Real.log x + 1\n"
                "noncomputable def BadB (y : ℝ) : ℝ := Real.exp y + Real.log y + 1\n"
                "noncomputable def NotBad (x : ℝ) : ℝ := Real.exp x + Real.log x + 2\n" + marker,
            ),
            encoding="utf-8",
        )
        found = [g for g in duplicate_definitions(bad) if "BadA" in g or "NotBad" in g]
    if found != [["BadA", "BadB"]]:
        print(f"check_architecture: the duplicate scan missed a bad definition, it found {found}")
        return 1
    groups = duplicate_definitions(DUPLICATES_SCRIPT)
    for group in groups:
        print("duplicate definitions: " + ", ".join(group))
    print(f"check_architecture: {len(groups)} groups of duplicate definitions")
    return 1 if strict and groups else 0


def theorem_count(root: Path) -> int:
    return sum(len(THEOREM.findall(code(f))) for f in lean_files(root))


def review_deadline(root: Path) -> list[str]:
    """Fails if the library outgrew the baseline, or the audit behind it is not recorded."""
    fields = dict(
        line.split(": ", 1)
        for line in (root / BASELINE).read_text(encoding="utf-8").splitlines()
        if line and not line.startswith("#")
    )
    count, baseline, margin = theorem_count(root), int(fields["theorems"]), int(fields["margin"])
    problems = []
    if count > baseline + margin:
        problems.append(
            f"{count} theorems, more than {margin} past the {baseline} of the last audit "
            f"({fields['audit']}): an audit is due. Record it in {FAITHFULNESS}, then update {BASELINE}."
        )
    headings = (root / FAITHFULNESS).read_text(encoding="utf-8").splitlines()
    if not any(line.startswith("## ") and fields["audit"] in line for line in headings):
        problems.append(f"{BASELINE} names the audit `{fields['audit']}`, which has no heading in {FAITHFULNESS}")
    return problems


def self_test() -> int:
    def write(root: Path, name: str, text: str) -> None:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    failures = []

    def expect(what: str, ok: bool) -> None:
        print(f"{'ok  ' if ok else 'FAIL'} {what}")
        if not ok:
            failures.append(what)

    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        write(root, "ExtremeValueTheory/ForMathlib/Good.lean",
              "public import Mathlib.Order.Basic\nimport ExtremeValueTheory.ForMathlib.Other\n-- import Bad\n")
        expect("ForMathlib: Mathlib and ForMathlib imports are accepted", not formathlib_imports(root))
        write(root, "ExtremeValueTheory/ForMathlib/Bad.lean", "import ExtremeValueTheory.GEV.Family\n")
        expect("ForMathlib: a library import is rejected", len(formathlib_imports(root)) == 1)

    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        write(root, "ExtremeValueTheory/A.lean",
              "theorem a : True := trivial\n\nprivate theorem b : True := trivial\n\n-- theorem c\n")
        write(root, "FAITHFULNESS.md", "# Audits\n\n## Sixth audit (late)\n")
        write(root, "Test/AUDIT_BASELINE", "# comment\ntheorems: 1\nmargin: 1\naudit: Sixth audit\n")
        expect("deadline: counts theorems, not comments", theorem_count(root) == 2)
        expect("deadline: within the margin is accepted", not review_deadline(root))
        write(root, "Test/AUDIT_BASELINE", "theorems: 1\nmargin: 0\naudit: Sixth audit\n")
        expect("deadline: past the margin is rejected", len(review_deadline(root)) == 1)
        write(root, "Test/AUDIT_BASELINE", "theorems: 2\nmargin: 0\naudit: Seventh audit\n")
        expect("deadline: an unrecorded audit is rejected", len(review_deadline(root)) == 1)

    cwd = Path.cwd()
    with tempfile.TemporaryDirectory() as d:
        os.chdir(d)
        try:
            write(Path("."), "Challenge.lean", "theorem t : False := sorry\n")
            write(Path("."), "Solution.lean", "theorem t : False := sorry\n")
            write(Path("."), "Test/Challenge.lean", "theorem t : False := sorry\n")
            expect("sorry: allowed in Challenge.lean", not check_source_file(Path("Challenge.lean")))
            expect("sorry: rejected in Solution.lean", bool(check_source_file(Path("Solution.lean"))))
            expect("sorry: rejected in another file named Challenge.lean",
                   bool(check_source_file(Path("Test/Challenge.lean"))))
            write(Path("."), "Challenge.lean", "axiom a : False\ntheorem t : False := by native_decide\n")
            expect("sorry: Challenge.lean is exempt from nothing else",
                   len(check_source_file(Path("Challenge.lean"))) == 2)
        finally:
            os.chdir(cwd)

    print(f"check_architecture self-test: {len(failures)} failures")
    return 1 if failures else 0


def main() -> int:
    args = sys.argv[1:]
    if args == ["--self-test"]:
        return self_test()
    if args == ["--count"]:
        print(theorem_count(Path(".")))
        return 0
    if args in (["--duplicates"], ["--duplicates", "--strict"]):
        return duplicates("--strict" in args)
    if args:
        print(__doc__, file=sys.stderr)
        return 2
    root = Path(".")
    problems = formathlib_imports(root) + review_deadline(root)
    for p in problems:
        print(p)
    print(f"check_architecture: {len(problems)} problems, {theorem_count(root)} theorems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
