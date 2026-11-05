Title: A script that checks the blueprint
Labels: area:tooling, type:tooling, difficulty:small, good first issue, status:ready

## Context
Blueprint names are checked only by the blueprint workflow, after a slow LaTeX build, and `CONTRIBUTING.md` carries a long one-line command to do the same locally. Math in a section title breaks the PDF bookmarks unless it is in `\texorpdfstring`. A script can catch both early. No Lean is needed.

## Task
Write `scripts/check_blueprint.py`, in the style of `scripts/check_source.py`:

1. Read `blueprint/src/sections/*.tex` with comments removed. A commented `%\lean{lcinv}` in `types.tex` must be ignored, and an escaped `\%` is not a comment.
2. Fail, naming the file and line, if a `\section` or `\subsection` title contains `$` outside `\texorpdfstring`.
3. With `--write PATH`, write the `\lean{}` names, which may be comma-separated, to `PATH`, one per line, for `lake exe checkdecls PATH`.

Then add a step to `build.yml` that runs it before the build, and replace the one-line command in `CONTRIBUTING.md`.

## Acceptance criteria
- [ ] The script passes on the current blueprint and writes 1321 names at commit `99fe16a`, all of which `lake exe checkdecls` accepts.
- [ ] It fails on a test title `\section{The case $x$}` (say how you tried this in the pull request).
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `scripts/check_source.py`; `.github/workflows/build.yml`; `.github/workflows/blueprint.yml` for how CI runs `checkdecls`.
