# Agent workflow

A Lean 4 library of extreme value theory on Mathlib. Conventions are in `docs/DESIGN.md`, rules for all
contributors in `CONTRIBUTING.md`, setup failures in `docs/TROUBLESHOOTING.md`.

## Setting up

Work in a git worktree on its own branch, one per task. Clone the build directory from the main checkout
instead of rebuilding:

```sh
cp -cR /path/to/main/checkout/.lake ./.lake     # instant on APFS (macOS)
cp -a --reflink=auto /path/to/main/checkout/.lake ./.lake   # Linux
```

`lake` is at `~/.elan/bin/lake`, which may not be on `PATH`. If a build fails with "too many open files",
retry it; it is not an error in the code.

To check one file: `~/.elan/bin/lake env lean path/to/File.lean`.

## Saving work

- Commit checkpoints often and push them to `wip/<task>`: `git push -u origin HEAD:wip/<task>`.
- Open a draft pull request for long tasks, so the work survives the session.
- Add named files only. Never `git add -A`.
- Never push to `main`.
- Never leave `sorry` in a checkpoint without saying so in the commit message.

## Before merging

Run all of these:

```sh
~/.elan/bin/lake build
~/.elan/bin/lake build Test
python3 scripts/check_source.py
```

Then check that:

- only the standard axioms appear (`Test/AxiomAudit.lean` reports them in `lake build Test`);
- blueprint `\lean{}` names resolve (the command is in `CONTRIBUTING.md`);
- no blueprint `\section` title contains bare math; use `\texorpdfstring{$x$}{x}`;
- new files are imported from `ExtremeValueTheory.lean` or `Test.lean`.

## Keep claims honest

- A docstring or a sentence of prose must not outrun the statement. Say what is assumed, not just what is
  concluded, and record every way a result is narrower than its source.
- A theorem with a strong hypothesis is not the textbook theorem. A hypothesis that assumes the hard part
  must be named as such.
- Add a non-vacuity or known-answer test in `Test/` for a new headline result.
- Do not report a build, a test or a literature check you did not run.

## At merge

Update in the same change: `README.md` (results, limitations, counts), `THEOREMS.md`, `FAITHFULNESS.md`, and
`ROADMAP.md` (the Version 1.0 checklist and the Work-in-flight table).

Merge with a merge commit, never a squash.
