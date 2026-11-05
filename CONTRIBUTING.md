# Contributing

**The most useful contribution is a correction.** Lean checks the proofs, not whether a statement says
what its textbook says. If a formal statement differs from its source, open a
[statement bug](.github/ISSUE_TEMPLATE/statement-bug.md). You need no Lean for this, and
[`docs/REVIEW.md`](docs/REVIEW.md) is written for readers who do not use it.

New here? [`docs/ONBOARDING.md`](docs/ONBOARDING.md) goes from clone to merged pull request, and
[`docs/TROUBLESHOOTING.md`](docs/TROUBLESHOOTING.md) covers setup failures. Issues labelled
`good first issue` are the place to start; labels are explained in
[`docs/ISSUE_LABELS.md`](docs/ISSUE_LABELS.md). Participation is under the
[Code of Conduct](CODE_OF_CONDUCT.md).

## Setup

Install [elan](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/unbalancedparentheses/lean-extremevaluetheory.git
cd lean-extremevaluetheory
lake exe cache get   # prebuilt Mathlib; no Docker or registry login needed
lake build           # the library compiles from source the first time
```

To check one file while you work: `lake env lean path/to/File.lean`.

## Where things go

The full conventions, including naming, are in [`docs/DESIGN.md`](docs/DESIGN.md).

| Content | Location |
|---|---|
| general probability or measure theory, Mathlib imports only | `ForMathlib/` |
| c.d.f.s, affine action, types, the law bridge | top-level files |
| GEV, max-stability | `GEV/`, `MaxStable/` |
| regular variation | `RegularVariation/` |
| domains of attraction, named examples | `DomainOfAttraction/` |
| peaks over threshold, GPD | `PeaksOverThreshold/` |
| heavy tails, ruin; stable laws | `HeavyTails/`; `StableLaws/` |
| stationary sequences, extremal index, tail process | `Dependence/` |
| multivariate extremes; point processes | `Multivariate/`; `PointProcess/` |
| estimators and their asymptotics | `Statistics/` |
| sharpness of hypotheses | `Minimality/` |
| checks of the statements | `Test/` |

A lemma goes where a user would look for it: next to the definition it evaluates, or next to the theorem
it feeds.

## Rules

- **No `sorry`, standard axioms only:** `propext`, `Classical.choice`, `Quot.sound`. `lake build Test`
  fails otherwise.
- **Faithful docstrings.** Cite the source with its theorem number and state what is actually proved,
  including every way it is narrower than the source. A docstring must not outrun its statement.
- **Reuse before writing.** Search the library and Mathlib first. Do not add a second definition of a
  concept; prove a bridge to the existing one.
- **Register new files.** Every library file is imported from `ExtremeValueTheory.lean`; every test file
  from `Test.lean`.
- **Renames leave a deprecated alias** (see Deprecation in `docs/DESIGN.md`). A changed statement gets a new
  name.

## Checklist before a pull request

```sh
lake build
lake build Test
python3 scripts/check_source.py
```

If you changed or renamed a declaration named in the blueprint, check that every `\lean{}` name still
resolves (CI runs the same `checkdecls`). This command prints nothing when all is well:

```sh
python3 -c "import re,glob;print('\n'.join(sorted({n.strip() for f in glob.glob('blueprint/src/sections/*.tex') for m in re.findall(r'\\\\lean\{([^}]*)\}',re.sub(r'(?m)(?<!\\\\)%.*$','',open(f).read())) for n in m.split(',') if n.strip()})))" > .lake/lean_decls
lake exe checkdecls .lake/lean_decls
```

Blueprint section titles must not contain bare math: write
`\section{\texorpdfstring{$\xi = 0$}{xi = 0}}`.

## Credit

- Pull requests are merged with a merge commit, never squashed, so your commits reach `main` as you wrote
  them.
- Put your own name on the `Copyright` and `Authors:` lines of the files you create. In a file you change
  substantially, add your name to `Authors:`. Files derived from ExtremeValueProject keep their original
  headers (see [`NOTICE`](NOTICE)).
- If you commit under more than one name or email, add a line to `.mailmap` (create it if it is missing).
- Add yourself to the Acknowledgements section of the [README](README.md) in your first pull request.
