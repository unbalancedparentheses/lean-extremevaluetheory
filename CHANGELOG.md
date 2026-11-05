# Changelog

## Unreleased (planned as v0.10.0)

Still no human expert review: the statements, tests and audits were written with AI assistance. See the README's
Limitations section.

- **GEV likelihood:** joint asymptotic normality of the three-parameter maximum likelihood estimator and unconditional
  return-level normality, for `ξ₀ > −1/2`, `ξ₀ ≠ 0`.
- **Wilks' theorem and profile-likelihood intervals** for the GPD with `ξ₀ > 0`, and a chi-squared law.
- **Pickands estimator normality** for every shape, and nonparametric tail dependence estimation.
- The normal, Gamma and Cauchy laws' domains of attraction with explicit constants, and stronger regular variation
  (Karamata without monotonicity, uniform-convergence tails), after comparison with Hirata's Isabelle development.
- One definition per concept, with deprecated aliases. `gpdSurvivalNonneg` is deprecated; `extRVLimit`, `gpdSurvivalInv`,
  `gaussianTail` and `stdExpMeasure` give way to `boxCox`, `gevTransform`, `tail` and `expMeasure 1`.
- Comparator challenge, theorem catalogue with CI checks, review deadline, architecture checks, contributor docs.
- Seventh and eighth faithfulness audits, and tutorial, worked and applied examples.
- A new `Examples` library, built in CI and importing only the umbrella: a tutorial (`docs/TUTORIAL.md`), the
  standard laws and three applied problems. A guide to finding results (`docs/FINDING_RESULTS.md`).
- New in the library: domains of attraction of the GPD, GEV, Cauchy and Student t laws, explicit norming constants
  (`DomainOfAttraction/NamedLaws.lean`), reinsurance layers (`HeavyTails/Layer.lean`) and Hill consistency for a
  sample with a given law (`Statistics/HillOfLaw.lean`).
- Seventh faithfulness audit: every result added since the sixth, new rows, and scope notes and docstrings
  corrected where they outran their statements. Verdicts lowered to DIFFERS for the blocks, runs and intervals
  estimators, return levels and GARCH.
- `AC(rₙ)` at the critical scale: it fails for every `c > 0` when `rₙ ~ c n^{γ/α}`, and holds when
  `rₙ = o(n^{γ/α})` (`powEchoProcess_antiClustering_iff_critical`).
- The defining property of the POT return level (`gpdSurvivalAll_gpdReturnLevel_sub`); second and fourth
  Gaussian moments.
- Non-vacuity tests for return levels and intervals, the Hill interval, GARCH with Gaussian innovations and
  the newest estimators of the extremal index; known answers from two worked examples of Coles (2001).
- Non-vacuity tests for the answer to Bai–Kulik–Wang's question (on both sides of the cutoff), for mixing
  without `θ = ϑ` (at each of its three block scales) and for the warning about short runs (with all its
  rates realized).
- README, website and repository description rewritten in a plainer style, with the main results as
  mathematics and a Verification section.

## v0.9.0 (2026-11-04)

The first release, on Lean and Mathlib v4.35.0. It is usable and citable, but no human expert has
reviewed it yet: the statements, tests and audits were written with AI assistance. See the README's
Limitations section for where results are narrower than their textbook form.

**Contents.** About 100,000 lines and 4,300 theorems and lemmas, with no `sorry`:

- limits of maxima (Fisher–Tippett–Gnedenko), max-stability, domains of attraction;
- regular variation, Karamata, Potter bounds, Breiman's lemma;
- peaks over threshold (Pickands–Balkema–de Haan);
- stable laws, the generalized central limit theorem, subexponential laws, ruin asymptotics;
- Hill, Pickands, moment, Weissman and L-moment estimators; GPD and GEV likelihood; return levels and
  confidence intervals;
- extremes of dependent sequences: Leadbetter's theorem, the extremal index, the tail process, AR(1),
  ARMAX, linear processes, Markov chains, `X = AX + B`, GARCH(1,1);
- multivariate regular variation, max-stable vectors, the multivariate generalized Pareto law;
- Poisson random measures, exceedance point processes, the Skorokhod space, the tail empirical process;
- counterexamples showing which hypotheses are needed, and the echo processes.

**Checks.**

- CI fails if any library declaration depends on an axiom other than `propext`, `Classical.choice` and
  `Quot.sound` (`Test/AxiomAudit.lean`), or if the source contains `sorry`, a new axiom or a search
  tactic, or if a library file is not reachable from the umbrella import (`scripts/check_source.py`).
- A nightly job rechecks every declaration with an independent kernel.
- Non-vacuity and known-answer tests in `Test/`, and a weekly build of a fresh project that requires this
  repository (`Downstream/`).
- An AI review by Codex of the headline statements and public claims. It found no blocking problem in the
  statements and several overstated claims, which were corrected. This is not an expert review.

**Stability.** Before 1.0, public names may still change. Renames leave a `@[deprecated]` alias
([`docs/DESIGN.md`](docs/DESIGN.md)).

**Not in this release.** Three-parameter GEV likelihood normality, Pickands and moment estimator normality,
profile-likelihood intervals, nonparametric tail-dependence estimation and the consolidation of duplicate
definitions are in progress in pull requests #4–#8.
