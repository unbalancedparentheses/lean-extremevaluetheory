# Extreme Value Theory in Lean

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23966372.svg)](https://doi.org/10.5281/zenodo.23966372)
[![Build](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/build.yml/badge.svg)](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/build.yml)
[![Blueprint](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/blueprint.yml/badge.svg)](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/)
[![Kernel check](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/kernel-check.yml/badge.svg)](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/kernel-check.yml)
[![Nix](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/nix.yml/badge.svg)](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/nix.yml)

**The mathematics of rare events, machine-checked.** This is a Lean 4 library, built on Mathlib, that
proves the theory behind floods, heat waves, market crashes and insurance catastrophes: how maxima
behave, how heavy tails look, how to estimate them from data, and how extremes cluster in time.

- **Broad.** The classical theory of maxima and regular variation, peaks over threshold, the
  statistics of extremes (estimators, likelihood, return levels, confidence intervals), stable laws
  and heavy tails, extremes of dependent sequences, multivariate extremes, point processes and the
  Skorokhod space. About 100,000 lines and 4,300 theorems and lemmas, with no `sorry`.
- **Checked twice.** Lean's kernel checks every proof, and CI re-checks all 719,515 declarations
  with an independent checker.
- **Tested against the textbooks.** Proving a theorem is not enough: it has to *state* the right
  thing. About 250 specification tests and six audits check that it does.
- **New mathematics.** Formalizing forced every hypothesis into the open, and that led to new
  results, including an answer to an open question of Bai, Kulik and Wang (2024).

[Website](https://unbalancedparentheses.github.io/lean-extremevaluetheory/) ·
[Blueprint](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/) ·
[API documentation](https://unbalancedparentheses.github.io/lean-extremevaluetheory/docs/) ·
[Roadmap](ROADMAP.md) ·
[Changelog](CHANGELOG.md)

## Start here

| If you are… | Read |
|---|---|
| **A practitioner** using `evd`, `ismev`, `extRemes`, `POT`, `ReIns`, `pyextremes` or `scipy.stats` | [`docs/PRACTITIONERS.md`](docs/PRACTITIONERS.md): which theorem justifies each function, under which assumptions, and the conventions that trip people up (scipy's GEV shape is `c = −ξ`) |
| **An extreme value theorist** who wants to know whether the formal statements are right | [`docs/REVIEW.md`](docs/REVIEW.md), written for readers who do not use Lean, and [`FAITHFULNESS.md`](FAITHFULNESS.md) |
| **A researcher** looking for new results or open problems | [`RESEARCH.md`](RESEARCH.md) and [`docs/PRACTICAL_OPEN_PROBLEMS.md`](docs/PRACTICAL_OPEN_PROBLEMS.md) |
| **A Lean or Mathlib user** | The [blueprint](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/), [`THEOREMS.md`](THEOREMS.md), and [`ForMathlib/`](ExtremeValueTheory/ForMathlib/UPSTREAMING.md), the general results written for Mathlib |

## What a theorem looks like

The Fisher–Tippett–Gnedenko theorem, as stated in the library:

```lean
theorem CumulativeDistributionFunction.IsExtremeValueDistr.classification
    {G : CumulativeDistributionFunction} (hG : G.IsExtremeValueDistr) :
    (∃ (A : AffineIncrEquiv), A • G = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • G = standardFrechetCDF hξ) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • G = standardWeibullCDF hξ)
```

`G.IsExtremeValueDistr` says that `G` is non-degenerate and is the limit of `F(aₙx + bₙ)ⁿ` for some
distribution function `F` and affine normalizations; `A • G` is `G` after an increasing affine change
of variables. So every limit law of normalized maxima is, up to type, Gumbel, Fréchet or Weibull.

And one a hydrologist would recognize: the usual confidence interval for a peaks-over-threshold
return level ("the 100-year flood is 8.2 m ± 0.9") has the coverage it claims, asymptotically
(`tendsto_measure_mem_gpdReturnLevelInterval`).

## Why you can trust it

A formal proof guarantees that the conclusion follows from the hypotheses. It does not guarantee
that the statement says what the textbook says. The library checks both.

| Check | What it rules out | Result |
|---|---|---|
| Lean's kernel, at every build | a wrong proof | every proof checked |
| [`con-leche`](.github/workflows/kernel-check.yml), an independent kernel with a machine-checked proof that it never accepts `False` | a bug in Lean's kernel | all 719,515 declarations accepted (2026-11-04), nightly |
| [Axiom audit](Test/AxiomAudit.lean), at every build in CI | `sorry` and hidden assumptions | all 9,487 declarations use only `propext`, `Classical.choice`, `Quot.sound` |
| [Non-vacuity tests](Test/README.md) | hypotheses that can never hold together | 95 tests: headline theorems applied to a concrete object, including the echo-process theorems named under New results |
| [Known-answer tests](Test/README.md) | sign and parametrization slips in definitions | 159 tests against textbook values (Gumbel moments, Smith's Fisher information, extremal indices, …) |
| [Junk-value audit](Test/JUNK_VALUES.md) | statements true only because `x/0 = 0` or `log 0 = 0` | 3,718 theorems scanned by a script outside CI; one such statement found and fixed |
| [Mutation checks](Test/MUTATION.md) | statements proved "too easily" | 323 perturbed statements, by a script outside CI; none reveals a weakness |
| [Faithfulness audits](FAITHFULNESS.md) | statements that differ from the literature | six audits; every known deviation recorded |

What is still missing is review by human experts: the audits and tests were written with AI
assistance, so an independent reader is the remaining safeguard. [`docs/REVIEW.md`](docs/REVIEW.md) is
written for that reader, and corrections are very welcome.

## What is proved

| Area | Highlights | Lean names |
|---|---|---|
| Limits of maxima | Fisher–Tippett–Gnedenko; max-stable laws are exactly the extreme value laws | `CumulativeDistributionFunction.IsExtremeValueDistr.classification`, `isMaxStable_iff_isExtremeValueDistr` |
| Domains of attraction | Fréchet, Weibull and Gumbel characterizations; the quantile form | `isInMDAFrechet_iff`, `isInMDAWeibull_iff`, `isInMDAGumbel_iff`, `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile` |
| Peaks over threshold | Pickands–Balkema–de Haan, as an equivalence for every shape | `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` |
| Regular variation | Karamata (both halves), Potter bounds, representation theorem, Breiman's lemma | `IsRegularlyVarying.tendsto_integral_Ioi_div`, `tendsto_measure_mul_div_measure` |
| Stable laws | Generalized CLT for every `0 < α < 2` with textbook constants; domains of attraction; uniqueness of the index | `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt'`, `domainOfAttraction_isStableIndex_iff`, `IsStable.existsUnique_isStableIndex` |
| Heavy tails | Subexponential laws, random sums, Embrechts–Veraverbeke ruin asymptotics | `IsSubexponential.tendsto_tail_compound_div`, `tendsto_pkRuin_div_mul_tail` |
| Estimators | Hill (consistency, normality, dependent data), Pickands, moment, Weissman | `tendstoInMeasure_hill`, `tendstoInDistribution_hill`, `tendstoInMeasure_pickands`, `tendstoInDistribution_weissman` |
| Likelihood | GPD and GEV maximum likelihood: consistency, Fisher information, joint normality | `ae_tendsto_gpdMLE'`, `exists_gpdMLE_tendstoInDistribution`, `ae_tendsto_gevMLE` |
| Return levels | Asymptotic normality; Wald intervals with correct coverage; the delta method | `tendstoInDistribution_gpdReturnLevel`, `tendsto_measure_mem_gpdReturnLevelInterval`, `TendstoInDistribution.delta_method_gaussian` |
| Dependence | Leadbetter's theorem; extremal index; tail process; `θ = ϑ` under anticlustering and the block condition `A(uₙ)` on a common block sequence | `tendsto_measureReal_partialMax_le_exp`, `HasSpectralTailProcess.hasExtremalIndex_abs` |
| Clustering estimators | Blocks and runs estimators converge to their population ratio; that ratio equals the extremal index only under further hypotheses | `tendstoInMeasure_blocksEstimator`, `tendstoInMeasure_runsEstimator` |
| Time series | AR(1), ARMAX, linear processes, Markov chains; `X = AX + B` and GARCH(1,1) tails | `SRE.eq_stationaryLaw`, `SRE.GARCH.exists_tail_index` |
| Multivariate | Regular variation, converse Cramér–Wold, max-stable spectral representation, domains of attraction, the multivariate GPD | `isRegVarVector_iff`, `IsSimpleMaxStable.existsUnique_hasSpectralMeasure`, `isMDAWith_iff`, `IsMDAWith.tendsto_conditionalExcessCDF` |
| Processes | Poisson random measures; exceedances converge to a Poisson process; `D[0,1]` is Polish; tail empirical process ⇒ Brownian motion | `ProbabilityTheory.exists_isPoissonRandomMeasure`, `SkorokhodSpace.instPolishSpace`, `tendstoInDistribution_tailEmpiricalPath` |

Every result, with its source: [`THEOREMS.md`](THEOREMS.md). What is not proved yet: [`ROADMAP.md`](ROADMAP.md).

## New results

Formalizing the extremal index forced every hypothesis into the open. The results below were found
that way; their novelty has been checked against the literature
([`docs/NOVELTY.md`](docs/NOVELTY.md), [`docs/NOVELTY2.md`](docs/NOVELTY2.md)) but not yet by experts.

- **An answer to a question of Bai, Kulik and Wang (2024).** They asked whether some process
  satisfies the anticlustering condition only for block lengths up to `n^{ρ₀}` with `ρ₀ < 1`. The
  *power-lag echo process* (each large shock reappears once, after a delay that grows with its size)
  does so for every `ρ₀ ∈ (0,1)` (`powEchoProcess_antiClustering_iff`).
- **Mixing does not give `θ = ϑ`.** The same processes are β-mixing, yet their extremal index
  `θ = 1/2` differs from the value `ϑ = 1` read off the tail process
  (`logEchoProcess_betaMixing_incompatible`).
- **The echo process.** A simple stationary sequence with `θ < ϑ`, apparently only the second known
  mechanism after Bai and Wang's (`logEchoProcess_theta_lt_vartheta`), with a phase transition in the
  block length (`logEchoProcess_phase_transition`).
- **A warning for practitioners, proved.** On the echo process, the runs estimator with short runs
  converges to `ϑ`, not to the extremal index `θ` (`logEcho_tendstoInMeasure_runsEstimator`).
- **Which hypotheses are needed.** Counterexamples show that the hypotheses of Karamata's theorem,
  Breiman's lemma, the von Mises condition, the generalized CLT and Hill consistency cannot be dropped;
  some others can be weakened (`ExtremeValueTheory/Minimality/`).
- **Known results, proved under weaker hypotheses:** `θ ≤ ϑ` (Kulik–Soulier Lemma 7.5.4) and an exact
  formula for the gap `ϑ − θ`.

## Limitations

Many results are narrower than their textbook form, and each case is recorded here so that nobody has
to discover it. Rows and scope notes are in [`FAITHFULNESS.md`](FAITHFULNESS.md), and missing results
in [`ROADMAP.md`](ROADMAP.md).

**Nobody independent has reviewed this yet.** The statements, tests and audits were written with AI
assistance, and no human expert has checked them. The kernel guarantees the proofs, not that a
statement matches its textbook. The new results' novelty has not been confirmed by experts either.

**Maximum likelihood and return levels**
- GEV: consistency only on a compact parameter set `K ⊂ {ξ > −1, σ > 0}`, and only for an exact iid GEV
  sample. Fitting finite-block maxima from a law in a domain of attraction, or dependent block maxima, is
  not covered. Joint normality of the
  three-parameter estimator is not proved, so GEV and Gumbel return-level normality
  (`tendstoInDistribution_gevReturnLevel`) assume parameter normality as a hypothesis.
- GPD: also on a compact set, with the true parameter in its interior. Joint normality needs
  `ξ₀ > −1/2` and `ξ₀ ≠ 0`.
- `ξ = 0`: the likelihood is only partly covered. With the shape known to be `0`, the scale estimator is
  normal (`tendstoInDistribution_sampleMean_gpd_zero`). Joint estimation when the true shape is `0` is not
  proved.
- Peaks-over-threshold return levels treat the excesses as an exact iid GPD sample with a known exceedance
  probability `ζ`. The number of exceedances is not random, and neither the error of the GPD
  approximation above a finite threshold nor the estimation of `ζ` is accounted for.
- Not proved: profile-likelihood intervals, and likelihood over the whole parameter space.

**Tail estimators**
- Normality of the Pickands and moment estimators is not proved. Hill intervals are only without bias
  (`λ = 0`), and there are no bias-reduced estimators.
- The basic far-tail Weissman theorems assume the rate and the bias condition; second-order versions
  derive them, for `ρ < 0`, and with extra regularity at `ρ = 0`.
- The blocks and runs estimators (`tendstoInMeasure_blocksEstimator`, `tendstoInMeasure_runsEstimator`)
  assume that the population block or run ratio converges to `θ`. They do not prove that this limit is the
  extremal index, and on the echo process it is not (`logEcho_tendstoInMeasure_runsEstimator`).
- The intervals estimator (`tendstoInMeasure_intervalsEstimator₁`) assumes the two empirical-moment limits.
  Deriving them from a sequence's actual inter-exceedance times (Ferro–Segers Theorem 1) is not proved.
- The non-vacuity tests of the dependent-data Hill theorem and of the intervals estimator use iid data.
  Hill does have a dependent application in the library (`MovingAverage.tendstoInMeasure_hill`).
- These are asymptotic statements. The library says nothing about finite samples or how to choose a
  threshold, a block length or `k`.

**Heavy tails and stable laws**
- The ruin probability `pkRuin` is *defined* by the Pollaczek–Khinchine formula. It is not derived from
  the Cramér–Lundberg process.
- `X = AX + B` and GARCH(1,1): the tail is bounded by `O(x^{−s})` for `s < κ` and shown not to be for
  `s > κ`. The sharp Kesten–Goldie asymptotics `c x^{−κ}` is not proved.
- The parametric stable family `S(α, β, σ, μ)` and the tails of stable laws are not developed.

**Dependence**
- `θ = ϑ` needs anticlustering and the block condition `A(uₙ)` on a common block sequence, and this is
  essential: the echo processes are β-mixing and have `θ < ϑ`.
- The moving-maximum, moving-average and echo theorems assume noise that is nonnegative for every `ω`, not
  almost surely, which is formally stronger than the textbook. The tails of linear processes do not
  (`tendsto_measureReal_tsum_mul_div_of_summable_rpow` allows signed noise and coefficients).
- Infinite moving averages need `Σ|ψ|^δ < ∞` for some `δ < min(α, 1)`, which for `α > 1` is slightly
  stronger than the optimal `Σ|ψ| < ∞`.
- ARMAX needs exact Pareto innovations.

**Multivariate extremes and processes**
- The multivariate GPD limit `IsMDAWith.tendsto_conditionalExcessCDF` needs `G(x ∧ 0) > 0`, which fails
  for unit-Fréchet-standardized limits; use `IsMDAWith.tendsto_conditionalExcess_tailQuantile` for those.
- The multivariate domain-of-attraction equivalence assumes continuous margins.
- The Pickands dependence estimator assumes known unit Fréchet margins. Nonparametric tail-dependence
  estimation is not finished.
- Point-process convergence is stated through joint laws of counts on finite families of disjoint sets,
  with no topology on the space of measures.
- The functional limit of the tail empirical process is for uniform observations in unweighted `D[0,1]`;
  only weighted near-zero bounds are proved beyond it. Cluster point processes and Brown–Resnick, Schlather
  and extremal-t processes are not formalized.

**Classical theory**
- Karamata's direct half has versions for measurable `F` and for `F` antitone on `[a, ∞)`, but
  its converse `IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi` assumes `F` antitone on all of `ℝ`.

## Status and what's next

The theory taught in the standard textbooks is essentially complete. The library is on Mathlib
v4.35.0, the latest stable release, and a weekly CI job tries newer Mathlib versions. The first release
is `v0.9.0`; it is usable and citable, but has had no expert review. What is left for version 1.0, in
order (details and progress in [`ROADMAP.md`](ROADMAP.md)):

1. **The statistics practitioners use most:** three-parameter GEV maximum likelihood normality,
   profile-likelihood intervals, Pickands estimator normality, nonparametric tail-dependence estimation
   (in progress).
2. **A consistent design.** Done: names and namespaces, one representation of laws, split files,
   conventions in [`docs/DESIGN.md`](docs/DESIGN.md). Left: one definition per concept (in progress),
   splitting the statistics files, a changelog and a tagged release.
3. **Documentation that matches the code**, with specification tests and a faithfulness audit of the
   newest results.
4. **Usability:** a tutorial and worked examples for the standard distributions.
5. **Review by human experts**, the one check independent of the AI that helped write the statements,
   then **a paper** on the new results and an announcement on the Lean Zulip.

After 1.0: the remaining textbook gaps (the parametric stable family, cluster point processes,
Brown–Resnick processes), open problems ([`docs/PRACTICAL_OPEN_PROBLEMS.md`](docs/PRACTICAL_OPEN_PROBLEMS.md),
[`docs/OPEN_PROBLEMS_SURVEY2.md`](docs/OPEN_PROBLEMS_SURVEY2.md)), upstreaming the general results to
Mathlib, and executable estimators cross-checked against R and Python.

## Build

```sh
lake exe cache get
lake build          # the library
lake build Test     # the specification tests
```

With Nix, `nix develop` gives a shell with `elan` and the other tools used by the scripts and CI.

## Use it in your project

Create a Lean project with the same [`lean-toolchain`](lean-toolchain), and add to its `lakefile.toml`:

```toml
[[require]]
name = "lean-extremevaluetheory"
git = "https://github.com/unbalancedparentheses/lean-extremevaluetheory"
rev = "v0.9.0"
```

Then fetch it and build:

```sh
lake update
lake exe cache get   # prebuilt Mathlib; the library itself compiles from source the first time
lake build
```

and write `import ExtremeValueTheory`. Each tag fixes Lean and Mathlib together.
[`Downstream/Readme.lean`](Downstream/Readme.lean) is such a client, and a weekly
[workflow](.github/workflows/downstream.yml) builds it in a fresh project that requires this repository.

## Layout

| Directory | Contents |
|---|---|
| top level, `GEV/` | distribution functions, types, Fisher–Tippett–Gnedenko, max-stability, the GEV family |
| `RegularVariation/` | slow, regular, extended and second-order variation; Karamata; Breiman; multivariate |
| `DomainOfAttraction/`, `PeaksOverThreshold/` | the three domains, von Mises conditions, Pickands–Balkema–de Haan |
| `StableLaws/`, `HeavyTails/` | stable laws, the generalized CLT; subexponential laws, random sums, ruin |
| `Statistics/` | order statistics, estimators, likelihood, return levels, confidence intervals, extremal-index estimators |
| `Dependence/` | extremal index, tail process, mixing, Markov chains, linear processes, `X = AX + B`, GARCH, the echo processes |
| `Multivariate/`, `MaxStable/` | multivariate regular variation and domains of attraction, the multivariate GPD, max-stable vectors and processes |
| `PointProcess/` | exceedance point processes |
| `Minimality/` | counterexamples showing which hypotheses are needed |
| `ForMathlib/` | general results written for Mathlib (vague convergence, Poisson random measures, mixing, Skorokhod space, delta method, …); see [`UPSTREAMING.md`](ExtremeValueTheory/ForMathlib/UPSTREAMING.md) |
| `Test/` | specification tests: non-vacuity, known answers, junk values, mutation checks |

## Contributing

The most useful contribution is a correction: if a formal statement does not say what its textbook
counterpart says, please open an issue. Open problems with precise targets are listed in
[`ROADMAP.md`](ROADMAP.md) and [`RESEARCH.md`](RESEARCH.md).

## Citing

See [`CITATION.cff`](CITATION.cff), or use GitHub's "Cite this repository" button. The DOI
[10.5281/zenodo.23966372](https://doi.org/10.5281/zenodo.23966372) always points to the latest release; [10.5281/zenodo.23966373](https://doi.org/10.5281/zenodo.23966373) is `v0.9.0`.

## Credits

The Fisher–Tippett–Gnedenko development and its blueprint are based on
[ExtremeValueProject](https://github.com/kkytola/ExtremeValueProject) by Kalle Kytölä and the
participants of the Aalto University course MS-EV0029 *Introduction to Formalized Mathematics
in Lean*. Several of its statements were false as written and have been corrected; see
[`TRIAGE.md`](TRIAGE.md). Derived files keep their original copyright headers; see [`NOTICE`](NOTICE).

Independently, Michikazu Hirata has formalized
[Fisher–Tippett–Gnedenko and Pickands–Balkema–de Haan](https://isa-afp.org/entries/Extreme_Value_Theory.html)
and [regular variation](https://isa-afp.org/entries/Regular_Variation.html) in Isabelle, in the Archive of
Formal Proofs.

## License

Apache 2.0, see [`LICENSE`](LICENSE).
