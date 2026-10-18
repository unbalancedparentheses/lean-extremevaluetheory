# Extreme Value Theory in Lean

[![Build](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/build.yml/badge.svg)](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/build.yml)
[![Blueprint](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/blueprint.yml/badge.svg)](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/)

A machine-checked library of extreme value theory and heavy-tailed probability, written in Lean 4
on top of Mathlib. It covers the classical theory of maxima and tails, the statistics of extremes,
stable laws, extremes of dependent sequences, multivariate extremes, point processes and the
Skorokhod space, and it contains new results on the extremal index.

- **About 80,000 lines, no `sorry`.** Every main theorem depends only on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`).
- **Statements are audited.** Six independent faithfulness audits compared each formal statement
  with its textbook source; the results, including every known deviation, are in
  [`FAITHFULNESS.md`](FAITHFULNESS.md).
- **Documented.** A [blueprint](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/)
  explains each result and links it to the Lean code, and the
  [API documentation](https://unbalancedparentheses.github.io/lean-extremevaluetheory/docs/) lists
  every declaration.

## What a theorem looks like

Fisher–Tippett–Gnedenko, as stated in the library:

```lean
theorem CumulativeDistributionFunction.IsExtremeValueDistr.classification
    {G : CumulativeDistributionFunction} (hG : G.IsExtremeValueDistr) :
    (∃ A, A • G = standardGumbelCDF) ∨
      (∃ A ξ, ∃ (hξ : 0 < ξ), A • G = standardFrechetCDF hξ) ∨
      (∃ A ξ, ∃ (hξ : 0 < ξ), A • G = standardWeibullCDF hξ)
```

`G.IsExtremeValueDistr` says that `G` is non-degenerate and is the limit of `F(aₙx + bₙ)ⁿ` for some
distribution function `F` and affine normalizations; `A • G` is `G` after an increasing affine change
of variables. So every limit law of normalized maxima is, up to type, Gumbel, Fréchet or Weibull.

## Headline theorems

| Area | Theorem | Lean name |
|---|---|---|
| Limits of maxima | Fisher–Tippett–Gnedenko: the only non-degenerate limits of normalized maxima are Gumbel, Fréchet and Weibull | `CumulativeDistributionFunction.IsExtremeValueDistr.classification` |
| | Max-stable laws are exactly the extreme value laws | `isMaxStable_iff_isExtremeValueDistr` |
| Domains of attraction | Fréchet ⇔ regularly varying tail | `isInMDAFrechet_iff` |
| | Weibull ⇔ finite endpoint with regularly varying tail | `isInMDAWeibull_iff` |
| | Gumbel ⇔ auxiliary function (de Haan) | `isInMDAGumbel_iff` |
| | Quantile form: `MDA(H_γ)` ⇔ `U` extended regularly varying | `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile` |
| Peaks over threshold | Pickands–Balkema–de Haan, as an equivalence for every shape | `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` |
| Regular variation | Karamata (both halves), Potter bounds, representation theorem, Breiman's lemma | `IsRegularlyVarying.tendsto_integral_Ioi_div`, `tendsto_measure_mul_div_measure` |
| Stable laws | Generalized CLT for every `0 < α < 2`, with textbook constants | `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt'` |
| | Domain of attraction of an `α`-stable law ⇔ regularly varying tail + tail balance | `domainOfAttraction_isStableIndex_iff` |
| | Every stable law has a unique index (Feller VI.1); normal domain of attraction | `IsStable.existsUnique_isStableIndex`, `domainOfAttraction_gaussianReal_iff` |
| Heavy tails | Subexponential laws, random sums, Embrechts–Veraverbeke ruin asymptotics | `IsSubexponential.tendsto_tail_compound_div`, `tendsto_pkRuin_div_mul_tail` |
| Statistics | Hill estimator: consistency, asymptotic normality, dependent data | `tendstoInMeasure_hill`, `tendstoInDistribution_hill`, `tendstoInMeasure_hill_of_alphaMixing_rate` |
| | Pickands and moment estimators, Weissman extreme quantiles | `tendstoInMeasure_pickands`, `tendstoInMeasure_momentEstimator_of_isInMDAGEV'`, `tendstoInDistribution_weissman` |
| | GPD/GEV maximum likelihood: consistency, Fisher information, joint normality | `ae_tendsto_gpdMLE'`, `exists_gpdMLE_tendstoInDistribution`, `ae_tendsto_gevMLE` |
| Dependence | Leadbetter's theorem and the extremal index | `tendsto_measureReal_partialMax_le_exp`, `HasExtremalIndex` |
| | Tail process, time-change formula, `θ = ϑ` under anticlustering | `HasSpectralTailProcess.lintegral_timeChange`, `HasSpectralTailProcess.hasExtremalIndex_abs` |
| Multivariate | Regular variation, polar decomposition, converse Cramér–Wold (non-integer `α`) | `isRegVarVector_iff`, `CramerWold.isRegVarVector_of_tendsto_linear` |
| | Max-stable spectral representation, existence and uniqueness | `IsSimpleMaxStable.existsUnique_hasSpectralMeasure` |
| Processes | Poisson random measures; exceedances converge to a Poisson process | `ProbabilityTheory.exists_isPoissonRandomMeasure`, `tendsto_measureReal_sumDiracRange_timeSpace_eq` |
| | Skorokhod space `D[0,1]` is Polish; tail empirical process ⇒ Brownian motion | `SkorokhodSpace.instPolishSpace`, `tendstoInDistribution_tailEmpiricalPath` |

The full list is in [`THEOREMS.md`](THEOREMS.md).

## Research results

Formalizing the extremal index forced every hypothesis into the open. A literature check (see
[`RESEARCH.md`](RESEARCH.md)) classifies the results as follows:

- **The echo process (likely new).** An explicit stationary, regularly varying sequence whose tail
  process is that of an iid sequence (`ϑ = 1`, so the tail process sees no clustering) but whose
  extremal index is `θ = 1/2` (`logEchoProcess_theta_lt_vartheta`). Each large shock reappears once,
  after a lag that grows with its size. The cluster ratio has a block-length phase transition at
  `rₙ ≍ log n` (`logEchoProcess_phase_transition`). It appears to be only the second known mechanism
  with `θ < ϑ`, and far simpler than the first (Bai and Wang).
- **An exact gap formula (partly known).** `θ = ϑ − η`, where `η` is the mass of cluster returns at
  lags that grow with the threshold (`HasSpectralTailProcess.lt_candidateExtremalIndex_iff`). The
  underlying identity is close to classical results of O'Brien and Segers; the two-sided statement is
  formalized here.
- **`θ ≤ ϑ` (known, Kulik–Soulier Lemma 7.5.4)**, proved here assuming only stationarity and a
  spectral tail process (`HasSpectralTailProcess.le_candidateExtremalIndex'`).

## Layout

| Directory | Contents |
|---|---|
| top level, `GEV/` | distribution functions, types, Fisher–Tippett–Gnedenko, max-stability, the GEV family |
| `RegularVariation/` | slow, regular, extended and second-order variation; Karamata; Breiman; multivariate |
| `DomainOfAttraction/`, `PeaksOverThreshold/` | the three domains, von Mises conditions, Pickands–Balkema–de Haan |
| `StableLaws/` | stable laws, the generalized CLT and its converse |
| `HeavyTails/` | subexponential laws, random sums, ruin, linear processes |
| `Statistics/` | order statistics, records, Hill, Pickands, moment, Weissman, block maxima, likelihood |
| `Dependence/` | stationary sequences, extremal index, tail process, mixing, Markov chains, the echo process |
| `Multivariate/`, `MaxStable/` | dependence functions, tail dependence, max-stable vectors and processes |
| `PointProcess/` | exceedance point processes |
| `ForMathlib/` | general results (vague convergence, Poisson random measures, mixing, Skorokhod space, …) written for upstreaming to Mathlib; see [`UPSTREAMING.md`](ExtremeValueTheory/ForMathlib/UPSTREAMING.md) |

## Build

```sh
lake exe cache get
lake build
```

## Guides

- [`docs/PRACTITIONERS.md`](docs/PRACTITIONERS.md): for users of the R and Python packages (`evd`,
  `ismev`, `extRemes`, `POT`, `ReIns`, `pyextremes`, `scipy.stats`, …). Which estimator each function
  computes, which theorem guarantees it, under which assumptions, and what is not covered, with a
  cheat-sheet of sign and parametrization conventions.
- [`docs/REVIEW.md`](docs/REVIEW.md): a guide for extreme value theorists reviewing whether the formal
  statements say what the textbook theorems say, written for readers who do not use Lean.
- [`FAITHFULNESS.md`](FAITHFULNESS.md): statement-by-statement comparison with the literature and the
  results of six audits.
- [`THEOREMS.md`](THEOREMS.md): the full catalogue of results.

## Contributing

Corrections to statements are especially welcome: if a formal statement does not say what its
textbook counterpart says, please open an issue. Open problems with precise formal targets are
listed in [`RESEARCH.md`](RESEARCH.md).

## Credits

The Fisher–Tippett–Gnedenko development and its blueprint are based on
[ExtremeValueProject](https://github.com/kkytola/ExtremeValueProject) by Kalle Kytölä and the
participants of the Aalto University course MS-EV0029 *Introduction to Formalized Mathematics
in Lean*. Several of its statements were false as written and have been corrected; see
[`TRIAGE.md`](TRIAGE.md). Derived files keep their original copyright headers; see [`NOTICE`](NOTICE).

## License

Apache 2.0, see [`LICENSE`](LICENSE).
