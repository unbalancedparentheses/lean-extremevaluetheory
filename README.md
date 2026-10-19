# Extreme Value Theory in Lean

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
  Skorokhod space. About 94,000 lines and 3,900 theorems, with no `sorry`.
- **Checked twice.** Lean's kernel checks every proof, and CI re-checks all 718,274 declarations
  with an independent checker.
- **Tested against the textbooks.** Proving a theorem is not enough: it has to *state* the right
  thing. About 250 specification tests and six audits check that it does.
- **New mathematics.** Formalizing forced every hypothesis into the open, and that led to new
  results, including an answer to an open question of Bai, Kulik and Wang (2024).

[Website](https://unbalancedparentheses.github.io/lean-extremevaluetheory/) ·
[Blueprint](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/) ·
[API documentation](https://unbalancedparentheses.github.io/lean-extremevaluetheory/docs/) ·
[Roadmap](ROADMAP.md)

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
    (∃ A, A • G = standardGumbelCDF) ∨
      (∃ A ξ, ∃ (hξ : 0 < ξ), A • G = standardFrechetCDF hξ) ∨
      (∃ A ξ, ∃ (hξ : 0 < ξ), A • G = standardWeibullCDF hξ)
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
| [`con-leche`](.github/workflows/kernel-check.yml), an independent kernel with a machine-checked proof that it never accepts `False` | a bug in Lean's kernel | all 718,274 declarations accepted |
| `#print axioms` | hidden assumptions | only `propext`, `Classical.choice`, `Quot.sound` |
| [Non-vacuity tests](Test/README.md) | hypotheses that can never hold together | 92 tests: every headline theorem applied to a concrete object |
| [Known-answer tests](Test/README.md) | sign and parametrization slips in definitions | 158 tests against textbook values (Gumbel moments, Smith's Fisher information, extremal indices, …) |
| [Junk-value audit](Test/JUNK_VALUES.md) | statements true only because `x/0 = 0` or `log 0 = 0` | 3,718 theorems scanned; one such statement found and fixed |
| [Mutation checks](Test/MUTATION.md) | statements proved "too easily" | 323 perturbed statements; none reveals a weakness |
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
| Dependence | Leadbetter's theorem; extremal index; tail process; `θ = ϑ` under anticlustering | `tendsto_measureReal_partialMax_le_exp`, `HasSpectralTailProcess.hasExtremalIndex_abs` |
| Clustering estimators | Blocks and runs estimators of the extremal index are consistent | `tendstoInMeasure_blocksEstimator`, `tendstoInMeasure_runsEstimator` |
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

## Build

```sh
lake exe cache get
lake build          # the library
lake build Test     # the specification tests
```

With Nix, `nix develop` gives a shell with `elan` and the other tools used by the scripts and CI.

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

See [`CITATION.cff`](CITATION.cff), or use GitHub's "Cite this repository" button.

## Credits

The Fisher–Tippett–Gnedenko development and its blueprint are based on
[ExtremeValueProject](https://github.com/kkytola/ExtremeValueProject) by Kalle Kytölä and the
participants of the Aalto University course MS-EV0029 *Introduction to Formalized Mathematics
in Lean*. Several of its statements were false as written and have been corrected; see
[`TRIAGE.md`](TRIAGE.md). Derived files keep their original copyright headers; see [`NOTICE`](NOTICE).

## License

Apache 2.0, see [`LICENSE`](LICENSE).
