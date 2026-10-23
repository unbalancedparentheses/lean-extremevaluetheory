# Design

## Tests and library API

`Test/` checks the *statements* of the library (non-vacuity, known answers, junk values; see
`Test/README.md`). It is not a place to prove mathematics the library lacks.

### What belongs where

A lemma goes in the **library** if it is a general fact a reader of a textbook would expect to
find stated, or an evaluation lemma that any user of a definition needs. Examples promoted from
the tests:

| Fact | Library name | File |
|---|---|---|
| index of regular variation is unique | `IsRegularlyVarying.index_eq` (already existed) | `StableLaws/GaussianDomain.lean` |
| symmetric `α`-stable laws have index `α` | `IsSymmStable.isStableIndex`, `IsSymmStable.stableIndex_eq` | `StableLaws/StableIndex.lean` |
| Weibull, `τ ≥ 1` (incl. the exponential law), is not subexponential | `not_isSubexponential_weibullTailLaw` | `HeavyTails/Examples.lean` |
| `δₓ^{*n} = δ_{nx}` | `Subexp.convPow_dirac` | `HeavyTails/Subexponential.lean` |
| tail balance of the symmetrized Pareto law | `SymmPareto.measureReal_Ioi`, `SymmPareto.tendsto_measureReal_Ioi_div_absTail` | `StableLaws/DomainOfAttraction.lean` |
| `U(t) = t + c` is second-order RV (`γ = 1`, `ρ = -1`) | `isSecondOrderRegularlyVarying_add_const` | `RegularVariation/SecondOrder.lean` |
| iid ⇒ `0`-dependent, `α(h) = β(h) = 0` for `h ≥ 1` | `iIndepFun.isMDependent_zero`, `iIndepFun.alphaMixing_eq_zero`, `iIndepFun.betaMixing_eq_zero` | `ForMathlib/Probability/Process/Mixing.lean` |
| the three cases of `IsInMDAGEV ξ` and textbook members | `isInMDAGEV_iff_of_pos/_of_neg`, `isInMDAGEV_zero_iff`, `isInMDAGEV_paretoCDF`, `isInMDAGEV_powerCDF`, `isInMDAGEV_standardExponentialCDF` | `DomainOfAttraction/GEVDomain.lean` |
| CDF evaluation | `paretoCDF_apply_of_le_one`, `one_sub_paretoCDF_of_one_le`, `powerCDF_apply_of_nonpos`, `powerCDF_apply_of_one_le`, `standardGumbelCDF_pos`, `standardGumbelCDF_lt_one` | `DomainOfAttraction/VonMises.lean`, `ExtremeValueDistribution.lean` |
| block / run probabilities of an iid sequence | `measureReal_blockEvent_of_iIndepFun`, `measureReal_runEvent_of_iIndepFun` | `Statistics/ExtremalIndexEstimatorsIid.lean` |
| Ferro–Segers law: moments integrable, `θ = 1` is `Exp(1)` | `integrable_pow_ferroSegersLaw`, `ferroSegersLaw_one` | `Statistics/FerroSegersLaw.lean` |
| order statistics of a sorted sample | `orderStat_of_monotone`, `orderStat_eq_of_monotone_comp` | `Statistics/OrderStatisticsSorted.lean` |

Before adding a test helper, search the library and Mathlib (e.g. `HasLaw.measure_eq`,
`HasLaw.identDistrib`, `ProbabilityTheory.exists_iid`, `ExtremeValueTheory.tendsto_sqrt_atTop`,
`ExtremeValueTheory.tendsto_sqrt_div`); if a test has to work around a missing evaluation,
measurability or `simp` lemma, add that lemma to the library instead.

A lemma stays in **`Test/`** only if it is about a concrete object built for one test (a specific
sample, compact parameter set, sequence `kₙ = ⌊√n⌋`, product space, innovation law, …) or is
packaging for one file (e.g. `exists_iid` plus the identical-distribution facts).

### Test conventions

* Tests are `theorem test_…` or `example`, each with a docstring citing the textbook value or the
  headline theorem it exercises.
* Every other declaration in `Test/` is `private` and has a docstring saying what it is for
  (test-specific helpers are not part of the API and must not be imported elsewhere).
* Tests use only public library statements, never internals, and no `sorry`.
* A known-answer test may be a one-line application of a library lemma: the check is that the
  lemma's *statement* has the textbook value.
* `lake build Test` runs in CI; checkdecls loads every library, so the `Test` library must build.
