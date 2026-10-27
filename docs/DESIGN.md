# Design

Conventions of the `ExtremeValueTheory` library. They apply to new code and to every rename; when
existing code disagrees, the code is wrong and is fixed with a deprecated alias (see
[Deprecation](#deprecation)).

## Naming

We follow the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
(`lowerCamelCase` for terms and theorems, `UpperCamelCase` for types and `Prop`-valued
structures, theorem names describe the statement). Library-specific rules:

* **Predicates** are `Is…` structures or definitions: `IsRegularlyVarying f ρ`,
  `IsSecondOrderRegularlyVarying U γ ρ A`, `IsSubexponential μ`, `IsMDependent X m P`,
  `IsStationary X P`, `IsMaxStable G`, `IsExtremeValueDistr G`. Facts about them use dot
  notation in the predicate's namespace: `IsRegularlyVarying.index_eq`,
  `IsSymmStable.isStableIndex`, `iIndepFun.isMDependent_zero`.
* **Domains of attraction** are `IsInMDAFrechet hα`, `IsInMDAWeibull hα`, `IsInMDAGumbel` on a
  `CumulativeDistributionFunction`, and the unified `IsInMDAGEV ξ` with the de Haan–Ferreira sign
  convention: `ξ > 0` is the Fréchet side with index `1/ξ`, `ξ < 0` the Weibull side with index
  `-1/ξ`, `ξ = 0` the Gumbel domain (`isInMDAGEV_iff_of_pos`, `isInMDAGEV_iff_of_neg`,
  `isInMDAGEV_zero_iff` in `DomainOfAttraction/GEVDomain.lean`). Membership of a named law is
  `isInMDA…_<law>`, e.g. `isInMDAGEV_paretoCDF`.
* **Named laws.** A c.d.f. is `<name>CDF` (`standardGumbelCDF`, `standardFrechetCDF hα`,
  `paretoCDF hα`, `powerCDF hα`, `standardExponentialCDF`); a measure is `<name>Measure` or
  Mathlib's name (`paretoMeasure t r`, `expMeasure 1`, `gpdMeasure ξ σ`); a survival function is
  `<name>Survival…`. Evaluation lemmas are `<f>_apply_of_<hypothesis>` (`paretoCDF_apply_of_one_le`,
  `powerCDF_apply_of_nonpos`), tail evaluations `tail_<law>` or `<law>_Ioi`, and the bridge from
  a c.d.f. to its measure `<f>_apply_eq_measureReal_Iic`.
* **Hypotheses in names** state the hypothesis that is actually used. `_of_summable_rpow`, not
  `_of_lt_one`, when the hypothesis is the summability of `|c_j|^δ` (the old name suggested
  `α < 1`).
* **No primes or vague suffixes for genuinely different objects.** `gpdSurvivalNonneg` (correct
  only for `ξ ≥ 0`) and `gpdSurvivalAll` (all `ξ`) replaced `gpdSurvival` and `gpdSurvival'`. A
  prime is acceptable only for a local variant of a lemma with the same statement shape, as in
  Mathlib.
* **Terminology that clashes with the literature is renamed.** The quantity once called the
  "escape mass" (`HasEscapeMass`, `escapeSet`, `clusterEscape`) is the *late-return mass*
  (`HasLateReturnMass`, …), since Abadi–Freitas–Freitas use "escape" for something else.
* **Theorem headlines.** A theorem that is the formal counterpart of a textbook result says so
  in bold at the start of its docstring (`**Gnedenko's theorem (Fréchet) for laws**`) and cites
  the source (`[EKM, Theorem 3.3.7]`, `[dHF, Theorem 1.1.3]`).
* Asymptotic hypotheses on sample fractions are named after what they say: `hk : Tendsto k atTop
  atTop`, `hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)`. The standard witness
  `k n = ⌊√n⌋` has its own API (`tendsto_sqrt_atTop`, `tendsto_sqrt_div`,
  `tendsto_natCast_sqrt_atTop`, `tendsto_log_div_natSqrt`) in `Dependence/MDependent.lean`.

## Namespaces

* Everything is in `ExtremeValueTheory` unless one of the rules below applies.
* The c.d.f. API (`IsInMDA…`, affine action, types, `paretoCDF`, `ofMeasure`, …) is in
  `CumulativeDistributionFunction`, so it is available by dot notation on `F`.
* Dot-notation namespaces of predicates and structures: `IsRegularlyVarying`,
  `IsSubexponential`, `IsSimpleMaxStable`, `InfiniteMovingAverage`, `LinearProcess`, `SRE`, ….
* `ForMathlib/` uses Mathlib's namespaces (`ProbabilityTheory`, `MeasureTheory`, …) so that its
  declarations can be upstreamed unchanged; see `ForMathlib/UPSTREAMING.md`.
* Results about the *sharpness* of hypotheses (counterexamples showing a hypothesis cannot be
  dropped) live in `ExtremeValueTheory.Minimality`, in the `Minimality/` folder.
* Short-lived proof namespaces of one file (`GCLT`, `GCLTConverse`, `Subexp`, `SymmPareto`) are
  allowed for helpers that are not meant to be used by name elsewhere; a lemma from such a
  namespace that other files need is moved to the main namespace.
* `Test/` declarations live in `Test.<Folder>.<File>` and are `private` (see below).

## One representation of laws

A probability law on `ℝ` appears in three forms; `ExtremeValueTheory/CDFBridge.lean` is the
single bridge between them, and no other file proves conversions.

1. **`μ : Measure ℝ` with `[IsProbabilityMeasure μ]`** is the canonical *law*, as in Mathlib.
   Random variables carry their law as `HasLaw X μ P` (Mathlib). `ProbabilityMeasure ℝ` is used
   only where the topology of convergence in distribution is needed.
2. **Mathlib's `ProbabilityTheory.cdf μ : StieltjesFunction ℝ`** is the distribution function of
   a law.
3. **`CumulativeDistributionFunction`** (a Stieltjes function with limits `0` and `1`) is the
   canonical object of the classical theory of maxima: affine action `A • F`, types,
   Fisher–Tippett–Gnedenko, max-stability, domains of attraction, peaks over threshold.

Conversions: `F.measure` (law of `F`), `ofMeasure μ` (c.d.f. of `μ`, literally `cdf μ`),
`equivMeasure`, `hasLaw_measure_iff` (`HasLaw X F.measure P ↔ ∀ x, F x = P.real {ω | X ω ≤ x}`).
`lawOfCDF` is deprecated in favour of `F.measure`. Domains of attraction of laws and random
variables are in `DomainOfAttraction/OfMeasure.lean`.

Further conventions:

* Probabilities of events are written `P.real s` (Mathlib's `measureReal`), not
  `(P s).toReal`; the two are definitionally equal. Tails are `tail μ x = μ.real (Ioi x)`.
* Statistical theorems take samples as `X : ℕ → Ω → ℝ` with `(∀ i, Measurable (X i))`,
  `iIndepFun X P` and `(∀ i, IdentDistrib (X i) (X 0) P P)`; the marginal is given either by
  `HasLaw (X 0) μ P` or by `hF : ∀ x, F x = P.real {ω | X 0 ω ≤ x}`.
* A concrete law gets a bridge lemma once, next to its definition (e.g.
  `paretoCDF_apply_eq_measureReal_Iic` relates `paretoCDF hα` and `paretoMeasure 1 α`), so users
  never redo the computation.

## Where things go

| Content | Location |
|---|---|
| general measure theory / probability with only Mathlib imports | `ForMathlib/` (module system, upstreamable) |
| c.d.f.s, affine action, types, the law bridge | top-level files (`CumulativeDistributionFunction.lean`, `CDFBridge.lean`, `TypeOfCDF.lean`, …) |
| GEV, max-stability | `GEV/`, `MaxStable/`, `ExtremeValueDistribution.lean` |
| regular variation (univariate, second order, multivariate) | `RegularVariation/` |
| domains of attraction and named examples | `DomainOfAttraction/` (examples next to the criterion they illustrate: `paretoCDF` in `VonMises.lean`) |
| peaks over threshold, GPD | `PeaksOverThreshold/` |
| heavy tails, subexponentiality, ruin | `HeavyTails/` (named laws in `Examples.lean`) |
| stable laws and generalized CLT | `StableLaws/` |
| stationary sequences, extremal index, tail process | `Dependence/` |
| point processes | `PointProcess/` |
| estimators and their asymptotics | `Statistics/` |
| sharpness of hypotheses | `Minimality/` |
| checks of the statements | `Test/` |

* A lemma goes where a user would look for it: next to the definition it evaluates, or next to
  the theorem it feeds. Evaluation, measurability and `simp` lemmas for a definition live in the
  definition's file.
* Files over ~1000 lines are split into parts in a folder of the same name; the original file
  stays as an umbrella importing its parts, so `import` lines do not change.
* Every new file is imported from `ExtremeValueTheory.lean`.
* Every public declaration has a docstring; every file has a module docstring with *Main
  results* and *References*. No `sorry`, no new axioms.

## Deprecation

* A public name is never deleted or changed silently. Renames and moves leave
  `@[deprecated (since := "YYYY-MM-DD")] alias oldName := newName` in the file that now holds
  the declaration (for example `hasEscapeMass_echoProcess`, `lawOfCDF`).
* A changed *statement* gets a new name; the old statement stays, deprecated, if it is still true.
* Deprecated aliases are kept for at least six months and across at least one Mathlib bump, then
  removed in a dedicated commit that lists them.
* Blueprint references, `THEOREMS.md`, `FAITHFULNESS.md` and `ROADMAP.md` are updated in the
  same change as the rename.

## Tests and library API

`Test/` checks the *statements* of the library (non-vacuity, known answers, junk values; see
`Test/README.md`). It is not a place to prove mathematics the library lacks.

### What belongs where

A lemma goes in the **library** if it is a general fact a reader of a textbook would expect to
find stated, or an evaluation lemma that any user of a definition needs. Examples promoted from
the tests:

| Fact | Library name | File |
|---|---|---|
| index of regular variation is unique | `IsRegularlyVarying.index_eq` | `StableLaws/GaussianDomain/Necessity.lean` |
| symmetric `α`-stable laws have index `α` | `IsSymmStable.isStableIndex`, `IsSymmStable.stableIndex_eq` | `StableLaws/StableIndex.lean` |
| Weibull, `τ ≥ 1` (incl. the exponential law), is not subexponential | `not_isSubexponential_weibullTailLaw` | `HeavyTails/Examples.lean` |
| `δₓ^{*n} = δ_{nx}` | `Subexp.convPow_dirac` | `HeavyTails/Subexponential.lean` |
| tail balance of the symmetrized Pareto law | `SymmPareto.measureReal_Ioi`, `SymmPareto.tendsto_measureReal_Ioi_div_absTail` | `StableLaws/DomainOfAttraction.lean` |
| `U(t) = t + c` is second-order RV (`γ = 1`, `ρ = -1`) | `isSecondOrderRegularlyVarying_add_const` | `RegularVariation/SecondOrder.lean` |
| iid ⇒ `0`-dependent, `α(h) = β(h) = 0` for `h ≥ 1` | `iIndepFun.isMDependent_zero`, `iIndepFun.alphaMixing_eq_zero`, `iIndepFun.betaMixing_eq_zero` | `ForMathlib/Probability/Process/Mixing.lean` |
| the three cases of `IsInMDAGEV ξ` and textbook members | `isInMDAGEV_iff_of_pos/_of_neg`, `isInMDAGEV_zero_iff`, `IsInMDA{Frechet,Weibull,Gumbel}.isInMDAGEV`, `isInMDAGEV_paretoCDF`, `isInMDAGEV_powerCDF`, `isInMDAGEV_standardExponentialCDF` | `DomainOfAttraction/GEVDomain.lean` |
| c.d.f. evaluation | `paretoCDF_apply_of_le_one`, `one_sub_paretoCDF_of_one_le`, `powerCDF_apply_of_nonpos`, `powerCDF_apply_of_one_le`, `standardGumbelCDF_pos`, `standardGumbelCDF_lt_one` | `DomainOfAttraction/VonMises.lean`, `ExtremeValueDistribution.lean` |
| `paretoCDF hα` is the c.d.f. of `paretoMeasure 1 α` | `paretoCDF_apply_eq_measureReal_Iic` | `DomainOfAttraction/VonMises.lean` |
| exponential tail of a random variable, `P(E > v) = e^{-v}` | `measureReal_lt_expMeasure_of_hasLaw` | `Statistics/HillNormality.lean` |
| `⌊√n⌋ → ∞` in `ℝ`, `log x / √x → 0`, `log n / ⌊√n⌋ → 0` | `tendsto_natCast_sqrt_atTop`, `tendsto_log_div_sqrt_atTop`, `tendsto_log_div_natSqrt` | `Dependence/MDependent.lean` |
| block / run probabilities of an iid sequence | `measureReal_blockEvent_of_iIndepFun`, `measureReal_runEvent_of_iIndepFun` | `Statistics/ExtremalIndexEstimatorsIid.lean` |
| Ferro–Segers law: moments integrable, `θ = 1` is `Exp(1)` | `integrable_pow_ferroSegersLaw`, `integrable_id_ferroSegersLaw`, `integrable_sq_ferroSegersLaw`, `ferroSegersLaw_one` | `Statistics/FerroSegersLaw.lean` |
| order statistics of a sorted sample | `orderStat_of_monotone`, `orderStat_eq_of_monotone_comp` | `Statistics/OrderStatisticsSorted.lean` |

Before adding a test helper, search the library and Mathlib (e.g. `HasLaw.measure_eq`,
`HasLaw.measureReal_eq`, `HasLaw.identDistrib`, `ProbabilityTheory.exists_iid`,
`CumulativeDistributionFunction.hasLaw_measure_iff`, `isRegularlyVarying_tail_paretoMeasure`,
`standardGumbelCDF_pow_apply_add_log`); if a test has to work around a missing evaluation,
measurability or `simp` lemma, add that lemma to the library instead.

A lemma stays in **`Test/`** only if it is about a concrete object built for one test (a specific
sample, compact parameter set, sequence `rₙ = ⌊√⌊√n⌋⌋`, product space, innovation law, …) or is
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
