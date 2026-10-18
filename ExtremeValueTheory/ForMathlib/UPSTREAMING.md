# Upstreaming `ExtremeValueTheory/ForMathlib` to Mathlib

This file plans how to move the `ForMathlib` files into Mathlib as a series of small PRs.
The files import only Mathlib and each other. Every declaration passes `#lint` (Batteries and
Mathlib linters) and the Mathlib standard style linter set (`linter.mathlibStandardSet`,
`linter.style.header`). The pinned Mathlib is `v4.35.0`.

## Checks before opening any PR

1. **Module system (done).** Every file here is a module, following the Mathlib convention:
   the header `module`, then `public import` for the imports, then the module docstring, then
   `@[expose] public section` in the files that contain definitions (`Vague`, `Stationary`,
   `Mixing`, `PoissonRandomMeasure`, `PoissonLimit`, `RandomMeasureLaw`,
   `PointProcessConvergence`), so that bodies such as `TendstoVaguely`, `IsStationary`,
   `IsMDependent`, the mixing coefficients, `sumDiracRange`, `poissonSampleMeasure` and
   `torusMeasure` can be unfolded downstream. Files with only theorems use `public section`.
   The one import needed only in proofs (`Mathlib.Algebra.BigOperators.Fin` in `Mixing.lean`)
   is a plain `import`. The rest of the library is not yet in the module system and imports
   these files as before. Before opening a PR, check (with Mathlib's `shake`) which imports
   can be demoted from `public import` to `import`.
2. **Bibliography.** `docs/references.bib` already has `billingsley1999`, `kallenberg2017` and
   `kallenberg2021`. Add these keys with the first PR that cites them: `resnick1987`,
   `leadbetter1983`, `bradley2005`, `lastpenrose2017`, `abramowitz1964` and `feller1968`. The
   entries, in Mathlib's format, are in `references.bib` in this directory.
3. **Naming and placement.** Some helpers live in `ProbabilityTheory` only because that is where
   they were needed. Move them to their natural namespaces when upstreaming:
   - The `ereal_exp_neg_coe_*` lemmas and `continuous_ereal_exp_neg_coe`, which are split
     between `PoissonRandomMeasureLaplace.lean` and `RandomMeasureLaw.lean`, go together into
     `EReal`. A possible scheme is `EReal.exp_neg_coe_ennreal_add` and so on.
   - `cexp_sum_indicator_eq` goes into `Complex`.
   - `tendsto_prod_range_one_add` goes into `Complex`.
   - `integral_Ioc_cexp_mul_intCast_mul_I` goes near `integral_exp_mul_complex`.
4. **Zulip.** Before each probability PR, search the `#mathlib4` and `#Is there code for X?`
   streams. Topics that may overlap with ongoing work are listed in the last section.

## Duplicate audit (done in this repository)

The audit was done in three ways:

- A meta-program compared every `ForMathlib` declaration against all Mathlib constants, both by
  type (up to α-equivalence) and by name in the same namespace. It found no hits.
- Every name was grepped across Mathlib.
- The likely candidates were reviewed by hand.

Changes made as a result:

- `BoundedContinuousFunction.ofAbsLe` (with `_apply`) was deleted. It duplicated
  `BoundedContinuousFunction.ofNormedAddCommGroup` (with `coe_ofNormedAddCommGroup`), and its
  uses, including those in `RegularVariation/Multivariate.lean`, now call the Mathlib versions.
- `Measure.exists_continuous_hasCompactSupport_one_on_zero_off` was deleted. It only restated
  `exists_continuous_one_zero_of_isCompact`, which is now called directly.
- `measurable_of_measurable_nat_prod` is now `private`. It is a specialization of
  `measurable_from_prod_countable_right` that elaborates better at its call sites.

Overlaps that remain on purpose. Resolve them in review:

- **`Measure.ext_of_forall_integral_eq_of_hasCompactSupport`** (`Vague.lean`) is close to
  Mathlib's `Measure.ext_of_integral_eq_on_compactlySupported` (RMK, `RieszMarkovKakutani/Real`).
  Our version takes unbundled functions (`Continuous f → HasCompactSupport f`) and assumes only
  `[OpensMeasurableSpace X]`. Mathlib's version takes bundled `C_c(X, ℝ)` and assumes
  `[BorelSpace X]`. The upstream PR should generalize the Mathlib lemma, or add the unbundled
  form as a corollary, rather than add a second proof. The blueprint references our name, so
  keep it here, or make it a deprecated alias, until then.
- **`TendstoInDistribution.exists_measure_le_abs_le`** is a filter-indexed, real-valued
  tightness statement. Mathlib's `isTightMeasureSet_*` lemmas in `Measure/TightNormed` and
  `LevyConvergence` are about sets of measures. Check whether it can be stated as, or derived
  from, `IsTightMeasureSet` of the range.
- **`sum_measureReal_sub_sum_inter_le_measureReal_biUnion`** (Bonferroni) is the truncated
  inequality. The exact inclusion–exclusion formula `measureReal_biUnion_eq_sum_powerset` is
  already in Mathlib, so the PR could also derive the inequality from it.

## Target paths

| ForMathlib file | Lines | Proposed Mathlib location |
|---|---|---|
| `MeasureTheory/Measure/Bonferroni.lean` | 59 | `Mathlib/MeasureTheory/Measure/Real.lean` (append) or new `Mathlib/MeasureTheory/Measure/Bonferroni.lean` |
| `MeasureTheory/Function/ConvergenceInDistribution.lean` | 68 | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` (append) |
| `MeasureTheory/Measure/Portmanteau.lean` | 328 | new `Mathlib/MeasureTheory/Measure/Portmanteau/Measure.lean`, or the end of `Mathlib/MeasureTheory/Measure/Portmanteau.lean` |
| `MeasureTheory/Measure/Vague.lean` | 270 | new `Mathlib/MeasureTheory/Measure/Vague.lean` |
| `Analysis/SpecialFunctions/Gamma/Trigamma.lean` | 201 | analyticity in `Gamma/Deriv.lean`; values in new `Mathlib/Analysis/SpecialFunctions/Gamma/Trigamma.lean`; `Γ''` in `Gamma/Deriv.lean` |
| `Probability/Process/Stationary.lean` | 130 | new `Mathlib/Probability/Process/Stationary.lean` |
| `Probability/Process/Mixing.lean` | 327 | new `Mathlib/Probability/Independence/MixingCoeff.lean` (σ-algebra part) and `Mathlib/Probability/Process/Mixing.lean` (process part) |
| Poisson-distribution helpers in `PoissonRandomMeasure.lean`, `PoissonLimit.lean` | ~80 | `Mathlib/Probability/Distributions/Poisson/Basic.lean` |
| `Probability/PoissonRandomMeasure.lean` | 928 | new directory `Mathlib/Probability/PointProcess/Poisson/` (`Defs`, `Construction`, `Superposition`) |
| `Probability/PoissonRandomMeasureLaplace.lean` | 224 | `Mathlib/Probability/PointProcess/Poisson/Laplace.lean` |
| `Probability/RandomMeasureLaw.lean` | 319 | moments on `[0,1]^k` in `Mathlib/MeasureTheory/Measure/FiniteMeasureExt.lean`; rest in `Mathlib/Probability/PointProcess/Law.lean` |
| `Probability/PoissonLimit.lean` | 397 | inversion in `Mathlib/Probability/CharacteristicFunction/Lattice.lean` (new); product limit in `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean`; theorem in `Mathlib/Probability/Distributions/Poisson/PoissonLimitThm.lean` |
| `Probability/BinomialPointProcess.lean` | 103 | `Mathlib/Probability/PointProcess/Binomial.lean` |
| `Probability/PointProcessConvergence.lean` | 159 | `Mathlib/Probability/PointProcess/Convergence.lean` |

## Dependency graph between PRs

```
A1 Bonferroni            (leaf)
A2 Tightness             (leaf)
A3 Portmanteau a,b,c     (leaf chain: a <- b, a <- c)
A4 Gamma a <- b <- c     (leaf chain)
B1 Stationary            (leaf)
B2 MixingCoeff <- B3 ProcessMixing
C1 Vague a <- b
D1 Poisson helpers       (leaf)
D2 EReal exp(-a)         (leaf)
E1 PRM defs   <- D1
E2 PRM finite construction <- E1
E3 PRM superposition + existence <- E2
E4 Laplace functional    <- E1, D2
E5a moments on cube      (leaf)
E5b law of random measure <- E4, E5a, D2
F1a lattice inversion    (leaf)    F1b prod limit (leaf)
F1c Poisson limit for counts <- F1a, F1b, D1
G1 Binomial point process <- C1, E2
G2 Point process convergence <- C1, E1, F1c
```

The leaves (A*, B1, B2, C1, D*, E5a, F1a, F1b) can be opened in parallel.

## PR drafts

Line counts are approximate and include docstrings.

### A1. Second Bonferroni inequality (~60 lines)
**Title:** `feat(MeasureTheory/Measure/Real): second Bonferroni inequality`
> Proves `∑ μ(Aᵢ) - ∑_{i<j} μ(Aᵢ ∩ Aⱼ) ≤ μ(⋃ Aᵢ)` for finitely many measurable sets under a
> finite measure, stated with `Measure.real`. Together with the union bound, this is the
> order-two inclusion–exclusion estimate used in Poisson approximation and extreme value theory.
> It complements the exact formula `measureReal_biUnion_eq_sum_powerset`.

### A2. Tightness of sequences converging in distribution (~70 lines)
**Title:** `feat(MeasureTheory/Function/ConvergenceInDistribution): convergent sequences are tight`
> Adds `TendstoInDistribution.exists_measure_le_abs_le`: if real random variables `X i` converge
> in distribution along any filter, then for every `ε > 0` there is `M` with
> `μ i {M ≤ |X i|} ≤ ε` eventually. The proof applies the portmanteau `limsup` bound for closed
> sets. Reviewers may prefer an `IsTightMeasureSet` formulation, so discuss before merging.

### A3a. Portmanteau for families that are eventually probability measures (~100 lines)
**Title:** `feat(MeasureTheory/Measure/Portmanteau): weak convergence of eventually-probability families`
> Mathlib's portmanteau is stated for `γ → ProbabilityMeasure Ω`. Conditional laws `P[·|A n]`
> are probability measures only eventually. This PR adds `exists_probabilityMeasure_eventuallyEq`,
> `exists_tendsto_probabilityMeasure`, the Lipschitz test-function criterion
> `tendsto_integral_of_forall_lipschitz`, the null-frontier implication and uniqueness of limits
> (`eq_of_forall_integral_tendsto`) for `γ → Measure Ω`.

### A3b. Weak convergence against `H · 1{c < ψ}` (~120 lines, after A3a)
**Title:** `feat(MeasureTheory/Measure/Portmanteau): integrals of truncated bounded continuous functions`
> `tendsto_integral_indicator_of_forall_integral_tendsto`: weak convergence extends to
> `y ↦ 1{c < ψ y} H y` for `H` bounded continuous and `ψ` continuous, provided the limit gives
> no mass to `{ψ = c}`. The proof approximates the indicator by explicit continuous cutoffs.

### A3c. Weak convergence of finite measures via normalization (~110 lines, after A3a, A3b)
**Title:** `feat(MeasureTheory/Measure/Portmanteau): portmanteau for finite measures by normalization`
> `tendsto_integral_normalize` shows that weak convergence of finite measures implies
> convergence of the total masses and weak convergence of the normalized probability measures.
> As corollaries, it adds the null-frontier and truncated-integral statements for finite
> measures.

### A4a. Analyticity of `Γ` and `ψ` on the right half-plane (~30 lines)
**Title:** `feat(Analysis/SpecialFunctions/Gamma): Gamma and digamma are analytic for re s > 0`
> `differentiableOn_Gamma_re_pos`, `analyticAt_Gamma_of_re_pos`, `analyticAt_digamma_of_re_pos`
> and `hasDerivAt_digamma_of_re_pos`. These are small API lemmas used to differentiate the
> reflection and duplication formulas for `digamma`. Consider whether a global
> `MeromorphicOn`/`AnalyticOnNhd` statement off the poles already exists or is wanted.

### A4b. Trigamma at `1/2` and `1`, and `Γ''(1)` (~110 lines, after A4a)
**Title:** `feat(Analysis/SpecialFunctions/Gamma/Trigamma): ψ'(1/2) = π²/2, ψ'(1) = π²/6, Γ''(1) = γ² + π²/6`
> Differentiates `digamma_one_sub` (reflection) at `1/2` and `digamma_two_mul` (duplication)
> to compute `deriv digamma (1/2) = π²/2` and `deriv digamma 1 = π²/6` without series. It then
> deduces `deriv (deriv Gamma) 1 = γ² + π²/6`. This gives a series-free proof of `ζ(2) = π²/6`
> in the form `ψ'(1)`.

### A4c. Second derivative of `Γ` as an integral (~60 lines, after A4b)
**Title:** `feat(Analysis/SpecialFunctions/Gamma/Deriv): Γ'' as a Mellin integral; ∫ (log t)² e^{-t}`
> `hasDerivAt_deriv_Gamma_of_re_pos` differentiates the Mellin representation of `Γ'` once more,
> and `Real.integral_log_sq_mul_exp_neg` evaluates `∫₀^∞ (log t)² e^{-t} dt = γ² + π²/6`. This is
> the second moment of the Gumbel law.

### B1. Stationary processes in discrete time (~130 lines)
**Title:** `feat(Probability/Process/Stationary): strictly stationary processes`
> Defines `IsStationary X μ` for `X : ℕ → Ω → E` as shift invariance of the path law on
> `ℕ → E`. Proves invariance under all shifts and for path events, identical distribution of the
> marginals, stationarity of i.i.d. sequences and of sliding-window factors. Check whether
> reviewers want `MeasurePreserving` of the shift on the path law as the definition, which would
> connect to `Dynamics.Ergodic`.

### B2. Mixing coefficients of two σ-algebras (~190 lines)
**Title:** `feat(Probability/Independence/MixingCoeff): α- and β-mixing coefficients`
> Defines `strongMixingCoeff m₁ m₂ μ` (Rosenblatt's `α`) and `betaMixingCoeff m₁ m₂ μ` (absolute
> regularity `β`) as suprema in `ℝ≥0∞`. Proves monotonicity, `α ≤ 1`, the defining inequality,
> vanishing under independence (`Indep m₁ m₂ μ`), and `α ≤ β`.

### B3. Mixing and `m`-dependence of processes (~140 lines, after B2)
**Title:** `feat(Probability/Process/Mixing): strong mixing, β-mixing and m-dependence`
> Defines the past and future σ-algebras of a process, the coefficients `alphaMixing X μ h` and
> `betaMixing X μ h`, the predicates `IsStrongMixing`, `IsBetaMixing` and `IsMDependent`.
> Shows that `m`-dependent processes have vanishing coefficients beyond lag `m` (hence are
> `α`- and `β`-mixing), that `X s` and `X t` are independent for `t > s + m`, and that
> `m`-dependence is stable under coordinatewise measurable maps.

### C1a. Vague convergence: definition and uniqueness (~170 lines)
**Title:** `feat(MeasureTheory/Measure/Vague): vague convergence of measures`
> Defines `Measure.TendstoVaguely μs l μ` (convergence of integrals of continuous compactly
> supported functions), as a predicate rather than a topology. Proves that regular measures are
> determined by these integrals and that vague limits of regular measures are unique. The
> extensionality lemma overlaps with `ext_of_integral_eq_on_compactlySupported` (RMK), so this PR
> should generalize that lemma to `OpensMeasurableSpace` instead of adding a second copy.

### C1b. Portmanteau for vague convergence (~100 lines, after C1a)
**Title:** `feat(MeasureTheory/Measure/Vague): portmanteau inequalities; weak ⇒ vague`
> Adds `limsup μs K ≤ μ K` for compact `K`, `μ U ≤ liminf μs U` for open `U`, and convergence
> on relatively compact `μ`-continuity sets. Also shows that weak convergence of finite or
> probability measures implies vague convergence.

### D1. Poisson distribution API (~80 lines)
**Title:** `feat(Probability/Distributions/Poisson): mean, Dirac at 0, and joint characteristic functions`
> `poissonMeasure_zero`, the mean `∫⁻ n ∂poissonMeasure r = r`, the characteristic function as
> an integral over `ℕ`, and products of independent Poisson laws: the joint characteristic
> function and point masses of `Measure.pi (poissonMeasure ∘ r)`. To be extracted from
> `PoissonRandomMeasure.lean` and `PoissonLimit.lean`.

### D2. `exp (-a)` on `[0, ∞]` (~50 lines)
**Title:** `feat(Analysis/SpecialFunctions/Log/ERealExp): exp of negated extended nonnegative reals`
> Lemmas on `a ↦ EReal.exp (-(a : EReal))` for `a : ℝ≥0∞`: continuity, the value at finite `a`,
> the bound `≤ 1`, and multiplicativity over sums and natural multiples. Consolidates the helpers
> from `PoissonRandomMeasureLaplace.lean` and `RandomMeasureLaw.lean` under `EReal.*` names.

### E1. Poisson random measures: definition and basic API (~310 lines; split if requested)
**Title:** `feat(Probability/PointProcess/Poisson/Defs): Poisson random measures`
> Defines `IsPoissonRandomMeasure N ν P`: the joint law of the counts on disjoint sets of finite
> intensity is a product of Poisson laws, and sets of infinite intensity have a.s. infinite
> count. Derives the Poisson marginals (`hasLaw`), independence of disjoint counts and the
> Laplace functional at simple functions. Shows that for σ-finite `ν` the infinite-intensity
> field is automatic (`of_map_eq_pi`). Can be split at `section MapEqPi` / `namespace
> IsPoissonRandomMeasure` if 310 lines is too long.

### E2. Construction for finite intensity (~300 lines, after E1; split into two)
**Title:** `feat(Probability/PointProcess/Poisson/Construction): mixed binomial construction`
> Defines `sumDiracRange n z = ∑_{k<n} δ_{z k}` and `poissonSampleMeasure c μ` (Poisson count
> times an i.i.d. sequence). Proves `isPoissonRandomMeasure_sumDiracRange` and the Laplace
> functional `integral_exp_neg_integral_sumDiracRange`. Suggested split: (i) the
> counting-measure API and integrals over `poissonSampleMeasure`, (ii) the characteristic
> function computation and the main theorem.

### E3. Superposition and existence (~300 lines, after E2)
**Title:** `feat(Probability/PointProcess/Poisson/Superposition): existence for s-finite intensities`
> `isPoissonRandomMeasure_sum_sumDiracRange`: a countable superposition of independent
> finite-intensity Poisson random measures is Poisson with the summed intensity. The proof uses
> dominated convergence of the characteristic functions, and Laplace transforms for the
> infinite-intensity sets. `exists_isPoissonRandomMeasure`: every s-finite measure is the
> intensity of a Poisson random measure.

### E4. Laplace functional (~220 lines, after E1, D2)
**Title:** `feat(Probability/PointProcess/Poisson/Laplace): Laplace functional of a Poisson random measure`
> For σ-finite intensity and any measurable `f : E → ℝ≥0∞`, proves
> `E exp(-∫ f dN) = exp(-∫ (1 - exp(-f)) dν)` in `[0, ∞]`. It first proves the identity for
> simple functions, then uses monotone approximation. Includes
> `SimpleFunc.lintegral_comp_eq_sum_fin`, which may belong in
> `MeasureTheory/Function/SimpleFunc.lean`.

### E5a. Measures on `[0,1]^k` are determined by their moments (~75 lines)
**Title:** `feat(MeasureTheory/Measure/FiniteMeasureExt): finite measures on the cube are determined by moments`
> `ext_of_forall_integral_prod_pow_eq`, by Stone–Weierstrass applied to the monomials in the
> coordinates of `Fin k → unitInterval`. Check whether a Hausdorff moment uniqueness statement
> already exists, or is in progress, for `[0,1]`.

### E5b. The law of a random measure is determined by its Laplace functional (~170 lines)
**Title:** `feat(Probability/PointProcess/Law): Laplace functional determines the law of a random measure`
> `map_eq_of_lintegral_exp_neg_sum_eq` and `map_eq_of_lintegral_exp_neg_lintegral_eq`: two
> random measures with equal Laplace functionals on `ℕ`-valued simple functions have the same
> law on `Measure E` with the Giry σ-algebra. Corollary: Poisson random measures with a given
> σ-finite intensity are unique in law (`IsPoissonRandomMeasure.map_eq`).

### F1a. Inversion formula on `ℕ^k` (~140 lines)
**Title:** `feat(Probability/CharacteristicFunction): inversion for lattice-valued random vectors`
> `integral_torusMeasure_charFun_mul`: `(2π)^k P(Y = m) = ∫_{(0,2π]^k} φ_Y(t) e^{-i⟨t,m⟩} dt`
> for `Y` with values in `ℕ^k`. Consequence: pointwise convergence of characteristic functions
> implies convergence of point masses. Check overlap with the Lévy continuity work
> (`LevyConvergence`) and with Fourier series on `AddCircle`.

### F1b. Products `∏ (1 + w i) → exp s` (~50 lines)
**Title:** `feat(Analysis/SpecialFunctions/Complex/LogBounds): limits of products of 1 + small terms`
> `tendsto_prod_range_one_add`: if `∑_{i<n} w n i → s`, `∑ ‖w n i‖` is bounded and
> `max ‖w n i‖ → 0`, then `∏_{i<n} (1 + w n i) → exp s`. This is the standard triangular-array
> lemma behind Poisson and Lindeberg-type limit theorems.

### F1c. Multivariate Poisson limit for triangular arrays (~155 lines, after F1a, F1b, D1)
**Title:** `feat(Probability/Distributions/Poisson/PoissonLimitThm): multinomial Poisson limit theorem`
> `tendsto_measureReal_card_filter_range_eq`: the counts `#{i < n | Z n i ∈ B j}` of independent
> points in disjoint sets converge jointly to independent Poisson laws. This generalizes the
> existing binomial `tendsto_choose_mul_pow_of_tendsto_mul_atTop` to non-identically distributed
> rows and to several sets at once.

### G1. Binomial point processes (~100 lines, after C1, E2)
**Title:** `feat(Probability/PointProcess/Binomial): Poisson approximation of binomial point processes`
> The Laplace functional of `∑_{k<n} δ_{Z k}` for `Z` i.i.d. If `n • μₙ → ν` vaguely, the
> Laplace functionals converge to `exp(-∫ (1 - e^{-f}) dν)` for continuous compactly supported
> `f ≥ 0` (Resnick, Prop. 3.21).

### G2. Convergence in law of point processes (~160 lines, after C1, E1, F1c)
**Title:** `feat(Probability/PointProcess/Convergence): binomial point processes converge to Poisson`
> Defines `TendstoInLawVaguely` (convergence of the finite-dimensional count laws on disjoint
> relatively compact `ν`-continuity sets). Proves that binomial point processes with
> `n • μ n → ν` vaguely converge in this sense to the Poisson random measure with intensity
> `ν`. Reviewers may ask for the vague topology on `Measure E` and convergence in law in that
> topology instead. See the Zulip notes below.

## Possible overlaps to raise on Zulip before submitting

- **Poisson point processes / random measures.** Search for "Poisson process", "point process"
  and "random measure". Ask whether anyone is formalizing Poisson processes on `ℝ≥0` (counting
  processes, Lévy processes) or marked point processes. Agree on a home directory
  (`Probability/PointProcess/`?) and on whether a random measure should be `Ω → Measure E`
  (measurable for the Giry σ-algebra, as here) or a kernel.
- **Vague topology.** Mathlib has the weak topology on `FiniteMeasure`/`ProbabilityMeasure` and
  RMK for regular measures. Ask whether a topology on Radon measures (or on `C_c(X, ℝ) →ₚ ℝ`) is
  planned. If so, `TendstoVaguely` should be `Tendsto` in that topology, and C1 should build on
  it. The extensionality lemma should merge with `ext_of_integral_eq_on_compactlySupported`.
- **Stationary processes / ergodic theory.** Check with the `Dynamics.Ergodic` maintainers
  whether stationarity should be phrased as `MeasurePreserving` of the shift on
  `Measure.infinitePi`/path laws. Also check consistency with
  `Probability/Process/FiniteDimensionalLaws`.
- **Mixing.** "Mixing" in `Dynamics` means something else (`T`-mixing of measure-preserving
  maps). Ask whether α/β/φ/ρ-mixing coefficients are wanted and under which names, and whether
  someone is doing CLTs for mixing sequences.
- **Brownian motion project** (R. Degenne et al.). It develops stochastic-process
  infrastructure: Kolmogorov extension and continuity, Gaussian processes, `IsGaussianProcess`,
  finite-dimensional laws, `Indistinguishable`. Check its conventions for processes indexed by
  `ℕ`/`ℝ≥0` and for path σ-algebras before B1 and B3, so that the definitions agree with what
  will be upstreamed from there.
- **Characteristic functions / Lévy continuity / tightness.** `charFun`, `LevyConvergence` and
  `TightNormed` are active areas. A2 and F1a should be coordinated with whoever maintains them.
- **Gamma / zeta.** `ψ'(1) = π²/6` relates to `riemannZeta_two`/`hasSum_zeta_two`. Mention it
  in A4b and ask whether a general `trigamma` definition is wanted.

## Added later: delta method and Wald intervals

- `Probability/DeltaMethod.lean`: continuous mapping in probability, tightness from convergence in
  distribution, `rₙYₙ ⇒ Z, rₙ → ∞ ⟹ Yₙ → 0` in probability, the delta method (general limit and
  Gaussian), and the law of `⟨a, X⟩` for a multivariate Gaussian. Mathlib v4.35.0 has no delta method.
- `Probability/WaldInterval.lean`: asymptotic coverage of `θ̂ ± zŜ/r` and existence of the Gaussian
  quantile `z` with `N(0,1)([−z, z]) = 1 − α`.
- Both cite `vandervaart1998`; add that key to `references.bib` with the first PR.
