# Extreme Value Theory in Lean

A Lean 4 / Mathlib formalization of extreme value theory and heavy-tailed probability.

**Goals**

- **Fisher–Tippett–Gnedenko**: the only non-degenerate limits of normalized maxima are the
  Gumbel, Fréchet and Weibull families (the generalized extreme value distributions).
- **Regular variation**: slowly and regularly varying functions, Potter bounds, Karamata's
  theorem, Breiman's lemma.
- **Domains of attraction**: Gnedenko's characterization of the Fréchet domain by regularly
  varying tails.
- **Peaks over threshold**: Pickands–Balkema–de Haan and the generalized Pareto distribution.
- **Estimation**: consistency of the Hill estimator.

## Status

- **Fisher–Tippett–Gnedenko** (`CumulativeDistributionFunction.IsExtremeValueDistr.classification`):
  proved, depending only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
- **Max-stability and the GEV family** (`GEV/`): max-stable laws are exactly the extreme value
  laws (`isMaxStable_iff_isExtremeValueDistr`); the unified family `H_ξ` (`gevCDF`) with explicit
  affine links to the three types, the Jenkinson–von Mises form of Fisher–Tippett–Gnedenko
  (`IsExtremeValueDistr.exists_smul_eq_gevCDF`), and moments: the Gumbel mean is Euler's `γ` and its variance `π²/6`, GEV
  means and variances via `Γ`, probability-weighted moments. Block maxima: normalized block maxima
  and their empirical c.d.f. converge to `H` (`tendstoInMeasure_blockMaxEmpCDF`).
- **Karamata's tail-integral theorem** (`IsRegularlyVarying.tendsto_integral_Ioi_div`): for an
  antitone survival function regularly varying with index `-α`, `α > 1`,
  `∫ₓ^∞ F̄(t) dt / (x F̄(x)) → 1/(α-1)`. Proved, standard axioms only.
- **Karamata's theorem, both halves and the `[0, x]` version**
  (`IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi`, `tendsto_integral_zero_div`,
  `tendsto_integral_Ioi_div_of_measurable`): the converse half, integrals over `[0, x]`, and the
  tail-integral theorem for measurable (not necessarily monotone) functions.
- **Breiman's lemma** (`tendsto_measure_mul_div_measure`): for independent `X`, `Y ≥ 0` with
  `P(X > x)` regularly varying with index `-α` and `E[Y^(α+ε)] < ∞`,
  `P(XY > x) / P(X > x) → E[Y^α]`. Proved, standard axioms only.
- **Gnedenko's characterization of the Fréchet domain** (`isInMDAFrechet_iff`): `F` is in the
  maximum domain of attraction of the Fréchet law `exp(-x^(-α))` if and only if `1 - F` is
  regularly varying with index `-α`. Both directions proved, standard axioms only.
- **Gnedenko's characterization of the Weibull domain** (`isInMDAWeibull_iff`): `F` is in the
  domain of attraction of `exp(-(-x)^α)` if and only if it has a finite right endpoint `x_F` and
  `1 - F(x_F - 1/t)` is regularly varying with index `-α`.
- **Von Mises conditions for Fréchet and Weibull** (`isInMDAFrechet_of_vonMises`,
  `isInMDAWeibull_of_vonMises`): `x F'(x)/(1 − F(x)) → α` (resp. `(x_F − x) F'(x)/(1 − F(x)) → α`)
  gives the domain of attraction. Pareto and Beta(1, α) are examples.
- **Characterization of the Gumbel domain** (`isInMDAGumbel_iff`): `F` is in the domain of
  attraction of `exp(-e^(-x))` if and only if there is a positive auxiliary function `f` with
  `(1 - F(t + x f(t)))/(1 - F(t)) → e^(-x)` as `t` tends to the right endpoint (finite or
  infinite). The von Mises condition is a sufficient criterion, for infinite and finite right
  endpoints (`isInMDAGumbel_of_vonMises`, `isInMDAGumbel_of_vonMises_nhdsLT`); the exponential,
  Gumbel and `1 - exp(-x/(1-x))` laws are examples.
- **Pickands–Balkema–de Haan** (`exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV'`): if `F`
  is in the domain of attraction of the extreme value law with shape `ξ ∈ ℝ`, there is a scale
  `β(u) > 0` with `F̄(u + β(u)x)/F̄(u)` converging to the generalized Pareto survival function of
  shape `ξ` uniformly in `x ≥ 0` as `u` tends to the right endpoint. This is an equivalence for
  every `ξ`, with an arbitrary scale function in the converse
  (`isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`). The mean excess satisfies
  `e(u)/u → 1/(α-1)` for regularly varying tails with `α > 1`.
- **Subexponential distributions** (`IsSubexponential`): regularly varying tails are
  subexponential; `P(X₁+…+Xₙ > x) ~ n P(X > x)` and the single big jump
  `P(X₁+…+Xₙ > x) ~ P(max Xᵢ > x)` for iid samples; Kesten's bound. Closure under tail
  equivalence and convolution; random sums `P(S_N > x) ~ E N · P(X > x)`
  (`IsSubexponential.tendsto_tail_compound_div`); the Embrechts–Veraverbeke ruin asymptotics
  `ψ(u) ~ F̄_I(u)/ρ` from the Pollaczek–Khinchine formula (`tendsto_pkRuin_div`,
  `tendsto_pkRuin_div_mul_tail`); Weibull-type tails `exp(-x^τ)`, `τ < 1`, are subexponential. The lognormal law
  is subexponential (`IsSubexponential.lognormal`), the class `𝒮*` is contained in `𝒮` and gives
  subexponential integrated tails (`IsSStar.isSubexponential_integratedTail`), and `𝒮` is closed
  under convolution roots (`IsSubexponential.of_convPow`).
- **Hill estimator consistency** (`tendstoInMeasure_hill`): for iid samples whose tail is
  regularly varying with index `-α`, and `k → ∞`, `k/n → 0`, the Hill estimator
  `(1/k) Σ_{i<k} (log X₍ᵢ₊₁₎ - log X₍ₖ₊₁₎)` converges to `1/α` in probability. With order
  statistics and their binomial distribution.
- **Hill estimator asymptotic normality** (`tendstoInDistribution_hill`): under second-order
  regular variation with `√k A(n/k) → λ`, `√k(γ̂ − γ) ⇒ N(λ/(1−ρ), γ²)`; the exact Pareto case
  `tendstoInDistribution_hill_pareto`. Via the Rényi representation.
- **Extended regular variation and the quantile characterization**
  (`isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile`): `F ∈ MDA(H_γ)` iff `U` is
  extended regularly varying with index `γ`.
- **Pickands estimator consistency for every ξ** (`tendstoInMeasure_pickands`): for `F` in the
  domain of attraction of `H_ξ`, `ξ ∈ ℝ`, the Pickands estimator converges to `ξ` in probability.
  The **moment estimator** (Dekkers–Einmahl–de Haan) is consistent for every `ξ`
  (`tendstoInMeasure_momentEstimator_of_isInMDAGEV'`, assuming `x_F > 0`).
- **Extreme quantiles** (`Statistics/ExtremeQuantile.lean`): ratio consistency of the Weissman
  estimator `X₍ₖ₊₁₎ (k/(n pₙ))^γ̂` and of the tail-probability estimator, for intermediate levels
  unconditionally and beyond the sample range given a `√k` rate for the Hill estimator and a bias
  condition (automatic for Pareto tails). GEV return levels.
- **Upper order statistics and records**: the Poisson limit law of the `k`-th largest
  (`tendsto_measureReal_orderStat_le`), the joint law of the two largest, and records: `P(record at
  k) = 1/k`, `E N_n = H_n`, `N_n / log n → 1` in probability (`tendstoInMeasure_recordCount_div_log`).
- **Stable laws and the generalized central limit theorem, symmetric case**
  (`tendsto_map_convPow_of_isRegularlyVarying`): for iid symmetric `X` with `P(|X| > x)`
  regularly varying of index `-α`, `0 < α < 2`, and `n P(|X| > aₙ) → 1`, the law of
  `(X₁+…+Xₙ)/aₙ` converges weakly to the symmetric α-stable law with characteristic function
  `exp(-C_α|t|^α)`. Symmetric α-stable laws exist for every `0 < α ≤ 2` (`exists_isSymmStable`);
  Gaussian and Cauchy laws are stable, with the Cauchy characteristic function computed. Includes
  the Lévy continuity theorem with existence of the limit (`exists_tendsto_of_tendsto_charFun`).
- **Generalized central limit theorem, asymmetric tails, `α ≠ 1`**
  (`tendsto_map_convPow_of_isRegularlyVarying_of_lt_one`,
  `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt`): with tail balance
  `P(X > x)/P(|X| > x) → p`, `S_n/aₙ` (for `α < 1`) and `(S_n − n E X)/aₙ` (for `1 < α < 2`)
  converge weakly to a skewed strictly stable law with characteristic function
  `exp(−C_α|t|^α(1 − i(2p−1) sign(t) tan(πα/2)))` with `C_α = Γ(1−α) cos(πα/2)`
  (`StableIntegral.stableConst_eq_Gamma_mul_cos`, `stableSkewConst_eq_mul_tan`, and the primed
  textbook-form theorems). For `α = 1`
  (`tendsto_map_convPow_sub_of_isRegularlyVarying_one'`), centering by `n E[X 1{|X| ≤ aₙ}]` gives
  the limit `exp(−(π/2)|t| + i(2p−1)(c t − t log|t|))` with `c` an explicit integral.
- **Extremes of stationary sequences** (`Dependence/`): stationarity (`IsStationary`),
  Leadbetter's conditions `D(uₙ)` and `D'(uₙ)`, Leadbetter's theorem `P(M_n ≤ uₙ) → e^{-τ}`
  (`tendsto_measureReal_partialMax_le_exp`), the extremal index `θ` (`HasExtremalIndex`), and
  `P(M_n ≤ aₙx + bₙ) → H(x)^θ` with `H^θ` of the same type. Iid sequences have `θ = 1`; the moving
  maximum `max(Z_t, Z_{t+1})` has `θ = 1/2`.
- **Tail process of regularly varying time series** (`Dependence/TailProcess.lean`,
  `TimeChange.lean`): the Basrak–Segers polar decomposition (`polar_iff`), equivalence of tail and
  spectral tail processes, the time-change formula
  (`HasSpectralTailProcess.lintegral_timeChange`), and the candidate extremal index
  `ϑ = E[sup_{k≥0}|Θ_k|^α − sup_{k≥1}|Θ_k|^α] = P(sup_{k≥1}|Y_k| ≤ 1)`, with `ϑ ≤ 1`, `ϑ = 1` for
  iid sequences, and `ϑ > 0` when `Θ_t → 0`.
- **Vague convergence and Poisson random measures** (`ForMathlib/`, Mathlib-only imports, intended
  for upstreaming): vague convergence with its portmanteau properties, Poisson random measures with
  existence for every s-finite intensity (`exists_isPoissonRandomMeasure`), Laplace functionals,
  the Laplace functional for all `f ≥ 0`, uniqueness of laws from
  Laplace functionals, a multivariate Poisson limit theorem for triangular arrays, and convergence
  in law of binomial point processes to Poisson random measures (`tendstoInLawVaguely_sumDiracRange`).
- **Point process of exceedances** (`PointProcess/Exceedances.lean`): for `F ∈ MDA(G)`, the
  normalized exceedance point process, in space and in time-space, converges to a Poisson random
  measure (`tendsto_measureReal_sumDiracRange_timeSpace_eq`); the limit laws of upper order
  statistics follow as corollaries.
- **Multivariate regular variation** (`RegularVariation/Multivariate.lean`): exponent measures on
  sets bounded away from 0, homogeneity, the polar decomposition `μ = α r^{−α−1}dr ⊗ S`
  (`isRegVarVector_iff`, `IsRegVarVector.eq_polarMeasure`), tails of linear combinations, and
  asymptotic independence vs. full dependence examples.
- **Uniform convergence theorem and Karamata's representation theorem** for measurable slowly
  and regularly varying functions (no monotonicity), with two-sided Potter bounds
  (`isSlowlyVarying_iff_exists_representation`, `potter_bounds_of_measurable`).
- Regular variation API: closure properties and the elementary monotone versions of the above.

The library contains no `sorry`.

The development started from [ExtremeValueProject](https://github.com/kkytola/ExtremeValueProject);
several of its statements were false as written and have been corrected. See
[`TRIAGE.md`](TRIAGE.md) for the list of corrections.

## Build

```sh
lake exe cache get
lake build
```

## Credits

The Fisher–Tippett–Gnedenko development and its blueprint are based on
[ExtremeValueProject](https://github.com/kkytola/ExtremeValueProject) by Kalle Kytölä and the
participants of the Aalto University course MS-EV0029 *Introduction to Formalized Mathematics
in Lean*. Derived files keep their original copyright headers; see [`NOTICE`](NOTICE).

## License

Apache 2.0, see [`LICENSE`](LICENSE).
