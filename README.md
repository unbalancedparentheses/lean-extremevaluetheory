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
- **Karamata's tail-integral theorem** (`IsRegularlyVarying.tendsto_integral_Ioi_div`): for an
  antitone survival function regularly varying with index `-α`, `α > 1`,
  `∫ₓ^∞ F̄(t) dt / (x F̄(x)) → 1/(α-1)`. Proved, standard axioms only.
- **Breiman's lemma** (`tendsto_measure_mul_div_measure`): for independent `X`, `Y ≥ 0` with
  `P(X > x)` regularly varying with index `-α` and `E[Y^(α+ε)] < ∞`,
  `P(XY > x) / P(X > x) → E[Y^α]`. Proved, standard axioms only.
- **Gnedenko's characterization of the Fréchet domain** (`isInMDAFrechet_iff`): `F` is in the
  maximum domain of attraction of the Fréchet law `exp(-x^(-α))` if and only if `1 - F` is
  regularly varying with index `-α`. Both directions proved, standard axioms only.
- **Gnedenko's characterization of the Weibull domain** (`isInMDAWeibull_iff`): `F` is in the
  domain of attraction of `exp(-(-x)^α)` if and only if it has a finite right endpoint `x_F` and
  `1 - F(x_F - 1/t)` is regularly varying with index `-α`.
- **Characterization of the Gumbel domain** (`isInMDAGumbel_iff`): `F` is in the domain of
  attraction of `exp(-e^(-x))` if and only if there is a positive auxiliary function `f` with
  `(1 - F(t + x f(t)))/(1 - F(t)) → e^(-x)` as `t` tends to the right endpoint (finite or
  infinite). The von Mises condition is a sufficient criterion, for infinite and finite right
  endpoints (`isInMDAGumbel_of_vonMises`, `isInMDAGumbel_of_vonMises_nhdsLT`); the exponential,
  Gumbel and `1 - exp(-x/(1-x))` laws are examples.
- **Pickands–Balkema–de Haan** (`exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV'`): if `F`
  is in the domain of attraction of the extreme value law with shape `ξ ∈ ℝ`, there is a scale
  `β(u) > 0` with `F̄(u + β(u)x)/F̄(u)` converging to the generalized Pareto survival function of
  shape `ξ` uniformly in `x ≥ 0` as `u` tends to the right endpoint. For `ξ > 0` and `ξ < 0` this
  is an equivalence (`isInMDAFrechet_iff_tendstoUniformlyOn_excessSurvival`,
  `isInMDAWeibull_iff_tendstoUniformlyOn_excessSurvival`). The mean excess satisfies
  `e(u)/u → 1/(α-1)` for regularly varying tails with `α > 1`.
- **Subexponential distributions** (`IsSubexponential`): regularly varying tails are
  subexponential; `P(X₁+…+Xₙ > x) ~ n P(X > x)` and the single big jump
  `P(X₁+…+Xₙ > x) ~ P(max Xᵢ > x)` for iid samples; Kesten's bound.
- **Hill estimator consistency** (`tendstoInMeasure_hill`): for iid samples whose tail is
  regularly varying with index `-α`, and `k → ∞`, `k/n → 0`, the Hill estimator
  `(1/k) Σ_{i<k} (log X₍ᵢ₊₁₎ - log X₍ₖ₊₁₎)` converges to `1/α` in probability. With order
  statistics and their binomial distribution.
- **Stable laws and the generalized central limit theorem, symmetric case**
  (`tendsto_map_convPow_of_isRegularlyVarying`): for iid symmetric `X` with `P(|X| > x)`
  regularly varying of index `-α`, `0 < α < 2`, and `n P(|X| > aₙ) → 1`, the law of
  `(X₁+…+Xₙ)/aₙ` converges weakly to the symmetric α-stable law with characteristic function
  `exp(-C_α|t|^α)`. Symmetric α-stable laws exist for every `0 < α ≤ 2` (`exists_isSymmStable`);
  Gaussian and Cauchy laws are stable, with the Cauchy characteristic function computed. Includes
  the Lévy continuity theorem with existence of the limit (`exists_tendsto_of_tendsto_charFun`).
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
