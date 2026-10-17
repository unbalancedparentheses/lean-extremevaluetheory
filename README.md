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
- **Gumbel domain, sufficient conditions**: the auxiliary-function criterion
  `(1 - F(t + x f(t)))/(1 - F(t)) → e^(-x)` (infinite and finite right endpoint) and the
  von Mises condition imply `F` is in the Gumbel domain; the exponential and Gumbel laws are
  examples. (The converse, via Γ-variation, is not yet formalized.)
- **Peaks over threshold, heavy-tailed case** (`tendstoUniformlyOn_excessSurvival`): if `F̄` is
  regularly varying with index `-α`, the scaled excess distribution `F̄(u + (u/α)x)/F̄(u)`
  converges to the generalized Pareto survival function `(1 + x/α)^(-α)` uniformly in `x ≥ 0`
  (Pickands–Balkema–de Haan); the mean excess satisfies `e(u)/u → 1/(α-1)` for `α > 1`.
- **Subexponential distributions** (`IsSubexponential`): regularly varying tails are
  subexponential; `P(X₁+…+Xₙ > x) ~ n P(X > x)` and the single big jump
  `P(X₁+…+Xₙ > x) ~ P(max Xᵢ > x)` for iid samples; Kesten's bound.
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
