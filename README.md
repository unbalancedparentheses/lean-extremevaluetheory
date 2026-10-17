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
- Regular variation API: closure properties, uniform convergence theorem and Potter bounds for
  monotone functions.

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
