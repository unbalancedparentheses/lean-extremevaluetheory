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

Work in progress. The Fisher–Tippett–Gnedenko development is imported from
[ExtremeValueProject](https://github.com/kkytola/ExtremeValueProject) and ported to Lean v4.35.0;
its remaining `sorry`s are being filled. See [`TRIAGE.md`](TRIAGE.md) for the open proof
obligations.

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
