# Proof status

**Fisher–Tippett–Gnedenko is proved.**
`CumulativeDistributionFunction.IsExtremeValueDistr.classification` (`SelfSimilarCDF.lean`)
depends only on `propext`, `Classical.choice` and `Quot.sound`, and the compiled modules pass
`leanchecker` replay. **Karamata's tail-integral theorem**
(`ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div`) and the Potter bounds are
proved with the same axioms.

All 95 `sorry`s inherited from ExtremeValueProject are filled. The last 8 sat on statements that
were false or mistyped upstream; they have been corrected (see below) and proved. The
counterexample lemmas documenting why the upstream versions fail are kept next to them.

## Statements corrected from upstream

These were false as stated and are now restated and proved:

- `tendsto_of_limitcondition`, `limitCondition_iff_log`, `limitCondition_iff`,
  `limitCondition_iff_inv` (`ExtremeValueDistribution`): added the hypothesis that `φs n` is
  eventually nonnegative (counterexamples `not_limitCondition_iff_log`, `not_limitCondition_iff`,
  `not_limitCondition_iff_inv`).
- `solve_Q` (`ClassificationCalculation`): added `hγ : γ = deriv (deriv Q) 0`
  (counterexample `not_solve_Q`).
- `solve_E` (`ClassificationCalculation`): `γ = H''(0) / c` with `H = E ∘ exp`, conclusion
  `E σ = c * (σ ^ γ - 1) / γ` (or `c * log σ` if `γ = 0`) for `σ > 0` only, `hc` made explicit
  (counterexample `not_solve_E`). Blueprint statement fixed accordingly.
- `exists_interval_measure_inter_gt_mul_measure` (`OneParameterAffine`): conclusion
  `(interior J).Nonempty` instead of `(interior A).Nonempty`; proved via Lebesgue density points.
- `continuous_parameter_ev_limit_relation` (`SelfSimilarCDF`): hypothesis is
  `((As n • F) x) ^ n → G x` instead of `(As n • F) x → G x`.
- `AffineMap.leftOrdContinuous`, `AffineMap.rightOrdContinuous`: need a nonnegative slope.
- `AffineMap.leftOrdContinuous_extend`, `rightOrdContinuous_extend`: false for negative slopes;
  replaced by `AffineIncrEquiv.leftOrdContinuous_extend` / `rightOrdContinuous_extend`.
- `CumulativeDistributionFunction.comp_rightOrdContinuous`: needs left-continuity of `φ` at `1`.
- `weibull_scale_pos_of_selfSimilar_index_neg'`: the Weibull scale exponent is `α`, not `-α`.

Porting changes for Mathlib v4.35 (order continuity over nonempty sets, `Multiplicative ℝ`) are
described in the history of the first commit.
