# Proof status

**Fisher–Tippett–Gnedenko is proved.**
`CumulativeDistributionFunction.IsExtremeValueDistr.classification` (`SelfSimilarCDF.lean`)
depends only on `propext`, `Classical.choice` and `Quot.sound`, and the compiled modules pass
`leanchecker` replay. **Karamata's tail-integral theorem**
(`ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div`) and the Potter bounds are
proved with the same axioms.

Of the 95 `sorry`s inherited from ExtremeValueProject, 87 are filled. The remaining 8 sit on
statements that are false as written upstream; none is used by `classification`.

| Declaration | File | Problem |
|---|---|---|
| `tendsto_of_limitcondition`, `limitCondition_iff_log` | `ExtremeValueDistribution` | false when `φ n < 0` (`Real.log` ignores sign); counterexample `not_limitCondition_iff_log` |
| `limitCondition_iff`, `limitCondition_iff_inv` | `ExtremeValueDistribution` | false for sign-alternating `φ n`; counterexamples `not_limitCondition_iff`, `not_limitCondition_iff_inv`. All four hold with `φ n` eventually nonnegative |
| `solve_Q` | `ClassificationCalculation` | `γ` unconstrained; counterexample `not_solve_Q`, corrected version `solve_Q_of_gamma_eq` proved |
| `solve_E` | `ClassificationCalculation` | wrong normalisation and domain; counterexample `not_solve_E` |
| `exists_interval_measure_inter_gt_mul_measure` | `OneParameterAffine` | statement corrected (`interior J`, upstream had `interior A`); proof pending (Lebesgue density) |
| `continuous_parameter_ev_limit_relation` | `SelfSimilarCDF` | hypothesis should be about `((As n • F) x) ^ n` |

## Statements corrected from upstream

These were false as stated and are now restated and proved:

- `AffineMap.leftOrdContinuous`, `AffineMap.rightOrdContinuous`: need a nonnegative slope.
- `AffineMap.leftOrdContinuous_extend`, `rightOrdContinuous_extend`: false for negative slopes;
  replaced by `AffineIncrEquiv.leftOrdContinuous_extend` / `rightOrdContinuous_extend`.
- `CumulativeDistributionFunction.comp_rightOrdContinuous`: needs left-continuity of `φ` at `1`.
- `weibull_scale_pos_of_selfSimilar_index_neg'`: the Weibull scale exponent is `α`, not `-α`.

Porting changes for Mathlib v4.35 (order continuity over nonempty sets, `Multiplicative ℝ`) are
described in the history of the first commit.
