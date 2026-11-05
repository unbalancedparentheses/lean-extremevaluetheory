Title: Known answers for the sample probability-weighted moments
Labels: area:statistics, type:proof, difficulty:small, good first issue, status:ready

## Context
`samplePWM`, `sampleLMoment1`, `sampleLMoment2`, `sampleLMoment3` and `sampleLSkewness` in `Statistics/LMomentsEstimators.lean` have consistency theorems (`ae_tendsto_samplePWM`), but no test in `Test/` evaluates them on data, so an off-by-one in the rank or the weight `pwmWeight` would go unnoticed.

## Task
On the sample `x₀, x₁, x₂ = 1, 2, 3`, as `fun k : ℕ ↦ (k : ℝ) + 1`, prove in `Test/KnownAnswers/Statistics.lean`:

- `samplePWM x 3 0 = 2`, `samplePWM x 3 1 = 4 / 3`, `samplePWM x 3 2 = 1`;
- `sampleLMoment2 x 3 = 2 / 3`, `sampleLMoment3 x 3 = 0` and `sampleLSkewness x 3 = 0` (a symmetric sample).

Hand check of `b₁`: `(1/3)(1·0/2 + 2·1/2 + 3·2/2) = 4/3`.

Suggested helper, `private` as test helpers are: `countLE x 3 (x i) = i + 1` for `i < 3`, by showing that the filtered set is `Finset.range (i + 1)`. After that, `simp only` with `samplePWM`, `pwmWeight`, `Finset.sum_range_succ` and `Finset.prod_range_succ`, then `norm_num`, should finish each value.

## Acceptance criteria
- [ ] The six values are `theorem test_…` with docstrings citing Hosking (1990), (2.4).
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `ExtremeValueTheory/Statistics/LMomentsEstimators.lean`: the definitions, with Hosking's formula in the module docstring.
- `test_lSkewness_exponential` in `Test/KnownAnswers/Statistics.lean` for the style; `docs/DESIGN.md`, Test conventions.
