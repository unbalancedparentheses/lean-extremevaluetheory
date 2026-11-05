Title: Unbiasedness of the sample probability-weighted moment b_1
Labels: area:statistics, type:proof, difficulty:medium, good first issue, status:ready

## Context
`samplePWM` is called the unbiased sample PWM, but its unbiasedness is not proved: the Scope section of `Statistics/LMomentsEstimators.lean` says so and the roadmap lists it (A.2). The case `r = 1` is elementary and, since the weight counts observations `≤ x_i`, it needs no continuity: ties are fine because `cdf μ x = μ(-∞, x]`. It needs `n ≥ 2`, as the weight divides by `n - 1`.

## Task
Prove in `Statistics/LMomentsEstimators.lean`:

```lean
theorem integral_samplePWM_one {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hm : ∀ i, Measurable (X i)) (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hint : Integrable (fun x ↦ x) μ) {n : ℕ} (hn : 2 ≤ n) :
    ∫ ω, samplePWM (fun i ↦ X i ω) n 1 ∂P = pwm μ 1
```

Plan:

1. For independent `X, Y` with law `μ`, `∫ X * (if Y ≤ X then 1 else 0) ∂P = pwm μ 1`. Move to `μ.prod μ` with `indepFun_iff_map_prod_eq_prod_map_map` and `integral_map`, then apply `integral_prod`. The inner integral is `cdf μ x`.
2. Pointwise, `samplePWM x n 1 = (n (n-1))⁻¹ ∑ᵢ ∑_{j ≠ i} xᵢ 1{xⱼ ≤ xᵢ}`, using `Finset.add_sum_erase` to split off `j = i`, which accounts for the `- 1` in the weight.
3. Integrate term by term (`integral_finset_sum`) and count the `n (n-1)` terms.

This plan has been checked with a complete scratch proof of about 100 lines, using only the standard axioms.

Optional follow-up, a separate pull request: general `r`, with `n > r`. The weight counts ordered `r`-tuples of distinct indices other than `i` with `xⱼ ≤ xᵢ`.

## Acceptance criteria
- [ ] `integral_samplePWM_one`, with a docstring citing Landwehr–Matalas–Wallis (1979) or Hosking (1990).
- [ ] The Scope section of the module docstring says `r = 1` is done and general `r` is not.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `pwm`, `cdf_eq_real`: `Statistics/LMoments.lean`, Mathlib.
- `countLE`, `pwmWeight`, `samplePWM`: `Statistics/LMomentsEstimators.lean`.
- `iIndepFun.indepFun` gives the pairwise independence.
