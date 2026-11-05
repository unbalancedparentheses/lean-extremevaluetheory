Title: Bridge: countLE and exceedCount are complementary
Labels: area:statistics, type:proof, difficulty:small, good first issue, status:ready

## Context
Two files count the observations on either side of a level: `countLE x n t` (`x : ℕ → ℝ`, observations `≤ t`) in `Statistics/LMomentsEstimators.lean`, and `exceedCount x a` (`x : Fin n → ℝ`, observations `> a`) in `Statistics/OrderStatistics.lean`. Nothing relates them. This is separate from the `tailCount` bridge of pull request #4 and does not depend on it.

## Task
Prove in `Statistics/LMomentsEstimators.lean`:

```lean
theorem countLE_add_exceedCount (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    countLE x n t + exceedCount (fun i : Fin n ↦ x i) t = n
```

and the corollary `empCDF x n t = 1 - exceedCount (fun i : Fin n ↦ x i) t / n` for `0 < n`.

Rewrite `exceedCount` as a filter over `Finset.range n` (`Finset.card_filter` and `Finset.sum_range`), then use `Finset.card_filter_add_card_filter_not`. If `OrderStatistics` is not yet imported there, add the import.

## Acceptance criteria
- [ ] The theorem and the corollary, with docstrings.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `countLE`, `empCDF`: `Statistics/LMomentsEstimators.lean`. `exceedCount`: `Statistics/OrderStatistics.lean`.
