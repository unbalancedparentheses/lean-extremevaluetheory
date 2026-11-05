Title: The GPD return level is the level exceeded once in N observations
Labels: area:statistics, type:proof, difficulty:small, good first issue, status:ready

## Context
`gevFun_returnLevel` shows that the GEV return level has the defining property `H_ξ(z_m) = 1 - 1/m`. The peaks-over-threshold return level `gpdReturnLevel` in `Statistics/ReturnLevelNormality.lean` has normality and interval theorems, but its defining property is not stated, and `Test/` does not evaluate it.

## Task
In `Statistics/ReturnLevelNormality.lean`, prove:

```lean
theorem gpdSurvivalAll_gpdReturnLevel {ξ σ ζ N : ℝ} (hσ : 0 < σ) (hNζ : 0 < N * ζ) (u : ℝ) :
    gpdSurvivalAll ξ σ (gpdReturnLevel u ξ σ ζ N - u) = (N * ζ)⁻¹
```

So an observation exceeds `x_N` with probability `ζ · (Nζ)⁻¹ = 1/N`. Split on `ξ = 0`, using `gpdReturnLevel_zero` and `gpdReturnLevel_of_ne`.

In `Test/KnownAnswers/Statistics.lean`, add `gpdReturnLevel u 0 1 ζ N = u + log (N * ζ)` and, for `ξ = 1`, `gpdReturnLevel u 1 σ (2 / N) N = u + σ` with `N ≠ 0`.

## Acceptance criteria
- [ ] `gpdSurvivalAll_gpdReturnLevel`, with a docstring citing Coles (2001), §4.3.3.
- [ ] The two known-answer tests.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `gevFun_returnLevel` in `Statistics/ExtremeQuantile.lean` is the model. `gpdSurvivalAll`: `PeaksOverThreshold/Frechet.lean`.
