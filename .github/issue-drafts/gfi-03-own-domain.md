Title: The Fréchet and Weibull laws are in their own domains of attraction
Labels: area:classical, type:proof, difficulty:small, good first issue, status:ready

## Context
`isInMDAGumbel_standardGumbelCDF` says the Gumbel law is in its own domain. The Fréchet and Weibull analogues are missing, although the max-stability they need is already proved explicitly (`standardFrechetCDF_pow_apply_rpow_mul`, `standardWeibullCDF_pow_apply_rpow_mul`).

## Task
Prove in `DomainOfAttraction/GEVDomain.lean`, adding `import ExtremeValueTheory.GEV.MaxStable`:

```lean
theorem isInMDAFrechet_standardFrechetCDF {α : ℝ} (hα : 0 < α) :
    (standardFrechetCDF hα).IsInMDAFrechet hα
theorem isInMDAWeibull_standardWeibullCDF {α : ℝ} (hα : 0 < α) :
    (standardWeibullCDF hα).IsInMDAWeibull hα
```

Take `As n = (AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹` with `a n = max (n : ℝ) 1 ^ (1 / α)` (`-1 / α` for Weibull), since `n = 0` must be avoided. The sequence is eventually constant: use `tendsto_const_nhds.congr'` and `eventually_ge_atTop 1`.

Then add the two `isInMDAGEV` corollaries with `IsInMDAFrechet.isInMDAGEV` and `IsInMDAWeibull.isInMDAGEV`.

## Acceptance criteria
- [ ] The two theorems and two corollaries, listed under Main results in the module docstring.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `isInMDAGumbel_standardGumbelCDF` in `DomainOfAttraction/Gumbel.lean`; `IsInMDAFrechet` in `DomainOfAttraction/Frechet.lean`; `IsInMDAWeibull` in `DomainOfAttraction/Weibull.lean`.
- `ExtremeValueTheory/GEV/MaxStable.lean`.
