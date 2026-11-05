Title: Bridges: the exponential, uniform and Pareto laws as generalized Pareto laws
Labels: area:pot, type:proof, difficulty:small, good first issue, status:ready

## Context
`docs/DESIGN.md` asks that each concrete law have its bridge lemma once, so users never redo the computation. `paretoCDF` has one (`paretoCDF_apply_eq_measureReal_Iic`), but `standardExponentialCDF` has none to Mathlib's `expMeasure 1`. `gpdCDF` is related to the named c.d.f.s only through numeric tests such as `test_gpdCDF_uniform`.

## Task
Create `ExtremeValueTheory/Statistics/GPDSpecialCases.lean`, importing `ExtremeValueTheory.Statistics.GPDLikelihood` and `ExtremeValueTheory.DomainOfAttraction.VonMises`, and register it in `ExtremeValueTheory.lean`. Prove:

```lean
theorem standardExponentialCDF_apply_eq_measureReal_Iic (x : ℝ) :
    standardExponentialCDF x = (expMeasure 1).real (Set.Iic x)
theorem gpdCDF_zero_one (x : ℝ) : gpdCDF 0 1 x = standardExponentialCDF x
theorem gpdCDF_neg_one_one (x : ℝ) : gpdCDF (-1) 1 x = powerCDF one_pos x
theorem gpdCDF_inv_inv {α : ℝ} (hα : 0 < α) (x : ℝ) :
    gpdCDF (1 / α) (1 / α) x = paretoCDF hα (x + 1)
```

Each is a case split on the position of `x`, using the evaluation lemmas of the named c.d.f.s and `simp [gpdCDF, gpdSurvivalAll, …]`. The first starts from Mathlib's `cdf_expMeasure_eq` and `cdf_eq_real`.

## Acceptance criteria
- [ ] The four theorems, in a new file with your name in the header and a module docstring with Main results and References.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `gpdCDF`: `Statistics/GPDLikelihood.lean`. `gpdSurvivalAll`: `PeaksOverThreshold/Balkema.lean`.
- `standardExponentialCDF_apply_of_nonneg`, `standardExponentialCDF_apply_of_nonpos`: `DomainOfAttraction/Gumbel.lean`.
- `powerCDF_apply_of_mem_Icc`, `powerCDF_apply_of_nonpos`, `powerCDF_apply_of_one_le`, `paretoCDF_apply_of_one_le`, `paretoCDF_apply_of_le_one`: `DomainOfAttraction/VonMises.lean`.
