Title: The logistic law is in the Gumbel domain
Labels: area:classical, type:proof, difficulty:small, good first issue, status:ready

## Context
`DomainOfAttraction/` has the exponential, Gumbel, Pareto and power laws as named examples. The logistic law `F(x) = (1 + e^{-x})⁻¹` is not there, and is a good first definition of a law: its tail is explicit, and `n (1 - F(x + log n)) → e^{-x}` directly.

## Task
In `DomainOfAttraction/GEVDomain.lean`:

1. Define `logisticCDF : CumulativeDistributionFunction` with `toFun x := (1 + exp (-x))⁻¹`, following `standardExponentialCDF`.
2. Prove `isInMDAGumbel_logisticCDF : logisticCDF.IsInMDAGumbel` with `isInMDAGumbel_of_tendsto_mul` and `a n = 1`, `b n = log n`. For `n > 0`, `n (1 - F(x + log n)) = e^{-x} / (1 + e^{-x} / n)`.
3. Prove the corollary `isInMDAGEV_logisticCDF : logisticCDF.IsInMDAGEV 0`.

## Acceptance criteria
- [ ] The definition and two theorems, with docstrings; add them to Main results.
- [ ] The docstring cites the textbook you checked, or says plainly that this is a direct computation.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `standardExponentialCDF`, `isInMDAGumbel_of_tendsto_mul`: `DomainOfAttraction/Gumbel.lean`.
- `IsInMDAGumbel.isInMDAGEV`: `DomainOfAttraction/GEVDomain.lean`.
