Title: Worked example: maxima of the uniform law, end to end
Labels: area:classical, type:docs, difficulty:small, good first issue, status:ready

## Context
The roadmap (D, Usability) asks for worked examples for the standard laws. None exists yet: a reader must piece the path together from `Test/NonVacuity`. The uniform law is the shortest case, because everything is explicit: `n (M_n - 1)` converges to the Weibull law with `α = 1`.

## Task
Create `Test/Examples/Uniform.lean`, in the namespace `Test.Examples.Uniform`, importing `ExtremeValueTheory`, and import it from `Test.lean`. Its module docstring should read as a short tutorial for someone new to the library, and it should contain:

1. `powerCDF one_pos` is the uniform c.d.f.: `powerCDF one_pos x = x` on `[0, 1]` (`powerCDF_apply_of_mem_Icc`).
2. The explicit limit, for `x < 0`:
   ```lean
   Tendsto (fun n : ℕ ↦ powerCDF one_pos (1 + x / n) ^ n) atTop (𝓝 (exp x))
   ```
   using `Real.tendsto_one_add_div_pow_exp`, after noting that `1 + x / n ∈ [0, 1]` eventually.
3. The same fact from the general theory: `isInMDAWeibull_powerCDF one_pos` and `isInMDAGEV_powerCDF one_pos`, with a sentence on what each says.

## Acceptance criteria
- [ ] `Test/Examples/Uniform.lean` builds with `lake build Test` and uses only public statements.
- [ ] A row for worked examples in `Test/README.md`.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `DomainOfAttraction/VonMises.lean` (`powerCDF`), `DomainOfAttraction/GEVDomain.lean`.
- `docs/DESIGN.md`, Test conventions.
