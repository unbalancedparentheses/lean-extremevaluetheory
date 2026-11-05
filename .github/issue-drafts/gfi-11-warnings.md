Title: Remove deprecated names and unused simp arguments
Labels: area:classical, type:refactor, difficulty:small, good first issue, status:ready

## Context
`lake build` prints warnings that are simple to fix, and each one hides new warnings from view. The line numbers below are from commit `99fe16a`.

## Task
Fix these warnings; Lean's message names the replacement:

- `DomainOfAttraction/GEVDomain.lean`, lines 42, 47 and 51: `dif_pos` becomes `dite_eq_left` and `dif_neg` becomes `dite_eq_right` (checked to work as drop-in replacements).
- `Statistics/ExtremalIndexEstimatorsIid.lean`, lines 65, 74, 83 and 87: `Set.mem_setOf_eq`, `if_neg`, `if_pos`.
- `ExtremeValueDistribution.lean` line 41 and `OrderContinuity.lean` line 37: an unused `simp` argument.

Leave warnings about unused hypotheses and `module` imports alone: renaming a hypothesis changes a public signature, and the module warnings come from Mathlib's new module system.

## Acceptance criteria
- [ ] `lake build` no longer prints these warnings, and no statement changes.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- Check one file with `lake env lean ExtremeValueTheory/DomainOfAttraction/GEVDomain.lean`.
