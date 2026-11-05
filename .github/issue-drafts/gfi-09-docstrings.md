Title: Docstrings for fifteen public lemmas
Labels: area:docs, type:docs, difficulty:small, good first issue, status:ready

## Context
`docs/DESIGN.md` says every public declaration has a docstring. These do not, and they are simple enough to describe after reading the statement. The proofs do not change.

## Task
Add a one-line docstring, saying in mathematics what the lemma states, to:

- `RegularVariation/SecondOrder.lean`: `boxCox_zero`, `boxCox_of_ne`, `boxCox_exp`, `boxCox_pos_of_one_lt`, and `eventually_ne_zero`.
- `Statistics/OrderStatistics.lean`: `orderStat_of_lt`, `orderStat_of_le`, `exceedCount_eq_sum`, `measurable_exceedCount`.
- `GEV/Moments.lean`: `integrable_id_smul`, `measurable_gevTransform`.
- `MaxStable/Basic.lean`: `smul_le_smul_of_le`, `measureReal_Iic_pos`.
- `Statistics/BlockMaxima.lean`: `blockMax_le_iff`.
- `DomainOfAttraction/VonMises.lean`: `powerCDF_apply_of_mem_Icc`.

## Acceptance criteria
- [ ] All fifteen have docstrings, and the docstrings say no more than the statements.
- [ ] No statement or proof changes.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `docs/DESIGN.md`. Nearby docstrings in the same files show the style, e.g. `boxCox_exp_nonneg_le`.
