## What this does

<!-- One or two sentences. Link the issue: "Closes #123". -->

## Source

<!-- The book or paper and theorem number each new statement formalizes, or "not applicable". -->

**How the statement differs from the source:** <!-- narrower hypotheses, different form, or "it does not". -->

## Checklist

- [ ] `lake build`
- [ ] `lake build Test`
- [ ] `python3 scripts/check_source.py`
- [ ] No `sorry`; only the standard axioms
- [ ] Docstrings cite the source and state what is proved, no more
- [ ] Searched the library and Mathlib before adding a definition or lemma
- [ ] New files are imported from `ExtremeValueTheory.lean` or `Test.lean`
- [ ] Renamed declarations leave a deprecated alias, and blueprint `\lean{}` names still resolve
- [ ] My name is on the `Copyright` and `Authors:` lines of my files, and in the README's Acknowledgements (first pull request)
