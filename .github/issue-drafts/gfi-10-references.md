Title: Add References sections to eight module docstrings
Labels: area:docs, type:docs, difficulty:small, good first issue, status:ready

## Context
`docs/DESIGN.md` says every file has a module docstring with Main results and References. These eight files cite sources by a short tag such as `[BDM16]` or `[LLR, Theorem 1.7.13]`, or by name only, and never expand the citation.

## Task
Add a `## References` section with full citations to the module docstrings of the following files, all under `ExtremeValueTheory/Dependence/` unless noted:

- `Mixing.lean`: tags `[BS09]`, `[KS20]`, `[LLR]`.
- `BetaMixing.lean`: same sources as `Mixing.lean`.
- `StrictExtremalIndex.lean`, `StrictExtremalIndexAll.lean`: `[LLR]`.
- `SREPathwise.lean`: `[BDM16]`, Brandt 1986, Bougerol–Picard 1992.
- `SREExponent.lean`: `[BDM16]`, `[EKM]`.
- `StationaryWindows.lean`: find a suitable source, or state that it is a direct proof.
- `ExtremeValueTheory/DomainOfAttraction/OfMeasure.lean`: the source of Gnedenko's characterizations, e.g. `[EKM]`.

The tags stand for Basrak–Segers (2009), Kulik–Soulier (2020), Leadbetter–Lindgren–Rootzén (1983), Buraczewski–Damek–Mikosch (2016) and Embrechts–Klüppelberg–Mikosch (1997). Check each against the publication, and see `Statistics/LMomentsEstimators.lean` for the format.

## Acceptance criteria
- [ ] Eight files have a References section, with every tag used in the file expanded.
- [ ] No Lean code changes.
- [ ] `lake build`, `lake build Test` and `python3 scripts/check_source.py` pass.

## Pointers
- `ExtremeValueTheory/DomainOfAttraction/GEVDomain.lean` has a short example of the section.
