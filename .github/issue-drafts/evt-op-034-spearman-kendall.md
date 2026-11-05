Title: EVT-OP-034: Sharp upper bound of Spearman's ρ given Kendall's τ for extreme-value copulas
Labels: open-problem, area:multivariate, type:research, difficulty:medium, status:research

**Status in the survey:** OPEN-EXPLICIT for the upper half; the lower bound is proved.

## Source and quote
Mroz and Trutschnig, arXiv:1811.02256, §4:

> We conjecture that in the class of EVCs the upper Hutchinson-Lai is not sharp either. Deriving the best-possible upper inequality will, however, be harder than deriving the sharp lower inequality has been.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
`τ` and `ρ` are the two dependence summaries reported for fitted bivariate copulas, so the exact region is a model-checking diagnostic.

## What the library already has
`pickandsDependence`, `HasSpectralMeasure.convexOn_pickands`, `max_le_pickands`, `pickandsDependence_le_one`.

## What is missing
The copula, Kendall and Spearman definitions, and their integral formulas in terms of the Pickands function.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D12. Survey feasibility estimates are unchecked plans, not results.
