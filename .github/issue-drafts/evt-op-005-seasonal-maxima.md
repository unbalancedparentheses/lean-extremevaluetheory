Title: EVT-OP-005: Annual maxima under within-season non-stationarity
Labels: open-problem, area:classical, type:research, difficulty:medium, status:research

**Status in the survey:** OPEN-EXPLICIT for the dependent case; the iid theorem is Stein's.

## Source and quote
Bücher and Zanger, arXiv:2110.15576, §4, reporting Stein, Biometrika 104 (2017):

> In the case of serially independent observations, the limiting distribution was found to be GEV again, despite with an unexpected shape parameter; see Theorem 1. Extensions to serial dependence were not worked out explicitly, but it was conjectured that similar phenomena arise.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Climate attribution and heat-wave studies fit the GEV to annual maxima and interpret the shape. Seasonal non-stationarity changes the shape systematically, so the fitted shape is not the daily tail shape.

## What the library already has
GEV and max-stability, the Weibull-domain characterization `isInMDAWeibull_iff`, Leadbetter's theorem `tendsto_measureReal_partialMax_le_exp`, m-dependence and α-mixing to the block condition.

## What is missing
Maxima of triangular arrays that are not identically distributed, Stein's endpoint-variation computation, and a non-stationary version of the Leadbetter machinery.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C5. Survey feasibility estimates are unchecked plans, not results.
