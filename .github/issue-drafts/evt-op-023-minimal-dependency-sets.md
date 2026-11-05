Title: EVT-OP-023: Minimal dependency sets with prescribed extremal coefficients
Labels: open-problem, area:multivariate, type:research, difficulty:medium, status:research

**Status in the survey:** OPEN-EXPLICIT. The survey's bivariate answer is marked as an unchecked argument.

## Source and quote
Strokorb and Schlather, arXiv:1205.1315, §4:

> It is an open problem and it would be interesting to know whether there exist also minimal dependency sets and if they would help to better understand the classification of all dependency structures.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Sharp upper bounds on joint exceedance probabilities given extremal coefficients come from the maximal set; sharp lower bounds would come from minimal ones.

## What the library already has
`pickandsDependence`, `HasSpectralMeasure.convexOn_pickands`, `max_le_pickands`, `pickandsDependence_le_one`, `exists_isSimpleMaxStable_pickands`, `extremalCoefficient`, `IsSimpleMaxStable.existsUnique_hasSpectralMeasure`.

## What is missing
That every convex `A` between the bounds is a Pickands function (or the explicit discrete spectral measures), the dependency-set dictionary, and compactness of spectral measures for the Zorn argument.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D2. Survey feasibility estimates are unchecked plans, not results.
