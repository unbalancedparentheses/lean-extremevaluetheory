Title: EVT-OP-024: Geometry of the tail-correlation polytope
Labels: open-problem, area:multivariate, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT; question (G) at `n = 7` is probably answerable from the cut-polytope literature, which the survey did not check.

## Source and quote
Fiebig, Strokorb and Schlather, Extremes 20 (2017), arXiv:1405.6876, §8:

> (G) Are there non-hypermetric facets at $v_{1}$ for $n\geq 7\,$ ? Are there hypermetric facets at $v_{1}$ with $\sum_{i=1}^{n}b_{i}=0$ for $n\geq 7\,$ ?

The same section:

> (F) For which values of $n$ does $\text{TCF}_{n}(v_{0},v_{1})\subset\text{PSD}_{n}$ hold?

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
It decides which matrices of tail correlations a spatial analyst can fit. Realizability itself is settled (NP-complete); only the facet geometry is open.

## What the library already has
Extremal coefficients and `two_sub_extremalCoefficient_mem_Icc`, `hasUpperTailDependence_pickands`, simple max-stable vectors in finite dimension. Nothing on polytopes.

## What is missing
The tail-correlation characterization and polytope machinery. A single rational certificate at `n = 7` is estimated as medium.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D3. Survey feasibility estimates are unchecked plans, not results.
