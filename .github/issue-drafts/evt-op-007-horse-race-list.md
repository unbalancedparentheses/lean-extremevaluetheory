Title: EVT-OP-007: The Bücher–Zhou list: rates, tests and second-order relations for block maxima
Labels: open-problem, area:statistics, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT; one item partly resolved. This is a list, and may be split when work starts.

## Source and quote
Bücher and Zhou, Stat. Sci. 36 (2021), §6:

> In case the BM method yields to faster attainable rates of convergence than the POT approach (Section 2.1): are the obtained rates optimal?

The same list:

> Derive a test for which approach is preferably for a given data set ($H_0:\rho_{BM}\le\rho_{POT}$, or similar).

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Annual maxima versus peaks over threshold is the central methodological choice in hydrology.

## What the library already has
Second-order regular variation for `ρ ≤ 0`, both domain-of-attraction characterizations, block-maxima empirical c.d.f. convergence, Hill normality with bias `λ/(1-ρ)`, GEV and GPD likelihood.

## What is missing
The Drees–de Haan–Li (2003) relation between `ρ_BM` and `ρ_POT` (estimated as medium: it tells users when block maxima have the faster optimal rate), any block-maxima estimator CLT, and the optimality, test and comparison items.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C7. Survey feasibility estimates are unchecked plans, not results.
