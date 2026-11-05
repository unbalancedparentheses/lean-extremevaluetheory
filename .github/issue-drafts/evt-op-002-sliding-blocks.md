Title: EVT-OP-002: Sliding-blocks estimators without β-mixing
Labels: open-problem, area:statistics, type:research, difficulty:medium, status:research

**Status in the survey:** OPEN-EXPLICIT. Whether the result is new for the extremal index is uncertain: Robert, Segers and Ferro (2009) were not checked.

## Source and quote
Cissokho and Kulik, arXiv:2005.11378 (EJS 2021), §5.3:

> For the sliding blocks estimators, obtain consistency under minimal conditions (that is, without relying on $\beta$-mixing).

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
`exdex::spm`, a widely used sliding block maxima estimator, falls here. GARCH-type and Markov models are usually proved α-mixing; β-mixing is harder to establish.

## What the library already has
A Chebyshev framework for disjoint blocks and runs under α-mixing rates: `tendstoInMeasure_blockCount_div`, `variance_sum_ite_mem_le`, and the m-dependent versions.

## What is missing
The variance bound for overlapping block sums, and the passage from indicator functionals to general bounded functionals.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C3. Survey feasibility estimates are unchecked plans, not results.
