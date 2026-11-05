Title: EVT-OP-017: Explaining the discrepancy between the two indices θ and ϑ
Labels: open-problem, area:dependence, type:research, difficulty:medium, status:research

**Status in the survey:** A motivating question in the source, open-ended; the library's gap formula is one answer.

## Source and quote
Bai, Kulik and Wang, arXiv:2409.17966v2, introduction:

> Second, it is natural to ask for a further explanation on the discrepancy between the two indices.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
`θ` and `ϑ` are what estimators target, so knowing why they differ says which estimator measures what.

## What the library already has
The gap formula `θ = ϑ - η` under the block condition (`Dependence/ThetaGap.lean`), and `logEchoProcess_theta_lt_vartheta`.

## What is missing
The weakest condition for `θ = ϑ` (roadmap, B).

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, §0, question 4. Survey feasibility estimates are unchecked plans, not results.
