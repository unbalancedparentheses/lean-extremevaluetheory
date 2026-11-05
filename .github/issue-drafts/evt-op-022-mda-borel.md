Title: EVT-OP-022: Is the maximum domain of attraction a Borel set?
Labels: open-problem, area:classical, type:research, difficulty:medium, status:research

**Status in the survey:** OPEN-EXPLICIT; no citing paper addressing it was found. The survey's plan for `k = 1` is marked as an unchecked argument.

## Source and quote
Leonetti and Khorrami Chokami, Electron. Commun. Probab. 27 (2022), arXiv:2203.15761v2, §4:

> We leave as open question for the interested reader to establish the topological complexity of $\mathsf{D}$ and, in particular, whether it is a Borel set.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
It answers a stated question, and an exact Borel class would give a precise sense in which "is my data in a domain of attraction?" cannot be tested, complementing `Minimality/`.

## What the library already has
`isInMDAFrechet_iff`, `isInMDAWeibull_iff`, `isInMDAGumbel_iff`, `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile`, and the multivariate domain of attraction.

## What is missing
Measurability of `μ ↦ U_μ(q)`, the reduction of the limit from `ℝ` to `ℚ` for monotone left-continuous functions, and "convergence of a ratio of increments to a nonconstant limit implies extended regular variation". Estimated easy to medium for `k = 1`, hard for the exact class.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D1. Survey feasibility estimates are unchecked plans, not results.
