Title: EVT-OP-025: Identifying totally skewed 1-stable laws from weighted sums
Labels: open-problem, area:heavy-tails, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT; no follow-up addressing `α = 1` was found.

## Source and quote
Jacobsen, Mikosch, Rosiński and Samorodnitsky, Ann. Appl. Probab. 19 (2009), arXiv:0712.0576, §6:

> What happens in the case α = 1 is still unclear.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
It is the converse Breiman or linear-filter problem: does the tail behaviour of an aggregate force it on the components?

## What the library already has
`tendsto_map_convPow_sub_of_isRegularlyVarying_one'`, `domainOfAttraction_isStableIndex_iff`, `IsStable.existsUnique_isStableIndex`, finite moving-average tails, Breiman, `IsSubexponential.of_convPow`.

## What is missing
Laplace transforms of one-sided stable laws, the cancellation theorem, and Mellin transforms. A reduction to a functional equation is estimated as medium.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D4. Survey feasibility estimates are unchecked plans, not results.
