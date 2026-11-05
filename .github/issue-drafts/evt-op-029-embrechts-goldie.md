Title: EVT-OP-029: Embrechts–Goldie conjectures on convolution roots
Labels: open-problem, area:heavy-tails, type:research, difficulty:medium, status:research

**Status in the survey:** RESOLVED, negatively: a verification target complementing `IsSubexponential.of_convPow`.

## Source and quote
Watanabe, Ann. Probab. 47 (2019), arXiv:1511.01246:

> However, Shimura and Watanabe [ 16 ] disproved Conjecture I for every $\gamma\geq 0$ . On the other hand, Conjecture II was unsolved for over thirty years. In this paper, we disprove Conjecture II for every $\gamma>0$ .

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Proving that the long-tailed class is not closed under convolution roots would show subexponentiality is the right hypothesis: a minimality result in the style of `Minimality/`.

## What the library already has
`IsSubexponential.of_convPow`, the positive `γ = 0` subexponential case.

## What is missing
The counterexample. Estimated as medium for `γ = 0` and the long-tailed class, hard for `𝒮(γ)`, `γ > 0`.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D8. Survey feasibility estimates are unchecked plans, not results.
