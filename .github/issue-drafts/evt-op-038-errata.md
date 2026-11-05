Title: EVT-OP-038: Errata in standard texts, as formal warnings
Labels: open-problem, area:classical, type:research, difficulty:small, status:research

**Status in the survey:** Not an open problem: published corrections, which the library's statements should respect.

## Source and quote
De Haan and Ferreira (2006), official errata, p. 213, Remark 6.1.8:

> Relation (6.1.15*) does not necessarily hold for Borel sets A not of the form (6.1.16)

Charras-Garrido and Lezaud (2013), corrected 2017:

> Two mistakes appears in Proposition 2.9, one is due to a typographical error in Beirlant et al. (2004).

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
These guard against common misuses. The first limits `P(Y ∈ A) = exp(-ν(A))` to complements of lower orthants; the second concerns the Gumbel von Mises condition, which must read `(1/r)' → 0`.

## What the library already has
The max-stable and exponent-measure API, and `isInMDAGumbel_of_vonMises`.

## What is missing
Checking that the library states exactly these forms, and an easy formal counterexample for the first.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D16. Survey feasibility estimates are unchecked plans, not results.
