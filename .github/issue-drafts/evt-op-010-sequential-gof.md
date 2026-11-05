Title: EVT-OP-010: Threshold selection by sequential goodness-of-fit tests: error-rate control
Labels: open-problem, area:statistics, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT, essentially. The survey marks it as off-mission for this library.

## Source and quote
Belzile and Davison (2026), arXiv:2606.28540, §8.1.1:

> these rely on independence of the null $p$-values ... The procedures described above do not provide independent null $p$-values, so the proofs of their properties fail.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Automated threshold choice for many series (`eva::gpdSeqTests`).

## What the library already has
GPD likelihood and Pickands–Balkema–de Haan.

## What is missing
Goodness-of-fit statistics, multiple testing, and the dependence of p-values.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C10. Survey feasibility estimates are unchecked plans, not results.
