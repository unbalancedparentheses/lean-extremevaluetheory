Title: EVT-OP-004: GEV maximum likelihood over the full parameter space
Labels: open-problem, area:statistics, type:research, difficulty:hard, status:research

**Status in the survey:** RESOLVED 2025 by a paper whose publication status is unknown: a verification target, not a research target.

## Source and quote
Carl, Padoan and Rizzelli, arXiv:2506.17448 (2025):

> Notably, even in the independence case, whether the MLE—computed over the full parameter space—is consistent and uniquely maximizes the likelihood has remained an open question. We resolve this question for both independent and dependent data, thereby closing a long-standing gap in the literature.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Annual-maximum analyses fit the GEV with an unconstrained optimizer (`extRemes::fevd`, `ismev`, `scipy`), while the library's theorems assume a compact parameter set. This would remove a standing scope caveat.

## What the library already has
GEV identifiability, strong consistency on compact sets for `ξ > -1` (`ae_tendsto_gevMLE`), a Wald framework covering extended-real values and parameter-dependent supports, and the full 3×3 Fisher information (see the roadmap, A.2).

## What is missing
Joint normality (in progress in draft pull request #6), and global uniqueness: bounds near the truth and control of the likelihood at the boundary as `σ → 0` and `|ξ| → ∞`.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C4. Survey feasibility estimates are unchecked plans, not results.
