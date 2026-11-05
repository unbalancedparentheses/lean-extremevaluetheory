Title: EVT-OP-011: Hsing's null-variance conjecture for linear models
Labels: open-problem, area:dependence, type:research, difficulty:hard, status:research

**Status in the survey:** RESOLVED by Buriticá–Wintenberger, to be verified: a verification target. It also supports EVT-OP-003.

## Source and quote
Buriticá and Wintenberger, arXiv:2212.13521, abstract:

> Regarding linear models, we prove that the asymptotic variance of classical index cluster-based estimators is null as first conjectured in [Hsing 1993].

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
It explains why bootstrap intervals for `θ` collapse on ARMA-type data.

## What the library already has
Finite and infinite moving-average spectral tail processes, with `θ = max ψ^α / Σ ψ^α`.

## What is missing
The ℓᵖ-block functionals and the estimator CLT. The deterministic core, that the spectral cluster is non-random up to shift so the variance functional vanishes, is estimated as medium.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C11. Survey feasibility estimates are unchecked plans, not results.
