Title: EVT-OP-008: Adaptive choice of the level for estimating the second-order parameter
Labels: open-problem, area:statistics, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT, older source; Belzile and Davison (2026) still call the estimates too noisy.

## Source and quote
Beirlant, Caeiro and Gomes, REVSTAT 10 (2012), §3.1.3:

> Such a crucial property can potentially be achieved if we compute $\hat\rho$ at its optimal level (see Caeiro et al., 2009), but the adaptive choice of such a level is still an open research topic.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Reduced-bias Hill estimators (`evt0`, `tea`) need an estimate of `ρ`, with `(ρ̂ - ρ) log n = o_p(1)`.

## What the library already has
Second-order regular variation, Hill normality with bias, Weissman at `ρ ≤ 0` including the `ρ = 0` cancellation.

## What is missing
The Fraga Alves–Gomes–de Haan estimators, their consistency, and third-order conditions. Consistency at a fixed level is known and estimated as medium; the adaptive rule is probably beyond formal methods for now.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C8. Survey feasibility estimates are unchecked plans, not results.
