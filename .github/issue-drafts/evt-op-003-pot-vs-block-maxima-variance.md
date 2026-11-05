Title: EVT-OP-003: Does peaks over threshold always have smaller variance than block maxima?
Labels: open-problem, area:statistics, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT; no resolution found. The survey has a possible negative lead through Buriticá–Wintenberger, by an unchecked hand calculation.

## Source and quote
Cissokho and Kulik, arXiv:2005.11378, §5.3 "Open questions":

> In view of the behaviour of $\widetilde{\vartheta}_{n,1}(u_n)$ and $\widetilde{\vartheta}_{n,1}(c_{r_n})$, it would be interesting to know if (whenever possible) the PoT method always gives a smaller variance than the block maxima ones.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Hydrology and finance users choose between sliding block maxima (`exdex::spm`) and blocks, runs or intervals estimators (`extRemes`, `evd`). Which has the smaller standard error is a daily decision.

## What the library already has
Spectral tail processes with closed forms for finite and infinite moving averages, AR(1) and ARMAX; `ϑ = P(sup_{k≥1}|Y_k| ≤ 1)`; consistency of the blocks and runs estimators for their population targets.

## What is missing
CLTs for the cluster estimators (far off), the Berghaus–Bücher variance formula, and `Σ_j P(Y_j>1)` as a functional of the tail process. Taking the published variance formulas as definitions would give a conditional result at medium difficulty.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C1. Survey feasibility estimates are unchecked plans, not results.
