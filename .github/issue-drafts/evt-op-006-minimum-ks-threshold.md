Title: EVT-OP-006: Minimum Kolmogorov–Smirnov threshold selection
Labels: open-problem, area:statistics, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT conjecture, plus an unproved hypothesis.

## Source and quote
Drees, Janßen, Resnick and Wang, SIAM J. Math. Data Sci. 2 (2020), arXiv:1811.06433, introducing eq. (11):

> we conjecture that $(k_n^*/n, n^{1/2}(\hat\alpha_{n,k_n^*}-\alpha))\to(T^*, \ldots)$ weakly.

The same paper, Corollary 2:

> If $t\mapsto\sup_{0<s\le1}|Z_1(s,t)|$ has a unique point of minimum $T$ a.s., then ...

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
The Clauset–Shalizi–Newman `poweRlaw` method is used across network science and the Danielsson method in finance. For exact Pareto data the procedure selects thresholds that are too high and has a non-normal limit, so its usual intervals are not valid.

## What the library already has
Hill consistency and normality, the exact-Pareto iff `tendstoInMeasure_hill_pareto_iff`, the Rényi representation, the uniform tail empirical process `tendstoInDistribution_tailEmpiricalPath`, and the Skorokhod space.

## What is missing
Weighted approximations at the `√n` scale uniformly in `t`, argmin continuous-mapping theorems, and Hill at a random `k`. A weaker warning, that `k*/n` does not tend to 0 for exact Pareto, is estimated as medium.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C6. Survey feasibility estimates are unchecked plans, not results.
