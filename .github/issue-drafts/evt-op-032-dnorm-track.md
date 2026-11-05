Title: EVT-OP-032: Is the limit of a D-norm track idempotent?
Labels: open-problem, area:multivariate, type:research, difficulty:small, status:research

**Status in the survey:** OPEN-EXPLICIT; no resolution found. The survey proposes a small counterexample in `d = 2`, unchecked against Falk's 2019 book: check the book first.

## Source and quote
Falk, J. Multivariate Anal. (2015), arXiv:1303.1284, §3:

> But it is an open problem, whether the limit of a track is again idempotent if $\left\|\cdot\right\|_{D^{(i)}}\not=\left\|\cdot\right\|_{\infty}$ for infinitely many $i\in\mathbb{N}$ .

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
It settles a stated question in the D-norm calculus behind multivariate GPD and max-stable modelling.

## What the library already has
`IsSimpleMaxStable`, `maxStableExponent`, `maxStableExponent_eq_pickands`, `extremalCoefficient`, `one_le_extremalCoefficient`, `extremalCoefficient_le_card`, `exists_isSimpleMaxStable_hasSpectralMeasure`.

## What is missing
D-norm products and tracks, monotonicity of tracks, and the limit being a D-norm.

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D10. Survey feasibility estimates are unchecked plans, not results.
