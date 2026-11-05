Title: EVT-OP-026: Arithmetic Kesten–Goldie: when is the log-periodic factor constant?
Labels: open-problem, area:dependence, type:research, difficulty:hard, status:research

**Status in the survey:** OPEN-EXPLICIT, phrased as "would be interesting". No follow-up found.

## Source and quote
Kevei, J. Appl. Probab. 54 (2017), arXiv:1609.07339, §2.1:

> It would be interesting to know what conditions on $(A,B)$ imply that $q$ is constant, or $q$ is continuous, but these questions do not seem to be tractable with our methods.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
GARCH tail-index estimation assumes `c x^{-κ}`. In lattice models the tail need not be regularly varying, so Hill and Weissman are not consistent in the usual sense.

## What the library already has
`SRE.exists_integral_abs_rpow_eq_one`, `SRE.kesten_exponent_unique`, `SRE.lintegral_enorm_rpow_stationaryLaw_lt_top`, and `tendstoInMeasure_hill`.

## What is missing
The implicit renewal theorem and the Mellin description of `q`. An explicit stationary example whose tail is not regularly varying is estimated as easy; the survey's `A ∈ {0, 2}` example falls outside the library's hypothesis `E log |A| < 0` as stated (see its runners-up note).

## Pointers
`docs/OPEN_PROBLEMS_SURVEY2.md`, D5. Survey feasibility estimates are unchecked plans, not results.
