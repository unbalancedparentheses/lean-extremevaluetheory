Title: EVT-OP-001: Block and run length for extremal-index estimators
Labels: open-problem, area:statistics, type:research, difficulty:medium, status:research

**Status in the survey:** OPEN-EXPLICIT; the library already has strong partial results.

## Source and quote
Markovich and Rodionov, *Threshold selection for extremal index estimation*, arXiv:2009.02318, §1:

> The semiparametric maxima estimators (Berghaus and Bücher 2018; Northrop 2015) depend on the block size only. The choice of the latter remains an open problem.

Bücher and Zhou, *A horse race between the block maxima method and the peak-over-threshold approach*, Stat. Sci. 36 (2021), arXiv:1807.00282, §6:

> Block length choice and bias reduction for BM.

The quote was extracted from the source text, with symbols flattened; check it against the published version before citing.

## Why it matters
Runs declustering with a fixed run length is the standard peaks-over-threshold workflow for rainfall, river flow and wind (`extRemes::decluster`, `evd::exi`), and return levels scale with the extremal index. The target is a warning theorem: no polynomial run-length rule works for every model, while long blocks are safe. The echo process is a constructed model, so the message is that short-lag diagnostics cannot certify `θ`, not that real data contain echoes.

## What the library already has
`logEcho_tendstoInMeasure_runsEstimator` (short runs converge to `ϑ = 1`, not `θ = 1/2`), `logEcho_tendstoInMeasure_blocksEstimator` (long blocks converge to `θ`), `powEchoProcess_polyBlocks` (a step transition at `r_n ≍ n^{γ/α}`, at macroscopic levels), `HasSpectralTailProcess.tendstoInMeasure_runsEstimator`, `isBetaMixing_echoProcess`.

## What is missing
Estimator-level results for the power-lag echo at intermediate thresholds, which need a mixing-rate bound good enough for the concentration conditions, and a clean "no universal rule" statement.

## Pointers
`docs/PRACTICAL_OPEN_PROBLEMS.md`, C2. Survey feasibility estimates are unchecked plans, not results.
