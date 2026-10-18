# Mutation checks

Lean checks that each proof proves its statement. A mutation check asks the reverse question: does
the proof depend on the statement as written? We perturb the **statement** of a theorem (flip an
inequality, change a constant, flip the sign of a parameter, move a limit, replace a hypothesis by
`True`), keep the original proof, and recompile. If the proof still goes through, the mutant
**survives**. Either the perturbation gives an equivalent or weaker statement (harmless), or the
perturbed part of the statement does no work: a vacuous hypothesis, an irrelevant constant, or a
conclusion that holds for a trivial reason.

Script: [`scripts/mutation_check.py`](../scripts/mutation_check.py). Latest run: 2026-10-18, on
`main` at `c8661cc`.

## Result

**45 theorems, 323 mutants: 306 killed, 16 invalid, 1 survived, 0 timeouts.** The one survivor is
harmless (a stronger hypothesis, see below). No mutant showed a real weakness in a headline or
research statement.

## Method

1. **Locate.** The script indexes every `theorem`/`lemma` under `ExtremeValueTheory/`, tracking
   `namespace`/`section`/`end` to get full names. The statement is the text from the end of the
   name to the first top-level `:=`, so it covers binders, hypotheses and the conclusion.
2. **Mutate.** The operators, in priority order:

   | Key | Mutation |
   |---|---|
   | `nhds` | `𝓝 c` → `𝓝 (c + 1)` (the limit value) |
   | `atTop` / `atBot` | `atTop` ↔ `atBot` |
   | `pos` / `nonneg` | `0 < t` → `t < 0`, `0 ≤ t` → `t ≤ 0` (sign of a parameter) |
   | `hyp` | an explicit hypothesis `(h : P)`, not mentioned elsewhere in the statement, → `(h : True)` |
   | `lt` / `le` | `<` → `≤`, `≤` → `<` |
   | `lit1` / `lit2` / `lit0` | numerals `1` → `2`, `2` → `3` (so `1/2` → `1/3`), `0` → `1` |
   | `neg` | drop a unary `-` |
   | `and` / `or` | `∧` ↔ `∨` |
   | `Ioi` / `Iio` | `Ioi` → `Ici`, `Iio` → `Iic` |
   | `eq` | `=` → `≠` |

   At most 8 mutants per theorem (`--max-mutants`), picked round-robin over the operators. The
   conclusion comes first, then hypotheses from last to first, and the script prefers positions
   not already mutated. Comments and strings are never mutated.
3. **Check.** Each mutant is written into a scratch copy of its module in a fresh system temporary
   directory, which is deleted at the end. The real source tree is never touched. The copy is
   truncated right after the theorem. The proofs of earlier `theorem`/`lemma`/`example`
   declarations in the copy are replaced by `sorry`: later code sees only their statements, so this
   does not change what is checked, and it makes each check take seconds rather than minutes. If
   this "fast prefix" does not compile, the script uses the full prefix instead. That happened for
   1 of 45 theorems. Each copy is checked with `lake env lean <file>`, at most 4 at a time
   (`--jobs`).
4. **Classify.**
   - **killed**: the proof fails against the mutated statement.
   - **invalid**: the first error lies inside the mutated statement, so the mutant does not even
     elaborate. This is uninformative and is counted separately. Typical case: `hα : 0 < α` → `α < 0`
     when `hα` is passed to `F.IsInMDAFrechet hα` in the same statement.
   - **survived**: the original proof still checks. Inspect by hand.
   - **timeout**: the check took longer than `max(300 s, 3 × baseline + 60 s)`. Inconclusive.
   - **error**: an OS resource failure persisted after retries. Inconclusive.

   An unmutated baseline runs first. A theorem whose baseline does not compile, or takes longer
   than `--skip-after` (600 s), is skipped and reported. In this run no theorem was skipped. The
   slowest baseline took 54 s.

## Running it

From the repository root, after `lake build`:

```sh
python3 scripts/mutation_check.py                     # headline + research theorems (below)
python3 scripts/mutation_check.py isInMDAFrechet_iff  # selected theorems (suffix of the full name)
python3 scripts/mutation_check.py --list              # show the mutants without compiling
python3 scripts/mutation_check.py --jobs 4 --max-mutants 8 --json results.json
```

The full default run takes about 40 minutes with 4 jobs. It prints one line per mutant, a summary,
and the list of survivors. `--keep` keeps the scratch directory for inspection.

## Theorems covered

The default list is every Lean name in the README "Headline theorems" table and "Research results"
list, plus `tendsto_blockRatio`, `hasExtremalIndex_abs_of_alphaMixing` and `powEchoProcess_critical`
from `RESEARCH.md`. The short name `tendstoInMeasure_hill` also matches
`MovingAverage.tendstoInMeasure_hill`, and both are checked.

| Theorem | File | Mutants | Killed | Invalid | Survived |
|---|---|---|---|---|---|
| `IsExtremeValueDistr.classification` | `SelfSimilarCDF.lean` | 8 | 3 | 5 | 0 |
| `isMaxStable_iff_isExtremeValueDistr` | `GEV/MaxStable.lean` | 0 | – | – | – |
| `isInMDAFrechet_iff` | `DomainOfAttraction/Frechet.lean` | 5 | 2 | 3 | 0 |
| `isInMDAWeibull_iff` | `DomainOfAttraction/Weibull.lean` | 8 | 6 | 2 | 0 |
| `isInMDAGumbel_iff` | `DomainOfAttraction/GumbelNecessity.lean` | 8 | 8 | 0 | 0 |
| `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile` | `DomainOfAttraction/Quantile.lean` | 0 | – | – | – |
| `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` | `PeaksOverThreshold/Converse.lean` | 7 | 7 | 0 | 0 |
| `IsRegularlyVarying.tendsto_integral_Ioi_div` | `RegularVariation/Karamata.lean` | 8 | 7 | 0 | **1** |
| `tendsto_measure_mul_div_measure` | `RegularVariation/Breiman.lean` | 8 | 8 | 0 | 0 |
| `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt'` | `StableLaws/Constants.lean` | 8 | 7 | 1 | 0 |
| `domainOfAttraction_isStableIndex_iff` | `StableLaws/DomainOfAttractionIff.lean` | 8 | 7 | 1 | 0 |
| `IsStable.existsUnique_isStableIndex` | `StableLaws/StableIndex.lean` | 1 | 1 | 0 | 0 |
| `domainOfAttraction_gaussianReal_iff` | `StableLaws/GaussianDomain.lean` | 8 | 7 | 1 | 0 |
| `IsSubexponential.tendsto_tail_compound_div` | `HeavyTails/RandomSums.lean` | 8 | 8 | 0 | 0 |
| `tendsto_pkRuin_div_mul_tail` | `HeavyTails/Ruin.lean` | 8 | 8 | 0 | 0 |
| `tendstoInMeasure_hill` | `Statistics/Hill.lean` | 8 | 8 | 0 | 0 |
| `MovingAverage.tendstoInMeasure_hill` | `Statistics/HillCluster.lean` | 8 | 8 | 0 | 0 |
| `tendstoInDistribution_hill` | `Statistics/HillNormality.lean` | 8 | 8 | 0 | 0 |
| `tendstoInMeasure_hill_of_alphaMixing_rate` | `Statistics/HillDependent.lean` | 8 | 8 | 0 | 0 |
| `tendstoInMeasure_pickands` | `Statistics/Pickands.lean` | 8 | 8 | 0 | 0 |
| `tendstoInMeasure_momentEstimator_of_isInMDAGEV'` | `Statistics/MomentGeneral.lean` | 8 | 8 | 0 | 0 |
| `tendstoInDistribution_weissman` | `Statistics/ExtremeQuantileSecondOrder.lean` | 8 | 8 | 0 | 0 |
| `ae_tendsto_gpdMLE'` | `Statistics/GPDJointMLE.lean` | 8 | 8 | 0 | 0 |
| `exists_gpdMLE_tendstoInDistribution` | `Statistics/GPDMLENormality.lean` | 8 | 8 | 0 | 0 |
| `ae_tendsto_gevMLE` | `Statistics/GEVMLE.lean` | 8 | 7 | 1 | 0 |
| `tendsto_measureReal_partialMax_le_exp` | `Dependence/Leadbetter.lean` | 8 | 8 | 0 | 0 |
| `HasSpectralTailProcess.lintegral_timeChange` | `Dependence/TimeChange.lean` | 8 | 8 | 0 | 0 |
| `HasSpectralTailProcess.hasExtremalIndex_abs` | `Dependence/Anticlustering.lean` | 8 | 8 | 0 | 0 |
| `isRegVarVector_iff` | `RegularVariation/Multivariate.lean` | 8 | 8 | 0 | 0 |
| `CramerWold.isRegVarVector_of_tendsto_linear` | `RegularVariation/CramerWoldConverse.lean` | 8 | 8 | 0 | 0 |
| `isMDAWith_iff` | `Multivariate/DomainOfAttractionConverse.lean` | 8 | 8 | 0 | 0 |
| `IsMDAWith.tendsto_conditionalExcessCDF` | `Multivariate/POT.lean` | 8 | 8 | 0 | 0 |
| `IsSimpleMaxStable.existsUnique_hasSpectralMeasure` | `MaxStable/Uniqueness.lean` | 5 | 5 | 0 | 0 |
| `ProbabilityTheory.exists_isPoissonRandomMeasure` | `ForMathlib/Probability/PoissonRandomMeasure.lean` | 1 | 1 | 0 | 0 |
| `tendsto_measureReal_sumDiracRange_timeSpace_eq` | `PointProcess/Exceedances.lean` | 8 | 6 | 2 | 0 |
| `tendstoInDistribution_tailEmpiricalPath` | `Statistics/TailEmpiricalProcess.lean` | 8 | 8 | 0 | 0 |
| `logEchoProcess_theta_lt_vartheta` | `Dependence/EchoProcess.lean` | 8 | 8 | 0 | 0 |
| `logEchoProcess_phase_transition` | `Dependence/EchoPhaseTransition.lean` | 8 | 8 | 0 | 0 |
| `powEchoProcess_antiClustering_iff` | `Dependence/EchoPowerLag.lean` | 8 | 8 | 0 | 0 |
| `logEchoProcess_betaMixing_incompatible` | `Dependence/EchoMixing.lean` | 8 | 8 | 0 | 0 |
| `HasSpectralTailProcess.lt_candidateExtremalIndex_iff` | `Dependence/ThetaGap.lean` | 8 | 8 | 0 | 0 |
| `HasSpectralTailProcess.le_candidateExtremalIndex'` | `Dependence/ThetaLeVartheta.lean` | 8 | 8 | 0 | 0 |
| `HasSpectralTailProcess.tendsto_blockRatio` | `Dependence/Anticlustering.lean` | 8 | 8 | 0 | 0 |
| `HasSpectralTailProcess.hasExtremalIndex_abs_of_alphaMixing` | `Minimality/DependenceMixing.lean` | 8 | 8 | 0 | 0 |
| `powEchoProcess_critical` | `Dependence/EchoPowerLag.lean` | 8 | 8 | 0 | 0 |

By operator:

| Operator | Killed | Invalid | Survived |
|---|---|---|---|
| `hyp` (hypothesis → `True`) | 47 | 0 | 0 |
| `lt` | 37 | 4 | 0 |
| `atTop` | 37 | 0 | 0 |
| `nhds` | 32 | 3 | 0 |
| `pos` | 30 | 6 | 0 |
| `lit1` | 28 | 0 | 1 |
| `lit0` | 23 | 3 | 0 |
| `neg` | 18 | 0 | 0 |
| `and` | 17 | 0 | 0 |
| `le` | 12 | 0 | 0 |
| `lit2` | 10 | 0 | 0 |
| `eq` | 7 | 0 | 0 |
| `or`, `nonneg` | 3 each | 0 | 0 |
| `Ioi` | 2 | 0 | 0 |

## Survivors

**`IsRegularlyVarying.tendsto_integral_Ioi_div`** (`RegularVariation/Karamata.lean`), mutant `1 → 2`
in the hypothesis `(hα : 1 < α)`, giving `(hα : 2 < α)`.

*Classification: harmless (a stronger hypothesis).* The mutated theorem is a special case of the
original: Karamata's limit `∫_x^∞ F / (x F(x)) → 1/(α − 1)` for `α > 2`. It survives because the
proof uses `hα` only through `linarith` (to get `δ = (α − 1)/2 > 0` and `−α + δ < −1`), and
`linarith` accepts the stronger fact. The mutants that weaken or perturb the statement are all
killed: `1 < α` → `1 ≤ α`, `-α` → `α` in `hRV`, `hF` → `True`, `hRV` → `True`, and in the
conclusion `𝓝 (1/(α−1))` → `𝓝 (1/(α−1) + 1)`, `atTop` → `atBot` and `Ioi x` → `Ici x`. The
hypothesis itself is sharp: Karamata fails for `α < 1` and for `α = 1`
(`not_tendsto_integral_Ioi_div_of_lt_one`, `tendsto_integral_Ioi_div_atTop_of_neg_one` in
`Minimality/ClassicalKaramata.lean`).

No survivor revealed a real weakness.

## Invalid mutants

All 16 invalid mutants are ill-typed statements, not evidence about the proofs:

- 13 change a hypothesis that the same statement passes as an argument (`F.IsInMDAFrechet hα`,
  `standardFrechetCDF hξ`, the GEV log-likelihood's `hσ₀`, the exceedance level's `hu`), so the
  argument no longer has the expected type.
- 3 replace `𝓝 ν` by `𝓝 (ν + 1)` where `ν` is a `ProbabilityMeasure`, which has no `+`.

## What the checks do and do not show

- **Every tested hypothesis is used.** Each of the 47 `hyp` mutants replaces a hypothesis by `True`
  and keeps its name. All were killed, so for these hypotheses (measurability, independence,
  stationarity, regular variation, rate conditions, …) the proof really uses the stated fact. This
  complements the negative tests in `ExtremeValueTheory/Minimality/`, which show that some
  hypotheses cannot be dropped *at all*.
- **A kill is weaker evidence than a survivor.** A term-mode proof breaks under almost any change
  to the statement, so a kill shows that the proof depends on the statement, not that the mutated
  statement is false. Survivors are the signal. Whether a statement says the right thing is checked
  by `Test/NonVacuity`, `Test/KnownAnswers` and `FAITHFULNESS.md`.
- **Wrapper theorems have no operator.** `isMaxStable_iff_isExtremeValueDistr`
  (`G.IsMaxStable ↔ G.IsExtremeValueDistr`) and
  `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile` contain no inequality, numeral or
  limit target. Their content lives in the definitions, which the known-answer tests check. The
  same holds, almost entirely, for `IsStable.existsUnique_isStableIndex` and
  `exists_isPoissonRandomMeasure` (one `hyp` or `∧` mutant each).
- **Statement-only.** Definitions (`IsInMDAGEV`, `candidateExtremalIndex`, `hill`, …) are not
  mutated. A sign error inside a definition is the domain of the known-answer tests.
