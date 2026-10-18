# Junk-value audit

Lean makes partial operations total by returning a conventional ("junk") value: `x / 0 = 0`,
`0⁻¹ = 0`, `Real.log 0 = 0`, `Real.log (-x) = Real.log x`, `Real.sqrt (-x) = 0`, truncated `ℕ`
subtraction, `ENNReal.toReal ∞ = 0`, `ENNReal.ofReal (-x) = 0`, `rpow` of a negative base, the
sum of a non-summable series is `0`, the integral of a non-integrable function is `0`, `sSup` of an
unbounded set of reals is `0`, `limUnder` of a divergent function is arbitrary. A theorem can be
true only because one of these conventions fires. Then the formal statement says less than the
textbook statement, or something different. This audit looks for such theorems.

## Method

1. **Scan.** `scripts/JunkScan.lean` is a Lean meta-program that loads the whole library and walks
   the *statement* (type) of every public theorem from a module under `ExtremeValueTheory`
   (including `ForMathlib`). It records every junk-prone operation:
   - division and inverse on `ℝ`, `ℝ≥0`, `ℝ≥0∞`, `ℕ`;
   - `Real.log`, `Real.logb`, `Real.sqrt`, and real `rpow`;
   - `ℕ` subtraction;
   - `ENNReal.toReal`, `ENNReal.toNNReal`, `EReal.toReal`, `ENNReal.ofReal`, `Real.toNNReal`;
   - `Nat.floor`, `Nat.ceil`, `Int.toNat`;
   - `tsum` outside `ℝ≥0∞`, and the Bochner integral;
   - `limUnder`, `lim`, `Classical.epsilon`;
   - `sSup`/`sInf`/`iSup`/`iInf` on `ℝ` and `ℕ`, and `limsup`/`liminf` on `ℝ`;
   - `deriv`, `variance`, `condExp`.

   It also walks the bodies of all definitions. Run it with

   ```
   lake env lean scripts/JunkScan.lean > junk_scan.tsv            # summary table
   JUNK_DETAIL=1 lake env lean scripts/JunkScan.lean > detail.tsv # plus the unguarded terms
   ```

   It is not part of any library target, so CI neither builds nor runs it. A theorem counts as
   *priority* if it is named in `README.md`, in `THEOREMS.md`, or in a blueprint `\lean{…}` list.

2. **Automatic classification.** Each occurrence gets one of these labels:
   - **G** (guarded): a hypothesis with a guarding head (`≠`, `<`, `≤`, `Integrable`,
     `IntegrableOn`, `Summable`, `HasSum`, `BddAbove`, `IsFiniteMeasure`, …) mentions the term the
     operation could junk on.
   - **C** (constant): the term is closed, for example `x / 2`.
   - **L** (lambda-bound): the term mentions a variable bound by a `fun` inside the statement, such
     as a sequence under `Tendsto` or an integrand. A junk value at isolated points does not matter
     there.
   - **Q** (quantifier-bound): the term mentions a variable bound by an inner `∀` or `∃`.
   - **U** (unguarded): none of the above.

   Occurrences that appear only in hypotheses are tagged `hyp:`.

3. **Manual triage.** Every theorem with a **U** or **Q** occurrence in its *conclusion* was read
   in the source, priority theorems first. Many **U** hits are guarded in ways the scanner cannot
   see:
   - hypotheses from `variable`/`include` blocks;
   - structure fields, such as `IsRegularlyVarying` giving `∀ᶠ x, 0 < f x`, `AffineIncrEquiv`
     giving a positive scale, or a CDF measure being a probability measure;
   - interval membership, such as `G x ∈ Ioo 0 1`;
   - identities whose two sides become junk together, such as change-of-variables formulas.

   Each finding was checked against the textbook statement.

## Counts

| | |
|---|---|
| Public theorems scanned | 3718 |
| Theorems whose statement contains a junk-prone operation | 1696 |
| Priority theorems (README / THEOREMS.md / blueprint) | 1039, of which 572 have a hit |
| Theorems with a **U**/**Q** occurrence in the conclusion, all reviewed by hand | 740 (187 priority) |
| Definitions scanned / with a junk-prone operation in their body | 485 / 209 |
| Occurrences by class | G 807, C 439, L 1844, Q 416, U 1173 |
| Occurrences by operation | div 1856, rpow 633, inv 491, integral 487, log 453, ofReal 219, toReal 206, sqrt 110, tsum 45, deriv 42, `Real.toNNReal` 36, natSub 23, EReal.toReal 20, iSup 18, variance 18, sInf 16, toNNReal 6 |
| **Genuine issues** | **1, fixed** |
| Harmless but surprising (documented below) | 13 |

No headline theorem (README table, THEOREMS.md) depends on a junk value. The known Karamata issue
(`α = 1`, where `1 / (1 - 1) = 0` and the integral of a non-integrable `F` is `0`) was fixed
earlier: `tendsto_integral_Ioi_div` now assumes `1 < α`, and the `α = 1` and `α < 1` regimes are
stated separately in `Minimality/ClassicalKaramata.lean`.

## Genuine issues

| Theorem | Junk mechanism | Status |
|---|---|---|
| `HasSpectralMeasure.measure_univ_toReal` (`MaxStable/Converse.lean`; blueprint `max_stable.tex`) | `HasSpectralMeasure ν H` reads the exponent as `(∫⁻ … ∂H).toReal`. For an infinite `H` this is `toReal ∞ = 0`, so `∞ • δ₁` is a "spectral measure" of the point mass `δ₀`. The conclusion "total mass = extremal coefficient", whose textbook value lies in `[1, d]`, then read `0 = 0`. | **Fixed**: added `[IsFiniteMeasure H]`. Both users still build: `IsSimpleMaxStable.exists_isRegVarVector` already had `IsFiniteMeasure H`, and `measure_univ_ne_zero_of_hasSpectralMeasure` derives it locally from `H univ = 0`. Tests: `test_hasSpectralMeasure_infinite`, `test_spectral_both_sides_junk`, `test_Hinf_not_finite`. |

## Harmless but surprising

None of these makes a statement false or vacuous in the textbook range. Each holds in a
degenerate instance for a junk reason, or both sides become junk together.

| Theorem | What happens | Status |
|---|---|---|
| `Minimality.exists_hill_k_bounded_counterexample`, `Minimality.measure_dist_hill_pareto_ge` (`Minimality/ClassicalHill.lean`) | They quantify over every bounded `k`. In the `kₙ = 0` instances, `hill x 0 = 0⁻¹ * 0 = 0`, so the estimator is junk 0 and fails consistency for that reason only. The content for `k ≥ 1` is genuine. | Documented; test `test_hill_zero` |
| `Minimality.not_tendsto_integral_Ioi_div_of_lt_one` (`Minimality/ClassicalKaramata.lean`) | When `α < 1`, `F` is not integrable on `Ioi x`, so the Karamata ratio is identically junk 0 and fails to tend to `1/(α-1)` for that reason. The divergence itself is stated honestly in `max_rpow_karamata_counterexample`, and the module docstring explains this. | Documented; test `test_karamata_lt_one_ratio_zero` |
| `tail_compound` (`HeavyTails/RandomSums.lean`) | There is no summability assumption on `p`. For non-summable `p` the identity reads `0 = 0` (`toReal ∞` on the left, a non-summable `tsum` on the right). Its only user, `tendsto_tail_compound_div`, assumes summability. | Documented; test `test_tail_compound_nonsummable` |
| `hill_eq_sum_logExcess` (`Statistics/Hill.lean`) | `k = 0` is allowed; both sides are `0⁻¹ · … = 0`. | Harmless |
| `tendstoInDistribution_sum_hillSummand` (`Statistics/TailEmpiricalProcessRV.lean`) | With `ε₀ = 0` the variance `1 + 2 ε₀ log ε₀` uses `log 0 = 0`. That agrees with the continuous extension `ε log ε → 0`. | Harmless |
| `toReal_gpdLogDensityE`, `toReal_gevLogDensityE` | Off the support both sides are 0, because `(⊥ : EReal).toReal = 0` and `log 0 = 0` agree. These are bridge lemmas. | Harmless |
| `integral_pow_ferroSegersLaw`, `integral_id_ferroSegersLaw`, `integral_sq_ferroSegersLaw` | They assume only `0 < θ`. For `θ > 1`, `ferroSegersLaw θ` is not a probability measure (`ofReal (1 - θ) = 0`), but the moment formulas are still correct for that measure. `isProbabilityMeasure_ferroSegersLaw` assumes `θ ≤ 1`. | Harmless |
| `candidateExtremalIndex_mixture` (`Dependence/MixtureProcess.lean`) | `p` is unconstrained, and `mixtureCoin p` truncates through `ofReal`. The identity is still literally correct. | Harmless |
| `LinearProcess.exists_measure_tsum_gt_le` | There is no `0 < δ`. For `δ < 0` the junk value `0 ^ δ = 0` (textbook `∞`) only extends the theorem to a degenerate case. | Harmless |
| `StableIntegral.integral_one_sub_cos_mul_rpow`, `integral_sin_mul_rpow`, `integral_comp_mul_mul_rpow`, `neg_mul_integral_one_sub_cos_mul_rpow` | These are scaling identities. Outside the integrable range of `α`, both sides are junk 0. | Harmless |
| `stableExponent_mul_tan` (`StableLaws/Constants.lean`) | At `α = 1`, `tan (π/2) = 0` through `x / 0 = 0`. It is a rewriting lemma, used only with `α ≠ 1`. | Harmless |
| `card_filter_range_add_one_div_mem_Ioc` (`PointProcess/Exceedances.lean`) | For `s > t`, truncated subtraction gives 0, which is the correct count. | Harmless |
| `Minimality.mixture_hill_needs_mixing` | The cluster conjunct is instantiated with `rₙ = 0`, so it is an empty sum (`Icc 1 0 = ∅`). This is an explicit, documented choice, not a junk value. | Harmless |

## Convention-dependent definitions a reviewer should know

These definitions return a conventional value outside their intended domain. Every theorem that
uses them outside that domain was checked, and the hypotheses exclude the junk case unless listed
above.

- **Regular variation.**
  - `IsRegularlyVarying`/`IsSlowlyVarying` use `f (c x) / f x`, but also require `f` eventually
    positive, so the quotient is never `0/0` eventually.
  - `IsExtendedRegularlyVarying`, `HasTailProcess` and `HasSpectralTailProcess` divide by
    quantities that their own hypotheses keep positive.
- **Quantiles.**
  - `tailQuantile` (`DomainOfAttraction/Quantile.lean`, `Statistics/ExtremeQuantile.lean`) and
    `survivalQuantile` are `sInf` on `ℝ`, which is junk 0 on empty or unbounded sets. The lemmas
    assume `1 < t` or `p < F̄(M)`.
- **POT functions.**
  - `excessSurvival F u x = F (u + x) / F u` and `meanExcess F u = (∫_{Ioi u} F) / F u` are junk
    when `F u = 0`, and the mean excess is also junk when `F` is not integrable.
  - `conditionalExcessCDF`, `tailDependenceRatio`, `tailLaw` and `scaledLaw` divide by a
    probability that can be 0.
- **Shape-parameter families.**
  - `gevCDF`, `IsInMDAGEV`, `gpdSurvivalInv` and `boxCox` split off shape 0 with an explicit
    `if`, so they are junk-free.
  - `gpdSurvival` (`PeaksOverThreshold/Frechet.lean`) has no `max (·, 0)`, so for `ξ < 0` past the
    endpoint it is `rpow` of a negative base. It is used only with `ξ ≥ 0`, `x ≥ 0`; `gpdSurvival'`
    is correct for every shape.
- **Estimators.**
  - `hill x k` and `logMoment x k j` are 0 at `k = 0`. They use `Real.log` of order statistics,
    which equals `log |x|` for non-positive values, and `orderStat x j = 0` for `j ≥ n`.
  - `logExcess t y = log (max y t / t)` is 0 at `t = 0`.
  - `tailEmpiricalProcess`, `hillSummand`, `sampleMean`, `crossAvg`, `scoreAvg`,
    `intervalsEstimator₁/₂`, `blocksEstimator`, `runsEstimator` and
    `pickandsDependenceEstimator` evaluate to 0 for empty samples, via `x / 0` and `0⁻¹`.
- **Moments as integrals.**
  - `gpdMoment ρ p`, `stableConst α`, `stableSkewConst α` and `truncSecondMoment` are junk 0
    outside their integrability range. For example, `stableConst α = 0` for `α ≥ 2`, and
    `stableSkewConst` is meaningful only on `(0,1) ∪ (1,2)`; `α = 1` goes through
    `HasStableOneCharFun`.
- **Stable index.** `stableIndex μ` is 0 for a non-stable `μ`, and every user assumes
  `IsStable μ`.
- **Max-stable spectral measures.**
  - `HasSpectralMeasure` uses `toReal` of a possibly infinite lintegral; see the fixed issue
    above. It is harmless together with `IsSimpleMaxStable` or `IsFiniteMeasure H`.
  - `maxStableExponent μ y = -log (μ.real (Iic y))` and `extremalCoefficient` are junk 0, rather
    than `+∞`, when `μ (Iic y) = 0`; `IsSimpleMaxStable` rules this out.
- **Heavy tails.**
  - `tail μ x = μ.real (Ioi x)` is junk 0 for infinite measures.
  - `compound μ p` does not require `∑ p = 1`.
  - `mixtureCoin p` and `ferroSegersLaw θ` truncate their weights through `ENNReal.ofReal`.
  - `InfiniteMovingAverage.indexLaw` and `MovingAverage.indexLaw` divide by `∑ ψ^α`, and their
    users assume it is positive.
- **Conditioning.** `ProbabilityTheory.cond` on a null set is the zero measure, so identities
  stated with it read `0 = 0` there.
- **Wald truncation.** `waldTrunc` is an `EReal.toReal`, which is safe because of its
  `max … M` and the finite upper bound.
