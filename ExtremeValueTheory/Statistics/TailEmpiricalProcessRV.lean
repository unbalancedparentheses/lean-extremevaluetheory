/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.TailEmpiricalProcess
import ExtremeValueTheory.Statistics.HillNormality
import ExtremeValueTheory.ForMathlib.Probability.SkorokhodFunctionals

/-!
# Hill's estimator via the tail empirical process

Applications of the uniform tail empirical process
`W_n(t) = √k ((1/k) ∑_{i<n} 1{U_i ≥ 1 - (k/n) t} - t)` (`tailEmpiricalProcess`) and of its
weak convergence in `D([0, 1])` ([de Haan–Ferreira, §5.1–5.2]; [Drees 1998]).

* **Continuous functionals.** If `B` has the finite-dimensional distributions of Brownian motion,
  `h(W_n) ⇒ h(B)` for every measurable functional `h` on `D` continuous at almost every path of
  `B` (`tendstoInDistribution_comp_tailEmpiricalPath`), e.g. the supremum
  (`tendstoInDistribution_supNorm_tailEmpiricalPath`) and the integral functionals of
  `SkorokhodSpace.continuous_integral_mul`. As an application, the law of the Brownian functional
  `∫_ε^1 B(t) dt / t - B(1)` is `N(0, 1 + 2 ε log ε)` (`map_hillFunctional_eq_gaussianReal`).
* **Weighted approximation near `0`.** For `η > 0`,
  `lim_{δ → 0} limsup_n P(sup_{0 < t ≤ δ} |W_n(t)| / t ^ (1/2 - η) > ε) = 0`
  (`exists_eventually_measureReal_weighted_le`), and `E ∫_0^ε |W_n(t)| dt / t ≤ 2 √ε`
  (`lintegral_lintegral_tailEmpiricalProcess_div_le`).
* **Hill's estimator.** For the exponential sample `E_i = -log (1 - U_i)` and
  `T = (n/k) (1 - U_{(k+1)})`, the Hill statistic is exactly
  `√k ((1/k) ∑_{j<k} (E_{(j+1)} - E_{(k+1)}) - 1) = ∫_0^T W_n(t) dt / t + √k (T - 1)`
  (`meanExcess_eq_integral_tailEmpiricalProcess`). This is
  `∫_ε^1 W_n(t) dt / t - W_n(1)` up to a remainder that vanishes in probability
  (`tendstoInMeasure_meanExcessStat_sub_sum_hillSummand`), and the truncated functional is a row
  sum of a triangular array satisfying the central limit theorem
  (`tendstoInDistribution_sum_hillSummand`). Hence the Hill statistic is asymptotically `N(0, 1)`
  (`tendstoInDistribution_meanExcessStat`,
  `tendstoInDistribution_meanExcess_of_tailEmpiricalProcess`)
  and, for Pareto samples with `k → ∞`, `k / n → 0`, `√k (H_{k,n} - 1/α) ⇒ N(0, 1/α²)`
  (`tendstoInDistribution_hill_pareto_of_tailEmpiricalProcess`), a second proof of
  `tendstoInDistribution_hill_pareto` (which uses the Rényi representation).

## References

* [L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*], Theorems 3.2.5, 5.1.4
* [J. H. J. Einmahl, *Limit theorems for tail processes with application to intermediate quantile
  estimation*, J. Statist. Plann. Inference 32 (1992)]
* [H. Drees, *On smooth statistical tail functionals*, Scand. J. Statist. 25 (1998)]
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal NNReal Real

namespace ExtremeValueTheory

/-! ### Deterministic integrals -/

section Integrals

open intervalIntegral

lemma intervalIntegrable_indicator_Ici_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    IntervalIntegrable ((Set.Ici c).indicator fun t : ℝ ↦ t⁻¹) volume a b := by
  have hinv : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume a b :=
    intervalIntegral.intervalIntegrable_inv (fun x hx ↦ by
      rw [Set.uIcc_of_le hab] at hx; exact (ha.trans_le hx.1).ne') continuous_id.continuousOn
  refine hinv.mono_fun ?_ (ae_of_all _ fun t ↦ ?_)
  · exact (measurable_inv.indicator measurableSet_Ici).aestronglyMeasurable
  · exact norm_indicator_le_norm_self _ _

/-- `∫_a^b 1{t ≥ c} dt / t = log (b / max a (min b c))` for `0 < a ≤ b`. -/
lemma integral_indicator_Ici_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    ∫ t in a..b, (Set.Ici c).indicator (fun t : ℝ ↦ t⁻¹) t = Real.log (b / max a (min b c)) := by
  rcases le_or_gt c a with hca | hac
  · rw [min_eq_right (hca.trans hab), max_eq_left hca, ← integral_inv_of_pos ha (ha.trans_le hab)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hab] at ht
    simp [Set.indicator, hca.trans ht.1]
  rcases lt_or_ge b c with hbc | hcb
  · rw [min_eq_left hbc.le, max_eq_right hab, div_self (ha.trans_le hab).ne', Real.log_one]
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_]
    · simp
    rw [Set.uIcc_of_le hab] at ht
    simp [Set.indicator, not_le.2 (ht.2.trans_lt hbc)]
  rw [min_eq_right hcb, max_eq_right hac.le,
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_indicator_Ici_inv ha hac.le c)
      (intervalIntegrable_indicator_Ici_inv (ha.trans hac) hcb c)]
  have h1 : ∫ t in a..c, (Set.Ici c).indicator (fun t : ℝ ↦ t⁻¹) t = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (0 : ℝ)) ?_]
    · simp
    filter_upwards [Measure.ae_ne volume c] with t htc ht
    rw [Set.uIoc_of_le hac.le] at ht
    simp [Set.indicator, not_le.2 (lt_of_le_of_ne ht.2 htc)]
  have h2 : ∫ t in c..b, (Set.Ici c).indicator (fun t : ℝ ↦ t⁻¹) t = Real.log (b / c) := by
    rw [← integral_inv_of_pos (ha.trans hac) (ha.trans_le (hac.le.trans hcb))]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hcb] at ht
    simp [Set.indicator, ht.1]
  rw [h1, h2, zero_add]

/-- `∫_0^b 1{t ≥ c} dt / t = log⁺ (b / c)` for `c > 0`. -/
lemma integral_zero_indicator_Ici_inv {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) :
    ∫ t in (0 : ℝ)..b, (Set.Ici c).indicator (fun t : ℝ ↦ t⁻¹) t = max (Real.log (b / c)) 0 := by
  rcases lt_or_ge b c with hbc | hcb
  · rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_]
    · simp only [intervalIntegral.integral_zero]
      refine (max_eq_right ?_).symm
      rcases hb.eq_or_lt with h | h
      · simp [← h]
      exact Real.log_nonpos (by positivity) ((div_le_one hc).2 hbc.le)
    rw [Set.uIcc_of_le hb] at ht
    simp [Set.indicator, not_le.2 (ht.2.trans_lt hbc)]
  have hii : IntervalIntegrable ((Set.Ici c).indicator fun t : ℝ ↦ t⁻¹) volume 0 c := by
    refine (intervalIntegrable_congr_ae ?_).1 (intervalIntegrable_const (c := (0 : ℝ)))
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [Measure.ae_ne volume c] with t htc ht
    rw [Set.uIoc_of_le hc.le] at ht
    simp [Set.indicator, not_le.2 (lt_of_le_of_ne ht.2 htc)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hii
      (intervalIntegrable_indicator_Ici_inv hc hcb c)]
  have h1 : ∫ t in (0 : ℝ)..c, (Set.Ici c).indicator (fun t : ℝ ↦ t⁻¹) t = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (0 : ℝ)) ?_]
    · simp
    filter_upwards [Measure.ae_ne volume c] with t htc ht
    rw [Set.uIoc_of_le hc.le] at ht
    simp [Set.indicator, not_le.2 (lt_of_le_of_ne ht.2 htc)]
  rw [h1, zero_add, integral_indicator_Ici_inv hc hcb, min_eq_right hcb, max_self,
    max_eq_left (Real.log_nonneg ((one_le_div hc).2 hcb))]

lemma intervalIntegrable_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun hf.aestronglyMeasurable (ae_of_all _ fun x ↦ by
    simp only [Real.norm_eq_abs]
    exact (hC x).trans (le_abs_self C))

/-- `logTrunc p ε v = -log (max ε (min 1 (v / p)))`, the value of `∫_ε^1 1{v ≤ p t} dt / t`. -/
noncomputable def logTrunc (p ε v : ℝ) : ℝ := -Real.log (max ε (min 1 (v / p)))

lemma measurable_logTrunc (p ε : ℝ) : Measurable (logTrunc p ε) := by
  unfold logTrunc; fun_prop

lemma logTrunc_nonneg {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (v : ℝ) : 0 ≤ logTrunc p ε v := by
  unfold logTrunc
  rw [neg_nonneg]
  exact Real.log_nonpos (hε0.le.trans (le_max_left _ _)) (max_le hε1 (min_le_left _ _))

lemma logTrunc_le {p ε : ℝ} (hε0 : 0 < ε) (v : ℝ) : logTrunc p ε v ≤ -Real.log ε := by
  unfold logTrunc
  exact neg_le_neg (Real.log_le_log hε0 (le_max_left _ _))

lemma indicator_Ici_one_sub_div {p : ℝ} (hp : 0 < p) (u t : ℝ) :
    (Set.Ici (1 - p * t)).indicator (1 : ℝ → ℝ) u / t =
      (Set.Ici ((1 - u) / p)).indicator (fun t : ℝ ↦ t⁻¹) t := by
  have : 1 - p * t ≤ u ↔ (1 - u) / p ≤ t := by
    rw [div_le_iff₀ hp]; constructor <;> intro h <;> linarith
  by_cases h : 1 - p * t ≤ u
  · simp [Set.indicator, h, this.1 h]
  · simp [Set.indicator, h, mt this.2 h]

/-- `∫_ε^1 (1{u ≥ 1 - p t} - p t) dt / t = logTrunc p ε (1 - u) - p (1 - ε)`. -/
lemma integral_indicator_sub_div {p ε : ℝ} (hp : 0 < p) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (u : ℝ) :
    ∫ t in ε..1, ((Set.Ici (1 - p * t)).indicator 1 u - p * t) / t =
      logTrunc p ε (1 - u) - p * (1 - ε) := by
  rw [intervalIntegral.integral_congr (g := fun t ↦
      (Set.Ici ((1 - u) / p)).indicator (fun t : ℝ ↦ t⁻¹) t - p) fun t ht ↦ ?_]
  · rw [intervalIntegral.integral_sub (intervalIntegrable_indicator_Ici_inv hε0 hε1 _)
      intervalIntegrable_const, integral_indicator_Ici_inv hε0 hε1, intervalIntegral.integral_const,
      smul_eq_mul, one_div, Real.log_inv, logTrunc]
    ring
  rw [Set.uIcc_of_le hε1] at ht
  have ht0 : 0 < t := hε0.trans_le ht.1
  simp only
  rw [sub_div, indicator_Ici_one_sub_div hp u t, mul_div_assoc, div_self ht0.ne', mul_one]

/-- The uniform law is invariant under `u ↦ 1 - u`. -/
lemma integral_uniform_comp_one_sub (g : ℝ → ℝ) : ∫ u, g (1 - u) ∂μU = ∫ v in (0 : ℝ)..1, g v := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left]
  norm_num

/-- The centered log-excess `logTrunc p ε v - 1{v ≤ p}`. -/
noncomputable def logTruncExcess (p ε v : ℝ) : ℝ := logTrunc p ε v - (Set.Iic p).indicator 1 v

lemma measurable_logTruncExcess (p ε : ℝ) : Measurable (logTruncExcess p ε) :=
  (measurable_logTrunc p ε).sub (measurable_one.indicator measurableSet_Iic)

lemma abs_logTruncExcess_le {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (v : ℝ) :
    |logTruncExcess p ε v| ≤ -Real.log ε + 1 := by
  unfold logTruncExcess
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_of_nonneg (logTrunc_nonneg hε0 hε1 v)]; exact logTrunc_le hε0 v
  · by_cases h : v ∈ Set.Iic p <;> simp [h]

lemma logTruncExcess_of_le {p ε v : ℝ} (hp : 0 < p) (hε1 : ε ≤ 1) (hv : v ≤ p * ε) :
    logTruncExcess p ε v = -Real.log ε - 1 := by
  have h1 : min 1 (v / p) ≤ ε := (min_le_right _ _).trans (by rwa [div_le_iff₀' hp])
  have h2 : v ≤ p := hv.trans (mul_le_of_le_one_right hp.le hε1)
  simp [logTruncExcess, logTrunc, max_eq_left h1, Set.indicator, h2]

lemma logTruncExcess_of_mem {p ε v : ℝ} (hp : 0 < p) (hv : v ∈ Set.Icc (p * ε) p) :
    logTruncExcess p ε v = -Real.log (v / p) - 1 := by
  have h1 : v / p ≤ 1 := (div_le_one hp).2 hv.2
  have h2 : ε ≤ v / p := by rw [le_div_iff₀' hp]; exact hv.1
  simp [logTruncExcess, logTrunc, min_eq_right h1, max_eq_right h2, Set.indicator, hv.2]

lemma logTruncExcess_of_lt {p ε v : ℝ} (hp : 0 < p) (hε1 : ε ≤ 1) (hv : p < v) :
    logTruncExcess p ε v = 0 := by
  have h1 : 1 ≤ v / p := by rw [le_div_iff₀ hp]; linarith
  simp [logTruncExcess, logTrunc, min_eq_left h1, max_eq_right hε1, Set.indicator, not_le.2 hv]

lemma integral_logTruncExcess_zero_mul {p ε : ℝ} (hp : 0 < p) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (j : ℕ) :
    ∫ v in (0 : ℝ)..p * ε, logTruncExcess p ε v ^ j = p * ε * (-Real.log ε - 1) ^ j := by
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (-Real.log ε - 1) ^ j) fun v hv ↦ ?_]
  · simp
  rw [Set.uIcc_of_le (mul_pos hp hε0).le] at hv
  simp only
  rw [logTruncExcess_of_le hp hε1 hv.2]

lemma integral_logTruncExcess_of_lt {p ε : ℝ} (hp : 0 < p) (hε1 : ε ≤ 1) (hp1 : p ≤ 1) (j : ℕ)
    (hj : j ≠ 0) : ∫ v in p..1, logTruncExcess p ε v ^ j = 0 := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (0 : ℝ)) ?_]
  · simp
  refine ae_of_all _ fun v hv ↦ ?_
  rw [Set.uIoc_of_le hp1] at hv
  simp [logTruncExcess_of_lt hp hε1 hv.1, hj]

lemma integral_logTruncExcess_mid {p ε : ℝ} (hp : 0 < p) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ v in p * ε..p, logTruncExcess p ε v = p * ε * Real.log ε := by
  have hpe : 0 < p * ε := mul_pos hp hε0
  have hle : p * ε ≤ p := mul_le_of_le_one_right hp.le hε1
  rw [intervalIntegral.integral_congr (g := fun v ↦ -Real.log (v / p) - 1) fun v hv ↦ by
    rw [Set.uIcc_of_le hle] at hv; exact logTruncExcess_of_mem hp hv]
  have hderiv : ∀ v ∈ Set.uIcc (p * ε) p,
      HasDerivAt (fun v ↦ -(v * Real.log (v / p))) (-Real.log (v / p) - 1) v := by
    intro v hv
    rw [Set.uIcc_of_le hle] at hv
    have hv0 : 0 < v := hpe.trans_le hv.1
    have h1 : HasDerivAt (fun v ↦ v / p) (1 / p) v := (hasDerivAt_id v).div_const p
    have h2 := (h1.log (div_pos hv0 hp).ne')
    refine ((hasDerivAt_id' v).mul h2).neg.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · rw [div_self hp.ne', Real.log_one, mul_div_cancel_left₀ _ hp.ne']
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    refine ContinuousOn.sub (ContinuousOn.neg ?_) continuousOn_const
    exact ContinuousOn.log (continuousOn_id.div_const p) fun v hv ↦
      (div_pos (hpe.trans_le hv.1) hp).ne'

lemma integral_logTruncExcess_sq_mid {p ε : ℝ} (hp : 0 < p) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ v in p * ε..p, logTruncExcess p ε v ^ 2 =
      p - (p * ε * (Real.log ε + 1) ^ 2 - 2 * (p * ε) * Real.log ε) := by
  have hpe : 0 < p * ε := mul_pos hp hε0
  have hle : p * ε ≤ p := mul_le_of_le_one_right hp.le hε1
  rw [intervalIntegral.integral_congr (g := fun v ↦ (Real.log (v / p) + 1) ^ 2) fun v hv ↦ by
    rw [Set.uIcc_of_le hle] at hv; simp only; rw [logTruncExcess_of_mem hp hv]; ring]
  have hderiv : ∀ v ∈ Set.uIcc (p * ε) p,
      HasDerivAt (fun v ↦ v * (Real.log (v / p) + 1) ^ 2 - 2 * v * Real.log (v / p))
        ((Real.log (v / p) + 1) ^ 2) v := by
    intro v hv
    rw [Set.uIcc_of_le hle] at hv
    have hv0 : 0 < v := hpe.trans_le hv.1
    have h1 : HasDerivAt (fun v ↦ v / p) (1 / p) v := (hasDerivAt_id v).div_const p
    have h2 := (h1.log (div_pos hv0 hp).ne')
    refine (((hasDerivAt_id' v).mul ((h2.add_const 1).pow 2)).sub
      (((hasDerivAt_id' v).const_mul 2).mul h2)).congr_deriv ?_
    norm_num
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · rw [div_self hp.ne', Real.log_one, mul_div_cancel_left₀ _ hp.ne']
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    refine ContinuousOn.pow (ContinuousOn.add ?_ continuousOn_const) 2
    exact ContinuousOn.log (continuousOn_id.div_const p) fun v hv ↦
      (div_pos (hpe.trans_le hv.1) hp).ne'

lemma intervalIntegrable_logTruncExcess_pow {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ)
    (a b : ℝ) : IntervalIntegrable (fun v ↦ logTruncExcess p ε v ^ j) volume a b :=
  intervalIntegrable_of_abs_le ((measurable_logTruncExcess p ε).pow_const j)
    (C := (-Real.log ε + 1) ^ j) (fun v ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_logTruncExcess_le hε0 hε1 v) j) a b

/-- `∫_0^1 (logTrunc p ε v - 1{v ≤ p}) dv = - p ε`. -/
lemma integral_logTruncExcess {p ε : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ v in (0 : ℝ)..1, logTruncExcess p ε v = -(p * ε) := by
  have h := fun a b ↦ intervalIntegrable_logTruncExcess_pow (p := p) hε0 hε1 1 a b
  simp only [pow_one] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (h 0 (p * ε)) (h (p * ε) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (h (p * ε) p) (h p 1)]
  have h1 := integral_logTruncExcess_zero_mul hp hε0 hε1 1
  have h3 := integral_logTruncExcess_of_lt hp hε1 hp1 1 one_ne_zero
  simp only [pow_one] at h1 h3
  rw [h1, h3, integral_logTruncExcess_mid hp hε0 hε1]
  ring

/-- `∫_0^1 (logTrunc p ε v - 1{v ≤ p}) ^ 2 dv = p (1 + 2 ε log ε)`. -/
lemma integral_logTruncExcess_sq {p ε : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∫ v in (0 : ℝ)..1, logTruncExcess p ε v ^ 2 = p * (1 + 2 * ε * Real.log ε) := by
  have h := fun a b ↦ intervalIntegrable_logTruncExcess_pow (p := p) hε0 hε1 2 a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (h 0 (p * ε)) (h (p * ε) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (h (p * ε) p) (h p 1),
    integral_logTruncExcess_zero_mul hp hε0 hε1 2,
    integral_logTruncExcess_of_lt hp hε1 hp1 2 two_ne_zero,
    integral_logTruncExcess_sq_mid hp hε0 hε1]
  ring

end Integrals

/-! ### The truncated Hill functional as a row sum -/

section Summand

/-- The summand of the row sum `∫_ε^1 W_n(t) dt / t - W_n(1) = ∑_{i<n} hillSummand n k ε (U_i)`:
with `p = k / n`, `k^{-1/2} (logTrunc p ε (1 - u) - 1{u ≥ 1 - p} + p ε)`. -/
noncomputable def hillSummand (n k : ℕ) (ε u : ℝ) : ℝ :=
  (√(k : ℝ))⁻¹ * (logTruncExcess (k / n) ε (1 - u) + k / n * ε)

lemma measurable_hillSummand (n k : ℕ) (ε : ℝ) : Measurable (hillSummand n k ε) := by
  unfold hillSummand
  exact ((((measurable_logTruncExcess _ ε).comp (measurable_const.sub measurable_id)).add
    measurable_const).const_mul _)

lemma abs_hillSummand_le (n k : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (u : ℝ) :
    |hillSummand n k ε u| ≤ (√(k : ℝ))⁻¹ * (-Real.log ε + 1 + k / n * ε) := by
  unfold hillSummand
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (by positivity)
  rw [abs_of_nonneg (show (0 : ℝ) ≤ k / n * ε by positivity)]
  linarith [abs_logTruncExcess_le (p := (k : ℝ) / n) hε0 hε1 (1 - u)]

lemma integral_hillSummand {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) : ∫ u, hillSummand n k ε u ∂μU = 0 := by
  have hn : 0 < n := hk.trans_le hkn
  have hp : (0 : ℝ) < k / n := by positivity
  have hp1 : (k : ℝ) / n ≤ 1 := (div_le_one (by exact_mod_cast hn)).2 (by exact_mod_cast hkn)
  unfold hillSummand
  rw [integral_const_mul, integral_add, integral_uniform_comp_one_sub (logTruncExcess _ ε),
    integral_logTruncExcess hp hp1 hε0 hε1]
  · simp
  · exact (Integrable.of_bound (C := -Real.log ε + 1)
      ((measurable_logTruncExcess _ ε).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun u ↦ abs_logTruncExcess_le hε0 hε1 _))
  · exact integrable_const _

lemma mul_integral_hillSummand_sq {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    n * ∫ u, hillSummand n k ε u ^ 2 ∂μU = 1 + 2 * ε * Real.log ε - k / n * ε ^ 2 := by
  have hn : 0 < n := hk.trans_le hkn
  have hp : (0 : ℝ) < k / n := by positivity
  have hp1 : (k : ℝ) / n ≤ 1 := (div_le_one (by exact_mod_cast hn)).2 (by exact_mod_cast hkn)
  set p : ℝ := k / n with hpdef
  have hsq (u : ℝ) : hillSummand n k ε u ^ 2 = (k : ℝ)⁻¹ * ((fun v ↦ logTruncExcess p ε v ^ 2 +
      2 * (p * ε) * logTruncExcess p ε v + (p * ε) ^ 2) (1 - u)) := by
    unfold hillSummand
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  simp_rw [hsq]
  have hc := integral_uniform_comp_one_sub (fun v ↦ logTruncExcess p ε v ^ 2 +
      2 * (p * ε) * logTruncExcess p ε v + (p * ε) ^ 2)
  rw [integral_const_mul, hc]
  have h1 := intervalIntegrable_logTruncExcess_pow (p := p) hε0 hε1 1 0 1
  have h2 := intervalIntegrable_logTruncExcess_pow (p := p) hε0 hε1 2 0 1
  simp only [pow_one] at h1
  rw [intervalIntegral.integral_add (h2.add (h1.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_add h2 (h1.const_mul _), intervalIntegral.integral_const_mul,
    integral_logTruncExcess_sq hp hp1 hε0 hε1, integral_logTruncExcess hp hp1 hε0 hε1,
    intervalIntegral.integral_const]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnp : (n : ℝ) * (k : ℝ)⁻¹ * p = 1 := by rw [hpdef]; field_simp
  simp only [smul_eq_mul, sub_zero, one_mul]
  linear_combination (1 + 2 * ε * Real.log ε - p * ε ^ 2) * hnp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The truncated Hill functional of the tail empirical process,
`∫_ε^1 W_n(t) dt / t = k^{-1/2} ∑_{i<n} (logTrunc (k/n) ε (1 - U_i) - (k/n) (1 - ε))`. -/
lemma integral_tailEmpiricalProcess_div (U : ℕ → Ω → ℝ) (ω : Ω) {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ t in ε..1, tailEmpiricalProcess U n k t ω / t =
      (√(k : ℝ))⁻¹ * ∑ i ∈ range n, (logTrunc (k / n) ε (1 - U i ω) - k / n * (1 - ε)) := by
  have hp : (0 : ℝ) < k / n := by positivity
  have h (t : ℝ) : tailEmpiricalProcess U n k t ω / t = ∑ i ∈ range n, (√(k : ℝ))⁻¹ *
      (((Set.Ici (1 - k / n * t)).indicator 1 (U i ω) - k / n * t) / t) := by
    unfold tailEmpiricalProcess
    rw [sqrt_mul_inv_sub_eq hn.ne', ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_const, card_range, nsmul_eq_mul, mul_div_assoc]
  simp_rw [h]
  have hint (i : ℕ) : IntervalIntegrable (fun t ↦ (√(k : ℝ))⁻¹ *
      (((Set.Ici (1 - k / n * t)).indicator 1 (U i ω) - k / n * t) / t)) volume ε 1 := by
    refine IntervalIntegrable.const_mul ?_ _
    refine (intervalIntegrable_congr fun t ht ↦ ?_).1
      ((intervalIntegrable_indicator_Ici_inv hε0 hε1 ((1 - U i ω) / (k / n))).sub
        (intervalIntegrable_const (c := (k : ℝ) / n)))
    rw [Set.uIoc_of_le hε1] at ht
    have ht0 : 0 < t := hε0.trans ht.1
    rw [show ((Set.Ici (1 - (k : ℝ) / n * t)).indicator 1 (U i ω) - k / n * t) / t =
      (Set.Ici (1 - (k : ℝ) / n * t)).indicator 1 (U i ω) / t - k / n by field_simp,
      indicator_Ici_one_sub_div hp]
  rw [intervalIntegral.integral_finsetSum fun i _ ↦ hint i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [intervalIntegral.integral_const_mul, integral_indicator_sub_div hp hε0 hε1]

/-- **The truncated Hill functional as a row sum**:
`∫_ε^1 W_n(t) dt / t - W_n(1) = ∑_{i<n} hillSummand n k ε (U_i)`. -/
lemma sum_hillSummand_eq (U : ℕ → Ω → ℝ) (ω : Ω) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∑ i ∈ range n, hillSummand n k ε (U i ω) =
      (∫ t in ε..1, tailEmpiricalProcess U n k t ω / t) - tailEmpiricalProcess U n k 1 ω := by
  rw [integral_tailEmpiricalProcess_div U ω hn hk hε0 hε1]
  unfold tailEmpiricalProcess
  rw [sqrt_mul_inv_sub_eq hn.ne', ← mul_sub]
  unfold hillSummand
  rw [← Finset.mul_sum]
  congr 1
  have hind (u : ℝ) : (Set.Iic ((k : ℝ) / n)).indicator 1 (1 - u) =
      (Set.Ici (1 - (k : ℝ) / n * 1)).indicator (1 : ℝ → ℝ) u := by
    rw [mul_one]
    by_cases h : 1 - u ≤ (k : ℝ) / n
    · simp [Set.indicator, h, show 1 - (k : ℝ) / n ≤ u by linarith]
    · simp [Set.indicator, h, show ¬ (1 - (k : ℝ) / n ≤ u) by intro h'; apply h; linarith]
  simp only [logTruncExcess, hind, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    card_range, nsmul_eq_mul]
  ring

/-- **Central limit theorem for the truncated Hill functional of the tail empirical process**.
If `k n → ∞`, `k n / n → 0`, and the truncation levels `ε n ∈ (0, 1]` satisfy `ε n → ε₀` and
`log (ε n) / √(k n) → 0`, then `∑_{i<n} hillSummand n (k n) (ε n) (U_i)`, i.e.
`∫_{ε n}^1 W_n(t) dt / t - W_n(1)`, converges in distribution to `N(0, 1 + 2 ε₀ log ε₀)`. -/
theorem tendstoInDistribution_sum_hillSummand [IsProbabilityMeasure P] {U : ℕ → Ω → ℝ}
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) {ε₀ : ℝ}
    (hεlim : Tendsto ε atTop (𝓝 ε₀))
    (hlog : Tendsto (fun n ↦ Real.log (ε n) / √(k n : ℝ)) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ i ∈ range n, hillSummand n (k n) (ε n) (U i ω)) atTop id
      (fun _ ↦ P) (gaussianReal 0 (1 + 2 * ε₀ * Real.log ε₀).toNNReal) := by
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hsq : Tendsto (fun n ↦ (√(k n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hkR)
  have hkn1 : ∀ᶠ n in atTop, k n ≤ n := by
    filter_upwards [hkn.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    rw [div_lt_one hn'] at hn
    exact_mod_cast hn.le
  have hvar : Tendsto (fun n : ℕ ↦ n * ∫ u, hillSummand n (k n) (ε n) u ^ 2 ∂μU) atTop
      (𝓝 (1 + 2 * ε₀ * Real.log ε₀)) := by
    have h1 : Tendsto (fun n ↦ 1 + 2 * (ε n * Real.log (ε n)) - k n / n * ε n ^ 2) atTop
        (𝓝 (1 + 2 * (ε₀ * Real.log ε₀) - 0 * ε₀ ^ 2)) :=
      (tendsto_const_nhds.add
        ((Real.continuous_mul_log.tendsto ε₀).comp hεlim |>.const_mul 2)).sub
        (hkn.mul (hεlim.pow 2))
    rw [zero_mul, sub_zero, ← mul_assoc] at h1
    refine h1.congr' ?_
    filter_upwards [hkn1, hk.eventually_gt_atTop 0] with n hn hk0
    rw [mul_integral_hillSummand_sq hk0 hn (hε0 n) (hε1 n)]
    ring
  have hv0 : 0 ≤ 1 + 2 * ε₀ * Real.log ε₀ := by
    refine ge_of_tendsto hvar (Eventually.of_forall fun n ↦ ?_)
    exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun u ↦ sq_nonneg _)
  refine tendstoInDistribution_sum_range_of_bounded hU hind hlaw
    (fun n ↦ measurable_hillSummand n (k n) (ε n))
    (M := fun n ↦ (√(k n : ℝ))⁻¹ * (-Real.log (ε n) + 1 + k n / n * ε n)) ?_
    (fun n u ↦ abs_hillSummand_le n (k n) (hε0 n) (hε1 n) u) ?_ ?_
  · have h2 : Tendsto (fun n ↦ -(Real.log (ε n) / √(k n : ℝ)) +
        (√(k n : ℝ))⁻¹ * (1 + k n / n * ε n))
        atTop (𝓝 (-0 + 0 * (1 + 0 * ε₀))) :=
      hlog.neg.add (hsq.mul (tendsto_const_nhds.add (hkn.mul hεlim)))
    simp only [neg_zero, zero_mul, add_zero] at h2
    refine h2.congr fun n ↦ ?_
    rw [div_eq_inv_mul]
    ring
  · filter_upwards [hkn1, hk.eventually_gt_atTop 0] with n hn hk0
    exact integral_hillSummand hk0 hn (hε0 n) (hε1 n)
  · rwa [Real.coe_toNNReal _ hv0]

end Summand

/-! ### The Hill statistic as an integral of the tail empirical process -/

section Representation

variable {n : ℕ}

/-- The sum of the top `k` excesses over the `(k+1)`-th largest observation is the sum of the
positive parts of all excesses. -/
lemma sum_range_orderStat_sub_eq (x : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    ∑ j ∈ range k, (orderStat x j - orderStat x k) = ∑ i, max (x i - orderStat x k) 0 := by
  rw [← sum_orderStat x (fun z ↦ max (z - orderStat x k) 0),
    ← Finset.sum_range_add_sum_Ico _ hk.le]
  rw [Finset.sum_eq_zero (s := Ico k n), add_zero]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [max_eq_left (sub_nonneg.2 (orderStat_anti x (mem_range.1 hj).le hk))]
  · intro j hj
    rw [Finset.mem_Ico] at hj
    exact max_eq_right (sub_nonpos.2 (orderStat_anti x hj.1 hj.2))

/-- At least `k + 1` observations are at least the `(k+1)`-th largest one. -/
lemma succ_le_card_orderStat_le (x : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    k + 1 ≤ #{i | orderStat x k ≤ x i} := by
  obtain ⟨σ, hσ⟩ := orderStat_perm x
  have hn : 0 < n := (Nat.zero_le k).trans_lt hk
  set f : ℕ → Fin n := fun j ↦ if h : j < n then σ ⟨j, h⟩ else σ ⟨0, hn⟩ with hf
  have h := Finset.card_le_card_of_injOn (s := range (k + 1))
    (t := ({i | orderStat x k ≤ x i} : Finset (Fin n))) f ?_ ?_
  · simpa using h
  · intro j hj
    have hj' : j < n := (Nat.lt_succ_iff.1 (mem_range.1 hj)).trans_lt hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hf, hj',
      dite_true]
    rw [← hσ ⟨j, hj'⟩]
    exact orderStat_anti x (Nat.lt_succ_iff.1 (mem_range.1 hj)) hk
  · intro i hi j hj hij
    have hi' : i < n := (Nat.lt_succ_iff.1 (mem_range.1 hi)).trans_lt hk
    have hj' : j < n := (Nat.lt_succ_iff.1 (mem_range.1 hj)).trans_lt hk
    simp only [hf, hi', hj', dite_true] at hij
    simpa using σ.injective hij

lemma sum_range_indicator_eq_card {Ω : Type*} (U : ℕ → Ω → ℝ) (ω : Ω) (a : ℝ) :
    ∑ i ∈ range n, (Set.Ici a).indicator (1 : ℝ → ℝ) (U i ω) =
      (#{i : Fin n | a ≤ U i ω} : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (Set.Ici a).indicator (1 : ℝ → ℝ) (U i ω)) n,
    Finset.natCast_card_filter]
  simp [Set.indicator_apply]

variable {Ω : Type*}

lemma sqrt_mul_tailEmpiricalProcess (U : ℕ → Ω → ℝ) (n : ℕ) {k : ℕ} (hk : 0 < k) (t : ℝ)
    (ω : Ω) : √(k : ℝ) * tailEmpiricalProcess U n k t ω =
      ∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator 1 (U i ω) - k * t := by
  unfold tailEmpiricalProcess
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  rw [← mul_assoc, Real.mul_self_sqrt hk'.le, mul_sub, ← mul_assoc, mul_inv_cancel₀ hk'.ne',
    one_mul]

lemma measurable_tailEmpiricalProcess_time (U : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    Measurable fun t ↦ tailEmpiricalProcess U n k t ω := by
  unfold tailEmpiricalProcess
  refine Measurable.const_mul (Measurable.sub (Measurable.const_mul (Finset.measurable_sum _
    fun i _ ↦ ?_) _) measurable_id) _
  simp only [Set.indicator_apply, Set.mem_Ici, Pi.one_apply]
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
    measurable_const

lemma abs_indicator_Ici_inv_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    |(Set.Ici c).indicator (fun t : ℝ ↦ t⁻¹) t| ≤ c⁻¹ := by
  by_cases h : c ≤ t
  · simp only [Set.indicator, Set.mem_Ici, h, ite_true]
    rw [abs_of_pos (inv_pos.2 (hc.trans_le h))]
    exact inv_anti₀ hc h
  · simp [Set.indicator, h, hc.le]

/-- The counting function divided by `t` as a sum of truncated inverses. -/
lemma sum_range_indicator_div (U : ℕ → Ω → ℝ) {n k : ℕ} (hp : (0 : ℝ) < k / n) (ω : Ω) (t : ℝ) :
    (∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω)) / t =
      ∑ i : Fin n, (Set.Ici ((1 - U i ω) / (k / n))).indicator (fun t : ℝ ↦ t⁻¹) t := by
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range
    (fun i ↦ (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω) / t) n]
  exact Finset.sum_congr rfl fun i _ ↦ indicator_Ici_one_sub_div hp _ t

/-- If no observation equals `1`, then `W_n(t) / t` is bounded. -/
lemma abs_tailEmpiricalProcess_div_le {U : ℕ → Ω → ℝ} {ω : Ω} {n k : ℕ}
    (hx : ∀ i < n, U i ω < 1) (hn : 0 < n) (hk : 0 < k) (t : ℝ) :
    |tailEmpiricalProcess U n k t ω / t| ≤
      (√(k : ℝ))⁻¹ * (∑ i : Fin n, ((1 - U i ω) / (k / n))⁻¹ + k) := by
  have hp : (0 : ℝ) < k / n := by positivity
  have hc (i : Fin n) : 0 < (1 - U i ω) / (k / n) := div_pos (by linarith [hx i i.2]) hp
  have hk' : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  have hR : 0 ≤ (√(k : ℝ))⁻¹ * (∑ i : Fin n, ((1 - U i ω) / (k / n))⁻¹ + k) :=
    mul_nonneg (inv_nonneg.2 hk'.le) (add_nonneg (Finset.sum_nonneg fun i _ ↦ (inv_pos.2
      (hc i)).le) (Nat.cast_nonneg _))
  rcases eq_or_ne t 0 with ht | ht
  · simpa [ht] using hR
  have e : tailEmpiricalProcess U n k t ω / t = (√(k : ℝ))⁻¹ *
      ((∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω)) / t - k) := by
    have hW : tailEmpiricalProcess U n k t ω = (√(k : ℝ))⁻¹ *
        (∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω) - k * t) := by
      rw [← sqrt_mul_tailEmpiricalProcess U n hk t ω]; field_simp
    rw [hW]
    field_simp
  rw [e, sum_range_indicator_div U hp ω t, abs_mul, abs_of_pos (inv_pos.2 hk')]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ (by simp)))
    (inv_nonneg.2 hk'.le)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
    abs_indicator_Ici_inv_le (hc i) t)

lemma intervalIntegrable_tailEmpiricalProcess_div {U : ℕ → Ω → ℝ} {ω : Ω} {n k : ℕ}
    (hx : ∀ i < n, U i ω < 1) (hn : 0 < n) (hk : 0 < k) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ tailEmpiricalProcess U n k t ω / t) volume a b :=
  intervalIntegrable_of_abs_le ((measurable_tailEmpiricalProcess_time U n k ω).div measurable_id)
    (abs_tailEmpiricalProcess_div_le hx hn hk) a b

/-- **The Hill statistic of the exponential sample `-log (1 - U_i)` as an integral of the tail
empirical process.** If no `U_i` equals `1` and `0 < k < n`, then with
`T = (n / k) (1 - U_{(k+1)})`,
`√k ((1/k) ∑_{j<k} (E_{(j+1)} - E_{(k+1)}) - 1) = ∫_0^T W_n(t) dt / t + √k (T - 1)`,
where `E_i = -log (1 - U_i)`. -/
theorem meanExcess_eq_integral_tailEmpiricalProcess {U : ℕ → Ω → ℝ} {ω : Ω} {n k : ℕ}
    (hx : ∀ i < n, U i ω < 1) (hk : 0 < k) (hkn : k < n) :
    √(k : ℝ) * ((k : ℝ)⁻¹ * ∑ j ∈ range k,
        (orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) j -
          orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) k) - 1) =
      (∫ t in (0 : ℝ)..((1 - orderStat (fun i : Fin n ↦ U i ω) k) / (k / n)),
        tailEmpiricalProcess U n k t ω / t) +
        √(k : ℝ) * ((1 - orderStat (fun i : Fin n ↦ U i ω) k) / (k / n) - 1) := by
  have hn : 0 < n := hk.trans hkn
  have hp : (0 : ℝ) < k / n := by positivity
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set x : Fin n → ℝ := fun i ↦ U i ω with hxdef
  set c := orderStat x k with hcdef
  set T := (1 - c) / (k / n) with hT
  have hxi (i : Fin n) : x i < 1 := hx i i.2
  have hc1 : c < 1 := by rw [hcdef, orderStat_of_lt x hkn]; exact hxi _
  have hT0 : 0 ≤ T := div_nonneg (by linarith) hp.le
  have hmono : MonotoneOn (fun u : ℝ ↦ -Real.log (1 - u)) (Set.Iio 1) := by
    intro u hu v hv huv
    exact neg_le_neg (Real.log_le_log (by simp only [Set.mem_Iio] at hv; linarith) (by linarith))
  have hy : (fun i : Fin n ↦ -Real.log (1 - U i ω)) = (fun u : ℝ ↦ -Real.log (1 - u)) ∘ x := rfl
  have hyk : orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) k = -Real.log (1 - c) := by
    rw [hy, orderStat_comp_monotoneOn hmono (fun i ↦ hxi i) hkn]
  have hci (i : Fin n) : 0 < (1 - x i) / (k / n) := div_pos (by linarith [hxi i]) hp
  -- the sum of excesses as an integral of the counting function
  have hsum : ∑ j ∈ range k, (orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) j -
      orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) k) =
      ∫ t in (0 : ℝ)..T, (∑ i ∈ range n,
        (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω)) / t := by
    rw [sum_range_orderStat_sub_eq _ hkn, hyk]
    simp_rw [sum_range_indicator_div U hp ω]
    rw [intervalIntegral.integral_finsetSum fun i _ ↦ intervalIntegrable_of_abs_le
      (measurable_inv.indicator measurableSet_Ici) (abs_indicator_Ici_inv_le (hci i)) _ _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_zero_indicator_Ici_inv hT0 (hci i)]
    congr 1
    rw [hT, div_div_div_cancel_right₀ hp.ne', Real.log_div (by linarith) (by linarith [hxi i])]
    ring
  have hint := intervalIntegrable_tailEmpiricalProcess_div hx hn hk 0 T
  have hcount : ∫ t in (0 : ℝ)..T, (∑ i ∈ range n,
      (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω)) / t =
      ∫ t in (0 : ℝ)..T, ((k : ℝ) + √(k : ℝ) * (tailEmpiricalProcess U n k t ω / t)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume 0] with t ht _
    rw [← mul_div_assoc, sqrt_mul_tailEmpiricalProcess U n hk t ω]
    field_simp
    ring
  rw [hsum, hcount, intervalIntegral.integral_add intervalIntegrable_const (hint.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero]
  have hs : √(k : ℝ) * √(k : ℝ) = k := Real.mul_self_sqrt hk'.le
  field_simp
  linear_combination (∫ t in (0 : ℝ)..T, tailEmpiricalProcess U n k t ω / t) * hs

/-- Below the random threshold `T = (n/k) (1 - U_{(k+1)})` at most `k` observations exceed
`1 - (k/n) t`. -/
lemma sum_range_indicator_le_of_lt {U : ℕ → Ω → ℝ} {ω : Ω} {n k : ℕ} (hkn : k < n) {t : ℝ}
    (ht : (k : ℝ) / n * t < 1 - orderStat (fun i : Fin n ↦ U i ω) k) :
    ∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω) ≤ k := by
  rw [sum_range_indicator_eq_card]
  have h1 := (orderStat_le_iff (fun i : Fin n ↦ U i ω) hkn
    (orderStat (fun i : Fin n ↦ U i ω) k)).1 le_rfl
  have h2 : #{i : Fin n | 1 - k / n * t ≤ U i ω} ≤ exceedCount (fun i : Fin n ↦ U i ω)
      (orderStat (fun i : Fin n ↦ U i ω) k) := by
    unfold exceedCount
    exact Finset.card_le_card fun i hi ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      linarith
  exact_mod_cast h2.trans h1

/-- Above the random threshold at least `k + 1` observations exceed `1 - (k/n) t`. -/
lemma le_sum_range_indicator_of_le {U : ℕ → Ω → ℝ} {ω : Ω} {n k : ℕ} (hkn : k < n) {t : ℝ}
    (ht : 1 - orderStat (fun i : Fin n ↦ U i ω) k ≤ (k : ℝ) / n * t) :
    (k : ℝ) + 1 ≤ ∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) (U i ω) := by
  rw [sum_range_indicator_eq_card]
  have h1 := succ_le_card_orderStat_le (fun i : Fin n ↦ U i ω) hkn
  have h2 : #{i : Fin n | orderStat (fun i : Fin n ↦ U i ω) k ≤ U i ω} ≤
      #{i : Fin n | 1 - k / n * t ≤ U i ω} :=
    Finset.card_le_card fun i hi ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      linarith
  exact_mod_cast h1.trans h2

/-- **Deterministic remainder bound.** On the event where the weighted integral near `0` is
small, the threshold `T` is within `δ` of `1`, the oscillation of `W_n` near `1` is small, and
`W_n(1)` is bounded, the Hill statistic is close to the truncated functional
`∫_ε^1 W_n(t) dt / t - W_n(1)`. -/
theorem abs_meanExcess_sub_sum_hillSummand_lt {U : ℕ → Ω → ℝ} {ω : Ω} {n k : ℕ}
    (hx : ∀ i < n, U i ω < 1) (hk : 0 < k) (hkn : k < n) {ε δ lam K : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hlam : 0 < lam)
    (h1 : ∫⁻ t in Set.Ioc 0 ε, ‖tailEmpiricalProcess U n k t ω / t‖ₑ < ENNReal.ofReal lam)
    (h2 : |tailEmpiricalProcess U n k (1 - δ) ω| < √(k : ℝ) * δ)
    (h3 : |tailEmpiricalProcess U n k (1 + δ) ω| < √(k : ℝ) * δ)
    (h4 : ∀ u ∈ Set.Icc (1 - δ) (1 - δ + 2 * δ),
      |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k (1 - δ) ω| ≤ 2 * lam)
    (h5 : |tailEmpiricalProcess U n k 1 ω| < K) :
    |√(k : ℝ) * ((k : ℝ)⁻¹ * ∑ j ∈ range k,
        (orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) j -
          orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) k) - 1) -
      ∑ i ∈ range n, hillSummand n k ε (U i ω)| < lam + 2 * δ * (K + 4 * lam) + 4 * lam := by
  have hn : 0 < n := hk.trans hkn
  have hp : (0 : ℝ) < k / n := by positivity
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk'
  set W := fun t ↦ tailEmpiricalProcess U n k t ω with hWdef
  set c := orderStat (fun i : Fin n ↦ U i ω) k with hc
  set T := (1 - c) / (k / n) with hT
  -- `√k W(t) = N(t) - k t`
  have hNW (t : ℝ) := sqrt_mul_tailEmpiricalProcess U n hk t ω
  have hlt (t : ℝ) (ht : t < T) : √(k : ℝ) * (t - 1) ≤ -W t := by
    have := sum_range_indicator_le_of_lt (U := U) (ω := ω) hkn (t := t)
      (by rw [hT, lt_div_iff₀ hp] at ht; linarith)
    have e := hNW t
    have : √(k : ℝ) * (√(k : ℝ) * (t - 1) + W t) ≤ 0 := by
      rw [mul_add, ← mul_assoc, Real.mul_self_sqrt hk'.le]; simp only [hWdef]; linarith
    nlinarith
  have hge (t : ℝ) (ht : T ≤ t) : -W t + (√(k : ℝ))⁻¹ ≤ √(k : ℝ) * (t - 1) := by
    have := le_sum_range_indicator_of_le (U := U) (ω := ω) hkn (t := t)
      (by rw [hT, div_le_iff₀ hp] at ht; linarith)
    have e := hNW t
    have hs2 : √(k : ℝ) * √(k : ℝ) = k := Real.mul_self_sqrt hk'.le
    have : 1 ≤ √(k : ℝ) * (√(k : ℝ) * (t - 1) + W t) := by
      rw [mul_add, ← mul_assoc, hs2]; simp only [hWdef]; linarith
    rw [← sub_nonneg]
    have : 0 ≤ √(k : ℝ) * (√(k : ℝ) * (t - 1) + W t) - 1 := by linarith
    have h' : √(k : ℝ) * (t - 1) - (-W t + (√(k : ℝ))⁻¹) =
        (√(k : ℝ) * (√(k : ℝ) * (t - 1) + W t) - 1) / √(k : ℝ) := by
      field_simp; ring
    rw [h']
    positivity
  -- the threshold is close to `1`
  have hTlow : 1 - δ < T := by
    by_contra h
    push Not at h
    have := hge (1 - δ) h
    have hW := (abs_lt.1 h2).2
    have : √(k : ℝ) * δ < W (1 - δ) + (√(k : ℝ))⁻¹ - (√(k : ℝ))⁻¹ := by
      simp only [hWdef] at *; nlinarith [inv_pos.2 hsk]
    have : √(k : ℝ) * δ ≤ -W (1 - δ) := by nlinarith
    linarith [abs_lt.1 h2]
  have hTup : T ≤ 1 + δ := by
    by_contra h
    push Not at h
    have := hlt (1 + δ) h
    have hW := abs_lt.1 h3
    simp only [hWdef] at *
    nlinarith
  -- the oscillation near `1`
  have hclose (u : ℝ) (hu : u ∈ Set.Icc (1 - δ) (1 + δ)) : |W u - W 1| ≤ 4 * lam := by
    have hu' : u ∈ Set.Icc (1 - δ) (1 - δ + 2 * δ) := ⟨hu.1, by linarith [hu.2]⟩
    have h1' : (1 : ℝ) ∈ Set.Icc (1 - δ) (1 - δ + 2 * δ) := ⟨by linarith, by linarith⟩
    have e1 := h4 u hu'
    have e2 := h4 1 h1'
    calc |W u - W 1| = |(W u - W (1 - δ)) - (W 1 - W (1 - δ))| := by ring_nf
      _ ≤ |W u - W (1 - δ)| + |W 1 - W (1 - δ)| := abs_sub _ _
      _ ≤ 2 * lam + 2 * lam := add_le_add e1 e2
      _ = 4 * lam := by ring
  -- the threshold term
  have hup : √(k : ℝ) * (T - 1) ≤ -W 1 + 4 * lam := by
    by_contra h
    push Not at h
    set s := 1 + (-W 1 + 4 * lam) / √(k : ℝ) with hs
    have hsT : s < T := by
      rw [hs]
      have : (-W 1 + 4 * lam) / √(k : ℝ) < T - 1 := by rw [div_lt_iff₀ hsk]; linarith
      linarith
    set t := (max (1 - δ) s + T) / 2 with ht
    have ht1 : max (1 - δ) s < t := by rw [ht]; linarith [max_lt hTlow hsT]
    have htT : t < T := by rw [ht]; linarith [max_lt hTlow hsT]
    have e1 := hlt t htT
    have e2 := hclose t ⟨(le_max_left _ _).trans ht1.le, htT.le.trans hTup⟩
    have e3 : -W 1 + 4 * lam < √(k : ℝ) * (t - 1) := by
      have : s < t := (le_max_right _ _).trans_lt ht1
      rw [hs] at this
      have : (-W 1 + 4 * lam) / √(k : ℝ) < t - 1 := by linarith
      rw [div_lt_iff₀ hsk] at this
      linarith
    linarith [(abs_le.1 e2).1]
  have hlow : -W 1 - 4 * lam ≤ √(k : ℝ) * (T - 1) := by
    have e1 := hge T le_rfl
    have e2 := hclose T ⟨hTlow.le, hTup⟩
    linarith [(abs_le.1 e2).2, inv_pos.2 hsk]
  -- the integrals
  have hI := intervalIntegrable_tailEmpiricalProcess_div hx hn hk
  have hM := meanExcess_eq_integral_tailEmpiricalProcess hx hk hkn
  have hA := sum_hillSummand_eq U ω hn hk hε0 hε1
  rw [hM, hA, ← intervalIntegral.integral_add_adjacent_intervals (hI 0 ε) (hI ε T),
    ← intervalIntegral.integral_add_adjacent_intervals (hI ε 1) (hI 1 T)]
  set I0 := ∫ t in (0 : ℝ)..ε, tailEmpiricalProcess U n k t ω / t
  set I1 := ∫ t in (1 : ℝ)..T, tailEmpiricalProcess U n k t ω / t
  have hI0 : |I0| < lam := by
    have := (enorm_integral_le_lintegral_enorm _).trans_lt h1
    rw [← intervalIntegral.integral_of_le hε0.le, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_lt_ofReal_iff hlam] at this
    exact this
  have hI1 : |I1| ≤ 2 * δ * (K + 4 * lam) := by
    have hb : ∀ t ∈ Set.uIoc 1 T, ‖tailEmpiricalProcess U n k t ω / t‖ ≤ 2 * (K + 4 * lam) := by
      intro t ht
      have ht' : t ∈ Set.Icc (1 - δ) (1 + δ) := by
        rcases le_total 1 T with h | h
        · rw [Set.uIoc_of_le h] at ht; exact ⟨by linarith [ht.1], ht.2.trans hTup⟩
        · rw [Set.uIoc_of_ge h] at ht; exact ⟨hTlow.le.trans ht.1.le, by linarith [ht.2]⟩
      have ht0 : 1 / 2 ≤ t := by linarith [ht'.1]
      have hWt : |W t| ≤ K + 4 * lam := by
        have := hclose t ht'
        have := abs_sub_abs_le_abs_sub (W t) (W 1)
        linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < t by linarith),
        div_le_iff₀ (by linarith)]
      have : 0 ≤ K + 4 * lam := (abs_nonneg _).trans hWt
      simp only [hWdef] at hWt
      nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at this
    have hT1 : |T - 1| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
    calc |I1| ≤ 2 * (K + 4 * lam) * |T - 1| := this
      _ ≤ 2 * (K + 4 * lam) * δ := by
          refine mul_le_mul_of_nonneg_left hT1 ?_
          have := (abs_nonneg _).trans_lt h5
          positivity
      _ = 2 * δ * (K + 4 * lam) := by ring
  have hR : |√(k : ℝ) * (T - 1) + W 1| ≤ 4 * lam := abs_le.2 ⟨by linarith, by linarith⟩
  rw [← hc, ← hT]
  calc _ = |I0 + I1 + (√(k : ℝ) * (T - 1) + W 1)| := by congr 1; simp only [hWdef]; ring
    _ ≤ |I0| + |I1| + |√(k : ℝ) * (T - 1) + W 1| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ < lam + 2 * δ * (K + 4 * lam) + 4 * lam := by linarith

end Representation

/-! ### Moment bounds for the tail empirical process -/

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {U : ℕ → Ω → ℝ}

lemma integrable_tailEmpiricalProcess_pow (hU : ∀ i, Measurable (U i)) (n k : ℕ) (t : ℝ)
    (j : ℕ) : Integrable (fun ω ↦ tailEmpiricalProcess U n k t ω ^ j) P :=
  integrable_pow_of_abs_le (measurable_tailEmpiricalProcess hU n k t)
    (fun ω ↦ abs_tailEmpiricalProcess_le U n k t ω) j

/-- The variance of the tail empirical process: `E W_n(t) ^ 2 = t - (k/n) t ^ 2`. -/
theorem integral_tailEmpiricalProcess_sq (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) (htp : (k : ℝ) / n * t ≤ 1) :
    ∫ ω, tailEmpiricalProcess U n k t ω ^ 2 ∂P = t - k / n * t ^ 2 := by
  set τ : Unit → ℝ≥0 := fun _ ↦ ⟨t, ht⟩
  set a : Unit → ℝ := fun _ ↦ 1
  set X : ℕ → Ω → ℝ := fun i ω ↦ tailSummand τ a n k (U i ω) with hX
  have hXm (i : ℕ) : Measurable (X i) := (measurable_tailSummand τ a n k).comp (hU i)
  have hXind : iIndepFun X P := hind.comp (fun _ ↦ tailSummand τ a n k)
    (fun _ ↦ measurable_tailSummand τ a n k)
  have hXC (i : ℕ) (ω : Ω) : |X i ω| ≤ (√(k : ℝ))⁻¹ * ∑ s : Unit, |a s| * (1 + k / n * τ s) :=
    abs_tailSummand_le τ a n k _
  have hmap (i : ℕ) {g : ℝ → ℝ} (hg : Measurable g) :
      ∫ ω, g (X i ω) ∂P = ∫ u, g (tailSummand τ a n k u) ∂μU := by
    rw [show μU = P.map (U i) from (hlaw i).symm, integral_map (hU i).aemeasurable
      (f := fun u ↦ g (tailSummand τ a n k u))
      (hg.comp (measurable_tailSummand τ a n k)).aestronglyMeasurable]
  have hX0 (i : ℕ) : ∫ ω, X i ω ∂P = 0 := by
    have := hmap i measurable_id
    simp only [id] at this
    rw [this, integral_tailSummand τ a fun _ ↦ htp]
  have hW (ω : Ω) : tailEmpiricalProcess U n k t ω = ∑ i ∈ range n, X i ω := by
    have := sum_mul_tailEmpiricalProcess_eq τ a U hn.ne' k ω
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, a] at this
    exact this
  have h2 (i : ℕ) : ∫ ω, X i ω ^ 2 ∂P = ∫ u, tailSummand τ a n k u ^ 2 ∂μU :=
    hmap i (g := fun x ↦ x ^ 2) (measurable_id.pow_const 2)
  simp_rw [hW]
  rw [integral_sum_range_sq_eq hXm hXind hXC hX0 n]
  simp_rw [h2]
  rw [Finset.sum_const, card_range, nsmul_eq_mul,
    mul_integral_tailSummand_sq τ a hn.ne' hk.ne' fun _ ↦ htp]
  simp only [a, τ, Finset.univ_unique, Finset.sum_singleton, one_mul, min_self]
  change t - (k : ℝ) / n * t * t = _
  ring

lemma integral_tailEmpiricalProcess_sq_le (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) (htp : (k : ℝ) / n * t ≤ 1) :
    ∫ ω, tailEmpiricalProcess U n k t ω ^ 2 ∂P ≤ t := by
  rw [integral_tailEmpiricalProcess_sq hU hind hlaw hn hk ht htp]
  have : 0 ≤ (k : ℝ) / n * t ^ 2 := by positivity
  linarith

omit [IsProbabilityMeasure P] in
/-- Chebyshev's inequality. -/
lemma measureReal_le_abs_le_integral_sq_div {X : Ω → ℝ}
    (hint : Integrable (fun ω ↦ X ω ^ 2) P) {a : ℝ} (ha : 0 < a) :
    P.real {ω | a ≤ |X ω|} ≤ (∫ ω, X ω ^ 2 ∂P) / a ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg (X ω)) hint (a ^ 2)
  have e : {ω | a ≤ |X ω|} = {ω | a ^ 2 ≤ X ω ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [← sq_abs (X ω)]
    exact (pow_le_pow_iff_left₀ ha.le (abs_nonneg _) two_ne_zero).symm
  rw [e, le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- `E |W_n(t)| ≤ √t`. -/
lemma integral_abs_tailEmpiricalProcess_le (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) {t : ℝ} (ht : 0 < t) (htp : (k : ℝ) / n * t ≤ 1) :
    ∫ ω, |tailEmpiricalProcess U n k t ω| ∂P ≤ √t := by
  have hs : 0 < √t := Real.sqrt_pos.2 ht
  have hle (ω : Ω) : |tailEmpiricalProcess U n k t ω| ≤
      (tailEmpiricalProcess U n k t ω ^ 2 / √t + √t) / 2 := by
    have h := sq_nonneg (|tailEmpiricalProcess U n k t ω| - √t)
    rw [← sq_abs (tailEmpiricalProcess U n k t ω)]
    rw [le_div_iff₀ two_pos, div_add' _ _ _ hs.ne', le_div_iff₀ hs]
    nlinarith
  have hi2 := integrable_tailEmpiricalProcess_pow (P := P) hU n k t 2
  have hi1 := integrable_tailEmpiricalProcess_pow (P := P) hU n k t 1
  simp only [pow_one] at hi1
  refine (integral_mono hi1.abs (((hi2.div_const _).add (integrable_const _)).div_const 2)
    hle).trans ?_
  rw [integral_div]
  simp only [Pi.add_apply]
  rw [integral_add (hi2.div_const _) (integrable_const _), integral_div,
    integral_const, probReal_univ, one_smul, div_le_iff₀ two_pos]
  have := integral_tailEmpiricalProcess_sq_le hU hind hlaw hn hk ht.le htp
  have h3 : (∫ ω, tailEmpiricalProcess U n k t ω ^ 2 ∂P) / √t ≤ √t := by
    rw [div_le_iff₀ hs, Real.mul_self_sqrt ht.le]; exact this
  linarith

lemma measurable_tailEmpiricalProcess_uncurry (hU : ∀ i, Measurable (U i)) (n k : ℕ) :
    Measurable fun q : Ω × ℝ ↦ tailEmpiricalProcess U n k q.2 q.1 := by
  unfold tailEmpiricalProcess
  refine Measurable.const_mul (Measurable.sub (Measurable.const_mul (Finset.measurable_sum _
    fun i _ ↦ ?_) _) measurable_snd) _
  simp only [Set.indicator_apply, Set.mem_Ici, Pi.one_apply]
  exact Measurable.ite (measurableSet_le (by fun_prop) ((hU i).comp measurable_fst))
    measurable_const measurable_const

/-- `∫_0^ε t^{-1/2} dt = 2 √ε`, as a lower integral. -/
lemma lintegral_Ioc_rpow_neg_half {ε : ℝ} (hε : 0 ≤ ε) :
    ∫⁻ t in Set.Ioc 0 ε, ENNReal.ofReal (t ^ (-(1 / 2) : ℝ)) = ENNReal.ofReal (2 * √ε) := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(1 / 2) : ℝ)) volume 0 ε :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε).1 hi)
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht ↦ Real.rpow_nonneg ht.1.le _)),
    ← intervalIntegral.integral_of_le hε, integral_rpow (Or.inl (by norm_num))]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.zero_rpow (by norm_num)]
  norm_num
  ring

/-- **The singularity at `0`**: `E ∫_0^ε |W_n(t)| dt / t ≤ 2 √ε`. -/
theorem lintegral_lintegral_tailEmpiricalProcess_div_le (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {ε : ℝ} (hε : 0 ≤ ε) (hεp : (k : ℝ) / n * ε ≤ 1) :
    ∫⁻ ω, (∫⁻ t in Set.Ioc 0 ε, ‖tailEmpiricalProcess U n k t ω / t‖ₑ) ∂P ≤
      ENNReal.ofReal (2 * √ε) := by
  have hm := measurable_tailEmpiricalProcess_uncurry hU n k
  rw [lintegral_lintegral_swap (f := fun ω t ↦ ‖tailEmpiricalProcess U n k t ω / t‖ₑ)
    ((hm.div measurable_snd).enorm.aemeasurable), ← lintegral_Ioc_rpow_neg_half hε]
  refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
  have hp : (k : ℝ) / n * t ≤ 1 := (mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans hεp
  have hi : Integrable (fun ω ↦ tailEmpiricalProcess U n k t ω / t) P := by
    have := integrable_tailEmpiricalProcess_pow (P := P) hU n k t 1
    simp only [pow_one] at this
    exact this.div_const t
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [Real.norm_eq_abs, abs_div, abs_of_pos ht.1]
  rw [integral_div, Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow, div_le_iff₀ ht.1]
  refine (integral_abs_tailEmpiricalProcess_le hU hind hlaw hn hk ht.1 hp).trans_eq ?_
  have hs : 0 < √t := Real.sqrt_pos.2 ht.1
  field_simp
  rw [Real.sq_sqrt ht.1.le]

end Moments

/-! ### The remainder is negligible -/

section Remainder

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {U : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma measure_exists_one_le_eq_zero (hU : ∀ i, Measurable (U i))
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) (n : ℕ) :
    P {ω | ∃ i < n, 1 ≤ U i ω} = 0 := by
  have hnull (i : ℕ) : P {ω | 1 ≤ U i ω} = 0 := by
    have h := measureReal_uniform_Ici (x := 0) le_rfl zero_le_one
    rw [sub_zero, measureReal_eq_zero_iff] at h
    rw [show {ω | 1 ≤ U i ω} = U i ⁻¹' Set.Ici 1 from rfl, ← Measure.map_apply (hU i)
      measurableSet_Ici, hlaw i]
    exact h
  refine measure_mono_null (fun ω hω ↦ ?_) ((measure_biUnion_null_iff
    (Finset.range n).countable_toSet).2 fun i _ ↦ hnull i)
  obtain ⟨i, hi, h⟩ := hω
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi)) h

lemma measureReal_le_abs_tailEmpiricalProcess_le (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) (htp : (k : ℝ) / n * t ≤ 1) {a : ℝ}
    (ha : 0 < a) :
    P.real {ω | a ≤ |tailEmpiricalProcess U n k t ω|} ≤ t / a ^ 2 :=
  (measureReal_le_abs_le_integral_sq_div (integrable_tailEmpiricalProcess_pow hU n k t 2) ha).trans
    (div_le_div_of_nonneg_right (integral_tailEmpiricalProcess_sq_le hU hind hlaw hn hk ht htp)
      (sq_nonneg _))

lemma measureReal_ofReal_le_lintegral_le (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {ε : ℝ} (hε : 0 ≤ ε) (hεp : (k : ℝ) / n * ε ≤ 1) {lam : ℝ}
    (hlam : 0 < lam) :
    P.real {ω | ENNReal.ofReal lam ≤
      ∫⁻ t in Set.Ioc 0 ε, ‖tailEmpiricalProcess U n k t ω / t‖ₑ} ≤ 2 * √ε / lam := by
  have hm : Measurable fun ω ↦ ∫⁻ t in Set.Ioc 0 ε, ‖tailEmpiricalProcess U n k t ω / t‖ₑ :=
    Measurable.lintegral_prod_right' (f := fun q : Ω × ℝ ↦ ‖tailEmpiricalProcess U n k q.2 q.1 /
      q.2‖ₑ) ((measurable_tailEmpiricalProcess_uncurry hU n k).div measurable_snd).enorm
  have h := meas_ge_le_lintegral_div hm.aemeasurable (ENNReal.ofReal_pos.2 hlam).ne'
    ENNReal.ofReal_ne_top (μ := P)
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans ?_)
  rw [ENNReal.ofReal_div_of_pos hlam]
  exact ENNReal.div_le_div_right
    (lintegral_lintegral_tailEmpiricalProcess_div_le hU hind hlaw hn hk hε hεp) _

/-- The oscillation of `W_n` on `[1 - δ, 1 + δ]` is small, up to a term `O(δ²)`. -/
lemma eventually_measureReal_osc_le (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {δ lam θ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hlam : 0 < lam) (hθ : 0 < θ) :
    ∀ᶠ n in atTop, P.real {ω | ∃ u ∈ Set.Icc (1 - δ) (1 - δ + 2 * δ),
      2 * lam < |tailEmpiricalProcess U n (k n) u ω - tailEmpiricalProcess U n (k n) (1 - δ) ω|} ≤
      8 ^ 4 / lam ^ 4 * (84 * (2 * δ) ^ 2) + θ := by
  set C : ℝ := 8 ^ 4 / lam ^ 4 with hC
  have hC0 : 0 < C := by positivity
  have hq (n : ℕ) : ∃ q : ℕ, √(k n : ℝ) * (2 * δ) / lam ≤ 2 ^ q ∧
      (2 : ℝ) ^ q ≤ 2 * (1 + √(k n : ℝ) * (2 * δ) / lam) := by
    obtain ⟨q₀, h1, h2⟩ := exists_nat_pow_near (le_max_left 1 (√(k n : ℝ) * (2 * δ) / lam))
      (one_lt_two : (1 : ℝ) < 2)
    refine ⟨q₀ + 1, (le_max_right _ _).trans h2.le, ?_⟩
    rw [pow_succ]
    have : max 1 (√(k n : ℝ) * (2 * δ) / lam) ≤ 1 + √(k n : ℝ) * (2 * δ) / lam :=
      max_le (by linarith [show 0 ≤ √(k n : ℝ) * (2 * δ) / lam by positivity]) (by linarith)
    linarith
  choose q hq1 hq2 using hq
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hsmall : Tendsto (fun n ↦ C * (8 * (1 + √(k n : ℝ) * (2 * δ) / lam) * (2 * δ) / k n))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ (k n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
    have h2 : Tendsto (fun n ↦ (√(k n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hkR)
    have h3 : Tendsto (fun n ↦ C * (8 * (2 * δ) * ((k n : ℝ)⁻¹ +
        (√(k n : ℝ))⁻¹ * (2 * δ) / lam))) atTop
        (𝓝 (C * (8 * (2 * δ) * (0 + 0 * (2 * δ) / lam)))) :=
      ((h1.add ((h2.mul_const _).div_const _)).const_mul _).const_mul _
    simp only [zero_mul, zero_div, add_zero, mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [hk.eventually_gt_atTop 0] with n hn
    have hk' : (0 : ℝ) < k n := Nat.cast_pos.2 hn
    have hs : √(k n : ℝ) * √(k n : ℝ) = k n := Real.mul_self_sqrt hk'.le
    have hs0 : √(k n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hk').ne'
    field_simp
    linear_combination (-(2 * δ)) * hs
  have hkn1 : ∀ᶠ n in atTop, (k n : ℝ) / n ≤ 1 / 2 :=
    hkn.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hsmall.eventually (ge_mem_nhds hθ), hkn1, eventually_gt_atTop 0,
    hk.eventually_gt_atTop 0] with n hn hkn' hn0 hk0
  have hqn : √(k n : ℝ) * (2 * δ / 2 ^ q n) ≤ lam := by
    have h1 := hq1 n
    rw [div_le_iff₀ hlam] at h1
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  have hp : (k n : ℝ) / n * (1 - δ + 2 * δ) ≤ 1 := by
    have : 1 - δ + 2 * δ ≤ 3 / 2 := by linarith
    have h0 : (0 : ℝ) ≤ k n / n := by positivity
    nlinarith
  have hPE := measureReal_exists_abs_tailEmpiricalProcess_sub_gt_le hU hind hlaw hn0.ne'
    (a := 1 - δ) (L := 2 * δ) (by linarith) (by linarith) hp hlam (q n) hqn
  refine hPE.trans ?_
  rw [mul_add]
  have h2 : (2 : ℝ) ^ (q n + 2) * (2 * δ) / k n ≤ 8 * (1 + √(k n : ℝ) * (2 * δ) / lam) *
      (2 * δ) / k n := by
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    rw [pow_add]
    nlinarith [hq2 n]
  have := (mul_le_mul_of_nonneg_left h2 hC0.le).trans hn
  rw [← hC]
  linarith

/-- The Hill statistic of the exponential sample `-log (1 - U_i)`. -/
noncomputable def meanExcessStat (U : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  √(k : ℝ) * ((k : ℝ)⁻¹ * ∑ j ∈ range k,
    (orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) j -
      orderStat (fun i : Fin n ↦ -Real.log (1 - U i ω)) k) - 1)

omit [IsProbabilityMeasure P] in
lemma measurable_meanExcessStat (hU : ∀ i, Measurable (U i)) (n k : ℕ) :
    Measurable (meanExcessStat U n k) := by
  have hv : ∀ i : Fin n, Measurable fun ω ↦ -Real.log (1 - U i ω) := fun i ↦
    ((measurable_const.sub (hU i)).log).neg
  unfold meanExcessStat
  exact measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun j _ ↦
    (measurable_orderStat hv j).sub (measurable_orderStat hv k))).sub measurable_const)

/-- **The Hill statistic is asymptotically the truncated functional of the tail empirical
process**: if `ε n → 0`, then
`√k ((1/k) ∑_{j<k} (E_{(j+1)} - E_{(k+1)}) - 1) - (∫_{ε n}^1 W_n(t) dt / t - W_n(1)) → 0`
in probability. The proof splits the difference into `∫_0^ε W_n / t` (small in `L¹`),
`∫_1^T W_n / t` and `√k (T - 1) + W_n(1)`, where `T = (n/k)(1 - U_{(k+1)}) → 1`; the last two
are controlled by the maximal inequality for `W_n` near `1`. -/
theorem tendstoInMeasure_meanExcessStat_sub_sum_hillSummand (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ meanExcessStat U n (k n) ω -
      ∑ i ∈ range n, hillSummand n (k n) (ε n) (U i ω)) atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro η hη
  suffices key : ∀ θ > 0, ∀ᶠ n in atTop, P.real {ω | η ≤ ‖meanExcessStat U n (k n) ω -
      ∑ i ∈ range n, hillSummand n (k n) (ε n) (U i ω) - (0 : Ω → ℝ) ω‖} ≤ θ by
    refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦
      ha.trans_le measureReal_nonneg, fun a ha ↦ ?_⟩
    filter_upwards [key (a / 2) (half_pos ha)] with n hn
    exact hn.trans_lt (half_lt_self ha)
  intro θ hθ
  -- the parameters
  set lam : ℝ := η / 10 with hlamdef
  have hlam : 0 < lam := by positivity
  set K : ℝ := 10 / θ + 1 with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith [show 0 < 10 / θ by positivity]
  have hK : 1 / K ^ 2 ≤ θ / 10 := by
    have h1 : 10 / θ ≤ K ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hθ] at h1
    nlinarith
  set δ : ℝ := min (1 / 2) (min (η / (4 * (K + 4 * lam))) (θ * lam ^ 4 / (3360 * 8 ^ 4)))
    with hδdef
  have hδ0 : 0 < δ := by
    have : 0 < K + 4 * lam := by positivity
    positivity
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδη : δ ≤ η / (4 * (K + 4 * lam)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδθ : δ ≤ θ * lam ^ 4 / (3360 * 8 ^ 4) := (min_le_right _ _).trans (min_le_right _ _)
  have hsum : lam + 2 * δ * (K + 4 * lam) + 4 * lam ≤ η := by
    have hK4 : 0 < K + 4 * lam := by positivity
    have : 2 * δ * (K + 4 * lam) ≤ η / 2 := by
      have := mul_le_mul_of_nonneg_right hδη hK4.le
      have e : η / (4 * (K + 4 * lam)) * (K + 4 * lam) = η / 4 := by field_simp
      linarith
    linarith
  have hosc : 8 ^ 4 / lam ^ 4 * (84 * (2 * δ) ^ 2) ≤ θ / 10 := by
    have hδ2 : δ ^ 2 ≤ δ := by nlinarith
    have : 8 ^ 4 / lam ^ 4 * (84 * (2 * δ) ^ 2) ≤ 8 ^ 4 / lam ^ 4 * (336 * δ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity); nlinarith
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδθ
    nlinarith
  -- eventual conditions
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hsqrt : Tendsto (fun n ↦ 2 * √(ε n) / lam) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hεlim).const_mul 2 |>.div_const lam
    simpa using this
  have hkδ : Tendsto (fun n ↦ 3 / ((k n : ℝ) * δ ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hkR.atTop_mul_const (by positivity))
  filter_upwards [hk.eventually_gt_atTop 0, eventually_lt_of_tendsto_div hkn,
    hkn.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hsqrt.eventually (ge_mem_nhds (show 0 < θ / 10 by positivity)),
    hkδ.eventually (ge_mem_nhds (show 0 < θ / 5 by positivity)),
    eventually_measureReal_osc_le hU hind hlaw hk hkn hδ0 hδ1 hlam
      (show 0 < θ / 10 by positivity)] with n hk0 hkn' hp hB1 hB23 hB4
  have hn0 : 0 < n := hk0.trans hkn'
  have hp0 : (0 : ℝ) ≤ k n / n := by positivity
  have hpt (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 3 / 2) : (k n : ℝ) / n * t ≤ 1 := by nlinarith
  set W := fun t ω ↦ tailEmpiricalProcess U n (k n) t ω with hWdef
  -- the bad events
  set G := {ω | ∃ i < n, 1 ≤ U i ω}
  set B1 := {ω | ENNReal.ofReal lam ≤ ∫⁻ t in Set.Ioc 0 (ε n), ‖W t ω / t‖ₑ}
  set B2 := {ω | √(k n : ℝ) * δ ≤ |W (1 - δ) ω|}
  set B3 := {ω | √(k n : ℝ) * δ ≤ |W (1 + δ) ω|}
  set B4 := {ω | ∃ u ∈ Set.Icc (1 - δ) (1 - δ + 2 * δ), 2 * lam < |W u ω - W (1 - δ) ω|}
  set B5 := {ω | K ≤ |W 1 ω|}
  have hsub : {ω | η ≤ ‖meanExcessStat U n (k n) ω -
      ∑ i ∈ range n, hillSummand n (k n) (ε n) (U i ω) - (0 : Ω → ℝ) ω‖} ⊆
      G ∪ B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 := by
    intro ω hω
    by_contra hcon
    simp only [G, B1, B2, B3, B4, B5, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists,
      not_and, not_le, not_lt] at hcon
    obtain ⟨⟨⟨⟨⟨hG, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hcon
    have := abs_meanExcess_sub_sum_hillSummand_lt (U := U) (ω := ω) hG hk0 hkn' (hε0 n) (hε1 n)
      hδ0 hδ1 hlam h1 h2 h3 h4 h5 (K := K)
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω
    unfold meanExcessStat at hω
    linarith
  -- the probabilities
  have hPG : P.real G = 0 := by
    rw [measureReal_eq_zero_iff]; exact measure_exists_one_le_eq_zero hU hlaw n
  have hP1 : P.real B1 ≤ θ / 10 :=
    (measureReal_ofReal_le_lintegral_le hU hind hlaw hn0 hk0 (hε0 n).le
      (hpt _ (hε0 n).le (by linarith [hε1 n])) hlam).trans hB1
  have hsk : 0 < √(k n : ℝ) * δ := by
    have : (0 : ℝ) < k n := Nat.cast_pos.2 hk0
    positivity
  have hsq : (√(k n : ℝ) * δ) ^ 2 = k n * δ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hP2 : P.real B2 ≤ 1 / (k n * δ ^ 2) := by
    refine (measureReal_le_abs_tailEmpiricalProcess_le hU hind hlaw hn0 hk0 (by linarith)
      (hpt _ (by linarith) (by linarith)) hsk).trans ?_
    rw [hsq]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hP3 : P.real B3 ≤ 2 / (k n * δ ^ 2) := by
    refine (measureReal_le_abs_tailEmpiricalProcess_le hU hind hlaw hn0 hk0 (by linarith)
      (hpt _ (by linarith) (by linarith)) hsk).trans ?_
    rw [hsq]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hP5 : P.real B5 ≤ θ / 10 := by
    refine (measureReal_le_abs_tailEmpiricalProcess_le hU hind hlaw hn0 hk0 zero_le_one
      (hpt _ zero_le_one (by norm_num)) (by linarith : (0 : ℝ) < K)).trans hK
  have h23 : 1 / ((k n : ℝ) * δ ^ 2) + 2 / (k n * δ ^ 2) ≤ θ / 5 := by
    rw [← add_div]; norm_num; exact hB23
  have u1 := measureReal_union_le (μ := P) (G ∪ B1 ∪ B2 ∪ B3 ∪ B4) B5
  have u2 := measureReal_union_le (μ := P) (G ∪ B1 ∪ B2 ∪ B3) B4
  have u3 := measureReal_union_le (μ := P) (G ∪ B1 ∪ B2) B3
  have u4 := measureReal_union_le (μ := P) (G ∪ B1) B2
  have u5 := measureReal_union_le (μ := P) G B1
  have hP4 := hB4
  linarith [measureReal_mono (μ := P) hsub]

end Remainder

/-! ### Asymptotic normality of the Hill estimator via the tail empirical process -/

section Normality

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Central limit theorem for the Hill statistic via the tail empirical process.** If the
`U_i` are i.i.d. uniform on `[0, 1]`, `k → ∞` and `k / n → 0`, then the Hill statistic of the
standard exponential sample `E_i = -log (1 - U_i)`,
`√k ((1/k) ∑_{j<k} (E_{(j+1)} - E_{(k+1)}) - 1)`, converges in distribution to `N(0, 1)`.

The proof is the tail empirical process route of [de Haan–Ferreira, §5.1–5.2]: the statistic is
`∫_0^T W_n(t) dt / t + √k (T - 1)` with `T = (n/k) (1 - U_{(k+1)})`
(`meanExcess_eq_integral_tailEmpiricalProcess`); up to a remainder that is negligible in
probability (`tendstoInMeasure_meanExcessStat_sub_sum_hillSummand`) this is the truncated
functional `∫_ε^1 W_n(t) dt / t - W_n(1)` with `ε = ε_n → 0`, which is asymptotically
`N(0, 1)` (`tendstoInDistribution_sum_hillSummand`); in the limit this is the Gaussian variable
`∫_0^1 W(t) dt / t - W(1)` of a Brownian motion `W`. -/
theorem tendstoInDistribution_meanExcessStat {U : ℕ → Ω → ℝ} (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ↦ meanExcessStat U n (k n)) atTop Z (fun _ ↦ P) P' := by
  set ε : ℕ → ℝ := fun n ↦ Real.exp (-√(√(k n : ℝ))) with hεdef
  have hε0 (n : ℕ) : 0 < ε n := Real.exp_pos _
  have hε1 (n : ℕ) : ε n ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hss : Tendsto (fun n ↦ √(√(k n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hkR)
  have hεlim : Tendsto ε atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hss
  have hlog : Tendsto (fun n ↦ Real.log (ε n) / √(k n : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hss).neg
    rw [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [hk.eventually_gt_atTop 0] with n hn
    have hk' : (0 : ℝ) < k n := Nat.cast_pos.2 hn
    have h1 : 0 < √(√(k n : ℝ)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hk')
    have h2 : √(√(k n : ℝ)) * √(√(k n : ℝ)) = √(k n : ℝ) :=
      Real.mul_self_sqrt (Real.sqrt_nonneg _)
    simp only [Function.comp_apply, hεdef, Real.log_exp]
    set r := √(√(k n : ℝ))
    rw [← h2]
    field_simp
  have hA := tendstoInDistribution_sum_hillSummand hU hind hlaw hk hkn hε0 hε1 hεlim hlog
  simp only [mul_zero, zero_mul, add_zero, Real.toNNReal_one] at hA
  have hR := tendstoInMeasure_meanExcessStat_sub_sum_hillSummand hU hind hlaw hk hkn hε0 hε1 hεlim
  have hM := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun n ↦ meanExcessStat U n (k n)) id hA hR
    (fun n ↦ (measurable_meanExcessStat hU n (k n)).aemeasurable)
  exact hM.congr_limit hZ.aemeasurable (by rw [Measure.map_id, hZ.map_eq])

/-- The law of `-log (1 - U)`, `U` uniform on `[0, 1]`, is the standard exponential law. -/
theorem map_uniform_neg_log_one_sub :
    μU.map (fun u ↦ -Real.log (1 - u)) = expMeasure 1 := by
  have hg : Measurable fun u : ℝ ↦ -Real.log (1 - u) := by fun_prop
  refine measure_eq_of_Ioi fun a ↦ ?_
  rw [Measure.map_apply hg measurableSet_Ioi, Measure.restrict_apply (hg measurableSet_Ioi)]
  rcases le_or_gt 0 a with ha | ha
  · have e : (fun u : ℝ ↦ -Real.log (1 - u)) ⁻¹' Set.Ioi a ∩ Set.Icc 0 1 =
        Set.Ioo (1 - Real.exp (-a)) 1 := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioo]
      have hexp : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      constructor
      · rintro ⟨h, h0, h1⟩
        rcases h1.eq_or_lt with h1 | h1
        · subst h1; simp at h; linarith
        have h1' : 0 < 1 - u := by linarith
        have : Real.log (1 - u) < -a := by linarith
        rw [Real.log_lt_iff_lt_exp h1'] at this
        exact ⟨by linarith, h1⟩
      · rintro ⟨h0, h1⟩
        have h1' : 0 < 1 - u := by linarith
        refine ⟨?_, by linarith [Real.exp_pos (-a)], h1.le⟩
        have : Real.log (1 - u) < -a := by
          rw [Real.log_lt_iff_lt_exp h1']; linarith
        linarith
    rw [e, Real.volume_Ioo, expMeasure_Ioi ha]
    congr 1
    ring
  · have e : (fun u : ℝ ↦ -Real.log (1 - u)) ⁻¹' Set.Ioi a ∩ Set.Icc 0 1 = Set.Icc 0 1 := by
      refine Set.inter_eq_right.2 fun u hu ↦ ?_
      simp only [Set.mem_preimage, Set.mem_Ioi]
      have : Real.log (1 - u) ≤ 0 := Real.log_nonpos (by linarith [hu.2]) (by linarith [hu.1])
      linarith
    rw [e, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
    refine le_antisymm ?_ prob_le_one
    calc (1 : ℝ≥0∞) = expMeasure 1 (Set.Ioi 0) := by
          rw [expMeasure_Ioi le_rfl, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
      _ ≤ _ := measure_mono (Set.Ioi_subset_Ioi ha.le)

/-- **Central limit theorem for the mean top excess of an exponential sample, via the tail
empirical process.** This is `tendstoInDistribution_meanExcess` (proved there with the Rényi
representation) under the additional assumption `k / n → 0`, proved through the uniform tail
empirical process: the sample `E_i` has the law of `-log (1 - U_i)` with `U_i` uniform, and
`tendstoInDistribution_meanExcessStat` applies. -/
theorem tendstoInDistribution_meanExcess_of_tailEmpiricalProcess {E : ℕ → Ω → ℝ}
    (hEm : ∀ i, Measurable (E i)) (hE : ∀ i, HasLaw (E i) (expMeasure 1) P)
    (hind : iIndepFun E P) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω ↦ √(k n : ℝ) * (((k n : ℝ))⁻¹ * ∑ i ∈ range (k n),
        (orderStat (fun i : Fin n ↦ E i ω) i - orderStat (fun i : Fin n ↦ E i ω) (k n)) - 1))
      atTop Z (fun _ ↦ P) P' := by
  obtain ⟨Ω₀, _, P₀, V, hVm, hV, hindV, hP₀⟩ := exists_iid ℕ μU
  have hg : Measurable fun u : ℝ ↦ -Real.log (1 - u) := by fun_prop
  have hE' (i : ℕ) : HasLaw (fun ω ↦ -Real.log (1 - V i ω)) (expMeasure 1) P₀ := by
    have := (hasLaw_map hg.aemeasurable).comp (hV i)
    rwa [map_uniform_neg_log_one_sub] at this
  have hind' : iIndepFun (fun i ω ↦ -Real.log (1 - V i ω)) P₀ :=
    hindV.comp (fun _ u ↦ -Real.log (1 - u)) fun _ ↦ hg
  have hlawV (i : ℕ) : P₀.map (V i) = volume.restrict (Set.Icc 0 1) := (hV i).map_eq
  have hM := tendstoInDistribution_meanExcessStat hVm hindV hlawV hk hkn hZ
  refine hM.of_map_eq (fun n ↦ ?_) (Eventually.of_forall fun n ↦ ?_)
  · have hv : ∀ i : Fin n, Measurable fun ω ↦ E i ω := fun i ↦ hEm i
    exact (measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
      (measurable_orderStat hv i).sub (measurable_orderStat hv (k n)))).sub
      measurable_const)).aemeasurable
  · have hT : Measurable fun y : Fin n → ℝ ↦ √(k n : ℝ) * (((k n : ℝ))⁻¹ *
        ∑ i ∈ range (k n), (orderStat y i - orderStat y (k n)) - 1) :=
      measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
        (measurable_orderStat_pi i).sub (measurable_orderStat_pi _))).sub measurable_const)
    rw [map_comp_vec_of_iid hE hind hT]
    exact (map_comp_vec_of_iid hE' hind' hT).symm

/-- **Asymptotic normality of the Hill estimator for Pareto samples, second proof** (via the
tail empirical process, [de Haan–Ferreira, Theorem 3.2.5 and §5.2]). Let `X_0, X_1, …` be iid
`Pareto(α)` and let `k(n) → ∞` with `k(n) / n → 0`. Then `√k (H_{k,n} - 1/α) ⇒ N(0, 1/α²)`.
Compare `tendstoInDistribution_hill_pareto`, proved with the Rényi representation (which needs
only `k(n) < n`). -/
theorem tendstoInDistribution_hill_pareto_of_tailEmpiricalProcess {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (α⁻¹ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ √(k n : ℝ) * (hill (fun i : Fin n ↦ X i ω) (k n) - α⁻¹))
      atTop Z (fun _ ↦ P) P' := by
  obtain ⟨Ω₀, _, P₀, E, hEm, hE, hind, hP₀⟩ := exists_iid ℕ (expMeasure 1)
  set γ := α⁻¹ with hγ
  have hγ0 : 0 < γ := inv_pos.2 hα
  have hZ1 : HasLaw (fun ω ↦ α * Z ω) (gaussianReal 0 1) P' := by
    have := gaussianReal_const_mul hZ α
    convert this using 2
    · simp
    · ext
      simp only [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _
        (sq_nonneg _), hγ]
      field_simp
  have hA := tendstoInDistribution_meanExcess_of_tailEmpiricalProcess hEm hE hind hk hkn hZ1
  have hB := hA.continuous_comp (g := fun x ↦ γ * x) (continuous_const.mul continuous_id)
  have hZe : (fun ω ↦ γ * (α * Z ω)) = Z := by
    funext ω; rw [hγ, ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
  replace hB := hB.congr_limit hZ.aemeasurable (by congr 1)
  refine hB.of_map_eq (fun n ↦ ?_) ?_
  · exact (measurable_const.mul ((measurable_hill_pi n (k n)).comp
      (measurable_pi_iff.2 fun i ↦ hX i) |>.sub measurable_const)).aemeasurable
  · filter_upwards [eventually_lt_of_tendsto_div hkn] with n hn
    have hg : Measurable fun e : ℝ ↦ Real.exp (γ * e) := by fun_prop
    have hS : Measurable fun y : Fin n → ℝ ↦ √(k n : ℝ) * (hill y (k n) - γ) :=
      measurable_const.mul ((measurable_hill_pi n (k n)).sub measurable_const)
    have hlawX : HasLaw (fun ω (i : Fin n) ↦ X i ω)
        (Measure.pi fun _ : Fin n ↦ (expMeasure 1).map fun e ↦ Real.exp (γ * e)) P := by
      refine (hindep.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective).hasLaw_pi
        (fun i ↦ ⟨(hX i).aemeasurable, ?_⟩)
      rw [(hident i).map_eq]
      exact map_eq_expMeasure_map_of_pareto (hX 0) hα hPar
    have hT : Measurable fun y : Fin n → ℝ ↦ γ * (√(k n : ℝ) * (((k n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range (k n), (orderStat y i - orderStat y (k n)) - 1)) :=
      measurable_const.mul (measurable_const.mul ((measurable_const.mul
        (Finset.measurable_sum _ fun i _ ↦ (measurable_orderStat_pi i).sub
          (measurable_orderStat_pi _))).sub measurable_const))
    have e1 : P.map (fun ω ↦ √(k n : ℝ) * (hill (fun i : Fin n ↦ X i ω) (k n) - γ)) =
        (Measure.pi fun _ : Fin n ↦ (expMeasure 1).map fun e ↦ Real.exp (γ * e)).map
          (fun y : Fin n → ℝ ↦ √(k n : ℝ) * (hill y (k n) - γ)) :=
      ((hasLaw_map hS.aemeasurable).comp hlawX).map_eq
    have e2 : P₀.map ((fun x ↦ γ * x) ∘ fun ω ↦ √(k n : ℝ) * (((k n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range (k n), (orderStat (fun i : Fin n ↦ E i ω) i -
          orderStat (fun i : Fin n ↦ E i ω) (k n)) - 1)) =
        (Measure.pi fun _ : Fin n ↦ expMeasure 1).map (fun y : Fin n → ℝ ↦
          γ * (√(k n : ℝ) * (((k n : ℝ))⁻¹ * ∑ i ∈ Finset.range (k n),
            (orderStat y i - orderStat y (k n)) - 1))) :=
      map_comp_vec_of_iid hE hind hT
    rw [e1, e2, ← Measure.pi_map_pi (fun _ ↦ hg.aemeasurable), Measure.map_map hS (by fun_prop)]
    congr 1
    funext y
    simp only [Function.comp_apply]
    rw [hill_exp_mul γ hγ0.le y hn]
    ring

end Normality

/-! ### Continuous functionals of the tail empirical process -/

section ContinuousMapping

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Continuous mapping theorem for the tail empirical process** ([de Haan–Ferreira, §5.1]): if
`B` is a random element of `D([0, 1])` with the finite-dimensional distributions of Brownian
motion and `h` is a measurable functional on `D([0, 1])` that is continuous at almost every path
of `B`, then `h(W_n) ⇒ h(B)`. -/
theorem tendstoInDistribution_comp_tailEmpiricalPath {U : ℕ → Ω → ℝ}
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {B : Ω' → SkorokhodSpace ℝ} (hB : Measurable B)
    (hBfdd : ∀ J : Finset unitInterval,
      (P'.map B).map (fun x : SkorokhodSpace ℝ ↦ fun t : J ↦ x t) =
        brownianFdd (fun t : J ↦ unitInterval.toNNReal' t))
    {F : Type*} [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {h : SkorokhodSpace ℝ → F} (hh : Measurable h)
    (hcont : ∀ᵐ x ∂(P'.map B), ContinuousAt h x) :
    TendstoInDistribution (fun n ω ↦ h (tailEmpiricalPath U n (k n) ω)) atTop (h ∘ B)
      (fun _ ↦ P) P' := by
  have hW := (tendstoInDistribution_tailEmpiricalPath hU hind hlaw hk hkn hB hBfdd).tendsto
  have h2 := ProbabilityMeasure.tendsto_map_of_ae_continuousAt hW hh hcont
  refine ⟨fun n ↦ (hh.comp (measurable_tailEmpiricalPath hU n (k n))).aemeasurable,
    (hh.comp hB).aemeasurable, ?_⟩
  have hlim : ProbabilityMeasure.map
      (⟨P'.map B, inferInstance⟩ : ProbabilityMeasure (SkorokhodSpace ℝ)) h =
      ⟨P'.map (h ∘ B), inferInstance⟩ := by
    refine ProbabilityMeasure.toMeasure_injective ?_
    exact Measure.map_map hh hB
  rw [hlim] at h2
  refine h2.congr fun n ↦ ProbabilityMeasure.toMeasure_injective ?_
  exact Measure.map_map hh (measurable_tailEmpiricalPath hU n (k n))

/-- The supremum of the tail empirical process converges in distribution to the supremum of
Brownian motion. -/
theorem tendstoInDistribution_supNorm_tailEmpiricalPath {U : ℕ → Ω → ℝ}
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {B : Ω' → SkorokhodSpace ℝ} (hB : Measurable B)
    (hBfdd : ∀ J : Finset unitInterval,
      (P'.map B).map (fun x : SkorokhodSpace ℝ ↦ fun t : J ↦ x t) =
        brownianFdd (fun t : J ↦ unitInterval.toNNReal' t)) :
    TendstoInDistribution (fun n ω ↦ SkorokhodSpace.supNorm (tailEmpiricalPath U n (k n) ω))
      atTop (SkorokhodSpace.supNorm ∘ B) (fun _ ↦ P) P' :=
  tendstoInDistribution_comp_tailEmpiricalPath hU hind hlaw hk hkn hB hBfdd
    SkorokhodSpace.continuous_supNorm.measurable
    (ae_of_all _ fun _ ↦ SkorokhodSpace.continuous_supNorm.continuousAt)

/-- The truncated Hill functional `x ↦ ∫_ε^1 x(t) dt / t - x(1)` on `D([0, 1])`. -/
noncomputable def hillFunctional (ε : ℝ) (x : SkorokhodSpace ℝ) : ℝ :=
  (∫ t in Set.Ioc ε 1, t⁻¹ * x (Set.projIcc 0 1 zero_le_one t)) - x 1

lemma continuous_hillFunctional {ε : ℝ} (hε : 0 < ε) : Continuous (hillFunctional ε) := by
  have hg : Integrable (fun t : ℝ ↦ t⁻¹) (volume.restrict (Set.Ioc ε 1)) := by
    rcases le_or_gt ε 1 with h | h
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h).1
        (intervalIntegral.intervalIntegrable_inv (fun x hx ↦ by
          rw [Set.uIcc_of_le h] at hx; exact (hε.trans_le hx.1).ne') continuousOn_id)
    · rw [Set.Ioc_eq_empty (not_lt.2 h.le), Measure.restrict_empty]
      exact integrable_zero_measure
  exact (SkorokhodSpace.continuous_integral_mul hg).sub SkorokhodSpace.continuous_apply_one

lemma hillFunctional_tailEmpiricalPath (U : ℕ → Ω → ℝ) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ω : Ω) :
    hillFunctional ε (tailEmpiricalPath U n k ω) = ∑ i ∈ range n, hillSummand n k ε (U i ω) := by
  rw [sum_hillSummand_eq U ω hn hk hε0 hε1, hillFunctional, intervalIntegral.integral_of_le hε1]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    simp only [tailEmpiricalPath_apply]
    rw [Set.projIcc_of_mem _ ⟨hε0.le.trans ht.1.le, ht.2⟩, div_eq_inv_mul]

/-- **The law of a Brownian functional, via the invariance principle.** If `B` is a random
element of `D([0, 1])` with the finite-dimensional distributions of Brownian motion, then for
`0 < ε ≤ 1`, `∫_ε^1 B(t) dt / t - B(1)` is centered Gaussian with variance `1 + 2 ε log ε`.
The proof compares two limits of the truncated Hill functional of the uniform tail empirical
process: the continuous mapping theorem in `D` and the triangular-array central limit theorem
(`tendstoInDistribution_sum_hillSummand`). As `ε → 0` the variance tends to `1`, the variance of
`∫_0^1 B(t) dt / t - B(1)`, the limit of the Hill statistic. -/
theorem map_hillFunctional_eq_gaussianReal {B : Ω' → SkorokhodSpace ℝ} (hB : Measurable B)
    (hBfdd : ∀ J : Finset unitInterval,
      (P'.map B).map (fun x : SkorokhodSpace ℝ ↦ fun t : J ↦ x t) =
        brownianFdd (fun t : J ↦ unitInterval.toNNReal' t))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    P'.map (hillFunctional ε ∘ B) = gaussianReal 0 (1 + 2 * ε * Real.log ε).toNNReal := by
  obtain ⟨Ω₀, _, P₀, V, hVm, hV, hindV, hP₀⟩ := exists_iid ℕ μU
  have hlawV (i : ℕ) : P₀.map (V i) = volume.restrict (Set.Icc 0 1) := (hV i).map_eq
  set k : ℕ → ℕ := fun n ↦ Nat.sqrt n with hkdef
  have hk : Tendsto k atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b ↦ ⟨b * b, fun n hn ↦ ?_⟩
    exact Nat.le_sqrt.2 hn
  have hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) h1
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 h
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn
    rw [div_le_iff₀ hn]
    calc (k n : ℝ) ≤ √(n : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ = (√(n : ℝ))⁻¹ * n := by
          field_simp
          rw [Real.sq_sqrt hn.le]
  have h1 := tendstoInDistribution_comp_tailEmpiricalPath hVm hindV hlawV hk hkn hB hBfdd
    (continuous_hillFunctional hε0).measurable
    (ae_of_all _ fun _ ↦ (continuous_hillFunctional hε0).continuousAt)
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have h2 := tendstoInDistribution_sum_hillSummand hVm hindV hlawV hk hkn (ε := fun _ ↦ ε)
    (fun _ ↦ hε0) (fun _ ↦ hε1) tendsto_const_nhds
    (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hkR))
  have h2' := h2.of_map_eq
    (X := fun n ω ↦ hillFunctional ε (tailEmpiricalPath V n (k n) ω))
    (fun n ↦ ((continuous_hillFunctional hε0).measurable.comp
      (measurable_tailEmpiricalPath hVm n (k n))).aemeasurable) (by
      filter_upwards [eventually_gt_atTop 0, hk.eventually_gt_atTop 0] with n hn hk0
      congr 1
      funext ω
      exact hillFunctional_tailEmpiricalPath V hn hk0 hε0 hε1 ω)
  have := tendstoInDistribution_unique _ h1 h2'
  rw [this, Measure.map_id]

end ContinuousMapping

/-! ### A weighted bound near `0` -/

section Weighted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {U : ℕ → Ω → ℝ}

/-- **The weighted process on one block** `[a, 2a]`: the probability that
`|W_n(t)| > ε t ^ α` for some `t ∈ [a, 2a]` is bounded by Chebyshev's inequality at `a` and the
maximal inequality on the block. -/
lemma measureReal_block_weighted_le (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) {a α ε : ℝ} (ha : 0 < a) (hα : 0 ≤ α) (hε : 0 < ε)
    (hp : (k : ℝ) / n * (2 * a) ≤ 1) :
    P.real {ω | ∃ t ∈ Set.Icc a (2 * a), ε * t ^ α < |tailEmpiricalProcess U n k t ω|} ≤
      4 / ε ^ 2 * a ^ (1 - 2 * α) + 8 ^ 4 * 256 / ε ^ 4 *
        (84 * a ^ (2 - 4 * α) + 8 * a ^ (1 - 4 * α) / k + 32 / ε * a ^ (2 - 5 * α) / √(k : ℝ)) := by
  set c : ℝ := ε * a ^ α with hc
  have haα : 0 < a ^ α := Real.rpow_pos_of_pos ha α
  have hc0 : 0 < c := mul_pos hε haα
  set lam : ℝ := c / 4 with hlam
  have hlam0 : 0 < lam := by positivity
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk'
  -- the number of dyadic levels
  obtain ⟨q₀, hq₀', hq₀⟩ := exists_nat_pow_near (le_max_left 1 (√(k : ℝ) * a / lam))
    (one_lt_two : (1 : ℝ) < 2)
  set q := q₀ + 1
  have hq1 : √(k : ℝ) * a / lam ≤ 2 ^ q := (le_max_right _ _).trans hq₀.le
  have hq2 : (2 : ℝ) ^ q ≤ 2 * (1 + √(k : ℝ) * a / lam) := by
    rw [pow_succ]
    have : max 1 (√(k : ℝ) * a / lam) ≤ 1 + √(k : ℝ) * a / lam :=
      max_le (by linarith [show 0 ≤ √(k : ℝ) * a / lam by positivity]) (by linarith)
    linarith [hq₀']
  have hq : √(k : ℝ) * (a / 2 ^ q) ≤ lam := by
    rw [div_le_iff₀ hlam0] at hq1
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  -- the events
  have hsub : {ω | ∃ t ∈ Set.Icc a (2 * a), ε * t ^ α < |tailEmpiricalProcess U n k t ω|} ⊆
      {ω | c / 2 ≤ |tailEmpiricalProcess U n k a ω|} ∪
        {ω | ∃ u ∈ Set.Icc a (a + a), 2 * lam <
          |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k a ω|} := by
    rintro ω ⟨t, ht, hlt⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_exists, not_and,
      not_lt] at hcon
    have h1 := hcon.2 t ⟨ht.1, by linarith [ht.2]⟩
    have h2 : c ≤ ε * t ^ α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ha.le ht.1 hα) hε.le
    have h3 := abs_sub_abs_le_abs_sub (tailEmpiricalProcess U n k t ω)
      (tailEmpiricalProcess U n k a ω)
    rw [hlam] at h1
    linarith [hcon.1]
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  have hA := measureReal_le_abs_tailEmpiricalProcess_le hU hind hlaw (P := P) hn hk ha.le
    ((mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans hp) (half_pos hc0)
  have hB := measureReal_exists_abs_tailEmpiricalProcess_sub_gt_le hU hind hlaw (P := P)
    hn.ne' ha.le ha (by rw [← two_mul]; exact hp) hlam0 q hq
  refine add_le_add (hA.trans_eq ?_) (hB.trans ?_)
  · have h2 : (a ^ α) ^ 2 = a ^ (2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; ring_nf
    rw [hc, Real.rpow_sub ha, Real.rpow_one, ← h2]
    field_simp
    ring
  · -- simplify the bound of the maximal inequality
    have h4 : (a ^ α) ^ 4 = a ^ (4 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; ring_nf
    have hl4 : lam ^ 4 = ε ^ 4 * a ^ (4 * α) / 256 := by
      rw [hlam, hc, ← h4]; ring
    have e1 : a ^ 2 / a ^ (4 * α) = a ^ (2 - 4 * α) := by
      rw [Real.rpow_sub ha]; norm_num
    have e2 : a / a ^ (4 * α) = a ^ (1 - 4 * α) := by
      rw [Real.rpow_sub ha, Real.rpow_one]
    have e3 : a * a / lam / a ^ (4 * α) = 4 / ε * a ^ (2 - 5 * α) := by
      rw [show 2 - 5 * α = 2 - α - 4 * α by ring, Real.rpow_sub ha, Real.rpow_sub ha, hlam, hc]
      norm_num
      field_simp
    have h2q : (2 : ℝ) ^ (q + 2) * a / k ≤
        8 * (a / k) + 8 * √(k : ℝ) * (a * a / lam) / k := by
      calc (2 : ℝ) ^ (q + 2) * a / k = 4 * (2 ^ q * a) / k := by ring
        _ ≤ 4 * (2 * (1 + √(k : ℝ) * a / lam) * a) / k := by gcongr
        _ = _ := by ring
    have hkk : √(k : ℝ) / k = 1 / √(k : ℝ) := by
      field_simp; rw [Real.sq_sqrt hk'.le]
    calc 8 ^ 4 / lam ^ 4 * (84 * a ^ 2 + 2 ^ (q + 2) * a / k)
        ≤ 8 ^ 4 / lam ^ 4 * (84 * a ^ 2 + (8 * (a / k) + 8 * √(k : ℝ) * (a * a / lam) / k)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 ^ 4 * 256 / ε ^ 4 * (84 * (a ^ 2 / a ^ (4 * α)) + 8 * (a / a ^ (4 * α)) / k +
          8 * (a * a / lam / a ^ (4 * α)) * (√(k : ℝ) / k)) := by
          rw [hl4]; field_simp; ring
      _ = _ := by
          rw [e1, e2, e3, hkk]
          ring

lemma sum_range_mul_two_pow_rpow {s : ℝ} (hs : 0 < s) (γ : ℝ) (J : ℕ) :
    ∑ i ∈ range J, (s * 2 ^ i) ^ γ = s ^ γ * ∑ i ∈ range J, ((2 : ℝ) ^ γ) ^ i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.mul_rpow hs.le (by positivity), ← Real.rpow_natCast (2 : ℝ) i,
    ← Real.rpow_mul zero_le_two, mul_comm (i : ℝ) γ, Real.rpow_mul zero_le_two,
    Real.rpow_natCast]

lemma sum_range_mul_two_pow_rpow_le_of_neg {s : ℝ} (hs : 0 < s) {γ : ℝ} (hγ : γ < 0) (J : ℕ) :
    ∑ i ∈ range J, (s * 2 ^ i) ^ γ ≤ s ^ γ / (1 - 2 ^ γ) := by
  have hr : (2 : ℝ) ^ γ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hγ
  rw [sum_range_mul_two_pow_rpow hs, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (sum_range_geom_le_of_lt_one (by positivity) hr J) (by positivity)

lemma sum_range_mul_two_pow_rpow_le_of_pos {s : ℝ} (hs : 0 < s) {γ : ℝ} (hγ : 0 < γ) (J : ℕ) :
    ∑ i ∈ range J, (s * 2 ^ i) ^ γ ≤ (s * 2 ^ J) ^ γ / (2 ^ γ - 1) := by
  have hr : 1 < (2 : ℝ) ^ γ := Real.one_lt_rpow one_lt_two hγ
  have hr' : 0 < (2 : ℝ) ^ γ - 1 := by linarith
  have e : (s * 2 ^ J) ^ γ = s ^ γ * ((2 : ℝ) ^ γ) ^ J := by
    rw [Real.mul_rpow hs.le (by positivity), ← Real.rpow_natCast (2 : ℝ) J,
      ← Real.rpow_mul zero_le_two, mul_comm (J : ℝ) γ, Real.rpow_mul zero_le_two,
      Real.rpow_natCast]
  rw [sum_range_mul_two_pow_rpow hs, geom_sum_eq hr.ne', e, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact div_le_div_of_nonneg_right (by linarith) hr'.le

/-- Dyadic blocks `[s 2^i, s 2^{i+1}]`, `i < M`, cover `(s, s 2^M]`. -/
lemma exists_mem_dyadic_block {s t : ℝ} (M : ℕ) (hst : s < t)
    (ht : t ≤ s * 2 ^ M) : ∃ i < M, t ∈ Set.Icc (s * 2 ^ i) (2 * (s * 2 ^ i)) := by
  induction M with
  | zero => simp at ht; linarith
  | succ M ih =>
    by_cases h : t ≤ s * 2 ^ M
    · obtain ⟨i, hi, hti⟩ := ih h
      exact ⟨i, by omega, hti⟩
    · refine ⟨M, by omega, (not_le.1 h).le, ?_⟩
      rw [pow_succ] at ht
      linarith

/-- The probability that some observation exceeds `1 - (k/n) s` is at most `k s`. -/
lemma measureReal_exists_one_sub_le (hU : ∀ i, Measurable (U i))
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : 0 < n) {s : ℝ}
    (hs : 0 ≤ s) (hps : (k : ℝ) / n * s ≤ 1) :
    P.real {ω | ∃ i < n, 1 - k / n * s ≤ U i ω} ≤ k * s := by
  have hsub : {ω | ∃ i < n, 1 - k / n * s ≤ U i ω} ⊆
      ⋃ i ∈ range n, U i ⁻¹' Set.Ici (1 - k / n * s) := by
    rintro ω ⟨i, hi, h⟩
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi)) h
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  have h (i : ℕ) : P.real (U i ⁻¹' Set.Ici (1 - k / n * s)) = k / n * s := by
    rw [← map_measureReal_apply (hU i) measurableSet_Ici, hlaw i]
    exact measureReal_uniform_Ici (mul_nonneg (by positivity) hs) hps
  simp_rw [h]
  rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  rfl

lemma tendsto_rpow_nhds_zero_of_pos {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun δ : ℝ ↦ δ ^ γ) (𝓝 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto
  rwa [Real.zero_rpow hγ.ne'] at this

/-- `(c / k) ^ g / k ^ h = c ^ g / k ^ (g + h)`. -/
lemma div_rpow_div_rpow_eq {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (g h : ℝ) :
    (c / x) ^ g / x ^ h = c ^ g / x ^ (g + h) := by
  rw [Real.div_rpow hc hx.le, Real.rpow_add hx, div_div]

/-- **Weighted approximation near `0`** (core case `η ≤ 1/20`). -/
theorem exists_eventually_measureReal_weighted_le_aux (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 20) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ᶠ n in atTop, P.real {ω | ∃ t ∈ Set.Ioc 0 δ,
      ε * t ^ (1 / 2 - η) < |tailEmpiricalProcess U n (k n) t ω|} ≤ θ := by
  set α : ℝ := 1 / 2 - η with hα
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  set K : ℝ := 8 ^ 4 * 256 / ε ^ 4 with hK
  have hK0 : 0 < K := by positivity
  have hg1 : 0 < 1 - 2 * α := by rw [hα]; linarith
  have hg2 : 0 < 2 - 4 * α := by rw [hα]; linarith
  have hg3 : 1 - 4 * α < 0 := by rw [hα]; linarith
  have hg4 : 2 - 5 * α < 0 := by rw [hα]; linarith
  have hd1 : 0 < (2 : ℝ) ^ (1 - 2 * α) - 1 := by
    linarith [Real.one_lt_rpow one_lt_two hg1]
  have hd2 : 0 < (2 : ℝ) ^ (2 - 4 * α) - 1 := by
    linarith [Real.one_lt_rpow one_lt_two hg2]
  have hd3 : 0 < 1 - (2 : ℝ) ^ (1 - 4 * α) := by
    linarith [Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hg3]
  have hd4 : 0 < 1 - (2 : ℝ) ^ (2 - 5 * α) := by
    linarith [Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hg4]
  -- the choice of `δ`
  set F : ℝ → ℝ := fun δ ↦ 4 / ε ^ 2 * (δ ^ (1 - 2 * α) / (2 ^ (1 - 2 * α) - 1)) +
    K * 84 * (δ ^ (2 - 4 * α) / (2 ^ (2 - 4 * α) - 1)) with hF
  have hFlim : Tendsto F (𝓝 0) (𝓝 0) := by
    have := (((tendsto_rpow_nhds_zero_of_pos hg1).div_const ((2 : ℝ) ^ (1 - 2 * α) - 1)).const_mul
      (4 / ε ^ 2)).add (((tendsto_rpow_nhds_zero_of_pos hg2).div_const
        ((2 : ℝ) ^ (2 - 4 * α) - 1)).const_mul (K * 84))
    simpa using this
  obtain ⟨r, hr, hFr⟩ := Metric.eventually_nhds_iff.1
    (hFlim.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 3 by positivity)))
  set δ : ℝ := min (r / 2) 1 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hFδ : F δ < θ / 3 := hFr (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]
    exact (min_le_left _ _).trans_lt (half_lt_self hr))
  refine ⟨δ, ⟨hδ0, hδ1⟩, ?_⟩
  -- the eventual conditions
  set θ' : ℝ := θ / 3 with hθ'
  have hθ'0 : 0 < θ' := by positivity
  set c : ℝ := θ' / 2 with hc
  have hc0 : 0 < c := by positivity
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hlim (C g : ℝ) (hg : 0 < g) : Tendsto (fun n ↦ C / (k n : ℝ) ^ g) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hg).comp hkR)
  have hT3 := hlim (K * 8 * (c ^ (1 - 4 * α) / (1 - 2 ^ (1 - 4 * α)))) (1 - 4 * α + 1)
    (by linarith)
  have hT4 := hlim (K * (32 / ε) * (c ^ (2 - 5 * α) / (1 - 2 ^ (2 - 5 * α))))
    (2 - 5 * α + 1 / 2) (by linarith)
  have hT5 := hlim (θ' ^ (1 - α)) (1 - α - 1 / 2) (by rw [hα]; linarith)
  filter_upwards [hk.eventually_gt_atTop 0, eventually_gt_atTop 0,
    hkn.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hkR.eventually (Filter.eventually_ge_atTop (θ' / δ)),
    (hT3.add hT4).eventually (ge_mem_nhds (show (0 : ℝ) + 0 < θ / 3 by linarith)),
    hT5.eventually (ge_mem_nhds hε)] with n hk0 hn0 hp hkδ hT34 hT5n
  have hk' : (0 : ℝ) < k n := Nat.cast_pos.2 hk0
  have hsk : 0 < √(k n : ℝ) := Real.sqrt_pos.2 hk'
  set p : ℝ := (k n : ℝ) / n with hpdef
  have hp0 : 0 ≤ p := by positivity
  -- the dyadic scale
  have hx1 : 1 ≤ δ * k n / θ' := by
    rw [le_div_iff₀ hθ'0, one_mul]
    rw [div_le_iff₀ hδ0] at hkδ
    linarith
  obtain ⟨J, hJ1, hJ2⟩ := exists_nat_pow_near hx1 one_lt_two
  set M := J + 1 with hM
  set s : ℝ := δ / 2 ^ M with hs
  have hs0 : 0 < s := by positivity
  have hsM : s * 2 ^ M = δ := by rw [hs]; field_simp
  have hsup : s ≤ θ' / k n := by
    rw [hs, div_le_div_iff₀ (by positivity) hk']
    rw [div_lt_iff₀ hθ'0] at hJ2
    linarith
  have hslow : c / k n ≤ s := by
    rw [hs, hc, div_div, div_le_div_iff₀ (by positivity) (by positivity), hM, pow_succ]
    rw [le_div_iff₀ hθ'0] at hJ1
    nlinarith
  -- the events
  set Bot := {ω | ∃ i < n, 1 - p * s ≤ U i ω}
  set Bl : ℕ → Set Ω := fun i ↦ {ω | ∃ t ∈ Set.Icc (s * 2 ^ i) (2 * (s * 2 ^ i)),
    ε * t ^ α < |tailEmpiricalProcess U n (k n) t ω|}
  have hsub : {ω | ∃ t ∈ Set.Ioc 0 δ, ε * t ^ (1 / 2 - η) <
      |tailEmpiricalProcess U n (k n) t ω|} ⊆ Bot ∪ ⋃ i ∈ range M, Bl i := by
    rintro ω ⟨t, ht, hlt⟩
    by_cases hB : ω ∈ Bot
    · exact Or.inl hB
    right
    rcases le_or_gt t s with hts | hts
    · exfalso
      simp only [Bot, Set.mem_ofPred_eq, not_exists, not_and, not_le] at hB
      have hW : tailEmpiricalProcess U n (k n) t ω = -(√(k n : ℝ) * t) := by
        unfold tailEmpiricalProcess
        rw [Finset.sum_eq_zero fun i hi ↦ ?_]
        · ring
        have : U i ω < 1 - k n / n * t := by
          have := hB i (Finset.mem_range.1 hi)
          have : p * t ≤ p * s := mul_le_mul_of_nonneg_left hts hp0
          rw [hpdef] at *
          linarith
        simp [Set.indicator, not_le.2 this]
      rw [hW, abs_neg, abs_of_pos (mul_pos hsk ht.1)] at hlt
      -- `√k t = √k t ^ (1 - α) t ^ α ≤ ε t ^ α`
      have ht0 := ht.1
      have e : t = t ^ (1 - α) * t ^ α := by
        rw [← Real.rpow_add ht0]; simp
      have h1 : t ^ (1 - α) ≤ (θ' / k n) ^ (1 - α) :=
        Real.rpow_le_rpow ht0.le (hts.trans hsup) (by rw [hα]; linarith)
      have h2 : √(k n : ℝ) * (θ' / k n) ^ (1 - α) = θ' ^ (1 - α) / (k n : ℝ) ^ (1 - α - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, Real.div_rpow hθ'0.le hk'.le, Real.rpow_sub hk' (1 - α)]
        field_simp
      have h3 : √(k n : ℝ) * t ^ (1 - α) ≤ ε :=
        (mul_le_mul_of_nonneg_left h1 hsk.le).trans (h2 ▸ hT5n)
      have h4 : √(k n : ℝ) * t ≤ ε * t ^ α := by
        calc √(k n : ℝ) * t = (√(k n : ℝ) * t ^ (1 - α)) * t ^ α := by rw [mul_assoc, ← e]
          _ ≤ ε * t ^ α := mul_le_mul_of_nonneg_right h3 (by positivity)
      rw [hα] at h4
      linarith
    · obtain ⟨i, hi, hti⟩ := exists_mem_dyadic_block M hts (hsM.symm ▸ ht.2)
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi)) ⟨t, hti, by rwa [hα]⟩
  -- the probabilities
  have hPbot : P.real Bot ≤ θ' := by
    refine (measureReal_exists_one_sub_le hU hlaw hn0 hs0.le ?_).trans ?_
    · have : s ≤ 1 := (div_le_self hδ0.le (one_le_pow₀ one_le_two)).trans hδ1
      calc p * s ≤ 1 / 2 * 1 := mul_le_mul hp this hs0.le (by norm_num)
        _ ≤ 1 := by norm_num
    · rw [le_div_iff₀ hk'] at hsup; linarith
  set b : ℝ → ℝ := fun a ↦ 4 / ε ^ 2 * a ^ (1 - 2 * α) + K *
    (84 * a ^ (2 - 4 * α) + 8 * a ^ (1 - 4 * α) / k n + 32 / ε * a ^ (2 - 5 * α) / √(k n : ℝ))
  have hPbl (i : ℕ) (hi : i ∈ range M) : P.real (Bl i) ≤ b (s * 2 ^ i) := by
    refine measureReal_block_weighted_le hU hind hlaw hn0 hk0 (by positivity) hα0 hε ?_
    have h2a : 2 * (s * 2 ^ i) ≤ 1 := by
      have hi' : i + 1 ≤ M := Finset.mem_range.1 hi
      calc 2 * (s * 2 ^ i) = s * 2 ^ (i + 1) := by ring
        _ ≤ s * 2 ^ M := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hi') hs0.le
        _ ≤ 1 := hsM ▸ hδ1
    calc (k n : ℝ) / n * (2 * (s * 2 ^ i)) ≤ 1 / 2 * 1 :=
          mul_le_mul hp h2a (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hsum : ∑ i ∈ range M, b (s * 2 ^ i) ≤ F δ +
      (K * 8 * (c ^ (1 - 4 * α) / (1 - 2 ^ (1 - 4 * α))) / (k n : ℝ) ^ (1 - 4 * α + 1) +
        K * (32 / ε) * (c ^ (2 - 5 * α) / (1 - 2 ^ (2 - 5 * α))) /
          (k n : ℝ) ^ (2 - 5 * α + 1 / 2)) := by
    have e : ∑ i ∈ range M, b (s * 2 ^ i) =
        4 / ε ^ 2 * ∑ i ∈ range M, (s * 2 ^ i) ^ (1 - 2 * α) +
        K * 84 * ∑ i ∈ range M, (s * 2 ^ i) ^ (2 - 4 * α) +
        K * 8 / k n * ∑ i ∈ range M, (s * 2 ^ i) ^ (1 - 4 * α) +
        K * (32 / ε) / √(k n : ℝ) * ∑ i ∈ range M, (s * 2 ^ i) ^ (2 - 5 * α) := by
      simp only [b, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have s1 := sum_range_mul_two_pow_rpow_le_of_pos hs0 hg1 M
    have s2 := sum_range_mul_two_pow_rpow_le_of_pos hs0 hg2 M
    have s3 := sum_range_mul_two_pow_rpow_le_of_neg hs0 hg3 M
    have s4 := sum_range_mul_two_pow_rpow_le_of_neg hs0 hg4 M
    rw [hsM] at s1 s2
    have c3 : s ^ (1 - 4 * α) ≤ (c / k n) ^ (1 - 4 * α) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hslow hg3.le
    have c4 : s ^ (2 - 5 * α) ≤ (c / k n) ^ (2 - 5 * α) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hslow hg4.le
    have e3 : K * 8 / k n * ((c / k n) ^ (1 - 4 * α) / (1 - 2 ^ (1 - 4 * α))) =
        K * 8 * (c ^ (1 - 4 * α) / (1 - 2 ^ (1 - 4 * α))) / (k n : ℝ) ^ (1 - 4 * α + 1) := by
      have h := div_rpow_div_rpow_eq hc0.le hk' (1 - 4 * α) 1
      rw [Real.rpow_one] at h
      calc _ = K * 8 * ((c / k n) ^ (1 - 4 * α) / k n) / (1 - 2 ^ (1 - 4 * α)) := by ring
        _ = _ := by rw [h]; ring
    have e4 : K * (32 / ε) / √(k n : ℝ) * ((c / k n) ^ (2 - 5 * α) / (1 - 2 ^ (2 - 5 * α))) =
        K * (32 / ε) * (c ^ (2 - 5 * α) / (1 - 2 ^ (2 - 5 * α))) /
          (k n : ℝ) ^ (2 - 5 * α + 1 / 2) := by
      have h := div_rpow_div_rpow_eq hc0.le hk' (2 - 5 * α) (1 / 2)
      rw [← Real.sqrt_eq_rpow] at h
      calc _ = K * (32 / ε) * ((c / k n) ^ (2 - 5 * α) / √(k n : ℝ)) /
            (1 - 2 ^ (2 - 5 * α)) := by ring
        _ = _ := by rw [h]; ring
    rw [e, hF, ← e3, ← e4]
    have t1 := mul_le_mul_of_nonneg_left s1 (show 0 ≤ 4 / ε ^ 2 by positivity)
    have t2 := mul_le_mul_of_nonneg_left s2 (show 0 ≤ K * 84 by positivity)
    have t3 := mul_le_mul_of_nonneg_left (s3.trans (div_le_div_of_nonneg_right c3 hd3.le))
      (show 0 ≤ K * 8 / k n by positivity)
    have t4 := mul_le_mul_of_nonneg_left (s4.trans (div_le_div_of_nonneg_right c4 hd4.le))
      (show 0 ≤ K * (32 / ε) / √(k n : ℝ) by positivity)
    linarith
  calc P.real _ ≤ P.real (Bot ∪ ⋃ i ∈ range M, Bl i) := measureReal_mono hsub
    _ ≤ P.real Bot + ∑ i ∈ range M, P.real (Bl i) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_biUnion_finset_le _ _))
    _ ≤ θ' + ∑ i ∈ range M, b (s * 2 ^ i) :=
        add_le_add hPbot (Finset.sum_le_sum hPbl)
    _ ≤ θ' + (F δ + (K * 8 * (c ^ (1 - 4 * α) / (1 - 2 ^ (1 - 4 * α))) /
          (k n : ℝ) ^ (1 - 4 * α + 1) + K * (32 / ε) * (c ^ (2 - 5 * α) /
            (1 - 2 ^ (2 - 5 * α))) / (k n : ℝ) ^ (2 - 5 * α + 1 / 2))) := by linarith
    _ ≤ θ := by linarith

/-- **Weighted approximation of the tail empirical process near `0`** (Chibisov–O'Reilly type
tail estimate; [de Haan–Ferreira, Theorem 5.1.4, weighted form]; [Einmahl 1992]). For
`η > 0` (the interesting range is `η < 1/2`), `ε > 0` and `θ > 0` there is `δ ∈ (0, 1]` such
that eventually
`P(∃ t ∈ (0, δ], |W_n(t)| > ε t ^ (1/2 - η)) ≤ θ`; that is,
`lim_{δ → 0} limsup_n P(sup_{0 < t ≤ δ} |W_n(t)| / t ^ (1/2 - η) > ε) = 0`.

The proof covers `(0, δ]` by the region `(0, s]` with `s ≍ θ / k`, where with high probability
no observation exceeds `1 - (k/n) s`, so that `W_n(t) = -√k t` there, and by the dyadic blocks
`[s 2^i, s 2^{i+1}]`, on which Chebyshev's inequality and the maximal inequality
(`measureReal_exists_abs_tailEmpiricalProcess_sub_gt_le`) give geometrically summable bounds.
It suffices to treat `η ≤ 1/20`, since the weight `t ^ (1/2 - η)` increases with `η` on
`(0, 1]`. -/
theorem exists_eventually_measureReal_weighted_le (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {η : ℝ} (hη0 : 0 < η) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ᶠ n in atTop, P.real {ω | ∃ t ∈ Set.Ioc 0 δ,
      ε * t ^ (1 / 2 - η) < |tailEmpiricalProcess U n (k n) t ω|} ≤ θ := by
  set η' := min η (1 / 20) with hη'
  obtain ⟨δ, hδ, hev⟩ := exists_eventually_measureReal_weighted_le_aux hU hind hlaw hk hkn
    (η := η') (lt_min hη0 (by norm_num)) (min_le_right _ _) hε hθ
  refine ⟨δ, hδ, hev.mono fun n hn ↦ (measureReal_mono ?_).trans hn⟩
  rintro ω ⟨t, ht, hlt⟩
  refine ⟨t, ht, lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hε.le) hlt⟩
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 (ht.2.trans hδ.2)
    (by linarith [min_le_left η (1 / 20)])

end Weighted

end ExtremeValueTheory
