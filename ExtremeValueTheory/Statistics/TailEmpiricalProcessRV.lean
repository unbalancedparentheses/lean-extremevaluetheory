/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.TailEmpiricalProcess
import ExtremeValueTheory.Statistics.HillNormality

/-!
# Hill's estimator via the tail empirical process
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
    integral_logTruncExcess_of_lt hp hε1 hp1 2 two_ne_zero, integral_logTruncExcess_sq_mid hp hε0 hε1]
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
      ((measurable_logTruncExcess _ ε).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
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
  · have h2 : Tendsto (fun n ↦ -(Real.log (ε n) / √(k n : ℝ)) + (√(k n : ℝ))⁻¹ * (1 + k n / n * ε n))
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

end Moments

end ExtremeValueTheory
