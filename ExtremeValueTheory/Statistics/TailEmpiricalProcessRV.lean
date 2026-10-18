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

lemma abs_hillSummand_le {n k : ℕ} (hkn : k ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (u : ℝ) :
    |hillSummand n k ε u| ≤ (√(k : ℝ))⁻¹ * (-Real.log ε + 2) := by
  unfold hillSummand
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (by positivity)
  have hp : (k : ℝ) / n ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact (div_le_one (by exact_mod_cast h)).2 (by exact_mod_cast hkn)
  have : |(k : ℝ) / n * ε| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
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

end Summand

end ExtremeValueTheory
