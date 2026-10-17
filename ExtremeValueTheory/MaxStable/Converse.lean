import ExtremeValueTheory.Multivariate.Dependence
import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section Truncated

/-- The integrand `1 - exp (-v / t)` of the truncated mean of a Fréchet variable with scale `v`. -/
lemma intervalIntegrable_one_sub_exp {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c) :
    IntervalIntegrable (fun t : ℝ ↦ 1 - Real.exp (-(v / t))) volume 0 c := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun (by fun_prop) ?_
  rw [uIoc_of_le hc]
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦ ?_)
  have h1 : Real.exp (-(v / t)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hv ht.1.le))
  dsimp only
  rw [Real.norm_eq_abs, norm_one, abs_of_nonneg (by linarith)]
  linarith [Real.exp_pos (-(v / t))]

lemma integral_one_sub_exp_nonneg {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c) :
    0 ≤ ∫ t in (0)..c, (1 - Real.exp (-(v / t))) := by
  refine intervalIntegral.integral_nonneg hc fun t ht ↦ ?_
  have : Real.exp (-(v / t)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hv ht.1))
  linarith

lemma integral_one_sub_exp_le {v c : ℝ} (hv : 0 < v) (hc : 1 ≤ c) :
    ∫ t in (0)..c, (1 - Real.exp (-(v / t))) ≤ 1 + v * Real.log c := by
  have hint1 := intervalIntegrable_one_sub_exp hv.le zero_le_one
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ 1 - Real.exp (-(v / t))) volume 1 c := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hc] at ht
    have : t ≠ 0 := by linarith [ht.1]
    fun_prop (disch := assumption)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hinv : IntervalIntegrable (fun t : ℝ ↦ v * t⁻¹) volume 1 c := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hc] at ht
    have : t ≠ 0 := by linarith [ht.1]
    fun_prop (disch := assumption)
  have h1 : ∫ t in (0)..1, (1 - Real.exp (-(v / t))) ≤ ∫ t in (0)..1, (1 : ℝ) :=
    intervalIntegral.integral_mono_on zero_le_one hint1 intervalIntegrable_const fun t _ ↦ by
      linarith [Real.exp_pos (-(v / t))]
  have h2 : ∫ t in (1)..c, (1 - Real.exp (-(v / t))) ≤ ∫ t in (1)..c, v * t⁻¹ :=
    intervalIntegral.integral_mono_on hc hint2 hinv fun t ht ↦ by
      have := Real.add_one_le_exp (-(v / t))
      rw [div_eq_mul_inv] at this ⊢
      linarith
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith), div_one]
    at h2
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1
  linarith

lemma le_integral_one_sub_exp {v c : ℝ} (hv : 0 < v) (hc : 0 ≤ c) :
    v * Real.log (c + v) - v * Real.log v ≤ ∫ t in (0)..c, (1 - Real.exp (-(v / t))) := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ v * (t + v)⁻¹) volume 0 c := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hc] at ht
    have : t + v ≠ 0 := by linarith [ht.1]
    fun_prop (disch := assumption)
  have hmono : ∫ t in (0)..c, v * (t + v)⁻¹ ≤ ∫ t in (0)..c, (1 - Real.exp (-(v / t))) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hc hint
      (intervalIntegrable_one_sub_exp hv.le hc) fun t ht ↦ ?_
    have ht0 : 0 < t := ht.1
    -- `1 - exp (-u) ≥ u / (1 + u)` with `u = v / t`
    have h1 := Real.add_one_le_exp (v / t)
    have h2 : Real.exp (-(v / t)) * Real.exp (v / t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 : Real.exp (-(v / t)) ≤ t / (t + v) := by
      rw [le_div_iff₀ (by positivity)]
      have : Real.exp (-(v / t)) * (v / t + 1) ≤ 1 := by
        nlinarith [Real.exp_pos (-(v / t))]
      have e : v / t + 1 = (t + v) / t := by field_simp; ring
      rw [e, mul_div_assoc'] at this
      rwa [div_le_one ht0] at this
    have h4 : v * (t + v)⁻¹ = 1 - t / (t + v) := by field_simp; ring
    rw [h4]
    linarith
  have hcomp : ∫ t in (0)..c, v * (t + v)⁻¹ = v * (Real.log (c + v) - Real.log v) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun t ↦ t⁻¹) v, zero_add,
      integral_inv_of_pos hv (by linarith), Real.log_div (by linarith) hv.ne']
  linarith [hcomp ▸ hmono]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ}

/-- **Truncated means of Fréchet-tailed variables**: if `P(X > r) = 1 - exp (-v / r)`, then
`E[min X c] = ∫₀ᶜ (1 - exp (-v / t)) dt`. -/
lemma lintegral_ofReal_min_eq (hXm : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    (hX : ∀ r > 0, μ {x | r < X x} = ENNReal.ofReal (1 - Real.exp (-(v / r)))) (hv : 0 ≤ v)
    {c : ℝ} (hc : 0 < c) :
    ∫⁻ x, ENNReal.ofReal (min (X x) c) ∂μ =
      ENNReal.ofReal (∫ t in (0)..c, (1 - Real.exp (-(v / t)))) := by
  rw [lintegral_eq_lintegral_meas_lt μ (hX0.mono fun x hx ↦ le_min hx hc.le)
    (hXm.min measurable_const).aemeasurable]
  have hcongr : ∫⁻ t in Ioi 0, μ {a | t < min (X a) c} =
      ∫⁻ t in Ioi 0, (Iio c).indicator (fun t ↦ ENNReal.ofReal (1 - Real.exp (-(v / t)))) t := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    by_cases htc : t < c
    · rw [indicator_of_mem (show t ∈ Iio c from htc), ← hX t ht]
      congr 1
      ext x
      simp [lt_min_iff, htc]
    · rw [indicator_of_notMem (show t ∉ Iio c from htc)]
      have : {a | t < min (X a) c} = ∅ := by
        ext x; simp only [mem_ofPred_eq, lt_min_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun _ ↦ htc
      rw [this, measure_empty]
  rw [hcongr, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, intervalIntegral.integral_of_le hc.le, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal]
  · exact ((intervalIntegrable_one_sub_exp hv hc.le).1).mono_set Ioo_subset_Ioc_self
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht ↦ ?_)
    have : Real.exp (-(v / t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hv ht.1.le))
    simp only [Pi.zero_apply]
    linarith

/-- **Logarithmic growth of truncated means**: if `P(X > r) = 1 - exp (-v / r)` for `r > 0`,
then `E[min X (a M)] / log M → v` as `M → ∞`, for every `a > 0`. -/
theorem tendsto_lintegral_min_div_log (hXm : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    (hX : ∀ r > 0, μ {x | r < X x} = ENNReal.ofReal (1 - Real.exp (-(v / r)))) (hv : 0 < v)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun M : ℝ ↦ (∫⁻ x, ENNReal.ofReal (min (X x) (a * M)) ∂μ).toReal / Real.log M)
      atTop (𝓝 v) := by
  have hlow : Tendsto (fun M : ℝ ↦ v + (v * Real.log a - v * Real.log v) / Real.log M) atTop
      (𝓝 v) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have hup : Tendsto (fun M : ℝ ↦ v + (1 + v * Real.log a) / Real.log M) atTop (𝓝 v) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have hev : ∀ᶠ M : ℝ in atTop, 1 < M ∧ 1 ≤ a * M := by
    filter_upwards [eventually_gt_atTop 1, eventually_ge_atTop a⁻¹] with M hM hMa
    refine ⟨hM, ?_⟩
    calc (1 : ℝ) = a * a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
      _ ≤ a * M := by gcongr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hev] with M ⟨hM, haM⟩
    have hlog : 0 < Real.log M := Real.log_pos hM
    have h1 := le_integral_one_sub_exp hv (c := a * M) (by linarith)
    have h2 : Real.log (a * M) ≤ Real.log (a * M + v) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [lintegral_ofReal_min_eq hXm hX0 hX hv.le (by linarith),
      ENNReal.toReal_ofReal (integral_one_sub_exp_nonneg hv.le (by linarith))]
    rw [Real.log_mul ha.ne' (by linarith)] at h2
    rw [show v + (v * Real.log a - v * Real.log v) / Real.log M =
      (v * (Real.log a + Real.log M) - v * Real.log v) / Real.log M by field_simp; ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hlog.le
  · filter_upwards [hev] with M ⟨hM, haM⟩
    have hlog : 0 < Real.log M := Real.log_pos hM
    rw [lintegral_ofReal_min_eq hXm hX0 hX hv.le (by linarith),
      ENNReal.toReal_ofReal (integral_one_sub_exp_nonneg hv.le (by linarith))]
    have h1 := integral_one_sub_exp_le hv haM
    rw [Real.log_mul ha.ne' (by linarith)] at h1
    rw [show v + (1 + v * Real.log a) / Real.log M =
      (1 + v * (Real.log a + Real.log M)) / Real.log M by field_simp; ring]
    exact div_le_div_of_nonneg_right h1 hlog.le

end Truncated

end ExtremeValueTheory
