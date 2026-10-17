/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The integrals behind the symmetric stable characteristic function

For `0 < α < 2` the constant in the characteristic function `exp (-C_α |t| ^ α)` of the
symmetric `α`-stable limit in the generalized central limit theorem is
`C_α = α ∫₀^∞ (1 - cos u) u ^ (-α - 1) du` ([Feller, Vol. II, §XVII.4, (4.4)–(4.9)],
[GK, §35], [EKM, §2.2]). Classically `C_α = Γ(1 - α) cos (π α / 2)` (`α ≠ 1`), `C_1 = π / 2`;
we only need `0 < C_α < ∞`.

This file contains the deterministic analysis:

* `integrableOn_one_sub_cos_mul_rpow`: `u ↦ (1 - cos (t u)) u ^ (-α - 1)` is integrable on
  `(0, ∞)`.
* `integral_one_sub_cos_mul_rpow`: scaling, `∫₀^∞ (1 - cos (t u)) u^(-α-1) du = |t|^α ∫₀^∞ ⋯`.
* `stableConst`, `stableConst_pos`.
* `intervalIntegral_sin_mul_rpow_eq`: the integration by parts
  `∫₀^M t sin (t u) u^(-α) du = (1 - cos (t M)) M^(-α) + α ∫₀^M (1 - cos (t u)) u^(-α-1) du`.
* `tendsto_intervalIntegral_sin_mul_rpow`: `∫₀^M t sin (t u) u^(-α) du → C_α |t|^α` as
  `M → ∞`.
-/

open MeasureTheory Filter Topology Set Real intervalIntegral

namespace ExtremeValueTheory

namespace StableIntegral

variable {α : ℝ}

theorem one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - cos x := by linarith [cos_le_one x]

theorem one_sub_cos_le_two (x : ℝ) : 1 - cos x ≤ 2 := by linarith [neg_one_le_cos x]

theorem one_sub_cos_le_sq (x : ℝ) : 1 - cos x ≤ x ^ 2 / 2 := by
  linarith [one_sub_sq_div_two_le_cos (x := x)]

/-- `|t sin (t u) u^(-α)| ≤ t² u^(1-α)` for `u > 0`. -/
theorem abs_sin_mul_rpow_le (t : ℝ) {u : ℝ} (hu : 0 < u) :
    |t * sin (t * u) * u ^ (-α)| ≤ t ^ 2 * u ^ (1 - α) := by
  have h1 : u ^ (1 - α) = u * u ^ (-α) := by
    rw [show 1 - α = 1 + -α by ring, rpow_add hu, rpow_one]
  rw [h1, abs_mul, abs_mul, abs_of_pos (rpow_pos_of_pos hu _)]
  have h2 : |sin (t * u)| ≤ |t| * u := by
    have := abs_sin_le_abs (x := t * u); rwa [abs_mul, abs_of_pos hu] at this
  have h3 : 0 ≤ u ^ (-α) := (rpow_pos_of_pos hu _).le
  calc |t| * |sin (t * u)| * u ^ (-α) ≤ |t| * (|t| * u) * u ^ (-α) := by gcongr
    _ = t ^ 2 * (u * u ^ (-α)) := by rw [← sq_abs t]; ring

/-- `0 ≤ (1 - cos (t u)) u^(-α-1) ≤ t²/2 u^(1-α)` for `u > 0`. -/
theorem one_sub_cos_mul_rpow_le (t : ℝ) {u : ℝ} (hu : 0 < u) :
    (1 - cos (t * u)) * u ^ (-α - 1) ≤ t ^ 2 / 2 * u ^ (1 - α) := by
  have h1 : u ^ (1 - α) = u ^ 2 * u ^ (-α - 1) := by
    rw [show 1 - α = (2 : ℕ) + (-α - 1) by push_cast; ring, rpow_add hu, rpow_natCast]
  rw [h1]
  have h3 : 0 ≤ u ^ (-α - 1) := (rpow_pos_of_pos hu _).le
  calc (1 - cos (t * u)) * u ^ (-α - 1) ≤ (t * u) ^ 2 / 2 * u ^ (-α - 1) := by
        gcongr; exact one_sub_cos_le_sq _
    _ = t ^ 2 / 2 * (u ^ 2 * u ^ (-α - 1)) := by ring

theorem one_sub_cos_mul_rpow_nonneg (t : ℝ) {u : ℝ} (hu : 0 < u) :
    0 ≤ (1 - cos (t * u)) * u ^ (-α - 1) :=
  mul_nonneg (one_sub_cos_nonneg _) (rpow_pos_of_pos hu _).le

theorem intervalIntegrable_rpow_one_sub (hα2 : α < 2) (M : ℝ) :
    IntervalIntegrable (fun u : ℝ => u ^ (1 - α)) volume 0 M :=
  intervalIntegrable_rpow' (by linarith)

theorem intervalIntegrable_sin_mul_rpow (hα2 : α < 2) (t : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    IntervalIntegrable (fun u : ℝ => t * sin (t * u) * u ^ (-α)) volume 0 M := by
  refine ((intervalIntegrable_rpow_one_sub hα2 M).const_mul (t ^ 2)).mono_fun' (by fun_prop) ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun u hu => ?_
  rw [uIoc_of_le hM] at hu
  rw [Real.norm_eq_abs]
  exact abs_sin_mul_rpow_le t hu.1

theorem intervalIntegrable_one_sub_cos_mul_rpow (hα2 : α < 2) (t : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    IntervalIntegrable (fun u : ℝ => (1 - cos (t * u)) * u ^ (-α - 1)) volume 0 M := by
  refine ((intervalIntegrable_rpow_one_sub hα2 M).const_mul (t ^ 2 / 2)).mono_fun'
    (by fun_prop) ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun u hu => ?_
  rw [uIoc_of_le hM] at hu
  rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_mul_rpow_nonneg t hu.1)]
  exact one_sub_cos_mul_rpow_le t hu.1

/-- `u ↦ (1 - cos (t u)) u ^ (-α - 1)` is integrable on `(0, ∞)` for `0 < α < 2`. -/
theorem integrableOn_one_sub_cos_mul_rpow (hα0 : 0 < α) (hα2 : α < 2) (t : ℝ) :
    IntegrableOn (fun u : ℝ => (1 - cos (t * u)) * u ^ (-α - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegrable_one_sub_cos_mul_rpow hα2 t zero_le_one)
  · refine ((integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) one_pos).const_mul 2).mono'
      (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := one_pos.trans hu
    rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_mul_rpow_nonneg t hu0)]
    exact mul_le_mul_of_nonneg_right (one_sub_cos_le_two _) (rpow_pos_of_pos hu0 _).le

/-- Scaling: `∫₀^∞ (1 - cos (t u)) u^(-α-1) du = |t|^α ∫₀^∞ (1 - cos u) u^(-α-1) du`. -/
theorem integral_one_sub_cos_mul_rpow (hα0 : 0 < α) (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), (1 - cos (t * u)) * u ^ (-α - 1) =
      |t| ^ α * ∫ u in Ioi (0 : ℝ), (1 - cos u) * u ^ (-α - 1) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [zero_rpow hα0.ne']
  have hs : 0 < |t| := abs_pos.2 ht
  have hcos : ∀ u, cos (t * u) = cos (|t| * u) := fun u => by
    rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, neg_mul, cos_neg]
  set g : ℝ → ℝ := fun v => (1 - cos v) * v ^ (-α - 1) with hg
  have h1 : ∫ u in Ioi (0 : ℝ), (1 - cos (t * u)) * u ^ (-α - 1) =
      ∫ u in Ioi (0 : ℝ), |t| ^ (α + 1) * g (|t| * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [hg, hcos]
    rw [mul_rpow hs.le (le_of_lt hu)]
    have : |t| ^ (α + 1) * |t| ^ (-α - 1) = 1 := by
      rw [← rpow_add hs]; simp
    calc (1 - cos (|t| * u)) * u ^ (-α - 1)
        = (|t| ^ (α + 1) * |t| ^ (-α - 1)) * ((1 - cos (|t| * u)) * u ^ (-α - 1)) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [h1, MeasureTheory.integral_const_mul, integral_comp_mul_left_Ioi g 0 hs, mul_zero, smul_eq_mul,
    ← mul_assoc, ← rpow_neg_one, ← rpow_add hs]
  simp [hg]

/-- The constant `C_α = α ∫₀^∞ (1 - cos u) u^(-α-1) du` of the symmetric `α`-stable limit
([Feller, §XVII.4]). -/
noncomputable def stableConst (α : ℝ) : ℝ := α * ∫ u in Ioi (0 : ℝ), (1 - cos u) * u ^ (-α - 1)

theorem stableConst_pos (hα0 : 0 < α) (hα2 : α < 2) : 0 < stableConst α := by
  refine mul_pos hα0 ?_
  have hint := integrableOn_one_sub_cos_mul_rpow hα0 hα2 1
  simp only [one_mul] at hint
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo 0 π) ?_)
    · simp [pi_pos]
    · intro u hu
      refine ⟨?_, hu.1⟩
      have hc : cos u < cos 0 := cos_lt_cos_of_nonneg_of_le_pi le_rfl hu.2.le hu.1
      rw [cos_zero] at hc
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
      exact ⟨by linarith, (rpow_pos_of_pos hu.1 _).ne'⟩
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun u hu => by
      simpa using one_sub_cos_mul_rpow_nonneg (α := α) 1 hu

/-- **Integration by parts**:
`∫₀^M t sin (t u) u^(-α) du = (1 - cos (t M)) M^(-α) + α ∫₀^M (1 - cos (t u)) u^(-α-1) du`. -/
theorem intervalIntegral_sin_mul_rpow_eq (hα2 : α < 2) (t : ℝ) {M : ℝ}
    (hM : 0 < M) :
    ∫ u in (0 : ℝ)..M, t * sin (t * u) * u ^ (-α) =
      (1 - cos (t * M)) * M ^ (-α) + α * ∫ u in (0 : ℝ)..M, (1 - cos (t * u)) * u ^ (-α - 1) := by
  set f₁ : ℝ → ℝ := fun u => t * sin (t * u) * u ^ (-α) with hf₁
  set f₂ : ℝ → ℝ := fun u => (1 - cos (t * u)) * u ^ (-α - 1) with hf₂
  have hi₁ := intervalIntegrable_sin_mul_rpow hα2 t hM.le
  have hi₂ := intervalIntegrable_one_sub_cos_mul_rpow hα2 t hM.le
  -- the identity on `[ε, M]`
  have key : ∀ ε ∈ Ioo 0 M, ∫ u in ε..M, f₁ u =
      (1 - cos (t * M)) * M ^ (-α) - (1 - cos (t * ε)) * ε ^ (-α) + α * ∫ u in ε..M, f₂ u := by
    intro ε hε
    have hsub : ∀ x ∈ uIcc ε M, 0 < x := fun x hx => by
      rw [uIcc_of_le hε.2.le] at hx; exact hε.1.trans_le hx.1
    have hu : ∀ x ∈ uIcc ε M, HasDerivAt (fun x : ℝ => x ^ (-α)) (-α * x ^ (-α - 1)) x :=
      fun x hx => hasDerivAt_rpow_const (Or.inl (hsub x hx).ne')
    have hv : ∀ x ∈ uIcc ε M, HasDerivAt (fun x : ℝ => 1 - cos (t * x)) (t * sin (t * x)) x := by
      intro x _
      have := (((hasDerivAt_id' x).const_mul t).cos).const_sub 1
      convert this using 1; ring
    have hu' : IntervalIntegrable (fun x : ℝ => -α * x ^ (-α - 1)) volume ε M := by
      refine ContinuousOn.intervalIntegrable fun x hx => ?_
      exact ((continuousAt_rpow_const x _ (Or.inl (hsub x hx).ne')).const_mul _).continuousWithinAt
    have hv' : IntervalIntegrable (fun x : ℝ => t * sin (t * x)) volume ε M :=
      (by fun_prop : Continuous fun x : ℝ => t * sin (t * x)).intervalIntegrable _ _
    have h := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    have e1 : ∫ x in ε..M, x ^ (-α) * (t * sin (t * x)) = ∫ u in ε..M, f₁ u :=
      integral_congr fun x _ => by simp only [hf₁]; ring
    have e2 : ∫ x in ε..M, -α * x ^ (-α - 1) * (1 - cos (t * x)) = -α * ∫ u in ε..M, f₂ u := by
      rw [← intervalIntegral.integral_const_mul]; exact integral_congr fun x _ => by simp only [hf₂]; ring
    rw [e1, e2] at h
    rw [h]; ring
  -- pass to the limit `ε → 0+`
  have hIcc : Icc 0 M ∈ 𝓝[>] (0 : ℝ) := mem_of_superset (Ioo_mem_nhdsGT hM) Ioo_subset_Icc_self
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 M] 0 := nhdsWithin_le_of_mem hIcc
  have hlim : ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume 0 M →
      Tendsto (fun ε => ∫ u in ε..M, f u) (𝓝[>] 0) (𝓝 (∫ u in (0 : ℝ)..M, f u)) := by
    intro f hf
    have hc := continuousOn_primitive_interval_left (a := 0) (b := M) (f := f) (μ := volume)
      (by rw [uIcc_of_le hM.le, integrableOn_Icc_iff_integrableOn_Ioc]
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1 hf)
    have := (hc 0 (by rw [uIcc_of_le hM.le]; exact ⟨le_rfl, hM.le⟩))
    rw [uIcc_of_le hM.le] at this
    exact this.tendsto.mono_left hle
  have hbd : Tendsto (fun ε : ℝ => (1 - cos (t * ε)) * ε ^ (-α)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => t ^ 2 / 2 * ε ^ (2 - α)) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuousAt_rpow_const 0 (2 - α) (Or.inr (by linarith))).tendsto.const_mul
        (t ^ 2 / 2)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [zero_rpow (by linarith : (2 : ℝ) - α ≠ 0)] using this
    refine squeeze_zero' ?_ ?_ hc
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_nonneg (one_sub_cos_nonneg _) (rpow_pos_of_pos hε _).le
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have e : ε ^ (2 - α) = ε ^ 2 * ε ^ (-α) := by
        rw [show 2 - α = (2 : ℕ) + -α by push_cast; ring, rpow_add hε, rpow_natCast]
      rw [e]
      calc (1 - cos (t * ε)) * ε ^ (-α) ≤ (t * ε) ^ 2 / 2 * ε ^ (-α) := by
            gcongr
            exact one_sub_cos_le_sq _
        _ = _ := by ring
  have hR : Tendsto (fun ε => (1 - cos (t * M)) * M ^ (-α) - (1 - cos (t * ε)) * ε ^ (-α) +
      α * ∫ u in ε..M, f₂ u) (𝓝[>] 0)
      (𝓝 ((1 - cos (t * M)) * M ^ (-α) - 0 + α * ∫ u in (0 : ℝ)..M, f₂ u)) :=
    (tendsto_const_nhds.sub hbd).add ((hlim hi₂).const_mul α)
  have hL := hlim hi₁
  have hL' : Tendsto (fun ε => ∫ u in ε..M, f₁ u) (𝓝[>] 0)
      (𝓝 ((1 - cos (t * M)) * M ^ (-α) - 0 + α * ∫ u in (0 : ℝ)..M, f₂ u)) :=
    hR.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hM] with ε hε using (key ε hε).symm)
  have := tendsto_nhds_unique hL hL'
  rw [this, sub_zero]

/-- `∫₀^M t sin (t u) u^(-α) du → C_α |t|^α` as `M → ∞`. -/
theorem tendsto_intervalIntegral_sin_mul_rpow (hα0 : 0 < α) (hα2 : α < 2) (t : ℝ) :
    Tendsto (fun M => ∫ u in (0 : ℝ)..M, t * sin (t * u) * u ^ (-α)) atTop
      (𝓝 (stableConst α * |t| ^ α)) := by
  have h1 : Tendsto (fun M : ℝ => (1 - cos (t * M)) * M ^ (-α)) atTop (𝓝 0) := by
    have h2 := (tendsto_rpow_neg_atTop hα0).const_mul 2
    rw [mul_zero] at h2
    refine squeeze_zero' ?_ ?_ h2
    · filter_upwards [eventually_gt_atTop 0] with M hM
      exact mul_nonneg (one_sub_cos_nonneg _) (rpow_pos_of_pos hM _).le
    · filter_upwards [eventually_gt_atTop 0] with M hM
      exact mul_le_mul_of_nonneg_right (one_sub_cos_le_two _) (rpow_pos_of_pos hM _).le
  have h3 := (intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_one_sub_cos_mul_rpow hα0 hα2 t) tendsto_id).const_mul α
  have h4 := h1.add h3
  rw [zero_add, integral_one_sub_cos_mul_rpow hα0 t] at h4
  rw [show stableConst α * |t| ^ α =
      α * (|t| ^ α * ∫ u in Ioi (0 : ℝ), (1 - cos u) * u ^ (-α - 1)) by
    rw [stableConst]; ring]
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  rw [intervalIntegral_sin_mul_rpow_eq hα2 t hM]
  rfl

end StableIntegral

end ExtremeValueTheory
