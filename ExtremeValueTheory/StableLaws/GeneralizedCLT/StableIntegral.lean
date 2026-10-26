/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.DomainOfAttraction
import Mathlib.Basic.Real.Sign

/-!
# The skewness constant of stable laws

The improper integrals `∫₀^∞ sin u · u^(-α-1) du` (`0 < α < 1`) and
`∫₀^∞ (1 - cos u) u^(-α) du` (`1 < α < 2`), the integration-by-parts and scaling identities they
satisfy, and the skewness constant `stableSkewConst α` of the generalized central limit theorem.

## Main definitions

* `StableIntegral.stableSkewConst`: The skewness constant of the stable limit, `E_α = α ∫₀^∞ sin u ·
  u^(-α-1) du` for `0 < α < 1` and `E_α = -∫₀^∞ (1 - cos u) u^(-α) du` for `1 < α < 2` (the value
  for `α = 1` is not used).

This file is part of the proof in `ExtremeValueTheory.StableLaws.GeneralizedCLT`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), §XVII.5 [Feller].
* B. V. Gnedenko and A. N. Kolmogorov, *Limit Distributions for Sums of Independent Random
  Variables*, Addison-Wesley (1954), §35 [GK].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 2.2.8 [EKM].
* G. Samorodnitsky and M. S. Taqqu, *Stable Non-Gaussian Random Processes*, Chapman & Hall
  (1994) [ST].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

namespace StableIntegral

variable {α : ℝ}

theorem abs_sin_mul_le (t : ℝ) {u : ℝ} (hu : 0 ≤ u) : |sin (t * u)| ≤ |t| * u := by
  have := abs_sin_le_abs (x := t * u); rwa [abs_mul, abs_of_nonneg hu] at this

/-- Scaling: `∫₀^∞ h (s u) u^(-β-1) du = s^β ∫₀^∞ h(u) u^(-β-1) du` for `s > 0`. -/
theorem integral_comp_mul_mul_rpow {s : ℝ} (hs : 0 < s) (h : ℝ → ℝ) (β : ℝ) :
    ∫ u in Ioi (0 : ℝ), h (s * u) * u ^ (-β - 1) =
      s ^ β * ∫ u in Ioi (0 : ℝ), h u * u ^ (-β - 1) := by
  set g : ℝ → ℝ := fun v => h v * v ^ (-β - 1) with hg
  have h1 : ∫ u in Ioi (0 : ℝ), h (s * u) * u ^ (-β - 1) =
      ∫ u in Ioi (0 : ℝ), s ^ (β + 1) * g (s * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [hg]
    rw [mul_rpow hs.le (le_of_lt hu)]
    have : s ^ (β + 1) * s ^ (-β - 1) = 1 := by
      rw [← rpow_add hs]; simp
    calc h (s * u) * u ^ (-β - 1)
        = (s ^ (β + 1) * s ^ (-β - 1)) * (h (s * u) * u ^ (-β - 1)) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [h1, MeasureTheory.integral_const_mul, integral_comp_mul_left_Ioi g 0 hs, mul_zero,
    smul_eq_mul, ← mul_assoc, ← rpow_neg_one, ← rpow_add hs]
  simp [hg]

/-- `t |t|^(α-1) = sign t |t|^α`. -/
theorem mul_abs_rpow_sub_one (hα : 0 < α) (t : ℝ) :
    t * |t| ^ (α - 1) = Real.sign t * |t| ^ α := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h0 : 0 < |t| := abs_pos.2 ht.ne
    rw [Real.sign_of_neg ht, show α = (α - 1) + 1 by ring, rpow_add h0, rpow_one,
      abs_of_neg ht]
    ring_nf
  · simp [zero_rpow hα.ne']
  · rw [Real.sign_of_pos ht, abs_of_pos ht, one_mul]
    conv_rhs => rw [show α = (α - 1) + 1 by ring]
    rw [rpow_add ht, rpow_one, mul_comm]

/-- `u ↦ sin (t u) u^(-α-1)` is integrable on `(0, ∞)` for `0 < α < 1`. -/
theorem integrableOn_sin_mul_rpow (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) :
    IntegrableOn (fun u : ℝ => sin (t * u) * u ^ (-α - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have hi : IntegrableOn (fun u : ℝ => |t| * u ^ (-α)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
    refine hi.mono' (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have e : u ^ (-α) = u * u ^ (-α - 1) := by
      conv_lhs => rw [show -α = 1 + (-α - 1) by ring]
      rw [rpow_add hu.1, rpow_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos hu.1 _), e]
    calc |sin (t * u)| * u ^ (-α - 1) ≤ (|t| * u) * u ^ (-α - 1) :=
          mul_le_mul_of_nonneg_right (abs_sin_mul_le t hu.1.le) (rpow_pos_of_pos hu.1 _).le
      _ = _ := by ring
  · refine (integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) one_pos).mono'
      (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := one_pos.trans hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos hu0 _)]
    exact mul_le_of_le_one_left (rpow_pos_of_pos hu0 _).le (abs_sin_le_one _)

/-- Scaling: `∫₀^∞ sin (t u) u^(-α-1) du = sign t |t|^α ∫₀^∞ sin u u^(-α-1) du`. -/
theorem integral_sin_mul_rpow (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), sin (t * u) * u ^ (-α - 1) =
      Real.sign t * |t| ^ α * ∫ u in Ioi (0 : ℝ), sin u * u ^ (-α - 1) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := integral_comp_mul_mul_rpow (neg_pos.2 ht) sin α
    rw [Real.sign_of_neg ht, abs_of_neg ht]
    have : ∫ u in Ioi (0 : ℝ), sin (t * u) * u ^ (-α - 1) =
        -∫ u in Ioi (0 : ℝ), sin (-t * u) * u ^ (-α - 1) := by
      rw [← integral_neg]; congr 1; funext u; rw [neg_mul, sin_neg]; ring
    rw [this, h]; ring
  · simp [Real.sign_zero]
  · rw [Real.sign_of_pos ht, abs_of_pos ht, one_mul]
    exact integral_comp_mul_mul_rpow ht sin α

theorem intervalIntegrable_cos_mul_rpow (hα1 : α < 1) (t : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    IntervalIntegrable (fun u : ℝ => t * cos (t * u) * u ^ (-α)) volume 0 M := by
  refine ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -α)).const_mul
    |t|).mono_fun' (by fun_prop) ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun u hu => ?_
  rw [uIoc_of_le hM] at hu
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (rpow_pos_of_pos hu.1 _)]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
    (rpow_pos_of_pos hu.1 _).le

theorem intervalIntegrable_sin_mul_rpow' (hα1 : α < 1) (t : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    IntervalIntegrable (fun u : ℝ => sin (t * u) * u ^ (-α - 1)) volume 0 M := by
  refine ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -α)).const_mul
    |t|).mono_fun' (by fun_prop) ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun u hu => ?_
  rw [uIoc_of_le hM] at hu
  have e : u ^ (-α) = u * u ^ (-α - 1) := by
    conv_lhs => rw [show -α = 1 + (-α - 1) by ring]
    rw [rpow_add hu.1, rpow_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos hu.1 _), e]
  calc |sin (t * u)| * u ^ (-α - 1) ≤ (|t| * u) * u ^ (-α - 1) :=
        mul_le_mul_of_nonneg_right (abs_sin_mul_le t hu.1.le) (rpow_pos_of_pos hu.1 _).le
    _ = _ := by ring

/-- **Integration by parts**:
`∫₀^M t cos (t u) u^(-α) du = sin (t M) M^(-α) + α ∫₀^M sin (t u) u^(-α-1) du`. -/
theorem intervalIntegral_cos_mul_rpow_eq (hα1 : α < 1) (t : ℝ) {M : ℝ} (hM : 0 < M) :
    ∫ u in (0 : ℝ)..M, t * cos (t * u) * u ^ (-α) =
      sin (t * M) * M ^ (-α) + α * ∫ u in (0 : ℝ)..M, sin (t * u) * u ^ (-α - 1) := by
  set f₁ : ℝ → ℝ := fun u => t * cos (t * u) * u ^ (-α) with hf₁
  set f₂ : ℝ → ℝ := fun u => sin (t * u) * u ^ (-α - 1) with hf₂
  have hi₁ := intervalIntegrable_cos_mul_rpow hα1 t hM.le
  have hi₂ := intervalIntegrable_sin_mul_rpow' hα1 t hM.le
  have key : ∀ ε ∈ Ioo 0 M, ∫ u in ε..M, f₁ u =
      sin (t * M) * M ^ (-α) - sin (t * ε) * ε ^ (-α) + α * ∫ u in ε..M, f₂ u := by
    intro ε hε
    have hsub : ∀ x ∈ uIcc ε M, 0 < x := fun x hx => by
      rw [uIcc_of_le hε.2.le] at hx; exact hε.1.trans_le hx.1
    have hu : ∀ x ∈ uIcc ε M, HasDerivAt (fun x : ℝ => x ^ (-α)) (-α * x ^ (-α - 1)) x :=
      fun x hx => hasDerivAt_rpow_const (Or.inl (hsub x hx).ne')
    have hv : ∀ x ∈ uIcc ε M, HasDerivAt (fun x : ℝ => sin (t * x)) (t * cos (t * x)) x := by
      intro x _
      have := ((hasDerivAt_id' x).const_mul t).sin
      convert this using 1; ring
    have hu' : IntervalIntegrable (fun x : ℝ => -α * x ^ (-α - 1)) volume ε M := by
      refine ContinuousOn.intervalIntegrable fun x hx => ?_
      exact ((continuousAt_rpow_const x _ (Or.inl (hsub x hx).ne')).const_mul _).continuousWithinAt
    have hv' : IntervalIntegrable (fun x : ℝ => t * cos (t * x)) volume ε M :=
      (by fun_prop : Continuous fun x : ℝ => t * cos (t * x)).intervalIntegrable _ _
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    have e1 : ∫ x in ε..M, x ^ (-α) * (t * cos (t * x)) = ∫ u in ε..M, f₁ u :=
      intervalIntegral.integral_congr fun x _ => by simp only [hf₁]; ring
    have e2 : ∫ x in ε..M, -α * x ^ (-α - 1) * sin (t * x) = -α * ∫ u in ε..M, f₂ u := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by simp only [hf₂]; ring
    rw [e1, e2] at h
    rw [h]; ring
  have hIcc : Icc 0 M ∈ 𝓝[>] (0 : ℝ) := mem_of_superset (Ioo_mem_nhdsGT hM) Ioo_subset_Icc_self
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 M] 0 := nhdsWithin_le_of_mem hIcc
  have hlim : ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume 0 M →
      Tendsto (fun ε => ∫ u in ε..M, f u) (𝓝[>] 0) (𝓝 (∫ u in (0 : ℝ)..M, f u)) := by
    intro f hf
    have hc := intervalIntegral.continuousOn_primitive_interval_left (a := 0) (b := M) (f := f)
      (μ := volume)
      (by rw [uIcc_of_le hM.le, integrableOn_Icc_iff_integrableOn_Ioc]
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1 hf)
    have := (hc 0 (by rw [uIcc_of_le hM.le]; exact ⟨le_rfl, hM.le⟩))
    rw [uIcc_of_le hM.le] at this
    exact this.tendsto.mono_left hle
  have hbd : Tendsto (fun ε : ℝ => sin (t * ε) * ε ^ (-α)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => |t| * ε ^ (1 - α)) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuousAt_rpow_const 0 (1 - α) (Or.inr (by linarith))).tendsto.const_mul
        |t|).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [zero_rpow (by linarith : (1 : ℝ) - α ≠ 0)] using this
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have e : ε ^ (1 - α) = ε * ε ^ (-α) := by
      rw [show 1 - α = 1 + -α by ring, rpow_add hε, rpow_one]
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos hε _)]
    calc |sin (t * ε)| * ε ^ (-α) ≤ (|t| * ε) * ε ^ (-α) := by
          gcongr; exact abs_sin_mul_le t hε.le
      _ = _ := by ring
  have hR : Tendsto (fun ε => sin (t * M) * M ^ (-α) - sin (t * ε) * ε ^ (-α) +
      α * ∫ u in ε..M, f₂ u) (𝓝[>] 0)
      (𝓝 (sin (t * M) * M ^ (-α) - 0 + α * ∫ u in (0 : ℝ)..M, f₂ u)) :=
    (tendsto_const_nhds.sub hbd).add ((hlim hi₂).const_mul α)
  have hL := hlim hi₁
  have hL' : Tendsto (fun ε => ∫ u in ε..M, f₁ u) (𝓝[>] 0)
      (𝓝 (sin (t * M) * M ^ (-α) - 0 + α * ∫ u in (0 : ℝ)..M, f₂ u)) :=
    hR.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hM] with ε hε using (key ε hε).symm)
  have := tendsto_nhds_unique hL hL'
  rw [this, sub_zero]

/-- The skewness constant of the stable limit,
`E_α = α ∫₀^∞ sin u · u^(-α-1) du` for `0 < α < 1` and `E_α = -∫₀^∞ (1 - cos u) u^(-α) du` for
`1 < α < 2` (the value for `α = 1` is not used). Classically
`E_α = Γ(1 - α) sin (π α / 2) = C_α tan (π α / 2)` ([Feller, §XVII.4], [ST, (1.1.6)]). -/
noncomputable def stableSkewConst (α : ℝ) : ℝ :=
  if α < 1 then α * ∫ u in Ioi (0 : ℝ), sin u * u ^ (-α - 1)
  else -∫ u in Ioi (0 : ℝ), (1 - cos u) * u ^ (-α)

/-- `∫₀^M t cos (t u) u^(-α) du → E_α sign t |t|^α` as `M → ∞`, for `0 < α < 1`. -/
theorem tendsto_intervalIntegral_cos_mul_rpow (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) :
    Tendsto (fun M => ∫ u in (0 : ℝ)..M, t * cos (t * u) * u ^ (-α)) atTop
      (𝓝 (stableSkewConst α * Real.sign t * |t| ^ α)) := by
  have h1 : Tendsto (fun M : ℝ => sin (t * M) * M ^ (-α)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_rpow_neg_atTop hα0)
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos hM _)]
    exact mul_le_of_le_one_left (rpow_pos_of_pos hM _).le (abs_sin_le_one _)
  have h3 := (intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_sin_mul_rpow hα0 hα1 t) tendsto_id).const_mul α
  have h4 := h1.add h3
  rw [zero_add, integral_sin_mul_rpow t] at h4
  rw [show stableSkewConst α * Real.sign t * |t| ^ α =
      α * (Real.sign t * |t| ^ α * ∫ u in Ioi (0 : ℝ), sin u * u ^ (-α - 1)) by
    rw [stableSkewConst, ite_eq_left hα1]; ring]
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  rw [intervalIntegral_cos_mul_rpow_eq hα1 t hM]
  rfl

/-- For `1 < α < 2`, `-t ∫₀^∞ (1 - cos (t u)) u^(-α) du = E_α sign t |t|^α`. -/
theorem neg_mul_integral_one_sub_cos_mul_rpow (hα1 : 1 < α) (t : ℝ) :
    -(t * ∫ u in Ioi (0 : ℝ), (1 - cos (t * u)) * u ^ (-α)) =
      stableSkewConst α * Real.sign t * |t| ^ α := by
  have h := integral_one_sub_cos_mul_rpow (α := α - 1) (by linarith) t
  rw [show -(α - 1) - 1 = -α by ring] at h
  rw [h, stableSkewConst, ite_eq_right (by linarith : ¬α < 1), ← mul_assoc,
    mul_abs_rpow_sub_one (by linarith)]
  ring

end StableIntegral

end ExtremeValueTheory
