/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The trigamma function at `1` and the second derivative of `Γ`

We compute the values of the trigamma function `ψ' = (log Γ)''` at `1/2` and `1` without any
series: differentiating Euler's reflection formula `ψ(1 - s) = ψ(s) + π cot(π s)` at `s = 1/2`
gives `ψ'(1/2) = π² / 2`, and differentiating the duplication formula
`ψ(2s) = (ψ(s) + ψ(s + 1/2)) / 2 + log 2` at `s = 1/2` gives `2 ψ'(1) = (ψ'(1/2) + ψ'(1)) / 2`,
whence `ψ'(1) = π² / 6` (equivalently `ζ(2) = π² / 6`). Since `ψ' = Γ''/Γ - (Γ'/Γ)²` and
`Γ'(1) = -γ`, this yields `Γ''(1) = γ² + π² / 6`. Differentiating the Mellin representation of
`Γ'` once more under the integral sign identifies `Γ''(1)` with `∫_0^∞ (log t)² e^{-t} dt`.

## Main results

* `Complex.analyticAt_digamma_of_re_pos`: `ψ` is analytic on the right half-plane.
* `Complex.deriv_digamma_one_half`: `ψ'(1/2) = π² / 2`.
* `Complex.deriv_digamma_one`: `ψ'(1) = π² / 6`.
* `Complex.deriv_deriv_Gamma_one`: `Γ''(1) = γ² + π² / 6`.
* `Complex.hasDerivAt_deriv_Gamma_of_re_pos`: `Γ''(s) = ∫_0^∞ t^(s-1) (log t)² e^{-t} dt`.
* `Real.integral_log_sq_mul_exp_neg`: `∫_0^∞ (log t)² e^{-t} dt = γ² + π² / 6`.

## References

* [M. Abramowitz, I. A. Stegun, *Handbook of Mathematical Functions*][abramowitz1964]
-/

open Filter Topology Set MeasureTheory
open scoped Real

namespace Complex

/-- `Γ` is complex-differentiable on the right half-plane. -/
lemma differentiableOn_Gamma_re_pos : DifferentiableOn ℂ Gamma {s : ℂ | 0 < s.re} := by
  intro s hs
  refine (differentiableAt_Gamma s fun m h ↦ ?_).differentiableWithinAt
  have : s.re = -m := by simp [h]
  simp only [mem_ofPred_eq] at hs
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  linarith

/-- `Γ` is analytic at every point of the right half-plane. -/
lemma analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gamma s :=
  differentiableOn_Gamma_re_pos.analyticAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hs)

/-- The digamma function is analytic at every point of the right half-plane. -/
lemma analyticAt_digamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ digamma s := by
  have : digamma = fun z ↦ deriv Gamma z / Gamma z := funext fun z ↦ logDeriv_apply _ _
  rw [this]
  exact (analyticAt_Gamma_of_re_pos hs).deriv.div (analyticAt_Gamma_of_re_pos hs)
    (Gamma_ne_zero_of_re_pos hs)

/-- The digamma function is differentiable on the right half-plane. -/
lemma hasDerivAt_digamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt digamma (deriv digamma s) s :=
  (analyticAt_digamma_of_re_pos hs).differentiableAt.hasDerivAt

/-- The derivative of `s ↦ π cot(π s)` at `1/2` is `-π²`. -/
lemma hasDerivAt_pi_mul_cot_one_half :
    HasDerivAt (fun s : ℂ ↦ π * cot (π * s)) (-π ^ 2) (1 / 2) := by
  have hl : HasDerivAt (fun s : ℂ ↦ (π : ℂ) * s) π (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (π : ℂ)
  have hpi : (π : ℂ) * (1 / 2) = π / 2 := by ring
  have hs := (hasDerivAt_sin ((π : ℂ) * (1 / 2))).comp (1 / 2 : ℂ) hl
  have hc := (hasDerivAt_cos ((π : ℂ) * (1 / 2))).comp (1 / 2 : ℂ) hl
  have hsin : sin ((π : ℂ) * (1 / 2)) ≠ 0 := by rw [hpi, sin_pi_div_two]; exact one_ne_zero
  have hd := (hc.div hs hsin).const_mul (π : ℂ)
  have hf : (fun s : ℂ ↦ (π : ℂ) * cot (π * s)) =
      fun s ↦ (π : ℂ) * ((cos ∘ fun s ↦ (π : ℂ) * s) s / (sin ∘ fun s ↦ (π : ℂ) * s) s) := by
    funext s; simp [cot_eq_cos_div_sin]
  rw [hf]
  convert hd using 1
  simp only [Function.comp_apply, hpi, sin_pi_div_two, cos_pi_div_two]
  ring

/-- The trigamma function at `1/2`: `ψ'(1/2) = π² / 2`, by differentiating the reflection
formula `ψ(1 - s) = ψ(s) + π cot(π s)` at `s = 1/2`. -/
theorem deriv_digamma_one_half : deriv digamma (1 / 2) = π ^ 2 / 2 := by
  have heq : (fun s ↦ digamma (1 - s)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun s ↦ digamma s + π * cot (π * s) := by
    have hU : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    filter_upwards [hU.mem_nhds (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1)]
      with s hs
    refine digamma_one_sub fun n h ↦ ?_
    have hre : s.re = n := by simp [h]
    obtain ⟨h0, h1⟩ := hs
    rw [hre] at h0 h1
    have h0' : (0 : ℤ) < n := by exact_mod_cast h0
    have h1' : n < 1 := by exact_mod_cast h1
    omega
  have hψ : HasDerivAt digamma (deriv digamma (1 / 2)) (1 - 1 / 2) := by
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
    exact hasDerivAt_digamma_of_re_pos (by norm_num)
  have hL := hψ.comp (1 / 2 : ℂ) ((hasDerivAt_id (1 / 2 : ℂ)).const_sub 1)
  have hR := ((hasDerivAt_digamma_of_re_pos (s := 1 / 2) (by norm_num)).add
    hasDerivAt_pi_mul_cot_one_half).congr_of_eventuallyEq heq
  have := hL.unique hR
  linear_combination -this / 2

/-- The trigamma function at `1`: `ψ'(1) = π² / 6`, by differentiating the duplication formula
`ψ(2s) = (ψ(s) + ψ(s + 1/2)) / 2 + log 2` at `s = 1/2` and using `ψ'(1/2) = π² / 2`. -/
theorem deriv_digamma_one : deriv digamma 1 = π ^ 2 / 6 := by
  have heq : (fun s ↦ digamma (2 * s)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun s ↦ (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)] with s hs
    refine digamma_two_mul fun m h ↦ ?_
    have hre : 2 * s.re = -m := by simpa using congrArg re h
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    have hs' : 0 < s.re := hs
    linarith
  have h1 : HasDerivAt digamma (deriv digamma 1) (2 * (1 / 2)) := by
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num]
    exact hasDerivAt_digamma_of_re_pos (by norm_num)
  have h1' : HasDerivAt digamma (deriv digamma 1) (1 / 2 + 1 / 2) := by
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]
    exact hasDerivAt_digamma_of_re_pos (by norm_num)
  have hL : HasDerivAt (fun s ↦ digamma (2 * s)) (deriv digamma 1 * (2 * 1)) (1 / 2) :=
    h1.comp (1 / 2 : ℂ) ((hasDerivAt_id' (1 / 2 : ℂ)).const_mul 2)
  have h3 : HasDerivAt (fun s ↦ digamma (s + 1 / 2)) (deriv digamma 1 * 1) (1 / 2) :=
    HasDerivAt.comp (h := fun s : ℂ ↦ s + 1 / 2) (1 / 2 : ℂ) h1'
      ((hasDerivAt_id' (1 / 2 : ℂ)).add_const (1 / 2))
  have hψ : HasDerivAt (fun s ↦ digamma s) (deriv digamma (1 / 2)) (1 / 2) :=
    hasDerivAt_digamma_of_re_pos (by norm_num)
  have hR : HasDerivAt (fun s ↦ (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2)
      ((1 / 2) * (deriv digamma (1 / 2) + deriv digamma 1 * 1)) (1 / 2) :=
    ((hψ.add h3).const_mul (1 / 2 : ℂ)).add_const (log 2)
  replace hR := hR.congr_of_eventuallyEq heq
  have := hL.unique hR
  have h2 := deriv_digamma_one_half
  linear_combination (2 / 3 : ℂ) * this + (1 / 3 : ℂ) * h2

/-- `Γ''(1) = γ² + π² / 6`. -/
theorem deriv_deriv_Gamma_one :
    deriv (deriv Gamma) 1 = Real.eulerMascheroniConstant ^ 2 + π ^ 2 / 6 := by
  have hΓ := analyticAt_Gamma_of_re_pos (s := 1) (by norm_num)
  have hdig : digamma = deriv Gamma / Gamma := funext fun z ↦ logDeriv_apply _ _
  have hd := hΓ.deriv.differentiableAt.hasDerivAt.div hasDerivAt_Gamma_one
    (by rw [Gamma_one]; exact one_ne_zero)
  rw [← hdig, hasDerivAt_Gamma_one.deriv, Gamma_one] at hd
  have := hd.unique (hasDerivAt_digamma_of_re_pos (by norm_num))
  rw [deriv_digamma_one] at this
  linear_combination this

/-- The derivative of `Γ'` on the right half-plane, as a Mellin transform:
`Γ''(s) = ∫_0^∞ t^(s-1) (log t)² e^{-t} dt` for `0 < re s`. -/
theorem hasDerivAt_deriv_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (deriv Gamma)
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * ((Real.log t ^ 2 * Real.exp (-t) : ℝ) : ℂ)) s := by
  set f : ℝ → ℂ := fun t ↦ ((Real.exp (-t) : ℝ) : ℂ) with hf
  have hf_top : f =O[atTop] (· ^ (-(s.re + 2))) := by
    rw [← Asymptotics.isBigO_norm_left]
    simp_rw [hf, norm_real, Asymptotics.isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  have hf_bot : f =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    simp_rw [neg_zero, Real.rpow_zero]
    refine Asymptotics.isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
    rw [(by simp : (1 : ℂ) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt
  set f₁ : ℝ → ℂ := fun t ↦ Real.log t • f t with hf₁
  have hf₁c : LocallyIntegrableOn f₁ (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi
    exact ((Real.continuousAt_log ht.ne').smul (by fun_prop)).continuousWithinAt
  have hd := (mellin_hasDerivAt_of_isBigO_rpow hf₁c
    (isBigO_rpow_top_log_smul (by linarith : s.re + 1 < s.re + 2) hf_top)
    (by linarith : s.re < s.re + 1)
    (isBigO_rpow_zero_log_smul (by linarith : (0 : ℝ) < s.re / 2) hf_bot)
    (by linarith : s.re / 2 < s.re)).2
  have heq : deriv Gamma =ᶠ[𝓝 s] mellin f₁ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    rw [(hasDerivAt_Gamma_of_re_pos hz).deriv, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp [hf₁, hf, real_smul]
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp only [hf₁, hf, real_smul, ofReal_mul, ofReal_pow]
  ring

end Complex

namespace Real

/-- `Γ''(1) = ∫_0^∞ (log t)² e^{-t} dt = γ² + π² / 6`. -/
theorem integral_log_sq_mul_exp_neg :
    ∫ t in Ioi 0, log t ^ 2 * exp (-t) = eulerMascheroniConstant ^ 2 + π ^ 2 / 6 := by
  have h := (Complex.hasDerivAt_deriv_Gamma_of_re_pos (s := 1) (by norm_num)).deriv
  rw [Complex.deriv_deriv_Gamma_one] at h
  simp only [sub_self, Complex.cpow_zero, one_mul] at h
  exact_mod_cast h.symm

end Real
