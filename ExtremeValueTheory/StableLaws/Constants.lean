/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Closed forms of the stable constants
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace ExtremeValueTheory

namespace StableIntegral

/-- `∫₀^∞ e^{-x u} du = 1 / x`. -/
theorem integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(x * u)) = 1 / x := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at h
  rw [h]; field_simp

theorem integrableOn_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-(x * u))) (Ioi 0) := by
  simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0

/-- The complex Laplace transform `∫₀^∞ e^{(-x + i) u} du = (x + i) / (1 + x²)`. -/
theorem integral_exp_neg_add_I_mul {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), Complex.exp ((-x + Complex.I) * u) =
      ((x / (1 + x ^ 2) : ℝ) : ℂ) + ((1 / (1 + x ^ 2) : ℝ) : ℂ) * Complex.I := by
  have ha : (-(x : ℂ) + Complex.I).re < 0 := by simp [hx]
  rw [integral_exp_mul_complex_Ioi ha 0]
  have hne : (-(x : ℂ) + Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have h1' : (1 + (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_eq_iff hne]
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * Complex.I_sq

theorem integrableOn_exp_neg_add_I_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Complex.exp ((-x + Complex.I) * u)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simp [hx]) 0

/-- `∫₀^∞ cos u e^{-x u} du = x / (1 + x²)`. -/
theorem integral_cos_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), cos u * Real.exp (-(x * u)) = x / (1 + x ^ 2) := by
  have h := congrArg Complex.re (integral_exp_neg_add_I_mul hx)
  have h2 := integral_re (integrableOn_exp_neg_add_I_mul hx)
  simp only [RCLike.re_to_complex] at h2
  rw [← h2] at h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp [Complex.exp_re, mul_comm]

/-- `∫₀^∞ sin u e^{-x u} du = 1 / (1 + x²)`. -/
theorem integral_sin_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), sin u * Real.exp (-(x * u)) = 1 / (1 + x ^ 2) := by
  have h := congrArg Complex.im (integral_exp_neg_add_I_mul hx)
  have h2 := integral_im (integrableOn_exp_neg_add_I_mul hx)
  simp only [RCLike.im_to_complex] at h2
  rw [← h2] at h
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp [Complex.exp_im, mul_comm]

/-- `∫₀^∞ x^(s-1) / (1 + x²) dx = π / (2 sin (π s / 2))` for `0 < s < 2`, via
`1 / (1 + x²) = ∫₀^∞ e^{-(1 + x²) y} dy`, Tonelli, and the reflection formula. -/
theorem integral_rpow_div_one_add_sq {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∫ x in Ioi (0 : ℝ), x ^ (s - 1) / (1 + x ^ 2) = π / (2 * sin (π * s / 2)) := by
  set f : ℝ → ℝ → ℝ := fun x y => x ^ (s - 1) * (Real.exp (-y) * Real.exp (-y * x ^ (2 : ℝ)))
    with hf
  have hq : -1 < s - 1 := by linarith
  have hin : ∀ y, 0 < y → ∫ x in Ioi (0 : ℝ), f x y =
      Real.exp (-y) * (y ^ (-s / 2) * (1 / 2) * Gamma (s / 2)) := by
    intro y hy
    have h := integral_rpow_mul_exp_neg_mul_rpow two_pos hq hy
    rw [show (s - 1 + 1) = s by ring] at h
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hf]; ring
  have hout : ∀ x, 0 < x → ∫ y in Ioi (0 : ℝ), f x y = x ^ (s - 1) / (1 + x ^ 2) := by
    intro x hx
    have h := integral_exp_neg_mul_Ioi (by positivity : (0 : ℝ) < 1 + x ^ 2)
    rw [div_eq_mul_one_div, ← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hf]
    rw [← Real.exp_add, rpow_two]; ring_nf
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_prod_iff' (Measurable.aestronglyMeasurable (by simp only [hf]; fun_prop))).2
      ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun y hy => ?_
      refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_exp_neg_mul_rpow hq two_pos hy).const_mul
        (Real.exp (-y))) (fun x _ => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair, hf]; ring_nf
    · refine IntegrableOn.congr_fun ((Real.GammaIntegral_convergent
        (by linarith : 0 < 1 - s / 2)).mul_const ((1 / 2) * Gamma (s / 2)))
        (fun y hy => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair]
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => f x y) fun x hx => ?_]
      · rw [hin y hy, show 1 - s / 2 - 1 = -s / 2 by ring]; ring
      · exact Real.norm_of_nonneg (by simp only [hf]; have := rpow_pos_of_pos hx (s - 1); positivity)
  calc ∫ x in Ioi (0 : ℝ), x ^ (s - 1) / (1 + x ^ 2)
      = ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f x y :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx => (hout x hx).symm
    _ = ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), f x y := integral_integral_swap hint
    _ = ∫ y in Ioi (0 : ℝ), Real.exp (-y) * y ^ (1 - s / 2 - 1) * ((1 / 2) * Gamma (s / 2)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        rw [hin y hy, show 1 - s / 2 - 1 = -s / 2 by ring]; ring
    _ = Gamma (1 - s / 2) * ((1 / 2) * Gamma (s / 2)) := by
        rw [integral_mul_const, ← Real.Gamma_eq_integral (by linarith)]
    _ = π / (2 * sin (π * s / 2)) := by
        have h := Real.Gamma_mul_Gamma_one_sub (s / 2)
        rw [show π * (s / 2) = π * s / 2 by ring] at h
        rw [show Gamma (1 - s / 2) * ((1 / 2) * Gamma (s / 2)) =
          (Gamma (s / 2) * Gamma (1 - s / 2)) / 2 by ring, h]
        field_simp

end StableIntegral

end ExtremeValueTheory
