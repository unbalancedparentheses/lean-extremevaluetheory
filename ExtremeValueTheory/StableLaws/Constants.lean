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

/-- The Gamma-function representation `Γ(α + 1) u^(-α-1) = ∫₀^∞ x^α e^{-u x} dx` and Fubini:
`Γ(α + 1) ∫₀^∞ g(u) u^(-α-1) du = ∫₀^∞ x^α (∫₀^∞ g(u) e^{-x u} du) dx`. -/
theorem Gamma_mul_integral_mul_rpow {α : ℝ} (hα : -1 < α) {g : ℝ → ℝ} (hg : Measurable g)
    (hint : IntegrableOn (fun u => g u * u ^ (-α - 1)) (Ioi 0)) :
    Gamma (α + 1) * ∫ u in Ioi (0 : ℝ), g u * u ^ (-α - 1) =
      ∫ x in Ioi (0 : ℝ), x ^ α * ∫ u in Ioi (0 : ℝ), g u * Real.exp (-(x * u)) := by
  set F : ℝ → ℝ → ℝ := fun u x => g u * (x ^ α * Real.exp (-(u * x))) with hF
  have hα1 : 0 < α + 1 := by linarith
  have hgam : ∀ u, 0 < u → ∫ x in Ioi (0 : ℝ), x ^ α * Real.exp (-(u * x)) =
      u ^ (-α - 1) * Gamma (α + 1) := by
    intro u hu
    have h := integral_rpow_mul_exp_neg_mul_Ioi hα1 hu
    rw [show α + 1 - 1 = α by ring] at h
    rw [h, one_div, inv_rpow hu.le, ← rpow_neg hu.le, neg_add']
  have hsec : ∀ u, 0 < u → IntegrableOn (fun x => x ^ α * Real.exp (-(u * x))) (Ioi 0) := by
    intro u hu
    refine IntegrableOn.congr_fun (integrableOn_rpow_mul_exp_neg_mul_rpow hα one_pos hu)
      (fun x _ => ?_) measurableSet_Ioi
    simp only [rpow_one, neg_mul]
  have hin : ∀ u, 0 < u → ∫ x in Ioi (0 : ℝ), F u x = g u * u ^ (-α - 1) * Gamma (α + 1) := by
    intro u hu
    simp only [hF]
    rw [integral_const_mul, hgam u hu, mul_assoc]
  have hint2 : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_prod_iff (Measurable.aestronglyMeasurable (by simp only [hF]; fun_prop))).2
      ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun u hu => (hsec u hu).const_mul (g u)
    · refine IntegrableOn.congr_fun (hint.norm.mul_const (Gamma (α + 1)))
        (fun u hu => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair, hF, norm_mul]
      rw [integral_const_mul]
      rw [setIntegral_congr_fun measurableSet_Ioi
        (g := fun x => x ^ α * Real.exp (-(u * x))) fun x hx => ?_]
      · rw [hgam u hu, Real.norm_of_nonneg (rpow_pos_of_pos hu _).le]; ring
      · rw [Real.norm_of_nonneg (rpow_pos_of_pos hx _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Gamma (α + 1) * ∫ u in Ioi (0 : ℝ), g u * u ^ (-α - 1)
      = ∫ u in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F u x := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        rw [hin u hu]; ring
    _ = ∫ x in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F u x := integral_integral_swap hint2
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        simp only [hF]
        rw [← integral_const_mul]
        congr 1; funext u; rw [mul_comm u x]; ring

/-- `Γ(α + 1) ∫₀^∞ (1 - cos u) u^(-α-1) du = π / (2 sin (π α / 2))` for `0 < α < 2`. -/
theorem Gamma_mul_integral_one_sub_cos_mul_rpow {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Gamma (α + 1) * ∫ u in Ioi (0 : ℝ), (1 - cos u) * u ^ (-α - 1) =
      π / (2 * sin (π * α / 2)) := by
  have hint := integrableOn_one_sub_cos_mul_rpow hα0 hα2 1
  simp only [one_mul] at hint
  rw [Gamma_mul_integral_mul_rpow (by linarith) (by fun_prop) hint,
    ← integral_rpow_div_one_add_sq hα0 hα2]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx : (0 : ℝ) < x := hx
  have hsub : ∫ u in Ioi (0 : ℝ), (1 - cos u) * Real.exp (-(x * u)) = 1 / x - x / (1 + x ^ 2) := by
    rw [← integral_exp_neg_mul_Ioi hx, ← integral_cos_mul_exp_neg_mul hx, ← integral_sub
      (integrableOn_exp_neg_mul_Ioi hx) ((integrableOn_exp_neg_mul_Ioi hx).mono' (by fun_prop)
        (ae_of_all _ fun u => ?_))]
    · congr 1; funext u; ring
    · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (abs_cos_le_one u)
  rw [hsub, show x ^ α = x ^ (α - 1) * x by rw [← rpow_add_one hx.ne']; ring_nf]
  have : (1 + x ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `Γ(α + 1) ∫₀^∞ sin u · u^(-α-1) du = π / (2 cos (π α / 2))` for `0 < α < 1`. -/
theorem Gamma_mul_integral_sin_mul_rpow {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Gamma (α + 1) * ∫ u in Ioi (0 : ℝ), sin u * u ^ (-α - 1) = π / (2 * cos (π * α / 2)) := by
  have hint := integrableOn_sin_mul_rpow hα0 hα1 1
  simp only [one_mul] at hint
  rw [Gamma_mul_integral_mul_rpow (by linarith) (by fun_prop) hint,
    show π * α / 2 = π * (α + 1) / 2 - π / 2 by ring, Real.cos_sub_pi_div_two,
    ← integral_rpow_div_one_add_sq (by linarith : 0 < α + 1) (by linarith)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [integral_sin_mul_exp_neg_mul hx, add_sub_cancel_right]
  ring

variable {α : ℝ}

theorem sin_pi_mul_div_two_pos (hα0 : 0 < α) (hα2 : α < 2) : 0 < sin (π * α / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])

theorem cos_pi_mul_div_two_ne_zero (hα0 : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) :
    cos (π * α / 2) ≠ 0 := by
  rcases lt_or_gt_of_ne hα1 with h | h
  · exact (Real.cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩).ne'
  · exact (Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [pi_pos])
      (by nlinarith [pi_pos])).ne

/-- `C_α = π / (2 sin (π α / 2) Γ(α))` for `0 < α < 2` ([Feller, Vol. II, §XVII.4]). -/
theorem stableConst_eq_pi_div (hα0 : 0 < α) (hα2 : α < 2) :
    stableConst α = π / (2 * sin (π * α / 2) * Gamma α) := by
  have h := Gamma_mul_integral_one_sub_cos_mul_rpow hα0 hα2
  have hs := sin_pi_mul_div_two_pos hα0 hα2
  have hg : 0 < Gamma α := Real.Gamma_pos_of_pos hα0
  rw [Real.Gamma_add_one hα0.ne'] at h
  rw [stableConst, show π / (2 * sin (π * α / 2) * Gamma α) =
    π / (2 * sin (π * α / 2)) / Gamma α by rw [div_div],
    ← h]
  field_simp

/-- `C_1 = π / 2` ([Feller, Vol. II, §XVII.4]): the Cauchy case. -/
theorem stableConst_one : stableConst 1 = π / 2 := by
  rw [stableConst_eq_pi_div one_pos one_lt_two, mul_one, Real.sin_pi_div_two, Real.Gamma_one]
  ring

/-- `E_α = π / (2 cos (π α / 2) Γ(α))` for `0 < α < 2`, `α ≠ 1`. -/
theorem stableSkewConst_eq_pi_div (hα0 : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) :
    stableSkewConst α = π / (2 * cos (π * α / 2) * Gamma α) := by
  have hc := cos_pi_mul_div_two_ne_zero hα0 hα2 hα1
  have hg : 0 < Gamma α := Real.Gamma_pos_of_pos hα0
  rcases lt_or_gt_of_ne hα1 with h1 | h1
  · have h := Gamma_mul_integral_sin_mul_rpow hα0 h1
    rw [Real.Gamma_add_one hα0.ne'] at h
    rw [stableSkewConst, ite_eq_left h1, show π / (2 * cos (π * α / 2) * Gamma α) =
      π / (2 * cos (π * α / 2)) / Gamma α by rw [div_div],
      ← h]
    field_simp
  · have h := Gamma_mul_integral_one_sub_cos_mul_rpow (α := α - 1) (by linarith) (by linarith)
    rw [show α - 1 + 1 = α by ring, show -(α - 1) - 1 = -α by ring,
      show π * (α - 1) / 2 = π * α / 2 - π / 2 by ring, Real.sin_sub_pi_div_two] at h
    rw [stableSkewConst, ite_eq_right (by linarith), show π / (2 * cos (π * α / 2) * Gamma α) =
      -(π / (2 * -cos (π * α / 2)) / Gamma α) by field_simp, ← h]
    field_simp

theorem Gamma_one_sub_eq (hα0 : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) :
    Gamma (1 - α) = π / (2 * sin (π * α / 2) * cos (π * α / 2) * Gamma α) := by
  have hc := cos_pi_mul_div_two_ne_zero hα0 hα2 hα1
  have hs := sin_pi_mul_div_two_pos hα0 hα2
  have hg : 0 < Gamma α := Real.Gamma_pos_of_pos hα0
  have h := Real.Gamma_mul_Gamma_one_sub α
  rw [show π * α = 2 * (π * α / 2) by ring, Real.sin_two_mul] at h
  have h' : Gamma α * Gamma (1 - α) * (2 * sin (π * α / 2) * cos (π * α / 2)) = π := by
    rw [h]; field_simp
  rw [eq_div_iff (by positivity)]
  linear_combination h'

/-- **Closed form of `C_α`**: `C_α = Γ(1 - α) cos (π α / 2)` for `0 < α < 2`, `α ≠ 1`
([Feller, Vol. II, §XVII.4, (4.9)], [ST, (1.1.6)]). For `1 < α < 2` both factors are negative;
equivalently `C_α = Γ(2 - α) cos (π α / 2) / (1 - α)`. -/
theorem stableConst_eq_Gamma_mul_cos (hα0 : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) :
    stableConst α = Gamma (1 - α) * cos (π * α / 2) := by
  have hc := cos_pi_mul_div_two_ne_zero hα0 hα2 hα1
  have hs := sin_pi_mul_div_two_pos hα0 hα2
  have hg : 0 < Gamma α := Real.Gamma_pos_of_pos hα0
  rw [stableConst_eq_pi_div hα0 hα2, Gamma_one_sub_eq hα0 hα2 hα1]
  field_simp

/-- **Closed form of `E_α`**: `E_α = Γ(1 - α) sin (π α / 2)` for `0 < α < 2`, `α ≠ 1`
([Feller, Vol. II, §XVII.4], [ST, (1.1.6)]). -/
theorem stableSkewConst_eq_Gamma_mul_sin (hα0 : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) :
    stableSkewConst α = Gamma (1 - α) * sin (π * α / 2) := by
  have hc := cos_pi_mul_div_two_ne_zero hα0 hα2 hα1
  have hs := sin_pi_mul_div_two_pos hα0 hα2
  have hg : 0 < Gamma α := Real.Gamma_pos_of_pos hα0
  rw [stableSkewConst_eq_pi_div hα0 hα2 hα1, Gamma_one_sub_eq hα0 hα2 hα1]
  field_simp

/-- `E_α = C_α tan (π α / 2)` for `0 < α < 2`, `α ≠ 1` ([ST, (1.1.6)]). -/
theorem stableSkewConst_eq_mul_tan (hα0 : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) :
    stableSkewConst α = stableConst α * tan (π * α / 2) := by
  have hc := cos_pi_mul_div_two_ne_zero hα0 hα2 hα1
  rw [stableSkewConst_eq_Gamma_mul_sin hα0 hα2 hα1, stableConst_eq_Gamma_mul_cos hα0 hα2 hα1,
    Real.tan_eq_sin_div_cos, mul_assoc]
  congr 1
  field_simp

end StableIntegral

end ExtremeValueTheory
