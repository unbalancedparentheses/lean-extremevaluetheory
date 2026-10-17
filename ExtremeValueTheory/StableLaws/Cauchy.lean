/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.Basic
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Cauchy law is stable

We compute the characteristic function of Mathlib's Cauchy distribution
`ProbabilityTheory.cauchyMeasure x₀ γ` (density `γ / (π ((x - x₀)² + γ²))`):
`φ(t) = exp (i x₀ t - γ |t|)` ([Feller, Vol. II, §XV.2, Example (e) and §XVII.3]).

The computation goes through Fourier inversion: the Fourier transform (Mathlib normalization
`𝓕 f (w) = ∫ e^{-2π i v w} f v dv`) of `v ↦ exp (-2π |v|)` is the standard Cauchy density
`w ↦ 1 / (π (1 + w²))`, by splitting the integral at `0` and integrating exponentials; Fourier
inversion (`Continuous.fourierInv_fourier_eq`) then gives the characteristic function.

## Main results

* `charFun_cauchyMeasure`: `φ_{Cauchy(x₀, γ)}(t) = exp (i t x₀ - γ |t|)`.
* `isStrictlyStable_cauchyMeasure`: for `γ ≠ 0`, `Cauchy(x₀, γ)` is strictly stable with
  `aₙ = n`, i.e. `(X₁ + ⋯ + Xₙ) / n ∼ X₁` ([Feller, §VI.1]).
* `isSymmStable_cauchyMeasure`: `Cauchy(0, γ)` is symmetric `1`-stable with `c = γ`.
-/

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal Real FourierTransform RealInnerProductSpace

namespace ExtremeValueTheory

namespace CauchyCharFun

/-- The function `v ↦ exp (-2π |v|)`, whose Fourier transform is the standard Cauchy density. -/
noncomputable def expAbs (v : ℝ) : ℂ := ((Real.exp (-(2 * π * |v|)) : ℝ) : ℂ)

lemma kernel_Ioi (w v : ℝ) (hv : 0 < v) :
    cexp (↑(-2 * π * v * w) * I) • expAbs v = cexp ((-(2 * π) - 2 * π * w * I) * v) := by
  rw [expAbs, abs_of_pos hv, smul_eq_mul, ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma kernel_Iic (w v : ℝ) (hv : v ≤ 0) :
    cexp (↑(-2 * π * v * w) * I) • expAbs v = cexp ((2 * π - 2 * π * w * I) * v) := by
  rw [expAbs, abs_of_nonpos hv, smul_eq_mul, ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma re_neg (w : ℝ) : (-(2 * π) - 2 * π * w * I : ℂ).re < 0 := by
  simp [Real.pi_pos]

lemma re_pos (w : ℝ) : 0 < (2 * π - 2 * π * w * I : ℂ).re := by
  simp [Real.pi_pos]

lemma integrableOn_Ioi (w : ℝ) :
    IntegrableOn (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) • expAbs v) (Ioi 0) :=
  (integrableOn_exp_mul_complex_Ioi (re_neg w) 0).congr_fun
    (fun v hv => (kernel_Ioi w v hv).symm) measurableSet_Ioi

lemma integrableOn_Iic (w : ℝ) :
    IntegrableOn (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) • expAbs v) (Iic 0) :=
  (integrableOn_exp_mul_complex_Iic (re_pos w) 0).congr_fun
    (fun v hv => (kernel_Iic w v hv).symm) measurableSet_Iic

lemma integrable_expAbs : Integrable expAbs := by
  have h := (integrableOn_Iic 0).union (integrableOn_Ioi 0)
  rw [Iic_union_Ioi, integrableOn_univ] at h
  simpa using h

lemma continuous_expAbs : Continuous expAbs := by
  unfold expAbs; fun_prop

lemma fourier_expAbs (w : ℝ) : 𝓕 expAbs w = (cauchyPDFReal 0 1 w : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← intervalIntegral.integral_Iic_add_Ioi (integrableOn_Iic w)
    (integrableOn_Ioi w), setIntegral_congr_fun measurableSet_Iic (fun v hv => kernel_Iic w v hv),
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => kernel_Ioi w v hv),
    integral_exp_mul_complex_Iic (re_pos w), integral_exp_mul_complex_Ioi (re_neg w)]
  have h1 : (2 * π - 2 * π * w * I : ℂ) ≠ 0 := fun h => by
    have := congrArg re h; simp [Real.pi_pos.ne'] at this
  have h2 : (-(2 * π) - 2 * π * w * I : ℂ) ≠ 0 := fun h => by
    have := congrArg re h; simp [Real.pi_pos.ne'] at this
  have h3 : ((w : ℂ) ^ 2 + 1) ≠ 0 := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]; exact_mod_cast (by positivity)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, cauchyPDFReal, NNReal.coe_one, sub_zero,
    one_pow, mul_one]
  have k1 : (1 - (w : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg re h; simp at this
  have k2 : (-1 - (w : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg re h; simp at this
  push_cast
  field_simp
  ring_nf
  field_simp
  ring_nf
  rw [I_sq]
  ring

lemma integral_cexp_mul_cauchyPDFReal (t : ℝ) :
    ∫ w : ℝ, (cauchyPDFReal 0 1 w : ℂ) * cexp (t * w * I) = Real.exp (-|t|) := by
  have hF : 𝓕 expAbs = fun w => (cauchyPDFReal 0 1 w : ℂ) := funext fourier_expAbs
  have hint : Integrable (𝓕 expAbs) := by
    rw [hF]; exact (integrable_cauchyPDFReal 0).ofReal
  have h := congrFun (continuous_expAbs.fourierInv_fourier_eq integrable_expAbs hint)
    (t / (2 * π))
  rw [hF, Real.fourierInv_eq'] at h
  have hπ : (0 : ℝ) < 2 * π := by positivity
  convert h using 1
  · congr 1; ext w
    rw [smul_eq_mul, mul_comm]
    congr 3
    simp only [RCLike.inner_apply, conj_trivial]
    field_simp
    push_cast; ring
  · rw [expAbs, abs_div, abs_of_pos hπ]
    congr 2
    field_simp

end CauchyCharFun

open CauchyCharFun

/-- **Characteristic function of the Cauchy law**: `φ(t) = exp (i t x₀ - γ |t|)`
([Feller, Vol. II, §XV.2]). -/
theorem charFun_cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) (t : ℝ) :
    charFun (cauchyMeasure x₀ γ) t = cexp (t * x₀ * I - γ * |t|) := by
  by_cases hγ : γ = 0
  · subst hγ
    simp [mul_comm]
  have hγ' : (0 : ℝ) < γ := lt_of_le_of_ne γ.2 (by exact_mod_cast Ne.symm hγ)
  rw [cauchyMeasure_of_scale_ne_zero x₀ hγ, charFun_apply_real,
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF x₀ γ)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos x₀ hγ _).le]
  set F : ℝ → ℂ := fun x => cauchyPDFReal x₀ γ x • cexp (t * x * I) with hF
  have h1 : ∫ x, F x = ∫ x, F (x + x₀) := (integral_add_right_eq_self F x₀).symm
  have h2 : ∫ z, F (γ * z + x₀) = |(γ : ℝ)⁻¹| • ∫ y, F (y + x₀) :=
    Measure.integral_comp_mul_left (fun y => F (y + x₀)) γ
  have h3 : ∀ z : ℝ, F (γ * z + x₀) =
      ((γ : ℝ)⁻¹ : ℂ) * cexp (t * x₀ * I) * ((cauchyPDFReal 0 1 z : ℂ) * cexp ((t * γ : ℝ) * z * I)) := by
    intro z
    simp only [hF, cauchyPDFReal, NNReal.coe_one, sub_zero, one_pow, mul_one, Complex.real_smul]
    have hγc : ((γ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hγ'.ne'
    have h4 : ((γ : ℝ) * z + x₀ - x₀) ^ 2 + (γ : ℝ) ^ 2 = (γ : ℝ) ^ 2 * (z ^ 2 + 1) := by ring
    rw [h4, show cexp (t * ((γ * z + x₀ : ℝ) : ℂ) * I) =
        cexp (t * x₀ * I) * cexp (((t * γ : ℝ) : ℂ) * z * I) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    have h5 : ((z : ℂ) ^ 2 + 1) ≠ 0 := by
      rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]; exact_mod_cast (by positivity)
    push_cast
    field_simp
  rw [h1]
  have h6 : ∫ y, F (y + x₀) = |(γ : ℝ)| • ∫ z, F (γ * z + x₀) := by
    rw [h2, smul_smul, abs_inv, mul_inv_cancel₀ (abs_pos.2 hγ'.ne').ne', one_smul]
  rw [h6]
  simp_rw [h3]
  rw [integral_const_mul, integral_cexp_mul_cauchyPDFReal, abs_of_pos hγ', abs_mul,
    abs_of_pos hγ', Complex.real_smul, ofReal_exp, ← mul_assoc, ← mul_assoc]
  rw [mul_inv_cancel₀ (ofReal_ne_zero.2 hγ'.ne'), one_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_charFun_cauchyMeasure_one_lt (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ‖charFun (cauchyMeasure x₀ γ) 1‖ < 1 := by
  have hγ' : (0 : ℝ) < γ := lt_of_le_of_ne γ.2 (by exact_mod_cast Ne.symm hγ)
  rw [charFun_cauchyMeasure, Complex.norm_exp]
  simp [hγ']

/-- **The Cauchy law is strictly stable** with `aₙ = n`: `Cauchy(x₀, γ)^{*n} = law (n X)`
([Feller, §VI.1, §XVII.3]). -/
theorem isStrictlyStable_cauchyMeasure (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    IsStrictlyStable (cauchyMeasure x₀ γ) where
  isProbabilityMeasure := inferInstance
  ne_dirac := ne_dirac_of_norm_charFun_lt_one (norm_charFun_cauchyMeasure_one_lt x₀ hγ)
  exists_mul n hn := by
    refine ⟨n, by exact_mod_cast hn, ?_⟩
    have := convPow_eq_map_of_charFun (μ := cauchyMeasure x₀ γ) (n := n) (a := n) (b := 0)
      fun t => by
        simp only [charFun_cauchyMeasure, ← Complex.exp_nat_mul, ofReal_zero, zero_mul,
          Complex.exp_zero, mul_one]
        congr 1
        rw [abs_mul, Nat.abs_cast]
        push_cast
        ring
    simpa using this

/-- The Cauchy law is stable. -/
theorem isStable_cauchyMeasure (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    IsStable (cauchyMeasure x₀ γ) :=
  (isStrictlyStable_cauchyMeasure x₀ hγ).isStable

/-- `Cauchy(0, γ)` is symmetric `1`-stable with `c = γ`: `φ(t) = exp (-γ |t|)`. -/
theorem isSymmStable_cauchyMeasure (γ : ℝ≥0) : IsSymmStable 1 γ (cauchyMeasure 0 γ) := by
  refine ⟨inferInstance, fun t => ?_⟩
  rw [charFun_cauchyMeasure, Real.rpow_one, ofReal_exp]
  congr 1
  push_cast
  ring

end ExtremeValueTheory
