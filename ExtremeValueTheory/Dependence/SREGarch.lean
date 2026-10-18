/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.SREExponent

/-!
# GARCH(1,1) and ARCH(1): the squared volatility as a stochastic recurrence

skeleton
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped ENNReal

namespace ExtremeValueTheory

namespace SRE

namespace GARCH

variable (α₀ α₁ β₁ : ℝ)

/-- The random multiplier `A = α₁ Z² + β₁` of the squared volatility recursion. -/
def coeff (z : ℝ) : ℝ := α₁ * z ^ 2 + β₁

/-- The innovation map `z ↦ (α₁ z² + β₁, α₀)`. -/
def innov (z : ℝ) : ℝ × ℝ := (coeff α₁ β₁ z, α₀)

/-- The law of the coefficients `(A, B) = (α₁ Z² + β₁, α₀)` for `Z ∼ ζ`. -/
noncomputable def coeffLaw (ζ : Measure ℝ) : Measure (ℝ × ℝ) := ζ.map (innov α₀ α₁ β₁)

theorem measurable_coeff : Measurable (coeff α₁ β₁) := by unfold coeff; fun_prop

theorem measurable_innov : Measurable (innov α₀ α₁ β₁) := by
  unfold innov; exact (measurable_coeff α₁ β₁).prodMk measurable_const

/-- **The GARCH(1,1) squared volatility recursion** `σ²_{t+1} = α₀ + (α₁ Z_t² + β₁) σ²_t` is the
stochastic recurrence `X_{t+1} = A_t X_t + B_t` with `(A_t, B_t) = (α₁ Z_t² + β₁, α₀)`. -/
theorem affine_innov (x z : ℝ) :
    affine x (innov α₀ α₁ β₁ z) = α₀ + (α₁ * z ^ 2 + β₁) * x := by
  simp only [affine, innov, coeff]; ring

variable {α₀ α₁ β₁}

theorem coeff_nonneg (hα₁ : 0 ≤ α₁) (hβ₁ : 0 ≤ β₁) (z : ℝ) : 0 ≤ coeff α₁ β₁ z := by
  unfold coeff; positivity

variable {ζ : Measure ℝ} [IsProbabilityMeasure ζ]

instance : IsProbabilityMeasure (coeffLaw α₀ α₁ β₁ ζ) := by
  unfold coeffLaw; infer_instance

/-! ### Transfer of the hypotheses from `Z` to `(A, B)` -/

section Transfer

omit [IsProbabilityMeasure ζ] in
theorem integrable_log_coeffLaw (hlog : Integrable (fun z => log (coeff α₁ β₁ z)) ζ) :
    Integrable (fun p : ℝ × ℝ => log |p.1|) (coeffLaw α₀ α₁ β₁ ζ) := by
  rw [coeffLaw, integrable_map_measure
    (by fun_prop : Measurable fun p : ℝ × ℝ => log |p.1|).aestronglyMeasurable
    (measurable_innov α₀ α₁ β₁).aemeasurable]
  refine hlog.congr (ae_of_all _ fun z => ?_)
  simp [innov]

omit [IsProbabilityMeasure ζ] in
theorem integral_log_coeffLaw :
    ∫ p, log |p.1| ∂(coeffLaw α₀ α₁ β₁ ζ) = ∫ z, log (coeff α₁ β₁ z) ∂ζ := by
  rw [coeffLaw, integral_map (measurable_innov α₀ α₁ β₁).aemeasurable
    (by fun_prop : Measurable fun p : ℝ × ℝ => log |p.1|).aestronglyMeasurable]
  simp [innov]

omit [IsProbabilityMeasure ζ] in
theorem lintegral_rpow_coeffLaw (hα₁ : 0 ≤ α₁) (hβ₁ : 0 ≤ β₁) {κ : ℝ} (hκ : 0 ≤ κ)
    (hi : Integrable (fun z => coeff α₁ β₁ z ^ κ) ζ) :
    ∫⁻ p, ‖p.1‖ₑ ^ κ ∂(coeffLaw α₀ α₁ β₁ ζ) = ENNReal.ofReal (∫ z, coeff α₁ β₁ z ^ κ ∂ζ) := by
  rw [coeffLaw, lintegral_map (by fun_prop) (measurable_innov α₀ α₁ β₁),
    ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun z => rpow_nonneg (coeff_nonneg hα₁ hβ₁ z) _)]
  refine lintegral_congr fun z => ?_
  rw [enorm_rpow_eq_ofReal _ hκ]
  simp [innov, abs_of_nonneg (coeff_nonneg hα₁ hβ₁ z)]

end Transfer

omit [IsProbabilityMeasure ζ] in
theorem ae_coeffLaw_iff {P : ℝ × ℝ → Prop} (hP : MeasurableSet {p | P p}) :
    (∀ᵐ p ∂(coeffLaw α₀ α₁ β₁ ζ), P p) ↔ ∀ᵐ z ∂ζ, P (innov α₀ α₁ β₁ z) :=
  ae_map_iff (measurable_innov α₀ α₁ β₁).aemeasurable hP


theorem integrable_posLog_coeffLaw :
    Integrable (fun p : ℝ × ℝ => posLog p.2) (coeffLaw α₀ α₁ β₁ ζ) := by
  rw [coeffLaw, integrable_map_measure (g := fun p : ℝ × ℝ => posLog p.2)
    (continuous_posLog.measurable.comp measurable_snd).aestronglyMeasurable
    (measurable_innov α₀ α₁ β₁).aemeasurable]
  exact integrable_const (posLog α₀)

end GARCH

end SRE

end ExtremeValueTheory
