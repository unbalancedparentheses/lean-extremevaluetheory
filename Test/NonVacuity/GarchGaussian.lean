import ExtremeValueTheory

/-!
# Non-vacuity: GARCH(1,1) with Gaussian innovations

The test in `Test/NonVacuity/Dependence.lean` uses a two-point innovation law and ARCH(1). Here the
innovations are standard Gaussian, with `α₀ = 1`, `α₁ = 7/10`, `β₁ = 1/5`, so that
`A = (7/10) Z² + 1/5`:

* `A ≥ 1/5`, so `log A` is integrable and `A ≠ 0`;
* `E log A ≤ E A - 1 = -1/10 < 0` (stationarity);
* `E A² = (49/100) · 3 + (7/25) · 1 + 1/25 = 179/100 > 1`, so that `S = 2` works.

This is one parameter pair. Nothing here derives the hypotheses for general `α₁, β₁`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace ExtremeValueTheory.Test.NonVacuity.GarchGaussian

/-- Test-specific: the multiplier `A = (7/10) z² + 1/5`. -/
private noncomputable abbrev A (z : ℝ) : ℝ := SRE.GARCH.coeff (7 / 10) (1 / 5) z

/-- Test-specific: the standard Gaussian law of the innovations. -/
private noncomputable abbrev γ₁ : Measure ℝ := gaussianReal 0 1

/-- Test-specific: `A ≥ 1/5`. -/
private theorem one_fifth_le_A (z : ℝ) : 1 / 5 ≤ A z := by
  simp only [A, SRE.GARCH.coeff]
  nlinarith [sq_nonneg z]

/-- Test-specific: `A` is integrable. -/
private theorem integrable_A : Integrable A γ₁ :=
  (integrable_sq_gaussianReal.const_mul (7 / 10)).add (integrable_const (1 / 5))

/-- Test-specific: `E A = 9/10`. -/
private theorem integral_A : ∫ z, A z ∂γ₁ = 9 / 10 := by
  simp only [A, SRE.GARCH.coeff]
  rw [integral_add (integrable_sq_gaussianReal.const_mul _) (integrable_const _),
    integral_const_mul, integral_sq_gaussianReal]
  simp
  norm_num

/-- Test-specific: `log A` is integrable, by `log (1/5) ≤ log A ≤ A - 1`. -/
private theorem hlog : Integrable (fun z => Real.log (A z)) γ₁ := by
  have hm : Measurable fun z => Real.log (A z) :=
    Real.measurable_log.comp (SRE.GARCH.measurable_coeff _ _)
  refine Integrable.mono' (integrable_A.add (integrable_const (Real.log 5 + 1)))
    hm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have h15 := one_fifth_le_A z
  have hpos : 0 < A z := by linarith
  have hup : Real.log (A z) ≤ A z - 1 := Real.log_le_sub_one_of_pos hpos
  have hlow : Real.log (1 / 5) ≤ Real.log (A z) := Real.log_le_log (by norm_num) h15
  have h5 : Real.log (1 / 5) = -Real.log 5 := by rw [one_div, Real.log_inv]
  have h50 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.add_apply]
  constructor <;> linarith

/-- Test-specific: `E log A ≤ E A - 1 = -1/10 < 0`. -/
private theorem hneg : ∫ z, Real.log (A z) ∂γ₁ < 0 := by
  have hle : ∫ z, Real.log (A z) ∂γ₁ ≤ ∫ z, (A z - 1) ∂γ₁ :=
    integral_mono hlog (integrable_A.sub (integrable_const _)) fun z =>
      Real.log_le_sub_one_of_pos (by linarith [one_fifth_le_A z])
  rw [integral_sub integrable_A (integrable_const _), integral_A] at hle
  simp at hle
  linarith

/-- Test-specific: the square of the multiplier, expanded. -/
private theorem A_rpow_two (z : ℝ) :
    A z ^ (2 : ℝ) = 49 / 100 * z ^ 4 + (7 / 25 * z ^ 2 + 1 / 25) := by
  rw [Real.rpow_two]
  simp only [A, SRE.GARCH.coeff]
  ring

/-- Test-specific: `A²` is integrable. -/
private theorem hSi : Integrable (fun z => A z ^ (2 : ℝ)) γ₁ := by
  simp only [A_rpow_two]
  exact (integrable_pow_four_gaussianReal.const_mul _).add
    ((integrable_sq_gaussianReal.const_mul _).add (integrable_const _))

/-- Known answer used by the test: `E A² = (49/100) · 3 + 7/25 + 1/25 = 179/100`, from
`E Z² = 1` and `E Z⁴ = 3`. -/
theorem test_integral_A_sq : ∫ z, A z ^ (2 : ℝ) ∂γ₁ = 179 / 100 := by
  simp only [A_rpow_two]
  have h2 : Integrable (fun z : ℝ => 7 / 25 * z ^ 2) γ₁ := integrable_sq_gaussianReal.const_mul _
  have h4 : Integrable (fun z : ℝ => 49 / 100 * z ^ 4) γ₁ :=
    integrable_pow_four_gaussianReal.const_mul _
  have h21 : Integrable (fun z : ℝ => 7 / 25 * z ^ 2 + 1 / 25) γ₁ := h2.add (integrable_const _)
  rw [integral_add h4 h21, integral_add h2 (integrable_const _),
    integral_const_mul, integral_const_mul, integral_pow_four_gaussianReal,
    integral_sq_gaussianReal]
  simp
  norm_num

/-- Test-specific: `A` is not almost surely `1`, since `E A = 9/10`. -/
private theorem hnd : ¬ ∀ᵐ z ∂γ₁, A z = 1 := by
  intro h
  have := integral_congr_ae h
  rw [integral_A] at this
  simp at this
  norm_num at this

/-- **Non-vacuity of `SRE.GARCH.isStationary`, `SRE.GARCH.exists_tail_index` and
`SRE.GARCH.tail_bounds` for Gaussian innovations**: `α₀ = 1`, `α₁ = 7/10`, `β₁ = 1/5`, `Z ∼ N(0, 1)`,
`S = 2`. The squared-volatility chain is stationary, there is `κ ∈ (0, 2)` with `E A^κ = 1`, and
the tail of the stationary law is `O(x^{-s})` for `s < κ`, and not for `s > κ`. All hypotheses
discharged. -/
theorem test_nonvacuous_garch_gaussian :
    IsStationary (RandomIteration.chain SRE.affine Prod.fst fun n (p : ℝ × (ℕ → ℝ × ℝ)) => p.2 n)
      (RandomIteration.canonicalMeasure
        (SRE.stationaryLaw (SRE.GARCH.coeffLaw 1 (7 / 10) (1 / 5) γ₁))
        (SRE.GARCH.coeffLaw 1 (7 / 10) (1 / 5) γ₁)) ∧
    ∃ κ ∈ Ioo (0 : ℝ) 2, ∫ z, A z ^ κ ∂γ₁ = 1 ∧
      (∀ s, 0 < s → s < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
        SRE.stationaryLaw (SRE.GARCH.coeffLaw 1 (7 / 10) (1 / 5) γ₁) {y | x < |y|} ≤
          ENNReal.ofReal (C * x ^ (-s))) ∧
      (∀ s, κ < s → ¬ ∃ C x₀ : ℝ, 0 ≤ C ∧ 0 < x₀ ∧ ∀ x, x₀ ≤ x →
        SRE.stationaryLaw (SRE.GARCH.coeffLaw 1 (7 / 10) (1 / 5) γ₁) {y | x < |y|} ≤
          ENNReal.ofReal (C * x ^ (-s))) := by
  have h7 : (0 : ℝ) ≤ 7 / 10 := by norm_num
  have h1 : (0 : ℝ) ≤ 1 / 5 := by norm_num
  have hA0 : ∀ᵐ z ∂γ₁, SRE.GARCH.coeff (7 / 10) (1 / 5) z ≠ 0 :=
    ae_of_all _ fun z => (lt_of_lt_of_le (by norm_num) (one_fifth_le_A z)).ne'
  have hS1 : 1 < ∫ z, A z ^ (2 : ℝ) ∂γ₁ := by rw [test_integral_A_sq]; norm_num
  obtain ⟨κ, hκ, hκi, hκ1⟩ := SRE.GARCH.exists_tail_index h7 h1 hlog hneg hA0 two_pos hSi hS1
  exact ⟨SRE.GARCH.isStationary hlog hneg, κ, hκ, hκ1,
    SRE.GARCH.tail_bounds h7 h1 hlog hneg one_pos hκ.1 hκi hκ1 hnd⟩

end ExtremeValueTheory.Test.NonVacuity.GarchGaussian
