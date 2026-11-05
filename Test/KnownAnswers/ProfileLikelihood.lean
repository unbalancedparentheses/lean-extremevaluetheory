import ExtremeValueTheory

/-!
# Known answers: the chi-squared laws and the profile likelihood objects

Checks of `chiSquared` against textbook values, and of the objects of
`ExtremeValueTheory.Statistics.GPDWilks` against direct computations.

Reference: [Coles] S. Coles, *An Introduction to Statistical Modeling of Extreme Values* (2001).
-/

open Real MeasureTheory ProbabilityTheory ExtremeValueTheory Set

namespace Test.KnownAnswers.ProfileLikelihood

/-- `χ²₁` lives on `[0, ∞)`: a statistic cannot be covered at a negative critical value. Fails if
`chiSquared` were not the law of a square. -/
theorem test_chiSquared_one_neg {c : ℝ} (hc : c < 0) : chiSquared 1 (Iic c) = 0 := by
  rw [chiSquared_one_eq_map, Measure.map_apply (by fun_prop) measurableSet_Iic]
  convert measure_empty (μ := gaussianReal 0 1)
  ext x
  simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
  nlinarith [sq_nonneg x]

/-- `χ²₁((-∞, z²]) = N(0, 1)([-z, z])` ([Coles, §2.6.6]: the `χ²₁` quantile is the square of the
two-sided normal quantile, so `3.84 ≈ 1.96²`). -/
theorem test_chiSquared_one_sq {z : ℝ} (hz : 0 ≤ z) :
    chiSquared 1 (Iic (z ^ 2)) = gaussianReal 0 1 (Icc (-z) z) := by
  rw [chiSquared_one_Iic (by positivity), Real.sqrt_sq hz]

/-- `χ²₂` is the exponential law with mean `2`: at `c = 2`, `1 - e⁻¹`. -/
theorem test_chiSquared_two_two : (chiSquared 2).real (Iic 2) = 1 - exp (-1) := by
  rw [chiSquared_two_real_Iic (by norm_num)]
  norm_num

/-- The return level curve of `isGPDProfileChart_returnLevel` has tangent orthogonal to the gradient
of the return level at the true parameter: `∇x_N · t = 0`, so it does parametrize the level set to
first order. Fails if the derivative of the curve had the wrong sign or power. -/
theorem test_returnLevel_tangent {ξ σ y : ℝ} (hb : boxCox ξ y ≠ 0) :
    (σ * boxCoxShapeDeriv ξ y) * 1 +
      boxCox ξ y * (-(σ * boxCox ξ y) * boxCoxShapeDeriv ξ y / boxCox ξ y ^ 2) = 0 := by
  field_simp
  ring

/-- `Sᵀ I⁻¹ S` at `ξ = 0`, `σ = 1`, the exponential case: `I⁻¹ = [[1, -1], [-1, 2]]`. -/
theorem test_gpdInfoInvQuad_exponential (s₁ s₂ : ℝ) :
    gpdInfoInvQuad 0 1 s₁ s₂ = s₁ ^ 2 - 2 * s₁ * s₂ + 2 * s₂ ^ 2 := by
  simp [gpdInfoInvQuad]

/-- `gpdInfoInvQuad` is the quadratic form of `gpdFisherInfoInv`. -/
theorem test_gpdInfoInvQuad_eq_dotProduct (ξ σ s₁ s₂ : ℝ) :
    gpdInfoInvQuad ξ σ s₁ s₂ =
      ![s₁, s₂] ⬝ᵥ Matrix.mulVec (gpdFisherInfoInv ξ σ) ![s₁, s₂] := by
  simp [gpdInfoInvQuad, gpdFisherInfoInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The maximized log-likelihood over the singleton `{θ}` is the log-likelihood at `θ`: so that the
deviance at the MLE of a one-point model is zero. -/
theorem test_gpdMaxLogLik_singleton {n : ℕ} (x : Fin n → ℝ) (θ : ℝ × ℝ) :
    gpdMaxLogLik {θ} x = gpdLogLikE θ.1 θ.2 x := by
  simp [gpdMaxLogLik]

/-- The profile log-likelihood at an unattained value is `-∞`: a value of the interest parameter
outside the image of `K` has profile likelihood `-∞`. -/
theorem test_gpdProfileLogLik_empty {K : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℝ} {ψ : ℝ}
    (h : ∀ p ∈ K, g p ≠ ψ) {n : ℕ} (x : Fin n → ℝ) : gpdProfileLogLik K g ψ x = ⊥ := by
  have : K ∩ g ⁻¹' {ψ} = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
      not_and]
    exact h p
  simp [gpdProfileLogLik, gpdMaxLogLik, this]

end Test.KnownAnswers.ProfileLikelihood
