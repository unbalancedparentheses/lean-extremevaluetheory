/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDScaleMLE

/-!
# The Fisher information of the generalized Pareto family and the joint score CLT

For a shape `ξ ≠ 0` and a point `x ≥ 0` of the support (`σ + ξ x > 0`), the GPD log-density is
`ℓ(ξ, σ; x) = -log σ - (1/ξ + 1) log(1 + ξ x / σ)`. With `w = x / (σ + ξ x)`, its score and
Hessian are

* `∂_ξ ℓ = log(1 + ξ x/σ) / ξ² - (1/ξ + 1) w` (`gpdScoreXi`),
* `∂_σ ℓ = ((1 + ξ) w - 1) / σ` (`gpdScoreSigma`),
* `∂²_ξ ℓ = -2 log(1 + ξ x/σ)/ξ³ + 2 w/ξ² + (1/ξ + 1) w²` (`gpdHessXiXi`),
* `∂_σ ∂_ξ ℓ = ∂_ξ ∂_σ ℓ = (w - (1 + ξ) w²) / σ` (`gpdHessXiSigma`),
* `∂²_σ ℓ = (1 - 2 (1 + ξ) w + ξ (1 + ξ) w²) / σ²` (`gpdHessSigmaSigma`).

For `ξ > -1/2` all of these are integrable under `GPD(ξ, σ)` (the score is square integrable),
the score has mean zero, and the **Fisher information** ([Smith 1985]; [Coles, §4.3.3])

  `I(ξ, σ) = 1/((1 + ξ)(1 + 2ξ)) · [[2, 1/σ], [1/σ, (1 + ξ)/σ²]]` (`gpdFisherInfo`)

is both the covariance of the score and minus the expected Hessian (the information identity).
Its inverse, the asymptotic covariance of the joint MLE, is

  `I(ξ, σ)⁻¹ = (1 + ξ) · [[1 + ξ, -σ], [-σ, 2σ²]]` (`gpdFisherInfoInv`).

## Main results

* `hasDerivAt_log_gpdDensity_xi`, `hasDerivAt_log_gpdDensity_sigma`: the score is the gradient
  of the log-density; `hasDerivAt_gpdScoreXi_xi`, `hasDerivAt_gpdScoreXi_sigma`,
  `hasDerivAt_gpdScoreSigma_xi`, `hasDerivAt_gpdScoreSigma_sigma`: the Hessian.
* `integral_gpdScoreXi`, `integral_gpdScoreSigma`: the score has mean zero.
* `integral_gpdScoreXi_sq`, `integral_gpdScoreXi_mul_gpdScoreSigma`, `integral_gpdScoreSigma_sq`:
  the covariance of the score is `I(ξ, σ)`.
* `integral_gpdHessXiXi`, `integral_gpdHessXiSigma`, `integral_gpdHessSigmaSigma`: the expected
  Hessian is `-I(ξ, σ)`.
* `gpdFisherInfo_mul_inv`, `inv_gpdFisherInfo`, `posDef_gpdFisherInfo`,
  `posDef_gpdFisherInfoInv`: the information matrix, its inverse and their positivity.
* `tendstoInDistribution_gpdScoreVec`: **the bivariate score CLT**
  `n^{-1/2} ∑_{i<n} ∇ℓ(ξ₀, σ₀; Xᵢ) ⇒ N(0, I(ξ₀, σ₀))` in `ℝ²`, by the Cramér–Wold device and the
  one-dimensional central limit theorem.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §4.3.3.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### The score and the Hessian of the log-density -/

section Derivatives

variable {ξ σ x : ℝ}

/-- The shape score `∂_ξ log g_{ξ,σ}(x) = log(1 + ξ x/σ)/ξ² - (1/ξ + 1) x/(σ + ξ x)`. -/
noncomputable def gpdScoreXi (ξ σ x : ℝ) : ℝ :=
  log (1 + ξ * x / σ) / ξ ^ 2 - (1 / ξ + 1) * (x / (σ + ξ * x))

/-- The scale score `∂_σ log g_{ξ,σ}(x) = ((1 + ξ) x/(σ + ξ x) - 1)/σ`. -/
noncomputable def gpdScoreSigma (ξ σ x : ℝ) : ℝ := ((1 + ξ) * (x / (σ + ξ * x)) - 1) / σ

/-- `∂²_ξ log g_{ξ,σ}(x)`. -/
noncomputable def gpdHessXiXi (ξ σ x : ℝ) : ℝ :=
  -2 * log (1 + ξ * x / σ) / ξ ^ 3 + 2 * (x / (σ + ξ * x)) / ξ ^ 2 +
    (1 / ξ + 1) * (x / (σ + ξ * x)) ^ 2

/-- `∂_σ ∂_ξ log g_{ξ,σ}(x) = ∂_ξ ∂_σ log g_{ξ,σ}(x)`. -/
noncomputable def gpdHessXiSigma (ξ σ x : ℝ) : ℝ :=
  (x / (σ + ξ * x) - (1 + ξ) * (x / (σ + ξ * x)) ^ 2) / σ

/-- `∂²_σ log g_{ξ,σ}(x)`. -/
noncomputable def gpdHessSigmaSigma (ξ σ x : ℝ) : ℝ :=
  (1 - 2 * (1 + ξ) * (x / (σ + ξ * x)) + ξ * (1 + ξ) * (x / (σ + ξ * x)) ^ 2) / σ ^ 2

lemma measurable_gpdScoreXi (ξ σ : ℝ) : Measurable (gpdScoreXi ξ σ) := by
  unfold gpdScoreXi; fun_prop

lemma measurable_gpdScoreSigma (ξ σ : ℝ) : Measurable (gpdScoreSigma ξ σ) := by
  unfold gpdScoreSigma; fun_prop

lemma measurable_gpdHessXiXi (ξ σ : ℝ) : Measurable (gpdHessXiXi ξ σ) := by
  unfold gpdHessXiXi; fun_prop

lemma measurable_gpdHessXiSigma (ξ σ : ℝ) : Measurable (gpdHessXiSigma ξ σ) := by
  unfold gpdHessXiSigma; fun_prop

lemma measurable_gpdHessSigmaSigma (ξ σ : ℝ) : Measurable (gpdHessSigmaSigma ξ σ) := by
  unfold gpdHessSigmaSigma; fun_prop

lemma one_add_mul_div_pos (hσ : 0 < σ) (hu : 0 < σ + ξ * x) : 0 < 1 + ξ * x / σ := by
  have : 1 + ξ * x / σ = (σ + ξ * x) / σ := by field_simp
  rw [this]; exact div_pos hu hσ

/-- **The shape score is the `ξ`-derivative of the log-density.** -/
theorem hasDerivAt_log_gpdDensity_xi (hσ : 0 < σ) (hξ : ξ ≠ 0) (hx : 0 ≤ x)
    (hu : 0 < σ + ξ * x) :
    HasDerivAt (fun ξ' => log (gpdDensity ξ' σ x)) (gpdScoreXi ξ σ x) ξ := by
  have hu' := one_add_mul_div_pos hσ hu
  have hev : (fun ξ' => log (gpdDensity ξ' σ x)) =ᶠ[𝓝 ξ]
      fun ξ' => -log σ - (1 / ξ' + 1) * log (1 + ξ' * x / σ) := by
    have h1 : ∀ᶠ ξ' in 𝓝 ξ, ξ' ≠ 0 := isOpen_ne.mem_nhds hξ
    have h2 : ∀ᶠ ξ' in 𝓝 ξ, 0 < 1 + ξ' * x / σ :=
      (show Continuous fun ξ' : ℝ => 1 + ξ' * x / σ by fun_prop).continuousAt.eventually
        (lt_mem_nhds hu')
    filter_upwards [h1, h2] with ξ' h1 h2
    exact log_gpdDensity hσ h1 hx h2
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hL : HasDerivAt (fun ξ' => log (1 + ξ' * x / σ)) ((1 * x / σ) / (1 + ξ * x / σ)) ξ :=
    ((((hasDerivAt_id ξ).mul_const x).div_const σ).const_add 1).log hu'.ne'
  have hI : HasDerivAt (fun ξ' => 1 / ξ' + 1) (-(1 / ξ ^ 2)) ξ := by
    have := (hasDerivAt_inv hξ).add_const 1
    simpa [one_div] using this
  have := (hI.mul hL).const_sub (-log σ)
  convert this using 1
  unfold gpdScoreXi
  field_simp
  ring

/-- **The scale score is the `σ`-derivative of the log-density.** -/
theorem hasDerivAt_log_gpdDensity_sigma (hσ : 0 < σ) (hξ : ξ ≠ 0) (hx : 0 ≤ x)
    (hu : 0 < σ + ξ * x) :
    HasDerivAt (fun σ' => log (gpdDensity ξ σ' x)) (gpdScoreSigma ξ σ x) σ := by
  have hu' := one_add_mul_div_pos hσ hu
  have hev : (fun σ' => log (gpdDensity ξ σ' x)) =ᶠ[𝓝 σ]
      fun σ' => -log σ' - (1 / ξ + 1) * log (1 + ξ * x / σ') := by
    have h1 : ∀ᶠ σ' in 𝓝 σ, 0 < σ' := lt_mem_nhds hσ
    have h2 : ∀ᶠ σ' in 𝓝 σ, 0 < σ' + ξ * x :=
      (show Continuous fun σ' : ℝ => σ' + ξ * x by fun_prop).continuousAt.eventually
        (lt_mem_nhds hu)
    filter_upwards [h1, h2] with σ' h1 h2
    exact log_gpdDensity h1 hξ hx (one_add_mul_div_pos h1 h2)
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hL : HasDerivAt (fun σ' => log (1 + ξ * x / σ'))
      ((-(ξ * x) / σ ^ 2) / (1 + ξ * x / σ)) σ := by
    have h := ((hasDerivAt_inv hσ.ne').const_mul (ξ * x)).const_add 1
    have h' : HasDerivAt (fun σ' => 1 + ξ * x / σ') (-(ξ * x) / σ ^ 2) σ := by
      convert h using 1
      · funext σ'; simp [div_eq_mul_inv]
      · ring
    exact h'.log hu'.ne'
  have := ((hasDerivAt_log hσ.ne').neg).sub (hL.const_mul (1 / ξ + 1))
  convert this using 1
  unfold gpdScoreSigma
  field_simp
  ring

/-- `∂_ξ` of the shape score. -/
theorem hasDerivAt_gpdScoreXi_xi (hσ : 0 < σ) (hξ : ξ ≠ 0) (hu : 0 < σ + ξ * x) :
    HasDerivAt (fun ξ' => gpdScoreXi ξ' σ x) (gpdHessXiXi ξ σ x) ξ := by
  have hu' := one_add_mul_div_pos hσ hu
  have hL : HasDerivAt (fun ξ' => log (1 + ξ' * x / σ)) ((1 * x / σ) / (1 + ξ * x / σ)) ξ :=
    ((((hasDerivAt_id ξ).mul_const x).div_const σ).const_add 1).log hu'.ne'
  have hS : HasDerivAt (fun ξ' => ξ' ^ 2) (2 * ξ) ξ := by
    simpa using hasDerivAt_pow 2 ξ
  have hW : HasDerivAt (fun ξ' => x / (σ + ξ' * x)) (-(x * x) / (σ + ξ * x) ^ 2) ξ := by
    have h := ((hasDerivAt_id ξ).mul_const x).const_add σ
    have h' := (hasDerivAt_const ξ x).div h (by simpa using hu.ne')
    exact h'.congr_deriv (by simp only [id]; ring)
  have hI : HasDerivAt (fun ξ' => 1 / ξ' + 1) (-(1 / ξ ^ 2)) ξ := by
    have := (hasDerivAt_inv hξ).add_const 1
    simpa [one_div] using this
  have := (hL.div hS (pow_ne_zero 2 hξ)).sub (hI.mul hW)
  unfold gpdScoreXi gpdHessXiXi
  convert this using 1
  field_simp
  ring

/-- `∂_σ` of the shape score. -/
theorem hasDerivAt_gpdScoreXi_sigma (hσ : 0 < σ) (hξ : ξ ≠ 0) (hu : 0 < σ + ξ * x) :
    HasDerivAt (fun σ' => gpdScoreXi ξ σ' x) (gpdHessXiSigma ξ σ x) σ := by
  have hu' := one_add_mul_div_pos hσ hu
  have hL : HasDerivAt (fun σ' => log (1 + ξ * x / σ'))
      ((-(ξ * x) / σ ^ 2) / (1 + ξ * x / σ)) σ := by
    have h := ((hasDerivAt_inv hσ.ne').const_mul (ξ * x)).const_add 1
    have h' : HasDerivAt (fun σ' => 1 + ξ * x / σ') (-(ξ * x) / σ ^ 2) σ := by
      convert h using 1
      · funext σ'; simp [div_eq_mul_inv]
      · ring
    exact h'.log hu'.ne'
  have hW : HasDerivAt (fun σ' => x / (σ' + ξ * x)) (-x / (σ + ξ * x) ^ 2) σ := by
    have h := (hasDerivAt_id σ).add_const (ξ * x)
    have h' := (hasDerivAt_const σ x).div h (by simpa using hu.ne')
    exact h'.congr_deriv (by simp only [id]; ring)
  have := (hL.div_const (ξ ^ 2)).sub (hW.const_mul (1 / ξ + 1))
  unfold gpdScoreXi gpdHessXiSigma
  convert this using 1
  field_simp
  ring

/-- `∂_ξ` of the scale score (the Hessian is symmetric). -/
theorem hasDerivAt_gpdScoreSigma_xi (hσ : 0 < σ) (hu : 0 < σ + ξ * x) :
    HasDerivAt (fun ξ' => gpdScoreSigma ξ' σ x) (gpdHessXiSigma ξ σ x) ξ := by
  have hW : HasDerivAt (fun ξ' => x / (σ + ξ' * x)) (-(x * x) / (σ + ξ * x) ^ 2) ξ := by
    have h := ((hasDerivAt_id ξ).mul_const x).const_add σ
    have h' := (hasDerivAt_const ξ x).div h (by simpa using hu.ne')
    exact h'.congr_deriv (by simp only [id]; ring)
  have := ((((hasDerivAt_id ξ).const_add 1).mul hW).sub_const 1).div_const σ
  unfold gpdScoreSigma gpdHessXiSigma
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `∂_σ` of the scale score. -/
theorem hasDerivAt_gpdScoreSigma_sigma (hσ : 0 < σ) (hu : 0 < σ + ξ * x) :
    HasDerivAt (fun σ' => gpdScoreSigma ξ σ' x) (gpdHessSigmaSigma ξ σ x) σ := by
  have hW : HasDerivAt (fun σ' => x / (σ' + ξ * x)) (-x / (σ + ξ * x) ^ 2) σ := by
    have h := (hasDerivAt_id σ).add_const (ξ * x)
    have h' := (hasDerivAt_const σ x).div h (by simpa using hu.ne')
    exact h'.congr_deriv (by simp only [id]; ring)
  have := ((hW.const_mul (1 + ξ)).sub_const 1).div (hasDerivAt_id σ) hσ.ne'
  unfold gpdScoreSigma gpdHessSigmaSigma
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

end Derivatives

end ExtremeValueTheory
