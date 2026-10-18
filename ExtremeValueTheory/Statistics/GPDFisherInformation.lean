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

/-! ### Moments on the exponential scale -/

section ExpMoments

variable {ξ : ℝ}

lemma exp_neg_mul_sq (ξ t : ℝ) : exp (-(ξ * t)) ^ 2 = exp ((-2 * ξ) * t) := by
  rw [sq, ← exp_add]; congr 1; ring

lemma integrable_mul_exp_neg_expMeasure (hξ : -1 < ξ) :
    Integrable (fun t => t * exp (-(ξ * t))) (expMeasure 1) := by
  rw [integrable_expMeasure_iff]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1 + ξ) (by norm_num)
    one_pos (by linarith)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [rpow_one]
  have : exp (-(1 + ξ) * t) = exp (-t) * exp (-(ξ * t)) := by rw [← exp_add]; ring_nf
  rw [this]; ring

lemma integral_mul_exp_neg_expMeasure (hξ : -1 < ξ) :
    ∫ t, t * exp (-(ξ * t)) ∂expMeasure 1 = 1 / (1 + ξ) ^ 2 := by
  have h1ξ : 0 < 1 + ξ := by linarith
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 + ξ) two_pos h1ξ
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.Gamma_two, mul_one, rpow_two, div_pow,
    one_pow] at h
  rw [integral_expMeasure, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [rpow_one]
  have : exp (-((1 + ξ) * t)) = exp (-t) * exp (-(ξ * t)) := by rw [← exp_add]; ring_nf
  rw [this]; ring

lemma integrable_poly_exp_expMeasure (hξ : -1 / 2 < ξ) (a b c d f g : ℝ) :
    Integrable (fun t => a + b * t + c * t ^ 2 + d * exp (-(ξ * t)) + f * exp (-(ξ * t)) ^ 2 +
      g * (t * exp (-(ξ * t)))) (expMeasure 1) := by
  have i2 : Integrable (fun t : ℝ => b * t) (expMeasure 1) :=
    ((integrable_pow_expMeasure 1).congr (ae_of_all _ fun t => by simp)).const_mul b
  have i3 : Integrable (fun t : ℝ => c * t ^ 2) (expMeasure 1) :=
    (integrable_pow_expMeasure 2).const_mul c
  have i4 : Integrable (fun t : ℝ => d * exp (-(ξ * t))) (expMeasure 1) :=
    ((integrable_exp_mul_expMeasure (a := -ξ) (by linarith)).congr
      (ae_of_all _ fun t => by simp only [neg_mul])).const_mul d
  have i5 : Integrable (fun t : ℝ => f * exp (-(ξ * t)) ^ 2) (expMeasure 1) :=
    ((integrable_exp_mul_expMeasure (a := -2 * ξ) (by linarith)).congr
      (ae_of_all _ fun t => (exp_neg_mul_sq ξ t).symm)).const_mul f
  have i6 : Integrable (fun t : ℝ => g * (t * exp (-(ξ * t)))) (expMeasure 1) :=
    (integrable_mul_exp_neg_expMeasure (by linarith)).const_mul g
  exact (((((integrable_const a).add i2).add i3).add i4).add i5).add i6

/-- The integral of `a + b t + c t² + d e^{-ξ t} + f e^{-2ξ t} + g t e^{-ξ t}` against the
standard exponential law. -/
theorem integral_poly_exp_expMeasure (hξ : -1 / 2 < ξ) (a b c d f g : ℝ) :
    ∫ t, (a + b * t + c * t ^ 2 + d * exp (-(ξ * t)) + f * exp (-(ξ * t)) ^ 2 +
      g * (t * exp (-(ξ * t)))) ∂expMeasure 1 =
      a + b + 2 * c + d / (1 + ξ) + f / (1 + 2 * ξ) + g / (1 + ξ) ^ 2 := by
  have h1 : Integrable (fun t : ℝ => t) (expMeasure 1) :=
    (integrable_pow_expMeasure 1).congr (ae_of_all _ fun t => by simp)
  have h2 : Integrable (fun t : ℝ => t ^ 2) (expMeasure 1) := integrable_pow_expMeasure 2
  have h3 : Integrable (fun t : ℝ => exp (-(ξ * t))) (expMeasure 1) :=
    (integrable_exp_mul_expMeasure (a := -ξ) (by linarith)).congr
      (ae_of_all _ fun t => by simp only [neg_mul])
  have h4 : Integrable (fun t : ℝ => exp (-(ξ * t)) ^ 2) (expMeasure 1) :=
    (integrable_exp_mul_expMeasure (a := -2 * ξ) (by linarith)).congr
      (ae_of_all _ fun t => (exp_neg_mul_sq ξ t).symm)
  have h5 : Integrable (fun t : ℝ => t * exp (-(ξ * t))) (expMeasure 1) :=
    integrable_mul_exp_neg_expMeasure (by linarith)
  have v1 : ∫ t, t ∂expMeasure 1 = 1 := integral_id_expMeasure
  have v2 : ∫ t, t ^ 2 ∂expMeasure 1 = 2 := by simpa using integral_pow_expMeasure 2
  have v3 : ∫ t, exp (-(ξ * t)) ∂expMeasure 1 = 1 / (1 + ξ) := by
    have := integral_exp_mul_expMeasure (a := -ξ) (by linarith)
    simp only [neg_mul, sub_neg_eq_add] at this
    exact this
  have v4 : ∫ t, exp (-(ξ * t)) ^ 2 ∂expMeasure 1 = 1 / (1 + 2 * ξ) := by
    have := integral_exp_mul_expMeasure (a := -2 * ξ) (by linarith)
    simp only [← exp_neg_mul_sq] at this
    rw [this]; ring_nf
  have v5 := integral_mul_exp_neg_expMeasure (ξ := ξ) (by linarith)
  have e1 : ∫ t, (a + b * t + c * t ^ 2 + d * exp (-(ξ * t)) + f * exp (-(ξ * t)) ^ 2 +
      g * (t * exp (-(ξ * t)))) ∂expMeasure 1 = ∫ t, (a + b * t + c * t ^ 2 +
      d * exp (-(ξ * t)) + f * exp (-(ξ * t)) ^ 2) ∂expMeasure 1 +
      ∫ t, g * (t * exp (-(ξ * t))) ∂expMeasure 1 :=
    integral_add (((((integrable_const a).add (h1.const_mul b)).add (h2.const_mul c)).add
      (h3.const_mul d)).add (h4.const_mul f)) (h5.const_mul g)
  have e2 : ∫ t, (a + b * t + c * t ^ 2 + d * exp (-(ξ * t)) + f * exp (-(ξ * t)) ^ 2)
      ∂expMeasure 1 = ∫ t, (a + b * t + c * t ^ 2 + d * exp (-(ξ * t))) ∂expMeasure 1 +
      ∫ t, f * exp (-(ξ * t)) ^ 2 ∂expMeasure 1 :=
    integral_add ((((integrable_const a).add (h1.const_mul b)).add (h2.const_mul c)).add
      (h3.const_mul d)) (h4.const_mul f)
  have e3 : ∫ t, (a + b * t + c * t ^ 2 + d * exp (-(ξ * t))) ∂expMeasure 1 =
      ∫ t, (a + b * t + c * t ^ 2) ∂expMeasure 1 + ∫ t, d * exp (-(ξ * t)) ∂expMeasure 1 :=
    integral_add (((integrable_const a).add (h1.const_mul b)).add (h2.const_mul c))
      (h3.const_mul d)
  have e4 : ∫ t, (a + b * t + c * t ^ 2) ∂expMeasure 1 =
      ∫ t, (a + b * t) ∂expMeasure 1 + ∫ t, c * t ^ 2 ∂expMeasure 1 :=
    integral_add ((integrable_const a).add (h1.const_mul b)) (h2.const_mul c)
  have e5 : ∫ t, (a + b * t) ∂expMeasure 1 = ∫ _t, a ∂expMeasure 1 + ∫ t, b * t ∂expMeasure 1 :=
    integral_add (integrable_const a) (h1.const_mul b)
  rw [e1, e2, e3, e4, e5, integral_const, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    v1, v2, v3, v4, v5, probReal_univ, one_smul]
  ring

lemma memLp_lin_exp_expMeasure (hξ : -1 / 2 < ξ) (a b d : ℝ) :
    MemLp (fun t => a + b * t + d * exp (-(ξ * t))) 2 (expMeasure 1) := by
  have he : MemLp (fun t => exp (-(ξ * t))) 2 (expMeasure 1) := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    exact (integrable_exp_mul_expMeasure (a := -2 * ξ) (by linarith)).congr
      (ae_of_all _ fun t => (exp_neg_mul_sq ξ t).symm)
  have ht : MemLp (fun t : ℝ => t) 2 (expMeasure 1) := memLp_two_id_expMeasure
  exact ((memLp_const a).add (ht.const_mul b)).add (he.const_mul d)

end ExpMoments

/-! ### Moments under the GPD -/

section GPDMoments

variable {ξ σ : ℝ}

lemma log_one_add_mul_gpdTransform (hσ : 0 < σ) (hξ : ξ ≠ 0) (t : ℝ) :
    log (1 + ξ * gpdTransform ξ σ t / σ) = ξ * t := by
  rw [one_add_mul_gpdTransform hσ hξ, log_exp]

/-- An integral against `GPD(ξ, σ)` of a function which, on the exponential scale, is a
combination of `1, t, t², e^{-ξ t}, e^{-2ξ t}, t e^{-ξ t}`. -/
lemma integral_gpdMeasure_of_poly (hξ : -1 / 2 < ξ) {h : ℝ → ℝ} (hh : Measurable h)
    (a b c d f g : ℝ) (heq : ∀ t, h (gpdTransform ξ σ t) = a + b * t + c * t ^ 2 +
      d * exp (-(ξ * t)) + f * exp (-(ξ * t)) ^ 2 + g * (t * exp (-(ξ * t)))) :
    ∫ x, h x ∂gpdMeasure ξ σ =
      a + b + 2 * c + d / (1 + ξ) + f / (1 + 2 * ξ) + g / (1 + ξ) ^ 2 := by
  rw [integral_gpdMeasure hh, ← integral_poly_exp_expMeasure hξ]
  exact integral_congr_ae (ae_of_all _ heq)

lemma integrable_gpdMeasure_of_poly (hξ : -1 / 2 < ξ) {h : ℝ → ℝ} (hh : Measurable h)
    (a b c d f g : ℝ) (heq : ∀ t, h (gpdTransform ξ σ t) = a + b * t + c * t ^ 2 +
      d * exp (-(ξ * t)) + f * exp (-(ξ * t)) ^ 2 + g * (t * exp (-(ξ * t)))) :
    Integrable h (gpdMeasure ξ σ) := by
  rw [integrable_gpdMeasure_iff hh]
  exact (integrable_poly_exp_expMeasure hξ a b c d f g).congr (ae_of_all _ fun t => (heq t).symm)

variable (hσ : 0 < σ) (hξ0 : ξ ≠ 0)
include hσ hξ0

lemma gpdScoreXi_gpdTransform (t : ℝ) :
    gpdScoreXi ξ σ (gpdTransform ξ σ t) =
      -((1 / ξ + 1) / ξ) + 1 / ξ * t + (1 / ξ + 1) / ξ * exp (-(ξ * t)) := by
  unfold gpdScoreXi
  rw [log_one_add_mul_gpdTransform hσ hξ0, gpdTransform_div hσ hξ0]
  field_simp
  ring

lemma gpdScoreSigma_gpdTransform (t : ℝ) :
    gpdScoreSigma ξ σ (gpdTransform ξ σ t) =
      ((1 + ξ) / ξ - 1) / σ + (-((1 + ξ) / ξ) / σ) * exp (-(ξ * t)) := by
  unfold gpdScoreSigma
  rw [gpdTransform_div hσ hξ0]
  field_simp
  ring

lemma gpdHessXiXi_gpdTransform (t : ℝ) :
    gpdHessXiXi ξ σ (gpdTransform ξ σ t) =
      (2 / ξ ^ 3 + (1 / ξ + 1) / ξ ^ 2) + (-2 / ξ ^ 2) * t + 0 * t ^ 2 +
        (-2 / ξ ^ 3 - 2 * ((1 / ξ + 1) / ξ ^ 2)) * exp (-(ξ * t)) +
        (1 / ξ + 1) / ξ ^ 2 * exp (-(ξ * t)) ^ 2 + 0 * (t * exp (-(ξ * t))) := by
  unfold gpdHessXiXi
  rw [log_one_add_mul_gpdTransform hσ hξ0, gpdTransform_div hσ hξ0]
  field_simp
  ring

lemma gpdHessXiSigma_gpdTransform (t : ℝ) :
    gpdHessXiSigma ξ σ (gpdTransform ξ σ t) =
      (1 / ξ - (1 + ξ) / ξ ^ 2) / σ + 0 * t + 0 * t ^ 2 +
        ((-1 / ξ + 2 * (1 + ξ) / ξ ^ 2) / σ) * exp (-(ξ * t)) +
        (-((1 + ξ) / ξ ^ 2) / σ) * exp (-(ξ * t)) ^ 2 + 0 * (t * exp (-(ξ * t))) := by
  unfold gpdHessXiSigma
  rw [gpdTransform_div hσ hξ0]
  field_simp
  ring

lemma gpdHessSigmaSigma_gpdTransform (t : ℝ) :
    gpdHessSigmaSigma ξ σ (gpdTransform ξ σ t) =
      (1 - (1 + ξ) / ξ) / σ ^ 2 + 0 * t + 0 * t ^ 2 + 0 * exp (-(ξ * t)) +
        ((1 + ξ) / ξ / σ ^ 2) * exp (-(ξ * t)) ^ 2 + 0 * (t * exp (-(ξ * t))) := by
  unfold gpdHessSigmaSigma
  rw [gpdTransform_div hσ hξ0]
  field_simp
  ring

/-- A combination `u ∂_ξ ℓ + v ∂_σ ℓ` of the scores, on the exponential scale. -/
lemma lin_score_gpdTransform (u v t : ℝ) :
    u * gpdScoreXi ξ σ (gpdTransform ξ σ t) + v * gpdScoreSigma ξ σ (gpdTransform ξ σ t) =
      (u * -((1 / ξ + 1) / ξ) + v * (((1 + ξ) / ξ - 1) / σ)) + u * (1 / ξ) * t +
        (u * ((1 / ξ + 1) / ξ) + v * (-((1 + ξ) / ξ) / σ)) * exp (-(ξ * t)) := by
  rw [gpdScoreXi_gpdTransform hσ hξ0, gpdScoreSigma_gpdTransform hσ hξ0]
  ring

variable (hξ : -1 / 2 < ξ)
include hξ

/-- **The shape score has mean zero.** -/
theorem integral_gpdScoreXi : ∫ x, gpdScoreXi ξ σ x ∂gpdMeasure ξ σ = 0 := by
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  rw [integral_gpdMeasure_of_poly hξ (measurable_gpdScoreXi ξ σ) (-((1 / ξ + 1) / ξ)) (1 / ξ) 0
    ((1 / ξ + 1) / ξ) 0 0 fun t => by rw [gpdScoreXi_gpdTransform hσ hξ0]; ring]
  field_simp
  ring

/-- **The scale score has mean zero.** -/
theorem integral_gpdScoreSigma : ∫ x, gpdScoreSigma ξ σ x ∂gpdMeasure ξ σ = 0 := by
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  rw [integral_gpdMeasure_of_poly hξ (measurable_gpdScoreSigma ξ σ) (((1 + ξ) / ξ - 1) / σ) 0 0
    (-((1 + ξ) / ξ) / σ) 0 0 fun t => by rw [gpdScoreSigma_gpdTransform hσ hξ0]; ring]
  field_simp
  ring

/-- The second moment of a combination of the scores: `E[(u ∂_ξ ℓ + v ∂_σ ℓ)²]` is the
quadratic form of the Fisher information. -/
theorem integral_lin_score_sq (u v : ℝ) :
    ∫ x, (u * gpdScoreXi ξ σ x + v * gpdScoreSigma ξ σ x) ^ 2 ∂gpdMeasure ξ σ =
      u ^ 2 * (2 / ((1 + ξ) * (1 + 2 * ξ))) + 2 * u * v * (1 / (σ * (1 + ξ) * (1 + 2 * ξ))) +
        v ^ 2 * (1 / (σ ^ 2 * (1 + 2 * ξ))) := by
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have h2ξ : 1 + 2 * ξ ≠ 0 := by intro h; linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  have hm : Measurable fun x => (u * gpdScoreXi ξ σ x + v * gpdScoreSigma ξ σ x) ^ 2 := by
    have := measurable_gpdScoreXi ξ σ; have := measurable_gpdScoreSigma ξ σ; fun_prop
  set α := u * -((1 / ξ + 1) / ξ) + v * (((1 + ξ) / ξ - 1) / σ)
  set β := u * (1 / ξ)
  set γ := u * ((1 / ξ + 1) / ξ) + v * (-((1 + ξ) / ξ) / σ)
  rw [integral_gpdMeasure_of_poly hξ hm (α ^ 2) (2 * α * β) (β ^ 2) (2 * α * γ) (γ ^ 2)
    (2 * β * γ) fun t => by rw [lin_score_gpdTransform hσ hξ0]; ring]
  simp only [α, β, γ]
  field_simp
  ring

/-- `E[(∂_ξ ℓ)²] = 2/((1 + ξ)(1 + 2ξ))`. -/
theorem integral_gpdScoreXi_sq :
    ∫ x, gpdScoreXi ξ σ x ^ 2 ∂gpdMeasure ξ σ = 2 / ((1 + ξ) * (1 + 2 * ξ)) := by
  have := integral_lin_score_sq hσ hξ0 hξ 1 0
  simp only [one_mul, zero_mul, add_zero, one_pow, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at this
  rw [this]

/-- `E[(∂_σ ℓ)²] = 1/(σ² (1 + 2ξ))`. -/
theorem integral_gpdScoreSigma_sq :
    ∫ x, gpdScoreSigma ξ σ x ^ 2 ∂gpdMeasure ξ σ = 1 / (σ ^ 2 * (1 + 2 * ξ)) := by
  have := integral_lin_score_sq hσ hξ0 hξ 0 1
  simp only [one_mul, zero_mul, zero_add, one_pow, mul_zero, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
  rw [this]

/-- `E[∂_ξ ℓ ∂_σ ℓ] = 1/(σ (1 + ξ)(1 + 2ξ))`. -/
theorem integral_gpdScoreXi_mul_gpdScoreSigma :
    ∫ x, gpdScoreXi ξ σ x * gpdScoreSigma ξ σ x ∂gpdMeasure ξ σ =
      1 / (σ * (1 + ξ) * (1 + 2 * ξ)) := by
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have h2ξ : 1 + 2 * ξ ≠ 0 := by intro h; linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  have hm : Measurable fun x => gpdScoreXi ξ σ x * gpdScoreSigma ξ σ x := by
    have := measurable_gpdScoreXi ξ σ; have := measurable_gpdScoreSigma ξ σ; fun_prop
  set A := -((1 / ξ + 1) / ξ)
  set B := 1 / ξ
  set D := (1 / ξ + 1) / ξ
  set A' := ((1 + ξ) / ξ - 1) / σ
  set D' := -((1 + ξ) / ξ) / σ
  rw [integral_gpdMeasure_of_poly hξ hm (A * A') (B * A') 0 (A * D' + D * A') (D * D') (B * D')
    fun t => by
      rw [gpdScoreXi_gpdTransform hσ hξ0, gpdScoreSigma_gpdTransform hσ hξ0]; ring]
  simp only [A, B, D, A', D']
  field_simp
  ring

/-- `E[∂²_ξ ℓ] = -2/((1 + ξ)(1 + 2ξ))`. -/
theorem integral_gpdHessXiXi :
    ∫ x, gpdHessXiXi ξ σ x ∂gpdMeasure ξ σ = -(2 / ((1 + ξ) * (1 + 2 * ξ))) := by
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have h2ξ : 1 + 2 * ξ ≠ 0 := by intro h; linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  rw [integral_gpdMeasure_of_poly hξ (measurable_gpdHessXiXi ξ σ) _ _ _ _ _ _
    (gpdHessXiXi_gpdTransform hσ hξ0)]
  field_simp
  ring

/-- `E[∂_ξ ∂_σ ℓ] = -1/(σ (1 + ξ)(1 + 2ξ))`. -/
theorem integral_gpdHessXiSigma :
    ∫ x, gpdHessXiSigma ξ σ x ∂gpdMeasure ξ σ = -(1 / (σ * (1 + ξ) * (1 + 2 * ξ))) := by
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have h2ξ : 1 + 2 * ξ ≠ 0 := by intro h; linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  rw [integral_gpdMeasure_of_poly hξ (measurable_gpdHessXiSigma ξ σ) _ _ _ _ _ _
    (gpdHessXiSigma_gpdTransform hσ hξ0)]
  field_simp
  ring

/-- `E[∂²_σ ℓ] = -1/(σ² (1 + 2ξ))`. -/
theorem integral_gpdHessSigmaSigma :
    ∫ x, gpdHessSigmaSigma ξ σ x ∂gpdMeasure ξ σ = -(1 / (σ ^ 2 * (1 + 2 * ξ))) := by
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have h2ξ : 1 + 2 * ξ ≠ 0 := by intro h; linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  rw [integral_gpdMeasure_of_poly hξ (measurable_gpdHessSigmaSigma ξ σ) _ _ _ _ _ _
    (gpdHessSigmaSigma_gpdTransform hσ hξ0)]
  field_simp
  ring

lemma integrable_gpdHessXiXi : Integrable (gpdHessXiXi ξ σ) (gpdMeasure ξ σ) :=
  integrable_gpdMeasure_of_poly hξ (measurable_gpdHessXiXi ξ σ) _ _ _ _ _ _
    (gpdHessXiXi_gpdTransform hσ hξ0)

lemma integrable_gpdHessXiSigma : Integrable (gpdHessXiSigma ξ σ) (gpdMeasure ξ σ) :=
  integrable_gpdMeasure_of_poly hξ (measurable_gpdHessXiSigma ξ σ) _ _ _ _ _ _
    (gpdHessXiSigma_gpdTransform hσ hξ0)

lemma integrable_gpdHessSigmaSigma : Integrable (gpdHessSigmaSigma ξ σ) (gpdMeasure ξ σ) :=
  integrable_gpdMeasure_of_poly hξ (measurable_gpdHessSigmaSigma ξ σ) _ _ _ _ _ _
    (gpdHessSigmaSigma_gpdTransform hσ hξ0)

/-- The combinations of the scores are square integrable. -/
lemma memLp_lin_score (u v : ℝ) :
    MemLp (fun x => u * gpdScoreXi ξ σ x + v * gpdScoreSigma ξ σ x) 2 (gpdMeasure ξ σ) := by
  have hm : Measurable fun x => u * gpdScoreXi ξ σ x + v * gpdScoreSigma ξ σ x := by
    have := measurable_gpdScoreXi ξ σ; have := measurable_gpdScoreSigma ξ σ; fun_prop
  rw [gpdMeasure, stdExpMeasure_eq_expMeasure, memLp_map_measure_iff hm.aestronglyMeasurable
    (measurable_gpdTransform ξ σ).aemeasurable]
  exact (memLp_lin_exp_expMeasure hξ (u * -((1 / ξ + 1) / ξ) + v * (((1 + ξ) / ξ - 1) / σ))
    (u * (1 / ξ)) (u * ((1 / ξ + 1) / ξ) + v * (-((1 + ξ) / ξ) / σ))).ae_eq
    (ae_of_all _ fun t => (lin_score_gpdTransform hσ hξ0 u v t).symm)

end GPDMoments

end ExtremeValueTheory
