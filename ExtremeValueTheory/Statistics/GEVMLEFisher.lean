/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLE
import ExtremeValueTheory.Statistics.GPDFisherInformation

/-!
# The location-scale Fisher information of the GEV family and the score CLT

Fix a shape `ξ ≠ 0`. For a point `x` of the support, `z = (x - μ)/σ`, `u = 1 + ξ z > 0`, the
GEV log-density is `ℓ(μ, σ; x) = -log σ - (1/ξ + 1) log u - u^{-1/ξ}`
(`log_gevLocScaleDensity`). Its location and scale scores are

* `∂_μ ℓ = (1 + ξ - u^{-1/ξ}) / (σ u)` (`gevScoreMu`),
* `∂_σ ℓ = -(1 + z (u^{-1/ξ} - 1 - ξ)/u) / σ` (`gevScoreSigma`).

On the exponential scale `x = μ + σ (t^{-ξ} - 1)/ξ`, with `t` standard exponential under the
true law, these are `σ ∂_μ ℓ = (1 + ξ - t) t^ξ` and `σ ∂_σ ℓ = -1 - (t - 1 - ξ)(1 - t^ξ)/ξ`,
combinations of the monomials `t^k (t^ξ)^j`, `k, j ≤ 2`, whose expectations are Gamma values
`Γ(k + j ξ + 1)`; they are finite exactly when `ξ > -1/2`. For `ξ > -1/2`, `ξ ≠ 0`, the scores
have mean zero, are square integrable, and their covariance is the location-scale block of the
**Fisher information of Prescott–Walden (1980)**:

  `I_μμ = p/σ²`, `I_μσ = (Γ(2 + ξ) - p)/(ξ σ²)`, `I_σσ = (1 - 2Γ(2 + ξ) + p)/(ξ² σ²)`,

with `p = (1 + ξ)² Γ(1 + 2ξ)` (`gevFisherInfoMuSigma`).

## Main results

* `hasDerivAt_log_gevLocScaleDensity_mu`, `hasDerivAt_log_gevLocScaleDensity_sigma`: the scores
  are the partial derivatives of the log-density.
* `integral_gevPoly`, `integral_gevLocScaleCDF_of_poly`: expectations of `t^k (t^ξ)^j`
  combinations against the GEV law as Gamma values.
* `integral_gevScoreMu`, `integral_gevScoreSigma`: the scores have mean zero.
* `integral_gevScoreMu_sq`, `integral_gevScoreMu_mul_gevScoreSigma`, `integral_gevScoreSigma_sq`:
  the Fisher information entries; `integral_lin_gevScore_sq`: the quadratic form.
* `posSemidef_gevFisherInfoMuSigma`, `posDef_gevFisherInfoMuSigma`: the information matrix is
  positive definite; its determinant is `((1 + ξ)² Γ(1 + 2ξ) - Γ(2 + ξ)²)/(ξ² σ⁴)`, positive by
  `Gamma_one_add_sq_lt`: `Γ(1 + ξ)² < Γ(1 + 2ξ)` (the variance of `T^ξ`, `T` exponential).
* `tendstoInDistribution_gevScoreVec`: **the bivariate score CLT**
  `n^{-1/2} ∑_{i<n} (∂_μ ℓ, ∂_σ ℓ)(Xᵢ) ⇒ N(0, I_{(μ,σ)})`, and in particular the one-parameter
  (location only, scale only) score CLTs `tendstoInDistribution_gevScoreMu`,
  `tendstoInDistribution_gevScoreSigma`.

## Not covered

The shape score `∂_ξ ℓ` involves `log t`, and its moments involve the digamma function and
`π²/6`; the shape row of the information matrix and the trivariate score CLT are in
`ExtremeValueTheory.Statistics.GEVFisherInformation`, the information identity (expected
Hessian) in `ExtremeValueTheory.Statistics.GEVHessian`. The joint asymptotic normality of the
three-parameter MLE (Bücher–Segers 2017) is not formalized.

## References

* D. Prescott and A. T. Walden, *Maximum likelihood estimation of the parameters of the
  generalized extreme-value distribution*, Biometrika 67 (1980).
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* A. Bücher and J. Segers, *On the maximum likelihood estimator for the Generalized Extreme-Value
  distribution*, Extremes 20 (2017).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### Gamma moments on the exponential scale -/

section GammaMoments

variable {β : ℝ}

/-- `∫_0^∞ e^{-t} t^a dt = Γ(a + 1)` for `a > -1`. -/
lemma integral_exp_neg_mul_rpow {a : ℝ} (ha : -1 < a) :
    ∫ t in Ioi 0, exp (-t) * t ^ a = Gamma (a + 1) := by
  rw [Gamma_eq_integral (by linarith)]
  simp

private lemma row_eq {t : ℝ} (ht : 0 < t) (β a b c : ℝ) :
    exp (-t) * (t ^ β * (a + b * t + c * t ^ 2)) =
      a * (exp (-t) * t ^ β) + b * (exp (-t) * t ^ (β + 1)) +
        c * (exp (-t) * t ^ (β + 2)) := by
  rw [rpow_add ht, rpow_add ht, rpow_one, rpow_two]
  ring

lemma integrableOn_row (hβ : -1 < β) (a b c : ℝ) :
    IntegrableOn (fun t => exp (-t) * (t ^ β * (a + b * t + c * t ^ 2))) (Ioi 0) :=
  IntegrableOn.congr_fun ((((integrableOn_exp_neg_mul_rpow hβ).const_mul a).add
    ((integrableOn_exp_neg_mul_rpow (a := β + 1) (by linarith)).const_mul b)).add
    ((integrableOn_exp_neg_mul_rpow (a := β + 2) (by linarith)).const_mul c))
    (fun t ht => (row_eq ht β a b c).symm) measurableSet_Ioi

/-- `∫_0^∞ e^{-t} t^β (a + b t + c t²) dt = Γ(β + 1)(a + (β + 1) b + (β + 2)(β + 1) c)`. -/
lemma integral_row (hβ : -1 < β) (a b c : ℝ) :
    ∫ t in Ioi 0, exp (-t) * (t ^ β * (a + b * t + c * t ^ 2)) =
      Gamma (β + 1) * (a + (β + 1) * b + (β + 2) * (β + 1) * c) := by
  have i0 := integrableOn_exp_neg_mul_rpow hβ
  have i1 := integrableOn_exp_neg_mul_rpow (a := β + 1) (by linarith)
  have i2 := integrableOn_exp_neg_mul_rpow (a := β + 2) (by linarith)
  have i01 : IntegrableOn (fun t => a * (exp (-t) * t ^ β) + b * (exp (-t) * t ^ (β + 1)))
      (Ioi 0) := (i0.const_mul a).add (i1.const_mul b)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => row_eq ht β a b c),
    integral_add i01 (i2.const_mul c),
    integral_add (i0.const_mul a) (i1.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_exp_neg_mul_rpow hβ, integral_exp_neg_mul_rpow (by linarith),
    integral_exp_neg_mul_rpow (by linarith)]
  have g1 : Gamma (β + 1 + 1) = (β + 1) * Gamma (β + 1) := Gamma_add_one (by linarith)
  have g2 : Gamma (β + 2 + 1) = (β + 2) * (β + 1) * Gamma (β + 1) := by
    rw [Gamma_add_one (by linarith), show β + 2 = β + 1 + 1 by ring, g1]
    ring
  rw [g1, g2]
  ring

/-- The combinations `P(t) = (a₀ + b₀ t + c₀ t²) + t^ξ (a₁ + b₁ t + c₁ t²) +
(t^ξ)² (a₂ + b₂ t + c₂ t²)` of the monomials `t^k (t^ξ)^j`. -/
noncomputable def gevPoly (ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t : ℝ) : ℝ :=
  (a₀ + b₀ * t + c₀ * t ^ 2) + t ^ ξ * (a₁ + b₁ * t + c₁ * t ^ 2) +
    (t ^ ξ) ^ 2 * (a₂ + b₂ * t + c₂ * t ^ 2)

variable {ξ : ℝ} (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)

private lemma exp_neg_mul_gevPoly {t : ℝ} (ht : 0 < t) :
    exp (-t) * gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t =
      exp (-t) * (t ^ (0 : ℝ) * (a₀ + b₀ * t + c₀ * t ^ 2)) +
        exp (-t) * (t ^ ξ * (a₁ + b₁ * t + c₁ * t ^ 2)) +
        exp (-t) * (t ^ (2 * ξ) * (a₂ + b₂ * t + c₂ * t ^ 2)) := by
  have h : (t ^ ξ) ^ 2 = t ^ (2 * ξ) := by rw [mul_comm, rpow_mul ht.le, rpow_two]
  rw [gevPoly, rpow_zero, h]
  ring

variable {a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂} in
lemma integrableOn_gevPoly (hξ : -1 / 2 < ξ) :
    IntegrableOn (fun t => exp (-t) * gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t) (Ioi 0) :=
  IntegrableOn.congr_fun (((integrableOn_row (β := 0) (by norm_num) a₀ b₀ c₀).add
    (integrableOn_row (β := ξ) (by linarith) a₁ b₁ c₁)).add
    (integrableOn_row (β := 2 * ξ) (by linarith) a₂ b₂ c₂))
    (fun t ht => (exp_neg_mul_gevPoly a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ ht).symm) measurableSet_Ioi

/-- **Gamma moments**: `E P(T) = a₀ + b₀ + 2c₀ + Γ(ξ + 1)(a₁ + (ξ + 1) b₁ + (ξ + 2)(ξ + 1) c₁)
+ Γ(2ξ + 1)(a₂ + (2ξ + 1) b₂ + (2ξ + 2)(2ξ + 1) c₂)` for a standard exponential `T`, `ξ > -1/2`. -/
theorem integral_gevPoly (hξ : -1 / 2 < ξ) :
    ∫ t in Ioi 0, exp (-t) * gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t =
      a₀ + b₀ + 2 * c₀ + Gamma (ξ + 1) * (a₁ + (ξ + 1) * b₁ + (ξ + 2) * (ξ + 1) * c₁) +
        Gamma (2 * ξ + 1) * (a₂ + (2 * ξ + 1) * b₂ + (2 * ξ + 2) * (2 * ξ + 1) * c₂) := by
  have i0 := integrableOn_row (β := 0) (by norm_num) a₀ b₀ c₀
  have i1 := integrableOn_row (β := ξ) (by linarith) a₁ b₁ c₁
  have i2 := integrableOn_row (β := 2 * ξ) (by linarith) a₂ b₂ c₂
  have i01 : IntegrableOn (fun t => exp (-t) * (t ^ (0 : ℝ) * (a₀ + b₀ * t + c₀ * t ^ 2)) +
      exp (-t) * (t ^ ξ * (a₁ + b₁ * t + c₁ * t ^ 2))) (Ioi 0) := i0.add i1
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => exp_neg_mul_gevPoly a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ ht),
    integral_add i01 i2, integral_add i0 i1, integral_row (by norm_num),
    integral_row (by linarith), integral_row (by linarith)]
  simp only [zero_add, Gamma_one]
  ring

end GammaMoments

/-! ### Expectations against the location-scale GEV law -/

section Law

variable {ξ μ σ : ℝ}

lemma measurable_affine_gevTransform (ξ μ σ : ℝ) :
    Measurable fun t => μ + σ * gevTransform ξ t :=
  measurable_const.add (measurable_const.mul (measurable_gevTransform ξ))

/-- Integrals against the location-scale GEV law on the exponential scale. -/
theorem integral_gevLocScaleCDF (hσ : 0 < σ) {h : ℝ → ℝ} (hh : Measurable h) :
    ∫ x, h x ∂(gevLocScaleCDF ξ μ hσ).measure =
      ∫ t in Ioi 0, exp (-t) * h (μ + σ * gevTransform ξ t) := by
  rw [measure_gevLocScaleCDF_eq_map, integral_map
    (measurable_affine_gevTransform ξ μ σ).aemeasurable hh.aestronglyMeasurable, stdExpMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext t
  rw [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]

theorem integrable_gevLocScaleCDF_iff (hσ : 0 < σ) {h : ℝ → ℝ} (hh : Measurable h) :
    Integrable h (gevLocScaleCDF ξ μ hσ).measure ↔
      IntegrableOn (fun t => exp (-t) * h (μ + σ * gevTransform ξ t)) (Ioi 0) := by
  rw [measure_gevLocScaleCDF_eq_map, integrable_map_measure hh.aestronglyMeasurable
    (measurable_affine_gevTransform ξ μ σ).aemeasurable,
    integrable_stdExpMeasure_iff (hh.comp (measurable_affine_gevTransform ξ μ σ))]
  rfl

variable {h : ℝ → ℝ} {a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ : ℝ}

/-- The expectation against the GEV law of a function which, on the exponential scale, is a
combination of the monomials `t^k (t^ξ)^j`, `k, j ≤ 2`. -/
theorem integral_gevLocScaleCDF_of_poly (hξ : -1 / 2 < ξ) (hσ : 0 < σ) (hh : Measurable h)
    (heq : ∀ t, 0 < t → h (μ + σ * gevTransform ξ t) = gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t) :
    ∫ x, h x ∂(gevLocScaleCDF ξ μ hσ).measure =
      a₀ + b₀ + 2 * c₀ + Gamma (ξ + 1) * (a₁ + (ξ + 1) * b₁ + (ξ + 2) * (ξ + 1) * c₁) +
        Gamma (2 * ξ + 1) * (a₂ + (2 * ξ + 1) * b₂ + (2 * ξ + 2) * (2 * ξ + 1) * c₂) := by
  rw [integral_gevLocScaleCDF hσ hh, ← integral_gevPoly _ _ _ _ _ _ _ _ _ hξ]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => congrArg (exp (-t) * ·) (heq t ht)

theorem integrable_gevLocScaleCDF_of_poly (hξ : -1 / 2 < ξ) (hσ : 0 < σ) (hh : Measurable h)
    (heq : ∀ t, 0 < t → h (μ + σ * gevTransform ξ t) = gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t) :
    Integrable h (gevLocScaleCDF ξ μ hσ).measure := by
  rw [integrable_gevLocScaleCDF_iff hσ hh]
  exact (integrableOn_gevPoly hξ).congr_fun
    (fun t ht => congrArg (exp (-t) * ·) (heq t ht).symm) measurableSet_Ioi

end Law

/-! ### The location and scale scores -/

section Scores

open Matrix

variable {ξ μ σ x : ℝ}

/-- The location score `∂_μ log(σ⁻¹ h_ξ((x - μ)/σ)) = (1 + ξ - u^{-1/ξ})/(σ u)`,
`u = 1 + ξ (x - μ)/σ`. -/
noncomputable def gevScoreMu (ξ μ σ x : ℝ) : ℝ :=
  (1 + ξ - (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ)) / (σ * (1 + ξ * ((x - μ) / σ)))

/-- The scale score `∂_σ log(σ⁻¹ h_ξ((x - μ)/σ)) = -(1 + z (u^{-1/ξ} - 1 - ξ)/u)/σ`,
`z = (x - μ)/σ`, `u = 1 + ξ z`. -/
noncomputable def gevScoreSigma (ξ μ σ x : ℝ) : ℝ :=
  -(1 + (x - μ) / σ * ((1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) - 1 - ξ) /
    (1 + ξ * ((x - μ) / σ))) / σ

lemma measurable_gevScoreMu (ξ μ σ : ℝ) : Measurable (gevScoreMu ξ μ σ) := by
  unfold gevScoreMu; fun_prop

lemma measurable_gevScoreSigma (ξ μ σ : ℝ) : Measurable (gevScoreSigma ξ μ σ) := by
  unfold gevScoreSigma; fun_prop

/-- **The location score is the derivative of the log-density in `μ`.** -/
theorem hasDerivAt_log_gevLocScaleDensity_mu (hσ : 0 < σ) (hξ : ξ ≠ 0)
    (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    HasDerivAt (fun m => log (gevLocScaleDensity ξ m σ x)) (gevScoreMu ξ μ σ x) μ := by
  have hU : HasDerivAt (fun m => 1 + ξ * ((x - m) / σ)) (ξ * (-1 / σ)) μ := by
    have := (((hasDerivAt_id μ).const_sub x).div_const σ).const_mul ξ
    simpa using this.const_add 1
  have hcu : ContinuousAt (fun m => 1 + ξ * ((x - m) / σ)) μ := hU.continuousAt
  have heq : (fun m => -log σ - (1 / ξ + 1) * log (1 + ξ * ((x - m) / σ)) -
      (1 + ξ * ((x - m) / σ)) ^ (-1 / ξ)) =ᶠ[𝓝 μ]
      fun m => log (gevLocScaleDensity ξ m σ x) := by
    filter_upwards [hcu.eventually (lt_mem_nhds hu)] with m hm
    rw [log_gevLocScaleDensity hσ hξ hm]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq.symm
  have hd := ((hasDerivAt_const μ (-log σ)).sub ((hU.log hu.ne').const_mul (1 / ξ + 1))).sub
    (hU.rpow_const (p := -1 / ξ) (Or.inl hu.ne'))
  convert hd using 1
  rw [gevScoreMu, rpow_sub_one hu.ne']
  field_simp
  ring

/-- **The scale score is the derivative of the log-density in `σ`.** -/
theorem hasDerivAt_log_gevLocScaleDensity_sigma (hσ : 0 < σ) (hξ : ξ ≠ 0)
    (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    HasDerivAt (fun s => log (gevLocScaleDensity ξ μ s x)) (gevScoreSigma ξ μ σ x) σ := by
  have hz : HasDerivAt (fun s => (x - μ) / s) ((0 * σ - (x - μ) * 1) / σ ^ 2) σ :=
    (hasDerivAt_const σ (x - μ)).div (hasDerivAt_id σ) hσ.ne'
  have hU : HasDerivAt (fun s => 1 + ξ * ((x - μ) / s)) (ξ * ((0 * σ - (x - μ) * 1) / σ ^ 2))
      σ := (hz.const_mul ξ).const_add 1
  have hcu : ContinuousAt (fun s => 1 + ξ * ((x - μ) / s)) σ := hU.continuousAt
  have heq : (fun s => -log s - (1 / ξ + 1) * log (1 + ξ * ((x - μ) / s)) -
      (1 + ξ * ((x - μ) / s)) ^ (-1 / ξ)) =ᶠ[𝓝 σ]
      fun s => log (gevLocScaleDensity ξ μ s x) := by
    filter_upwards [hcu.eventually (lt_mem_nhds hu), lt_mem_nhds hσ] with s hs hs0
    rw [log_gevLocScaleDensity hs0 hξ hs]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq.symm
  have hd := (((hasDerivAt_log hσ.ne').neg).sub ((hU.log hu.ne').const_mul (1 / ξ + 1))).sub
    (hU.rpow_const (p := -1 / ξ) (Or.inl hu.ne'))
  convert hd using 1
  rw [gevScoreSigma, rpow_sub_one hu.ne']
  field_simp
  ring

lemma rpow_neg_rpow_neg_one_div (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    (t ^ (-ξ)) ^ (-1 / ξ) = t := by
  rw [← rpow_mul ht.le, show -ξ * (-1 / ξ) = 1 by field_simp, rpow_one]

/-- A combination `a ∂_μ ℓ + b ∂_σ ℓ` of the scores on the exponential scale:
`A₀ + B₀ t + t^ξ (A₁ + B₁ t)`. -/
lemma lin_gevScore_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    a * gevScoreMu ξ μ σ (μ + σ * gevTransform ξ t) +
        b * gevScoreSigma ξ μ σ (μ + σ * gevTransform ξ t) =
      b / (ξ * σ) + (-(b / (ξ * σ))) * t +
        t ^ ξ * ((a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ)) + (b / (ξ * σ) - a / σ) * t) := by
  have hz : (μ + σ * gevTransform ξ t - μ) / σ = gevTransform ξ t := by
    field_simp; ring
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevScoreMu, gevScoreSigma, hz, one_add_mul_gevTransform hξ ht,
    rpow_neg_rpow_neg_one_div hξ ht]
  simp only [gevTransform, hξ, ↓reduceIte]
  rw [rpow_neg ht.le]
  field_simp
  ring

/-- The Fisher information of the location-scale GEV family (shape `ξ` known), in the
parametrization `(μ, σ)` (Prescott–Walden 1980): with `p = (1 + ξ)² Γ(1 + 2ξ)`,
`I = [[p/σ², (Γ(2 + ξ) - p)/(ξσ²)], [(Γ(2 + ξ) - p)/(ξσ²), (1 - 2Γ(2 + ξ) + p)/(ξ²σ²)]]`. -/
noncomputable def gevFisherInfoMuSigma (ξ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) / σ ^ 2,
    (Gamma (2 + ξ) - (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ * σ ^ 2);
    (Gamma (2 + ξ) - (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ * σ ^ 2),
    (1 - 2 * Gamma (2 + ξ) + (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ ^ 2 * σ ^ 2)]

lemma dotProduct_gevFisherInfoMuSigma_mulVec (v : Fin 2 → ℝ) :
    v ⬝ᵥ (gevFisherInfoMuSigma ξ σ *ᵥ v) =
      v 0 ^ 2 * ((1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) / σ ^ 2) +
        2 * v 0 * v 1 * ((Gamma (2 + ξ) - (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ * σ ^ 2)) +
        v 1 ^ 2 * ((1 - 2 * Gamma (2 + ξ) + (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) /
          (ξ ^ 2 * σ ^ 2)) := by
  simp [gevFisherInfoMuSigma, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

variable (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ)
include hσ hξ0 hξ

/-- **Every combination of the scores has mean zero.** -/
theorem integral_lin_gevScore (a b : ℝ) :
    ∫ x, (a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x)
      ∂(gevLocScaleCDF ξ μ hσ).measure = 0 := by
  have hm : Measurable fun x => a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ; fun_prop
  rw [integral_gevLocScaleCDF_of_poly hξ hσ hm (a₀ := b / (ξ * σ)) (b₀ := -(b / (ξ * σ)))
    (c₀ := 0) (a₁ := a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ)) (b₁ := b / (ξ * σ) - a / σ)
    (c₁ := 0) (a₂ := 0) (b₂ := 0) (c₂ := 0) fun t ht => by
      rw [lin_gevScore_transform hσ hξ0 a b ht, gevPoly]; ring]
  field_simp
  ring

/-- **The quadratic form of the Fisher information**: `E[(a ∂_μ ℓ + b ∂_σ ℓ)²] = (a, b) I (a, b)ᵀ`
for `ξ > -1/2`, `ξ ≠ 0`. -/
theorem integral_lin_gevScore_sq (a b : ℝ) :
    ∫ x, (a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x) ^ 2
      ∂(gevLocScaleCDF ξ μ hσ).measure =
      a ^ 2 * ((1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) / σ ^ 2) +
        2 * a * b * ((Gamma (2 + ξ) - (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ * σ ^ 2)) +
        b ^ 2 * ((1 - 2 * Gamma (2 + ξ) + (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) /
          (ξ ^ 2 * σ ^ 2)) := by
  have hm : Measurable fun x => (a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x) ^ 2 := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ; fun_prop
  set A₀ := b / (ξ * σ)
  set B₀ := -(b / (ξ * σ))
  set A₁ := a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ)
  set B₁ := b / (ξ * σ) - a / σ
  rw [integral_gevLocScaleCDF_of_poly hξ hσ hm (a₀ := A₀ ^ 2) (b₀ := 2 * A₀ * B₀) (c₀ := B₀ ^ 2)
    (a₁ := 2 * A₀ * A₁) (b₁ := 2 * (A₀ * B₁ + A₁ * B₀)) (c₁ := 2 * B₀ * B₁) (a₂ := A₁ ^ 2)
    (b₂ := 2 * A₁ * B₁) (c₂ := B₁ ^ 2) fun t ht => by
      rw [lin_gevScore_transform hσ hξ0 a b ht, gevPoly]; ring]
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one (by linarith)]
  rw [g2, show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  simp only [A₀, B₀, A₁, B₁]
  field_simp
  ring

/-- **The location score has mean zero.** -/
theorem integral_gevScoreMu : ∫ x, gevScoreMu ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure = 0 := by
  simpa using integral_lin_gevScore hσ hξ0 hξ 1 0

/-- **The scale score has mean zero.** -/
theorem integral_gevScoreSigma :
    ∫ x, gevScoreSigma ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure = 0 := by
  simpa using integral_lin_gevScore hσ hξ0 hξ 0 1

/-- `I_μμ = E[(∂_μ ℓ)²] = (1 + ξ)² Γ(1 + 2ξ)/σ²`. -/
theorem integral_gevScoreMu_sq :
    ∫ x, gevScoreMu ξ μ σ x ^ 2 ∂(gevLocScaleCDF ξ μ hσ).measure =
      (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) / σ ^ 2 := by
  simpa using integral_lin_gevScore_sq hσ hξ0 hξ 1 0

/-- `I_σσ = E[(∂_σ ℓ)²] = (1 - 2Γ(2 + ξ) + (1 + ξ)² Γ(1 + 2ξ))/(ξ² σ²)`. -/
theorem integral_gevScoreSigma_sq :
    ∫ x, gevScoreSigma ξ μ σ x ^ 2 ∂(gevLocScaleCDF ξ μ hσ).measure =
      (1 - 2 * Gamma (2 + ξ) + (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ ^ 2 * σ ^ 2) := by
  simpa using integral_lin_gevScore_sq hσ hξ0 hξ 0 1

/-- The combinations of the scores are square integrable. -/
lemma memLp_lin_gevScore (a b : ℝ) :
    MemLp (fun x => a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x) 2
      (gevLocScaleCDF ξ μ hσ).measure := by
  have hm : Measurable fun x => a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ; fun_prop
  set A₀ := b / (ξ * σ)
  set B₀ := -(b / (ξ * σ))
  set A₁ := a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ)
  set B₁ := b / (ξ * σ) - a / σ
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact integrable_gevLocScaleCDF_of_poly hξ hσ (hm.pow_const 2) (a₀ := A₀ ^ 2)
    (b₀ := 2 * A₀ * B₀) (c₀ := B₀ ^ 2) (a₁ := 2 * A₀ * A₁) (b₁ := 2 * (A₀ * B₁ + A₁ * B₀))
    (c₁ := 2 * B₀ * B₁) (a₂ := A₁ ^ 2) (b₂ := 2 * A₁ * B₁) (c₂ := B₁ ^ 2) fun t ht => by
      rw [lin_gevScore_transform hσ hξ0 a b ht, gevPoly]; ring

/-- `I_μσ = E[∂_μ ℓ ∂_σ ℓ] = (Γ(2 + ξ) - (1 + ξ)² Γ(1 + 2ξ))/(ξ σ²)`, by polarization. -/
theorem integral_gevScoreMu_mul_gevScoreSigma :
    ∫ x, gevScoreMu ξ μ σ x * gevScoreSigma ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure =
      (Gamma (2 + ξ) - (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ * σ ^ 2) := by
  have h11 := integral_lin_gevScore_sq hσ hξ0 hξ (μ := μ) 1 1
  have i11 := (memLp_lin_gevScore hσ hξ0 hξ (μ := μ) 1 1).integrable_sq
  have i10 := (memLp_lin_gevScore hσ hξ0 hξ (μ := μ) 1 0).integrable_sq
  have i01 := (memLp_lin_gevScore hσ hξ0 hξ (μ := μ) 0 1).integrable_sq
  have hsq1 := integral_gevScoreMu_sq hσ hξ0 hξ (μ := μ)
  have hsq2 := integral_gevScoreSigma_sq hσ hξ0 hξ (μ := μ)
  have e : (fun x => gevScoreMu ξ μ σ x * gevScoreSigma ξ μ σ x) = fun x =>
      ((1 * gevScoreMu ξ μ σ x + 1 * gevScoreSigma ξ μ σ x) ^ 2 -
        (1 * gevScoreMu ξ μ σ x + 0 * gevScoreSigma ξ μ σ x) ^ 2 -
        (0 * gevScoreMu ξ μ σ x + 1 * gevScoreSigma ξ μ σ x) ^ 2) / 2 := by
    funext x; ring
  have i2 : Integrable (fun x => (1 * gevScoreMu ξ μ σ x + 1 * gevScoreSigma ξ μ σ x) ^ 2 -
      (1 * gevScoreMu ξ μ σ x + 0 * gevScoreSigma ξ μ σ x) ^ 2)
      (gevLocScaleCDF ξ μ hσ).measure := i11.sub i10
  rw [e, integral_div, integral_sub i2 i01, integral_sub i11 i10, h11]
  simp only [one_mul, zero_mul, add_zero, zero_add] at hsq1 hsq2 ⊢
  rw [hsq1, hsq2]
  ring

end Scores

/-! ### Positivity of the information and the score CLT -/

section ScoreCLT

open RealInnerProductSpace Matrix

variable {ξ μ σ : ℝ}

/-- The location-scale Fisher information of the GEV is positive semidefinite (it is the
covariance matrix of the score). -/
theorem posSemidef_gevFisherInfoMuSigma (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    (gevFisherInfoMuSigma ξ σ).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [gevFisherInfoMuSigma]
  · rw [star_trivial, dotProduct_gevFisherInfoMuSigma_mulVec,
      ← integral_lin_gevScore_sq hσ hξ0 hξ (μ := 0) (v 0) (v 1)]
    exact integral_nonneg fun x => sq_nonneg _

/-- **`Γ(1 + ξ)² < Γ(1 + 2ξ)`** for `ξ > -1/2`, `ξ ≠ 0`: the difference is the variance
`∫_0^∞ e^{-t} (t^ξ - Γ(1 + ξ))² dt` of `T^ξ` for a standard exponential `T`, and `t ↦ t^ξ` is
injective. -/
theorem Gamma_one_add_sq_lt (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) :
    Gamma (1 + ξ) ^ 2 < Gamma (1 + 2 * ξ) := by
  set c := Gamma (1 + ξ) with hc
  have heq : ∀ t, gevPoly ξ (c ^ 2) 0 0 (-2 * c) 0 0 1 0 0 t = (t ^ ξ - c) ^ 2 := fun t => by
    rw [gevPoly]; ring
  have hI := integral_gevPoly (ξ := ξ) (c ^ 2) 0 0 (-2 * c) 0 0 1 0 0 hξ
  simp only [heq] at hI
  have hint : IntegrableOn (fun t => exp (-t) * (t ^ ξ - c) ^ 2) (Ioi 0) := by
    have := integrableOn_gevPoly (a₀ := c ^ 2) (b₀ := 0) (c₀ := 0) (a₁ := -2 * c) (b₁ := 0)
      (c₁ := 0) (a₂ := 1) (b₂ := 0) (c₂ := 0) hξ
    simpa only [heq] using this
  have hpos : 0 < ∫ t in Ioi 0, exp (-t) * (t ^ ξ - c) ^ 2 := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun t => by simp only [Pi.zero_apply]; positivity) hint]
    set S := {t : ℝ | 0 < t ∧ t ^ ξ = c}
    have hS : volume S = 0 := by
      refine Set.Subsingleton.measure_zero ?_ _
      intro s hs t ht
      exact rpow_left_injOn hξ0 (show (0 : ℝ) ≤ s from hs.1.le) (show (0 : ℝ) ≤ t from ht.1.le)
        (hs.2.trans ht.2.symm)
    have hsub : Ioi 0 \ S ⊆ Function.support (fun t => exp (-t) * (t ^ ξ - c) ^ 2) ∩ Ioi 0 := by
      intro t ht
      refine ⟨?_, ht.1⟩
      simp only [Function.mem_support]
      exact mul_ne_zero (exp_pos _).ne'
        (pow_ne_zero 2 (sub_ne_zero.2 fun h => ht.2 ⟨ht.1, h⟩))
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [measure_sdiff_null hS, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  rw [hI, show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring, ← hc] at hpos
  nlinarith

/-- **The location-scale Fisher information of the GEV is positive definite** for
`ξ > -1/2`, `ξ ≠ 0`: its determinant is `((1 + ξ)² Γ(1 + 2ξ) - Γ(2 + ξ)²)/(ξ² σ⁴) > 0`. -/
theorem posDef_gevFisherInfoMuSigma (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    (gevFisherInfoMuSigma ξ σ).PosDef := by
  have hG := Gamma_one_add_sq_lt hξ hξ0
  have hg2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one (by linarith)]
  have hΓ : 0 < Gamma (1 + 2 * ξ) := Gamma_pos_of_pos (by linarith)
  have h1ξ : 0 < 1 + ξ := by linarith
  have hp : 0 < (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) := by positivity
  have hpg : 0 < (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) - Gamma (2 + ξ) ^ 2 := by
    rw [hg2, mul_pow, ← mul_sub]
    exact mul_pos (by positivity) (by linarith)
  set p := (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)
  set g := Gamma (2 + ξ)
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [gevFisherInfoMuSigma]
  · rw [star_trivial, dotProduct_gevFisherInfoMuSigma_mulVec]
    have e : v 0 ^ 2 * (p / σ ^ 2) + 2 * v 0 * v 1 * ((g - p) / (ξ * σ ^ 2)) +
        v 1 ^ 2 * ((1 - 2 * g + p) / (ξ ^ 2 * σ ^ 2)) =
        (p * (v 0 + v 1 * ((g - p) / (ξ * p))) ^ 2 + v 1 ^ 2 * ((p - g ^ 2) / (ξ ^ 2 * p))) /
          σ ^ 2 := by
      field_simp
      ring
    rw [e]
    refine div_pos ?_ (by positivity)
    have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    have hA : 0 ≤ p * (v 0 + v 1 * ((g - p) / (ξ * p))) ^ 2 := by positivity
    rcases eq_or_ne (v 1) 0 with h1 | h1
    · have h0 : v 0 ≠ 0 := hne.resolve_right (not_not.2 h1)
      rw [h1]
      simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_pos hp (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0)))
    · have : 0 < v 1 ^ 2 * ((p - g ^ 2) / (ξ ^ 2 * p)) :=
        mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1)))
          (div_pos hpg (mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hξ0))) hp))
      linarith

/-- **The location-scale score vector** `(∂_μ ℓ, ∂_σ ℓ) ∈ ℝ²` of one observation. -/
noncomputable def gevScoreVec (ξ μ σ x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[gevScoreMu ξ μ σ x, gevScoreSigma ξ μ σ x]

lemma measurable_gevScoreVec (ξ μ σ : ℝ) : Measurable (gevScoreVec ξ μ σ) := by
  unfold gevScoreVec
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · simpa using measurable_gevScoreMu ξ μ σ
  · simpa using measurable_gevScoreSigma ξ μ σ

lemma inner_gevScoreVec (x : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ⟪gevScoreVec ξ μ σ x, v⟫ = v 0 * gevScoreMu ξ μ σ x + v 1 * gevScoreSigma ξ μ σ x := by
  simp [gevScoreVec, PiLp.inner_apply, Fin.sum_univ_two]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}

/-- **The bivariate central limit theorem for the GEV location-scale score.** Let
`X₀, X₁, …` be iid with the location-scale GEV law of parameters `(ξ, μ, σ)`,
`-1/2 < ξ`, `ξ ≠ 0`. Then `n^{-1/2} ∑_{i<n} (∂_μ ℓ, ∂_σ ℓ)(Xᵢ)` converges in distribution in
`ℝ²` to the centered Gaussian law whose covariance is the Fisher information
`gevFisherInfoMuSigma ξ σ`. -/
theorem tendstoInDistribution_gevScoreVec (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ μ hσ).measure P) (hind : iIndepFun X P)
    {Z : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hZ : HasLaw Z (multivariateGaussian 0 (gevFisherInfoMuSigma ξ σ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gevScoreVec ξ μ σ (X i ω))
      atTop Z (fun _ => P) P' := by
  refine TendstoInDistribution.of_inner hZ.aemeasurable (fun n => ?_) fun v => ?_
  · have := measurable_gevScoreVec ξ μ σ
    have := fun i => (hX i).aemeasurable
    fun_prop
  set f : ℝ → ℝ := fun x => v 0 * gevScoreMu ξ μ σ x + v 1 * gevScoreSigma ξ μ σ x
  have hf : Measurable f := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ
    simp only [f]; fun_prop
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_lin_gevScore hσ hξ0 hξ _ _
  have hint : ∀ g : ℝ → ℝ, Measurable g →
      P[g ∘ X 0] = ∫ x, g x ∂(gevLocScaleCDF ξ μ hσ).measure :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    exact integral_lin_gevScore hσ hξ0 hξ _ _
  have hvar : Var[Y 0; P] = v ⬝ᵥ gevFisherInfoMuSigma ξ σ *ᵥ v := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this
    simp only [Function.comp_def]
    rw [this, integral_lin_gevScore_sq hσ hξ0 hξ, dotProduct_gevFisherInfoMuSigma_mulVec]
  have hZt : HasLaw (fun ω => ⟪Z ω, v⟫) (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by
    rw [hvar]
    exact hasLaw_inner_multivariateGaussian (posSemidef_gevFisherInfoMuSigma hσ hξ0 hξ) hZ v
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp [Y, f, inner_gevScoreVec]

/-- **The one-dimensional score CLT** for a combination `a ∂_μ ℓ + b ∂_σ ℓ` of the location and
scale scores: `n^{-1/2} ∑_{i<n} (a ∂_μ ℓ + b ∂_σ ℓ)(Xᵢ) ⇒ N(0, (a, b) I (a, b)ᵀ)`. -/
theorem tendstoInDistribution_lin_gevScore (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ μ hσ).measure P) (hind : iIndepFun X P) (a b : ℝ)
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (a ^ 2 * ((1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) / σ ^ 2) +
        2 * a * b * ((Gamma (2 + ξ) - (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ * σ ^ 2)) +
        b ^ 2 * ((1 - 2 * Gamma (2 + ξ) + (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) /
          (ξ ^ 2 * σ ^ 2))).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
        (a * gevScoreMu ξ μ σ (X i ω) + b * gevScoreSigma ξ μ σ (X i ω)))
      atTop Y (fun _ => P) P' := by
  set f : ℝ → ℝ := fun x => a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x
  have hf : Measurable f := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ
    simp only [f]; fun_prop
  set Z : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Z P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Z 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_lin_gevScore hσ hξ0 hξ _ _
  have hint : ∀ g : ℝ → ℝ, Measurable g →
      P[g ∘ X 0] = ∫ x, g x ∂(gevLocScaleCDF ξ μ hσ).measure :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Z 0] = 0 := by
    rw [hint f hf]
    exact integral_lin_gevScore hσ hξ0 hξ _ _
  have hvar : Var[Z 0; P] = a ^ 2 * ((1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) / σ ^ 2) +
        2 * a * b * ((Gamma (2 + ξ) - (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ * σ ^ 2)) +
        b ^ 2 * ((1 - 2 * Gamma (2 + ξ) + (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) /
          (ξ ^ 2 * σ ^ 2)) := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this
    simp only [Function.comp_def]
    rw [this, integral_lin_gevScore_sq hσ hξ0 hξ]
  rw [← hvar] at hY
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hY hmemLp hind' hident
  rw [hmean] at hclt
  simpa [Z, f] using hclt

/-- **The location score CLT** (one-parameter location model, `ξ` and `σ` known):
`n^{-1/2} ∑_{i<n} ∂_μ ℓ(Xᵢ) ⇒ N(0, (1 + ξ)² Γ(1 + 2ξ)/σ²)`. -/
theorem tendstoInDistribution_gevScoreMu (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ μ hσ).measure P) (hind : iIndepFun X P)
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0
      ((1 + ξ) ^ 2 * Gamma (1 + 2 * ξ) / σ ^ 2).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gevScoreMu ξ μ σ (X i ω))
      atTop Y (fun _ => P) P' := by
  have := tendstoInDistribution_lin_gevScore hξ hξ0 hσ hX hind 1 0 (Y := Y) (by simpa using hY)
  simpa using this

/-- **The scale score CLT** (one-parameter scale model, `ξ` and `μ` known):
`n^{-1/2} ∑_{i<n} ∂_σ ℓ(Xᵢ) ⇒ N(0, (1 - 2Γ(2 + ξ) + (1 + ξ)² Γ(1 + 2ξ))/(ξ² σ²))`. -/
theorem tendstoInDistribution_gevScoreSigma (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ μ hσ).measure P) (hind : iIndepFun X P)
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 ((1 - 2 * Gamma (2 + ξ) +
      (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)) / (ξ ^ 2 * σ ^ 2)).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gevScoreSigma ξ μ σ (X i ω))
      atTop Y (fun _ => P) P' := by
  have := tendstoInDistribution_lin_gevScore hξ hξ0 hσ hX hind 0 1 (Y := Y) (by simpa using hY)
  simpa using this

end ScoreCLT

end ExtremeValueTheory
