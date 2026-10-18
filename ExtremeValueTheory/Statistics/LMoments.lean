/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDLikelihood
import ExtremeValueTheory.GEV.GumbelVariance

/-!
# Probability-weighted moments and L-moments

For a probability measure `μ` on `ℝ` with distribution function `F = cdf μ`, the
**probability-weighted moments** (PWMs) of Greenwood, Landwehr, Matalas and Wallis (1979) are

  `β_r = E[X F(X) ^ r]` (`pwm μ r`) and `α_r = E[X (1 - F(X)) ^ r]` (`pwmSurv μ r`).

Hosking, Wallis and Wood (1985) use `β_r` for the GEV law, Hosking and Wallis (1987) use `α_r`
for the generalized Pareto law; the two families determine each other, e.g.
`β₁ = α₀ - α₁` and `β₂ = α₀ - 2 α₁ + α₂` (`pwm_one_eq`, `pwm_two_eq`). The first three
**L-moments** (Hosking 1990) and the **L-skewness** are

  `λ₁ = β₀`, `λ₂ = 2 β₁ - β₀`, `λ₃ = 6 β₂ - 6 β₁ + β₀`, `τ₃ = λ₃ / λ₂`.

## Conventions

The shape parameter `ξ` is the library's: the GEV law is `H_ξ(x) = exp(-(1 + ξ x)^(-1/ξ))` and
the GPD survival function is `(1 + ξ x / σ)^(-1/ξ)` (`gpdMeasure ξ σ`). Hosking's papers use
`k = -ξ` for both families; every formula below is Hosking's with `k` replaced by `-ξ`.

## Main results

* *General.* `pwm_one_eq`, `pwm_two_eq`, `lMoment2_eq`, `lMoment3_eq` (L-moments through the
  `α_r`); `pwm_map_affine`, `lMoment1_map_affine`, `lMoment2_map_affine`,
  `lMoment3_map_affine`, `lSkewness_map_affine` (behaviour under `x ↦ a x + b`, `a > 0`, when
  `F(X)` has the uniform moments `E F(X) = 1/2`, `E F(X)² = 1/3`).
* *Generalized Pareto law* (Hosking–Wallis 1987). `pwmSurv_gpdMeasure`:
  `α_r = σ / ((r + 1)(r + 1 - ξ))` for `ξ < r + 1` (note: this is the formula for the
  *survival-weighted* PWMs `α_r`, often misquoted as one for `β_r`); `pwm_gpdMeasure_zero`,
  `pwm_gpdMeasure_one`, `pwm_gpdMeasure_two`; for `ξ < 1`:
  `λ₁ = σ/(1-ξ)`, `λ₂ = σ/((1-ξ)(2-ξ))`, `λ₃ = σ(1+ξ)/((1-ξ)(2-ξ)(3-ξ))`, `τ₃ = (1+ξ)/(3-ξ)`
  (`lMoment1_gpdMeasure`, …, `lSkewness_gpdMeasure`).
* *The PWM estimating equations for the GPD.* `gpdPWMShape l₁ l₂ = 2 - l₁/l₂` and
  `gpdPWMScale l₁ l₂ = l₁ (l₁/l₂ - 1)` invert `(ξ, σ) ↦ (λ₁, λ₂)`
  (`gpdPWMShape_lMoment`, `gpdPWMScale_lMoment`). In the `α`-form of Hosking and Wallis,
  `l₂ = a₀ - 2 a₁`, so `ξ̂ = 2 - a₀/(a₀ - 2a₁)` and `σ̂ = 2 a₀ a₁/(a₀ - 2 a₁)`
  (`gpdPWMShape_pwmSurv`, `gpdPWMScale_pwmSurv`).
* *GEV law* (Hosking–Wallis–Wood 1985, Hosking 1990). `pwm_gevCDF` (from
  `integral_mul_gevFun_pow_gevCDF`): `β_r = ((r+1)^ξ Γ(1-ξ) - 1)/(ξ (r+1))`; for `ξ < 1`,
  `ξ ≠ 0`: `λ₁ = (Γ(1-ξ) - 1)/ξ`, `λ₂ = (2^ξ - 1) Γ(1-ξ)/ξ`,
  `λ₃ = (2·3^ξ - 3·2^ξ + 1) Γ(1-ξ)/ξ`, `τ₃ = (2·3^ξ - 3·2^ξ + 1)/(2^ξ - 1)`, which is Hosking's
  `τ₃ = 2(1 - 3^{-k})/(1 - 2^{-k}) - 3`. The Gumbel case: `λ₂ = log 2`,
  `τ₃ = (2 log 3 - 3 log 2)/log 2`. The location-scale law `H_{ξ,μ,σ}`:
  `λ₂ = σ (2^ξ - 1) Γ(1-ξ)/ξ`, `τ₃` unchanged (`lMoment2_gevLocScaleCDF`,
  `lSkewness_gevLocScaleCDF`, …).

## References

* J. A. Greenwood, J. M. Landwehr, N. C. Matalas and J. R. Wallis, *Probability weighted
  moments*, Water Resources Research 15 (1979).
* J. R. M. Hosking, J. R. Wallis and E. F. Wood, *Estimation of the generalized extreme-value
  distribution by the method of probability-weighted moments*, Technometrics 27 (1985).
* J. R. M. Hosking and J. R. Wallis, *Parameter and quantile estimation for the generalized
  Pareto distribution*, Technometrics 29 (1987).
* J. R. M. Hosking, *L-moments: analysis and estimation of distributions using linear
  combinations of order statistics*, J. R. Statist. Soc. B 52 (1990).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### Definitions -/

section Defs

variable (μ : Measure ℝ)

/-- The **probability-weighted moment** `β_r = E[X F(X) ^ r]`, `F = cdf μ`. -/
noncomputable def pwm (r : ℕ) : ℝ := ∫ x, x * cdf μ x ^ r ∂μ

/-- The **survival-weighted probability-weighted moment** `α_r = E[X (1 - F(X)) ^ r]`. -/
noncomputable def pwmSurv (r : ℕ) : ℝ := ∫ x, x * (1 - cdf μ x) ^ r ∂μ

/-- The first **L-moment** `λ₁ = β₀` (the mean). -/
noncomputable def lMoment1 : ℝ := pwm μ 0

/-- The second **L-moment** `λ₂ = 2 β₁ - β₀` (half the Gini mean difference). -/
noncomputable def lMoment2 : ℝ := 2 * pwm μ 1 - pwm μ 0

/-- The third **L-moment** `λ₃ = 6 β₂ - 6 β₁ + β₀`. -/
noncomputable def lMoment3 : ℝ := 6 * pwm μ 2 - 6 * pwm μ 1 + pwm μ 0

/-- The **L-skewness** `τ₃ = λ₃ / λ₂`. -/
noncomputable def lSkewness : ℝ := lMoment3 μ / lMoment2 μ

end Defs

/-! ### General identities -/

section General

variable {μ : Measure ℝ}

lemma measurable_cdf_apply (μ : Measure ℝ) : Measurable (cdf μ) := (cdf μ).mono.measurable

@[simp] lemma pwm_zero : pwm μ 0 = ∫ x, x ∂μ := by simp [pwm]

@[simp] lemma pwmSurv_zero : pwmSurv μ 0 = ∫ x, x ∂μ := by simp [pwmSurv]

lemma pwmSurv_zero_eq_pwm_zero : pwmSurv μ 0 = pwm μ 0 := by simp

lemma integrable_mul_cdf_pow (h : Integrable (fun x ↦ x) μ) (r : ℕ) :
    Integrable (fun x ↦ x * cdf μ x ^ r) μ :=
  h.mul_bdd (c := 1) ((measurable_cdf_apply μ).pow_const r).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg μ x)]
      exact pow_le_one₀ (cdf_nonneg μ x) (cdf_le_one μ x))

lemma integrable_mul_one_sub_cdf_pow (h : Integrable (fun x ↦ x) μ) (r : ℕ) :
    Integrable (fun x ↦ x * (1 - cdf μ x) ^ r) μ :=
  h.mul_bdd (c := 1) ((measurable_const.sub (measurable_cdf_apply μ)).pow_const r).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      have h1 := cdf_nonneg μ x
      have h2 := cdf_le_one μ x
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact pow_le_one₀ (by linarith) (by linarith))

/-- `β₁ = α₀ - α₁`. -/
theorem pwm_one_eq (h : Integrable (fun x ↦ x) μ) : pwm μ 1 = pwmSurv μ 0 - pwmSurv μ 1 := by
  simp only [pwm, pwmSurv, pow_zero, mul_one, pow_one]
  rw [← integral_sub h (by simpa using integrable_mul_one_sub_cdf_pow h 1)]
  congr 1; funext x; ring

/-- `β₂ = α₀ - 2 α₁ + α₂`. -/
theorem pwm_two_eq (h : Integrable (fun x ↦ x) μ) :
    pwm μ 2 = pwmSurv μ 0 - 2 * pwmSurv μ 1 + pwmSurv μ 2 := by
  simp only [pwm, pwmSurv, pow_zero, mul_one, pow_one]
  have h1 := (by simpa using integrable_mul_one_sub_cdf_pow h 1 :
    Integrable (fun x ↦ x * (1 - cdf μ x)) μ)
  have e : (fun x ↦ x * cdf μ x ^ 2) =
      fun x ↦ (x - 2 * (x * (1 - cdf μ x))) + x * (1 - cdf μ x) ^ 2 := by funext x; ring
  have h2 : Integrable (fun x ↦ x - 2 * (x * (1 - cdf μ x))) μ := h.sub (h1.const_mul 2)
  rw [e, integral_add h2 (integrable_mul_one_sub_cdf_pow h 2),
    integral_sub h (h1.const_mul 2), integral_const_mul]

/-- `λ₂ = α₀ - 2 α₁`. -/
theorem lMoment2_eq (h : Integrable (fun x ↦ x) μ) :
    lMoment2 μ = pwmSurv μ 0 - 2 * pwmSurv μ 1 := by
  rw [lMoment2, pwm_one_eq h, ← pwmSurv_zero_eq_pwm_zero]; ring

/-- `λ₃ = α₀ - 6 α₁ + 6 α₂`. -/
theorem lMoment3_eq (h : Integrable (fun x ↦ x) μ) :
    lMoment3 μ = pwmSurv μ 0 - 6 * pwmSurv μ 1 + 6 * pwmSurv μ 2 := by
  rw [lMoment3, pwm_one_eq h, pwm_two_eq h, ← pwmSurv_zero_eq_pwm_zero]; ring

variable [IsProbabilityMeasure μ]

/-- The distribution function of the image of `μ` under `x ↦ a x + b`, `a > 0`. -/
lemma cdf_map_affine {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    cdf (μ.map fun y ↦ a * y + b) (a * x + b) = cdf μ x := by
  have hm : Measurable fun y : ℝ ↦ a * y + b := by fun_prop
  have : IsProbabilityMeasure (μ.map fun y ↦ a * y + b) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
  congr 1
  ext y
  simp only [mem_preimage, mem_Iic]
  constructor
  · intro hy; nlinarith
  · intro hy; nlinarith

/-- **PWMs under an affine map** `x ↦ a x + b`, `a > 0`:
`β_r(a X + b) = a β_r(X) + b E[F(X) ^ r]`. -/
theorem pwm_map_affine (h : Integrable (fun x ↦ x) μ) {a : ℝ} (ha : 0 < a) (b : ℝ) (r : ℕ) :
    pwm (μ.map fun y ↦ a * y + b) r = a * pwm μ r + b * ∫ x, cdf μ x ^ r ∂μ := by
  have hm : Measurable fun y : ℝ ↦ a * y + b := by fun_prop
  have hF : Integrable (fun x ↦ cdf μ x ^ r) μ :=
    (integrable_const (1 : ℝ)).mono ((measurable_cdf_apply μ).pow_const r).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg μ x), norm_one]
        exact pow_le_one₀ (cdf_nonneg μ x) (cdf_le_one μ x))
  rw [pwm, integral_map (f := fun x ↦ x * cdf (μ.map fun y ↦ a * y + b) x ^ r) hm.aemeasurable
    (measurable_id.mul ((measurable_cdf_apply _).pow_const r)).aestronglyMeasurable]
  simp_rw [cdf_map_affine ha b]
  rw [pwm, ← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_mul_cdf_pow h r).const_mul a) (hF.const_mul b)]
  congr 1; funext x; ring

section Affine

variable (h : Integrable (fun x ↦ x) μ) {a : ℝ} (ha : 0 < a) (b : ℝ)
  (hU1 : ∫ x, cdf μ x ∂μ = 1 / 2) (hU2 : ∫ x, cdf μ x ^ 2 ∂μ = 1 / 3)
include h ha

theorem lMoment1_map_affine : lMoment1 (μ.map fun y ↦ a * y + b) = a * lMoment1 μ + b := by
  simp [lMoment1, pwm_map_affine h ha b 0]

include hU1 in
theorem lMoment2_map_affine : lMoment2 (μ.map fun y ↦ a * y + b) = a * lMoment2 μ := by
  simp only [lMoment2, pwm_map_affine h ha b, pow_one, pow_zero, hU1, integral_const,
    probReal_univ, smul_eq_mul, mul_one]
  ring

include hU1 hU2 in
theorem lMoment3_map_affine : lMoment3 (μ.map fun y ↦ a * y + b) = a * lMoment3 μ := by
  simp only [lMoment3, pwm_map_affine h ha b, pow_one, pow_zero, hU1, hU2, integral_const,
    probReal_univ, smul_eq_mul, mul_one]
  ring

include hU1 hU2 in
/-- The L-skewness is invariant under increasing affine maps. -/
theorem lSkewness_map_affine : lSkewness (μ.map fun y ↦ a * y + b) = lSkewness μ := by
  rw [lSkewness, lSkewness, lMoment2_map_affine h ha b hU1, lMoment3_map_affine h ha b hU1 hU2,
    mul_div_mul_left _ _ ha.ne']

end Affine

end General

/-! ### The generalized Pareto law -/

section GPD

variable {ξ σ : ℝ}

/-- The distribution function of `GPD(ξ, σ)` is `gpdCDF ξ σ`. -/
lemma cdf_gpdMeasure (hσ : 0 < σ) (x : ℝ) : cdf (gpdMeasure ξ σ) x = gpdCDF ξ σ x := by
  rw [cdf_eq_real, measureReal_def, gpdMeasure_Iic hσ, ENNReal.toReal_ofReal]
  have := gpdSurvival'_le_one (ξ := ξ) hσ (le_max_right x 0)
  rw [gpdCDF]; linarith

/-- On the exponential scale the GPD survival function is explicit:
`Ḡ_{ξ,σ}(T(t)) = e^{-t}`. -/
lemma gpdSurvival'_gpdTransform (hσ : 0 < σ) (t : ℝ) :
    gpdSurvival' ξ σ (gpdTransform ξ σ t) = exp (-t) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [gpdSurvival'_zero_left, gpdTransform, ↓reduceIte]
    congr 1; field_simp
  · rw [gpdSurvival', ite_eq_right_iff.mpr (fun h ↦ absurd h hξ), one_add_mul_gpdTransform hσ hξ, max_eq_left (exp_pos _).le,
      ← exp_mul]
    congr 1; field_simp

/-- `1 - F(T(t)) = e^{-t}` for `t > 0`. -/
lemma one_sub_cdf_gpdMeasure_gpdTransform (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    1 - cdf (gpdMeasure ξ σ) (gpdTransform ξ σ t) = exp (-t) := by
  rw [cdf_gpdMeasure hσ, gpdCDF, max_eq_left (gpdTransform_pos hσ ht).le,
    gpdSurvival'_gpdTransform hσ]
  ring

private lemma gpd_alpha_integrand (hσ : 0 < σ) (r : ℕ) {t : ℝ} (ht : 0 < t) :
    exp (-t) * (gpdTransform ξ σ t * (1 - cdf (gpdMeasure ξ σ) (gpdTransform ξ σ t)) ^ r) =
      if ξ = 0 then σ * (t ^ ((2 : ℝ) - 1) * exp (-(((r : ℝ) + 1) * t)))
      else σ / ξ * (exp (-((r : ℝ) + 1 - ξ) * t) - exp (-((r : ℝ) + 1) * t)) := by
  rw [one_sub_cdf_gpdMeasure_gpdTransform hσ ht, ← exp_nat_mul]
  split_ifs with hξ
  · subst hξ
    simp only [gpdTransform, ↓reduceIte]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, rpow_one]
    rw [show -(((r : ℝ) + 1) * t) = -t + r * -t by ring, exp_add]
    ring
  · simp only [gpdTransform, hξ, ↓reduceIte]
    rw [show -((r : ℝ) + 1 - ξ) * t = -t + r * -t + ξ * t by ring,
      show -((r : ℝ) + 1) * t = -t + r * -t by ring, exp_add, exp_add]
    field_simp

private lemma gpd_alpha_integrableOn (hσ : 0 < σ) {r : ℕ} (hξ : ξ < r + 1) :
    IntegrableOn (fun t ↦ exp (-t) *
      (gpdTransform ξ σ t * (1 - cdf (gpdMeasure ξ σ) (gpdTransform ξ σ t)) ^ r)) (Ioi 0) := by
  have hr : (0 : ℝ) < r + 1 := by positivity
  refine IntegrableOn.congr_fun ?_ (fun t ht ↦ (gpd_alpha_integrand hσ r ht).symm)
    measurableSet_Ioi
  split_ifs with h0
  · refine Integrable.const_mul ?_ σ
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 : ℝ) - 1) (p := 1) (b := (r : ℝ) + 1)
      (by norm_num) one_pos hr).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    simp only [rpow_one, neg_mul]
  · refine Integrable.const_mul (Integrable.sub ?_ ?_) _
    · exact integrableOn_exp_mul_Ioi (by linarith) 0
    · exact integrableOn_exp_mul_Ioi (by linarith) 0

private lemma measurable_pwmSurv_integrand (μ : Measure ℝ) (r : ℕ) :
    Measurable fun x ↦ x * (1 - cdf μ x) ^ r :=
  measurable_id.mul ((measurable_const.sub (measurable_cdf_apply μ)).pow_const r)

/-- Under `GPD(ξ, σ)` the weighted variable `X (1 - F(X)) ^ r` is integrable when `ξ < r + 1`. -/
theorem integrable_pwmSurv_gpdMeasure (hσ : 0 < σ) {r : ℕ} (hξ : ξ < r + 1) :
    Integrable (fun x ↦ x * (1 - cdf (gpdMeasure ξ σ) x) ^ r) (gpdMeasure ξ σ) := by
  rw [integrable_gpdMeasure_iff (measurable_pwmSurv_integrand _ r),
    integrable_expMeasure_iff]
  exact gpd_alpha_integrableOn hσ hξ

/-- For `ξ < 1` the generalized Pareto law has a finite mean. -/
theorem integrable_id_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) :
    Integrable (fun x ↦ x) (gpdMeasure ξ σ) := by
  simpa using integrable_pwmSurv_gpdMeasure (r := 0) hσ (by simpa using hξ)

/-- **Survival-weighted PWMs of the GPD** (Hosking and Wallis 1987, (5)): for `ξ < r + 1`,
`α_r = E[X (1 - F(X)) ^ r] = σ / ((r + 1)(r + 1 - ξ))`. -/
theorem pwmSurv_gpdMeasure (hσ : 0 < σ) {r : ℕ} (hξ : ξ < r + 1) :
    pwmSurv (gpdMeasure ξ σ) r = σ / (((r : ℝ) + 1) * ((r : ℝ) + 1 - ξ)) := by
  have hr : (0 : ℝ) < r + 1 := by positivity
  have hr' : (0 : ℝ) < r + 1 - ξ := by linarith
  rw [pwmSurv, integral_gpdMeasure (measurable_pwmSurv_integrand _ r), integral_expMeasure,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ gpd_alpha_integrand hσ r ht)]
  split_ifs with h0
  · rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi two_pos hr, Gamma_two, h0,
      rpow_two, sub_zero]
    field_simp
  · rw [integral_const_mul, integral_sub (integrableOn_exp_mul_Ioi (by linarith) 0)
      (integrableOn_exp_mul_Ioi (by linarith) 0), integral_exp_neg_mul_Ioi hr',
      integral_exp_neg_mul_Ioi hr]
    field_simp
    ring

/-- The mean of `GPD(ξ, σ)`, `ξ < 1`: `β₀ = σ / (1 - ξ)`. -/
theorem pwm_gpdMeasure_zero (hσ : 0 < σ) (hξ : ξ < 1) :
    pwm (gpdMeasure ξ σ) 0 = σ / (1 - ξ) := by
  rw [← pwmSurv_zero_eq_pwm_zero, pwmSurv_gpdMeasure hσ (by simpa using hξ)]
  simp

/-- `β₁ = σ (3 - ξ) / (2 (1 - ξ)(2 - ξ))` for `GPD(ξ, σ)`, `ξ < 1`. -/
theorem pwm_gpdMeasure_one (hσ : 0 < σ) (hξ : ξ < 1) :
    pwm (gpdMeasure ξ σ) 1 = σ * (3 - ξ) / (2 * (1 - ξ) * (2 - ξ)) := by
  rw [pwm_one_eq (integrable_id_gpdMeasure hσ hξ), pwmSurv_gpdMeasure hσ (by simpa using hξ),
    pwmSurv_gpdMeasure hσ (by push_cast; linarith)]
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 2 - ξ ≠ 0 := by linarith
  norm_num
  field_simp
  ring

/-- `β₂ = σ (11 - 6ξ + ξ²) / (3 (1 - ξ)(2 - ξ)(3 - ξ))` for `GPD(ξ, σ)`, `ξ < 1`. -/
theorem pwm_gpdMeasure_two (hσ : 0 < σ) (hξ : ξ < 1) :
    pwm (gpdMeasure ξ σ) 2 = σ * (11 - 6 * ξ + ξ ^ 2) / (3 * (1 - ξ) * (2 - ξ) * (3 - ξ)) := by
  rw [pwm_two_eq (integrable_id_gpdMeasure hσ hξ), pwmSurv_gpdMeasure hσ (by simpa using hξ),
    pwmSurv_gpdMeasure hσ (by push_cast; linarith),
    pwmSurv_gpdMeasure hσ (by push_cast; linarith)]
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 2 - ξ ≠ 0 := by linarith
  have h3 : 3 - ξ ≠ 0 := by linarith
  norm_num
  field_simp
  ring

/-- **First L-moment of the GPD**: `λ₁ = σ / (1 - ξ)`. -/
theorem lMoment1_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) :
    lMoment1 (gpdMeasure ξ σ) = σ / (1 - ξ) := pwm_gpdMeasure_zero hσ hξ

/-- **Second L-moment of the GPD** (Hosking 1990, Table 1 with `k = -ξ`):
`λ₂ = σ / ((1 - ξ)(2 - ξ))`. -/
theorem lMoment2_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) :
    lMoment2 (gpdMeasure ξ σ) = σ / ((1 - ξ) * (2 - ξ)) := by
  rw [lMoment2_eq (integrable_id_gpdMeasure hσ hξ), pwmSurv_gpdMeasure hσ (by simpa using hξ),
    pwmSurv_gpdMeasure hσ (by push_cast; linarith)]
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 2 - ξ ≠ 0 := by linarith
  norm_num
  field_simp
  ring

/-- **Third L-moment of the GPD**: `λ₃ = σ (1 + ξ) / ((1 - ξ)(2 - ξ)(3 - ξ))`. -/
theorem lMoment3_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) :
    lMoment3 (gpdMeasure ξ σ) = σ * (1 + ξ) / ((1 - ξ) * (2 - ξ) * (3 - ξ)) := by
  rw [lMoment3_eq (integrable_id_gpdMeasure hσ hξ), pwmSurv_gpdMeasure hσ (by simpa using hξ),
    pwmSurv_gpdMeasure hσ (by push_cast; linarith),
    pwmSurv_gpdMeasure hσ (by push_cast; linarith)]
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 2 - ξ ≠ 0 := by linarith
  have h3 : 3 - ξ ≠ 0 := by linarith
  norm_num
  field_simp
  ring

/-- **L-skewness of the GPD** (Hosking 1990, Table 1: `τ₃ = (1 - k)/(3 + k)`, `k = -ξ`):
`τ₃ = (1 + ξ) / (3 - ξ)`. -/
theorem lSkewness_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) :
    lSkewness (gpdMeasure ξ σ) = (1 + ξ) / (3 - ξ) := by
  rw [lSkewness, lMoment2_gpdMeasure hσ hξ, lMoment3_gpdMeasure hσ hξ]
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 2 - ξ ≠ 0 := by linarith
  have h3 : 3 - ξ ≠ 0 := by linarith
  field_simp

/-- The **PWM shape estimating function** of Hosking and Wallis (1987):
`ξ = 2 - λ₁ / λ₂`. -/
noncomputable def gpdPWMShape (l₁ l₂ : ℝ) : ℝ := 2 - l₁ / l₂

/-- The **PWM scale estimating function** of Hosking and Wallis (1987):
`σ = λ₁ (λ₁ / λ₂ - 1)`. -/
noncomputable def gpdPWMScale (l₁ l₂ : ℝ) : ℝ := l₁ * (l₁ / l₂ - 1)

/-- The PWM equations recover the GPD shape: `2 - λ₁ / λ₂ = ξ`. -/
theorem gpdPWMShape_lMoment (hσ : 0 < σ) (hξ : ξ < 1) :
    gpdPWMShape (lMoment1 (gpdMeasure ξ σ)) (lMoment2 (gpdMeasure ξ σ)) = ξ := by
  rw [gpdPWMShape, lMoment1_gpdMeasure hσ hξ, lMoment2_gpdMeasure hσ hξ]
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 2 - ξ ≠ 0 := by linarith
  field_simp
  ring

/-- The PWM equations recover the GPD scale: `λ₁ (λ₁ / λ₂ - 1) = σ`. -/
theorem gpdPWMScale_lMoment (hσ : 0 < σ) (hξ : ξ < 1) :
    gpdPWMScale (lMoment1 (gpdMeasure ξ σ)) (lMoment2 (gpdMeasure ξ σ)) = σ := by
  rw [gpdPWMScale, lMoment1_gpdMeasure hσ hξ, lMoment2_gpdMeasure hσ hξ]
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 2 - ξ ≠ 0 := by linarith
  field_simp
  ring

/-- The Hosking–Wallis form of the shape equation: `ξ̂ = 2 - a₀ / (a₀ - 2 a₁)`. -/
theorem gpdPWMShape_pwmSurv (a₀ a₁ : ℝ) :
    gpdPWMShape a₀ (a₀ - 2 * a₁) = 2 - a₀ / (a₀ - 2 * a₁) := rfl

/-- The Hosking–Wallis form of the scale equation: `σ̂ = 2 a₀ a₁ / (a₀ - 2 a₁)`. -/
theorem gpdPWMScale_pwmSurv {a₀ a₁ : ℝ} (h : a₀ - 2 * a₁ ≠ 0) :
    gpdPWMScale a₀ (a₀ - 2 * a₁) = 2 * a₀ * a₁ / (a₀ - 2 * a₁) := by
  rw [gpdPWMScale]
  field_simp
  ring

end GPD

/-! ### The GEV law -/

section GEV

open CumulativeDistributionFunction

variable {ξ : ℝ}

/-- The distribution function of the law of `H_ξ` is `H_ξ`. -/
lemma cdf_gevCDF_measure (ξ x : ℝ) : cdf (gevCDF ξ).measure x = gevFun ξ x := by
  rw [cdf_measure_stieltjesFunction _ (gevCDF ξ).tendsto_atBot (gevCDF ξ).tendsto_atTop]
  exact gevCDF_apply ξ x

/-- **PWMs of the GEV law** (Hosking, Wallis and Wood 1985): for `ξ < 1`, `ξ ≠ 0`,
`β_r = ((r + 1) ^ ξ Γ(1 - ξ) - 1) / (ξ (r + 1))`. -/
theorem pwm_gevCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) (r : ℕ) :
    pwm (gevCDF ξ).measure r = (((r : ℝ) + 1) ^ ξ * Gamma (1 - ξ) - 1) / (ξ * ((r : ℝ) + 1)) := by
  simp_rw [pwm, cdf_gevCDF_measure]
  exact integral_mul_gevFun_pow_gevCDF hξ h0 r

/-- **PWMs of the Gumbel law**: `β_r = (γ + log (r + 1)) / (r + 1)`. -/
theorem pwm_gevCDF_zero (r : ℕ) :
    pwm (gevCDF 0).measure r = (eulerMascheroniConstant + log ((r : ℝ) + 1)) / ((r : ℝ) + 1) := by
  simp_rw [pwm, cdf_gevCDF_measure]
  exact integral_mul_gevFun_pow_gevCDF_zero r

/-- `F(X)` is uniform under `H_ξ`: `E[H_ξ(X) ^ r] = 1 / (r + 1)`. -/
theorem integral_cdf_pow_gevCDF (ξ : ℝ) (r : ℕ) :
    ∫ x, cdf (gevCDF ξ).measure x ^ r ∂(gevCDF ξ).measure = 1 / ((r : ℝ) + 1) := by
  have hr : (0 : ℝ) < r + 1 := by positivity
  simp_rw [cdf_gevCDF_measure]
  rw [integral_gevCDF ξ ((monotone_gevFun ξ).measurable.pow_const r),
    setIntegral_congr_fun measurableSet_Ioi (g := fun t ↦ exp (-((r : ℝ) + 1) * t))
      (fun t ht ↦ by
        simp only
        rw [gevFun_gevTransform ξ ht, ← exp_nat_mul, ← exp_add]
        congr 1; ring),
    integral_exp_neg_mul_Ioi hr]

private lemma gev_casts : ((1 : ℕ) : ℝ) + 1 = 2 ∧ ((2 : ℕ) : ℝ) + 1 = 3 ∧
    ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num

/-- **First L-moment of the GEV law**: `λ₁ = (Γ(1 - ξ) - 1) / ξ`. -/
theorem lMoment1_gevCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lMoment1 (gevCDF ξ).measure = (Gamma (1 - ξ) - 1) / ξ := by
  rw [lMoment1, pwm_gevCDF hξ h0]
  simp

/-- **Second L-moment of the GEV law** (Hosking 1990, Table 1:
`λ₂ = α (1 - 2^{-k}) Γ(1 + k) / k` with `k = -ξ`): `λ₂ = (2^ξ - 1) Γ(1 - ξ) / ξ`. -/
theorem lMoment2_gevCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lMoment2 (gevCDF ξ).measure = (2 ^ ξ - 1) * Gamma (1 - ξ) / ξ := by
  rw [lMoment2, pwm_gevCDF hξ h0, pwm_gevCDF hξ h0, gev_casts.1, gev_casts.2.2]
  simp only [one_rpow, one_mul, mul_one]
  field_simp
  ring

/-- **Third L-moment of the GEV law**: `λ₃ = (2·3^ξ - 3·2^ξ + 1) Γ(1 - ξ) / ξ`. -/
theorem lMoment3_gevCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lMoment3 (gevCDF ξ).measure = (2 * 3 ^ ξ - 3 * 2 ^ ξ + 1) * Gamma (1 - ξ) / ξ := by
  rw [lMoment3, pwm_gevCDF hξ h0, pwm_gevCDF hξ h0, pwm_gevCDF hξ h0, gev_casts.1,
    gev_casts.2.1, gev_casts.2.2]
  simp only [one_rpow, one_mul, mul_one]
  field_simp
  ring

lemma two_rpow_sub_one_ne_zero (h0 : ξ ≠ 0) : (2 : ℝ) ^ ξ - 1 ≠ 0 := by
  intro h
  have h2 := congrArg log (show (2 : ℝ) ^ ξ = 1 by linarith)
  rw [log_rpow two_pos, log_one] at h2
  exact h0 ((mul_eq_zero.1 h2).resolve_right (log_pos one_lt_two).ne')

/-- **L-skewness of the GEV law** (Hosking 1990, Table 1:
`τ₃ = 2 (1 - 3^{-k}) / (1 - 2^{-k}) - 3`, `k = -ξ`):
`τ₃ = (2·3^ξ - 3·2^ξ + 1) / (2^ξ - 1)`. -/
theorem lSkewness_gevCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lSkewness (gevCDF ξ).measure = (2 * 3 ^ ξ - 3 * 2 ^ ξ + 1) / (2 ^ ξ - 1) := by
  rw [lSkewness, lMoment2_gevCDF hξ h0, lMoment3_gevCDF hξ h0]
  have hG : Gamma (1 - ξ) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have h2 := two_rpow_sub_one_ne_zero h0
  field_simp

/-- Hosking's form of the GEV L-skewness, `k = -ξ`. -/
theorem lSkewness_gevCDF_hosking (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lSkewness (gevCDF ξ).measure =
      2 * (1 - 3 ^ (-(-ξ))) / (1 - 2 ^ (-(-ξ))) - 3 := by
  rw [lSkewness_gevCDF hξ h0, neg_neg]
  have h2 := two_rpow_sub_one_ne_zero h0
  have h2' : 1 - (2 : ℝ) ^ ξ ≠ 0 := fun h ↦ h2 (by linarith)
  field_simp
  ring

/-- **L-moments of the Gumbel law**: `λ₁ = γ`. -/
theorem lMoment1_gevCDF_zero : lMoment1 (gevCDF 0).measure = eulerMascheroniConstant := by
  rw [lMoment1, pwm_gevCDF_zero]; simp

/-- **L-moments of the Gumbel law**: `λ₂ = log 2`. -/
theorem lMoment2_gevCDF_zero : lMoment2 (gevCDF 0).measure = log 2 := by
  rw [lMoment2, pwm_gevCDF_zero, pwm_gevCDF_zero, gev_casts.1, gev_casts.2.2]
  simp only [log_one, add_zero, div_one]
  field_simp
  ring

/-- **L-moments of the Gumbel law**: `λ₃ = 2 log 3 - 3 log 2`. -/
theorem lMoment3_gevCDF_zero : lMoment3 (gevCDF 0).measure = 2 * log 3 - 3 * log 2 := by
  rw [lMoment3, pwm_gevCDF_zero, pwm_gevCDF_zero, pwm_gevCDF_zero, gev_casts.1, gev_casts.2.1,
    gev_casts.2.2]
  simp only [log_one, add_zero, div_one]
  field_simp
  ring

/-- **L-skewness of the Gumbel law**: `τ₃ = (2 log 3 - 3 log 2) / log 2 ≈ 0.1699`. -/
theorem lSkewness_gevCDF_zero :
    lSkewness (gevCDF 0).measure = (2 * log 3 - 3 * log 2) / log 2 := by
  rw [lSkewness, lMoment2_gevCDF_zero, lMoment3_gevCDF_zero]

/-- The law of `H_{ξ,μ,σ}` is the image of `H_ξ` under `x ↦ σ x + μ`. -/
lemma gevLocScaleCDF_measure (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (gevLocScaleCDF ξ μ hσ).measure = (gevCDF ξ).measure.map fun x ↦ σ * x + μ := by
  rw [gevLocScaleCDF, measure_smul_eq_map, AffineIncrEquiv.coefs_fst_mkOfCoefs,
    AffineIncrEquiv.coefs_snd_mkOfCoefs]

section LocScale

private lemma gev_hU1 (ξ : ℝ) : ∫ x, cdf (gevCDF ξ).measure x ∂(gevCDF ξ).measure = 1 / 2 := by
  have := integral_cdf_pow_gevCDF ξ 1
  norm_num at this ⊢; exact this

private lemma gev_hU2 (ξ : ℝ) :
    ∫ x, cdf (gevCDF ξ).measure x ^ 2 ∂(gevCDF ξ).measure = 1 / 3 := by
  have := integral_cdf_pow_gevCDF ξ 2
  norm_num at this ⊢; exact this

private lemma gev_integrable (hξ : ξ < 1) : Integrable (fun x ↦ x) (gevCDF ξ).measure :=
  integrable_id_gevCDF hξ

variable (μ : ℝ) {σ : ℝ} (hσ : 0 < σ)
include hσ

/-- `λ₂` of the location-scale GEV law: `λ₂ = σ (2^ξ - 1) Γ(1 - ξ) / ξ`. -/
theorem lMoment2_gevLocScaleCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lMoment2 (gevLocScaleCDF ξ μ hσ).measure = σ * ((2 ^ ξ - 1) * Gamma (1 - ξ) / ξ) := by
  rw [gevLocScaleCDF_measure, lMoment2_map_affine (gev_integrable hξ) hσ μ (gev_hU1 ξ),
    lMoment2_gevCDF hξ h0]

/-- `λ₃` of the location-scale GEV law. -/
theorem lMoment3_gevLocScaleCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lMoment3 (gevLocScaleCDF ξ μ hσ).measure =
      σ * ((2 * 3 ^ ξ - 3 * 2 ^ ξ + 1) * Gamma (1 - ξ) / ξ) := by
  rw [gevLocScaleCDF_measure, lMoment3_map_affine (gev_integrable hξ) hσ μ (gev_hU1 ξ)
    (gev_hU2 ξ), lMoment3_gevCDF hξ h0]

/-- `τ₃` of the location-scale GEV law does not depend on `(μ, σ)`. -/
theorem lSkewness_gevLocScaleCDF (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    lSkewness (gevLocScaleCDF ξ μ hσ).measure = (2 * 3 ^ ξ - 3 * 2 ^ ξ + 1) / (2 ^ ξ - 1) := by
  rw [gevLocScaleCDF_measure, lSkewness_map_affine (gev_integrable hξ) hσ μ (gev_hU1 ξ)
    (gev_hU2 ξ), lSkewness_gevCDF hξ h0]

/-- `λ₂` of the location-scale Gumbel law: `λ₂ = σ log 2`. -/
theorem lMoment2_gevLocScaleCDF_zero :
    lMoment2 (gevLocScaleCDF 0 μ hσ).measure = σ * log 2 := by
  rw [gevLocScaleCDF_measure, lMoment2_map_affine (gev_integrable one_pos) hσ μ (gev_hU1 0),
    lMoment2_gevCDF_zero]

/-- `τ₃` of the location-scale Gumbel law. -/
theorem lSkewness_gevLocScaleCDF_zero :
    lSkewness (gevLocScaleCDF 0 μ hσ).measure = (2 * log 3 - 3 * log 2) / log 2 := by
  rw [gevLocScaleCDF_measure, lSkewness_map_affine (gev_integrable one_pos) hσ μ (gev_hU1 0)
    (gev_hU2 0), lSkewness_gevCDF_zero]

end LocScale

end GEV

end ExtremeValueTheory
