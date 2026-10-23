/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.GEV.Moments
import ExtremeValueTheory.ForMathlib.Analysis.SpecialFunctions.Gamma.Trigamma

/-!
# Variance and probability-weighted moments of the Gumbel law

Through the exponential representation `Λ = law of -log T`, `T` standard exponential
(`measure_gevCDF_eq_map`), the second moment of the standard Gumbel law is
`∫_0^∞ (log t)² e^{-t} dt = Γ''(1) = γ² + π² / 6` (`Real.integral_log_sq_mul_exp_neg`), so its
variance is `π² / 6` ([EKM, §3.4]; [Coles, §3.1]). We also compute the `ξ = 0` case of the
probability-weighted moments of Hosking, Wallis and Wood,
`β_r = E[X Λ(X) ^ r] = (γ + log (r + 1)) / (r + 1)`.

## Main results

* `CumulativeDistributionFunction.variance_id_smul`: `Var (A • F) = a² Var F`.
* `integrable_sq_gevCDF_zero`, `integral_sq_gevCDF_zero`: `∫ x² dΛ(x) = γ² + π² / 6`.
* `variance_id_gevCDF_zero`, `variance_id_standardGumbelCDF`: `Var Λ = π² / 6`.
* `variance_id_gevLocScaleCDF_zero`: the variance of `Λ((x - μ)/σ)` is `σ² π² / 6`.
* `integral_mul_gevFun_pow_gevCDF_zero`: `∫ x Λ(x) ^ r dΛ(x) = (γ + log (r + 1)) / (r + 1)`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §3.4 [EKM].
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §3.1 [Coles].
* J. R. M. Hosking, J. R. Wallis and E. F. Wood, *Estimation of the generalized extreme-value
  distribution by the method of probability-weighted moments*, Technometrics 27 (1985).
-/

open Filter Topology Real MeasureTheory Set ExtremeValueTheory.CumulativeDistributionFunction ProbabilityTheory

namespace ExtremeValueTheory.CumulativeDistributionFunction

/-- Variance of an affine transform: `Var (A • F) = a² Var F`, `a = A.coefs.1`. -/
theorem variance_id_smul (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    variance (fun x ↦ x) (A • F).measure = A.coefs.1 ^ 2 * variance (fun x ↦ x) F.measure := by
  rw [measure_smul_eq_map, variance_map (by fun_prop) (by fun_prop)]
  change variance (fun x ↦ A.coefs.1 * x + A.coefs.2) F.measure = _
  rw [variance_add_const (by fun_prop), variance_const_mul]

end ExtremeValueTheory.CumulativeDistributionFunction

namespace ExtremeValueTheory

/-- **Second moment of the Gumbel law**: `∫ x² dΛ(x) = γ² + π² / 6`. -/
theorem integral_sq_gevCDF_zero :
    ∫ x, x ^ 2 ∂(gevCDF 0).measure = eulerMascheroniConstant ^ 2 + π ^ 2 / 6 := by
  rw [integral_gevCDF 0 (by fun_prop), ← integral_log_sq_mul_exp_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp [gevTransform]; ring

/-- The Gumbel law has a finite second moment. -/
theorem integrable_sq_gevCDF_zero : Integrable (fun x ↦ x ^ 2) (gevCDF 0).measure := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_sq_gevCDF_zero]
  positivity

/-- **Variance of the Gumbel law** ([EKM, §3.4]; [Coles, §3.1]): `Var Λ = π² / 6`. -/
theorem variance_id_gevCDF_zero : variance (fun x ↦ x) (gevCDF 0).measure = π ^ 2 / 6 := by
  have hL2 : MemLp (fun x : ℝ ↦ x) 2 (gevCDF 0).measure :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 integrable_sq_gevCDF_zero
  rw [variance_eq_sub hL2]
  change ∫ x, x ^ 2 ∂(gevCDF 0).measure - (∫ x, x ∂(gevCDF 0).measure) ^ 2 = _
  rw [integral_sq_gevCDF_zero, integral_id_gevCDF_zero]
  ring

/-- The second moment of the standard Gumbel law `Λ` is `γ² + π² / 6`. -/
theorem integral_sq_standardGumbelCDF :
    ∫ x, x ^ 2 ∂standardGumbelCDF.measure = eulerMascheroniConstant ^ 2 + π ^ 2 / 6 := by
  rw [← gevCDF_zero, integral_sq_gevCDF_zero]

/-- The variance of the standard Gumbel law `Λ` is `π² / 6`. -/
theorem variance_id_standardGumbelCDF :
    variance (fun x ↦ x) standardGumbelCDF.measure = π ^ 2 / 6 := by
  rw [← gevCDF_zero, variance_id_gevCDF_zero]

/-- **Variance of the location-scale Gumbel law**: `Λ((x - μ)/σ)` has variance `σ² π² / 6`. -/
theorem variance_id_gevLocScaleCDF_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    variance (fun x ↦ x) (gevLocScaleCDF 0 μ hσ).measure = σ ^ 2 * π ^ 2 / 6 := by
  rw [gevLocScaleCDF, variance_id_smul, variance_id_gevCDF_zero,
    AffineIncrEquiv.coefs_fst_mkOfCoefs]
  ring

/-- **Probability-weighted moments of the Gumbel law** (the `ξ = 0` case of Hosking, Wallis and
Wood): for `r ∈ ℕ`, `β_r = ∫ x Λ(x) ^ r dΛ(x) = (γ + log (r + 1)) / (r + 1)`. -/
theorem integral_mul_gevFun_pow_gevCDF_zero (r : ℕ) :
    ∫ x, x * gevFun 0 x ^ r ∂(gevCDF 0).measure =
      (eulerMascheroniConstant + log ((r : ℝ) + 1)) / ((r : ℝ) + 1) := by
  have hr : (0 : ℝ) < r + 1 := by positivity
  have hmeas : Measurable fun x ↦ x * gevFun 0 x ^ r :=
    measurable_id.mul ((monotone_gevFun 0).measurable.pow_const r)
  set g : ℝ → ℝ := fun u ↦ log ((r : ℝ) + 1) * exp (-u) - log u * exp (-u) with hg
  have key : ∀ t ∈ Ioi (0 : ℝ),
      exp (-t) * (gevTransform 0 t * gevFun 0 (gevTransform 0 t) ^ r) = g ((r + 1) * t) := by
    intro t (ht : 0 < t)
    rw [gevFun_gevTransform 0 ht, ← exp_nat_mul, hg]
    simp only [gevTransform, ↓reduceIte]
    rw [log_mul hr.ne' ht.ne', show -(((r : ℝ) + 1) * t) = -t + r * -t by ring, exp_add]
    ring
  rw [integral_gevCDF 0 hmeas, setIntegral_congr_fun measurableSet_Ioi key,
    integral_comp_mul_left_Ioi g 0 hr, mul_zero, hg,
    integral_sub ((integrableOn_exp_neg_Ioi 0).const_mul _) integrableOn_log_mul_exp_neg,
    integral_const_mul, integral_exp_neg_Ioi_zero, smul_eq_mul,
    show ∫ t in Ioi (0 : ℝ), log t * exp (-t) = -eulerMascheroniConstant by
      rw [eulerMascheroniConstant_eq_neg_integral_log, neg_neg]]
  field_simp
  ring

/-- `β_0 = γ`: the zeroth probability-weighted moment of `Λ` is its mean. -/
example : ∫ x, x * gevFun 0 x ^ 0 ∂(gevCDF 0).measure = eulerMascheroniConstant := by
  rw [integral_mul_gevFun_pow_gevCDF_zero]; simp

end ExtremeValueTheory
