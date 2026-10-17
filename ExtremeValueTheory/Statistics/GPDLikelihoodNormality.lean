/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDLikelihood

/-!
# Asymptotic normality of the GPD scale MLE for a known shape

Let `X₀, X₁, …` be iid `GPD(ξ, σ₀)` with known shape `-1/2 < ξ`, `ξ ≠ 0`, and let `σ̂ₙ` be the
maximum likelihood estimator of the scale, i.e. the root of the likelihood equation
`(1 + ξ) ∑_{i<n} Xᵢ / (σ̂ₙ + ξ Xᵢ) = n` (`ExtremeValueTheory.ae_existsUnique_gpdScaleMLE`). Then

  `√n (σ̂ₙ - σ₀) ⇒ N(0, I(σ₀)⁻¹)`, `I(σ₀) = 1 / (σ₀² (1 + 2ξ))`,

where `I(σ)` is the Fisher information of the scale: the score of one observation is
`σ⁻¹ ψ_σ(x)` with `ψ_σ(x) = (1 + ξ) x / (σ + ξ x) - 1`, and
`E[ψ_{σ₀}(X)²] = 1/(1 + 2ξ)`, `E[∂_σ ψ_σ(X)]|_{σ₀} = -1/(σ₀ (1 + 2ξ))`.

## Main results

* `ExtremeValueTheory.integral_gpdScorePsi`, `ExtremeValueTheory.integral_gpdScorePsi_sq`: the
  score has mean `0` and variance `1/(1 + 2ξ)` (finite exactly when `ξ > -1/2`).
* `ExtremeValueTheory.integral_gpdScoreDeriv`: `E[X / (σ₀ + ξ X)²] = 1/(σ₀ (1 + ξ)(1 + 2ξ))`.
* `ExtremeValueTheory.tendstoInDistribution_gpdScaleMLE`: **asymptotic normality**.

## Proof

Write `Fₙ(σ) = n⁻¹ ∑ ψ_σ(Xᵢ)`. At a root `σ̂ₙ` the exact (mean value) identity
`Fₙ(σ₀) = (σ̂ₙ - σ₀) Rₙ`, `Rₙ = (1 + ξ) n⁻¹ ∑ Xᵢ / ((σ₀ + ξ Xᵢ)(σ̂ₙ + ξ Xᵢ))`, gives
`√n (σ̂ₙ - σ₀) = √n Fₙ(σ₀) / Rₙ`. The numerator converges in distribution to `N(0, 1/(1 + 2ξ))`
by the central limit theorem, and `Rₙ → c = 1/(σ₀ (1 + 2ξ))` in probability; Slutsky's theorem
concludes, since `(1/(1 + 2ξ)) / c² = σ₀² (1 + 2ξ)`.

For `Rₙ → c`: on `{σ̂ₙ ≥ σ₀}`, `Rₙ` is squeezed by monotonicity between empirical means at
`σ₀ + δ` and `σ₀`, which converge almost surely by the strong law (the strong consistency of
`σ̂ₙ` is `ae_tendsto_gpdScaleMLE`). On `{σ̂ₙ < σ₀}` (where for `ξ < 0` the criterion is not
integrable below `σ₀`), the identity bounds `d = σ₀ - σ̂ₙ ≤ |Fₙ(σ₀)| / ((1 + ξ) Qₙ)` with
`Qₙ = n⁻¹ ∑ Xᵢ/(σ₀ + ξ Xᵢ)²`, hence `d / (σ₀ + ξ Xᵢ) ≤ ρₙ = |Fₙ(σ₀)| Mₙ / ((1 + ξ) Qₙ)` with
`Mₙ = max_{i<n} 1/(σ₀ + ξ Xᵢ)`, and `0 ≤ Rₙ - (1 + ξ) Qₙ ≤ 2 (1 + ξ) Qₙ ρₙ` when `ρₙ < 1/2`.
Here `√n Fₙ(σ₀)` is bounded in probability (Chebyshev), and `Mₙ / √n → 0` in probability: this is
trivial for `ξ > 0` (`Mₙ ≤ 1/σ₀`), and for `ξ < 0` it follows from
`P(σ₀ + ξ X < u) = (u/σ₀)^{-1/ξ}` and `-1/ξ > 2`, i.e. from `ξ > -1/2` once more.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §5.3.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtremeValueTheory

/-! ### Moments of the scale score -/

section ScoreMoments

variable {ξ σ₀ : ℝ}

/-- The (rescaled) scale score of one observation, `ψ(x) = (1 + ξ) x / (σ₀ + ξ x) - 1`; the
score itself is `σ₀⁻¹ ψ(x)`. -/
noncomputable def gpdScorePsi (ξ σ₀ x : ℝ) : ℝ := (1 + ξ) * (x / (σ₀ + ξ * x)) - 1

/-- The negative derivative of the score term in the scale: `x / (σ₀ + ξ x)²`. -/
noncomputable def gpdScoreDeriv (ξ σ₀ x : ℝ) : ℝ := x / ((σ₀ + ξ * x) * (σ₀ + ξ * x))

lemma measurable_gpdScorePsi (ξ σ₀ : ℝ) : Measurable (gpdScorePsi ξ σ₀) := by
  unfold gpdScorePsi; fun_prop

lemma measurable_gpdScoreDeriv (ξ σ₀ : ℝ) : Measurable (gpdScoreDeriv ξ σ₀) := by
  unfold gpdScoreDeriv; fun_prop

lemma add_mul_gpdTransform (hσ₀ : 0 < σ₀) (hξ : ξ ≠ 0) (t : ℝ) :
    σ₀ + ξ * gpdTransform ξ σ₀ t = σ₀ * exp (ξ * t) := by
  rw [← one_add_mul_gpdTransform hσ₀ hξ t]; field_simp

lemma gpdScorePsi_gpdTransform (hσ₀ : 0 < σ₀) (hξ : ξ ≠ 0) (t : ℝ) :
    gpdScorePsi ξ σ₀ (gpdTransform ξ σ₀ t) = (1 - (1 + ξ) * exp ((-ξ) * t)) / ξ := by
  unfold gpdScorePsi
  rw [gpdTransform_div hσ₀ hξ, neg_mul]
  field_simp
  ring

lemma gpdScoreDeriv_gpdTransform (hσ₀ : 0 < σ₀) (hξ : ξ ≠ 0) (t : ℝ) :
    gpdScoreDeriv ξ σ₀ (gpdTransform ξ σ₀ t) =
      (exp ((-ξ) * t) - exp ((-2 * ξ) * t)) / (ξ * σ₀) := by
  unfold gpdScoreDeriv
  rw [mul_comm, ← div_div, gpdTransform_div hσ₀ hξ, add_mul_gpdTransform hσ₀ hξ]
  have h2 : exp ((-2 * ξ) * t) = (exp (ξ * t))⁻¹ * (exp (ξ * t))⁻¹ := by
    rw [← exp_neg, ← exp_add]; congr 1; ring
  have h1 : exp ((-ξ) * t) = (exp (ξ * t))⁻¹ := by rw [← exp_neg]; congr 1; ring
  rw [h1, h2, exp_neg]
  have := exp_pos (ξ * t)
  field_simp

/-- The score is square integrable for `ξ > -1/2`. -/
lemma memLp_gpdScorePsi (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) :
    MemLp (gpdScorePsi ξ σ₀) 2 (gpdMeasure ξ σ₀) := by
  rw [gpdMeasure, stdExpMeasure_eq_expMeasure, memLp_map_measure_iff
    (measurable_gpdScorePsi ξ σ₀).aestronglyMeasurable
    (measurable_gpdTransform ξ σ₀).aemeasurable]
  have he : MemLp (fun t => exp ((-ξ) * t)) 2 (expMeasure 1) := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    refine (integrable_exp_mul_expMeasure (a := -2 * ξ) (by linarith)).congr
      (ae_of_all _ fun t => ?_)
    simp only
    rw [sq, ← exp_add]; congr 1; ring
  have : (gpdScorePsi ξ σ₀ ∘ gpdTransform ξ σ₀) =
      fun t => ξ⁻¹ * (1 - (1 + ξ) * exp ((-ξ) * t)) := by
    funext t
    rw [Function.comp_apply, gpdScorePsi_gpdTransform hσ₀ hξ0 t, div_eq_inv_mul]
  rw [this]
  exact ((memLp_const 1).sub (he.const_mul (1 + ξ))).const_mul ξ⁻¹

/-- Integrals of `a + b e^{-ξ t} + c e^{-2ξ t}` against the standard exponential law. -/
lemma integral_lin_exp_expMeasure (hξ : -1 / 2 < ξ) (a b c : ℝ) :
    ∫ t, (a + b * exp ((-ξ) * t) + c * exp ((-2 * ξ) * t)) ∂expMeasure 1 =
      a + b / (1 + ξ) + c / (1 + 2 * ξ) := by
  have h1 : Integrable (fun t => b * exp ((-ξ) * t)) (expMeasure 1) :=
    (integrable_exp_mul_expMeasure (a := -ξ) (by linarith)).const_mul b
  have h2 : Integrable (fun t => c * exp ((-2 * ξ) * t)) (expMeasure 1) :=
    (integrable_exp_mul_expMeasure (a := -2 * ξ) (by linarith)).const_mul c
  have h0 : Integrable (fun t => a + b * exp ((-ξ) * t)) (expMeasure 1) :=
    (integrable_const a).add h1
  rw [integral_add h0 h2, integral_add (integrable_const a) h1, integral_const_mul,
    integral_const_mul, integral_exp_mul_expMeasure (by linarith),
    integral_exp_mul_expMeasure (by linarith), integral_const, probReal_univ, one_smul]
  ring_nf

lemma integrable_lin_exp_expMeasure (hξ : -1 / 2 < ξ) (a b c : ℝ) :
    Integrable (fun t => a + b * exp ((-ξ) * t) + c * exp ((-2 * ξ) * t)) (expMeasure 1) :=
  ((integrable_const a).add ((integrable_exp_mul_expMeasure (by linarith)).const_mul b)).add
    ((integrable_exp_mul_expMeasure (by linarith)).const_mul c)

/-- **The score has mean zero.** -/
theorem integral_gpdScorePsi (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) :
    ∫ x, gpdScorePsi ξ σ₀ x ∂gpdMeasure ξ σ₀ = 0 := by
  rw [integral_gpdMeasure (measurable_gpdScorePsi ξ σ₀)]
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have := integral_lin_exp_expMeasure hξ ξ⁻¹ (-(ξ⁻¹ * (1 + ξ))) 0
  rw [integral_congr_ae (ae_of_all _ fun t => (gpdScorePsi_gpdTransform hσ₀ hξ0 t).trans
    (show (1 - (1 + ξ) * exp ((-ξ) * t)) / ξ = ξ⁻¹ + -(ξ⁻¹ * (1 + ξ)) * exp ((-ξ) * t) +
      0 * exp ((-2 * ξ) * t) by ring)), this]
  field_simp
  ring

/-- **The variance of the score**: `E[ψ(X)²] = 1/(1 + 2ξ)`, so that the Fisher information of
the scale is `I(σ₀) = E[(σ₀⁻¹ ψ(X))²] = 1/(σ₀² (1 + 2ξ))`. -/
theorem integral_gpdScorePsi_sq (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) :
    ∫ x, gpdScorePsi ξ σ₀ x ^ 2 ∂gpdMeasure ξ σ₀ = 1 / (1 + 2 * ξ) := by
  rw [integral_gpdMeasure ((measurable_gpdScorePsi ξ σ₀).pow_const 2)]
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have h2ξ : 1 + 2 * ξ ≠ 0 := by intro h; linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  have := integral_lin_exp_expMeasure hξ (ξ⁻¹ ^ 2) (-(2 * (1 + ξ) * ξ⁻¹ ^ 2))
    ((1 + ξ) ^ 2 * ξ⁻¹ ^ 2)
  rw [integral_congr_ae (ae_of_all _ fun t => ?_), this]
  · field_simp
    ring
  · show _ = _
    rw [gpdScorePsi_gpdTransform hσ₀ hξ0 t]
    have : exp ((-2 * ξ) * t) = exp ((-ξ) * t) ^ 2 := by rw [sq, ← exp_add]; congr 1; ring
    rw [this]
    field_simp
    ring

lemma integrable_gpdScoreDeriv (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) :
    Integrable (gpdScoreDeriv ξ σ₀) (gpdMeasure ξ σ₀) := by
  rw [integrable_gpdMeasure_iff (measurable_gpdScoreDeriv ξ σ₀)]
  refine (integrable_lin_exp_expMeasure hξ 0 (ξ * σ₀)⁻¹ (-(ξ * σ₀)⁻¹)).congr
    (ae_of_all _ fun t => ?_)
  simp only
  rw [gpdScoreDeriv_gpdTransform hσ₀ hξ0 t]
  ring

/-- **The expected derivative of the score**: `E[X / (σ₀ + ξ X)²] = 1/(σ₀ (1 + ξ)(1 + 2ξ))`. -/
theorem integral_gpdScoreDeriv (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) :
    ∫ x, gpdScoreDeriv ξ σ₀ x ∂gpdMeasure ξ σ₀ = 1 / (σ₀ * (1 + ξ) * (1 + 2 * ξ)) := by
  rw [integral_gpdMeasure (measurable_gpdScoreDeriv ξ σ₀)]
  have h1ξ : 1 + ξ ≠ 0 := by intro h; linarith
  have h2ξ : 1 + 2 * ξ ≠ 0 := by intro h; linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  rw [integral_congr_ae (ae_of_all _ fun t => (gpdScoreDeriv_gpdTransform hσ₀ hξ0 t).trans
    (show (exp ((-ξ) * t) - exp ((-2 * ξ) * t)) / (ξ * σ₀) = 0 + (ξ * σ₀)⁻¹ * exp ((-ξ) * t) +
      -(ξ * σ₀)⁻¹ * exp ((-2 * ξ) * t) by ring)), integral_lin_exp_expMeasure hξ]
  field_simp
  ring

end ScoreMoments

end ExtremeValueTheory
