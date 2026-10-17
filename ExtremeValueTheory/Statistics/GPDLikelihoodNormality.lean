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

/-! ### The deterministic expansion of the likelihood equation -/

section Expansion

variable {ξ σ₀ s t t' : ℝ} {x : ℕ → ℝ} {n : ℕ}

/-- The empirical score at `σ₀`: `Fₙ(σ₀) = n⁻¹ ∑_{i<n} ψ(xᵢ)`. -/
noncomputable def scoreAvg (ξ σ₀ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdScorePsi ξ σ₀ (x i)

/-- `Qₙ(t) = n⁻¹ ∑_{i<n} xᵢ / ((σ₀ + ξ xᵢ)(t + ξ xᵢ))`: the difference quotient of the score
between `t` and `σ₀` is `-(1 + ξ) Qₙ(t)`. -/
noncomputable def crossAvg (ξ σ₀ t : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i / ((σ₀ + ξ * x i) * (t + ξ * x i))

/-- The running maximum `max(0, f 0, …, f (n-1))`. -/
noncomputable def runMax (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (runMax f n) (f n)

lemma runMax_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ runMax f n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma le_runMax (f : ℕ → ℝ) {i n : ℕ} (hi : i < n) : f i ≤ runMax f n := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · exact (ih h).trans (le_max_left _ _)
    · exact le_max_right _ _

lemma exists_le_of_le_runMax (f : ℕ → ℝ) {n : ℕ} {η : ℝ} (hη : 0 < η) (h : η ≤ runMax f n) :
    ∃ i < n, η ≤ f i := by
  induction n with
  | zero => exact absurd h (not_le.2 hη)
  | succ n ih =>
    rcases le_max_iff.1 h with h' | h'
    · obtain ⟨i, hi, hfi⟩ := ih h'
      exact ⟨i, hi.trans (Nat.lt_succ_self n), hfi⟩
    · exact ⟨n, Nat.lt_succ_self n, h'⟩

/-- **The exact expansion of the score.** At an admissible root `s` of the likelihood equation,
`Fₙ(σ₀) = (s - σ₀) (1 + ξ) Qₙ(s)`. -/
theorem scoreAvg_eq_of_root (hn : 0 < n) (ha : ∀ i < n, 0 < σ₀ + ξ * x i)
    (hb : ∀ i < n, 0 < s + ξ * x i)
    (hroot : (1 + ξ) * ∑ i ∈ Finset.range n, x i / (s + ξ * x i) = n) :
    scoreAvg ξ σ₀ x n = (s - σ₀) * ((1 + ξ) * crossAvg ξ σ₀ s x n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : ∑ i ∈ Finset.range n, gpdScorePsi ξ σ₀ (x i) =
      (1 + ξ) * ∑ i ∈ Finset.range n, x i / (σ₀ + ξ * x i) - n := by
    simp only [gpdScorePsi, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  have h2 : ∑ i ∈ Finset.range n, x i / (σ₀ + ξ * x i) -
      ∑ i ∈ Finset.range n, x i / (s + ξ * x i) =
      (s - σ₀) * ∑ i ∈ Finset.range n, x i / ((σ₀ + ξ * x i) * (s + ξ * x i)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 := (ha i (Finset.mem_range.1 hi)).ne'
    have h2 := (hb i (Finset.mem_range.1 hi)).ne'
    rw [div_sub_div _ _ h1 h2, mul_div_assoc']
    congr 1
    ring
  unfold scoreAvg crossAvg
  rw [h1, ← hroot]
  have : (1 + ξ) * ∑ i ∈ Finset.range n, x i / (σ₀ + ξ * x i) -
      (1 + ξ) * ∑ i ∈ Finset.range n, x i / (s + ξ * x i) =
      (1 + ξ) * ((s - σ₀) * ∑ i ∈ Finset.range n, x i / ((σ₀ + ξ * x i) * (s + ξ * x i))) := by
    rw [← h2]; ring
  rw [this]
  ring

lemma crossAvg_anti (hx : ∀ i < n, 0 ≤ x i) (ha : ∀ i < n, 0 < σ₀ + ξ * x i)
    (ht : ∀ i < n, 0 < t + ξ * x i) (htt' : t ≤ t') :
    crossAvg ξ σ₀ t' x n ≤ crossAvg ξ σ₀ t x n := by
  unfold crossAvg
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
  have hi := Finset.mem_range.1 hi
  exact div_le_div_of_nonneg_left (hx i hi) (mul_pos (ha i hi) (ht i hi))
    (mul_le_mul_of_nonneg_left (by linarith) (ha i hi).le)

lemma crossAvg_pos (hn : 0 < n) (hx : ∀ i < n, 0 < x i) (ha : ∀ i < n, 0 < σ₀ + ξ * x i)
    (ht : ∀ i < n, 0 < t + ξ * x i) : 0 < crossAvg ξ σ₀ t x n := by
  unfold crossAvg
  refine mul_pos (by positivity) (Finset.sum_pos (fun i hi => ?_) ⟨0, by simpa using hn⟩)
  have hi := Finset.mem_range.1 hi
  exact div_pos (hx i hi) (mul_pos (ha i hi) (ht i hi))

/-- **The lower side of the expansion.** At an admissible root `s < σ₀`, with
`ρ = |Fₙ(σ₀)| M / ((1 + ξ) Qₙ(σ₀)) < 1/2`, where `M ≥ 1/(σ₀ + ξ xᵢ)` for all `i < n`,
`0 ≤ (1 + ξ) Qₙ(s) - (1 + ξ) Qₙ(σ₀) ≤ 2 (1 + ξ) Qₙ(σ₀) ρ`. -/
theorem crossAvg_sub_le (h1ξ : 0 < 1 + ξ) (hn : 0 < n) (hx : ∀ i < n, 0 < x i)
    (ha : ∀ i < n, 0 < σ₀ + ξ * x i) (hb : ∀ i < n, 0 < s + ξ * x i)
    (hroot : (1 + ξ) * ∑ i ∈ Finset.range n, x i / (s + ξ * x i) = n) (hs : s < σ₀) {M : ℝ}
    (hM : ∀ i < n, 1 / (σ₀ + ξ * x i) ≤ M)
    (hρ : |scoreAvg ξ σ₀ x n| / ((1 + ξ) * crossAvg ξ σ₀ σ₀ x n) * M < 1 / 2) :
    0 ≤ (1 + ξ) * crossAvg ξ σ₀ s x n - (1 + ξ) * crossAvg ξ σ₀ σ₀ x n ∧
      (1 + ξ) * crossAvg ξ σ₀ s x n - (1 + ξ) * crossAvg ξ σ₀ σ₀ x n ≤
        2 * ((1 + ξ) * crossAvg ξ σ₀ σ₀ x n) *
          (|scoreAvg ξ σ₀ x n| / ((1 + ξ) * crossAvg ξ σ₀ σ₀ x n) * M) := by
  set q₀ := (1 + ξ) * crossAvg ξ σ₀ σ₀ x n
  set R := (1 + ξ) * crossAvg ξ σ₀ s x n
  set ρ := |scoreAvg ξ σ₀ x n| / q₀ * M
  have hq₀ : 0 < q₀ := mul_pos h1ξ (crossAvg_pos hn hx ha ha)
  have hRq : q₀ ≤ R := mul_le_mul_of_nonneg_left
    (crossAvg_anti (fun i hi => (hx i hi).le) ha hb hs.le) h1ξ.le
  have hid := scoreAvg_eq_of_root hn ha hb hroot
  set d := σ₀ - s
  have hd : 0 < d := sub_pos.2 hs
  have habs : |scoreAvg ξ σ₀ x n| = d * R := by
    rw [hid, abs_mul, abs_of_neg (by linarith : s - σ₀ < 0), abs_of_pos (hq₀.trans_le hRq)]
    ring
  have hdq : d ≤ |scoreAvg ξ σ₀ x n| / q₀ := by
    rw [le_div_iff₀ hq₀, habs]
    exact mul_le_mul_of_nonneg_left hRq hd.le
  have hM0 : 0 ≤ M := (one_div_pos.2 (ha 0 hn)).le.trans (hM 0 hn)
  have hρ0 : 0 ≤ ρ := mul_nonneg (div_nonneg (abs_nonneg _) hq₀.le) hM0
  -- each denominator shrinks by at most the factor `1 - ρ`
  have hbi : ∀ i < n, (1 - ρ) * (σ₀ + ξ * x i) ≤ s + ξ * x i := fun i hi => by
    have h1 : d * (1 / (σ₀ + ξ * x i)) ≤ ρ := (mul_le_mul_of_nonneg_left (hM i hi) hd.le).trans
      (mul_le_mul_of_nonneg_right hdq hM0)
    have h2 : d ≤ ρ * (σ₀ + ξ * x i) := by
      rw [mul_one_div, div_le_iff₀ (ha i hi)] at h1; exact h1
    have : s + ξ * x i = σ₀ + ξ * x i - d := by simp only [d]; ring
    rw [this]; linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hQ : crossAvg ξ σ₀ s x n ≤ crossAvg ξ σ₀ σ₀ x n / (1 - ρ) := by
    rw [le_div_iff₀ h1ρ]
    unfold crossAvg
    rw [mul_comm, mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
    have hi := Finset.mem_range.1 hi
    have hai := ha i hi
    have hbi' := hbi i hi
    rw [mul_div_assoc', div_le_div_iff₀ (mul_pos hai (hb i hi)) (mul_pos hai hai)]
    have := (hx i hi).le
    nlinarith [mul_le_mul_of_nonneg_left hbi' (mul_nonneg this hai.le)]
  refine ⟨by linarith, ?_⟩
  have : R ≤ q₀ / (1 - ρ) := by
    simp only [R, q₀]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hQ h1ξ.le
  have h3 : q₀ / (1 - ρ) - q₀ ≤ 2 * q₀ * ρ := by
    rw [div_sub' h1ρ.ne', div_le_iff₀ h1ρ]
    nlinarith [mul_nonneg (mul_nonneg hρ0 hq₀.le) (by linarith : (0:ℝ) ≤ 1 - 2 * ρ)]
  linarith

end Expansion

/-! ### Convergence in probability: domination lemmas -/

section InProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Domination: if `|fₙ| ≤ gₙ` everywhere and `gₙ → 0` in probability, then `fₙ → 0`. -/
lemma tendstoInMeasure_zero_of_abs_le {f g : ℕ → Ω → ℝ} (h : ∀ n ω, |f n ω| ≤ g n ω)
    (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε)
    (fun _ => bot_le) fun n => measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  exact hω.trans ((h n ω).trans (le_abs_self _))

/-- Domination almost surely eventually: if a.s. `|fₙ| ≤ gₙ` for all large `n`, and `gₙ → 0` in
probability, then `fₙ → 0` in probability. -/
lemma tendstoInMeasure_zero_of_ae_eventually_abs_le [IsFiniteMeasure P] {f g : ℕ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hgm : ∀ n, AEStronglyMeasurable (g n) P)
    (hle : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |f n ω| ≤ g n ω)
    (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  set d : ℕ → Ω → ℝ := fun n ω => max (|f n ω| - g n ω) 0
  have hd : TendstoInMeasure P d atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · exact (((hf n).norm.sub (hgm n)).sup aestronglyMeasurable_const)
    · filter_upwards [hle] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω] with n hn
      simp only [d]
      rw [max_eq_right (by linarith)]
  have hsum := tendstoInMeasure_comp₂ hg hd (φ := fun p => p.1 + p.2) continuous_add.continuousAt
  simp only [add_zero] at hsum
  refine tendstoInMeasure_zero_of_abs_le (g := fun n ω => g n ω + d n ω) (fun n ω => ?_) hsum
  simp only [d]
  linarith [le_max_left (|f n ω| - g n ω) 0]

/-- A continuous cutoff, `0` on `(-∞, 1/4]` and `1` on `[1/2, ∞)`. -/
noncomputable def cutoff (r : ℝ) : ℝ := min 1 (max 0 (4 * r - 1))

lemma continuous_cutoff : Continuous cutoff := by unfold cutoff; fun_prop

lemma cutoff_nonneg (r : ℝ) : 0 ≤ cutoff r := le_min zero_le_one (le_max_left _ _)

lemma cutoff_of_le {r : ℝ} (h : r ≤ 1 / 4) : cutoff r = 0 := by
  unfold cutoff; rw [max_eq_left (by linarith), min_eq_right zero_le_one]

lemma cutoff_of_ge {r : ℝ} (h : 1 / 2 ≤ r) : cutoff r = 1 := by
  unfold cutoff; rw [max_eq_right (by linarith), min_eq_left (by linarith)]

/-- If `ρₙ → 0` in probability, then `Wₙ · cutoff(ρₙ) → 0` in probability, whatever `Wₙ`. -/
lemma tendstoInMeasure_mul_cutoff {ρ : ℕ → Ω → ℝ} (W : ℕ → Ω → ℝ)
    (hρ : TendstoInMeasure P ρ atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => W n ω * cutoff (ρ n ω)) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hρ ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hρ (1 / 4) (by norm_num))
    (fun _ => bot_le) fun n => measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  by_contra h
  rw [cutoff_of_le ((le_abs_self _).trans (not_le.1 h).le), mul_zero, abs_zero] at hω
  linarith

end InProbability

/-! ### The central limit theorem for the score -/

section ScoreCLT

variable {ξ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- The normalized score sum `(√n)⁻¹ ∑_{i<n} ψ(Xᵢ) = √n Fₙ(σ₀)`. -/
noncomputable def scoreSumNorm (ξ σ₀ : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScorePsi ξ σ₀ (X i ω)

omit [IsProbabilityMeasure P] in
lemma memLp_gpdScorePsi_comp (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) {Y : Ω → ℝ}
    (hY : HasLaw Y (gpdMeasure ξ σ₀) P) : MemLp (gpdScorePsi ξ σ₀ ∘ Y) 2 P := by
  rw [← memLp_map_measure_iff (measurable_gpdScorePsi ξ σ₀).aestronglyMeasurable hY.aemeasurable,
    hY.map_eq]
  exact memLp_gpdScorePsi hξ hξ0 hσ₀

omit [IsProbabilityMeasure P] in
lemma integral_gpdScorePsi_comp (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) {Y : Ω → ℝ}
    (hY : HasLaw Y (gpdMeasure ξ σ₀) P) : P[gpdScorePsi ξ σ₀ ∘ Y] = 0 := by
  rw [hY.integral_comp (measurable_gpdScorePsi ξ σ₀).aestronglyMeasurable]
  exact integral_gpdScorePsi hξ hξ0 hσ₀

omit [IsProbabilityMeasure P] in
lemma variance_gpdScorePsi_comp (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) {Y : Ω → ℝ}
    (hY : HasLaw Y (gpdMeasure ξ σ₀) P) : Var[gpdScorePsi ξ σ₀ ∘ Y; P] = 1 / (1 + 2 * ξ) := by
  rw [variance_of_integral_eq_zero ((measurable_gpdScorePsi ξ σ₀).comp_aemeasurable
    hY.aemeasurable) (integral_gpdScorePsi_comp hξ hξ0 hσ₀ hY)]
  have := hY.integral_comp (f := fun x => gpdScorePsi ξ σ₀ x ^ 2)
    ((measurable_gpdScorePsi ξ σ₀).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def] at this ⊢
  rw [this, integral_gpdScorePsi_sq hξ hξ0 hσ₀]

/-- **The central limit theorem for the score**: `√n Fₙ(σ₀) ⇒ N(0, 1/(1 + 2ξ))`. -/
theorem tendstoInDistribution_scoreSumNorm (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) (hind : iIndepFun X P) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (1 / (1 + 2 * ξ)).toNNReal) P') :
    TendstoInDistribution (scoreSumNorm ξ σ₀ X) atTop Z (fun _ => P) P' := by
  set Y : ℕ → Ω → ℝ := fun i => gpdScorePsi ξ σ₀ ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => gpdScorePsi ξ σ₀)
    (fun _ => measurable_gpdScorePsi ξ σ₀)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ (measurable_gpdScorePsi ξ σ₀)
  have hZ' : HasLaw Z (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by
    rw [variance_gpdScorePsi_comp hξ hξ0 hσ₀ (hX 0)]; exact hZ
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ'
    (memLp_gpdScorePsi_comp hξ hξ0 hσ₀ (hX 0)) hind' hident
  rw [integral_gpdScorePsi_comp hξ hξ0 hσ₀ (hX 0)] at hclt
  convert hclt using 3 with n ω
  simp [scoreSumNorm, Y]

/-- **The normalized score sum is bounded in probability** (Chebyshev: its variance is
`1/(1 + 2ξ)`). -/
theorem isBoundedInProbability_scoreSumNorm (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) (hind : iIndepFun X P) :
    IsBoundedInProbability P (scoreSumNorm ξ σ₀ X) := by
  set v : ℝ := 1 / (1 + 2 * ξ)
  have hv : 0 < v := one_div_pos.2 (by linarith)
  set Y : ℕ → Ω → ℝ := fun i => gpdScorePsi ξ σ₀ ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => gpdScorePsi ξ σ₀)
    (fun _ => measurable_gpdScorePsi ξ σ₀)
  have hL2 : ∀ i, MemLp (Y i) 2 P := fun i => memLp_gpdScorePsi_comp hξ hξ0 hσ₀ (hX i)
  have hS : ∀ n, scoreSumNorm ξ σ₀ X n = fun ω => (√(n : ℝ))⁻¹ * (∑ i ∈ Finset.range n, Y i) ω :=
    fun n => funext fun ω => by simp [scoreSumNorm, Y, Finset.sum_apply]
  have hmemS : ∀ n, MemLp (scoreSumNorm ξ σ₀ X n) 2 P := fun n => by
    rw [hS n]; exact (memLp_finsetSum' _ fun i _ => hL2 i).const_mul _
  have hmean : ∀ n, P[scoreSumNorm ξ σ₀ X n] = 0 := fun n => by
    rw [hS n, integral_const_mul]
    simp_rw [Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ => (hL2 i).integrable one_le_two]
    exact mul_eq_zero_of_right _
      (Finset.sum_eq_zero fun i _ => integral_gpdScorePsi_comp hξ hξ0 hσ₀ (hX i))
  have hvar : ∀ n, Var[scoreSumNorm ξ σ₀ X n; P] ≤ v := fun n => by
    rw [hS n, variance_const_mul, IndepFun.variance_sum (fun i _ => hL2 i)
      (fun i _ j _ hij => hind'.indepFun hij)]
    simp only [Y, variance_gpdScorePsi_comp hξ hξ0 hσ₀ (hX _), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, inv_pow, sq_sqrt (Nat.cast_nonneg n)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hv.le]
    · have : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨0, Eventually.of_forall fun _ => le_top⟩
  set e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  set M := √(v / e + 1)
  have hM : 0 < M := sqrt_pos.2 (by positivity)
  refine ⟨M, Eventually.of_forall fun n => ?_⟩
  have h1 := meas_ge_le_variance_div_sq (hmemS n) hM
  rw [hmean n] at h1
  simp only [sub_zero] at h1
  refine (measure_mono fun ω (hω : M < |scoreSumNorm ξ σ₀ X n ω|) => hω.le).trans
    (h1.trans ?_)
  rw [← ENNReal.ofReal_toReal hεtop]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [sq_sqrt (by positivity), div_le_iff₀ (by positivity)]
  have := hvar n
  calc Var[scoreSumNorm ξ σ₀ X n; P] ≤ v := this
    _ ≤ e * (v / e + 1) := by rw [mul_add, mul_div_cancel₀ _ he.ne']; linarith

end ScoreCLT

/-! ### The largest observations: `max_{i<n} 1/(σ₀ + ξ Xᵢ) = o_P(√n)` -/

section RunMax

lemma runMax_le {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, f i ≤ C) (n : ℕ) :
    runMax f n ≤ C := by
  induction n with
  | zero => exact hC
  | succ n ih => exact max_le ih (hf n)

lemma aemeasurable_runMax {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f : ℕ → Ω → ℝ} (hf : ∀ i, AEMeasurable (f i) P) (n : ℕ) :
    AEMeasurable (fun ω => runMax (fun i => f i ω) n) P := by
  induction n with
  | zero => exact aemeasurable_const
  | succ n ih => exact ih.max (hf n)

/-- `n (C/√n)^β → 0` for `β > 2`. -/
lemma tendsto_natCast_mul_div_sqrt_rpow {C β : ℝ} (hC : 0 ≤ C) (hβ : 2 < β) :
    Tendsto (fun n : ℕ => (n : ℝ) * (C / √(n : ℝ)) ^ β) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => C ^ β * (n : ℝ) ^ (-(β / 2 - 1))) atTop (𝓝 (C ^ β * 0)) :=
    ((tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).const_mul _
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_rpow hC (sqrt_nonneg _), sqrt_eq_rpow, ← rpow_mul hn'.le,
    show -(β / 2 - 1) = 1 - 1 / 2 * β by ring, rpow_sub hn', rpow_one]
  ring

variable {ξ σ₀ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

/-- For `ξ < 0`, `P(σ₀ + ξ X < u) = (u/σ₀)^{-1/ξ}` for `0 < u ≤ σ₀`. -/
lemma gpdMeasure_add_mul_lt (hξ : ξ < 0) (hσ₀ : 0 < σ₀) {u : ℝ} (hu : 0 < u) (huσ : u ≤ σ₀) :
    gpdMeasure ξ σ₀ {x | σ₀ + ξ * x < u} = ENNReal.ofReal ((u / σ₀) ^ (-(1 / ξ))) := by
  have hset : {x : ℝ | σ₀ + ξ * x < u} = Ioi ((u - σ₀) / ξ) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ioi]
    rw [div_lt_iff_of_neg hξ]
    constructor <;> intro h <;> linarith
  have hx0 : 0 ≤ (u - σ₀) / ξ := div_nonneg_of_nonpos (by linarith) hξ.le
  rw [hset, gpdMeasure_Ioi hσ₀ hx0]
  congr 1
  have h' : ξ * ((u - σ₀) / ξ) = u - σ₀ := mul_div_cancel₀ _ hξ.ne
  have : 1 + ξ * ((u - σ₀) / ξ) / σ₀ = u / σ₀ := by
    rw [h']; field_simp; ring
  simp only [gpdSurvival', hξ.ne, ↓reduceIte, this, max_eq_left (div_pos hu hσ₀).le]

/-- **The largest observations are `o_P(√n)` on the scale of the score**:
`max_{i<n} 1/(σ₀ + ξ Xᵢ) / √n → 0` in probability. For `ξ > 0` the maximum is at most `1/σ₀`;
for `-1/2 < ξ < 0` this is the tail estimate `n P(σ₀ + ξ X < u/√n) ≍ n^{1 + 1/(2ξ)} → 0`. -/
theorem tendstoInMeasure_runMax_div_sqrt (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) :
    TendstoInMeasure P (fun n ω => runMax (fun i => 1 / (σ₀ + ξ * X i ω)) n / √(n : ℝ))
      atTop (fun _ => 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun ω => runMax (fun i => 1 / (σ₀ + ξ * X i ω)) n / √(n : ℝ)) P := fun n =>
    ((aemeasurable_runMax (fun i => by have := (hX i).aemeasurable; fun_prop) n).div_const
      _).aestronglyMeasurable
  rcases lt_or_gt_of_ne hξ0 with hneg | hpos
  · -- `ξ < 0`: the tail estimate
    set β := -(1 / ξ)
    have hβ : 2 < β := by
      have : 1 / ξ < -2 := by rw [div_lt_iff_of_neg hneg]; linarith
      simp only [β]; linarith
    rw [tendstoInMeasure_iff_dist]
    intro η hη
    have hlim := (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_natCast_mul_div_sqrt_rpow (C := 2 / (η * σ₀)) (by positivity) hβ)
    rw [ENNReal.ofReal_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    -- for large `n`, `2/(η √n) ≤ σ₀`
    have hsmall : ∀ᶠ n : ℕ in atTop, 2 / (η * √(n : ℝ)) ≤ σ₀ := by
      have : Tendsto (fun n : ℕ => 2 / (η * √(n : ℝ))) atTop (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hη ?_)
        exact tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      exact this.eventually (ge_mem_nhds hσ₀)
    filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hn0
    have hsq : 0 < √(n : ℝ) := sqrt_pos.2 (by exact_mod_cast hn0)
    set u := 2 / (η * √(n : ℝ))
    have hu : 0 < u := by positivity
    have hsub : {ω | η ≤ dist (runMax (fun i => 1 / (σ₀ + ξ * X i ω)) n / √(n : ℝ)) 0} ⊆
        ⋃ i ∈ Finset.range n, X i ⁻¹' {x | σ₀ + ξ * x < u} := by
      intro ω hω
      simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
      rw [abs_of_nonneg (div_nonneg (runMax_nonneg _ _) hsq.le), le_div_iff₀ hsq] at hω
      obtain ⟨i, hi, hfi⟩ := exists_le_of_le_runMax _ (by positivity) hω
      refine mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, ?_⟩
      simp only [mem_preimage, mem_ofPred_eq]
      have hpos' : 0 < 1 / (σ₀ + ξ * X i ω) := lt_of_lt_of_le (by positivity) hfi
      have ha : 0 < σ₀ + ξ * X i ω := one_div_pos.1 hpos'
      rw [le_div_iff₀ ha] at hfi
      have : σ₀ + ξ * X i ω ≤ 1 / (η * √(n : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have : 1 / (η * √(n : ℝ)) < u := by
        simp only [u]; exact div_lt_div_of_pos_right (by norm_num) (by positivity)
      linarith
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    have hS : MeasurableSet {x : ℝ | σ₀ + ξ * x < u} :=
      measurableSet_lt (by fun_prop) measurable_const
    have heach : ∀ i, P (X i ⁻¹' {x | σ₀ + ξ * x < u}) =
        ENNReal.ofReal ((u / σ₀) ^ β) := fun i => by
      rw [← Measure.map_apply_of_aemeasurable (hX i).aemeasurable hS, (hX i).map_eq,
        gpdMeasure_add_mul_lt hneg hσ₀ hu hn]
    simp only [heach, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine le_of_eq ?_
    simp only [Function.comp_apply, u]
    congr 3
    field_simp
  · -- `ξ > 0`: the maximum is at most `1/σ₀`
    have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω := ae_all_iff.2 fun i =>
      (ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)).mono fun _ h => h.1
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le hmeas
      (g := fun n _ => 1 / σ₀ / √(n : ℝ)) (fun _ => aestronglyMeasurable_const) ?_
      (tendstoInMeasure_const_of_tendsto (tendsto_const_nhds.div_atTop
        (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)))
    filter_upwards [hsupp] with ω hω
    refine Eventually.of_forall fun n => ?_
    rw [abs_of_nonneg (div_nonneg (runMax_nonneg _ _) (sqrt_nonneg _))]
    refine div_le_div_of_nonneg_right (runMax_le (by positivity) (fun i => ?_) n) (sqrt_nonneg _)
    have := hω i
    exact one_div_le_one_div_of_le hσ₀ (by nlinarith)

end RunMax

/-! ### The law of large numbers for the derivative of the score, above `σ₀` -/

section CrossLLN

variable {ξ σ₀ t : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The summand of `crossAvg`: `x / ((σ₀ + ξ x)(t + ξ x))`. -/
noncomputable def crossTerm (ξ σ₀ t x : ℝ) : ℝ := x / ((σ₀ + ξ * x) * (t + ξ * x))

lemma measurable_crossTerm (ξ σ₀ t : ℝ) : Measurable (crossTerm ξ σ₀ t) := by
  unfold crossTerm; fun_prop

lemma crossAvg_eq (t : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    crossAvg ξ σ₀ t x n = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, crossTerm ξ σ₀ t (x i) := rfl

lemma crossTerm_self : crossTerm ξ σ₀ σ₀ = gpdScoreDeriv ξ σ₀ := rfl

lemma crossTerm_bounds (ht : σ₀ ≤ t) {x : ℝ} (hx : 0 < x ∧ 0 < σ₀ + ξ * x) :
    0 ≤ crossTerm ξ σ₀ t x ∧ crossTerm ξ σ₀ t x ≤ gpdScoreDeriv ξ σ₀ x := by
  have h2 : 0 < t + ξ * x := by linarith [hx.2]
  refine ⟨div_nonneg hx.1.le (mul_pos hx.2 h2).le, ?_⟩
  exact div_le_div_of_nonneg_left hx.1.le (mul_pos hx.2 hx.2)
    (mul_le_mul_of_nonneg_left (by linarith) hx.2.le)

lemma integrable_crossTerm (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) (ht : σ₀ ≤ t) :
    Integrable (crossTerm ξ σ₀ t) (gpdMeasure ξ σ₀) := by
  refine (integrable_gpdScoreDeriv hξ hξ0 hσ₀).mono'
    (measurable_crossTerm ξ σ₀ t).aestronglyMeasurable ?_
  filter_upwards [ae_gpdMeasure hσ₀] with x hx
  obtain ⟨h1, h2⟩ := crossTerm_bounds ht hx
  rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact h2

lemma tendsto_integral_crossTerm (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀) :
    Tendsto (fun k : ℕ => ∫ x, crossTerm ξ σ₀ (σ₀ + 1 / ((k : ℝ) + 1)) x ∂gpdMeasure ξ σ₀) atTop
      (𝓝 (∫ x, gpdScoreDeriv ξ σ₀ x ∂gpdMeasure ξ σ₀)) := by
  have htk : ∀ k : ℕ, σ₀ ≤ σ₀ + 1 / ((k : ℝ) + 1) := fun k => by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hlim : Tendsto (fun k : ℕ => σ₀ + 1 / ((k : ℝ) + 1)) atTop (𝓝 σ₀) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add σ₀
    rwa [add_zero] at this
  refine tendsto_integral_of_dominated_convergence (gpdScoreDeriv ξ σ₀)
    (fun k => (measurable_crossTerm _ _ _).aestronglyMeasurable)
    (integrable_gpdScoreDeriv hξ hξ0 hσ₀) (fun k => ?_) ?_
  · filter_upwards [ae_gpdMeasure hσ₀] with x hx
    obtain ⟨h1, h2⟩ := crossTerm_bounds (htk k) hx
    rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact h2
  · filter_upwards [ae_gpdMeasure hσ₀] with x hx
    have hc : ContinuousAt (fun t => crossTerm ξ σ₀ t x) σ₀ := by
      unfold crossTerm
      exact continuousAt_const.div (continuousAt_const.mul (continuousAt_id.add continuousAt_const))
        (mul_pos hx.2 hx.2).ne'
    exact hc.tendsto.comp hlim

/-- **The strong law for the derivative of the score, above `σ₀`.** Almost surely, along every
sequence `sₙ → σ₀`, `Qₙ(max(sₙ, σ₀)) → E[X / (σ₀ + ξ X)²]`. -/
theorem ae_tendsto_crossAvg_max (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, ∀ s : ℕ → ℝ, Tendsto s atTop (𝓝 σ₀) →
      Tendsto (fun n => crossAvg ξ σ₀ (max (s n) σ₀) (fun i => X i ω) n) atTop
        (𝓝 (∫ x, gpdScoreDeriv ξ σ₀ x ∂gpdMeasure ξ σ₀)) := by
  set J := ∫ x, gpdScoreDeriv ξ σ₀ x ∂gpdMeasure ξ σ₀
  set t : ℕ → ℝ := fun k => σ₀ + 1 / ((k : ℝ) + 1)
  have htk : ∀ k, σ₀ < t k := fun k => by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    simp only [t]; linarith
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  have hk : ∀ᵐ ω ∂P, ∀ k, Tendsto (fun n => crossAvg ξ σ₀ (t k) (fun i => X i ω) n) atTop
      (𝓝 (∫ x, crossTerm ξ σ₀ (t k) x ∂gpdMeasure ξ σ₀)) := ae_all_iff.2 fun k =>
    ae_tendsto_avg_comp hX hind (measurable_crossTerm _ _ _)
      (integrable_crossTerm hξ hξ0 hσ₀ (htk k).le)
  have h0 : ∀ᵐ ω ∂P, Tendsto (fun n => crossAvg ξ σ₀ σ₀ (fun i => X i ω) n) atTop (𝓝 J) :=
    ae_tendsto_avg_comp hX hind (measurable_gpdScoreDeriv _ _) (integrable_gpdScoreDeriv hξ hξ0 hσ₀)
  filter_upwards [hsupp, hk, h0] with ω hω hk h0 s hs
  have hx0 : ∀ n, ∀ i < n, 0 ≤ X i ω := fun _ i _ => (hω i).1.le
  have ha : ∀ n, ∀ i < n, 0 < σ₀ + ξ * X i ω := fun _ i _ => (hω i).2
  have hmax : ∀ n, ∀ i < n, 0 < max (s n) σ₀ + ξ * X i ω := fun n i _ => by
    linarith [(hω i).2, le_max_right (s n) σ₀]
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk'⟩ := ((tendsto_integral_crossTerm hξ hξ0 hσ₀).eventually (lt_mem_nhds hb)).exists
    filter_upwards [(hk k).eventually (lt_mem_nhds hk'), hs.eventually (gt_mem_nhds (htk k))]
      with n hn hsn
    exact hn.trans_le (crossAvg_anti (hx0 n) (ha n) (hmax n) (max_le hsn.le (htk k).le))
  · filter_upwards [h0.eventually (gt_mem_nhds hb)] with n hn
    exact (crossAvg_anti (hx0 n) (ha n) (ha n) (le_max_right _ _)).trans_lt hn

end CrossLLN

end ExtremeValueTheory
