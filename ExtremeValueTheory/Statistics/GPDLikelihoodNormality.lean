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

end ExtremeValueTheory
