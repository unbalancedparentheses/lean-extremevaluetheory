/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVHessian

/-!
# Envelopes for the GEV likelihood

The asymptotic normality of the three-parameter GEV maximum likelihood estimator needs bounds on
the log-likelihood and its derivatives by functions which are integrable under the true law. They
are given by the **envelopes** `gevEnv a b v = v^{-a} + v^b`, `v = 1 + ξ₀ (x - μ₀)/σ₀`
(`rpow_le_gevEnv`, `gevEnv_mul_le`), which are integrable under the true law as soon as
`-1 < a ξ₀` and `b ξ₀ < 1` (`integrable_gevEnv`: on the exponential scale `v = t^{-ξ₀}`).

## Main results

* `gevEnv`, `rpow_le_gevEnv`, `one_le_gevEnv`, `gevEnv_mul_le`, `gevEnv_le_of_le`,
  `gevEnv_le_of_comparable`, `abs_log_le_gevEnv`: the envelope calculus.
* `integrable_gevEnv`: integrability of the envelopes under the GEV law.
* `ae_gevU_pos`: the observations lie in the support almost surely.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* A. Bücher and J. Segers, *On the maximum likelihood estimator for the Generalized Extreme-Value
  distribution*, Extremes 20 (2017).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### The envelopes `u^{-a} + u^b` -/

section Env

/-- The envelope `u^{-a} + u^b`. -/
noncomputable def gevEnv (a b u : ℝ) : ℝ := u ^ (-a) + u ^ b

variable {a b c d u v r k : ℝ}

lemma gevEnv_nonneg (hu : 0 ≤ u) : 0 ≤ gevEnv a b u := by unfold gevEnv; positivity

lemma gevEnv_pos (hu : 0 < u) : 0 < gevEnv a b u := by unfold gevEnv; positivity

/-- Every power `u^r` with `-a ≤ r ≤ b` is below the envelope `u^{-a} + u^b`. -/
lemma rpow_le_gevEnv (hu : 0 < u) (h1 : -a ≤ r) (h2 : r ≤ b) : u ^ r ≤ gevEnv a b u := by
  unfold gevEnv
  rcases le_total u 1 with h | h
  · have := rpow_le_rpow_of_exponent_ge hu h h1
    linarith [rpow_pos_of_pos hu b]
  · have := rpow_le_rpow_of_exponent_le h h2
    linarith [rpow_pos_of_pos hu (-a)]

lemma one_le_gevEnv (hu : 0 < u) (ha : 0 ≤ a) (hb : 0 ≤ b) : 1 ≤ gevEnv a b u := by
  simpa using rpow_le_gevEnv (r := 0) hu (by linarith) hb

lemma inv_le_gevEnv (hu : 0 < u) (ha : 1 ≤ a) (hb : 0 ≤ b) : u⁻¹ ≤ gevEnv a b u := by
  simpa [rpow_neg_one] using rpow_le_gevEnv (r := -1) hu (by linarith) (by linarith)

lemma self_le_gevEnv (hu : 0 < u) (ha : 0 ≤ a) (hb : 1 ≤ b) : u ≤ gevEnv a b u := by
  simpa using rpow_le_gevEnv (r := 1) hu (by linarith) hb

/-- Products of envelopes. -/
lemma gevEnv_mul_le (hu : 0 < u) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    gevEnv a b u * gevEnv c d u ≤ 3 * gevEnv (a + c) (b + d) u := by
  have e1 : u ^ (-a) * u ^ (-c) = u ^ (-(a + c)) := by rw [← rpow_add hu]; ring_nf
  have e2 : u ^ (-a) * u ^ d = u ^ (-a + d) := (rpow_add hu _ _).symm
  have e3 : u ^ b * u ^ (-c) = u ^ (b + -c) := (rpow_add hu _ _).symm
  have e4 : u ^ b * u ^ d = u ^ (b + d) := (rpow_add hu _ _).symm
  have h2 := rpow_le_gevEnv (a := a + c) (b := b + d) (r := -a + d) hu (by linarith)
    (by linarith)
  have h3 := rpow_le_gevEnv (a := a + c) (b := b + d) (r := b + -c) hu (by linarith)
    (by linarith)
  have : gevEnv a b u * gevEnv c d u =
      u ^ (-(a + c)) + u ^ (-a + d) + u ^ (b + -c) + u ^ (b + d) := by
    unfold gevEnv; rw [← e1, ← e2, ← e3, ← e4]; ring
  rw [this]
  unfold gevEnv at h2 h3 ⊢
  linarith

/-- Monotonicity of the envelopes in the exponents. -/
lemma gevEnv_le_of_le (hu : 0 < u) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) :
    gevEnv a b u ≤ 2 * gevEnv c d u := by
  have h1 := rpow_le_gevEnv (a := c) (b := d) (r := -a) hu (by linarith) (by linarith)
  have h2 := rpow_le_gevEnv (a := c) (b := d) (r := b) hu (by linarith) hbd
  unfold gevEnv at h1 h2 ⊢
  linarith

/-- Envelopes at comparable points: if `v/k ≤ u ≤ k v`, `k ≥ 1`, then
`gevEnv a b u ≤ k^{a + b} gevEnv a b v`. -/
lemma gevEnv_le_of_comparable (hv : 0 < v) (hk : 1 ≤ k) (h1 : v / k ≤ u) (h2 : u ≤ k * v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : gevEnv a b u ≤ k ^ (a + b) * gevEnv a b v := by
  have hk0 : 0 < k := by linarith
  have hvk : 0 < v / k := by positivity
  have h3 : u ^ (-a) ≤ (v / k) ^ (-a) := rpow_le_rpow_of_nonpos hvk h1 (by linarith)
  have h4 : u ^ b ≤ (k * v) ^ b := rpow_le_rpow (by linarith) h2 hb
  rw [div_rpow hv.le hk0.le, rpow_neg hk0.le, div_inv_eq_mul] at h3
  rw [mul_rpow hk0.le hv.le] at h4
  have h5 : k ^ a ≤ k ^ (a + b) := rpow_le_rpow_of_exponent_le hk (by linarith)
  have h6 : k ^ b ≤ k ^ (a + b) := rpow_le_rpow_of_exponent_le hk (by linarith)
  have h7 : 0 ≤ v ^ (-a) := by positivity
  have h8 : 0 ≤ v ^ b := by positivity
  unfold gevEnv
  nlinarith

/-- `|log u| ≤ (u^{-ε} + u^ε)/ε`. -/
lemma abs_log_le_gevEnv {ε : ℝ} (hε : 0 < ε) (hu : 0 < u) : |log u| ≤ gevEnv ε ε u / ε := by
  have := abs_log_le_rpow_add_rpow hε hu
  unfold gevEnv
  rwa [add_comm (u ^ (-ε))]

lemma measurable_gevEnv_comp {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun x => gevEnv a b (f x) := by
  unfold gevEnv; fun_prop

end Env

/-! ### Integrability of the envelopes under the GEV law -/

section Integrability

variable {ξ μ σ a b : ℝ}

lemma measurable_gevEnv_gevU (a b ξ μ σ : ℝ) :
    Measurable fun x => gevEnv a b (gevU ξ μ σ x) :=
  measurable_gevEnv_comp (measurable_gevU ξ μ σ)

/-- **The envelopes are integrable under the GEV law**: on the exponential scale
`u = 1 + ξ (x - μ)/σ = t^{-ξ}`, so `u^{-a} + u^b = t^{a ξ} + t^{-b ξ}`, integrable against
`e^{-t}` when `-1 < a ξ` and `b ξ < 1`. -/
theorem integrable_gevEnv (hξ : ξ ≠ 0) (hσ : 0 < σ) (ha : -1 < a * ξ) (hb : b * ξ < 1) :
    Integrable (fun x => gevEnv a b (gevU ξ μ σ x)) (gevLocScaleCDF ξ μ hσ).measure := by
  rw [integrable_gevLocScaleCDF_iff hσ (measurable_gevEnv_gevU a b ξ μ σ)]
  have h1 := integrableOn_exp_neg_mul_rpow (a := a * ξ) ha
  have h2 := integrableOn_exp_neg_mul_rpow (a := -(b * ξ)) (by linarith)
  refine (h1.add h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht : 0 < t := ht
  simp only [Pi.add_apply, gevU_transform hσ hξ ht, gevEnv, ← rpow_mul ht.le]
  ring_nf

/-- **The observations lie in the support almost surely**: `u(θ₀, X) > 0` a.s. -/
theorem ae_gevU_pos (hξ : ξ ≠ 0) (hσ : 0 < σ) :
    ∀ᵐ x ∂(gevLocScaleCDF ξ μ hσ).measure, 0 < gevU ξ μ σ x := by
  rw [measure_gevLocScaleCDF_eq_map, ae_map_iff (measurable_affine_gevTransform ξ μ σ).aemeasurable
    (measurableSet_lt measurable_const (measurable_gevU ξ μ σ))]
  filter_upwards [ae_pos_expMeasure] with t ht
  rw [gevU_transform hσ hξ ht]
  exact rpow_pos_of_pos ht _

end Integrability

end ExtremeValueTheory
