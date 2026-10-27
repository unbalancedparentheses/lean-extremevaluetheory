/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVHessian

/-!
# Envelopes for the GEV likelihood near a moving endpoint

The asymptotic normality of the three-parameter GEV maximum likelihood estimator needs bounds on
the log-likelihood, the score and the Hessian at parameters `θ` near the true parameter
`θ₀ = (ξ₀, μ₀, σ₀)`, uniformly in the data, by functions which are integrable under the true law.
The support `{u > 0}`, `u = 1 + ξ (x - μ)/σ`, moves with the parameter, so no such bound can hold
for every observation; it holds for the observations which are *good* for `θ`:

  `ρ(θ) (1 + 1/u₀(x)) ≤ c₀`, `ρ(θ) = |ξ - ξ₀| + |μ - μ₀| + |σ - σ₀|`, `u₀ = u(θ₀, ·)`.

For good observations `u(θ, x)` is comparable to `u₀(x)`, within a factor `3`
(`gevU_comparable`). All the quantities are then bounded by the **envelopes**
`gevEnv a b u₀ = u₀^{-a} + u₀^b` (`rpow_le_gevEnv`, `gevEnv_mul_le`), which are integrable under
the true law exactly when `-1 < a ξ₀` and `b ξ₀ < 1` (`integrable_gevEnv`: on the exponential
scale `u₀ = t^{-ξ₀}`).

## Main results

* `gevEnv`, `rpow_le_gevEnv`, `one_le_gevEnv`, `gevEnv_mul_le`, `gevEnv_le_of_le`,
  `gevEnv_le_of_comparable`, `abs_log_le_gevEnv`: the envelope calculus.
* `integrable_gevEnv`: integrability of the envelopes under the GEV law.
* `ae_gevU_pos`: the observations lie in the support almost surely.
* `gevU_comparable`: for good observations, `u₀/3 ≤ u(θ, x) ≤ 3 u₀`, `|ξ - ξ₀| ≤ |ξ₀|/2`,
  `|σ - σ₀| ≤ σ₀/2`.

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
  have : ∀ᵐ t ∂stdExpMeasure, t ∈ Ioi (0 : ℝ) := by
    rw [stdExpMeasure]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [this] with t ht
  rw [gevU_transform hσ hξ ht]
  exact rpow_pos_of_pos ht _

end Integrability

/-! ### Comparability of the supports for good observations -/

section Comparable

/-- The `ℓ¹` distance `ρ(θ) = |ξ - ξ₀| + |μ - μ₀| + |σ - σ₀|` of the parameters. -/
noncomputable def gevDist (θ₀ θ : ℝ × ℝ × ℝ) : ℝ :=
  |θ.1 - θ₀.1| + |θ.2.1 - θ₀.2.1| + |θ.2.2 - θ₀.2.2|

lemma gevDist_nonneg (θ₀ θ : ℝ × ℝ × ℝ) : 0 ≤ gevDist θ₀ θ := by unfold gevDist; positivity

lemma gevDist_self (θ₀ : ℝ × ℝ × ℝ) : gevDist θ₀ θ₀ = 0 := by simp [gevDist]

/-- The constant `K₁ = 1 + σ₀/|ξ₀| + 2|ξ₀|` in `|σ u - σ₀ u₀| ≤ ρ K₁ (1 + u₀)`. -/
noncomputable def gevK₁ (ξ₀ σ₀ : ℝ) : ℝ := 1 + σ₀ / |ξ₀| + 2 * |ξ₀|

/-- The goodness threshold `c₀ = σ₀/(2 K₁)`: an observation `x` is good for `θ` when
`ρ(θ) (1 + 1/u₀(x)) ≤ c₀`. -/
noncomputable def gevC₀ (ξ₀ σ₀ : ℝ) : ℝ := σ₀ / (2 * gevK₁ ξ₀ σ₀)

variable {ξ₀ μ₀ σ₀ : ℝ}

lemma one_le_gevK₁ (hσ₀ : 0 < σ₀) : 1 ≤ gevK₁ ξ₀ σ₀ := by
  unfold gevK₁; have : 0 ≤ σ₀ / |ξ₀| := by positivity
  linarith [abs_nonneg ξ₀]

lemma gevC₀_pos (hσ₀ : 0 < σ₀) : 0 < gevC₀ ξ₀ σ₀ := by
  have := one_le_gevK₁ (ξ₀ := ξ₀) hσ₀
  unfold gevC₀; positivity

lemma gevC₀_le_sigma (hσ₀ : 0 < σ₀) : gevC₀ ξ₀ σ₀ ≤ σ₀ / 2 := by
  have := one_le_gevK₁ (ξ₀ := ξ₀) hσ₀
  unfold gevC₀
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma gevC₀_le_xi (hξ₀ : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) : gevC₀ ξ₀ σ₀ ≤ |ξ₀| / 2 := by
  have ha : 0 < |ξ₀| := abs_pos.2 hξ₀
  have := one_le_gevK₁ (ξ₀ := ξ₀) hσ₀
  unfold gevC₀ gevK₁
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have e : σ₀ / |ξ₀| * |ξ₀| = σ₀ := div_mul_cancel₀ _ ha.ne'
  nlinarith [abs_nonneg ξ₀, mul_pos ha ha]

/-- `σ u(θ, x) = σ + ξ (x - μ)`. -/
lemma mul_gevU {ξ μ σ x : ℝ} (hσ : σ ≠ 0) : σ * gevU ξ μ σ x = σ + ξ * (x - μ) := by
  unfold gevU; field_simp

/-- **Comparability of the supports for good observations.** If `u₀ = u(θ₀, x) > 0` and
`ρ(θ) (1 + 1/u₀) ≤ c₀`, then `|ξ - ξ₀| ≤ |ξ₀|/2`, `|σ - σ₀| ≤ σ₀/2` and
`u₀/3 ≤ u(θ, x) ≤ 3 u₀`. -/
theorem gevU_comparable (hξ₀ : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ × ℝ} {x : ℝ}
    (hu₀ : 0 < gevU ξ₀ μ₀ σ₀ x)
    (hgood : gevDist (ξ₀, μ₀, σ₀) θ * (1 + (gevU ξ₀ μ₀ σ₀ x)⁻¹) ≤ gevC₀ ξ₀ σ₀) :
    |θ.1 - ξ₀| ≤ |ξ₀| / 2 ∧ |θ.2.2 - σ₀| ≤ σ₀ / 2 ∧
      gevU ξ₀ μ₀ σ₀ x / 3 ≤ gevU θ.1 θ.2.1 θ.2.2 x ∧
      gevU θ.1 θ.2.1 θ.2.2 x ≤ 3 * gevU ξ₀ μ₀ σ₀ x := by
  obtain ⟨ξ, μ, σ⟩ := θ
  set u₀ := gevU ξ₀ μ₀ σ₀ x with hu₀_def
  set ρ := gevDist (ξ₀, μ₀, σ₀) (ξ, μ, σ) with hρ_def
  have hρ0 : 0 ≤ ρ := gevDist_nonneg _ _
  have hc₀ := gevC₀_pos (ξ₀ := ξ₀) hσ₀
  have hρc : ρ ≤ gevC₀ ξ₀ σ₀ := by
    have : ρ ≤ ρ * (1 + u₀⁻¹) := by
      have : 0 ≤ u₀⁻¹ := by positivity
      nlinarith
    linarith
  have hd1 : |ξ - ξ₀| ≤ ρ := by
    simp only [hρ_def, gevDist]; linarith [abs_nonneg (μ - μ₀), abs_nonneg (σ - σ₀)]
  have hd2 : |μ - μ₀| ≤ ρ := by
    simp only [hρ_def, gevDist]; linarith [abs_nonneg (ξ - ξ₀), abs_nonneg (σ - σ₀)]
  have hd3 : |σ - σ₀| ≤ ρ := by
    simp only [hρ_def, gevDist]; linarith [abs_nonneg (μ - μ₀), abs_nonneg (ξ - ξ₀)]
  have hξ1 : |ξ - ξ₀| ≤ |ξ₀| / 2 := hd1.trans (hρc.trans (gevC₀_le_xi hξ₀ hσ₀))
  have hσ1 : |σ - σ₀| ≤ σ₀ / 2 := hd3.trans (hρc.trans (gevC₀_le_sigma hσ₀))
  refine ⟨hξ1, hσ1, ?_⟩
  simp only
  have hσlo : σ₀ / 2 ≤ σ := by have := neg_abs_le (σ - σ₀); linarith
  have hσhi : σ ≤ 3 * σ₀ / 2 := by have := le_abs_self (σ - σ₀); linarith
  have hσ : 0 < σ := by linarith
  have ha0 : 0 < |ξ₀| := abs_pos.2 hξ₀
  -- `|x - μ₀| ≤ σ₀ (1 + u₀)/|ξ₀|`
  have hxμ : |x - μ₀| ≤ σ₀ * (1 + u₀) / |ξ₀| := by
    have e : x - μ₀ = σ₀ * (u₀ - 1) / ξ₀ := by
      simp only [hu₀_def, gevU]; field_simp; ring
    rw [e, abs_div, abs_mul, abs_of_pos hσ₀]
    gcongr
    rw [abs_le]; constructor <;> linarith
  have hξabs : |ξ| ≤ 2 * |ξ₀| := by
    have := abs_sub_abs_le_abs_sub ξ ξ₀
    linarith
  -- `|σ u - σ₀ u₀| ≤ ρ K₁ (1 + u₀)`
  have hD : |σ * gevU ξ μ σ x - σ₀ * u₀| ≤ ρ * gevK₁ ξ₀ σ₀ * (1 + u₀) := by
    rw [hu₀_def, mul_gevU hσ.ne', mul_gevU hσ₀.ne']
    have e : σ + ξ * (x - μ) - (σ₀ + ξ₀ * (x - μ₀)) =
        (σ - σ₀) + (ξ - ξ₀) * (x - μ₀) - ξ * (μ - μ₀) := by ring
    rw [e]
    have t1 : |(ξ - ξ₀) * (x - μ₀)| ≤ ρ * (σ₀ * (1 + u₀) / |ξ₀|) := by
      rw [abs_mul]; exact mul_le_mul hd1 hxμ (abs_nonneg _) hρ0
    have t2 : |ξ * (μ - μ₀)| ≤ 2 * |ξ₀| * ρ := by
      rw [abs_mul]; exact mul_le_mul hξabs hd2 (abs_nonneg _) (by positivity)
    have a1 := le_abs_self (σ - σ₀)
    have a2 := neg_abs_le (σ - σ₀)
    have b1 := le_abs_self ((ξ - ξ₀) * (x - μ₀))
    have b2 := neg_abs_le ((ξ - ξ₀) * (x - μ₀))
    have c1 := le_abs_self (ξ * (μ - μ₀))
    have c2 := neg_abs_le (ξ * (μ - μ₀))
    have hu0' : 0 ≤ u₀ := hu₀.le
    have e2 : ρ * (σ₀ * (1 + u₀) / |ξ₀|) = ρ * (σ₀ / |ξ₀|) * (1 + u₀) := by ring
    have hK : ρ * gevK₁ ξ₀ σ₀ * (1 + u₀) =
        ρ * (1 + u₀) + ρ * (σ₀ / |ξ₀|) * (1 + u₀) + 2 * |ξ₀| * ρ * (1 + u₀) := by
      unfold gevK₁; ring
    have h4 : ρ ≤ ρ * (1 + u₀) := by nlinarith
    have h5 : 2 * |ξ₀| * ρ ≤ 2 * |ξ₀| * ρ * (1 + u₀) := by
      have : 0 ≤ 2 * |ξ₀| * ρ := by positivity
      nlinarith
    rw [hK, abs_le]
    constructor <;> linarith
  -- `ρ K₁ (1 + u₀) ≤ σ₀ u₀ / 2`
  have hK1 := one_le_gevK₁ (ξ₀ := ξ₀) hσ₀
  have hR : ρ * gevK₁ ξ₀ σ₀ * (1 + u₀) ≤ σ₀ * u₀ / 2 := by
    have e : ρ * gevK₁ ξ₀ σ₀ * (1 + u₀) = gevK₁ ξ₀ σ₀ * u₀ * (ρ * (1 + u₀⁻¹)) := by
      field_simp
      ring
    rw [e]
    calc gevK₁ ξ₀ σ₀ * u₀ * (ρ * (1 + u₀⁻¹)) ≤ gevK₁ ξ₀ σ₀ * u₀ * gevC₀ ξ₀ σ₀ :=
          mul_le_mul_of_nonneg_left hgood (by positivity)
      _ = σ₀ * u₀ / 2 := by unfold gevC₀; field_simp
  rw [abs_le] at hD
  have hlo : σ₀ * u₀ / 2 ≤ σ * gevU ξ μ σ x := by linarith
  have hhi : σ * gevU ξ μ σ x ≤ 3 * (σ₀ * u₀) / 2 := by linarith
  constructor
  · by_contra h
    push Not at h
    have : σ * gevU ξ μ σ x < σ * (u₀ / 3) := mul_lt_mul_of_pos_left h hσ
    nlinarith
  · by_contra h
    push Not at h
    have : σ * (3 * u₀) < σ * gevU ξ μ σ x := mul_lt_mul_of_pos_left h hσ
    nlinarith

end Comparable

end ExtremeValueTheory
