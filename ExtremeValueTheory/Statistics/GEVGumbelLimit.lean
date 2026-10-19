/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVHessian

/-!
# The Gumbel case `ξ = 0` of the GEV likelihood

TODO
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### A second-order expansion of the logarithm -/

section Log1pQuad

/-- `(log(1 + t) - t/(1 + t))/t²`, extended by `1/2` at `t = 0`. -/
noncomputable def log1pQuad (t : ℝ) : ℝ :=
  if t = 0 then 1 / 2 else (log (1 + t) - t / (1 + t)) / t ^ 2

lemma log1pQuad_of_ne {t : ℝ} (ht : t ≠ 0) :
    log1pQuad t = (log (1 + t) - t / (1 + t)) / t ^ 2 := by
  simp [log1pQuad, ht]

/-- `|log1pQuad t - 1/2| ≤ 4 |t|` for `|t| ≤ 1/2`. -/
lemma abs_log1pQuad_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |log1pQuad t - 1 / 2| ≤ 4 * |t| := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [log1pQuad]
  have hlt : |-t| < 1 := by rw [abs_neg]; linarith
  have hT := abs_log_sub_add_sum_range_le hlt 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hT
  norm_num at hT
  have h1t : 1 / 2 ≤ 1 + t := by linarith [neg_abs_le t]
  have hpos : 0 < 1 + t := by linarith
  have habs : 0 < |t| := abs_pos.2 h0
  have hden : 1 / 2 ≤ 1 - |t| := by linarith
  have hT' : |log (1 + t) - t + t ^ 2 / 2| ≤ 2 * |t| ^ 3 := by
    have e : log (1 + t) - t + t ^ 2 / 2 = -t + t ^ 2 / 2 + log (1 + t) := by ring
    rw [e]
    calc _ ≤ |t| ^ 3 / (1 - |t|) := by simpa [add_comm] using hT
      _ ≤ |t| ^ 3 / (1 / 2) := by gcongr
      _ = 2 * |t| ^ 3 := by ring
  have hR : |t ^ 3 / (1 + t)| ≤ 2 * |t| ^ 3 := by
    rw [abs_div, abs_of_pos hpos, abs_pow, div_le_iff₀ hpos]
    nlinarith [pow_pos habs 3]
  have e : log1pQuad t - 1 / 2 =
      ((log (1 + t) - t + t ^ 2 / 2) - t ^ 3 / (1 + t)) / t ^ 2 := by
    rw [log1pQuad_of_ne h0]
    field_simp
    ring
  rw [e, abs_div, abs_pow, div_le_iff₀ (by positivity)]
  calc |log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / (1 + t)|
      ≤ |log (1 + t) - t + t ^ 2 / 2| + |t ^ 3 / (1 + t)| := abs_sub _ _
    _ ≤ 2 * |t| ^ 3 + 2 * |t| ^ 3 := add_le_add hT' hR
    _ = 4 * |t| * |t| ^ 2 := by ring

lemma continuousAt_log1pQuad_zero : ContinuousAt log1pQuad 0 := by
  rw [ContinuousAt, show log1pQuad 0 = 1 / 2 by simp [log1pQuad]]
  have h : Tendsto (fun t => log1pQuad t - 1 / 2) (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul 4)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    rw [Real.norm_eq_abs]
    have ht' := Metric.mem_ball.1 ht
    rw [dist_zero_right, Real.norm_eq_abs] at ht'
    exact abs_log1pQuad_sub_le ht'.le
  have := h.add_const (1 / 2)
  simp only [sub_add_cancel, zero_add] at this
  exact this

end Log1pQuad

/-! ### Derivatives at a point from the limit of the derivative -/

/-- If `f` is differentiable on a punctured neighbourhood of `a`, continuous at `a`, and its
derivative `g` converges at `a`, then `f` is differentiable at `a` with derivative the limit. -/
theorem hasDerivAt_of_tendsto_punctured {f g : ℝ → ℝ} {a e : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 a)
    (hd : ∀ y ∈ U, y ≠ a → HasDerivAt f (g y) y) (hf : ContinuousAt f a)
    (hg : Tendsto g (𝓝[≠] a) (𝓝 e)) : HasDerivAt f e a := by
  set s := U \ {a}
  have hdiff : DifferentiableOn ℝ f s := fun y hy =>
    (hd y hy.1 hy.2).differentiableAt.differentiableWithinAt
  have hderiv : ∀ᶠ y in 𝓝[≠] a, deriv f y = g y := by
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with y hy hya
    exact (hd y hy hya).deriv
  have hlim : Tendsto (fun y => deriv f y) (𝓝[≠] a) (𝓝 e) := hg.congr' (hderiv.mono fun _ h => h.symm)
  have hs_gt : s ∈ 𝓝[>] a :=
    mem_of_superset (inter_mem_nhdsWithin _ hU) fun y hy => ⟨hy.2, ne_of_gt hy.1⟩
  have hs_lt : s ∈ 𝓝[<] a :=
    mem_of_superset (inter_mem_nhdsWithin _ hU) fun y hy => ⟨hy.2, ne_of_lt hy.1⟩
  have h1 := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hf.continuousWithinAt hs_gt
    (hlim.mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy))
  have h2 := hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hf.continuousWithinAt hs_lt
    (hlim.mono_left (nhdsWithin_mono _ fun y hy => ne_of_lt hy))
  have := h2.union h1
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-! ### The Gumbel scores and the limits of the GEV scores as `ξ → 0` -/

section ScoreLimits

variable {ξ μ σ x : ℝ}

/-- The Gumbel location score `∂_μ ℓ = (1 - e^{-z})/σ`, `z = (x - μ)/σ`. -/
noncomputable def gumbelScoreMu (μ σ x : ℝ) : ℝ := (1 - exp (-((x - μ) / σ))) / σ

/-- The Gumbel scale score `∂_σ ℓ = (-1 + z (1 - e^{-z}))/σ`. -/
noncomputable def gumbelScoreSigma (μ σ x : ℝ) : ℝ :=
  (-1 + (x - μ) / σ * (1 - exp (-((x - μ) / σ)))) / σ

/-- The shape score of the GEV family at `ξ = 0`: `∂_ξ ℓ = -z + z² (1 - e^{-z})/2`. -/
noncomputable def gumbelScoreXi (μ σ x : ℝ) : ℝ :=
  -((x - μ) / σ) + ((x - μ) / σ) ^ 2 * (1 - exp (-((x - μ) / σ))) / 2

lemma measurable_gumbelScoreMu (μ σ : ℝ) : Measurable (gumbelScoreMu μ σ) := by
  unfold gumbelScoreMu; fun_prop

lemma measurable_gumbelScoreSigma (μ σ : ℝ) : Measurable (gumbelScoreSigma μ σ) := by
  unfold gumbelScoreSigma; fun_prop

lemma measurable_gumbelScoreXi (μ σ : ℝ) : Measurable (gumbelScoreXi μ σ) := by
  unfold gumbelScoreXi; fun_prop

/-- `u^{-1/ξ} = exp(-z λ(ξ z))` inside the support. -/
lemma one_add_mul_rpow_eq_exp {z : ℝ} (hξ : ξ ≠ 0) (hu : 0 < 1 + ξ * z) :
    (1 + ξ * z) ^ (-1 / ξ) = exp (-(z * log1pDiv (ξ * z))) := by
  rw [rpow_def_of_pos hu, mul_log1pDiv_eq hξ hu]
  congr 1
  ring

/-- Near `ξ = 0` the point `z` is in the support. -/
lemma eventually_one_add_mul_pos (z : ℝ) : ∀ᶠ k in 𝓝 (0 : ℝ), 0 < 1 + k * z :=
  ((continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ)).eventually
    (lt_mem_nhds (by simp))

lemma tendsto_one_add_mul_rpow (z : ℝ) :
    Tendsto (fun k => (1 + k * z) ^ (-1 / k)) (𝓝[≠] 0) (𝓝 (exp (-z))) := by
  have hc : ContinuousAt (fun k => exp (-(z * log1pDiv (k * z)))) 0 := by
    have : ContinuousAt (fun k : ℝ => log1pDiv (k * z)) 0 :=
      ContinuousAt.comp (g := log1pDiv) (by simpa using continuousAt_log1pDiv_zero)
        (continuous_id.mul continuous_const).continuousAt
    exact (continuous_exp.continuousAt).comp ((continuousAt_const.mul this).neg)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [zero_mul, log1pDiv_zero, mul_one] at h
  refine h.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (eventually_one_add_mul_pos z), self_mem_nhdsWithin]
    with k hk hk0
  exact (one_add_mul_rpow_eq_exp hk0 hk).symm

lemma tendsto_nhdsNE_id : Tendsto (fun k : ℝ => k) (𝓝[≠] 0) (𝓝 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

lemma tendsto_one_add_mul (z : ℝ) : Tendsto (fun k : ℝ => 1 + k * z) (𝓝[≠] 0) (𝓝 1) := by
  simpa using (tendsto_nhdsNE_id.mul_const z).const_add 1

/-- **Continuity of the location score at `ξ = 0`**: `∂_μ ℓ_ξ(x) → ∂_μ ℓ_0(x)`. -/
theorem tendsto_gevScoreMu_zero (hσ : 0 < σ) :
    Tendsto (fun k => gevScoreMu k μ σ x) (𝓝[≠] 0) (𝓝 (gumbelScoreMu μ σ x)) := by
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_nhdsNE_id).sub
    (tendsto_one_add_mul_rpow ((x - μ) / σ))).div
    ((tendsto_one_add_mul ((x - μ) / σ)).const_mul σ) (by simp [hσ.ne'])
  rw [show gumbelScoreMu μ σ x = (1 + 0 - exp (-((x - μ) / σ))) / (σ * 1) by
    simp [gumbelScoreMu]]
  exact h

/-- **Continuity of the scale score at `ξ = 0`**. -/
theorem tendsto_gevScoreSigma_zero :
    Tendsto (fun k => gevScoreSigma k μ σ x) (𝓝[≠] 0) (𝓝 (gumbelScoreSigma μ σ x)) := by
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (((tendsto_const_nhds (x := (x - μ) / σ)).mul
    (((tendsto_one_add_mul_rpow ((x - μ) / σ)).sub_const 1).sub tendsto_nhdsNE_id)).div
    (tendsto_one_add_mul ((x - μ) / σ)) one_ne_zero)).neg).div_const σ
  simp only [sub_zero, div_one] at h
  convert h using 2
  · rfl
  · rw [gumbelScoreSigma]; ring

/-- The shape score through the second-order expansion `log1pQuad`. -/
lemma gevScoreXi_eq_log1pQuad (hξ : ξ ≠ 0) (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    gevScoreXi ξ μ σ x = (1 - (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ)) *
      (((x - μ) / σ) ^ 2 * log1pQuad (ξ * ((x - μ) / σ))) -
      (x - μ) / σ / (1 + ξ * ((x - μ) / σ)) := by
  set z := (x - μ) / σ with hz
  rw [gevScoreXi, ← hz]
  rcases eq_or_ne z 0 with h0 | h0
  · simp [h0]
  rw [log1pQuad_of_ne (mul_ne_zero hξ h0)]
  have hu' := hu.ne'
  field_simp
  ring

/-- **Continuity of the shape score at `ξ = 0`**: `∂_ξ ℓ_ξ(x) → -z + z² (1 - e^{-z})/2`. -/
theorem tendsto_gevScoreXi_zero :
    Tendsto (fun k => gevScoreXi k μ σ x) (𝓝[≠] 0) (𝓝 (gumbelScoreXi μ σ x)) := by
  set z := (x - μ) / σ with hz
  have hq : Tendsto (fun k : ℝ => log1pQuad (k * z)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have : ContinuousAt (fun k : ℝ => log1pQuad (k * z)) 0 :=
      ContinuousAt.comp (g := log1pQuad) (by simpa using continuousAt_log1pQuad_zero)
        (continuous_id.mul continuous_const).continuousAt
    simpa [log1pQuad] using this.tendsto.mono_left nhdsWithin_le_nhds
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_one_add_mul_rpow z)).mul
    ((tendsto_const_nhds (x := z ^ 2)).mul hq)).sub
    ((tendsto_const_nhds (x := z)).div (tendsto_one_add_mul z) one_ne_zero)
  have heq : (fun k => (1 - (1 + k * z) ^ (-1 / k)) * (z ^ 2 * log1pQuad (k * z)) -
      z / (1 + k * z)) =ᶠ[𝓝[≠] 0] fun k => gevScoreXi k μ σ x := by
    filter_upwards [nhdsWithin_le_nhds (eventually_one_add_mul_pos z), self_mem_nhdsWithin]
      with k hk hk0
    rw [gevScoreXi_eq_log1pQuad hk0 (by rw [← hz]; linarith [hk.le, mul_comm k z]), ← hz]
  refine (h.congr' heq).trans (le_of_eq ?_)
  congr 1
  rw [gumbelScoreXi, ← hz]
  ring

end ScoreLimits

end ExtremeValueTheory
