/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVHessian

/-!
# The Gumbel case `ξ = 0` of the GEV likelihood

The GEV (resp. GPD) likelihood is defined piecewise, with the Gumbel (resp. exponential) law at
`ξ = 0`. We show that the log-density and the scores are continuous in `ξ` at `0`, so the
`ξ = 0` model is the continuous extension of the `ξ ≠ 0` one, and that the shape score at `0` is
the genuine derivative of the log-density there. With `z = (x - μ)/σ`:

* `∂_μ ℓ_0 = (1 - e^{-z})/σ`, `∂_σ ℓ_0 = (-1 + z(1 - e^{-z}))/σ` (`gumbelScoreMu`,
  `gumbelScoreSigma`), `∂_ξ ℓ|_{ξ=0} = -z + z²(1 - e^{-z})/2` (`gumbelScoreXi`);
* for the GPD, `∂_σ ℓ_0 = (x/σ - 1)/σ`, `∂_ξ ℓ|_{ξ=0} = (x/σ)²/2 - x/σ` (`expScoreSigma`,
  `expScoreXi`).

The key analytic input is the second-order expansion `log1pQuad`:
`(log(1 + t) - t/(1 + t))/t² → 1/2` (`continuousAt_log1pQuad_zero`), which resolves the `0/0`
in the shape score.

## Main results

* `tendsto_gevScoreMu_zero`, `tendsto_gevScoreSigma_zero`, `tendsto_gevScoreXi_zero`,
  `continuousAt_log_gevLocScaleDensity_xi_zero`: continuity at `ξ = 0`.
* `hasDerivAt_log_gevLocScaleDensity_xi_zero` (via `hasDerivAt_of_tendsto_punctured`),
  `hasDerivAt_log_gevLocScaleDensity_zero_mu`, `hasDerivAt_log_gevLocScaleDensity_zero_sigma`:
  the Gumbel scores are the derivatives of the log-density at `ξ = 0`.
* `integral_lin_gumbelScore`: all three scores have mean zero at `ξ = 0`.
* `gumbelFisherInfo`, `integral_lin_gumbelScore_sq`, `posDef_gumbelFisherInfo`: **the Gumbel
  Fisher information** `[[1, -(1 - γ)], [-(1 - γ), π²/6 + (1 - γ)²]]/σ²`, positive definite
  (determinant `π²/(6σ⁴)`).
* `integral_gumbelScoreMu_mul_gumbelScoreXi`: the location–shape entry at `ξ = 0`,
  `((1 - γ)² + π²/6 - 1)/(2σ)`.
* `tendstoInDistribution_gumbelScoreVec`: the bivariate Gumbel score CLT.
* `tendsto_gpdScoreSigma_zero`, `tendsto_gpdScoreXi_zero`, `continuousAt_log_gpdDensity_xi_zero`,
  `hasDerivAt_log_gpdDensity_xi_zero`: the same for the GPD.

## Not covered

The scale–shape and shape–shape entries of the information at `ξ = 0` involve
`E[(log T)³ ...]`, `E[(log T)⁴ ...]`, i.e. `Γ'''` and `Γ''''` at `1, 2, 3`, hence `ζ(3)`; they
are not formalized. Neither is the continuity of the Hessian in `ξ` at `0` (a third-order
expansion), nor the asymptotic normality of the MLE at `ξ = 0`.
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

/-! ### The log-density and its derivatives at `ξ = 0` -/

section AtZero

variable {μ σ x : ℝ}

/-- **Continuity of the GEV log-density in the shape at `ξ = 0`.** -/
theorem continuousAt_log_gevLocScaleDensity_xi_zero (hσ : 0 < σ) :
    ContinuousAt (fun k => log (gevLocScaleDensity k μ σ x)) 0 := by
  have hd : ContinuousAt (fun k => gevDensity k ((x - μ) / σ)) 0 :=
    ContinuousAt.comp (g := fun q : ℝ × ℝ => gevDensity q.1 q.2)
      (f := fun k : ℝ => (k, (x - μ) / σ)) (x := 0)
      (continuousAt_gevDensity (q := (0, (x - μ) / σ)) (by norm_num)) (by fun_prop)
  have hpos : gevLocScaleDensity 0 μ σ x ≠ 0 := by
    simp only [gevLocScaleDensity, gevDensity, ↓reduceIte]
    exact (mul_pos (inv_pos.2 hσ) (mul_pos (exp_pos _) (exp_pos _))).ne'
  exact (continuousAt_const.mul hd).log hpos

/-- **The Gumbel shape score is the derivative of the GEV log-density in `ξ` at `ξ = 0`.**
(Differentiability on a punctured neighbourhood, continuity of the log-density and of the score
at `0`.) -/
theorem hasDerivAt_log_gevLocScaleDensity_xi_zero (hσ : 0 < σ) :
    HasDerivAt (fun k => log (gevLocScaleDensity k μ σ x)) (gumbelScoreXi μ σ x) 0 :=
  hasDerivAt_of_tendsto_punctured (eventually_one_add_mul_pos ((x - μ) / σ))
    (fun _ hy hy0 => hasDerivAt_log_gevLocScaleDensity_xi hσ hy0 hy)
    (continuousAt_log_gevLocScaleDensity_xi_zero hσ) tendsto_gevScoreXi_zero

/-- The Gumbel location score is the derivative of the Gumbel log-density in `μ`. -/
theorem hasDerivAt_log_gevLocScaleDensity_zero_mu (hσ : 0 < σ) :
    HasDerivAt (fun m => log (gevLocScaleDensity 0 m σ x)) (gumbelScoreMu μ σ x) μ := by
  have e : (fun m => log (gevLocScaleDensity 0 m σ x)) =
      fun m => -log σ - (x - m) / σ - exp (-((x - m) / σ)) :=
    funext fun m => log_gevLocScaleDensity_zero hσ
  rw [e]
  have hz : HasDerivAt (fun m => (x - m) / σ) (-1 / σ) μ := by
    simpa [neg_div] using ((hasDerivAt_id μ).const_sub x).div_const σ
  have := ((hasDerivAt_const μ (-log σ)).sub hz).sub (hz.neg.exp)
  refine this.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [gumbelScoreMu]
  field_simp
  ring

/-- The Gumbel scale score is the derivative of the Gumbel log-density in `σ`. -/
theorem hasDerivAt_log_gevLocScaleDensity_zero_sigma (hσ : 0 < σ) :
    HasDerivAt (fun s => log (gevLocScaleDensity 0 μ s x)) (gumbelScoreSigma μ σ x) σ := by
  have e : (fun s => log (gevLocScaleDensity 0 μ s x)) =ᶠ[𝓝 σ]
      fun s => -log s - (x - μ) / s - exp (-((x - μ) / s)) := by
    filter_upwards [lt_mem_nhds hσ] with s hs
    exact log_gevLocScaleDensity_zero hs
  refine HasDerivAt.congr_of_eventuallyEq ?_ e
  have hz : HasDerivAt (fun s => (x - μ) / s) (-((x - μ) / σ) / σ) σ := by
    have := (hasDerivAt_inv hσ.ne').const_mul (x - μ)
    convert this using 1
    · funext s; rw [div_eq_mul_inv]
    · field_simp
  have := (((hasDerivAt_log hσ.ne').neg).sub hz).sub (hz.neg.exp)
  refine this.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [gumbelScoreSigma]
  field_simp
  ring

end AtZero

/-! ### The Gumbel Fisher information -/

section GumbelInformation

open Matrix

variable {μ σ : ℝ}

/-- **The Fisher information of the Gumbel family** in `(μ, σ)`:
`I = [[1, -(1 - γ)], [-(1 - γ), π²/6 + (1 - γ)²]]/σ²`. -/
noncomputable def gumbelFisherInfo (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / σ ^ 2, -(1 - eulerMascheroniConstant) / σ ^ 2;
    -(1 - eulerMascheroniConstant) / σ ^ 2,
      (π ^ 2 / 6 + (1 - eulerMascheroniConstant) ^ 2) / σ ^ 2]

lemma dotProduct_gumbelFisherInfo_mulVec (v : Fin 2 → ℝ) :
    v ⬝ᵥ (gumbelFisherInfo σ *ᵥ v) =
      (v 0 ^ 2 - 2 * (1 - eulerMascheroniConstant) * v 0 * v 1 +
        (π ^ 2 / 6 + (1 - eulerMascheroniConstant) ^ 2) * v 1 ^ 2) / σ ^ 2 := by
  simp [gumbelFisherInfo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

lemma gevTransform_zero (t : ℝ) : gevTransform 0 t = -log t := by simp [gevTransform]

/-- The Gumbel scores on the exponential scale (`z = -log t`). -/
lemma lin_gumbelScore_transform (hσ : 0 < σ) (a b c : ℝ) {t : ℝ} (ht : 0 < t) :
    a * gumbelScoreMu μ σ (μ + σ * gevTransform 0 t) +
        b * gumbelScoreSigma μ σ (μ + σ * gevTransform 0 t) +
        c * gumbelScoreXi μ σ (μ + σ * gevTransform 0 t) =
      (a * (1 - t) + b * (-1 - log t * (1 - t))) / σ + c * (log t + log t ^ 2 * (1 - t) / 2) := by
  have hz : (μ + σ * gevTransform 0 t - μ) / σ = -log t := by
    rw [gevTransform_zero]; field_simp; ring
  rw [gumbelScoreMu, gumbelScoreSigma, gumbelScoreXi, hz, neg_neg, exp_log ht]
  ring

variable (hσ : 0 < σ)
include hσ

/-- **The Gumbel scores have mean zero** (including the shape score at `ξ = 0`). -/
theorem integral_lin_gumbelScore (a b c : ℝ) :
    ∫ x, (a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x + c * gumbelScoreXi μ σ x)
      ∂(gevLocScaleCDF 0 μ hσ).measure = 0 := by
  have hm : Measurable fun x =>
      a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x + c * gumbelScoreXi μ σ x := by
    have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreSigma μ σ
    have := measurable_gumbelScoreXi μ σ; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm (a₀ := (a - b) / σ) (b₀ := -a / σ)
    (c₀ := 0) (a₁ := 0) (b₁ := 0) (c₁ := 0) (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := -b / σ + c)
    (e₀ := b / σ) (f₀ := 0) (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := c / 2) (h₀ := -c / 2) (k₀ := 0)
    fun t ht => by rw [lin_gumbelScore_transform hσ a b c ht, gevLogPoly, gevPoly]; ring]
  field_simp
  ring

/-- **The Gumbel Fisher information** (`μ, σ` block): `E[(a ∂_μ ℓ + b ∂_σ ℓ)²]` is the quadratic
form of `gumbelFisherInfo σ`. -/
theorem integral_lin_gumbelScore_sq (a b : ℝ) :
    ∫ x, (a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x) ^ 2
      ∂(gevLocScaleCDF 0 μ hσ).measure = ![a, b] ⬝ᵥ (gumbelFisherInfo σ *ᵥ ![a, b]) := by
  have hm : Measurable fun x => (a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x) ^ 2 := by
    have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreSigma μ σ; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm (a₀ := (a - b) ^ 2 / σ ^ 2)
    (b₀ := -2 * a * (a - b) / σ ^ 2) (c₀ := a ^ 2 / σ ^ 2) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := -2 * b * (a - b) / σ ^ 2)
    (e₀ := (2 * b * (a - b) + 2 * a * b) / σ ^ 2) (f₀ := -2 * a * b / σ ^ 2) (d₁ := 0) (e₁ := 0)
    (f₁ := 0) (g₀ := b ^ 2 / σ ^ 2) (h₀ := -2 * b ^ 2 / σ ^ 2) (k₀ := b ^ 2 / σ ^ 2)
    fun t ht => by
      have := lin_gumbelScore_transform (μ := μ) hσ a b 0 ht
      simp only [zero_mul, add_zero] at this
      rw [this, gevLogPoly, gevPoly]; field_simp; ring,
    dotProduct_gumbelFisherInfo_mulVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- **The location–shape entry at `ξ = 0`**:
`E[∂_μ ℓ ∂_ξ ℓ] = ((1 - γ)² + π²/6 - 1)/(2σ)`. -/
theorem integral_gumbelScoreMu_mul_gumbelScoreXi :
    ∫ x, gumbelScoreMu μ σ x * gumbelScoreXi μ σ x ∂(gevLocScaleCDF 0 μ hσ).measure =
      ((1 - eulerMascheroniConstant) ^ 2 + π ^ 2 / 6 - 1) / (2 * σ) := by
  have hm : Measurable fun x => gumbelScoreMu μ σ x * gumbelScoreXi μ σ x := by
    have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreXi μ σ; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm (a₀ := 0) (b₀ := 0) (c₀ := 0)
    (a₁ := 0) (b₁ := 0) (c₁ := 0) (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := 1 / σ) (e₀ := -1 / σ)
    (f₀ := 0) (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 1 / (2 * σ)) (h₀ := -1 / σ)
    (k₀ := 1 / (2 * σ))
    fun t ht => by
      have h1 := lin_gumbelScore_transform (μ := μ) hσ 1 0 0 ht
      have h3 := lin_gumbelScore_transform (μ := μ) hσ 0 0 1 ht
      simp only [one_mul, zero_mul, add_zero, zero_add] at h1 h3
      rw [h1, h3, gevLogPoly, gevPoly]; field_simp; ring]
  field_simp
  ring

/-- The Gumbel location and scale scores are square integrable. -/
lemma memLp_lin_gumbelScore (a b : ℝ) :
    MemLp (fun x => a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x) 2
      (gevLocScaleCDF 0 μ hσ).measure := by
  have hm : Measurable fun x => a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x := by
    have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreSigma μ σ; fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact integrable_gevLocScaleCDF_of_logPoly (by norm_num) hσ (hm.pow_const 2)
    (a₀ := (a - b) ^ 2 / σ ^ 2)
    (b₀ := -2 * a * (a - b) / σ ^ 2) (c₀ := a ^ 2 / σ ^ 2) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := -2 * b * (a - b) / σ ^ 2)
    (e₀ := (2 * b * (a - b) + 2 * a * b) / σ ^ 2) (f₀ := -2 * a * b / σ ^ 2) (d₁ := 0) (e₁ := 0)
    (f₁ := 0) (g₀ := b ^ 2 / σ ^ 2) (h₀ := -2 * b ^ 2 / σ ^ 2) (k₀ := b ^ 2 / σ ^ 2)
    fun t ht => by
      have := lin_gumbelScore_transform (μ := μ) hσ a b 0 ht
      simp only [zero_mul, add_zero] at this
      rw [this, gevLogPoly, gevPoly]; field_simp; ring

/-- **The Gumbel Fisher information is positive definite**: its determinant is
`π²/(6σ⁴) > 0`. -/
theorem posDef_gumbelFisherInfo : (gumbelFisherInfo σ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [gumbelFisherInfo]
  · rw [star_trivial, dotProduct_gumbelFisherInfo_mulVec]
    have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    have e : v 0 ^ 2 - 2 * (1 - eulerMascheroniConstant) * v 0 * v 1 +
        (π ^ 2 / 6 + (1 - eulerMascheroniConstant) ^ 2) * v 1 ^ 2 =
        (v 0 - (1 - eulerMascheroniConstant) * v 1) ^ 2 + π ^ 2 / 6 * v 1 ^ 2 := by ring
    rw [e]
    refine div_pos ?_ (by positivity)
    rcases eq_or_ne (v 1) 0 with h1 | h1
    · have h0 : v 0 ≠ 0 := hne.resolve_right (not_not.2 h1)
      rw [h1]
      simp only [mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
    · have : 0 < π ^ 2 / 6 * v 1 ^ 2 :=
        mul_pos (by positivity) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1)))
      nlinarith [sq_nonneg (v 0 - (1 - eulerMascheroniConstant) * v 1)]

end GumbelInformation

/-! ### The Gumbel score CLT -/

section GumbelCLT

open RealInnerProductSpace Matrix

variable {μ σ : ℝ}

/-- The Gumbel location-scale score vector. -/
noncomputable def gumbelScoreVec (μ σ x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[gumbelScoreMu μ σ x, gumbelScoreSigma μ σ x]

lemma measurable_gumbelScoreVec (μ σ : ℝ) : Measurable (gumbelScoreVec μ σ) := by
  unfold gumbelScoreVec
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · simpa using measurable_gumbelScoreMu μ σ
  · simpa using measurable_gumbelScoreSigma μ σ

lemma inner_gumbelScoreVec (x : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ⟪gumbelScoreVec μ σ x, v⟫ = v 0 * gumbelScoreMu μ σ x + v 1 * gumbelScoreSigma μ σ x := by
  simp [gumbelScoreVec, PiLp.inner_apply, Fin.sum_univ_two]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}

/-- **The bivariate score CLT for the Gumbel family**: for iid Gumbel(`μ, σ`) observations,
`n^{-1/2} ∑_{i<n} (∂_μ ℓ, ∂_σ ℓ)(Xᵢ) ⇒ N(0, gumbelFisherInfo σ)`. -/
theorem tendstoInDistribution_gumbelScoreVec (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ hσ).measure P) (hind : iIndepFun X P)
    {Z : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hZ : HasLaw Z (multivariateGaussian 0 (gumbelFisherInfo σ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gumbelScoreVec μ σ (X i ω))
      atTop Z (fun _ => P) P' := by
  refine TendstoInDistribution.of_inner hZ.aemeasurable (fun n => ?_) fun v => ?_
  · have := measurable_gumbelScoreVec μ σ
    have := fun i => (hX i).aemeasurable
    fun_prop
  set f : ℝ → ℝ := fun x => v 0 * gumbelScoreMu μ σ x + v 1 * gumbelScoreSigma μ σ x
  have hf : Measurable f := by
    have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreSigma μ σ
    simp only [f]; fun_prop
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_lin_gumbelScore hσ _ _
  have hint : ∀ g : ℝ → ℝ, Measurable g →
      P[g ∘ X 0] = ∫ x, g x ∂(gevLocScaleCDF 0 μ hσ).measure :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    simpa using integral_lin_gumbelScore (μ := μ) hσ (v 0) (v 1) 0
  have hvar : Var[Y 0; P] = v ⬝ᵥ gumbelFisherInfo σ *ᵥ v := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this
    simp only [Function.comp_def]
    rw [this, integral_lin_gumbelScore_sq hσ, dotProduct_gumbelFisherInfo_mulVec,
      dotProduct_gumbelFisherInfo_mulVec]
    simp
  have hZt : HasLaw (fun ω => ⟪Z ω, v⟫) (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by
    rw [hvar]
    exact hasLaw_inner_multivariateGaussian (posDef_gumbelFisherInfo hσ).posSemidef hZ v
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp [Y, f, inner_gumbelScoreVec]

end GumbelCLT

/-! ### The GPD at `ξ = 0`: the exponential law -/

section GPDZero

variable {ξ σ x : ℝ}

/-- The shape score of the GPD at `ξ = 0`: `∂_ξ ℓ = (x/σ)²/2 - x/σ`. -/
noncomputable def expScoreXi (σ x : ℝ) : ℝ := (x / σ) ^ 2 / 2 - x / σ

/-- The scale score of the exponential law `GPD(0, σ)`: `∂_σ ℓ = (x/σ - 1)/σ`. -/
noncomputable def expScoreSigma (σ x : ℝ) : ℝ := (x / σ - 1) / σ

lemma eventually_one_add_mul_div_pos (σ x : ℝ) : ∀ᶠ k in 𝓝 (0 : ℝ), 0 < 1 + k * x / σ := by
  have := eventually_one_add_mul_pos (x / σ)
  filter_upwards [this] with k hk
  rwa [mul_div_assoc]

/-- **Continuity of the GPD scale score at `ξ = 0`.** -/
theorem tendsto_gpdScoreSigma_zero (hσ : 0 < σ) :
    Tendsto (fun k => gpdScoreSigma k σ x) (𝓝[≠] 0) (𝓝 (expScoreSigma σ x)) := by
  have hc : ContinuousAt (fun k => gpdScoreSigma k σ x) 0 := by
    unfold gpdScoreSigma
    have : (σ + 0 * x) ≠ 0 := by simp [hσ.ne']
    fun_prop (disch := assumption)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  convert h using 2
  simp [gpdScoreSigma, expScoreSigma]

/-- **Continuity of the GPD shape score at `ξ = 0`**:
`log(1 + ξ x/σ)/ξ² - (1/ξ + 1) x/(σ + ξ x) → (x/σ)²/2 - x/σ`. -/
theorem tendsto_gpdScoreXi_zero (hσ : 0 < σ) :
    Tendsto (fun k => gpdScoreXi k σ x) (𝓝[≠] 0) (𝓝 (expScoreXi σ x)) := by
  set y := x / σ with hy
  have hq : Tendsto (fun k : ℝ => log1pQuad (k * y)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have : ContinuousAt (fun k : ℝ => log1pQuad (k * y)) 0 :=
      ContinuousAt.comp (g := log1pQuad) (by simpa using continuousAt_log1pQuad_zero)
        (continuous_id.mul continuous_const).continuousAt
    simpa [log1pQuad] using this.tendsto.mono_left nhdsWithin_le_nhds
  have h := ((tendsto_const_nhds (x := y ^ 2)).mul hq).sub
    ((tendsto_const_nhds (x := y)).div (tendsto_one_add_mul y) one_ne_zero)
  have heq : (fun k => y ^ 2 * log1pQuad (k * y) - y / (1 + k * y)) =ᶠ[𝓝[≠] 0]
      fun k => gpdScoreXi k σ x := by
    filter_upwards [nhdsWithin_le_nhds (eventually_one_add_mul_pos y), self_mem_nhdsWithin]
      with k hk hk0
    have hk0 : k ≠ 0 := hk0
    have hd : σ + k * x ≠ 0 := by
      have : σ + k * x = σ * (1 + k * y) := by rw [hy]; field_simp
      rw [this]; exact mul_ne_zero hσ.ne' hk.ne'
    rw [gpdScoreXi]
    rcases eq_or_ne y 0 with h0 | h0
    · have hx : x = 0 := by
        rw [hy] at h0; rcases div_eq_zero_iff.1 h0 with h | h
        · exact h
        · exact absurd h hσ.ne'
      simp [h0, hx]
    rw [log1pQuad_of_ne (mul_ne_zero hk0 h0), show k * x / σ = k * y by rw [hy]; ring,
      show x / (σ + k * x) = y / (1 + k * y) by rw [hy]; field_simp]
    have hu := hk.ne'
    generalize log (1 + k * y) = L
    field_simp
    ring
  refine (h.congr' heq).trans (le_of_eq ?_)
  congr 1
  rw [expScoreXi, ← hy]
  ring

/-- **Continuity of the GPD log-density in the shape at `ξ = 0`** (for `x ≥ 0`). -/
theorem continuousAt_log_gpdDensity_xi_zero (hσ : 0 < σ) (hx : 0 ≤ x) :
    ContinuousAt (fun k => log (gpdDensity k σ x)) 0 := by
  have hc : ContinuousAt (fun k => -log σ - (1 + k) * (x / σ * log1pDiv (k * (x / σ)))) 0 := by
    have : ContinuousAt (fun k : ℝ => log1pDiv (k * (x / σ))) 0 :=
      ContinuousAt.comp (g := log1pDiv) (by simpa using continuousAt_log1pDiv_zero)
        (continuous_id.mul continuous_const).continuousAt
    exact continuousAt_const.sub ((continuousAt_const.add continuousAt_id).mul
      (continuousAt_const.mul this))
  refine hc.congr ?_
  filter_upwards [eventually_one_add_mul_div_pos σ x] with k hk
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [log_gpdDensity_zero hσ hx]; simp [log1pDiv_zero]
  · rw [log_gpdDensity hσ hk0 hx hk]
    have hu : 0 < 1 + k * (x / σ) := by rwa [← mul_div_assoc]
    rw [mul_log1pDiv_eq hk0 hu, ← mul_div_assoc]
    field_simp

/-- **The GPD shape score at `ξ = 0` is the derivative of the log-density**:
`∂_ξ log g_{ξ,σ}(x)|_{ξ = 0} = (x/σ)²/2 - x/σ`. -/
theorem hasDerivAt_log_gpdDensity_xi_zero (hσ : 0 < σ) (hx : 0 ≤ x) :
    HasDerivAt (fun k => log (gpdDensity k σ x)) (expScoreXi σ x) 0 := by
  refine hasDerivAt_of_tendsto_punctured (eventually_one_add_mul_div_pos σ x)
    (fun k hk hk0 => hasDerivAt_log_gpdDensity_xi hσ hk0 hx ?_)
    (continuousAt_log_gpdDensity_xi_zero hσ hx) (tendsto_gpdScoreXi_zero hσ)
  have hk : 0 < 1 + k * x / σ := hk
  have : σ + k * x = σ * (1 + k * x / σ) := by field_simp
  rw [this]; positivity

end GPDZero

end ExtremeValueTheory
