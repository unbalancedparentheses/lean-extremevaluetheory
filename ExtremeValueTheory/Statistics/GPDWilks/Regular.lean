/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDWilks.Coverage
import ExtremeValueTheory.Statistics.GPDJointNormalityZero

/-!
# Wilks' theorem and profile likelihood intervals for the GPD, all regular shapes `ξ₀ > -1/2`

This file extends `ExtremeValueTheory.Statistics.GPDWilks` from `ξ₀ > 0` to the **entire regular
range** `ξ₀ > -1/2` (covering `-1/2 < ξ₀ < 0`, `ξ₀ = 0`, and `ξ₀ > 0`, [Coles, §2.6.5–2.6.6,
§4.3.3]; [Smith 1985]).

## Proof technique: exact second-order integral Taylor expansion (no third derivatives)

For `ξ₀ ≤ 0` the uniform Lipschitz bound on the GPD Hessian used in `GPDWilks/Deviance.lean`
fails. Instead, for any `C²` function `f` on `[0, 1]`, integration by parts yields the exact
identity

  `2 (f(1) - f(0)) = 2 f'(0) + ∫₀¹ 2 (1 - s) f''(s) ds`.

With the weighted segment Hessian
`segHessW H ξ₀ σ₀ θ x = ∫₀¹ 2 (1 - s) H(ξ₀ + s(θ₁ - ξ₀), σ₀ + s(θ₂ - σ₀), x) ds`
(whose weight `2(1 - s) ≥ 0` integrates to `1`), the sample deviance satisfies the exact quadratic
identity

  `2 (ℓₙ(θ) - ℓₙ(θ₀)) = 2 (T₁ S₁ + T₂ S₂) + (T₁² C₁₁ + 2 T₁ T₂ C₁₂ + T₂² C₂₂)`

with NO third-order remainder! Both the averaged segment Hessian `Bᵢⱼ` and the weighted averaged
segment Hessian `Cᵢⱼ` converge in probability to `-I(ξ₀, σ₀)ᵢⱼ` using the exact same
domination + endpoint cutoff machinery as `GPDJointNormalityNeg` (for `-1/2 < ξ₀ < 0`) and
`GPDJointNormalityZero` (for `ξ₀ = 0`). Solving the score equation (full or curve-restricted) and
substituting into the exact deviance formula expresses the error as a linear combination of
`S₁², S₁ S₂, S₂²` with coefficients tending to `0` in probability, giving `o_P(1)` directly.

## Main results

* `isGPDProfileChart_returnLevel_all`: level-set chart for the POT return level for ALL `ξ₀ ∈ ℝ`,
  including `ξ₀ = 0`.
* `tendstoInDistribution_gpdDeviance_reg`: `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₂` for all `ξ₀ > -1/2`.
* `tendstoInDistribution_gpdProfileDeviance_reg`: `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ̃ₙ)) ⇒ χ²₁` for all `ξ₀ > -1/2`.
* `tendsto_measure_mem_gpdProfileInterval_reg`,
  `exists_tendsto_measure_mem_gpdProfileInterval_reg`: profile-likelihood coverage for all
  `ξ₀ > -1/2`.
* `tendsto_measure_mem_gpdShapeProfileInterval_reg`,
  `tendsto_measure_mem_gpdScaleProfileInterval_reg`,
  `tendsto_measure_mem_gpdReturnLevelProfileInterval_reg`: shape, scale, and POT return level
  profile-likelihood coverage for all `ξ₀ > -1/2` (including `ξ₀ = 0`).
* `tendsto_measure_mem_gpdDevianceRegion_reg`,
  `tendsto_measure_mem_gpdDevianceRegion_of_alpha_reg`: full deviance region coverage for all
  `ξ₀ > -1/2`.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §2.6.5–2.6.6, §4.3.3.
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §16.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace ExtremeValueTheory

/-! ### Weighted segment Hessian and exact second-order Taylor identity -/

section WeightedSegHess

/-- Weighted average of a Hessian entry along the segment from `(ξ₀, σ₀)` to `θ`:
`∫₀¹ 2 (1 - s) H(ξ₀ + s(θ₁ - ξ₀), σ₀ + s(θ₂ - σ₀), x) ds`. -/
noncomputable def segHessW (H : ℝ → ℝ → ℝ → ℝ) (ξ₀ σ₀ : ℝ) (θ : ℝ × ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, 2 * (1 - s) * H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x

lemma integral_two_mul_one_sub : ∫ s in (0 : ℝ)..1, (2 * (1 - s) : ℝ) = 1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => 2 * s - s ^ 2) (f' := fun s : ℝ => 2 * (1 - s))
    (fun s _ => by
      have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by simpa using (hasDerivAt_id s).const_mul 2
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
      exact (h1.sub h2).congr_deriv (by ring))
    ((by fun_prop : Continuous fun s : ℝ => 2 * (1 - s)).intervalIntegrable 0 1)
  rw [h]; norm_num

lemma measurable_segHessW {H : ℝ → ℝ → ℝ → ℝ} {ξ₀ σ₀ : ℝ}
    (hH : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) :
    Measurable fun p : (ℝ × ℝ) × ℝ => segHessW H ξ₀ σ₀ p.1 p.2 := by
  have : (fun p : (ℝ × ℝ) × ℝ => segHessW H ξ₀ σ₀ p.1 p.2) = fun p =>
      ∫ s, 2 * (1 - s) * H (ξ₀ + s * (p.1.1 - ξ₀)) (σ₀ + s * (p.1.2 - σ₀)) p.2
        ∂(volume.restrict (Ioc 0 1)) := by
    funext p
    rw [segHessW, intervalIntegral.integral_of_le zero_le_one]
  rw [this]
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right
    (f := fun p : (ℝ × ℝ) × ℝ => fun s : ℝ =>
      2 * (1 - s) * H (ξ₀ + s * (p.1.1 - ξ₀)) (σ₀ + s * (p.1.2 - σ₀)) p.2) ?_
  refine Measurable.stronglyMeasurable ?_
  have h1 : Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ => 2 * (1 - q.2) := by fun_prop
  have h2 : Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      H (ξ₀ + q.2 * (q.1.1.1 - ξ₀)) (σ₀ + q.2 * (q.1.1.2 - σ₀)) q.1.2 :=
    hH.comp (f := fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      (ξ₀ + q.2 * (q.1.1.1 - ξ₀), σ₀ + q.2 * (q.1.1.2 - σ₀), q.1.2)) (by fun_prop)
  exact h1.mul h2

/-- **Exact second-order Taylor identity with integral remainder**: if `f` is twice differentiable on
`[0, 1]` with `f''` continuous on `[0, 1]`, then
`2 (f(1) - f(0)) = 2 f'(0) + ∫₀¹ 2 (1 - s) f''(s) ds`. -/
lemma two_mul_sub_eq_taylor_segW {f f' f'' : ℝ → ℝ}
    (hf : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt f' (f'' s) s)
    (hc'' : ContinuousOn f'' (uIcc (0 : ℝ) 1)) :
    2 * (f 1 - f 0) = 2 * f' 0 + ∫ s in (0 : ℝ)..1, 2 * (1 - s) * f'' s := by
  have hg : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => 2 * (f t + (1 - t) * f' t)) (2 * (1 - s) * f'' s) s := fun s hs => by
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) s :=
      ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).congr_deriv (by ring)
    have hprod := h1.mul (hf' s hs)
    have hsum := (hf s hs).add hprod
    refine (hsum.const_mul 2).congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun s => 2 * (1 - s) * f'' s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ((continuous_const.mul (continuous_const.sub continuous_id)).continuousOn).mul hc''
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint
  simp only [sub_self, zero_mul, add_zero, sub_zero, one_mul] at hftc
  linarith

lemma hasDerivAt_log1pDiv_zero : HasDerivAt log1pDiv (-(1 / 2)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hbd : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 / 2 → |slope log1pDiv 0 t - (-(1 / 2))| ≤ 2 * |t| := by
    intro t ht hle
    have hlt : |-t| < 1 := by rw [abs_neg]; linarith
    have hT := abs_log_sub_add_sum_range_le hlt 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hT
    norm_num at hT
    have hden : 1 / 2 ≤ 1 - |t| := by linarith
    have hT' : |log (1 + t) - t + t ^ 2 / 2| ≤ 2 * |t| ^ 3 := by
      have hT0 : |log (1 + t) - t + t ^ 2 / 2| ≤ |t| ^ 3 / (1 - |t|) := by
        convert hT using 2; ring
      calc |log (1 + t) - t + t ^ 2 / 2|
          ≤ |t| ^ 3 / (1 - |t|) := hT0
        _ ≤ |t| ^ 3 / (1 / 2) := by gcongr
        _ = 2 * |t| ^ 3 := by ring
    have he : slope log1pDiv 0 t - (-(1 / 2)) = (log (1 + t) - t + t ^ 2 / 2) / t ^ 2 := by
      simp only [slope_def_field, sub_zero, log1pDiv_zero, log1pDiv_of_ne ht]
      field_simp [ht]; ring
    rw [he, abs_div, abs_pow, div_le_iff₀ (sq_pos_of_pos (abs_pos.2 ht))]
    linarith [show 2 * |t| * |t| ^ 2 = 2 * |t| ^ 3 by ring]
  have h0 : Tendsto (fun t => slope log1pDiv 0 t - (-(1 / 2))) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa using ((continuous_abs.tendsto (0 : ℝ)).const_mul 2).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num))]
      with t (ht : t ≠ 0) hball
    rw [Real.norm_eq_abs]
    have hle : |t| ≤ 1 / 2 := (by simpa [Metric.mem_ball, Real.dist_eq] using hball : |t| < 1 / 2).le
    exact hbd t ht hle
  have h1 := h0.add_const (-(1 / 2))
  simp only [sub_add_cancel, zero_add] at h1
  exact h1

lemma log_gpdDensity_eq_log1pDiv {ξ σ x : ℝ} (hσ : 0 < σ) (hx : 0 ≤ x)
    (hu : 0 < σ + ξ * x) :
    log (gpdDensity ξ σ x) = -log σ - (1 + ξ) * (x / σ) * log1pDiv (ξ * (x / σ)) := by
  have hu' : 0 < 1 + ξ * x / σ := by
    have : 1 + ξ * x / σ = (σ + ξ * x) / σ := by field_simp
    rw [this]; exact div_pos hu hσ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [gpdDensity, ↓reduceIte, hx, zero_mul, zero_div, add_zero, zero_lt_one, and_self,
      log1pDiv_zero, mul_one]
    rw [log_mul (inv_pos.2 hσ).ne' (exp_pos _).ne', log_inv, log_exp]; ring
  · simp only [gpdDensity, hξ, hx, hu', ↓reduceIte, and_self]
    rw [log_mul (inv_pos.2 hσ).ne' (Real.rpow_pos_of_pos hu' _).ne', log_inv, Real.log_rpow hu']
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [log1pDiv_zero]
    · have ht : ξ * (x / σ) ≠ 0 := mul_ne_zero hξ (div_ne_zero hx0 hσ.ne')
      rw [log1pDiv_of_ne ht]
      have harg : 1 + ξ * (x / σ) = 1 + ξ * x / σ := by ring
      rw [harg]; field_simp [hξ, hσ.ne']; ring

/-- Derivative of `s ↦ log (gpdDensity (γ₁ s) (γ₂ s) x)` along ANY differentiable curve, valid at
`γ₁ s = 0` as well as `γ₁ s ≠ 0`. -/
lemma hasDerivAt_log_gpdDensity_curve_all {γ₁ γ₂ : ℝ → ℝ} {a b s x : ℝ}
    (h₁ : HasDerivAt γ₁ a s) (h₂ : HasDerivAt γ₂ b s)
    (hσ : 0 < γ₂ s) (hx : 0 ≤ x) (hu : 0 < γ₂ s + γ₁ s * x) :
    HasDerivAt (fun r => log (gpdDensity (γ₁ r) (γ₂ r) x))
      (a * gpdScoreXiAll (γ₁ s) (γ₂ s) x + b * gpdScoreSigma (γ₁ s) (γ₂ s) x) s := by
  rcases eq_or_ne (γ₁ s) 0 with h0 | hne
  · have hnear : ∀ᶠ r in 𝓝 s, 0 < γ₂ r ∧ 0 < γ₂ r + γ₁ r * x :=
      (h₂.continuousAt.eventually (lt_mem_nhds hσ)).and
        ((h₂.continuousAt.add (h₁.continuousAt.mul continuousAt_const)).eventually (lt_mem_nhds hu))
    have hev : (fun r => log (gpdDensity (γ₁ r) (γ₂ r) x)) =ᶠ[𝓝 s]
        fun r => -log (γ₂ r) - (1 + γ₁ r) * (x / γ₂ r) * log1pDiv (γ₁ r * (x / γ₂ r)) :=
      hnear.mono fun r ⟨hr1, hr2⟩ => log_gpdDensity_eq_log1pDiv hr1 hx hr2
    have hd_log : HasDerivAt (fun r => -log (γ₂ r)) (-(b / γ₂ s)) s :=
      (h₂.log hσ.ne').neg
    have hd_q : HasDerivAt (fun r => x / γ₂ r) (-(x * b) / γ₂ s ^ 2) s := by
      refine ((hasDerivAt_const s x).div h₂ hσ.ne').congr_deriv ?_; ring
    have hd_arg : HasDerivAt (fun r => γ₁ r * (x / γ₂ r)) (a * (x / γ₂ s)) s := by
      have := h₁.mul hd_q
      refine this.congr_deriv ?_; rw [h0]; ring
    have hd_l : HasDerivAt (fun r => log1pDiv (γ₁ r * (x / γ₂ r)))
        (-(1 / 2) * (a * (x / γ₂ s))) s := by
      have harg0 : γ₁ s * (x / γ₂ s) = 0 := by rw [h0, zero_mul]
      have hcomp := hasDerivAt_log1pDiv_zero
      rw [← harg0] at hcomp
      exact hcomp.comp s hd_arg
    have hd_1g : HasDerivAt (fun r => 1 + γ₁ r) a s := by
      have := (hasDerivAt_const s (1 : ℝ)).add h₁
      refine this.congr_deriv (by ring)
    have hd_p1 : HasDerivAt (fun r => (1 + γ₁ r) * (x / γ₂ r))
        (a * (x / γ₂ s) + 1 * (-(x * b) / γ₂ s ^ 2)) s := by
      have := hd_1g.mul hd_q
      refine this.congr_deriv ?_; simp only [h0]; ring
    have hd_prod : HasDerivAt (fun r => (1 + γ₁ r) * (x / γ₂ r) * log1pDiv (γ₁ r * (x / γ₂ r)))
        ((a * (x / γ₂ s) + 1 * (-(x * b) / γ₂ s ^ 2)) * 1 +
          (x / γ₂ s) * (-(1 / 2) * (a * (x / γ₂ s)))) s := by
      have := hd_p1.mul hd_l
      refine this.congr_deriv ?_
      simp only [h0, zero_mul, log1pDiv_zero]; ring
    refine ((hd_log.sub hd_prod).congr_of_eventuallyEq hev).congr_deriv ?_
    rw [h0, gpdScoreXiAll_zero, gpdScoreSigma_zero, expScoreXi, expScoreSigma]
    field_simp [hσ.ne']; ring
  · rw [gpdScoreXiAll_of_ne hne]
    exact hasDerivAt_log_gpdDensity_curve h₁ h₂ hne hσ hx hu

/-- Directional derivative of `log (gpdDensity (ξ₀ + s a) (σ₀ + s b) x)` along a segment, valid
across `ξ = 0` as well as `ξ ≠ 0`. -/
lemma hasDerivAt_log_gpdDensity_line_all {ξ₀ σ₀ a b x s : ℝ}
    (hσ : 0 < σ₀ + s * b) (hx : 0 ≤ x) (hu : 0 < (σ₀ + s * b) + (ξ₀ + s * a) * x) :
    HasDerivAt (fun r => log (gpdDensity (ξ₀ + r * a) (σ₀ + r * b) x))
      (a * gpdScoreXiAll (ξ₀ + s * a) (σ₀ + s * b) x +
        b * gpdScoreSigma (ξ₀ + s * a) (σ₀ + s * b) x) s := by
  have h1 : HasDerivAt (fun r : ℝ => ξ₀ + r * a) a s := by
    simpa using ((hasDerivAt_id s).mul_const a).const_add ξ₀
  have h2 : HasDerivAt (fun r : ℝ => σ₀ + r * b) b s := by
    simpa using ((hasDerivAt_id s).mul_const b).const_add σ₀
  exact hasDerivAt_log_gpdDensity_curve_all h1 h2 hσ hx hu

/-- **Exact second-order Taylor expansion of `2 (log f(θ; x) - log f(θ₀; x))` for negative shape
`ξ₀ < 0`** on `gpdNbhdNeg ξ₀ σ₀`. -/
lemma two_mul_log_gpdDensity_sub_eq_segHessW_neg {ξ₀ σ₀ : ℝ} (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x)
    (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x) :
    2 * (log (gpdDensity θ.1 θ.2 x) - log (gpdDensity ξ₀ σ₀ x)) =
      2 * ((θ.1 - ξ₀) * gpdScoreXi ξ₀ σ₀ x + (θ.2 - σ₀) * gpdScoreSigma ξ₀ σ₀ x) +
        ((θ.1 - ξ₀) ^ 2 * segHessW gpdHessXiXi ξ₀ σ₀ θ x +
          2 * (θ.1 - ξ₀) * (θ.2 - σ₀) * segHessW gpdHessXiSigma ξ₀ σ₀ θ x +
          (θ.2 - σ₀) ^ 2 * segHessW gpdHessSigmaSigma ξ₀ σ₀ θ x) := by
  set a := θ.1 - ξ₀
  set b := θ.2 - σ₀
  have hseg : ∀ s ∈ uIcc (0 : ℝ) 1,
      ξ₀ + s * a ≠ 0 ∧ 0 < σ₀ + s * b ∧ 0 < (σ₀ + s * b) + (ξ₀ + s * a) * x := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    have hmem := segment_mem_gpdNbhdNeg hξ₀' hσ₀ hθ hs
    obtain ⟨_, h2, h3, _⟩ := bounds_of_mem_gpdNbhdNeg hmem
    exact ⟨by linarith, by linarith, seg_support_pos h0 h1 hs⟩
  have hcXX : ContinuousOn (fun s => gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs; obtain ⟨hξs, hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessXiXi₃ (q := (ξ₀ + s * a, σ₀ + s * b, x)) hξs hσs hus).comp
      (f := fun r => (ξ₀ + r * a, σ₀ + r * b, x)) (by fun_prop)).continuousWithinAt
  have hcXS : ContinuousOn (fun s => gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs; obtain ⟨_, hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessXiSigma₃ (q := (ξ₀ + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun r => (ξ₀ + r * a, σ₀ + r * b, x)) (by fun_prop)).continuousWithinAt
  have hcSS : ContinuousOn (fun s => gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs; obtain ⟨_, hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessSigmaSigma₃ (q := (ξ₀ + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun r => (ξ₀ + r * a, σ₀ + r * b, x)) (by fun_prop)).continuousWithinAt
  have htay := two_mul_sub_eq_taylor_segW
    (f := fun s => log (gpdDensity (ξ₀ + s * a) (σ₀ + s * b) x))
    (f' := fun s => a * gpdScoreXi (ξ₀ + s * a) (σ₀ + s * b) x +
      b * gpdScoreSigma (ξ₀ + s * a) (σ₀ + s * b) x)
    (f'' := fun s => a ^ 2 * gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x +
      2 * a * b * gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x +
      b ^ 2 * gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x)
    (fun s hs => by
      obtain ⟨hξs, hσs, hus⟩ := hseg s hs
      exact hasDerivAt_log_gpdDensity_line hξs hσs hx hus)
    (fun s hs => by
      obtain ⟨hξs, hσs, hus⟩ := hseg s hs
      have d1 := (hasDerivAt_gpdScoreXi_line hξs hσs hus).const_mul a
      have d2 := (hasDerivAt_gpdScoreSigma_line hσs hus).const_mul b
      exact (d1.add d2).congr_deriv (by ring))
    (((continuousOn_const.mul hcXX).add (continuousOn_const.mul hcXS)).add
      (continuousOn_const.mul hcSS))
  have hw : ContinuousOn (fun s : ℝ => 2 * (1 - s)) (uIcc 0 1) := by fun_prop
  have hiXX : IntervalIntegrable (fun s => 2 * (1 - s) * gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x)
      volume 0 1 := (hw.mul hcXX).intervalIntegrable
  have hiXS : IntervalIntegrable (fun s => 2 * (1 - s) * gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x)
      volume 0 1 := (hw.mul hcXS).intervalIntegrable
  have hiSS : IntervalIntegrable (fun s => 2 * (1 - s) * gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x)
      volume 0 1 := (hw.mul hcSS).intervalIntegrable
  have hsplit : ∫ s in (0 : ℝ)..1, 2 * (1 - s) *
      (a ^ 2 * gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x +
        2 * a * b * gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x +
        b ^ 2 * gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x) =
      a ^ 2 * segHessW gpdHessXiXi ξ₀ σ₀ θ x +
        2 * a * b * segHessW gpdHessXiSigma ξ₀ σ₀ θ x +
        b ^ 2 * segHessW gpdHessSigmaSigma ξ₀ σ₀ θ x := by
    have hfun : (fun s => 2 * (1 - s) *
        (a ^ 2 * gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x +
          2 * a * b * gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x +
          b ^ 2 * gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x)) =
        fun s => a ^ 2 * (2 * (1 - s) * gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x) +
          (2 * a * b) * (2 * (1 - s) * gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x) +
          b ^ 2 * (2 * (1 - s) * gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x) := by
      funext s; ring
    rw [hfun, intervalIntegral.integral_add ((hiXX.const_mul _).add (hiXS.const_mul _)) (hiSS.const_mul _),
      intervalIntegral.integral_add (hiXX.const_mul _) (hiXS.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rfl
  rw [hsplit] at htay
  have e1 : ξ₀ + 1 * a = θ.1 := by simp [a]
  have e2 : σ₀ + 1 * b = θ.2 := by simp [b]
  simpa only [e1, e2, zero_mul, add_zero] using htay

/-- **Exact second-order Taylor expansion of `2 (log f(θ; x) - log f((0, σ₀); x))` at `ξ₀ = 0`**
on `gpdNbhdZero σ₀`. -/
lemma two_mul_log_gpdDensity_sub_eq_segHessW_zero {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀) {x : ℝ} (hx : 0 ≤ x)
    (h1 : 0 < θ.2 + θ.1 * x) :
    2 * (log (gpdDensity θ.1 θ.2 x) - log (gpdDensity 0 σ₀ x)) =
      2 * ((θ.1 - 0) * expScoreXi σ₀ x + (θ.2 - σ₀) * expScoreSigma σ₀ x) +
        ((θ.1 - 0) ^ 2 * segHessW gpdHessXiXiAll 0 σ₀ θ x +
          2 * (θ.1 - 0) * (θ.2 - σ₀) * segHessW gpdHessXiSigma 0 σ₀ θ x +
          (θ.2 - σ₀) ^ 2 * segHessW gpdHessSigmaSigma 0 σ₀ θ x) := by
  have h0 : 0 < σ₀ + 0 * x := by simpa using hσ₀
  set a := θ.1 - 0
  set b := θ.2 - σ₀
  have hseg : ∀ s ∈ uIcc (0 : ℝ) 1, 0 < σ₀ + s * b ∧
      0 < (σ₀ + s * b) + (0 + s * a) * x := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    have hmem := segment_mem_gpdNbhdZero hσ₀ hθ hs
    exact ⟨by linarith [hmem.2.1], seg_support_pos (ξ₀ := 0) h0 h1 hs⟩
  have hcXX : ContinuousOn (fun s => gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs; obtain ⟨hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessXiXiAll₃ (q := (0 + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun r => (0 + r * a, σ₀ + r * b, x)) (by fun_prop)).continuousWithinAt
  have hcXS : ContinuousOn (fun s => gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs; obtain ⟨hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessXiSigma₃ (q := (0 + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun r => (0 + r * a, σ₀ + r * b, x)) (by fun_prop)).continuousWithinAt
  have hcSS : ContinuousOn (fun s => gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs; obtain ⟨hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessSigmaSigma₃ (q := (0 + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun r => (0 + r * a, σ₀ + r * b, x)) (by fun_prop)).continuousWithinAt
  have htay := two_mul_sub_eq_taylor_segW
    (f := fun s => log (gpdDensity (0 + s * a) (σ₀ + s * b) x))
    (f' := fun s => a * gpdScoreXiAll (0 + s * a) (σ₀ + s * b) x +
      b * gpdScoreSigma (0 + s * a) (σ₀ + s * b) x)
    (f'' := fun s => a ^ 2 * gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x +
      2 * a * b * gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x +
      b ^ 2 * gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x)
    (fun s hs => by
      obtain ⟨hσs, hus⟩ := hseg s hs
      exact hasDerivAt_log_gpdDensity_line_all hσs hx hus)
    (fun s hs => by
      obtain ⟨hσs, hus⟩ := hseg s hs
      have d1 := (hasDerivAt_gpdScoreXiAll_line hσs hus).const_mul a
      have d2 := (hasDerivAt_gpdScoreSigma_line hσs hus).const_mul b
      exact (d1.add d2).congr_deriv (by ring))
    (((continuousOn_const.mul hcXX).add (continuousOn_const.mul hcXS)).add
      (continuousOn_const.mul hcSS))
  have hw : ContinuousOn (fun s : ℝ => 2 * (1 - s)) (uIcc 0 1) := by fun_prop
  have hiXX : IntervalIntegrable (fun s => 2 * (1 - s) * gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x)
      volume 0 1 := (hw.mul hcXX).intervalIntegrable
  have hiXS : IntervalIntegrable (fun s => 2 * (1 - s) * gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x)
      volume 0 1 := (hw.mul hcXS).intervalIntegrable
  have hiSS : IntervalIntegrable (fun s => 2 * (1 - s) * gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x)
      volume 0 1 := (hw.mul hcSS).intervalIntegrable
  have hsplit : ∫ s in (0 : ℝ)..1, 2 * (1 - s) *
      (a ^ 2 * gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x +
        2 * a * b * gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x +
        b ^ 2 * gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x) =
      a ^ 2 * segHessW gpdHessXiXiAll 0 σ₀ θ x +
        2 * a * b * segHessW gpdHessXiSigma 0 σ₀ θ x +
        b ^ 2 * segHessW gpdHessSigmaSigma 0 σ₀ θ x := by
    have hfun : (fun s => 2 * (1 - s) *
        (a ^ 2 * gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x +
          2 * a * b * gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x +
          b ^ 2 * gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x)) =
        fun s => a ^ 2 * (2 * (1 - s) * gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x) +
          (2 * a * b) * (2 * (1 - s) * gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x) +
          b ^ 2 * (2 * (1 - s) * gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x) := by
      funext s; ring
    rw [hfun, intervalIntegral.integral_add ((hiXX.const_mul _).add (hiXS.const_mul _)) (hiSS.const_mul _),
      intervalIntegral.integral_add (hiXX.const_mul _) (hiXS.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rfl
  rw [hsplit] at htay
  have e1 : 0 + 1 * a = θ.1 := by simp [a]
  have e2 : σ₀ + 1 * b = θ.2 := by simp [b]
  simpa only [e1, e2, zero_mul, add_zero, gpdScoreXiAll_zero, gpdScoreSigma_zero] using htay

end WeightedSegHess

/-! ### Convergence of `segHessW` for `-1/2 < ξ₀ < 0` and `ξ₀ = 0` -/

section WeightedConv

/-- Generic integral comparison for `segHessW`: if `|H(θ_s, x) - H(θ₀, x)| ≤ ε` on `[0, 1]`,
then `|segHessW H ξ₀ σ₀ θ x - H ξ₀ σ₀ x| ≤ ε`. -/
lemma abs_segHessW_sub_le_of_forall {H : ℝ → ℝ → ℝ → ℝ} {ξ₀ σ₀ : ℝ} {θ : ℝ × ℝ} {x ε : ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) (_hε : 0 ≤ ε)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1,
      |H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - H ξ₀ σ₀ x| ≤ ε) :
    |segHessW H ξ₀ σ₀ θ x - H ξ₀ σ₀ x| ≤ ε := by
  have hint_const : IntervalIntegrable (fun s : ℝ => 2 * (1 - s) * H ξ₀ σ₀ x) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => 2 * (1 - s) * H ξ₀ σ₀ x).intervalIntegrable 0 1
  have hm : Measurable fun s : ℝ =>
      2 * (1 - s) * (H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - H ξ₀ σ₀ x) := by
    have h1 : Measurable fun s : ℝ => 2 * (1 - s) := by fun_prop
    have h2 : Measurable fun s : ℝ => H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x :=
      hHm.comp (f := fun s : ℝ => (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x)) (by fun_prop)
    exact h1.mul (h2.sub measurable_const)
  have hint_diff : IntervalIntegrable
      (fun s => 2 * (1 - s) * (H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - H ξ₀ σ₀ x))
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine (integrableOn_const (C := 2 * ε) (hs := measure_Ioc_lt_top.ne)).mono' hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 2 * (1 - s))]
    exact mul_le_mul (by linarith [hs.1]) (hbd s hs') (abs_nonneg _) (by positivity)
  have hint_H : IntervalIntegrable
      (fun s => 2 * (1 - s) * H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) volume 0 1 := by
    have : (fun s => 2 * (1 - s) * H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) =
        fun s => 2 * (1 - s) * (H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - H ξ₀ σ₀ x) +
          2 * (1 - s) * H ξ₀ σ₀ x := by funext s; ring
    rw [this]; exact hint_diff.add hint_const
  have hsub : segHessW H ξ₀ σ₀ θ x - H ξ₀ σ₀ x =
      ∫ s in (0 : ℝ)..1, 2 * (1 - s) *
        (H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - H ξ₀ σ₀ x) := by
    have hH0 : H ξ₀ σ₀ x = ∫ s in (0 : ℝ)..1, 2 * (1 - s) * H ξ₀ σ₀ x := by
      rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul]
    conv_lhs => rw [segHessW, hH0]
    rw [← intervalIntegral.integral_sub hint_H hint_const]
    exact intervalIntegral.integral_congr fun s _ => (mul_sub _ _ _).symm
  rw [hsub]
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (a := (0 : ℝ)) (b := 1) zero_le_one
    (f := fun s => 2 * (1 - s) * (H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - H ξ₀ σ₀ x))
  refine habs.trans ?_
  have hle := intervalIntegral.integral_mono_on zero_le_one hint_diff.abs
    ((by fun_prop : Continuous fun s : ℝ => 2 * (1 - s) * ε).intervalIntegrable 0 1)
    fun s hs => by
      rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 2 * (1 - s))]
      exact mul_le_mul_of_nonneg_left (hbd s hs) (by linarith [hs.2])
  rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul] at hle
  exact hle

/-- Generic domination bound for `segHessW`: if `|H(θ_s, x)| ≤ M` on `[0, 1]`, then
`|segHessW H ξ₀ σ₀ θ x| ≤ M`. -/
lemma abs_segHessW_le_of_forall {H : ℝ → ℝ → ℝ → ℝ} {ξ₀ σ₀ : ℝ} {θ : ℝ × ℝ} {x M : ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) (_hM : 0 ≤ M)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1,
      |H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x| ≤ M) :
    |segHessW H ξ₀ σ₀ θ x| ≤ M := by
  have hm : Measurable fun s : ℝ =>
      2 * (1 - s) * H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x :=
    (by fun_prop : Measurable fun s : ℝ => 2 * (1 - s)).mul
      (hHm.comp (f := fun s : ℝ => (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x)) (by fun_prop))
  have hint : IntervalIntegrable
      (fun s => 2 * (1 - s) * H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine (integrableOn_const (C := 2 * M) (hs := measure_Ioc_lt_top.ne)).mono' hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 2 * (1 - s))]
    exact mul_le_mul (by linarith [hs.1]) (hbd s ⟨hs.1.le, hs.2⟩) (abs_nonneg _) (by positivity)
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (a := (0 : ℝ)) (b := 1) zero_le_one
    (f := fun s => 2 * (1 - s) * H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x)
  refine habs.trans ?_
  have hle := intervalIntegral.integral_mono_on zero_le_one hint.abs
    ((by fun_prop : Continuous fun s : ℝ => 2 * (1 - s) * M).intervalIntegrable 0 1)
    fun s hs => by
      rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 2 * (1 - s))]
      exact mul_le_mul_of_nonneg_left (hbd s hs) (by linarith [hs.2])
  rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul] at hle
  exact hle

/-- Deterministic convergence of the averaged `segHessW` for `-1/2 < ξ₀ < 0`. -/
lemma eventually_abs_avg_segHessW_sub_le_neg {ξ₀ σ₀ : ℝ} (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0)
    (hσ₀ : 0 < σ₀) {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    (hHb : ∀ ξ σ x, 0 ≤ x → 0 < σ + ξ * x → |H ξ σ x| ≤ gpdHessCoef (ξ, σ) *
      (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) + (x / (σ + ξ * x)) ^ 2 + 1))
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i ∧ 0 < σ₀ + ξ₀ * x i)
    {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (ξ₀, σ₀)))
    {m : ℝ} (hm : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i))
      atTop (𝓝 m))
    {d : ℕ → ℝ} (hD : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i)) atTop (𝓝 (d k)))
    (hd : Tendsto d atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (∀ i < n, (σ₀ + ξ₀ * x i) / 2 ≤ (θs n).2 + (θs n).1 * x i) →
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW H ξ₀ σ₀ (θs n) (x i) - m| ≤ ε := by
  obtain ⟨Kc, _, hKc, _, hb⟩ := exists_gpdCoef_bound hξ₀ hξ₀' hσ₀
  set A := 8 * Kc + 1 with hA
  have hA0 : 0 < A := by positivity
  obtain ⟨k, hk⟩ : ∃ k, A * d k < ε / 4 := by
    have h := hd.const_mul A; rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  -- Uniform continuity on the compact good set `gpdNbhdNeg × [0, (σ₀ - c)/(-ξ₀)]`
  set c : ℝ := 1 / ((k : ℝ) + 1)
  have hc0 : 0 < c := by positivity
  set e₀ := -σ₀ / ξ₀
  have hgood_delta : ∃ δ > 0, ∀ θ, gpdDist ξ₀ σ₀ θ ≤ δ → ∀ y, 0 ≤ y → c ≤ σ₀ + ξ₀ * y →
      |segHessW H ξ₀ σ₀ θ y - H ξ₀ σ₀ y| ≤ ε / 4 := by
    -- Compact set `K_p × [0, e₀]` inside `{u ≥ c/2}`
    set r₀ := min (min (-ξ₀ / 8) (σ₀ / 8)) (c / (4 * (1 + e₀)))
    have hr₀ : 0 < r₀ := by
      have he0 : 0 < e₀ := div_pos_of_neg_of_neg (by linarith) hξ₀'
      have hξp : 0 < -ξ₀ := by linarith
      positivity
    set Kp : Set (ℝ × ℝ) := Icc (ξ₀ - r₀) (ξ₀ + r₀) ×ˢ Icc (σ₀ - r₀) (σ₀ + r₀)
    set Kx : Set ℝ := Icc 0 ((σ₀ - c) / (-ξ₀))
    have hKc_set : IsCompact (Kp ×ˢ Kx) :=
      (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
    have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => H q.1.1 q.1.2 q.2) (Kp ×ˢ Kx) := by
      rintro ⟨⟨ξ, σ⟩, y⟩ ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨hy0, hy1⟩⟩
      have hr1 : r₀ ≤ -ξ₀ / 8 := (min_le_left _ _).trans (min_le_left _ _)
      have hr2 : r₀ ≤ σ₀ / 8 := (min_le_left _ _).trans (min_le_right _ _)
      have hr3 : r₀ ≤ c / (4 * (1 + e₀)) := min_le_right _ _
      have hy_le : y ≤ e₀ := by
        have hle : (σ₀ - c) / (-ξ₀) ≤ σ₀ / (-ξ₀) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith : (0 : ℝ) ≤ -ξ₀)
        have heq : σ₀ / (-ξ₀) = e₀ := by simp only [e₀, div_neg, neg_div]
        exact hy1.trans (heq ▸ hle)
      have hcy : c ≤ σ₀ + ξ₀ * y := by
        have := (le_div_iff₀ (show 0 < -ξ₀ by linarith)).1 hy1; linarith
      have hu : 0 < σ + ξ * y := by
        have he0 : 0 < e₀ := div_pos_of_neg_of_neg (by linarith) hξ₀'
        have hd1 : |ξ - ξ₀| ≤ r₀ := abs_le.2 ⟨by linarith, by linarith⟩
        have hd2 : |σ - σ₀| ≤ r₀ := abs_le.2 ⟨by linarith, by linarith⟩
        have hstep : r₀ * (1 + e₀) ≤ c / 4 := by
          have := (le_div_iff₀ (show 0 < 4 * (1 + e₀) by positivity)).1 hr3; linarith
        have hdiff : |(σ + ξ * y) - (σ₀ + ξ₀ * y)| ≤ r₀ * (1 + e₀) := by
          calc |(σ + ξ * y) - (σ₀ + ξ₀ * y)|
              = |(σ - σ₀) + (ξ - ξ₀) * y| := by ring_nf
            _ ≤ |σ - σ₀| + |ξ - ξ₀| * |y| := (abs_add_le _ _).trans (by rw [abs_mul])
            _ ≤ r₀ + r₀ * e₀ := add_le_add hd2 (mul_le_mul hd1 (by rw [abs_of_nonneg hy0]; exact hy_le)
                (abs_nonneg _) hr₀.le)
            _ = r₀ * (1 + e₀) := by ring
        linarith [(abs_le.1 hdiff).1]
      exact (ContinuousAt.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
        (g := fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) (x := ((ξ, σ), y))
        (hH (ξ, σ, y) (by linarith) (by linarith) hu) (by fun_prop)).continuousWithinAt
    have huc := hKc_set.uniformContinuousOn_of_continuous hcont
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨η, hη, hη_bd⟩ := huc (ε / 4) (by positivity)
    refine ⟨min r₀ (η / 2), lt_min hr₀ (by positivity), fun θ hθd y hy0 hcy => ?_⟩
    have hy_mem : y ∈ Kx := ⟨hy0, (le_div_iff₀ (show 0 < -ξ₀ by linarith)).2 (by linarith)⟩
    have hθ0_mem : ((ξ₀, σ₀), y) ∈ Kp ×ˢ Kx :=
      ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, hy_mem⟩
    refine abs_segHessW_sub_le_of_forall hHm (by positivity) fun s hs => ?_
    have hd_r0 : gpdDist ξ₀ σ₀ θ ≤ r₀ := hθd.trans (min_le_left _ _)
    have hd_eta : gpdDist ξ₀ σ₀ θ ≤ η / 2 := hθd.trans (min_le_right _ _)
    have hθs_mem : ((ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)), y) ∈ Kp ×ˢ Kx := by
      have ha : |s * (θ.1 - ξ₀)| ≤ r₀ := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_r0)
      have hb' : |s * (θ.2 - σ₀)| ≤ r₀ := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_r0)
      rw [abs_le] at ha hb'
      exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, hy_mem⟩
    have hdist : dist ((ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)), y) ((ξ₀, σ₀), y) < η := by
      simp only [Prod.dist_eq, dist_self, Real.dist_eq, add_sub_cancel_left]
      have ha : |s * (θ.1 - ξ₀)| ≤ η / 2 := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_eta)
      have hb' : |s * (θ.2 - σ₀)| ≤ η / 2 := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_eta)
      exact max_lt (max_lt (by linarith) (by linarith)) hη
    exact (hη_bd _ hθs_mem _ hθ0_mem hdist).le
  obtain ⟨δ, hδ, hgood⟩ := hgood_delta
  filter_upwards [tendsto_gpdDist hθ hδ, hθ.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀),
    ((hD k).const_mul A).eventually (gt_mem_nhds hk),
    hm.eventually (Metric.ball_mem_nhds m (show 0 < ε / 4 by positivity)),
    eventually_gt_atTop 0] with n hn1 hn2 hn3 hn4 hn5 hhalf
  set tail : ℕ → ℝ := fun i => gpdDomTail ξ₀ σ₀ c (x i)
  have hdev : ∀ i < n,
      |segHessW H ξ₀ σ₀ (θs n) (x i) - H ξ₀ σ₀ (x i)| ≤ ε / 4 + 8 * Kc * tail i := fun i hi' => by
    by_cases hcy : c ≤ σ₀ + ξ₀ * x i
    · rw [show tail i = 0 from gpdDomTail_of_le hcy, mul_zero, add_zero]
      exact hgood _ hn1 _ (hx i).1 hcy
    · rw [show tail i = gpdDom ξ₀ σ₀ (x i) from gpdDomTail_of_lt (not_le.1 hcy)]
      have hdom0 : 0 ≤ gpdDom ξ₀ σ₀ (x i) := by linarith [one_le_gpdDom hξ₀' hσ₀ (hx i).1 (hx i).2]
      have h1 : |segHessW H ξ₀ σ₀ (θs n) (x i)| ≤ 4 * Kc * gpdDom ξ₀ σ₀ (x i) := by
        refine abs_segHessW_le_of_forall hHm
          (mul_nonneg (by positivity) hdom0) fun s hs => ?_
        have hmem := segment_mem_gpdNbhdNeg hξ₀' hσ₀ hn2 hs
        have hus : (σ₀ + ξ₀ * x i) / 2 ≤ (σ₀ + s * ((θs n).2 - σ₀)) + (ξ₀ + s * ((θs n).1 - ξ₀)) * x i := by
          have heq : (σ₀ + s * ((θs n).2 - σ₀)) + (ξ₀ + s * ((θs n).1 - ξ₀)) * x i =
              (1 - s) * (σ₀ + ξ₀ * x i) + s * ((θs n).2 + (θs n).1 * x i) := by ring
          rw [heq]; nlinarith [hs.1, hs.2, (hx i).2, hhalf i hi']
        have hus0 : 0 < (σ₀ + s * ((θs n).2 - σ₀)) + (ξ₀ + s * ((θs n).1 - ξ₀)) * x i :=
          lt_of_lt_of_le (half_pos (hx i).2) hus
        have hterm0 : 0 ≤ |log (1 + (ξ₀ + s * ((θs n).1 - ξ₀)) * x i / (σ₀ + s * ((θs n).2 - σ₀)))| +
            x i / ((σ₀ + s * ((θs n).2 - σ₀)) + (ξ₀ + s * ((θs n).1 - ξ₀)) * x i) +
            (x i / ((σ₀ + s * ((θs n).2 - σ₀)) + (ξ₀ + s * ((θs n).1 - ξ₀)) * x i)) ^ 2 + 1 := by
          have := div_nonneg (hx i).1 hus0.le; positivity
        exact (hHb _ _ _ (hx i).1 hus0).trans
          ((mul_le_mul (hb _ hmem).1 (le_gpdDom_of_half hξ₀' hσ₀ hmem (hx i).1 (hx i).2 hus)
            hterm0 hKc).trans_eq (by ring))
      have h2 : |H ξ₀ σ₀ (x i)| ≤ 4 * Kc * gpdDom ξ₀ σ₀ (x i) :=
        abs_gpdHess_self_le hξ₀' hσ₀ hHb (fun θ hθ => (hb θ hθ).1) (hx i).1 (hx i).2
      have := abs_sub (segHessW H ξ₀ σ₀ (θs n) (x i)) (H ξ₀ σ₀ (x i))
      linarith
  have h1 := abs_avg_sub_le hn5 hdev
  have htail0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i :=
    avg_nonneg fun i _ => gpdDomTail_nonneg hξ₀' hσ₀ (hx i).1 (hx i).2
  have h2 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, 8 * Kc * tail i ≤
      A * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) := by
    rw [← Finset.mul_sum, show (n : ℝ)⁻¹ * (8 * Kc * ∑ i ∈ Finset.range n, tail i) =
      8 * Kc * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) htail0
  have h3 : |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i) - m| < ε / 4 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hn4
  have h4 := abs_sub_le ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW H ξ₀ σ₀ (θs n) (x i))
    ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i)) m
  linarith

/-- Deterministic convergence of the averaged `segHessW` at `ξ₀ = 0`. -/
lemma eventually_abs_avg_segHessW_sub_le_zero {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    (hHb : ∀ θ ∈ gpdNbhdZero σ₀, ∀ x, 0 ≤ x → -(1 / 2 : ℝ) ≤ θ.1 * (x / θ.2) →
      |H θ.1 θ.2 x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x)
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i)
    {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (0, σ₀)))
    {m : ℝ} (hm : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (x i))
      atTop (𝓝 m))
    {d : ℕ → ℝ} (hD : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomZeroTail σ₀ (k : ℝ) (x i)) atTop (𝓝 (d k)))
    (hd : Tendsto d atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (∀ i < n, -(1 / 2 : ℝ) ≤ (θs n).1 * (x i / (θs n).2)) →
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW H 0 σ₀ (θs n) (x i) - m| ≤ ε := by
  set C := gpdZeroConst σ₀
  have hC : 0 < C := gpdZeroConst_pos hσ₀
  set A := 2 * C + 1
  have hA : 0 < A := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A * d k < ε / 4 := by
    have h := hd.const_mul A; rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  have hgood_delta : ∃ δ > 0, ∀ θ, gpdDist 0 σ₀ θ ≤ δ → ∀ y, 0 ≤ y → y ≤ (k : ℝ) →
      |segHessW H 0 σ₀ θ y - H 0 σ₀ y| ≤ ε / 4 := by
    set r₀ := min (min (1 / 4 : ℝ) (σ₀ / 8)) (σ₀ / (4 * ((k : ℝ) + 1)))
    have hr₀ : 0 < r₀ := by positivity
    set Kp : Set (ℝ × ℝ) := Icc (-r₀) r₀ ×ˢ Icc (σ₀ - r₀) (σ₀ + r₀)
    set Kx : Set ℝ := Icc 0 (k : ℝ)
    have hKc_set : IsCompact (Kp ×ˢ Kx) :=
      (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
    have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => H q.1.1 q.1.2 q.2) (Kp ×ˢ Kx) := by
      rintro ⟨⟨ξ, σ⟩, y⟩ ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨hy0, hy1⟩⟩
      have hr2 : r₀ ≤ σ₀ / 8 := (min_le_left _ _).trans (min_le_right _ _)
      have hr3 : r₀ ≤ σ₀ / (4 * ((k : ℝ) + 1)) := min_le_right _ _
      have hσ_pos : 0 < σ := by linarith
      have hu : 0 < σ + ξ * y := by
        have hstep : r₀ * ((k : ℝ) + 1) ≤ σ₀ / 4 := by
          have := (le_div_iff₀ (show 0 < 4 * ((k : ℝ) + 1) by positivity)).1 hr3; linarith
        have hξy : |ξ * y| ≤ r₀ * (k : ℝ) := by
          rw [abs_mul, abs_of_nonneg hy0]
          exact mul_le_mul (abs_le.2 ⟨h1, h2⟩) hy1 hy0 hr₀.le
        linarith [(abs_le.1 hξy).1]
      exact (ContinuousAt.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
        (g := fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) (x := ((ξ, σ), y))
        (hH (ξ, σ, y) hσ_pos hu) (by fun_prop)).continuousWithinAt
    have huc := hKc_set.uniformContinuousOn_of_continuous hcont
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨η, hη, hη_bd⟩ := huc (ε / 4) (by positivity)
    refine ⟨min r₀ (η / 2), lt_min hr₀ (by positivity), fun θ hθd y hy0 hyk => ?_⟩
    have hθ0_mem : ((0, σ₀), y) ∈ Kp ×ˢ Kx :=
      ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ⟨hy0, hyk⟩⟩
    refine abs_segHessW_sub_le_of_forall hHm (by positivity) fun s hs => ?_
    have hd_r0 : gpdDist 0 σ₀ θ ≤ r₀ := hθd.trans (min_le_left _ _)
    have hd_eta : gpdDist 0 σ₀ θ ≤ η / 2 := hθd.trans (min_le_right _ _)
    have hθs_mem : ((0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀)), y) ∈ Kp ×ˢ Kx := by
      have ha : |s * (θ.1 - 0)| ≤ r₀ := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_r0)
      have hb' : |s * (θ.2 - σ₀)| ≤ r₀ := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_r0)
      rw [abs_le] at ha hb'
      exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ⟨hy0, hyk⟩⟩
    have hdist : dist ((0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀)), y) ((0, σ₀), y) < η := by
      simp only [Prod.dist_eq, dist_self, Real.dist_eq, add_sub_cancel_left]
      have ha : |s * (θ.1 - 0)| ≤ η / 2 := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_eta)
      have hb' : |s * (θ.2 - σ₀)| ≤ η / 2 := by
        rw [abs_mul, abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
          ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_eta)
      exact max_lt (max_lt (by linarith) (by linarith)) hη
    exact (hη_bd _ hθs_mem _ hθ0_mem hdist).le
  obtain ⟨δ, hδ, hgood⟩ := hgood_delta
  filter_upwards [tendsto_gpdDist hθ hδ, hθ.eventually (gpdNbhdZero_mem_nhds hσ₀),
    ((hD k).const_mul A).eventually (gt_mem_nhds hk),
    hm.eventually (Metric.ball_mem_nhds m (show 0 < ε / 4 by positivity)),
    eventually_gt_atTop 0] with n hn1 hn2 hn3 hn4 hn5 hsafe
  set tail : ℕ → ℝ := fun i => gpdDomZeroTail σ₀ (k : ℝ) (x i)
  have hdev : ∀ i < n,
      |segHessW H 0 σ₀ (θs n) (x i) - H 0 σ₀ (x i)| ≤ ε / 4 + 2 * C * tail i := fun i hi' => by
    by_cases hle : x i ≤ (k : ℝ)
    · rw [show tail i = 0 from gpdDomZeroTail_of_le hle, mul_zero, add_zero]
      exact hgood _ hn1 _ (hx i) hle
    · rw [show tail i = gpdDomZero σ₀ (x i) from gpdDomZeroTail_of_lt (not_le.1 hle)]
      have hdom0 : 0 ≤ gpdDomZero σ₀ (x i) := by unfold gpdDomZero; have := hx i; positivity
      have h1 : |segHessW H 0 σ₀ (θs n) (x i)| ≤ C * gpdDomZero σ₀ (x i) := by
        refine abs_segHessW_le_of_forall hHm
          (mul_nonneg hC.le hdom0) fun s hs => ?_
        have hmem := segment_mem_gpdNbhdZero hσ₀ hn2 hs
        have hσs : 0 < σ₀ + s * ((θs n).2 - σ₀) := by linarith [hmem.2.1]
        have hσθ : 0 < (θs n).2 := by linarith [hn2.2.1]
        have hts : -(1 / 2 : ℝ) ≤ (0 + s * ((θs n).1 - 0)) * (x i / (σ₀ + s * ((θs n).2 - σ₀))) := by
          have h1s : (θs n).2 / 2 ≤ (θs n).2 + (θs n).1 * x i := by
            have := hsafe i hi'
            have heq : (θs n).1 * (x i / (θs n).2) = (θs n).1 * x i / (θs n).2 := by ring
            rw [heq, le_div_iff₀ hσθ] at this; linarith
          have hconv : (σ₀ + s * ((θs n).2 - σ₀)) / 2 ≤
              (σ₀ + s * ((θs n).2 - σ₀)) + (0 + s * ((θs n).1 - 0)) * x i := by
            have heq : (σ₀ + s * ((θs n).2 - σ₀)) + (0 + s * ((θs n).1 - 0)) * x i =
                (1 - s) * σ₀ + s * ((θs n).2 + (θs n).1 * x i) := by ring
            rw [heq]; nlinarith [hs.1, hs.2, hσ₀, h1s]
          have heq2 : (0 + s * ((θs n).1 - 0)) * (x i / (σ₀ + s * ((θs n).2 - σ₀))) =
              ((0 + s * ((θs n).1 - 0)) * x i) / (σ₀ + s * ((θs n).2 - σ₀)) := by ring
          rw [heq2, le_div_iff₀ hσs]; linarith
        exact hHb _ hmem _ (hx i) hts
      have h2 := hHb (0, σ₀) (mem_gpdNbhdZero_self hσ₀) (x i) (hx i) (by simp)
      have := abs_sub (segHessW H 0 σ₀ (θs n) (x i)) (H 0 σ₀ (x i))
      linarith
  have h1 := abs_avg_sub_le hn5 hdev
  have htail0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i :=
    avg_nonneg fun i _ => gpdDomZeroTail_nonneg hσ₀ (hx i)
  have h2 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, 2 * C * tail i ≤
      A * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) := by
    rw [← Finset.mul_sum, show (n : ℝ)⁻¹ * (2 * C * ∑ i ∈ Finset.range n, tail i) =
      2 * C * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) htail0
  have h3 : |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (x i) - m| < ε / 4 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hn4
  have h4 := abs_sub_le ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW H 0 σ₀ (θs n) (x i))
    ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (x i)) m
  linarith

end WeightedConv

/-! ### General probability-convergence Wilks engines (no third derivatives) -/

section WilksEngine

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Product of two sequences bounded in probability is bounded in probability. -/
lemma isBoundedInProbability_mul {U V : ℕ → Ω → ℝ}
    (hU : IsBoundedInProbability P U) (hV : IsBoundedInProbability P V) :
    IsBoundedInProbability P fun n ω => U n ω * V n ω := by
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨M₁, hM₁⟩ := hU _ hε2
  obtain ⟨M₂, hM₂⟩ := hV _ hε2
  set M := max M₁ 0 * max M₂ 0
  refine ⟨M, ?_⟩
  filter_upwards [hM₁, hM₂] with n h1 h2
  refine (measure_mono (t := {ω | M₁ < |U n ω|} ∪ {ω | M₂ < |V n ω|}) ?_).trans
    ((measure_union_le _ _).trans ((add_le_add h1 h2).trans (ENNReal.add_halves ε).le))
  intro ω hω
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  rw [abs_mul] at hω
  have hprod : |U n ω| * |V n ω| ≤ max M₁ 0 * max M₂ 0 :=
    mul_le_mul (hcon.1.trans (le_max_left _ _)) (hcon.2.trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)
  linarith

/-- **Full-parameter Wilks engine in probability (exact second-order Taylor)**:
if `S₁, S₂ = O_P(1)`, `Bᵢⱼ, Cᵢⱼ → -Iᵢⱼ` in probability (`A C - B² > 0`), and a.s. eventually
`S₁ + B₁₁ T₁ + B₁₂ T₂ = 0`, `S₂ + B₁₂ T₁ + B₂₂ T₂ = 0`, and
`D = 2 (T₁ S₁ + T₂ S₂) + T₁² C₁₁ + 2 T₁ T₂ C₁₂ + T₂² C₂₂`, then
`D - (C S₁² - 2 B S₁ S₂ + A S₂²) / (A C - B²) → 0` in probability. -/
theorem tendstoInMeasure_full_deviance_of_converge
    {A B C : ℝ} (hd : 0 < A * C - B ^ 2)
    {S₁ S₂ T₁ T₂ B₁₁ B₁₂ B₂₂ C₁₁ C₁₂ C₂₂ D : ℕ → Ω → ℝ}
    (hS₁m : ∀ n, AEMeasurable (S₁ n) P) (hS₂m : ∀ n, AEMeasurable (S₂ n) P)
    (hB₁₁m : ∀ n, AEMeasurable (B₁₁ n) P) (hB₁₂m : ∀ n, AEMeasurable (B₁₂ n) P)
    (hB₂₂m : ∀ n, AEMeasurable (B₂₂ n) P)
    (hC₁₁m : ∀ n, AEMeasurable (C₁₁ n) P) (hC₁₂m : ∀ n, AEMeasurable (C₁₂ n) P)
    (hC₂₂m : ∀ n, AEMeasurable (C₂₂ n) P)
    (hDm : ∀ n, AEMeasurable (D n) P)
    (hS₁b : IsBoundedInProbability P S₁) (hS₂b : IsBoundedInProbability P S₂)
    (hB₁₁ : TendstoInMeasure P B₁₁ atTop (fun _ => -A))
    (hB₁₂ : TendstoInMeasure P B₁₂ atTop (fun _ => -B))
    (hB₂₂ : TendstoInMeasure P B₂₂ atTop (fun _ => -C))
    (hC₁₁ : TendstoInMeasure P C₁₁ atTop (fun _ => -A))
    (hC₁₂ : TendstoInMeasure P C₁₂ atTop (fun _ => -B))
    (hC₂₂ : TendstoInMeasure P C₂₂ atTop (fun _ => -C))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      S₁ n ω + B₁₁ n ω * T₁ n ω + B₁₂ n ω * T₂ n ω = 0 ∧
      S₂ n ω + B₁₂ n ω * T₁ n ω + B₂₂ n ω * T₂ n ω = 0)
    (hD : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      D n ω = 2 * (T₁ n ω * S₁ n ω + T₂ n ω * S₂ n ω) +
        (T₁ n ω ^ 2 * C₁₁ n ω + 2 * T₁ n ω * T₂ n ω * C₁₂ n ω + T₂ n ω ^ 2 * C₂₂ n ω)) :
    TendstoInMeasure P (fun n ω =>
      D n ω - (C * S₁ n ω ^ 2 - 2 * B * S₁ n ω * S₂ n ω + A * S₂ n ω ^ 2) / (A * C - B ^ 2))
      atTop (fun _ => 0) := by
  set d := A * C - B ^ 2
  set Dn : ℕ → Ω → ℝ := fun n ω => B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2
  have hDn : TendstoInMeasure P Dn atTop (fun _ => d) := by
    have h := tendstoInMeasure_comp₂ (tendstoInMeasure_mul hB₁₁ hB₂₂)
      (tendstoInMeasure_comp hB₁₂ (φ := fun z => z ^ 2) (by fun_prop))
      (φ := fun p => p.1 - p.2) (by fun_prop)
    convert h using 2; simp only [d]; ring
  -- Coefficients `p₁₁ = -B₂₂/Dn`, `p₁₂ = B₁₂/Dn`, `p₂₂ = -B₁₁/Dn` of `T = P S`
  set p₁₁ : ℕ → Ω → ℝ := fun n ω => -B₂₂ n ω / Dn n ω
  set p₁₂ : ℕ → Ω → ℝ := fun n ω => B₁₂ n ω / Dn n ω
  set p₂₂ : ℕ → Ω → ℝ := fun n ω => -B₁₁ n ω / Dn n ω
  have hp₁₁ : TendstoInMeasure P p₁₁ atTop (fun _ => C / d) := by
    have h := tendstoInMeasure_comp₂ hB₂₂ hDn (φ := fun p => -p.1 / p.2)
      (continuous_fst.neg.continuousAt.div continuous_snd.continuousAt hd.ne')
    simpa [neg_neg] using h
  have hp₁₂ : TendstoInMeasure P p₁₂ atTop (fun _ => -B / d) :=
    tendstoInMeasure_comp₂ hB₁₂ hDn (φ := fun p => p.1 / p.2)
      (continuous_fst.continuousAt.div continuous_snd.continuousAt hd.ne')
  have hp₂₂ : TendstoInMeasure P p₂₂ atTop (fun _ => A / d) := by
    have h := tendstoInMeasure_comp₂ hB₁₁ hDn (φ := fun p => -p.1 / p.2)
      (continuous_fst.neg.continuousAt.div continuous_snd.continuousAt hd.ne')
    simpa [neg_neg] using h
  -- Express `D_exact = (2 p₁₁ + p₁₁² C₁₁ + 2 p₁₁ p₁₂ C₁₂ + p₁₂² C₂₂) S₁² + ...`
  set e₁₁ : ℕ → Ω → ℝ := fun n ω =>
    (2 * p₁₁ n ω + p₁₁ n ω ^ 2 * C₁₁ n ω + 2 * p₁₁ n ω * p₁₂ n ω * C₁₂ n ω + p₁₂ n ω ^ 2 * C₂₂ n ω) -
      C / d
  set e₁₂ : ℕ → Ω → ℝ := fun n ω =>
    (4 * p₁₂ n ω + 2 * p₁₁ n ω * p₁₂ n ω * C₁₁ n ω +
      2 * (p₁₁ n ω * p₂₂ n ω + p₁₂ n ω ^ 2) * C₁₂ n ω + 2 * p₁₂ n ω * p₂₂ n ω * C₂₂ n ω) -
      (-2 * B / d)
  set e₂₂ : ℕ → Ω → ℝ := fun n ω =>
    (2 * p₂₂ n ω + p₁₂ n ω ^ 2 * C₁₁ n ω + 2 * p₁₂ n ω * p₂₂ n ω * C₁₂ n ω + p₂₂ n ω ^ 2 * C₂₂ n ω) -
      A / d
  have he₁₁ : TendstoInMeasure P e₁₁ atTop (fun _ => 0) := by
    have h1 := tendstoInMeasure_comp hp₁₁ (φ := fun x => 2 * x) (by fun_prop)
    have h2 := tendstoInMeasure_mul (tendstoInMeasure_comp hp₁₁ (φ := fun x => x ^ 2) (by fun_prop)) hC₁₁
    have h3 := tendstoInMeasure_mul (tendstoInMeasure_comp₂ hp₁₁ hp₁₂ (φ := fun p => 2 * p.1 * p.2) (by fun_prop)) hC₁₂
    have h4 := tendstoInMeasure_mul (tendstoInMeasure_comp hp₁₂ (φ := fun x => x ^ 2) (by fun_prop)) hC₂₂
    have hsum := tendstoInMeasure_comp₂ (tendstoInMeasure_comp₂ (tendstoInMeasure_comp₂ h1 h2
      (φ := fun p => p.1 + p.2) (by fun_prop)) h3 (φ := fun p => p.1 + p.2) (by fun_prop))
      h4 (φ := fun p => p.1 + p.2 - C / d) (by fun_prop)
    convert hsum using 2
    simp only [d]; field_simp [hd.ne']; ring
  have he₁₂ : TendstoInMeasure P e₁₂ atTop (fun _ => 0) := by
    have h1 := tendstoInMeasure_comp hp₁₂ (φ := fun x => 4 * x) (by fun_prop)
    have h2 := tendstoInMeasure_mul (tendstoInMeasure_comp₂ hp₁₁ hp₁₂ (φ := fun p => 2 * p.1 * p.2) (by fun_prop)) hC₁₁
    have h3 := tendstoInMeasure_mul
      (tendstoInMeasure_comp₂ (tendstoInMeasure_mul hp₁₁ hp₂₂)
        (tendstoInMeasure_comp hp₁₂ (φ := fun x => x ^ 2) (by fun_prop))
        (φ := fun p => 2 * (p.1 + p.2)) (by fun_prop)) hC₁₂
    have h4 := tendstoInMeasure_mul (tendstoInMeasure_comp₂ hp₁₂ hp₂₂ (φ := fun p => 2 * p.1 * p.2) (by fun_prop)) hC₂₂
    have hsum := tendstoInMeasure_comp₂ (tendstoInMeasure_comp₂ (tendstoInMeasure_comp₂ h1 h2
      (φ := fun p => p.1 + p.2) (by fun_prop)) h3 (φ := fun p => p.1 + p.2) (by fun_prop))
      h4 (φ := fun p => p.1 + p.2 - (-2 * B / d)) (by fun_prop)
    convert hsum using 2
    simp only [d]; field_simp [hd.ne']; ring
  have he₂₂ : TendstoInMeasure P e₂₂ atTop (fun _ => 0) := by
    have h1 := tendstoInMeasure_comp hp₂₂ (φ := fun x => 2 * x) (by fun_prop)
    have h2 := tendstoInMeasure_mul (tendstoInMeasure_comp hp₁₂ (φ := fun x => x ^ 2) (by fun_prop)) hC₁₁
    have h3 := tendstoInMeasure_mul (tendstoInMeasure_comp₂ hp₁₂ hp₂₂ (φ := fun p => 2 * p.1 * p.2) (by fun_prop)) hC₁₂
    have h4 := tendstoInMeasure_mul (tendstoInMeasure_comp hp₂₂ (φ := fun x => x ^ 2) (by fun_prop)) hC₂₂
    have hsum := tendstoInMeasure_comp₂ (tendstoInMeasure_comp₂ (tendstoInMeasure_comp₂ h1 h2
      (φ := fun p => p.1 + p.2) (by fun_prop)) h3 (φ := fun p => p.1 + p.2) (by fun_prop))
      h4 (φ := fun p => p.1 + p.2 - A / d) (by fun_prop)
    convert hsum using 2
    simp only [d]; field_simp [hd.ne']; ring
  set G : ℕ → Ω → ℝ := fun n ω =>
    e₁₁ n ω * (S₁ n ω * S₁ n ω) + e₁₂ n ω * (S₁ n ω * S₂ n ω) + e₂₂ n ω * (S₂ n ω * S₂ n ω)
  have hG : TendstoInMeasure P G atTop (fun _ => 0) := by
    have t1 := tendstoInMeasure_mul_zero_of_isBoundedInProbability'
      (isBoundedInProbability_mul hS₁b hS₁b) he₁₁
    have t2 := tendstoInMeasure_mul_zero_of_isBoundedInProbability'
      (isBoundedInProbability_mul hS₁b hS₂b) he₁₂
    have t3 := tendstoInMeasure_mul_zero_of_isBoundedInProbability'
      (isBoundedInProbability_mul hS₂b hS₂b) he₂₂
    exact tendstoInMeasure_add_zero (tendstoInMeasure_add_zero
      (by simpa [mul_comm] using t1) (by simpa [mul_comm] using t2)) (by simpa [mul_comm] using t3)
  -- On `{|Dn - d| < d/2}` and the a.s. eventual event, `D - Sᵀ I⁻¹ S = G`!
  set H : ℕ → Ω → ℝ := fun n ω =>
    (D n ω - (C * S₁ n ω ^ 2 - 2 * B * S₁ n ω * S₂ n ω + A * S₂ n ω ^ 2) / d) - G n ω
  have hHm : ∀ n, AEMeasurable (H n) P := fun n => by
    have := hDm n; have := hS₁m n; have := hS₂m n
    have := hB₁₁m n; have := hB₁₂m n; have := hB₂₂m n
    have := hC₁₁m n; have := hC₁₂m n; have := hC₂₂m n
    dsimp only [H, G, e₁₁, e₁₂, e₂₂, p₁₁, p₁₂, p₂₂, Dn]
    fun_prop
  have hDnm : ∀ n, AEMeasurable (Dn n) P := fun n => by
    have := hB₁₁m n; have := hB₁₂m n; have := hB₂₂m n
    dsimp only [Dn]; fun_prop
  -- `H * 1_{|Dn - d| < d/2} → 0` a.e., hence in probability!
  set ind : ℕ → Ω → ℝ := fun n ω => if |Dn n ω - d| < d / 2 then 1 else 0
  have hindm : ∀ n, AEMeasurable (ind n) P := fun n => by
    have hlt : AEMeasurable (fun ω => |Dn n ω - d|) P := (hDnm n).sub_const d |>.abs
    exact (Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const).comp_aemeasurable hlt
  have hH_ind : TendstoInMeasure P (fun n ω => H n ω * ind n ω) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ((hHm n).mul (hindm n)).aestronglyMeasurable) ?_
    filter_upwards [hroot, hD] with ω hr hDn'
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hr, hDn'] with n ⟨hr1, hr2⟩ hD_eq
    by_cases hgood : |Dn n ω - d| < d / 2
    · have hDn_ne : Dn n ω ≠ 0 := by
        have := (abs_lt.1 hgood).1; linarith
      have hT1 : T₁ n ω = p₁₁ n ω * S₁ n ω + p₁₂ n ω * S₂ n ω := by
        simp only [p₁₁, p₁₂, Dn]
        have hlin : (B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) * T₁ n ω =
            -B₂₂ n ω * S₁ n ω + B₁₂ n ω * S₂ n ω := by
          linear_combination B₂₂ n ω * hr1 - B₁₂ n ω * hr2
        have hne : B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2 ≠ 0 := hDn_ne
        calc T₁ n ω = ((B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) * T₁ n ω) /
              (B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) := (mul_div_cancel_left₀ _ hne).symm
          _ = (-B₂₂ n ω * S₁ n ω + B₁₂ n ω * S₂ n ω) /
              (B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) := by rw [hlin]
          _ = _ := by ring
      have hT2 : T₂ n ω = p₁₂ n ω * S₁ n ω + p₂₂ n ω * S₂ n ω := by
        simp only [p₁₂, p₂₂, Dn]
        have hlin : (B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) * T₂ n ω =
            B₁₂ n ω * S₁ n ω - B₁₁ n ω * S₂ n ω := by
          linear_combination -B₁₂ n ω * hr1 + B₁₁ n ω * hr2
        have hne : B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2 ≠ 0 := hDn_ne
        calc T₂ n ω = ((B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) * T₂ n ω) /
              (B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) := (mul_div_cancel_left₀ _ hne).symm
          _ = (B₁₂ n ω * S₁ n ω - B₁₁ n ω * S₂ n ω) /
              (B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2) := by rw [hlin]
          _ = _ := by ring
      have hH0 : H n ω = 0 := by
        have hd' : d ≠ 0 := hd.ne'
        simp only [H, G, e₁₁, e₁₂, e₂₂, hD_eq, hT1, hT2]
        field_simp [hd']; ring
      simp [ind, hgood, hH0]
    · simp [ind, hgood]
  -- Combine `H * ind → 0`, `P(|Dn - d| ≥ d/2) → 0`, and `G → 0`!
  rw [tendstoInMeasure_iff_norm] at hG hDn hH_ind ⊢
  intro ε hε
  have hsum : Tendsto (fun n =>
      P {ω | ε / 2 ≤ ‖H n ω * ind n ω - 0‖} +
      P {ω | d / 2 ≤ ‖Dn n ω - d‖} +
      P {ω | ε / 2 ≤ ‖G n ω - 0‖}) atTop (𝓝 0) := by
    simpa using ((hH_ind (ε / 2) (by positivity)).add (hDn (d / 2) (by positivity))).add
      (hG (ε / 2) (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
  refine (measure_mono fun ω hω => ?_).trans
    ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  by_contra hnot
  simp only [mem_union, mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs, sub_zero] at hω hnot
  obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
  have hind1 : ind n ω = 1 := ite_eq_left h2
  rw [hind1, mul_one] at h1
  have htri : |D n ω - (C * S₁ n ω ^ 2 - 2 * B * S₁ n ω * S₂ n ω + A * S₂ n ω ^ 2) / d| ≤
      |H n ω| + |G n ω| := by
    have : D n ω - (C * S₁ n ω ^ 2 - 2 * B * S₁ n ω * S₂ n ω + A * S₂ n ω ^ 2) / d =
        H n ω + G n ω := by simp [H]
    rw [this]; exact abs_add_le _ _
  linarith

/-- Algebraic error bound for the curve-restricted Wilks deviance: near `(-A, -B, -C, -A, -B, -C, t₁, t₂, t₁, t₂)`,
any solution of the curve stationarity equation and exact second-order deviance equation satisfies
`|D - (t₁ S₁ + t₂ S₂)² / c| ≤ η * (1 + S₁² + S₂²)`. -/
private lemma exists_delta_curve_deviance_err {A B C t₁ t₂ η : ℝ}
    (hc : 0 < A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2) (hη : 0 < η) :
    ∃ δ > 0, ∀ (b₁₁ b₁₂ b₂₂ c₁₁ c₁₂ c₂₂ sl₁ sl₂ tn₁ tn₂ S₁ S₂ τ D : ℝ),
      |b₁₁ - (-A)| < δ → |b₁₂ - (-B)| < δ → |b₂₂ - (-C)| < δ →
      |c₁₁ - (-A)| < δ → |c₁₂ - (-B)| < δ → |c₂₂ - (-C)| < δ →
      |sl₁ - t₁| < δ → |sl₂ - t₂| < δ → |tn₁ - t₁| < δ → |tn₂ - t₂| < δ →
      tn₁ * (S₁ + τ * (sl₁ * b₁₁ + sl₂ * b₁₂)) +
        tn₂ * (S₂ + τ * (sl₁ * b₁₂ + sl₂ * b₂₂)) = 0 →
      D = 2 * τ * (sl₁ * S₁ + sl₂ * S₂) +
        τ ^ 2 * (sl₁ ^ 2 * c₁₁ + 2 * sl₁ * sl₂ * c₁₂ + sl₂ ^ 2 * c₂₂) →
      |D - (t₁ * S₁ + t₂ * S₂) ^ 2 / (A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2)| ≤
        η * (1 + S₁ ^ 2 + S₂ ^ 2) := by
  set c := A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2
  let CnF : (Fin 10 → ℝ) → ℝ := fun v =>
    -(v 8 * (v 6 * v 0 + v 7 * v 1) + v 9 * (v 6 * v 1 + v 7 * v 2))
  let QnF : (Fin 10 → ℝ) → ℝ := fun v =>
    v 6 ^ 2 * v 3 + 2 * v 6 * v 7 * v 4 + v 7 ^ 2 * v 5
  let q₁F : (Fin 10 → ℝ) → ℝ := fun v => v 8 / CnF v
  let q₂F : (Fin 10 → ℝ) → ℝ := fun v => v 9 / CnF v
  let e₁₁F : (Fin 10 → ℝ) → ℝ := fun v => (2 * q₁F v * v 6 + q₁F v ^ 2 * QnF v) - t₁ ^ 2 / c
  let e₁₂F : (Fin 10 → ℝ) → ℝ := fun v =>
    (2 * (q₁F v * v 7 + q₂F v * v 6) + 2 * q₁F v * q₂F v * QnF v) - 2 * t₁ * t₂ / c
  let e₂₂F : (Fin 10 → ℝ) → ℝ := fun v => (2 * q₂F v * v 7 + q₂F v ^ 2 * QnF v) - t₂ ^ 2 / c
  let v₀ : Fin 10 → ℝ := ![-A, -B, -C, -A, -B, -C, t₁, t₂, t₁, t₂]
  have hCn₀ : CnF v₀ = c := by simp only [CnF, v₀, c, Matrix.cons_val]; ring
  have hQn₀ : QnF v₀ = -c := by simp only [QnF, v₀, c, Matrix.cons_val]; ring
  have he₁₁₀ : e₁₁F v₀ = 0 := by
    simp only [e₁₁F, q₁F, hCn₀, hQn₀, v₀, Matrix.cons_val]; field_simp [hc.ne']; ring
  have he₁₂₀ : e₁₂F v₀ = 0 := by
    simp only [e₁₂F, q₁F, q₂F, hCn₀, hQn₀, v₀, Matrix.cons_val]; field_simp [hc.ne']; ring
  have he₂₂₀ : e₂₂F v₀ = 0 := by
    simp only [e₂₂F, q₂F, hCn₀, hQn₀, v₀, Matrix.cons_val]; field_simp [hc.ne']; ring
  have hCn_cont : ContinuousAt CnF v₀ := by
    dsimp only [CnF]; fun_prop
  have hQn_cont : ContinuousAt QnF v₀ := by
    dsimp only [QnF]; fun_prop
  have hq₁_cont : ContinuousAt q₁F v₀ :=
    (continuous_apply 8).continuousAt.div hCn_cont (by rw [hCn₀]; exact hc.ne')
  have hq₂_cont : ContinuousAt q₂F v₀ :=
    (continuous_apply 9).continuousAt.div hCn_cont (by rw [hCn₀]; exact hc.ne')
  have he_cont : ContinuousAt (fun v => |e₁₁F v| + |e₁₂F v| + |e₂₂F v|) v₀ := by
    have c1 : ContinuousAt e₁₁F v₀ := by
      dsimp only [e₁₁F]
      exact (((continuousAt_const.mul hq₁_cont).mul (continuous_apply 6).continuousAt).add
        ((hq₁_cont.pow 2).mul hQn_cont)).sub continuousAt_const
    have c2 : ContinuousAt e₁₂F v₀ := by
      dsimp only [e₁₂F]
      exact ((continuousAt_const.mul ((hq₁_cont.mul (continuous_apply 7).continuousAt).add
        (hq₂_cont.mul (continuous_apply 6).continuousAt))).add
        (((continuousAt_const.mul hq₁_cont).mul hq₂_cont).mul hQn_cont)).sub continuousAt_const
    have c3 : ContinuousAt e₂₂F v₀ := by
      dsimp only [e₂₂F]
      exact (((continuousAt_const.mul hq₂_cont).mul (continuous_apply 7).continuousAt).add
        ((hq₂_cont.pow 2).mul hQn_cont)).sub continuousAt_const
    exact (c1.abs.add c2.abs).add c3.abs
  have hnhds : ∀ᶠ v in 𝓝 v₀, 0 < CnF v ∧ |e₁₁F v| + |e₁₂F v| + |e₂₂F v| < η := by
    refine (hCn_cont.eventually (lt_mem_nhds (by rw [hCn₀]; exact hc))).and ?_
    refine he_cont.eventually (gt_mem_nhds ?_)
    simp only [he₁₁₀, he₁₂₀, he₂₂₀, abs_zero, add_zero]; exact hη
  obtain ⟨δ, hδ, hδ_ball⟩ := Metric.eventually_nhds_iff.1 hnhds
  refine ⟨δ, hδ, fun b₁₁ b₁₂ b₂₂ c₁₁ c₁₂ c₂₂ sl₁ sl₂ tn₁ tn₂ S₁ S₂ τ D
    hb1 hb2 hb3 hc1 hc2 hc3 hs1 hs2 ht1 ht2 hroot hD => ?_⟩
  let v : Fin 10 → ℝ := ![b₁₁, b₁₂, b₂₂, c₁₁, c₁₂, c₂₂, sl₁, sl₂, tn₁, tn₂]
  have hv_dist : dist v v₀ < δ := by
    rw [dist_pi_lt_iff hδ]
    intro i
    fin_cases i
    · simpa [v, v₀, Real.dist_eq] using hb1
    · simpa [v, v₀, Real.dist_eq] using hb2
    · simpa [v, v₀, Real.dist_eq] using hb3
    · simpa [v, v₀, Real.dist_eq] using hc1
    · simpa [v, v₀, Real.dist_eq] using hc2
    · simpa [v, v₀, Real.dist_eq] using hc3
    · simpa [v, v₀, Real.dist_eq] using hs1
    · simpa [v, v₀, Real.dist_eq] using hs2
    · simpa [v, v₀, Real.dist_eq] using ht1
    · simpa [v, v₀, Real.dist_eq] using ht2
  obtain ⟨hCnp, hep⟩ := hδ_ball hv_dist
  have hCn_val : CnF v = -(tn₁ * (sl₁ * b₁₁ + sl₂ * b₁₂) + tn₂ * (sl₁ * b₁₂ + sl₂ * b₂₂)) := by
    simp [CnF, v]
  have hQn_val : QnF v = sl₁ ^ 2 * c₁₁ + 2 * sl₁ * sl₂ * c₁₂ + sl₂ ^ 2 * c₂₂ := by
    simp [QnF, v]
  have hτ : τ = q₁F v * S₁ + q₂F v * S₂ := by
    have hlin : CnF v * τ = tn₁ * S₁ + tn₂ * S₂ := by rw [hCn_val]; linear_combination -hroot
    have h1 : q₁F v = tn₁ / CnF v := by simp [q₁F, v]
    have h2 : q₂F v = tn₂ / CnF v := by simp [q₂F, v]
    rw [h1, h2]; field_simp [hCnp.ne']; linear_combination hlin
  have hdiff : D - (t₁ * S₁ + t₂ * S₂) ^ 2 / c =
      e₁₁F v * S₁ ^ 2 + e₁₂F v * (S₁ * S₂) + e₂₂F v * S₂ ^ 2 := by
    have hv6 : v 6 = sl₁ := by simp [v]
    have hv7 : v 7 = sl₂ := by simp [v]
    have he1 : e₁₁F v = (2 * q₁F v * sl₁ + q₁F v ^ 2 * QnF v) - t₁ ^ 2 / c := by
      simp only [e₁₁F, hv6]
    have he2 : e₁₂F v = (2 * (q₁F v * sl₂ + q₂F v * sl₁) + 2 * q₁F v * q₂F v * QnF v) - 2 * t₁ * t₂ / c := by
      simp only [e₁₂F, hv6, hv7]
    have he3 : e₂₂F v = (2 * q₂F v * sl₂ + q₂F v ^ 2 * QnF v) - t₂ ^ 2 / c := by
      simp only [e₂₂F, hv7]
    have hc' : c ≠ 0 := hc.ne'
    rw [hD, ← hQn_val, hτ, he1, he2, he3]
    field_simp [hc']; ring
  have hden_pos : 0 < 1 + S₁ ^ 2 + S₂ ^ 2 := by positivity
  have hprod_le : |S₁ * S₂| ≤ 1 + S₁ ^ 2 + S₂ ^ 2 := by
    rw [abs_mul]; nlinarith only [sq_nonneg (|S₁| - |S₂|), sq_abs S₁, sq_abs S₂]
  have hs1_le : S₁ ^ 2 ≤ 1 + S₁ ^ 2 + S₂ ^ 2 := by nlinarith only [sq_nonneg S₂]
  have hs2_le : S₂ ^ 2 ≤ 1 + S₁ ^ 2 + S₂ ^ 2 := by nlinarith only [sq_nonneg S₁]
  rw [hdiff]
  calc |e₁₁F v * S₁ ^ 2 + e₁₂F v * (S₁ * S₂) + e₂₂F v * S₂ ^ 2|
      ≤ |e₁₁F v * S₁ ^ 2| + |e₁₂F v * (S₁ * S₂)| + |e₂₂F v * S₂ ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |e₁₁F v| * S₁ ^ 2 + |e₁₂F v| * |S₁ * S₂| + |e₂₂F v| * S₂ ^ 2 := by
        simp only [abs_mul, abs_pow, sq_abs]
    _ ≤ |e₁₁F v| * (1 + S₁ ^ 2 + S₂ ^ 2) + |e₁₂F v| * (1 + S₁ ^ 2 + S₂ ^ 2) +
          |e₂₂F v| * (1 + S₁ ^ 2 + S₂ ^ 2) := by gcongr
    _ = (|e₁₁F v| + |e₁₂F v| + |e₂₂F v|) * (1 + S₁ ^ 2 + S₂ ^ 2) := by ring
    _ ≤ η * (1 + S₁ ^ 2 + S₂ ^ 2) := mul_le_mul_of_nonneg_right hep.le hden_pos.le

/-- **Curve-restricted Wilks engine in probability (exact second-order Taylor, no measurability of
curve coordinates needed)**: if `S₁, S₂ = O_P(1)`, `Bᵢⱼ, Cᵢⱼ → -Iᵢⱼ` in probability, `c = A t₁² + 2 B t₁ t₂ + C t₂² > 0`, and a.s. there exist sequences `τ, sl₁, sl₂, tn₁, tn₂` with `slᵢ, tnᵢ → tᵢ`
such that eventually
`tn₁ (S₁ + τ (sl₁ B₁₁ + sl₂ B₁₂)) + tn₂ (S₂ + τ (sl₁ B₁₂ + sl₂ B₂₂)) = 0` and
`D = 2 τ (sl₁ S₁ + sl₂ S₂) + τ² (sl₁² C₁₁ + 2 sl₁ sl₂ C₁₂ + sl₂² C₂₂)`, then
`D - (t₁ S₁ + t₂ S₂)² / c → 0` in probability. -/
theorem tendstoInMeasure_curve_deviance_of_converge
    {A B C t₁ t₂ : ℝ} (hc : 0 < A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2)
    {S₁ S₂ B₁₁ B₁₂ B₂₂ C₁₁ C₁₂ C₂₂ D : ℕ → Ω → ℝ}
    (hS₁m : ∀ n, AEMeasurable (S₁ n) P) (hS₂m : ∀ n, AEMeasurable (S₂ n) P)
    (hB₁₁m : ∀ n, AEMeasurable (B₁₁ n) P) (hB₁₂m : ∀ n, AEMeasurable (B₁₂ n) P)
    (hB₂₂m : ∀ n, AEMeasurable (B₂₂ n) P)
    (hC₁₁m : ∀ n, AEMeasurable (C₁₁ n) P) (hC₁₂m : ∀ n, AEMeasurable (C₁₂ n) P)
    (hC₂₂m : ∀ n, AEMeasurable (C₂₂ n) P)
    (hDm : ∀ n, AEMeasurable (D n) P)
    (hS₁b : IsBoundedInProbability P S₁) (hS₂b : IsBoundedInProbability P S₂)
    (hB₁₁ : TendstoInMeasure P B₁₁ atTop (fun _ => -A))
    (hB₁₂ : TendstoInMeasure P B₁₂ atTop (fun _ => -B))
    (hB₂₂ : TendstoInMeasure P B₂₂ atTop (fun _ => -C))
    (hC₁₁ : TendstoInMeasure P C₁₁ atTop (fun _ => -A))
    (hC₁₂ : TendstoInMeasure P C₁₂ atTop (fun _ => -B))
    (hC₂₂ : TendstoInMeasure P C₂₂ atTop (fun _ => -C))
    (hcurve : ∀ᵐ ω ∂P, ∃ τ sl₁ sl₂ tn₁ tn₂ : ℕ → ℝ,
      Tendsto sl₁ atTop (𝓝 t₁) ∧ Tendsto sl₂ atTop (𝓝 t₂) ∧
      Tendsto tn₁ atTop (𝓝 t₁) ∧ Tendsto tn₂ atTop (𝓝 t₂) ∧
      ∀ᶠ n in atTop,
        tn₁ n * (S₁ n ω + τ n * (sl₁ n * B₁₁ n ω + sl₂ n * B₁₂ n ω)) +
          tn₂ n * (S₂ n ω + τ n * (sl₁ n * B₁₂ n ω + sl₂ n * B₂₂ n ω)) = 0 ∧
        D n ω = 2 * τ n * (sl₁ n * S₁ n ω + sl₂ n * S₂ n ω) +
          τ n ^ 2 * (sl₁ n ^ 2 * C₁₁ n ω + 2 * sl₁ n * sl₂ n * C₁₂ n ω + sl₂ n ^ 2 * C₂₂ n ω)) :
    TendstoInMeasure P (fun n ω =>
      D n ω - (t₁ * S₁ n ω + t₂ * S₂ n ω) ^ 2 / (A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2))
      atTop (fun _ => 0) := by
  set c := A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2
  set Q : ℕ → Ω → ℝ := fun n ω => (t₁ * S₁ n ω + t₂ * S₂ n ω) ^ 2 / c
  set denom : ℕ → Ω → ℝ := fun n ω => 1 + S₁ n ω ^ 2 + S₂ n ω ^ 2
  set R : ℕ → Ω → ℝ := fun n ω => |D n ω - Q n ω| / denom n ω
  have hRm : ∀ n, AEMeasurable (R n) P := fun n => by
    have := hDm n; have := hS₁m n; have := hS₂m n
    dsimp only [R, Q, denom]; fun_prop
  have hR0 : TendstoInMeasure P R atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro η hη
    obtain ⟨δ, hδ, hδ_err⟩ := exists_delta_curve_deviance_err hc (show 0 < η / 2 by positivity)
    set goodBC : ℕ → Ω → Prop := fun n ω =>
      |B₁₁ n ω - (-A)| < δ ∧ |B₁₂ n ω - (-B)| < δ ∧ |B₂₂ n ω - (-C)| < δ ∧
      |C₁₁ n ω - (-A)| < δ ∧ |C₁₂ n ω - (-B)| < δ ∧ |C₂₂ n ω - (-C)| < δ
    set i₁ : ℕ → Ω → ℝ := fun n ω => if |B₁₁ n ω - (-A)| < δ then 1 else 0
    set i₂ : ℕ → Ω → ℝ := fun n ω => if |B₁₂ n ω - (-B)| < δ then 1 else 0
    set i₃ : ℕ → Ω → ℝ := fun n ω => if |B₂₂ n ω - (-C)| < δ then 1 else 0
    set i₄ : ℕ → Ω → ℝ := fun n ω => if |C₁₁ n ω - (-A)| < δ then 1 else 0
    set i₅ : ℕ → Ω → ℝ := fun n ω => if |C₁₂ n ω - (-B)| < δ then 1 else 0
    set i₆ : ℕ → Ω → ℝ := fun n ω => if |C₂₂ n ω - (-C)| < δ then 1 else 0
    set ind : ℕ → Ω → ℝ := fun n ω => i₁ n ω * i₂ n ω * i₃ n ω * i₄ n ω * i₅ n ω * i₆ n ω
    have hind_one : ∀ n ω, goodBC n ω → ind n ω = 1 := fun n ω hg => by
      simp only [ind, i₁, i₂, i₃, i₄, i₅, i₆, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1,
        hg.2.2.2.2.1, hg.2.2.2.2.2, ↓reduceIte, mul_one]
    have hind_zero : ∀ n ω, ¬ goodBC n ω → ind n ω = 0 := fun n ω hng => by
      dsimp only [goodBC] at hng
      by_cases h1 : |B₁₁ n ω - (-A)| < δ
      · by_cases h2 : |B₁₂ n ω - (-B)| < δ
        · by_cases h3 : |B₂₂ n ω - (-C)| < δ
          · by_cases h4 : |C₁₁ n ω - (-A)| < δ
            · by_cases h5 : |C₁₂ n ω - (-B)| < δ
              · have h6 : ¬ |C₂₂ n ω - (-C)| < δ := fun h6 => hng ⟨h1, h2, h3, h4, h5, h6⟩
                simp only [ind, i₆, h6, ↓reduceIte, mul_zero]
              · simp only [ind, i₅, h5, ↓reduceIte, mul_zero, zero_mul]
            · simp only [ind, i₄, h4, ↓reduceIte, mul_zero, zero_mul]
          · simp only [ind, i₃, h3, ↓reduceIte, mul_zero, zero_mul]
        · simp only [ind, i₂, h2, ↓reduceIte, mul_zero, zero_mul]
      · simp only [ind, i₁, h1, ↓reduceIte, zero_mul]
    have hindm : ∀ n, AEMeasurable (ind n) P := fun n => by
      have mlt : ∀ {f : Ω → ℝ} {a : ℝ}, AEMeasurable f P →
          AEMeasurable (fun ω => if |f ω - a| < δ then (1 : ℝ) else 0) P := fun {f a} hf =>
        (Measurable.ite (measurableSet_lt measurable_id measurable_const)
          measurable_const measurable_const).comp_aemeasurable ((hf.sub_const a).abs)
      exact (((((mlt (hB₁₁m n)).mul (mlt (hB₁₂m n))).mul (mlt (hB₂₂m n))).mul
        (mlt (hC₁₁m n))).mul (mlt (hC₁₂m n))).mul (mlt (hC₂₂m n))
    set W : ℕ → Ω → ℝ := fun n ω => max (R n ω * ind n ω - η / 2) 0
    have hWm : ∀ n, AEStronglyMeasurable (W n) P := fun n =>
      (((hRm n).mul (hindm n)).sub_const (η / 2)).max aemeasurable_const |>.aestronglyMeasurable
    have hW_ae : ∀ᵐ ω ∂P, Tendsto (fun n => W n ω) atTop (𝓝 0) := by
      filter_upwards [hcurve] with ω ⟨τ, sl₁, sl₂, tn₁, tn₂, hsl₁, hsl₂, htn₁, htn₂, hev⟩
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev,
        hsl₁.eventually (Metric.ball_mem_nhds t₁ hδ),
        hsl₂.eventually (Metric.ball_mem_nhds t₂ hδ),
        htn₁.eventually (Metric.ball_mem_nhds t₁ hδ),
        htn₂.eventually (Metric.ball_mem_nhds t₂ hδ)]
        with n ⟨hrootn, hDn⟩ hs1 hs2 ht1 ht2
      dsimp only [W]
      by_cases hg : goodBC n ω
      · rw [hind_one n ω hg, mul_one]
        have habs_le := hδ_err (B₁₁ n ω) (B₁₂ n ω) (B₂₂ n ω) (C₁₁ n ω) (C₁₂ n ω) (C₂₂ n ω)
          (sl₁ n) (sl₂ n) (tn₁ n) (tn₂ n) (S₁ n ω) (S₂ n ω) (τ n) (D n ω)
          hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2
          (by simpa [Metric.mem_ball, Real.dist_eq] using hs1)
          (by simpa [Metric.mem_ball, Real.dist_eq] using hs2)
          (by simpa [Metric.mem_ball, Real.dist_eq] using ht1)
          (by simpa [Metric.mem_ball, Real.dist_eq] using ht2)
          hrootn hDn
        have hden_pos : 0 < denom n ω := by dsimp only [denom]; positivity
        have hR_le : R n ω ≤ η / 2 := by
          dsimp only [R, Q, denom]; rw [div_le_iff₀ hden_pos]; exact habs_le
        exact (max_eq_right (by linarith)).symm
      · rw [hind_zero n ω hg, mul_zero, zero_sub]
        exact (max_eq_right (by linarith)).symm
    have hW0 := (tendstoInMeasure_iff_norm.1 (tendstoInMeasure_of_tendsto_ae hWm hW_ae))
      (η / 2) (by positivity)
    rw [tendstoInMeasure_iff_norm] at hB₁₁ hB₁₂ hB₂₂ hC₁₁ hC₁₂ hC₂₂
    have hsum : Tendsto (fun n =>
        P {ω | η / 2 ≤ ‖W n ω - 0‖} +
        (P {ω | δ ≤ ‖B₁₁ n ω - (-A)‖} + P {ω | δ ≤ ‖B₁₂ n ω - (-B)‖} + P {ω | δ ≤ ‖B₂₂ n ω - (-C)‖}) +
        (P {ω | δ ≤ ‖C₁₁ n ω - (-A)‖} + P {ω | δ ≤ ‖C₁₂ n ω - (-B)‖} + P {ω | δ ≤ ‖C₂₂ n ω - (-C)‖}))
        atTop (𝓝 0) := by
      simpa using (hW0.add (((hB₁₁ δ hδ).add (hB₁₂ δ hδ)).add (hB₂₂ δ hδ))).add
        (((hC₁₁ δ hδ).add (hC₁₂ δ hδ)).add (hC₂₂ δ hδ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
    have hsub : {ω | η ≤ ‖R n ω - 0‖} ⊆
        {ω | η / 2 ≤ ‖W n ω - 0‖} ∪
        (({ω | δ ≤ ‖B₁₁ n ω - (-A)‖} ∪ {ω | δ ≤ ‖B₁₂ n ω - (-B)‖}) ∪ {ω | δ ≤ ‖B₂₂ n ω - (-C)‖}) ∪
        (({ω | δ ≤ ‖C₁₁ n ω - (-A)‖} ∪ {ω | δ ≤ ‖C₁₂ n ω - (-B)‖}) ∪ {ω | δ ≤ ‖C₂₂ n ω - (-C)‖}) := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs, sub_zero] at hω hnot
      obtain ⟨⟨hWlt, ⟨⟨h1, h2⟩, h3⟩⟩, ⟨⟨h4, h5⟩, h6⟩⟩ := hnot
      have hg : goodBC n ω := ⟨h1, h2, h3, h4, h5, h6⟩
      have hRnn : 0 ≤ R n ω := by dsimp only [R, denom]; positivity
      rw [abs_of_nonneg hRnn] at hω
      have hWval : W n ω = R n ω - η / 2 := by
        dsimp only [W]; rw [hind_one n ω hg, mul_one]; exact max_eq_left (by linarith)
      rw [hWval, abs_of_nonneg (by linarith)] at hWlt
      linarith
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
    · refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
      exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    · exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  have hden_b : IsBoundedInProbability P denom := by
    intro ε hε
    obtain ⟨M₁, hM₁⟩ := (isBoundedInProbability_mul hS₁b hS₁b) (ε / 2) (ENNReal.half_pos hε.ne')
    obtain ⟨M₂, hM₂⟩ := (isBoundedInProbability_mul hS₂b hS₂b) (ε / 2) (ENNReal.half_pos hε.ne')
    refine ⟨1 + max M₁ 0 + max M₂ 0, ?_⟩
    filter_upwards [hM₁, hM₂] with n h1 h2
    refine (measure_mono (t := {ω | M₁ < |S₁ n ω * S₁ n ω|} ∪ {ω | M₂ < |S₂ n ω * S₂ n ω|}) ?_).trans
      ((measure_union_le _ _).trans ((add_le_add h1 h2).trans (ENNReal.add_halves ε).le))
    intro ω hω
    simp only [mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hnot; push Not at hnot
    have hd0 : 0 ≤ denom n ω := by dsimp only [denom]; positivity
    rw [abs_of_nonneg hd0] at hω
    have hs1 : S₁ n ω ^ 2 ≤ max M₁ 0 := by
      have := hnot.1; rw [← sq, abs_of_nonneg (sq_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    have hs2 : S₂ n ω ^ 2 ≤ max M₂ 0 := by
      have := hnot.2; rw [← sq, abs_of_nonneg (sq_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    dsimp only [denom] at hω; linarith
  have hprod0 := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hden_b hR0
  rw [tendstoInMeasure_iff_norm] at hprod0 ⊢
  intro ε hε
  refine (hprod0 ε hε).congr fun n => measure_congr (ae_of_all _ fun ω => ?_)
  have hd_pos : 0 < denom n ω := by dsimp only [denom]; positivity
  have heq : |(|D n ω - Q n ω| / denom n ω) * denom n ω| = |D n ω - Q n ω| := by
    rw [div_mul_cancel₀ _ hd_pos.ne', abs_abs]
  simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, R, Q, c] at heq ⊢
  rw [heq]

end WilksEngine

/-! ### One-sided negative definiteness of weighted segment Hessians -/

section WeightedQuad

/-- From `0 ≤ 2 (T₁ S₁ + T₂ S₂) + Tᵀ C T` and `Tᵀ C T ≤ -(lam/2) (T₁² + T₂²)`, deduce
`|T₁| + |T₂| ≤ (8 / lam) (|S₁| + |S₂|)`. Works for ANY maximizer (full or restricted)! -/
lemma abs_add_abs_le_of_nonneg_quad {lam S₁ S₂ C₁₁ C₁₂ C₂₂ T₁ T₂ : ℝ} (hlam : 0 < lam)
    (hq : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * C₁₁ + 2 * t₁ * t₂ * C₁₂ + t₂ ^ 2 * C₂₂ ≤
      -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2))
    (hD : 0 ≤ 2 * (T₁ * S₁ + T₂ * S₂) +
      (T₁ ^ 2 * C₁₁ + 2 * T₁ * T₂ * C₁₂ + T₂ ^ 2 * C₂₂)) :
    |T₁| + |T₂| ≤ 8 / lam * (|S₁| + |S₂|) := by
  have hqT := hq T₁ T₂
  have hquad_le : (lam / 2) * (T₁ ^ 2 + T₂ ^ 2) ≤ 2 * (T₁ * S₁ + T₂ * S₂) := by linarith
  have hlin_le : T₁ * S₁ + T₂ * S₂ ≤ (|T₁| + |T₂|) * (|S₁| + |S₂|) := by
    have h1 : T₁ * S₁ ≤ |T₁| * |S₁| := by rw [← abs_mul]; exact le_abs_self _
    have h2 : T₂ * S₂ ≤ |T₂| * |S₂| := by rw [← abs_mul]; exact le_abs_self _
    have h3 : 0 ≤ |T₁| * |S₂| := by positivity
    have h4 : 0 ≤ |T₂| * |S₁| := by positivity
    nlinarith
  have hsq_le : (|T₁| + |T₂|) ^ 2 ≤ 2 * (T₁ ^ 2 + T₂ ^ 2) := by
    nlinarith [sq_nonneg (|T₁| - |T₂|), sq_abs T₁, sq_abs T₂]
  have hmain : (lam / 4) * (|T₁| + |T₂|) ^ 2 ≤ 2 * (|T₁| + |T₂|) * (|S₁| + |S₂|) := by
    nlinarith
  by_cases h0 : |T₁| + |T₂| = 0
  · rw [h0]; positivity
  · have hpos : 0 < |T₁| + |T₂| := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have h1 : (lam / 4) * (|T₁| + |T₂|) ≤ 2 * (|S₁| + |S₂|) := by
      nlinarith
    have h2 : |T₁| + |T₂| ≤ 8 / lam * (|S₁| + |S₂|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
      linarith
    exact h2

/-- Pointwise one-sided bound on the weighted segment Hessian quadratic form, `-1/2 < ξ₀ < 0`. -/
lemma segHessW_quad_le_neg {ξ₀ σ₀ C₁ : ℝ} (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
    (hC : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdQuadCoef θ ≤ C₁) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀)
    {x : ℝ} (hx : 0 ≤ x) (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * segHessW gpdHessXiXi ξ₀ σ₀ θ x + 2 * t₁ * t₂ * segHessW gpdHessXiSigma ξ₀ σ₀ θ x +
        t₂ ^ 2 * segHessW gpdHessSigmaSigma ξ₀ σ₀ θ x ≤
      C₁ * (t₁ ^ 2 + t₂ ^ 2) := by
  have hi : ∀ (H : ℝ → ℝ → ℝ → ℝ),
      (∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
        ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
      IntervalIntegrable (fun s => 2 * (1 - s) * H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x)
        volume 0 1 := by
    intro H hH
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    intro s hs
    obtain ⟨_, hp1, hp2⟩ := seg_params hξ₀ hξ₀' hσ₀ hθ hs
    have hcontH : ContinuousAt (fun r => H (ξ₀ + r * (θ.1 - ξ₀)) (σ₀ + r * (θ.2 - σ₀)) x) s :=
      (hH _ hp1.ne hp2 (seg_support_pos h0 h1 hs)).comp
        (f := fun r => (ξ₀ + r * (θ.1 - ξ₀), σ₀ + r * (θ.2 - σ₀), x)) (by fun_prop)
    exact ((continuous_const.mul (continuous_const.sub continuous_id)).continuousAt.mul
      hcontH).continuousWithinAt
  have iXX := hi gpdHessXiXi (fun _ h1 h2 h3 => continuousAt_gpdHessXiXi₃ h1 h2 h3)
  have iXS := hi gpdHessXiSigma (fun _ _ h2 h3 => continuousAt_gpdHessXiSigma₃ h2 h3)
  have iSS := hi gpdHessSigmaSigma (fun _ _ h2 h3 => continuousAt_gpdHessSigmaSigma₃ h2 h3)
  unfold segHessW
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (iXX.const_mul _) (iXS.const_mul _),
    ← intervalIntegral.integral_add ((iXX.const_mul _).add (iXS.const_mul _)) (iSS.const_mul _)]
  have hle := intervalIntegral.integral_mono_on zero_le_one
    (((iXX.const_mul _).add (iXS.const_mul _)).add (iSS.const_mul _))
    ((by fun_prop : Continuous fun s : ℝ => 2 * (1 - s) * (C₁ * (t₁ ^ 2 + t₂ ^ 2))).intervalIntegrable 0 1)
    fun s hs => by
      obtain ⟨hp0, hp1, hp2⟩ := seg_params hξ₀ hξ₀' hσ₀ hθ hs
      have hb := gpdHess_quad_le_coef (by linarith) hp1 hp2 hx (seg_support_pos h0 h1 hs) t₁ t₂
      have hc := hC _ (segment_mem_gpdNbhdNeg hξ₀' hσ₀ hθ hs)
      have hq : t₁ ^ 2 * gpdHessXiXi (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x +
          2 * t₁ * t₂ * gpdHessXiSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x +
          t₂ ^ 2 * gpdHessSigmaSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x ≤
          C₁ * (t₁ ^ 2 + t₂ ^ 2) :=
        hb.trans (mul_le_mul_of_nonneg_right hc (by positivity))
      have hw : 0 ≤ 2 * (1 - s) := by linarith [hs.2]
      calc t₁ ^ 2 * (2 * (1 - s) * gpdHessXiXi (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) +
            2 * t₁ * t₂ * (2 * (1 - s) * gpdHessXiSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) +
            t₂ ^ 2 * (2 * (1 - s) * gpdHessSigmaSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x)
          = 2 * (1 - s) * (t₁ ^ 2 * gpdHessXiXi (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x +
              2 * t₁ * t₂ * gpdHessXiSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x +
              t₂ ^ 2 * gpdHessSigmaSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) := by ring
        _ ≤ 2 * (1 - s) * (C₁ * (t₁ ^ 2 + t₂ ^ 2)) := mul_le_mul_of_nonneg_left hq hw
  rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul] at hle
  exact hle

/-- Uniform continuity of `segHessW` away from the endpoint for `-1/2 < ξ₀ < 0`. -/
lemma exists_delta_segHessW_good_neg {ξ₀ σ₀ : ℝ} (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
    {H : ℝ → ℝ → ℝ → ℝ} (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ, gpdDist ξ₀ σ₀ θ ≤ δ → ∀ y, 0 ≤ y → c ≤ σ₀ + ξ₀ * y →
      |segHessW H ξ₀ σ₀ θ y - H ξ₀ σ₀ y| ≤ ε := by
  set e₀ := -σ₀ / ξ₀
  have he0 : 0 < e₀ := div_pos_of_neg_of_neg (by linarith) hξ₀'
  have hξp : 0 < -ξ₀ := by linarith
  set r₀ := min (min (-ξ₀ / 8) (σ₀ / 8)) (c / (4 * (1 + e₀)))
  have hr₀ : 0 < r₀ := by positivity
  set Kp : Set (ℝ × ℝ) := Icc (ξ₀ - r₀) (ξ₀ + r₀) ×ˢ Icc (σ₀ - r₀) (σ₀ + r₀)
  set Kx : Set ℝ := Icc 0 ((σ₀ - c) / (-ξ₀))
  have hKc_set : IsCompact (Kp ×ˢ Kx) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => H q.1.1 q.1.2 q.2) (Kp ×ˢ Kx) := by
    rintro ⟨⟨ξ, σ⟩, y⟩ ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨hy0, hy1⟩⟩
    have hr1 : r₀ ≤ -ξ₀ / 8 := (min_le_left _ _).trans (min_le_left _ _)
    have hr2 : r₀ ≤ σ₀ / 8 := (min_le_left _ _).trans (min_le_right _ _)
    have hr3 : r₀ ≤ c / (4 * (1 + e₀)) := min_le_right _ _
    have hy_le : y ≤ e₀ := by
      have hle : (σ₀ - c) / (-ξ₀) ≤ σ₀ / (-ξ₀) :=
        div_le_div_of_nonneg_right (by linarith) hξp.le
      have heq : σ₀ / (-ξ₀) = e₀ := by simp only [e₀, div_neg, neg_div]
      exact hy1.trans (heq ▸ hle)
    have hcy : c ≤ σ₀ + ξ₀ * y := by
      have := (le_div_iff₀ (show 0 < -ξ₀ by linarith)).1 hy1; linarith
    have hu : 0 < σ + ξ * y := by
      have hd1 : |ξ - ξ₀| ≤ r₀ := abs_le.2 ⟨by linarith, by linarith⟩
      have hd2 : |σ - σ₀| ≤ r₀ := abs_le.2 ⟨by linarith, by linarith⟩
      have hstep : r₀ * (1 + e₀) ≤ c / 4 := by
        have := (le_div_iff₀ (show 0 < 4 * (1 + e₀) by positivity)).1 hr3; linarith
      have hdiff : |(σ + ξ * y) - (σ₀ + ξ₀ * y)| ≤ r₀ * (1 + e₀) := by
        calc |(σ + ξ * y) - (σ₀ + ξ₀ * y)|
            = |(σ - σ₀) + (ξ - ξ₀) * y| := by ring_nf
          _ ≤ |σ - σ₀| + |ξ - ξ₀| * |y| := (abs_add_le _ _).trans (by rw [abs_mul])
          _ ≤ r₀ + r₀ * e₀ := add_le_add hd2 (mul_le_mul hd1 (by rw [abs_of_nonneg hy0]; exact hy_le)
              (abs_nonneg _) hr₀.le)
          _ = r₀ * (1 + e₀) := by ring
      linarith [(abs_le.1 hdiff).1]
    exact (ContinuousAt.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
      (g := fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) (x := ((ξ, σ), y))
      (hH (ξ, σ, y) (by linarith) (by linarith) hu) (by fun_prop)).continuousWithinAt
  obtain ⟨η, hη, hη_bd⟩ := Metric.uniformContinuousOn_iff.1
    (hKc_set.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min r₀ (η / 2), lt_min hr₀ (by positivity), fun θ hθd y hy0 hcy => ?_⟩
  have hy_mem : y ∈ Kx := ⟨hy0, (le_div_iff₀ (show 0 < -ξ₀ by linarith)).2 (by linarith)⟩
  have hθ0_mem : ((ξ₀, σ₀), y) ∈ Kp ×ˢ Kx :=
    ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, hy_mem⟩
  refine abs_segHessW_sub_le_of_forall hHm hε.le fun s hs => ?_
  have hd_r0 : gpdDist ξ₀ σ₀ θ ≤ r₀ := hθd.trans (min_le_left _ _)
  have hd_eta : gpdDist ξ₀ σ₀ θ ≤ η / 2 := hθd.trans (min_le_right _ _)
  have hθs_mem : ((ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)), y) ∈ Kp ×ˢ Kx := by
    have ha : |s * (θ.1 - ξ₀)| ≤ r₀ := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_r0)
    have hb' : |s * (θ.2 - σ₀)| ≤ r₀ := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_r0)
    rw [abs_le] at ha hb'
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, hy_mem⟩
  have hdist : dist ((ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)), y) ((ξ₀, σ₀), y) < η := by
    simp only [Prod.dist_eq, dist_self, Real.dist_eq, add_sub_cancel_left]
    have ha : |s * (θ.1 - ξ₀)| ≤ η / 2 := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_eta)
    have hb' : |s * (θ.2 - σ₀)| ≤ η / 2 := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_eta)
    exact max_lt (max_lt (by linarith) (by linarith)) hη
  exact (hη_bd _ hθs_mem _ hθ0_mem hdist).le

/-- Deterministic eventual negative definiteness of the averaged weighted segment Hessian for
`-1/2 < ξ₀ < 0`. -/
lemma eventually_quad_avg_segHessW_le_neg {ξ₀ σ₀ lam m₁₁ m₁₂ m₂₂ : ℝ}
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀) (hlam : 0 < lam)
    (hm : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * m₁₁ + 2 * t₁ * t₂ * m₁₂ + t₂ ^ 2 * m₂₂ ≤
      -lam * (t₁ ^ 2 + t₂ ^ 2))
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i ∧ 0 < σ₀ + ξ₀ * x i)
    {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (ξ₀, σ₀)))
    (hadm : ∀ᶠ n in atTop, ∀ i < n, 0 < (θs n).2 + (θs n).1 * x i)
    (h₁₁ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i))
      atTop (𝓝 m₁₁))
    (h₁₂ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i))
      atTop (𝓝 m₁₂))
    (h₂₂ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdHessSigmaSigma ξ₀ σ₀ (x i)) atTop (𝓝 m₂₂))
    {d : ℕ → ℝ} (hD : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i)) atTop (𝓝 (d k)))
    (hd : Tendsto d atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiXi ξ₀ σ₀ (θs n) (x i)) +
        2 * t₁ * t₂ *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiSigma ξ₀ σ₀ (θs n) (x i)) +
        t₂ ^ 2 *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma ξ₀ σ₀ (θs n) (x i)) ≤
      -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2) := by
  obtain ⟨Kc, C₁, hKc, hC₁, hb⟩ := exists_gpdCoef_bound hξ₀ hξ₀' hσ₀
  have hK : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdHessCoef θ ≤ Kc := fun θ hθ => (hb θ hθ).1
  have hC : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdQuadCoef θ ≤ C₁ := fun θ hθ => (hb θ hθ).2
  set A := C₁ + 8 * Kc + 1
  have hA0 : 0 < A := by positivity
  set ε := lam / 16
  have hε0 : 0 < ε := by positivity
  obtain ⟨k, hk⟩ : ∃ k, A * d k < lam / 16 := by
    have h := hd.const_mul A; rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨δ₁, hδ₁, g₁⟩ := exists_delta_segHessW_good_neg hξ₀' hσ₀ measurable_gpdHessXiXi₃
    (fun _ h1 h2 h3 => continuousAt_gpdHessXiXi₃ h1 h2 h3) hc hε0
  obtain ⟨δ₂, hδ₂, g₂⟩ := exists_delta_segHessW_good_neg hξ₀' hσ₀ measurable_gpdHessXiSigma₃
    (fun _ _ h2 h3 => continuousAt_gpdHessXiSigma₃ h2 h3) hc hε0
  obtain ⟨δ₃, hδ₃, g₃⟩ := exists_delta_segHessW_good_neg hξ₀' hσ₀ measurable_gpdHessSigmaSigma₃
    (fun _ _ h2 h3 => continuousAt_gpdHessSigmaSigma₃ h2 h3) hc hε0
  set δ := min δ₁ (min δ₂ δ₃)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hball : ∀ {f : ℕ → ℝ} {m : ℝ}, Tendsto f atTop (𝓝 m) → ∀ᶠ n in atTop, |f n - m| ≤ ε :=
    fun {f m} h => (h.eventually (Metric.closedBall_mem_nhds m hε0)).mono fun n hn => by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hn
  filter_upwards [tendsto_gpdDist hθ hδ, hθ.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀),
    ((hD k).const_mul A).eventually (gt_mem_nhds hk), hball h₁₁, hball h₁₂, hball h₂₂,
    eventually_gt_atTop 0, hadm] with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 t₁ t₂
  set T := t₁ ^ 2 + t₂ ^ 2
  have hT0 : 0 ≤ T := by positivity
  set tail : ℕ → ℝ := fun i => gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i)
  set q₀ : ℕ → ℝ := fun i => t₁ ^ 2 * gpdHessXiXi ξ₀ σ₀ (x i) +
    2 * t₁ * t₂ * gpdHessXiSigma ξ₀ σ₀ (x i) + t₂ ^ 2 * gpdHessSigmaSigma ξ₀ σ₀ (x i)
  have hi : ∀ i < n, t₁ ^ 2 * segHessW gpdHessXiXi ξ₀ σ₀ (θs n) (x i) +
      2 * t₁ * t₂ * segHessW gpdHessXiSigma ξ₀ σ₀ (θs n) (x i) +
      t₂ ^ 2 * segHessW gpdHessSigmaSigma ξ₀ σ₀ (θs n) (x i) ≤
      q₀ i + (2 * ε + (C₁ + 8 * Kc) * tail i) * T := fun i hi => by
    by_cases hcx : 1 / ((k : ℝ) + 1) ≤ σ₀ + ξ₀ * x i
    · rw [show tail i = 0 from gpdDomTail_of_le hcx, mul_zero, add_zero]
      have hq := quad_le_of_abs_le
        (g₁ _ (hn1.trans (min_le_left _ _)) _ (hx i).1 hcx)
        (g₂ _ (hn1.trans ((min_le_right _ _).trans (min_le_left _ _))) _ (hx i).1 hcx)
        (g₃ _ (hn1.trans ((min_le_right _ _).trans (min_le_right _ _))) _ (hx i).1 hcx) t₁ t₂
      dsimp only [q₀, T]; nlinarith
    · rw [show tail i = gpdDom ξ₀ σ₀ (x i) from gpdDomTail_of_lt (not_le.1 hcx)]
      have hDom := one_le_gpdDom hξ₀' hσ₀ (hx i).1 (hx i).2
      have hq := segHessW_quad_le_neg hξ₀ hξ₀' hσ₀ hC hn2 (hx i).1 (hx i).2 (hn8 i hi) t₁ t₂
      have b₁ := abs_gpdHess_self_le hξ₀' hσ₀ (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).1)
        hK (hx i).1 (hx i).2
      have b₂ := abs_gpdHess_self_le hξ₀' hσ₀ (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.1)
        hK (hx i).1 (hx i).2
      have b₃ := abs_gpdHess_self_le hξ₀' hσ₀ (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.2)
        hK (hx i).1 (hx i).2
      rw [← abs_neg] at b₁ b₂ b₃
      have hneg := quad_le_of_abs_le b₁ b₂ b₃ t₁ t₂
      have e1 : C₁ * T ≤ C₁ * gpdDom ξ₀ σ₀ (x i) * T := by
        have := mul_le_mul_of_nonneg_left hDom hC₁; nlinarith
      have e2 : 0 ≤ 2 * ε * T := by positivity
      dsimp only [q₀, T] at *; nlinarith
  rw [quad_avg]
  refine (avg_le_avg hi).trans ?_
  rw [avg_add_const_mul hn7]
  dsimp only [q₀]
  rw [← quad_avg]
  have htail0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i :=
    avg_nonneg fun i _ => gpdDomTail_nonneg hξ₀' hσ₀ (hx i).1 (hx i).2
  have hdev := quad_le_of_abs_le hn4 hn5 hn6 t₁ t₂
  have hmt := hm t₁ t₂
  have htl : (C₁ + 8 * Kc) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) ≤ lam / 16 := by
    have : (C₁ + 8 * Kc) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) ≤
        A * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) :=
      mul_le_mul_of_nonneg_right (by linarith) htail0
    linarith
  have e : t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i)) +
      2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i)) +
      t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessSigmaSigma ξ₀ σ₀ (x i)) =
      (t₁ ^ 2 * m₁₁ + 2 * t₁ * t₂ * m₁₂ + t₂ ^ 2 * m₂₂) +
      (t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i) - m₁₁) +
        2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i) - m₁₂) +
        t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessSigmaSigma ξ₀ σ₀ (x i) - m₂₂)) := by
    ring
  rw [e]
  have : (2 * ε + (C₁ + 8 * Kc) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i)) * T ≤
      (2 * ε + lam / 16) * T := mul_le_mul_of_nonneg_right (by linarith) hT0
  have hε_eq : ε = lam / 16 := rfl
  rw [hε_eq] at this hdev
  nlinarith

/-- Pointwise one-sided bound on the weighted segment Hessian quadratic form at `ξ₀ = 0`. -/
lemma segHessW_quad_le_zero {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀)
    {x : ℝ} (hx : 0 ≤ x) (h1 : 0 < θ.2 + θ.1 * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * segHessW gpdHessXiXiAll 0 σ₀ θ x +
        2 * t₁ * t₂ * segHessW gpdHessXiSigma 0 σ₀ θ x +
        t₂ ^ 2 * segHessW gpdHessSigmaSigma 0 σ₀ θ x ≤
      2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * (t₁ ^ 2 + t₂ ^ 2) := by
  have h0 : 0 < σ₀ + 0 * x := by simpa using hσ₀
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, 0 < σ₀ + s * (θ.2 - σ₀) ∧
      0 < (σ₀ + s * (θ.2 - σ₀)) + (0 + s * (θ.1 - 0)) * x := fun s hs =>
    ⟨by linarith [(segment_mem_gpdNbhdZero hσ₀ hθ hs).2.1], seg_support_pos (ξ₀ := 0) h0 h1 hs⟩
  have hi : ∀ (H : ℝ → ℝ → ℝ → ℝ),
      (∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
        ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
      IntervalIntegrable (fun s => 2 * (1 - s) * H (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x)
        volume 0 1 := by
    intro H hH
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    intro s hs
    have hcontH : ContinuousAt (fun r => H (0 + r * (θ.1 - 0)) (σ₀ + r * (θ.2 - σ₀)) x) s :=
      (hH _ (hseg s hs).1 (hseg s hs).2).comp
        (f := fun r => (0 + r * (θ.1 - 0), σ₀ + r * (θ.2 - σ₀), x)) (by fun_prop)
    exact ((continuous_const.mul (continuous_const.sub continuous_id)).continuousAt.mul
      hcontH).continuousWithinAt
  have iXX := hi gpdHessXiXiAll (fun _ h1 h2 => continuousAt_gpdHessXiXiAll₃ h1 h2)
  have iXS := hi gpdHessXiSigma (fun _ h1 h2 => continuousAt_gpdHessXiSigma₃ h1 h2)
  have iSS := hi gpdHessSigmaSigma (fun _ h1 h2 => continuousAt_gpdHessSigmaSigma₃ h1 h2)
  unfold segHessW
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (iXX.const_mul _) (iXS.const_mul _),
    ← intervalIntegral.integral_add ((iXX.const_mul _).add (iXS.const_mul _)) (iSS.const_mul _)]
  have hle := intervalIntegral.integral_mono_on zero_le_one
    (((iXX.const_mul _).add (iXS.const_mul _)).add (iSS.const_mul _))
    ((by fun_prop : Continuous fun s : ℝ =>
      2 * (1 - s) * (2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * (t₁ ^ 2 + t₂ ^ 2))).intervalIntegrable 0 1)
    fun s hs => by
      have hq := gpdHessAll_quad_le_zero hσ₀ (segment_mem_gpdNbhdZero hσ₀ hθ hs) hx (hseg s hs).2 t₁ t₂
      have hw : 0 ≤ 2 * (1 - s) := by linarith [hs.2]
      calc t₁ ^ 2 * (2 * (1 - s) * gpdHessXiXiAll (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x) +
            2 * t₁ * t₂ * (2 * (1 - s) * gpdHessXiSigma (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x) +
            t₂ ^ 2 * (2 * (1 - s) * gpdHessSigmaSigma (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x)
          = 2 * (1 - s) * (t₁ ^ 2 * gpdHessXiXiAll (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x +
              2 * t₁ * t₂ * gpdHessXiSigma (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x +
              t₂ ^ 2 * gpdHessSigmaSigma (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x) := by ring
        _ ≤ 2 * (1 - s) * (2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * (t₁ ^ 2 + t₂ ^ 2)) :=
            mul_le_mul_of_nonneg_left hq hw
  rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul] at hle
  exact hle

/-- Uniform continuity of `segHessW` on `[0, M]` at `ξ₀ = 0`. -/
lemma exists_delta_segHessW_good_zero {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ, gpdDist 0 σ₀ θ ≤ δ → ∀ y, 0 ≤ y → y ≤ M →
      |segHessW H 0 σ₀ θ y - H 0 σ₀ y| ≤ ε := by
  set r₀ := min (min (1 / 4 : ℝ) (σ₀ / 8)) (σ₀ / (4 * (M + 1)))
  have hr₀ : 0 < r₀ := by positivity
  set Kp : Set (ℝ × ℝ) := Icc (-r₀) r₀ ×ˢ Icc (σ₀ - r₀) (σ₀ + r₀)
  set Kx : Set ℝ := Icc 0 M
  have hKc_set : IsCompact (Kp ×ˢ Kx) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => H q.1.1 q.1.2 q.2) (Kp ×ˢ Kx) := by
    rintro ⟨⟨ξ, σ⟩, y⟩ ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨hy0, hy1⟩⟩
    have hr2 : r₀ ≤ σ₀ / 8 := (min_le_left _ _).trans (min_le_right _ _)
    have hr3 : r₀ ≤ σ₀ / (4 * (M + 1)) := min_le_right _ _
    have hσ_pos : 0 < σ := by linarith
    have hu : 0 < σ + ξ * y := by
      have hstep : r₀ * (M + 1) ≤ σ₀ / 4 := by
        have := (le_div_iff₀ (show 0 < 4 * (M + 1) by positivity)).1 hr3; linarith
      have hξy : |ξ * y| ≤ r₀ * M := by
        rw [abs_mul, abs_of_nonneg hy0]
        exact mul_le_mul (abs_le.2 ⟨h1, h2⟩) hy1 hy0 hr₀.le
      linarith [(abs_le.1 hξy).1]
    exact (ContinuousAt.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
      (g := fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) (x := ((ξ, σ), y))
      (hH (ξ, σ, y) hσ_pos hu) (by fun_prop)).continuousWithinAt
  obtain ⟨η, hη, hη_bd⟩ := Metric.uniformContinuousOn_iff.1
    (hKc_set.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min r₀ (η / 2), lt_min hr₀ (by positivity), fun θ hθd y hy0 hyM => ?_⟩
  have hθ0_mem : ((0, σ₀), y) ∈ Kp ×ˢ Kx :=
    ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ⟨hy0, hyM⟩⟩
  refine abs_segHessW_sub_le_of_forall hHm hε.le fun s hs => ?_
  have hd_r0 : gpdDist 0 σ₀ θ ≤ r₀ := hθd.trans (min_le_left _ _)
  have hd_eta : gpdDist 0 σ₀ θ ≤ η / 2 := hθd.trans (min_le_right _ _)
  have hθs_mem : ((0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀)), y) ∈ Kp ×ˢ Kx := by
    have ha : |s * (θ.1 - 0)| ≤ r₀ := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_r0)
    have hb' : |s * (θ.2 - σ₀)| ≤ r₀ := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_r0)
    rw [abs_le] at ha hb'
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ⟨hy0, hyM⟩⟩
  have hdist : dist ((0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀)), y) ((0, σ₀), y) < η := by
    simp only [Prod.dist_eq, dist_self, Real.dist_eq, add_sub_cancel_left]
    have ha : |s * (θ.1 - 0)| ≤ η / 2 := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_right (abs_nonneg _)).trans hd_eta)
    have hb' : |s * (θ.2 - σ₀)| ≤ η / 2 := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans
        ((le_add_of_nonneg_left (abs_nonneg _)).trans hd_eta)
    exact max_lt (max_lt (by linarith) (by linarith)) hη
  exact (hη_bd _ hθs_mem _ hθ0_mem hdist).le

/-- Deterministic eventual negative definiteness of the averaged weighted segment Hessian at
`ξ₀ = 0`. -/
lemma eventually_quad_avg_segHessW_le_zero {σ₀ lam m₁₁ m₁₂ m₂₂ : ℝ} (hσ₀ : 0 < σ₀) (hlam : 0 < lam)
    (hm : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * m₁₁ + 2 * t₁ * t₂ * m₁₂ + t₂ ^ 2 * m₂₂ ≤
      -lam * (t₁ ^ 2 + t₂ ^ 2))
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (0, σ₀)))
    (hadm : ∀ᶠ n in atTop, ∀ i < n, 0 < (θs n).2 + (θs n).1 * x i)
    (h₁₁ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXiAll 0 σ₀ (x i))
      atTop (𝓝 m₁₁))
    (h₁₂ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma 0 σ₀ (x i))
      atTop (𝓝 m₁₂))
    (h₂₂ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessSigmaSigma 0 σ₀ (x i))
      atTop (𝓝 m₂₂))
    {d : ℕ → ℝ} (hD : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomZeroTail σ₀ (k : ℝ) (x i)) atTop (𝓝 (d k)))
    (hd : Tendsto d atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiXiAll 0 σ₀ (θs n) (x i)) +
        2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiSigma 0 σ₀ (θs n) (x i)) +
        t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma 0 σ₀ (θs n) (x i)) ≤
      -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2) := by
  set C := gpdZeroConst σ₀
  have hC : 0 < C := gpdZeroConst_pos hσ₀
  set A := 4 * C + 1
  have hA : 0 < A := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A * d k < lam / 8 := by
    have h := hd.const_mul A; rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  obtain ⟨δ₁, hδ₁, g₁⟩ := exists_delta_segHessW_good_zero hσ₀ measurable_gpdHessXiXiAll₃
    (fun _ h1 h2 => continuousAt_gpdHessXiXiAll₃ h1 h2) (Nat.cast_nonneg k) (show 0 < lam / 16 by positivity)
  obtain ⟨δ₂, hδ₂, g₂⟩ := exists_delta_segHessW_good_zero hσ₀ measurable_gpdHessXiSigma₃
    (fun _ h1 h2 => continuousAt_gpdHessXiSigma₃ h1 h2) (Nat.cast_nonneg k) (show 0 < lam / 16 by positivity)
  obtain ⟨δ₃, hδ₃, g₃⟩ := exists_delta_segHessW_good_zero hσ₀ measurable_gpdHessSigmaSigma₃
    (fun _ h1 h2 => continuousAt_gpdHessSigmaSigma₃ h1 h2) (Nat.cast_nonneg k) (show 0 < lam / 16 by positivity)
  set δ := min δ₁ (min δ₂ δ₃)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  filter_upwards [tendsto_gpdDist hθ hδ, hθ.eventually (gpdNbhdZero_mem_nhds hσ₀), hadm,
    ((hD k).const_mul A).eventually (gt_mem_nhds hk),
    h₁₁.eventually (Metric.ball_mem_nhds m₁₁ (show 0 < lam / 16 by positivity)),
    h₁₂.eventually (Metric.ball_mem_nhds m₁₂ (show 0 < lam / 16 by positivity)),
    h₂₂.eventually (Metric.ball_mem_nhds m₂₂ (show 0 < lam / 16 by positivity)),
    eventually_gt_atTop 0] with n hn1 hn2 hn_adm hn3 ha1 ha2 ha3 hn0 t₁ t₂
  have hρ1 : gpdDist 0 σ₀ (θs n) ≤ δ₁ := hn1.trans (min_le_left _ _)
  have hρ2 : gpdDist 0 σ₀ (θs n) ≤ δ₂ := hn1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ3 : gpdDist 0 σ₀ (θs n) ≤ δ₃ := hn1.trans ((min_le_right _ _).trans (min_le_right _ _))
  set tail : ℕ → ℝ := fun i => gpdDomZeroTail σ₀ (k : ℝ) (x i)
  have hpt : ∀ i ∈ Finset.range n,
      t₁ ^ 2 * segHessW gpdHessXiXiAll 0 σ₀ (θs n) (x i) +
          2 * t₁ * t₂ * segHessW gpdHessXiSigma 0 σ₀ (θs n) (x i) +
          t₂ ^ 2 * segHessW gpdHessSigmaSigma 0 σ₀ (θs n) (x i) ≤
        (t₁ ^ 2 * gpdHessXiXiAll 0 σ₀ (x i) + 2 * t₁ * t₂ * gpdHessXiSigma 0 σ₀ (x i) +
          t₂ ^ 2 * gpdHessSigmaSigma 0 σ₀ (x i)) +
        (2 * (lam / 16) + 4 * C * tail i) * (t₁ ^ 2 + t₂ ^ 2) := fun i hi => by
    have hi' : i < n := Finset.mem_range.1 hi
    by_cases hle : x i ≤ (k : ℝ)
    · rw [show tail i = 0 from gpdDomZeroTail_of_le hle, mul_zero, add_zero]
      have hq := quad_le_of_abs_le (g₁ _ hρ1 _ (hx i) hle) (g₂ _ hρ2 _ (hx i) hle)
        (g₃ _ hρ3 _ (hx i) hle) t₁ t₂
      nlinarith
    · rw [show tail i = gpdDomZero σ₀ (x i) from gpdDomZeroTail_of_lt (not_le.1 hle)]
      have hq := segHessW_quad_le_zero hσ₀ hn2 (hx i) (hn_adm i hi') t₁ t₂
      obtain ⟨b1, b2, b3⟩ := abs_gpdHessAll_le_of_ge_neg_half hσ₀ (mem_gpdNbhdZero_self hσ₀) (hx i) (by simp)
      rw [← abs_neg] at b1 b2 b3
      have hneg := quad_le_of_abs_le b1 b2 b3 t₁ t₂
      have he : 0 ≤ 2 * (lam / 16) * (t₁ ^ 2 + t₂ ^ 2) := by positivity
      nlinarith
  have havg_le : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      (t₁ ^ 2 * segHessW gpdHessXiXiAll 0 σ₀ (θs n) (x i) +
        2 * t₁ * t₂ * segHessW gpdHessXiSigma 0 σ₀ (θs n) (x i) +
        t₂ ^ 2 * segHessW gpdHessSigmaSigma 0 σ₀ (θs n) (x i)) ≤
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ((t₁ ^ 2 * gpdHessXiXiAll 0 σ₀ (x i) + 2 * t₁ * t₂ * gpdHessXiSigma 0 σ₀ (x i) +
          t₂ ^ 2 * gpdHessSigmaSigma 0 σ₀ (x i)) +
          (2 * (lam / 16) + 4 * C * tail i) * (t₁ ^ 2 + t₂ ^ 2)) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [← quad_avg, avg_add_const_mul hn0, ← quad_avg] at havg_le
  have hd1 : |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXiAll 0 σ₀ (x i) - m₁₁| ≤ lam / 16 :=
    (by simpa [Metric.mem_ball, Real.dist_eq] using ha1 : _ < _).le
  have hd2 : |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma 0 σ₀ (x i) - m₁₂| ≤ lam / 16 :=
    (by simpa [Metric.mem_ball, Real.dist_eq] using ha2 : _ < _).le
  have hd3 : |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessSigmaSigma 0 σ₀ (x i) - m₂₂| ≤ lam / 16 :=
    (by simpa [Metric.mem_ball, Real.dist_eq] using ha3 : _ < _).le
  have hqm := quad_le_of_abs_le hd1 hd2 hd3 t₁ t₂
  have hm_le := hm t₁ t₂
  have htail0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i :=
    avg_nonneg fun i _ => gpdDomZeroTail_nonneg hσ₀ (hx i)
  have htail_le : 4 * C * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) ≤
      A * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) :=
    mul_le_mul_of_nonneg_right (by linarith) htail0
  have ht2 : 0 ≤ t₁ ^ 2 + t₂ ^ 2 := by positivity
  have hqm' : t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXiAll 0 σ₀ (x i)) +
      2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma 0 σ₀ (x i)) +
      t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessSigmaSigma 0 σ₀ (x i)) ≤
      (t₁ ^ 2 * m₁₁ + 2 * t₁ * t₂ * m₁₂ + t₂ ^ 2 * m₂₂) +
        2 * (lam / 16) * (t₁ ^ 2 + t₂ ^ 2) := by
    linear_combination hqm
  have hmul_le : (2 * (lam / 16) + 4 * C * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i)) *
      (t₁ ^ 2 + t₂ ^ 2) ≤ (lam / 4) * (t₁ ^ 2 + t₂ ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) ht2
  have hlt2 : 0 ≤ lam * (t₁ ^ 2 + t₂ ^ 2) := mul_nonneg hlam.le ht2
  linarith

end WeightedQuad

/-! ### Score quadratic forms converging to `χ²₂` and `χ²₁` for all `ξ₀ > -1/2` -/

section ScoreWilksAll

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {ξ₀ σ₀ : ℝ}

/-- Normalized shape score, valid for all `ξ₀ ∈ ℝ` (including `ξ₀ = 0`). -/
noncomputable def gpdNormScoreXiAll (ξ₀ σ₀ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreXiAll ξ₀ σ₀ (x i)

lemma gpdNormScoreXiAll_of_ne {ξ₀ : ℝ} (hξ₀ : ξ₀ ≠ 0) (σ₀ : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    gpdNormScoreXiAll ξ₀ σ₀ x n = gpdNormScoreXi ξ₀ σ₀ x n := by
  simp only [gpdNormScoreXiAll, gpdNormScoreXi, gpdScoreXiAll_of_ne hξ₀]

lemma gpdNormScoreXiAll_zero (σ₀ : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    gpdNormScoreXiAll 0 σ₀ x n = (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, expScoreXi σ₀ (x i) := by
  simp only [gpdNormScoreXiAll, gpdScoreXiAll_zero]

/-- Squared score statistic `Sₙᵀ I(θ₀)⁻¹ Sₙ ⇒ χ²₂` for ALL regular shapes `ξ₀ > -1/2`
(including `ξ₀ = 0`). -/
theorem tendstoInDistribution_gpdInfoInvQuad_reg (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (chiSquared 2) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        gpdInfoInvQuad ξ₀ σ₀ (gpdNormScoreXiAll ξ₀ σ₀ (fun i => X i ω) n)
          (gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n)) atTop Z (fun _ => P) P' := by
  have h2 : 0 < 1 + 2 * ξ₀ := by linarith
  set w := √(1 + 2 * ξ₀)
  have hw2 : w ^ 2 = 1 + 2 * ξ₀ := Real.sq_sqrt h2.le
  have hQ : ∀ t : Fin 2 → ℝ, gpdInfoQuad ξ₀ σ₀ (t 0 * (1 + ξ₀) + t 1 * 0)
      (t 0 * -σ₀ + t 1 * (σ₀ * w)) = t ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ t := fun t => by
    have h1 : 1 + ξ₀ ≠ 0 := by linarith
    have hw0 : w ≠ 0 := (Real.sqrt_pos.2 h2).ne'
    simp only [gpdInfoQuad, Matrix.one_mulVec, dotProduct, Fin.sum_univ_two, ← hw2]
    field_simp [h1, hσ₀.ne', hw0]
    have hw2' : ξ₀ = (w ^ 2 - 1) / 2 := by linarith
    rw [hw2']; ring
  set E2 := EuclideanSpace ℝ (Fin 2)
  have hW : HasLaw (id : E2 → E2) (multivariateGaussian 0 1) (multivariateGaussian 0 1) := HasLaw.id
  have hsqL : HasLaw ((fun v : E2 => ‖v‖ ^ 2) ∘ id) (chiSquared 2) (multivariateGaussian (0 : E2) 1) := by
    have : HasLaw (id : E2 → E2) (stdGaussian E2) (multivariateGaussian (0 : E2) 1) := by
      rw [multivariateGaussian_zero_one]; exact HasLaw.id
    exact this.norm_sq_chiSquared
  rcases eq_or_ne ξ₀ 0 with rfl | hξ0
  · have hV := tendstoInDistribution_gpdScoreLin_zero hσ₀ hX hind (1 + 0) (-σ₀) 0 (σ₀ * w)
      Matrix.PosSemidef.one hQ hW
    have hfin := tendstoInDistribution_congr_limit (hV.continuous_comp (g := fun v : E2 => ‖v‖ ^ 2) (by fun_prop))
      hsqL hZ
    convert hfin using 2 with n
    funext ω
    have e0 : ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
        gpdScoreLinZero (1 + 0) (-σ₀) 0 (σ₀ * w) σ₀ (X i ω)) 0 =
        (1 + 0) * gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n +
          -σ₀ * gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n := by
      simp only [gpdScoreLinZero, gpdNormScoreXiAll_zero, gpdNormScoreSigma, gpdScoreSigma_zero,
        PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, Matrix.cons_val_zero,
        Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    have e1 : ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
        gpdScoreLinZero (1 + 0) (-σ₀) 0 (σ₀ * w) σ₀ (X i ω)) 1 =
        (σ₀ * w) * gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n := by
      simp only [gpdScoreLinZero, gpdNormScoreSigma, gpdScoreSigma_zero,
        PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_zero, zero_mul, zero_add, ← Finset.mul_sum]; ring
    simp only [Function.comp_apply]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, e0, e1, gpdInfoInvQuad]
    have hw1 : w ^ 2 = 1 := by simpa using hw2
    generalize gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n = S₁
    generalize gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n = S₂
    nlinarith [hw1]
  · have hV := tendstoInDistribution_gpdScoreLin hξ₀ hξ0 hσ₀ hX hind (1 + ξ₀) (-σ₀) 0 (σ₀ * w)
      Matrix.PosSemidef.one hQ hW
    have hfin := tendstoInDistribution_congr_limit (hV.continuous_comp (g := fun v : E2 => ‖v‖ ^ 2) (by fun_prop))
      hsqL hZ
    convert hfin using 2 with n
    funext ω
    have e0 : ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
        gpdScoreLin (1 + ξ₀) (-σ₀) 0 (σ₀ * w) ξ₀ σ₀ (X i ω)) 0 =
        (1 + ξ₀) * gpdNormScoreXiAll ξ₀ σ₀ (fun i => X i ω) n +
          -σ₀ * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n := by
      simp only [gpdScoreLin, gpdNormScoreXiAll_of_ne hξ0, gpdNormScoreXi, gpdNormScoreSigma,
        PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, Matrix.cons_val_zero,
        Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    have e1 : ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
        gpdScoreLin (1 + ξ₀) (-σ₀) 0 (σ₀ * w) ξ₀ σ₀ (X i ω)) 1 =
        (σ₀ * w) * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n := by
      simp only [gpdScoreLin, gpdNormScoreSigma,
        PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_zero, zero_mul, zero_add, ← Finset.mul_sum]; ring
    simp only [Function.comp_apply]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, e0, e1, gpdInfoInvQuad]
    have hξw : ξ₀ = (w ^ 2 - 1) / 2 := by linarith
    generalize gpdNormScoreXiAll ξ₀ σ₀ (fun i => X i ω) n = S₁
    generalize gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n = S₂
    rw [hξw]; ring

/-- Profile score statistic `Sₙᵀ I⁻¹ Sₙ - (t · Sₙ)² / (tᵀ I t) ⇒ χ²₁` for ALL regular shapes
`ξ₀ > -1/2` (including `ξ₀ = 0`). -/
theorem tendstoInDistribution_gpdInfoInvQuad_sub_reg (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) {t₁ t₂ : ℝ}
    (ht : t₁ ≠ 0 ∨ t₂ ≠ 0) {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        gpdInfoInvQuad ξ₀ σ₀ (gpdNormScoreXiAll ξ₀ σ₀ (fun i => X i ω) n)
            (gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) -
          (t₁ * gpdNormScoreXiAll ξ₀ σ₀ (fun i => X i ω) n +
            t₂ * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) ^ 2 / gpdInfoQuad ξ₀ σ₀ t₁ t₂)
      atTop Z (fun _ => P) P' := by
  obtain ⟨hd, hJ₁₁, hJ₁₂, hJ₂₂⟩ := gpdFisherInfo_det_adj hξ₀ hσ₀
  have hc := gpdInfoQuad_pos hξ₀ hσ₀ ht
  set A := 2 / ((1 + ξ₀) * (1 + 2 * ξ₀))
  set B := 1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀))
  set C := 1 / (σ₀ ^ 2 * (1 + 2 * ξ₀))
  have hd' : 0 < A * C - B ^ 2 := hd
  have hq : gpdInfoQuad ξ₀ σ₀ t₁ t₂ = A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2 := by
    unfold gpdInfoQuad; ring
  rw [hq] at hc
  set c := A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2
  set u := √((A * C - B ^ 2) * c)
  have hu2 : u ^ 2 = (A * C - B ^ 2) * c := Real.sq_sqrt (mul_pos hd' hc).le
  have hu0 : 0 < u := Real.sqrt_pos.2 (mul_pos hd' hc)
  set c₁ := (B * t₁ + C * t₂) / u
  set c₂ := -(A * t₁ + B * t₂) / u
  have hvar : gpdInfoQuad ξ₀ σ₀ c₁ c₂ = 1 := by
    have : gpdInfoQuad ξ₀ σ₀ c₁ c₂ =
        (A * (B * t₁ + C * t₂) ^ 2 - 2 * B * (B * t₁ + C * t₂) * (A * t₁ + B * t₂) +
          C * (A * t₁ + B * t₂) ^ 2) / u ^ 2 := by
      unfold gpdInfoQuad
      simp only [c₁, c₂, A, B, C]
      field_simp; ring
    rw [this, hu2, div_eq_one_iff_eq (mul_pos hd' hc).ne']
    dsimp only [c]; ring
  have hN : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (gpdInfoQuad ξ₀ σ₀ c₁ c₂).toNNReal)
      (gaussianReal 0 1) := by
    rw [hvar, Real.toNNReal_one]; exact HasLaw.id
  have hsqL : HasLaw ((fun x : ℝ => x ^ 2) ∘ id) (chiSquared 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, by rw [chiSquared_one_eq_map]; rfl⟩
  have halg : ∀ S₁ S₂ : ℝ,
      gpdInfoInvQuad ξ₀ σ₀ S₁ S₂ - (t₁ * S₁ + t₂ * S₂) ^ 2 / gpdInfoQuad ξ₀ σ₀ t₁ t₂ =
        (c₁ * S₁ + c₂ * S₂) ^ 2 := fun S₁ S₂ => by
    rw [gpdInfoInvQuad, hq]
    have e2 := quad_div_eq_of_div_eq (s₁ := S₁) (s₂ := S₂) hJ₁₁ hJ₁₂ hJ₂₂
    have e3 : (1 + ξ₀) * ((1 + ξ₀) * S₁ ^ 2 - 2 * σ₀ * S₁ * S₂ + 2 * σ₀ ^ 2 * S₂ ^ 2) =
        (C * S₁ ^ 2 - 2 * B * S₁ * S₂ + A * S₂ ^ 2) / (A * C - B ^ 2) := by
      rw [show (C * S₁ ^ 2 - 2 * B * S₁ * S₂ + A * S₂ ^ 2) / (A * C - B ^ 2) = _ from e2]; ring
    rw [e3, div_sub_div _ _ hd'.ne' hc.ne']
    have hnum : (C * S₁ ^ 2 - 2 * B * S₁ * S₂ + A * S₂ ^ 2) * c -
        (A * C - B ^ 2) * (t₁ * S₁ + t₂ * S₂) ^ 2 =
        ((B * t₁ + C * t₂) * S₁ - (A * t₁ + B * t₂) * S₂) ^ 2 := by
      dsimp only [c]; ring
    rw [hnum, ← hu2]
    dsimp only [c₁, c₂]
    field_simp [hu0.ne']; ring
  rcases eq_or_ne ξ₀ 0 with rfl | hξ0
  · have hclt := tendstoInDistribution_lin_score_zero hσ₀ hX hind c₁ c₂ hN
    have hfin := tendstoInDistribution_congr_limit (hclt.continuous_comp (g := fun x : ℝ => x ^ 2) (by fun_prop))
      hsqL hZ
    convert hfin using 2 with n
    funext ω
    simp only [Function.comp_apply]
    rw [halg]
    congr 1
    simp only [gpdNormScoreXiAll_zero, gpdNormScoreSigma, gpdScoreSigma_zero,
      Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  · have hclt := tendstoInDistribution_lin_score hξ₀ hξ0 hσ₀ hX hind c₁ c₂ hN
    have hfin := tendstoInDistribution_congr_limit (hclt.continuous_comp (g := fun x : ℝ => x ^ 2) (by fun_prop))
      hsqL hZ
    convert hfin using 2 with n
    funext ω
    simp only [Function.comp_apply]
    rw [halg]
    congr 1
    simp only [gpdNormScoreXiAll_of_ne hξ0, gpdNormScoreXi, gpdNormScoreSigma,
      Finset.sum_add_distrib, ← Finset.mul_sum]; ring

end ScoreWilksAll

/-! ### Curve differentiability across `ξ = 0` and return-level chart for all `ξ₀ ∈ ℝ` -/

section CurveDerivAll

/-- Curve stationarity for ANY shape `γ₁ s ∈ ℝ` (including `γ₁ s ≤ 0`), assuming admissibility. -/
theorem curve_scoreAll_eq_zero_of_isMaxOn {K' : Set (ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ}
    {γ₁ γ₂ : ℝ → ℝ} {a b s : ℝ} (h₁ : HasDerivAt γ₁ a s) (h₂ : HasDerivAt γ₂ b s)
    (hp₂ : 0 < γ₂ s) (hadm : ∀ i, 0 ≤ x i ∧ 0 < 1 + γ₁ s * x i / γ₂ s)
    (hmem : ∀ᶠ s' in 𝓝 s, (γ₁ s', γ₂ s') ∈ K')
    (hmax : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K' (γ₁ s, γ₂ s)) :
    a * ∑ i, gpdScoreXiAll (γ₁ s) (γ₂ s) (x i) + b * ∑ i, gpdScoreSigma (γ₁ s) (γ₂ s) (x i) = 0 := by
  have hu : ∀ i, 0 < γ₂ s + γ₁ s * x i := fun i => by
    have h := (hadm i).2
    have e : 1 + γ₁ s * x i / γ₂ s = (γ₂ s + γ₁ s * x i) / γ₂ s := by field_simp [hp₂.ne']
    rw [e] at h; exact (div_pos_iff_of_pos_right hp₂).1 h
  have hd : HasDerivAt (fun r => ∑ i, log (gpdDensity (γ₁ r) (γ₂ r) (x i)))
      (∑ i, (a * gpdScoreXiAll (γ₁ s) (γ₂ s) (x i) + b * gpdScoreSigma (γ₁ s) (γ₂ s) (x i))) s := by
    have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
      hasDerivAt_log_gpdDensity_curve_all (x := x i) h₁ h₂ hp₂ (hadm i).1 (hu i)
    convert this using 1; funext r; simp
  have hnear : ∀ᶠ r in 𝓝 s, 0 < γ₂ r ∧ ∀ i, 0 < 1 + γ₁ r * x i / γ₂ r := by
    refine (h₂.continuousAt.eventually (lt_mem_nhds hp₂)).and (eventually_all.2 fun i => ?_)
    have hc : ContinuousAt (fun r => 1 + γ₁ r * x i / γ₂ r) s :=
      continuousAt_const.add ((h₁.continuousAt.mul continuousAt_const).div h₂.continuousAt hp₂.ne')
    exact hc.eventually (lt_mem_nhds (hadm i).2)
  have hloc : IsLocalMax (fun r => ∑ i, log (gpdDensity (γ₁ r) (γ₂ r) (x i))) s := by
    filter_upwards [hmem, hnear] with s' hs' ⟨_, h2⟩
    have := hmax hs'
    simp only [mem_ofPred_eq] at this
    rw [gpdLogLikE_eq_coe' (fun i => ⟨(hadm i).1, h2 i⟩), gpdLogLikE_eq_coe' hadm] at this
    exact EReal.coe_le_coe_iff.1 this
  have := hloc.hasDerivAt_eq_zero hd
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  exact this

/-- Level-set chart for the POT return level valid for **ALL** `ξ₀ ∈ ℝ` (including `ξ₀ = 0`). -/
theorem isGPDProfileChart_returnLevel_all {ξ₀ σ₀ u ζ N : ℝ} (hNζ : 1 < N * ζ) :
    IsGPDProfileChart (fun p => gpdReturnLevel u p.1 p.2 ζ N) ξ₀ σ₀ ξ₀ Prod.fst id
      (fun s => σ₀ * boxCox ξ₀ (N * ζ) / boxCox s (N * ζ)) (fun _ => 1)
      (fun s => -(σ₀ * boxCox ξ₀ (N * ζ)) * boxCoxShapeDeriv s (N * ζ) / boxCox s (N * ζ) ^ 2) where
  map_true := rfl
  continuousAt := continuousAt_fst
  curve_chart := Eventually.of_forall fun p hp => by
    have hb := boxCox_pos_of_one_lt (ρ := p.1) hNζ
    simp only [gpdReturnLevel, add_right_inj] at hp
    refine Prod.ext rfl ?_
    rw [← hp]; field_simp
  level := Eventually.of_forall fun s => by
    have hb := boxCox_pos_of_one_lt (ρ := s) hNζ
    simp only [gpdReturnLevel, id, add_right_inj]; field_simp
  hasDerivAt₁ := Eventually.of_forall fun s => hasDerivAt_id s
  hasDerivAt₂ := Eventually.of_forall fun s => by
    have hb := boxCox_pos_of_one_lt (ρ := s) hNζ
    have h := (hasDerivAt_boxCox_shape_all s (one_pos.trans hNζ)).inv hb.ne'
    have := h.const_mul (σ₀ * boxCox ξ₀ (N * ζ))
    refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => by simp [div_eq_mul_inv])
  continuousAt₁ := continuousAt_const
  continuousAt₂ := by
    have hb := boxCox_pos_of_one_lt (ρ := ξ₀) hNζ
    refine ContinuousAt.div (continuousAt_const.mul
      ((continuous_boxCoxShapeDeriv (one_pos.trans hNζ)).continuousAt))
      (((continuous_boxCox_shape (one_pos.trans hNζ)).pow 2).continuousAt) (by positivity)
  tangent_ne := Or.inl one_ne_zero

end CurveDerivAll

/-! ### Deviance convergence in probability for `-1/2 < ξ₀ < 0` and `ξ₀ = 0` -/

section DevianceNegZero

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {ξ₀ σ₀ : ℝ}

/-- Shared helper for `-1/2 < ξ₀ < 0`: any measurable, strongly consistent, admissible sequence `θn`
with `2 (ℓₙ(θn) - ℓₙ(θ₀)) ≥ 0` a.s. eventually satisfies `Bᵢⱼ, Cᵢⱼ → -Iᵢⱼ` in probability! -/
private lemma tendstoInMeasure_segHess_and_segHessW_neg
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θn : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θn n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θn n ω) atTop (𝓝 (ξ₀, σ₀)))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θn n ω).2 + (θn n ω).1 * X i ω)
    (hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      0 ≤ 2 * (gpdLogLikN (θn n ω).1 (θn n ω).2 (fun i => X i ω) n -
        gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n)) :
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHess gpdHessXiXi ξ₀ σ₀ (θn n ω) (X i ω)) atTop
      (fun _ => -(2 / ((1 + ξ₀) * (1 + 2 * ξ₀)))) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHess gpdHessXiSigma ξ₀ σ₀ (θn n ω) (X i ω)) atTop
      (fun _ => -(1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀)))) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHess gpdHessSigmaSigma ξ₀ σ₀ (θn n ω) (X i ω)) atTop
      (fun _ => -(1 / (σ₀ ^ 2 * (1 + 2 * ξ₀)))) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHessW gpdHessXiXi ξ₀ σ₀ (θn n ω) (X i ω)) atTop
      (fun _ => -(2 / ((1 + ξ₀) * (1 + 2 * ξ₀)))) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHessW gpdHessXiSigma ξ₀ σ₀ (θn n ω) (X i ω)) atTop
      (fun _ => -(1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀)))) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHessW gpdHessSigmaSigma ξ₀ σ₀ (θn n ω) (X i ω)) atTop
      (fun _ => -(1 / (σ₀ ^ 2 * (1 + 2 * ξ₀)))) := by
  have hξ0 : ξ₀ ≠ 0 := hξ₀'.ne
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hS₁m := aemeasurable_gpdNormScoreXi (ξ₀ := ξ₀) (σ₀ := σ₀) hX
  have hS₂m := aemeasurable_gpdNormScoreSigma (ξ₀ := ξ₀) (σ₀ := σ₀) hX
  set S₁ : ℕ → Ω → ℝ := fun n ω => gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n
  set S₂ : ℕ → Ω → ℝ := fun n ω => gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n
  have hS₁b : IsBoundedInProbability P S₁ := by
    simpa [S₁, gpdNormScoreXi] using isBoundedInProbability_lin_score hξ₀ hξ0 hσ₀ hX hind 1 0
  have hS₂b : IsBoundedInProbability P S₂ := by
    simpa [S₂, gpdNormScoreSigma] using isBoundedInProbability_lin_score hξ₀ hξ0 hσ₀ hX hind 0 1
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  have hs₁₁ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiXi ξ₀ σ₀)
    (integrable_gpdHessXiXi hσ₀ hξ0 hξ₀)
  have hs₁₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiSigma ξ₀ σ₀)
    (integrable_gpdHessXiSigma hσ₀ hξ0 hξ₀)
  have hs₂₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessSigmaSigma ξ₀ σ₀)
    (integrable_gpdHessSigmaSigma hσ₀ hξ0 hξ₀)
  rw [integral_gpdHessXiXi hσ₀ hξ0 hξ₀] at hs₁₁
  rw [integral_gpdHessXiSigma hσ₀ hξ0 hξ₀] at hs₁₂
  rw [integral_gpdHessSigmaSigma hσ₀ hξ0 hξ₀] at hs₂₂
  have hsD : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (X i ω)) atTop
      (𝓝 (∫ x, gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) x ∂gpdMeasure ξ₀ σ₀)) :=
    ae_all_iff.2 fun k => ae_tendsto_avg_comp hX hind (measurable_gpdDomTail _ _ _)
      (integrable_gpdDomTail hξ₀ hξ₀' hσ₀ _)
  have hdlim := tendsto_integral_gpdDomTail hξ₀ hξ₀' hσ₀
  set lam := 1 / (4 * (1 + ξ₀) * (1 + σ₀ ^ 2))
  have hlam : 0 < lam := by
    have : 0 < 1 + ξ₀ := by linarith
    positivity
  -- Preliminary √n rate from `0 ≤ 2 (ℓₙ(θn) - ℓₙ(θ₀))` + one-sided negative definiteness of `Cₙ`!
  have hquadW : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiXi ξ₀ σ₀ (θn n ω) (X i ω)) +
        2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiSigma ξ₀ σ₀ (θn n ω) (X i ω)) +
        t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma ξ₀ σ₀ (θn n ω) (X i ω)) ≤
        -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2) := by
    filter_upwards [hsupp, hcons, hadm, hs₁₁, hs₁₂, hs₂₂, hsD] with ω hω hc ha h1 h2 h3 hD
    exact eventually_quad_avg_segHessW_le_neg hξ₀ hξ₀' hσ₀ hlam (gpdInfo_quad_le hξ₀ hξ₀' hσ₀)
      (fun i => ⟨(hω i).1.le, (hω i).2⟩) hc ha h1 h2 h3 hD hdlim
  have hrate : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      |√(n : ℝ) * ((θn n ω).1 - ξ₀)| + |√(n : ℝ) * ((θn n ω).2 - σ₀)| ≤
        8 / lam * (|S₁ n ω| + |S₂ n ω|) := by
    filter_upwards [hsupp, hcons, hadm, hnonneg, hquadW] with ω hω hc ha hnn hq
    filter_upwards [hc.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀), ha, hnn, hq,
      eventually_gt_atTop 0] with n hnb han hnnn hqn hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsq_inv : √(n : ℝ) * (√(n : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)).ne'
    have hD_eq : 2 * (gpdLogLikN (θn n ω).1 (θn n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) =
        2 * (√(n : ℝ) * ((θn n ω).1 - ξ₀) * S₁ n ω + √(n : ℝ) * ((θn n ω).2 - σ₀) * S₂ n ω) +
          ((√(n : ℝ) * ((θn n ω).1 - ξ₀)) ^ 2 *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiXi ξ₀ σ₀ (θn n ω) (X i ω)) +
          2 * (√(n : ℝ) * ((θn n ω).1 - ξ₀)) * (√(n : ℝ) * ((θn n ω).2 - σ₀)) *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiSigma ξ₀ σ₀ (θn n ω) (X i ω)) +
          (√(n : ℝ) * ((θn n ω).2 - σ₀)) ^ 2 *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma ξ₀ σ₀ (θn n ω) (X i ω))) := by
      simp only [gpdLogLikN, S₁, S₂, gpdNormScoreXi, gpdNormScoreSigma]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      have hterm := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
        two_mul_log_gpdDensity_sub_eq_segHessW_neg hξ₀' hσ₀ hnb (hω i).1.le (hω i).2
          (han i (Finset.mem_range.1 hi))
      rw [hterm]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have h1 : √(n : ℝ) * ((θn n ω).1 - ξ₀) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω)) =
          ((θn n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω) := by
        calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θn n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω)) := by ring
          _ = _ := by rw [hsq_inv, one_mul]
      have h2 : √(n : ℝ) * ((θn n ω).2 - σ₀) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω)) =
          ((θn n ω).2 - σ₀) * ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω) := by
        calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θn n ω).2 - σ₀) * ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω)) := by ring
          _ = _ := by rw [hsq_inv, one_mul]
      have h3 : ∀ (a b c : ℝ), (√(n : ℝ) * a) * (√(n : ℝ) * b) * ((n : ℝ)⁻¹ * c) = a * b * c := fun a b c => by
        calc _ = ((√(n : ℝ)) ^ 2 * (n : ℝ)⁻¹) * (a * b * c) := by ring
          _ = a * b * c := by rw [hsq, mul_inv_cancel₀ hn', one_mul]
      rw [h1, h2]
      have q1 := h3 ((θn n ω).1 - ξ₀) ((θn n ω).1 - ξ₀) (∑ i ∈ Finset.range n, segHessW gpdHessXiXi ξ₀ σ₀ (θn n ω) (X i ω))
      have q2 := h3 ((θn n ω).1 - ξ₀) ((θn n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessXiSigma ξ₀ σ₀ (θn n ω) (X i ω))
      have q3 := h3 ((θn n ω).2 - σ₀) ((θn n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma ξ₀ σ₀ (θn n ω) (X i ω))
      linarith
    rw [hD_eq] at hnnn
    exact abs_add_abs_le_of_nonneg_quad hlam hqn hnnn
  -- Endpoint ratio `r n ω → 0` in probability
  set Mx : ℕ → Ω → ℝ := fun n ω => runMax (fun i => 1 / (σ₀ + ξ₀ * X i ω)) n
  set e₀ := -σ₀ / ξ₀
  have he₀0 : 0 < e₀ := div_pos_of_neg_of_neg (by linarith) hξ₀'
  set r : ℕ → Ω → ℝ := fun n ω => (1 + e₀) * (|(θn n ω).1 - ξ₀| + |(θn n ω).2 - σ₀|) * Mx n ω
  have hMxm : ∀ n, AEMeasurable (Mx n) P := fun n =>
    aemeasurable_runMax (fun i => by have := hXm i; fun_prop) n
  have hrm : ∀ n, AEMeasurable (r n) P := fun n => by
    have := hθm n; have := hMxm n; dsimp only [r]; fun_prop
  have hY := tendstoInMeasure_runMax_div_sqrt hξ₀ hξ0 hσ₀ hX
  have hr : TendstoInMeasure P r atTop (fun _ => 0) := by
    set g : ℕ → Ω → ℝ := fun n ω => (1 + e₀) * (8 / lam) *
      (|Mx n ω / √(n : ℝ) * S₁ n ω| + |Mx n ω / √(n : ℝ) * S₂ n ω|)
    have hg : TendstoInMeasure P g atTop (fun _ => 0) := by
      have a₁ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₁b hY)
      have a₂ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₂b hY)
      simpa only [mul_zero] using tendstoInMeasure_comp (tendstoInMeasure_add_zero a₁ a₂)
        (φ := fun z => (1 + e₀) * (8 / lam) * z) (by fun_prop)
    have hgm : ∀ n, AEStronglyMeasurable (g n) P := fun n => by
      have := hMxm n; have := hS₁m n; have := hS₂m n
      exact (by dsimp only [g, S₁, S₂]; fun_prop : AEMeasurable (g n) P).aestronglyMeasurable
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le (fun n => (hrm n).aestronglyMeasurable)
      hgm ?_ hg
    filter_upwards [hrate] with ω hω
    filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
    have hM0 : 0 ≤ Mx n ω := runMax_nonneg _ _
    rw [abs_mul, abs_mul, abs_of_nonneg hsq.le] at hn
    have hr0 : 0 ≤ r n ω := by dsimp only [r]; positivity
    rw [abs_of_nonneg hr0]
    dsimp only [r, g]
    rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hM0, abs_of_pos hsq]
    have e : (1 + e₀) * (|(θn n ω).1 - ξ₀| + |(θn n ω).2 - σ₀|) * Mx n ω =
        (1 + e₀) * (√(n : ℝ) * |(θn n ω).1 - ξ₀| + √(n : ℝ) * |(θn n ω).2 - σ₀|) *
          (Mx n ω / √(n : ℝ)) := by field_simp
    rw [e]
    have hY0 : 0 ≤ Mx n ω / √(n : ℝ) := by positivity
    have hle : (1 + e₀) * (√(n : ℝ) * |(θn n ω).1 - ξ₀| + √(n : ℝ) * |(θn n ω).2 - σ₀|) *
        (Mx n ω / √(n : ℝ)) ≤ (1 + e₀) * (8 / lam * (|S₁ n ω| + |S₂ n ω|)) *
        (Mx n ω / √(n : ℝ)) := by gcongr
    exact hle.trans (le_of_eq (by ring))
  -- Cutoff convergence helper for BOTH `segHess` and `segHessW`!
  have hconv_gen : ∀ (S : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ × ℝ → ℝ → ℝ),
      (∀ H, (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
        Measurable fun p : (ℝ × ℝ) × ℝ => S H ξ₀ σ₀ p.1 p.2) →
      (∀ (H : ℝ → ℝ → ℝ → ℝ) (m : ℝ) (x : ℕ → ℝ) (θs : ℕ → ℝ × ℝ) (d : ℕ → ℝ) (ε : ℝ),
        (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
        (∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
          ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
        (∀ ξ σ y, 0 ≤ y → 0 < σ + ξ * y → |H ξ σ y| ≤ gpdHessCoef (ξ, σ) *
          (|log (1 + ξ * y / σ)| + y / (σ + ξ * y) + (y / (σ + ξ * y)) ^ 2 + 1)) →
        (∀ i, 0 ≤ x i ∧ 0 < σ₀ + ξ₀ * x i) → Tendsto θs atTop (𝓝 (ξ₀, σ₀)) →
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i)) atTop (𝓝 m) →
        (∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i)) atTop (𝓝 (d k))) →
        Tendsto d atTop (𝓝 0) → 0 < ε →
        ∀ᶠ n : ℕ in atTop, (∀ i < n, (σ₀ + ξ₀ * x i) / 2 ≤ (θs n).2 + (θs n).1 * x i) →
          |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, S H ξ₀ σ₀ (θs n) (x i) - m| ≤ ε) →
      ∀ (H : ℝ → ℝ → ℝ → ℝ) (m : ℝ),
        (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
        (∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
          ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
        (∀ ξ σ y, 0 ≤ y → 0 < σ + ξ * y → |H ξ σ y| ≤ gpdHessCoef (ξ, σ) *
          (|log (1 + ξ * y / σ)| + y / (σ + ξ * y) + (y / (σ + ξ * y)) ^ 2 + 1)) →
        (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (X i ω))
          atTop (𝓝 m)) →
        TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          S H ξ₀ σ₀ (θn n ω) (X i ω)) atTop (fun _ => m) := by
    intro S hSm hSev H m hHm hH hHb hsm
    set f : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      S H ξ₀ σ₀ (θn n ω) (X i ω) - m
    have hfm : ∀ n, AEMeasurable (f n) P := fun n =>
      ((Finset.aemeasurable_fun_sum _ fun i _ =>
        (hSm H hHm).comp_aemeasurable ((hθm n).prodMk (hXm i))).const_mul _).sub_const m
    have h1 := tendstoInMeasure_mul_cutoff f hr
    have h2 : TendstoInMeasure P (fun n ω => f n ω * (1 - cutoff (r n ω))) atTop (fun _ => 0) := by
      refine tendstoInMeasure_of_tendsto_ae (fun n => ((hfm n).mul (aemeasurable_const.sub
        (continuous_cutoff.measurable.comp_aemeasurable (hrm n)))).aestronglyMeasurable) ?_
      filter_upwards [hsupp, hcons, hsm, hsD] with ω hω hc hm hD
      refine Metric.tendsto_nhds.2 fun ε hε => ?_
      filter_upwards [hSev H m (fun i => X i ω) (fun n => θn n ω)
        (fun k => ∫ x, gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) x ∂gpdMeasure ξ₀ σ₀) (ε / 2)
        hHm hH hHb (fun i => ⟨(hω i).1.le, (hω i).2⟩) hc hm hD hdlim (by positivity)] with n hn
      rw [Real.dist_eq, sub_zero]
      by_cases hcut : cutoff (r n ω) = 1
      · rw [hcut, sub_self, mul_zero, abs_zero]; exact hε
      · have hr' : r n ω < 1 / 2 := by
          by_contra h; exact hcut (cutoff_of_ge (not_lt.1 h))
        have hhalf := half_le_of_endpoint hξ₀' (θ := θn n ω) (fun i => ⟨(hω i).1.le, (hω i).2⟩) hr'
        have hfn := hn hhalf
        have hc0 := cutoff_nonneg (r n ω)
        have hc1 := cutoff_le_one (r n ω)
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - cutoff (r n ω))]
        calc |f n ω| * (1 - cutoff (r n ω)) ≤ ε / 2 * 1 :=
              mul_le_mul hfn (by linarith) (by linarith) (by positivity)
          _ < ε := by linarith
    have h3 := tendstoInMeasure_add_zero h1 h2
    have e : (fun n ω => f n ω * cutoff (r n ω) + f n ω * (1 - cutoff (r n ω))) = f := by
      funext n ω; ring
    rw [e] at h3
    have := tendstoInMeasure_comp h3 (φ := fun z => z + m) (by fun_prop)
    simpa only [f, sub_add_cancel, zero_add] using this
  have hB := hconv_gen segHess (fun H hH => measurable_segHess hH)
    (fun H m x θs d ε hHm hH hHb hx hc hm hD hd hε =>
      eventually_abs_avg_segHess_sub_le hξ₀ hξ₀' hσ₀ hHm hH hHb hx hc hm hD hd hε)
  have hC := hconv_gen segHessW (fun H hH => measurable_segHessW hH)
    (fun H m x θs d ε hHm hH hHb hx hc hm hD hd hε =>
      eventually_abs_avg_segHessW_sub_le_neg hξ₀ hξ₀' hσ₀ hHm hH hHb hx hc hm hD hd hε)
  exact ⟨
    hB gpdHessXiXi _ measurable_gpdHessXiXi₃ (fun _ h1 h2 h3 => continuousAt_gpdHessXiXi₃ h1 h2 h3)
      (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).1) hs₁₁,
    hB gpdHessXiSigma _ measurable_gpdHessXiSigma₃ (fun _ _ h2 h3 => continuousAt_gpdHessXiSigma₃ h2 h3)
      (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.1) hs₁₂,
    hB gpdHessSigmaSigma _ measurable_gpdHessSigmaSigma₃ (fun _ _ h2 h3 => continuousAt_gpdHessSigmaSigma₃ h2 h3)
      (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.2) hs₂₂,
    hC gpdHessXiXi _ measurable_gpdHessXiXi₃ (fun _ h1 h2 h3 => continuousAt_gpdHessXiXi₃ h1 h2 h3)
      (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).1) hs₁₁,
    hC gpdHessXiSigma _ measurable_gpdHessXiSigma₃ (fun _ _ h2 h3 => continuousAt_gpdHessXiSigma₃ h2 h3)
      (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.1) hs₁₂,
    hC gpdHessSigmaSigma _ measurable_gpdHessSigmaSigma₃ (fun _ _ h2 h3 => continuousAt_gpdHessSigmaSigma₃ h2 h3)
      (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.2) hs₂₂⟩

/-- Shared helper for `ξ₀ = 0`: any measurable, strongly consistent, admissible sequence `θn` with
`2 (ℓₙ(θn) - ℓₙ(θ₀)) ≥ 0` a.s. eventually satisfies `Bᵢⱼ, Cᵢⱼ → -I(0, σ₀)ᵢⱼ` in probability! -/
private lemma tendstoInMeasure_segHess_and_segHessW_zero
    (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P)
    {θn : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θn n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θn n ω) atTop (𝓝 (0, σ₀)))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θn n ω).2 + (θn n ω).1 * X i ω)
    (hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      0 ≤ 2 * (gpdLogLikN (θn n ω).1 (θn n ω).2 (fun i => X i ω) n -
        gpdLogLikN 0 σ₀ (fun i => X i ω) n)) :
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHess gpdHessXiXiAll 0 σ₀ (θn n ω) (X i ω)) atTop (fun _ => -2) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHess gpdHessXiSigma 0 σ₀ (θn n ω) (X i ω)) atTop (fun _ => -(1 / σ₀)) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHess gpdHessSigmaSigma 0 σ₀ (θn n ω) (X i ω)) atTop (fun _ => -(1 / σ₀ ^ 2)) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHessW gpdHessXiXiAll 0 σ₀ (θn n ω) (X i ω)) atTop (fun _ => -2) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHessW gpdHessXiSigma 0 σ₀ (θn n ω) (X i ω)) atTop (fun _ => -(1 / σ₀)) ∧
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHessW gpdHessSigmaSigma 0 σ₀ (θn n ω) (X i ω)) atTop (fun _ => -(1 / σ₀ ^ 2)) := by
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  set S₁ : ℕ → Ω → ℝ := fun n ω => gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n
  set S₂ : ℕ → Ω → ℝ := fun n ω => gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n
  have hS₁m : ∀ n, AEMeasurable (S₁ n) P := fun n => by
    have h1 : Measurable (expScoreXi σ₀) := by unfold expScoreXi; fun_prop
    refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul _
    simp only [gpdScoreXiAll_zero]
    exact h1.comp_aemeasurable (hXm i)
  have hS₂m := aemeasurable_gpdNormScoreSigma (ξ₀ := 0) (σ₀ := σ₀) hX
  have hS₁b : IsBoundedInProbability P S₁ := by
    simpa [S₁, gpdNormScoreXiAll_zero] using isBoundedInProbability_lin_score_zero hσ₀ hX hind 1 0
  have hS₂b : IsBoundedInProbability P S₂ := by
    simpa [S₂, gpdNormScoreSigma, gpdScoreSigma_zero] using
      isBoundedInProbability_lin_score_zero hσ₀ hX hind 0 1
  have hpos := ae_forall_pos_of_gpd (ξ := 0) hσ₀ hX
  have hs₁₁ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiXiAll 0 σ₀)
    (integrable_gpdHessXiXiAll_zero hσ₀)
  have hs₁₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiSigma 0 σ₀)
    (integrable_gpdHessXiSigma_zero hσ₀)
  have hs₂₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessSigmaSigma 0 σ₀)
    (integrable_gpdHessSigmaSigma_zero hσ₀)
  rw [integral_gpdHessXiXiAll_zero hσ₀] at hs₁₁
  rw [integral_gpdHessXiSigma_zero hσ₀] at hs₁₂
  rw [integral_gpdHessSigmaSigma_zero hσ₀] at hs₂₂
  have hsD : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomZeroTail σ₀ (k : ℝ) (X i ω)) atTop
        (𝓝 (∫ x, gpdDomZeroTail σ₀ (k : ℝ) x ∂gpdMeasure 0 σ₀)) :=
    ae_all_iff.2 fun k =>
      ae_tendsto_avg_comp hX hind (measurable_gpdDomZeroTail σ₀ k) (integrable_gpdDomZeroTail hσ₀ k)
  have hdlim := tendsto_integral_gpdDomZeroTail hσ₀
  set lam := 1 / (4 * (1 + σ₀ ^ 2))
  have hlam : 0 < lam := by positivity
  have hnegI : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * (-2) + 2 * t₁ * t₂ * (-(1 / σ₀)) + t₂ ^ 2 * (-(1 / σ₀ ^ 2)) ≤
      -lam * (t₁ ^ 2 + t₂ ^ 2) := fun t₁ t₂ => by
    set s := t₂ / σ₀
    have hq : (1 / 4 : ℝ) * (t₁ ^ 2 + s ^ 2) ≤ 2 * t₁ ^ 2 + 2 * t₁ * s + s ^ 2 := by
      nlinarith [sq_nonneg (t₁ + s), sq_nonneg (t₁ + s / 2), sq_nonneg t₁, sq_nonneg s]
    have hs2 : t₂ ^ 2 / (1 + σ₀ ^ 2) ≤ s ^ 2 := by
      simp only [s, div_pow]
      rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hσ₀)]
      nlinarith [sq_nonneg t₂]
    have ht1 : t₁ ^ 2 / (1 + σ₀ ^ 2) ≤ t₁ ^ 2 := div_le_self (sq_nonneg _) (by nlinarith)
    have h1 : lam * (t₁ ^ 2 + t₂ ^ 2) ≤ (1 / 4) * (t₁ ^ 2 + s ^ 2) := by
      have hden : 1 + σ₀ ^ 2 ≠ 0 := by positivity
      have e : lam * (t₁ ^ 2 + t₂ ^ 2) = (1 / 4) * (t₁ ^ 2 / (1 + σ₀ ^ 2) + t₂ ^ 2 / (1 + σ₀ ^ 2)) := by
        simp only [lam]; field_simp [hden]
      rw [e]; linarith
    have heq : t₁ ^ 2 * (-2) + 2 * t₁ * t₂ * (-(1 / σ₀)) + t₂ ^ 2 * (-(1 / σ₀ ^ 2)) =
        -(2 * t₁ ^ 2 + 2 * t₁ * s + s ^ 2) := by
      simp only [s]; field_simp [hσ₀.ne']; ring
    linarith
  have hquadW : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiXiAll 0 σ₀ (θn n ω) (X i ω)) +
        2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiSigma 0 σ₀ (θn n ω) (X i ω)) +
        t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma 0 σ₀ (θn n ω) (X i ω)) ≤
        -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2) := by
    filter_upwards [hpos, hcons, hadm, hs₁₁, hs₁₂, hs₂₂, hsD] with ω hω hc ha h1 h2 h3 hD
    exact eventually_quad_avg_segHessW_le_zero hσ₀ hlam hnegI (fun i => (hω i).le) hc ha h1 h2 h3 hD hdlim
  have hrate : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      |√(n : ℝ) * ((θn n ω).1 - 0)| + |√(n : ℝ) * ((θn n ω).2 - σ₀)| ≤
        8 / lam * (|S₁ n ω| + |S₂ n ω|) := by
    filter_upwards [hpos, hcons, hadm, hnonneg, hquadW] with ω hω hc ha hnn hq
    filter_upwards [hc.eventually (gpdNbhdZero_mem_nhds hσ₀), ha, hnn, hq,
      eventually_gt_atTop 0] with n hnb han hnnn hqn hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsq_inv : √(n : ℝ) * (√(n : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)).ne'
    have hD_eq : 2 * (gpdLogLikN (θn n ω).1 (θn n ω).2 (fun i => X i ω) n -
          gpdLogLikN 0 σ₀ (fun i => X i ω) n) =
        2 * (√(n : ℝ) * ((θn n ω).1 - 0) * S₁ n ω + √(n : ℝ) * ((θn n ω).2 - σ₀) * S₂ n ω) +
          ((√(n : ℝ) * ((θn n ω).1 - 0)) ^ 2 *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiXiAll 0 σ₀ (θn n ω) (X i ω)) +
          2 * (√(n : ℝ) * ((θn n ω).1 - 0)) * (√(n : ℝ) * ((θn n ω).2 - σ₀)) *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessXiSigma 0 σ₀ (θn n ω) (X i ω)) +
          (√(n : ℝ) * ((θn n ω).2 - σ₀)) ^ 2 *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma 0 σ₀ (θn n ω) (X i ω))) := by
      simp only [gpdLogLikN, S₁, S₂, gpdNormScoreXiAll_zero, gpdNormScoreSigma, gpdScoreSigma_zero]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      have hterm := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
        two_mul_log_gpdDensity_sub_eq_segHessW_zero hσ₀ hnb (hω i).le (han i (Finset.mem_range.1 hi))
      rw [hterm]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have h1 : √(n : ℝ) * ((θn n ω).1 - 0) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω)) =
          ((θn n ω).1 - 0) * ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω) := by
        calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θn n ω).1 - 0) * ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω)) := by ring
          _ = _ := by rw [hsq_inv, one_mul]
      have h2 : √(n : ℝ) * ((θn n ω).2 - σ₀) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω)) =
          ((θn n ω).2 - σ₀) * ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω) := by
        calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θn n ω).2 - σ₀) * ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω)) := by ring
          _ = _ := by rw [hsq_inv, one_mul]
      have h3 : ∀ (a b c : ℝ), (√(n : ℝ) * a) * (√(n : ℝ) * b) * ((n : ℝ)⁻¹ * c) = a * b * c := fun a b c => by
        calc _ = ((√(n : ℝ)) ^ 2 * (n : ℝ)⁻¹) * (a * b * c) := by ring
          _ = a * b * c := by rw [hsq, mul_inv_cancel₀ hn', one_mul]
      rw [h1, h2]
      have q1 := h3 ((θn n ω).1 - 0) ((θn n ω).1 - 0) (∑ i ∈ Finset.range n, segHessW gpdHessXiXiAll 0 σ₀ (θn n ω) (X i ω))
      have q2 := h3 ((θn n ω).1 - 0) ((θn n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessXiSigma 0 σ₀ (θn n ω) (X i ω))
      have q3 := h3 ((θn n ω).2 - σ₀) ((θn n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma 0 σ₀ (θn n ω) (X i ω))
      linarith
    rw [hD_eq] at hnnn
    exact abs_add_abs_le_of_nonneg_quad hlam hqn hnnn
  -- Safe-region control `r n ω = (2 / σ₀) * |(θn n ω).1| * runMax X n → 0` in probability
  set Mx : ℕ → Ω → ℝ := fun n ω => runMax (fun i => X i ω) n
  have hMxm : ∀ n, AEMeasurable (Mx n) P := fun n => aemeasurable_runMax hXm n
  have hMx0 := tendstoInMeasure_runMax_div_sqrt_zero hσ₀ hX
  set r : ℕ → Ω → ℝ := fun n ω => (2 / σ₀) * |(θn n ω).1| * Mx n ω
  have hrm : ∀ n, AEMeasurable (r n) P := fun n => by
    have := hθm n; have := hMxm n; dsimp only [r]; fun_prop
  have hr : TendstoInMeasure P r atTop (fun _ => 0) := by
    set g : ℕ → Ω → ℝ := fun n ω => (2 / σ₀) * (8 / lam) *
      ((Mx n ω / √(n : ℝ)) * |S₁ n ω| + (Mx n ω / √(n : ℝ)) * |S₂ n ω|)
    have hg : TendstoInMeasure P g atTop (fun _ => 0) := by
      have hS₁abs : IsBoundedInProbability P (fun n ω => |S₁ n ω|) := fun ε hε => by
        obtain ⟨M, hM⟩ := hS₁b ε hε
        exact ⟨M, hM.mono fun n hn => by simpa only [abs_abs] using hn⟩
      have hS₂abs : IsBoundedInProbability P (fun n ω => |S₂ n ω|) := fun ε hε => by
        obtain ⟨M, hM⟩ := hS₂b ε hε
        exact ⟨M, hM.mono fun n hn => by simpa only [abs_abs] using hn⟩
      have a₁ := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₁abs hMx0
      have a₂ := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₂abs hMx0
      simpa only [mul_zero] using tendstoInMeasure_comp (tendstoInMeasure_add_zero a₁ a₂)
        (φ := fun z => (2 / σ₀) * (8 / lam) * z) (by fun_prop)
    have hgm : ∀ n, AEStronglyMeasurable (g n) P := fun n => by
      have := hMxm n; have := hS₁m n; have := hS₂m n
      exact (by dsimp only [g]; fun_prop : AEMeasurable (g n) P).aestronglyMeasurable
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le (fun n => (hrm n).aestronglyMeasurable)
      hgm ?_ hg
    filter_upwards [hrate] with ω hω
    filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
    have hM0 : 0 ≤ Mx n ω := runMax_nonneg _ _
    have h1 : √(n : ℝ) * |(θn n ω).1| ≤ 8 / lam * (|S₁ n ω| + |S₂ n ω|) := by
      have e1 : |√(n : ℝ) * ((θn n ω).1 - 0)| = √(n : ℝ) * |(θn n ω).1| := by
        rw [sub_zero, abs_mul, abs_of_nonneg hsq.le]
      linarith [abs_nonneg (√(n : ℝ) * ((θn n ω).2 - σ₀))]
    have hr0 : 0 ≤ r n ω := by dsimp only [r]; positivity
    rw [abs_of_nonneg hr0]
    dsimp only [r, g]
    have e : (2 / σ₀) * |(θn n ω).1| * Mx n ω =
        (2 / σ₀) * (√(n : ℝ) * |(θn n ω).1|) * (Mx n ω / √(n : ℝ)) := by field_simp
    rw [e]
    have hY0 : 0 ≤ Mx n ω / √(n : ℝ) := by positivity
    have h2 : (2 / σ₀) * (√(n : ℝ) * |(θn n ω).1|) * (Mx n ω / √(n : ℝ)) ≤
        (2 / σ₀) * (8 / lam * (|S₁ n ω| + |S₂ n ω|)) * (Mx n ω / √(n : ℝ)) := by gcongr
    exact h2.trans (le_of_eq (by ring))
  -- Cutoff convergence for `segHess` and `segHessW`
  have hconv_gen : ∀ (S : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ × ℝ → ℝ → ℝ),
      (∀ H, (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
        Measurable fun p : (ℝ × ℝ) × ℝ => S H 0 σ₀ p.1 p.2) →
      (∀ (H : ℝ → ℝ → ℝ → ℝ) (m : ℝ) (x : ℕ → ℝ) (θs : ℕ → ℝ × ℝ) (d : ℕ → ℝ) (ε : ℝ),
        (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
        (∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
          ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
        (∀ θ ∈ gpdNbhdZero σ₀, ∀ y, 0 ≤ y → -(1 / 2) ≤ θ.1 * (y / θ.2) →
          |H θ.1 θ.2 y| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ y) →
        (∀ i, 0 ≤ x i) → Tendsto θs atTop (𝓝 (0, σ₀)) →
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (x i)) atTop (𝓝 m) →
        (∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          gpdDomZeroTail σ₀ (k : ℝ) (x i)) atTop (𝓝 (d k))) →
        Tendsto d atTop (𝓝 0) → 0 < ε →
        ∀ᶠ n : ℕ in atTop, (∀ i < n, |(θs n).1| * x i ≤ σ₀ / 4) →
          |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, S H 0 σ₀ (θs n) (x i) - m| ≤ ε) →
      ∀ (H : ℝ → ℝ → ℝ → ℝ) (m : ℝ),
        (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
        (∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
          ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
        (∀ θ ∈ gpdNbhdZero σ₀, ∀ y, 0 ≤ y → -(1 / 2) ≤ θ.1 * (y / θ.2) →
          |H θ.1 θ.2 y| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ y) →
        (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (X i ω))
          atTop (𝓝 m)) →
        TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          S H 0 σ₀ (θn n ω) (X i ω)) atTop (fun _ => m) := by
    intro S hSm hSev H m hHm hH hHb hsm
    set f : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      S H 0 σ₀ (θn n ω) (X i ω) - m
    have hfm : ∀ n, AEMeasurable (f n) P := fun n =>
      ((Finset.aemeasurable_fun_sum _ fun i _ =>
        (hSm H hHm).comp_aemeasurable ((hθm n).prodMk (hXm i))).const_mul _).sub_const m
    have h1 := tendstoInMeasure_mul_cutoff f hr
    have h2 : TendstoInMeasure P (fun n ω => f n ω * (1 - cutoff (r n ω))) atTop (fun _ => 0) := by
      refine tendstoInMeasure_of_tendsto_ae (fun n => ((hfm n).mul (aemeasurable_const.sub
        (continuous_cutoff.measurable.comp_aemeasurable (hrm n)))).aestronglyMeasurable) ?_
      filter_upwards [hpos, hcons, hsm, hsD] with ω hω hc hm hD
      refine Metric.tendsto_nhds.2 fun ε hε => ?_
      filter_upwards [hSev H m (fun i => X i ω) (fun n => θn n ω)
        (fun k => ∫ x, gpdDomZeroTail σ₀ (k : ℝ) x ∂gpdMeasure 0 σ₀) (ε / 2)
        hHm hH hHb (fun i => (hω i).le) hc hm hD hdlim (by positivity)] with n hn
      rw [Real.dist_eq, sub_zero]
      by_cases hcut : cutoff (r n ω) = 1
      · rw [hcut, sub_self, mul_zero, abs_zero]; exact hε
      · have hr' : r n ω < 1 / 2 := by
          by_contra h; exact hcut (cutoff_of_ge (not_lt.1 h))
        have hsafe : ∀ i < n, |(θn n ω).1| * X i ω ≤ σ₀ / 4 := fun i hi => by
          have hxi : X i ω ≤ Mx n ω := le_runMax (fun j => X j ω) hi
          have hmul : |(θn n ω).1| * X i ω ≤ |(θn n ω).1| * Mx n ω :=
            mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
          have hr_lt : (2 / σ₀) * (|(θn n ω).1| * Mx n ω) < 1 / 2 := by
            dsimp only [r] at hr'; linarith
          have : |(θn n ω).1| * Mx n ω < σ₀ / 4 := by
            have := mul_lt_mul_of_pos_left hr_lt (show 0 < σ₀ / 2 by positivity)
            have e1 : σ₀ / 2 * (2 / σ₀ * (|(θn n ω).1| * Mx n ω)) = |(θn n ω).1| * Mx n ω := by
              field_simp [hσ₀.ne']
            linarith
          linarith
        have hfn := hn hsafe
        have hc0 := cutoff_nonneg (r n ω)
        have hc1 := cutoff_le_one (r n ω)
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - cutoff (r n ω))]
        calc |f n ω| * (1 - cutoff (r n ω)) ≤ ε / 2 * 1 :=
              mul_le_mul hfn (by linarith) (by linarith) (by positivity)
          _ < ε := by linarith
    have h3 := tendstoInMeasure_add_zero h1 h2
    have e : (fun n ω => f n ω * cutoff (r n ω) + f n ω * (1 - cutoff (r n ω))) = f := by
      funext n ω; ring
    rw [e] at h3
    have := tendstoInMeasure_comp h3 (φ := fun z => z + m) (by fun_prop)
    simpa only [f, sub_add_cancel, zero_add] using this
  have hB := hconv_gen segHess (fun H hH => measurable_segHess hH)
    (fun H m x θs d ε hHm hH hHb hx hc hm hD hd hε =>
      eventually_abs_avg_segHess_sub_le_zero hσ₀ hHm hH hHb hx hc hm hD hd hε)
  have hC := hconv_gen segHessW (fun H hH => measurable_segHessW hH)
    (fun H m x θs d ε hHm hH hHb hx hc hm hD hd hε => by
      filter_upwards [eventually_abs_avg_segHessW_sub_le_zero hσ₀ hHm hH hHb hx hc hm hD hd hε,
        hc.eventually (gpdNbhdZero_mem_nhds hσ₀)] with n hn hnb hsafe
      refine hn fun i hi => ?_
      have hσθ : 7 * σ₀ / 8 ≤ (θs n).2 := hnb.2.1
      have hσθ_pos : 0 < (θs n).2 := by linarith
      have hlo : -(σ₀ / 4) ≤ (θs n).1 * x i := by
        have := hsafe i hi
        have h1 : |(θs n).1 * x i| ≤ σ₀ / 4 := by
          rw [abs_mul, abs_of_nonneg (hx i)]; exact this
        exact (abs_le.1 h1).1
      rw [← mul_div_assoc, le_div_iff₀ hσθ_pos]; linarith)
  exact ⟨
    hB gpdHessXiXiAll _ measurable_gpdHessXiXiAll₃ (fun _ h1 h2 => continuousAt_gpdHessXiXiAll₃ h1 h2)
      (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).1) hs₁₁,
    hB gpdHessXiSigma _ measurable_gpdHessXiSigma₃ (fun _ h1 h2 => continuousAt_gpdHessXiSigma₃ h1 h2)
      (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).2.1) hs₁₂,
    hB gpdHessSigmaSigma _ measurable_gpdHessSigmaSigma₃ (fun _ h1 h2 => continuousAt_gpdHessSigmaSigma₃ h1 h2)
      (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).2.2) hs₂₂,
    hC gpdHessXiXiAll _ measurable_gpdHessXiXiAll₃ (fun _ h1 h2 => continuousAt_gpdHessXiXiAll₃ h1 h2)
      (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).1) hs₁₁,
    hC gpdHessXiSigma _ measurable_gpdHessXiSigma₃ (fun _ h1 h2 => continuousAt_gpdHessXiSigma₃ h1 h2)
      (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).2.1) hs₁₂,
    hC gpdHessSigmaSigma _ measurable_gpdHessSigmaSigma₃ (fun _ h1 h2 => continuousAt_gpdHessSigmaSigma₃ h1 h2)
      (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).2.2) hs₂₂⟩

/-- Full-parameter deviance minus `Sₙᵀ I(θ₀)⁻¹ Sₙ` converges to `0` in probability for
`-1/2 < ξ₀ < 0`. -/
theorem tendstoInMeasure_gpdFullDeviance_sub_neg (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω)
    (hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      0 ≤ 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
        gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0) :
    TendstoInMeasure P (fun n ω =>
      2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) -
        gpdInfoInvQuad ξ₀ σ₀ (gpdNormScoreXiAll ξ₀ σ₀ (fun i => X i ω) n)
          (gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n)) atTop (fun _ => 0) := by
  have hξ0 : ξ₀ ≠ 0 := hξ₀'.ne
  obtain ⟨hd, hJ₁₁, hJ₁₂, hJ₂₂⟩ := gpdFisherInfo_det_adj hξ₀ hσ₀
  obtain ⟨hB₁₁, hB₁₂, hB₂₂, hC₁₁, hC₁₂, hC₂₂⟩ :=
    tendstoInMeasure_segHess_and_segHessW_neg hξ₀ hξ₀' hσ₀ hX hind hθm hcons hadm hnonneg
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hBm : ∀ (S : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ × ℝ → ℝ → ℝ) (H : ℝ → ℝ → ℝ → ℝ),
      (Measurable fun p : (ℝ × ℝ) × ℝ => S H ξ₀ σ₀ p.1 p.2) →
      ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        S H ξ₀ σ₀ (θh n ω) (X i ω)) P := fun S H hS n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hS.comp_aemeasurable ((hθm n).prodMk (hXm i))).const_mul _
  have hDm : ∀ n, AEMeasurable (fun ω => 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
      gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n)) P := fun n => by
    have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
    have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (ξ₀, σ₀)) hX aemeasurable_const n
    simp only at h2; fun_prop
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  have hS₁b : IsBoundedInProbability P (fun n ω => gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreXi] using isBoundedInProbability_lin_score hξ₀ hξ0 hσ₀ hX hind 1 0
  have hS₂b : IsBoundedInProbability P (fun n ω => gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreSigma] using isBoundedInProbability_lin_score hξ₀ hξ0 hσ₀ hX hind 0 1
  have hmain := tendstoInMeasure_full_deviance_of_converge (P := P)
    (A := 2 / ((1 + ξ₀) * (1 + 2 * ξ₀))) (B := 1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀)))
    (C := 1 / (σ₀ ^ 2 * (1 + 2 * ξ₀))) hd
    (S₁ := fun n ω => gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n)
    (S₂ := fun n ω => gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n)
    (T₁ := fun n ω => √(n : ℝ) * ((θh n ω).1 - ξ₀))
    (T₂ := fun n ω => √(n : ℝ) * ((θh n ω).2 - σ₀))
    (aemeasurable_gpdNormScoreXi hX) (aemeasurable_gpdNormScoreSigma hX)
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiXi₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiSigma₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessSigmaSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiXi₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessSigmaSigma₃))
    hDm hS₁b hS₂b hB₁₁ hB₁₂ hB₂₂ hC₁₁ hC₁₂ hC₂₂ ?_ ?_
  · convert hmain using 2 with n
    funext ω
    rw [gpdNormScoreXiAll_of_ne hξ0, gpdInfoInvQuad]
    have e2 := quad_div_eq_of_div_eq
      (s₁ := gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n)
      (s₂ := gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) hJ₁₁ hJ₁₂ hJ₂₂
    rw [e2]; ring
  · filter_upwards [hsupp, hcons, hadm, hroot] with ω hω hc ha hr
    filter_upwards [hc.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀), ha, hr, eventually_gt_atTop 0]
      with n hnb han hrn hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ))⁻¹ * n = √(n : ℝ) := by
      have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      field_simp; rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    have hexp := fun i (hi : i ∈ Finset.range n) =>
      gpdScore_sub_eq_segHess_neg hξ₀ hξ₀' hσ₀ hnb (hω i).2 (han i (Finset.mem_range.1 hi))
    have e1 := Finset.sum_congr rfl fun i hi => (hexp i hi).1
    have e2 := Finset.sum_congr rfl fun i hi => (hexp i hi).2
    rw [Finset.sum_sub_distrib, hrn.1, zero_sub] at e1
    rw [Finset.sum_sub_distrib, hrn.2, zero_sub] at e2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at e1 e2
    simp only [gpdNormScoreXi, gpdNormScoreSigma]
    constructor
    · rw [show ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω) =
        -(((θh n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiXi ξ₀ σ₀ (θh n ω) (X i ω) +
          ((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ (θh n ω) (X i ω))
        by linarith]
      have hsq_eq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ :=
        calc √(n : ℝ) * (n : ℝ)⁻¹ = ((√(n : ℝ))⁻¹ * n) * (n : ℝ)⁻¹ := by rw [hsq]
          _ = (√(n : ℝ))⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn', mul_one]
      have hcancel : ∀ x : ℝ, (n : ℝ)⁻¹ * x * (√(n : ℝ) * ((θh n ω).1 - ξ₀)) =
          (√(n : ℝ))⁻¹ * (((θh n ω).1 - ξ₀) * x) := fun x => by
        calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * (((θh n ω).1 - ξ₀) * x) := by ring
          _ = _ := by rw [hsq_eq]
      have hcancel2 : ∀ x : ℝ, (n : ℝ)⁻¹ * x * (√(n : ℝ) * ((θh n ω).2 - σ₀)) =
          (√(n : ℝ))⁻¹ * (((θh n ω).2 - σ₀) * x) := fun x => by
        calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * (((θh n ω).2 - σ₀) * x) := by ring
          _ = _ := by rw [hsq_eq]
      rw [hcancel, hcancel2]; ring
    · rw [show ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω) =
        -(((θh n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ (θh n ω) (X i ω) +
          ((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma ξ₀ σ₀ (θh n ω) (X i ω))
        by linarith]
      have hsq_eq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ :=
        calc √(n : ℝ) * (n : ℝ)⁻¹ = ((√(n : ℝ))⁻¹ * n) * (n : ℝ)⁻¹ := by rw [hsq]
          _ = (√(n : ℝ))⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn', mul_one]
      have hcancel : ∀ x : ℝ, (n : ℝ)⁻¹ * x * (√(n : ℝ) * ((θh n ω).1 - ξ₀)) =
          (√(n : ℝ))⁻¹ * (((θh n ω).1 - ξ₀) * x) := fun x => by
        calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * (((θh n ω).1 - ξ₀) * x) := by ring
          _ = _ := by rw [hsq_eq]
      have hcancel2 : ∀ x : ℝ, (n : ℝ)⁻¹ * x * (√(n : ℝ) * ((θh n ω).2 - σ₀)) =
          (√(n : ℝ))⁻¹ * (((θh n ω).2 - σ₀) * x) := fun x => by
        calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * (((θh n ω).2 - σ₀) * x) := by ring
          _ = _ := by rw [hsq_eq]
      rw [hcancel, hcancel2]; ring
  · filter_upwards [hsupp, hcons, hadm] with ω hω hc ha
    filter_upwards [hc.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀), ha, eventually_gt_atTop 0]
      with n hnb han hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsq_inv : √(n : ℝ) * (√(n : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)).ne'
    simp only [gpdLogLikN, gpdNormScoreXi, gpdNormScoreSigma]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have hterm := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
      two_mul_log_gpdDensity_sub_eq_segHessW_neg hξ₀' hσ₀ hnb (hω i).1.le (hω i).2
        (han i (Finset.mem_range.1 hi))
    rw [hterm]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : √(n : ℝ) * ((θh n ω).1 - ξ₀) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω)) =
        ((θh n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω) := by
      calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θh n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω)) := by ring
        _ = _ := by rw [hsq_inv, one_mul]
    have h2 : √(n : ℝ) * ((θh n ω).2 - σ₀) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω)) =
        ((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω) := by
      calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω)) := by ring
        _ = _ := by rw [hsq_inv, one_mul]
    have h3 : ∀ (a b c : ℝ), (√(n : ℝ) * a) * (√(n : ℝ) * b) * ((n : ℝ)⁻¹ * c) = a * b * c := fun a b c => by
      calc _ = ((√(n : ℝ)) ^ 2 * (n : ℝ)⁻¹) * (a * b * c) := by ring
        _ = a * b * c := by rw [hsq, mul_inv_cancel₀ hn', one_mul]
    rw [h1, h2]
    have q1 := h3 ((θh n ω).1 - ξ₀) ((θh n ω).1 - ξ₀) (∑ i ∈ Finset.range n, segHessW gpdHessXiXi ξ₀ σ₀ (θh n ω) (X i ω))
    have q2 := h3 ((θh n ω).1 - ξ₀) ((θh n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessXiSigma ξ₀ σ₀ (θh n ω) (X i ω))
    have q3 := h3 ((θh n ω).2 - σ₀) ((θh n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma ξ₀ σ₀ (θh n ω) (X i ω))
    linarith

/-- Curve-restricted deviance minus `(t₀ · Sₙ)² / (t₀ᵀ I t₀)` converges to `0` in probability for
`-1/2 < ξ₀ < 0`. -/
theorem tendstoInMeasure_gpdCurveDeviance_sub_neg (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {γ₁ γ₂ t₁ t₂ : ℝ → ℝ} {s₀ : ℝ} (hγ₁ : HasDerivAt γ₁ (t₁ s₀) s₀) (hγ₂ : HasDerivAt γ₂ (t₂ s₀) s₀)
    (ht₁ : ContinuousAt t₁ s₀) (ht₂ : ContinuousAt t₂ s₀) (hs₁ : γ₁ s₀ = ξ₀) (hs₂ : γ₂ s₀ = σ₀)
    (hne : t₁ s₀ ≠ 0 ∨ t₂ s₀ ≠ 0)
    {θt : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θt n) P)
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θt n ω).2 + (θt n ω).1 * X i ω)
    (hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      0 ≤ 2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
        gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n))
    (hcurve : ∀ᵐ ω ∂P, ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 s₀) ∧ ∀ᶠ n in atTop,
      θt n ω = (γ₁ (s n), γ₂ (s n)) ∧
      t₁ (s n) * ∑ i ∈ Finset.range n, gpdScoreXiAll (θt n ω).1 (θt n ω).2 (X i ω) +
        t₂ (s n) * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) = 0) :
    TendstoInMeasure P (fun n ω =>
      2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) -
        (t₁ s₀ * gpdNormScoreXiAll ξ₀ σ₀ (fun i => X i ω) n +
          t₂ s₀ * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) ^ 2 /
            gpdInfoQuad ξ₀ σ₀ (t₁ s₀) (t₂ s₀)) atTop (fun _ => 0) := by
  have hξ0 : ξ₀ ≠ 0 := hξ₀'.ne
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θt n ω) atTop (𝓝 (ξ₀, σ₀)) := by
    filter_upwards [hcurve] with ω ⟨s, hs, hev⟩
    have h1 : Tendsto (fun n => (γ₁ (s n), γ₂ (s n))) atTop (𝓝 (ξ₀, σ₀)) := by
      rw [← hs₁, ← hs₂]
      exact (hγ₁.continuousAt.tendsto.comp hs).prodMk_nhds (hγ₂.continuousAt.tendsto.comp hs)
    exact h1.congr' (hev.mono fun n hn => hn.1.symm)
  obtain ⟨hB₁₁, hB₁₂, hB₂₂, hC₁₁, hC₁₂, hC₂₂⟩ :=
    tendstoInMeasure_segHess_and_segHessW_neg hξ₀ hξ₀' hσ₀ hX hind hθm hcons hadm hnonneg
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hBm : ∀ (S : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ × ℝ → ℝ → ℝ) (H : ℝ → ℝ → ℝ → ℝ),
      (Measurable fun p : (ℝ × ℝ) × ℝ => S H ξ₀ σ₀ p.1 p.2) →
      ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        S H ξ₀ σ₀ (θt n ω) (X i ω)) P := fun S H hS n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hS.comp_aemeasurable ((hθm n).prodMk (hXm i))).const_mul _
  have hDm : ∀ n, AEMeasurable (fun ω => 2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
      gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n)) P := fun n => by
    have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
    have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (ξ₀, σ₀)) hX aemeasurable_const n
    simp only at h2; fun_prop
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  have hS₁b : IsBoundedInProbability P (fun n ω => gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreXi] using isBoundedInProbability_lin_score hξ₀ hξ0 hσ₀ hX hind 1 0
  have hS₂b : IsBoundedInProbability P (fun n ω => gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreSigma] using isBoundedInProbability_lin_score hξ₀ hξ0 hσ₀ hX hind 0 1
  have hq : gpdInfoQuad ξ₀ σ₀ (t₁ s₀) (t₂ s₀) =
      2 / ((1 + ξ₀) * (1 + 2 * ξ₀)) * t₁ s₀ ^ 2 +
        2 * (1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀))) * t₁ s₀ * t₂ s₀ +
        1 / (σ₀ ^ 2 * (1 + 2 * ξ₀)) * t₂ s₀ ^ 2 := by unfold gpdInfoQuad; ring
  have hc := gpdInfoQuad_pos hξ₀ hσ₀ hne
  rw [hq] at hc
  have hmain := tendstoInMeasure_curve_deviance_of_converge (P := P)
    (A := 2 / ((1 + ξ₀) * (1 + 2 * ξ₀))) (B := 1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀)))
    (C := 1 / (σ₀ ^ 2 * (1 + 2 * ξ₀))) (t₁ := t₁ s₀) (t₂ := t₂ s₀) hc
    (S₁ := fun n ω => gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n)
    (S₂ := fun n ω => gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n)
    (aemeasurable_gpdNormScoreXi hX) (aemeasurable_gpdNormScoreSigma hX)
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiXi₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiSigma₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessSigmaSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiXi₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessSigmaSigma₃))
    hDm hS₁b hS₂b hB₁₁ hB₁₂ hB₂₂ hC₁₁ hC₁₂ hC₂₂ ?_
  · convert hmain using 2 with n
    funext ω; rw [gpdNormScoreXiAll_of_ne hξ0, hq]
  · filter_upwards [hsupp, hcons, hadm, hcurve] with ω hω hc_ω ha ⟨s, hs, hev⟩
    have hsl₁ : Tendsto (fun n => dslope γ₁ s₀ (s n)) atTop (𝓝 (t₁ s₀)) := by
      have := (continuousAt_dslope_same.2 hγ₁.differentiableAt).tendsto.comp hs
      rwa [dslope_same, hγ₁.deriv] at this
    have hsl₂ : Tendsto (fun n => dslope γ₂ s₀ (s n)) atTop (𝓝 (t₂ s₀)) := by
      have := (continuousAt_dslope_same.2 hγ₂.differentiableAt).tendsto.comp hs
      rwa [dslope_same, hγ₂.deriv] at this
    refine ⟨fun n => √(n : ℝ) * (s n - s₀), fun n => dslope γ₁ s₀ (s n), fun n => dslope γ₂ s₀ (s n),
      fun n => t₁ (s n), fun n => t₂ (s n), hsl₁, hsl₂, ht₁.tendsto.comp hs, ht₂.tendsto.comp hs, ?_⟩
    filter_upwards [hc_ω.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀), ha, hev, eventually_gt_atTop 0]
      with n hnb han ⟨hγn, hrn⟩ hn0
    have hθ1_ne : (θt n ω).1 ≠ 0 := by linarith [hnb.1.2]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsq_inv : √(n : ℝ) * (√(n : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)).ne'
    have hsq' : (√(n : ℝ))⁻¹ * n = √(n : ℝ) := by
      have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      field_simp; rw [hsq]
    have hU₁ : (θt n ω).1 - ξ₀ = (s n - s₀) * dslope γ₁ s₀ (s n) := by
      have e := sub_smul_dslope γ₁ s₀ (s n); simp only [smul_eq_mul, hs₁] at e; rw [hγn, e]
    have hU₂ : (θt n ω).2 - σ₀ = (s n - s₀) * dslope γ₂ s₀ (s n) := by
      have e := sub_smul_dslope γ₂ s₀ (s n); simp only [smul_eq_mul, hs₂] at e; rw [hγn, e]
    have hexp := fun i (hi : i ∈ Finset.range n) =>
      gpdScore_sub_eq_segHess_neg hξ₀ hξ₀' hσ₀ hnb (hω i).2 (han i (Finset.mem_range.1 hi))
    have e1 := Finset.sum_congr rfl fun i hi => (hexp i hi).1
    have e2 := Finset.sum_congr rfl fun i hi => (hexp i hi).2
    rw [Finset.sum_sub_distrib] at e1 e2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at e1 e2
    have hrn' : t₁ (s n) * ∑ i ∈ Finset.range n, gpdScoreXi (θt n ω).1 (θt n ω).2 (X i ω) +
        t₂ (s n) * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) = 0 := by
      simpa only [gpdScoreXiAll_of_ne hθ1_ne] using hrn
    constructor
    · simp only [gpdNormScoreXi, gpdNormScoreSigma]
      have hsc1 : (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreXi (θt n ω).1 (θt n ω).2 (X i ω) =
          (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω) +
            √(n : ℝ) * (s n - s₀) * (dslope γ₁ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiXi ξ₀ σ₀ (θt n ω) (X i ω)) +
              dslope γ₂ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ (θt n ω) (X i ω))) := by
        have hsum : ∑ i ∈ Finset.range n, gpdScoreXi (θt n ω).1 (θt n ω).2 (X i ω) =
            ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω) +
              ((θt n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiXi ξ₀ σ₀ (θt n ω) (X i ω) +
              ((θt n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ (θt n ω) (X i ω) := by
          linarith
        rw [hsum, hU₁, hU₂]
        have hsq_eq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ :=
          calc √(n : ℝ) * (n : ℝ)⁻¹ = ((√(n : ℝ))⁻¹ * n) * (n : ℝ)⁻¹ := by rw [hsq']
            _ = (√(n : ℝ))⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn', mul_one]
        have hc1 : ∀ a b : ℝ, √(n : ℝ) * (s n - s₀) * (a * ((n : ℝ)⁻¹ * b)) =
            (√(n : ℝ))⁻¹ * ((s n - s₀) * a * b) := fun a b => by
          calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * ((s n - s₀) * a * b) := by ring
            _ = _ := by rw [hsq_eq]
        rw [mul_add (√(n : ℝ) * (s n - s₀)), hc1, hc1]; ring
      have hsc2 : (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) =
          (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω) +
            √(n : ℝ) * (s n - s₀) * (dslope γ₁ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ (θt n ω) (X i ω)) +
              dslope γ₂ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma ξ₀ σ₀ (θt n ω) (X i ω))) := by
        have hsum : ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) =
            ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω) +
              ((θt n ω).1 - ξ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ (θt n ω) (X i ω) +
              ((θt n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma ξ₀ σ₀ (θt n ω) (X i ω) := by
          linarith
        rw [hsum, hU₁, hU₂]
        have hsq_eq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ :=
          calc √(n : ℝ) * (n : ℝ)⁻¹ = ((√(n : ℝ))⁻¹ * n) * (n : ℝ)⁻¹ := by rw [hsq']
            _ = (√(n : ℝ))⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn', mul_one]
        have hc1 : ∀ a b : ℝ, √(n : ℝ) * (s n - s₀) * (a * ((n : ℝ)⁻¹ * b)) =
            (√(n : ℝ))⁻¹ * ((s n - s₀) * a * b) := fun a b => by
          calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * ((s n - s₀) * a * b) := by ring
            _ = _ := by rw [hsq_eq]
        rw [mul_add (√(n : ℝ) * (s n - s₀)), hc1, hc1]; ring
      rw [← hsc1, ← hsc2]
      linear_combination (√(n : ℝ))⁻¹ * hrn'
    · simp only [gpdLogLikN, gpdNormScoreXi, gpdNormScoreSigma]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      have hterm := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
        two_mul_log_gpdDensity_sub_eq_segHessW_neg hξ₀' hσ₀ hnb (hω i).1.le (hω i).2
          (han i (Finset.mem_range.1 hi))
      rw [hterm]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hU₁, hU₂]
      have h1 : ∀ a c : ℝ, √(n : ℝ) * (s n - s₀) * (a * ((√(n : ℝ))⁻¹ * c)) = (s n - s₀) * a * c := fun a c => by
        calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * ((s n - s₀) * a * c) := by ring
          _ = _ := by rw [hsq_inv, one_mul]
      have h2 : ∀ a b c : ℝ, (√(n : ℝ) * (s n - s₀)) ^ 2 * (a * b * ((n : ℝ)⁻¹ * c)) =
          ((s n - s₀) * a) * ((s n - s₀) * b) * c := fun a b c => by
        calc _ = ((√(n : ℝ)) ^ 2 * (n : ℝ)⁻¹) * (((s n - s₀) * a) * ((s n - s₀) * b) * c) := by ring
          _ = _ := by rw [hsq, mul_inv_cancel₀ hn', one_mul]
      have p1 := h1 (dslope γ₁ s₀ (s n)) (∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω))
      have p2 := h1 (dslope γ₂ s₀ (s n)) (∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω))
      have q1 := h2 (dslope γ₁ s₀ (s n)) (dslope γ₁ s₀ (s n)) (∑ i ∈ Finset.range n, segHessW gpdHessXiXi ξ₀ σ₀ (θt n ω) (X i ω))
      have q2 := h2 (dslope γ₁ s₀ (s n)) (dslope γ₂ s₀ (s n)) (∑ i ∈ Finset.range n, segHessW gpdHessXiSigma ξ₀ σ₀ (θt n ω) (X i ω))
      have q3 := h2 (dslope γ₂ s₀ (s n)) (dslope γ₂ s₀ (s n)) (∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma ξ₀ σ₀ (θt n ω) (X i ω))
      linarith

/-- Full-parameter deviance minus `Sₙᵀ I(0, σ₀)⁻¹ Sₙ` converges to `0` in probability at `ξ₀ = 0`. -/
theorem tendstoInMeasure_gpdFullDeviance_sub_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (0, σ₀)))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω)
    (hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      0 ≤ 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
        gpdLogLikN 0 σ₀ (fun i => X i ω) n))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXiAll (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0) :
    TendstoInMeasure P (fun n ω =>
      2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN 0 σ₀ (fun i => X i ω) n) -
        gpdInfoInvQuad 0 σ₀ (gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n)
          (gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n)) atTop (fun _ => 0) := by
  have hξ : (-1 / 2 : ℝ) < 0 := by norm_num
  have hd : 0 < (2 : ℝ) * (1 / σ₀ ^ 2) - (1 / σ₀) ^ 2 := by
    have : (2 : ℝ) * (1 / σ₀ ^ 2) - (1 / σ₀) ^ 2 = 1 / σ₀ ^ 2 := by field_simp [hσ₀.ne']; ring
    rw [this]; positivity
  obtain ⟨hB₁₁, hB₁₂, hB₂₂, hC₁₁, hC₁₂, hC₂₂⟩ :=
    tendstoInMeasure_segHess_and_segHessW_zero hσ₀ hX hind hθm hcons hadm hnonneg
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hS₁m : ∀ n, AEMeasurable (fun ω => gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n) P := fun n => by
    have h1 : Measurable (expScoreXi σ₀) := by unfold expScoreXi; fun_prop
    refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul _
    simp only [gpdScoreXiAll_zero]
    exact h1.comp_aemeasurable (hXm i)
  have hBm : ∀ (S : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ × ℝ → ℝ → ℝ) (H : ℝ → ℝ → ℝ → ℝ),
      (Measurable fun p : (ℝ × ℝ) × ℝ => S H 0 σ₀ p.1 p.2) →
      ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        S H 0 σ₀ (θh n ω) (X i ω)) P := fun S H hS n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hS.comp_aemeasurable ((hθm n).prodMk (hXm i))).const_mul _
  have hDm : ∀ n, AEMeasurable (fun ω => 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
      gpdLogLikN 0 σ₀ (fun i => X i ω) n)) P := fun n => by
    have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
    have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (0, σ₀)) hX aemeasurable_const n
    simp only at h2; fun_prop
  have hpos := ae_forall_pos_of_gpd (ξ := 0) hσ₀ hX
  have hS₁b : IsBoundedInProbability P (fun n ω => gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreXiAll_zero] using isBoundedInProbability_lin_score_zero hσ₀ hX hind 1 0
  have hS₂b : IsBoundedInProbability P (fun n ω => gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreSigma, gpdScoreSigma_zero] using
      isBoundedInProbability_lin_score_zero hσ₀ hX hind 0 1
  have hmain := tendstoInMeasure_full_deviance_of_converge (P := P)
    (A := 2) (B := 1 / σ₀) (C := 1 / σ₀ ^ 2) hd
    (S₁ := fun n ω => gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n)
    (S₂ := fun n ω => gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n)
    (T₁ := fun n ω => √(n : ℝ) * ((θh n ω).1 - 0))
    (T₂ := fun n ω => √(n : ℝ) * ((θh n ω).2 - σ₀))
    hS₁m (aemeasurable_gpdNormScoreSigma hX)
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiXiAll₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiSigma₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessSigmaSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiXiAll₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessSigmaSigma₃))
    hDm hS₁b hS₂b hB₁₁ hB₁₂ hB₂₂ hC₁₁ hC₁₂ hC₂₂ ?_ ?_
  · convert hmain using 2 with n
    funext ω; rw [gpdInfoInvQuad]; field_simp [hσ₀.ne']; ring
  · filter_upwards [hcons, hadm, hroot] with ω hc ha hr
    filter_upwards [hc.eventually (gpdNbhdZero_mem_nhds hσ₀), ha, hr, eventually_gt_atTop 0]
      with n hnb han hrn hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ))⁻¹ * n = √(n : ℝ) := by
      have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      field_simp; rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    have hexp := fun i (hi : i ∈ Finset.range n) =>
      gpdScoreAll_sub_eq_segHess hσ₀ hnb (han i (Finset.mem_range.1 hi))
    have e1 := Finset.sum_congr rfl fun i hi => (hexp i hi).1
    have e2 := Finset.sum_congr rfl fun i hi => (hexp i hi).2
    rw [Finset.sum_sub_distrib, hrn.1, zero_sub] at e1
    rw [Finset.sum_sub_distrib, hrn.2, zero_sub] at e2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at e1 e2
    simp only [gpdNormScoreXiAll_zero, gpdNormScoreSigma, gpdScoreSigma_zero]
    have hsq_eq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ :=
      calc √(n : ℝ) * (n : ℝ)⁻¹ = ((√(n : ℝ))⁻¹ * n) * (n : ℝ)⁻¹ := by rw [hsq]
        _ = (√(n : ℝ))⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn', mul_one]
    have hcancel : ∀ x : ℝ, (n : ℝ)⁻¹ * x * (√(n : ℝ) * ((θh n ω).1 - 0)) =
        (√(n : ℝ))⁻¹ * (((θh n ω).1 - 0) * x) := fun x => by
      calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * (((θh n ω).1 - 0) * x) := by ring
        _ = _ := by rw [hsq_eq]
    have hcancel2 : ∀ x : ℝ, (n : ℝ)⁻¹ * x * (√(n : ℝ) * ((θh n ω).2 - σ₀)) =
        (√(n : ℝ))⁻¹ * (((θh n ω).2 - σ₀) * x) := fun x => by
      calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * (((θh n ω).2 - σ₀) * x) := by ring
        _ = _ := by rw [hsq_eq]
    constructor
    · rw [show ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω) =
        -(((θh n ω).1 - 0) * ∑ i ∈ Finset.range n, segHess gpdHessXiXiAll 0 σ₀ (θh n ω) (X i ω) +
          ((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma 0 σ₀ (θh n ω) (X i ω))
        by linarith]
      rw [hcancel, hcancel2]; ring
    · rw [show ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω) =
        -(((θh n ω).1 - 0) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma 0 σ₀ (θh n ω) (X i ω) +
          ((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma 0 σ₀ (θh n ω) (X i ω))
        by linarith]
      rw [hcancel, hcancel2]; ring
  · filter_upwards [hpos, hcons, hadm] with ω hω hc ha
    filter_upwards [hc.eventually (gpdNbhdZero_mem_nhds hσ₀), ha, eventually_gt_atTop 0]
      with n hnb han hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsq_inv : √(n : ℝ) * (√(n : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)).ne'
    simp only [gpdLogLikN, gpdNormScoreXiAll_zero, gpdNormScoreSigma, gpdScoreSigma_zero]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have hterm := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
      two_mul_log_gpdDensity_sub_eq_segHessW_zero hσ₀ hnb (hω i).le (han i (Finset.mem_range.1 hi))
    rw [hterm]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : √(n : ℝ) * ((θh n ω).1 - 0) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω)) =
        ((θh n ω).1 - 0) * ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω) := by
      calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θh n ω).1 - 0) * ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω)) := by ring
        _ = _ := by rw [hsq_inv, one_mul]
    have h2 : √(n : ℝ) * ((θh n ω).2 - σ₀) * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω)) =
        ((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω) := by
      calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * (((θh n ω).2 - σ₀) * ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω)) := by ring
        _ = _ := by rw [hsq_inv, one_mul]
    have h3 : ∀ (a b c : ℝ), (√(n : ℝ) * a) * (√(n : ℝ) * b) * ((n : ℝ)⁻¹ * c) = a * b * c := fun a b c => by
      calc _ = ((√(n : ℝ)) ^ 2 * (n : ℝ)⁻¹) * (a * b * c) := by ring
        _ = a * b * c := by rw [hsq, mul_inv_cancel₀ hn', one_mul]
    rw [h1, h2]
    have q1 := h3 ((θh n ω).1 - 0) ((θh n ω).1 - 0) (∑ i ∈ Finset.range n, segHessW gpdHessXiXiAll 0 σ₀ (θh n ω) (X i ω))
    have q2 := h3 ((θh n ω).1 - 0) ((θh n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessXiSigma 0 σ₀ (θh n ω) (X i ω))
    have q3 := h3 ((θh n ω).2 - σ₀) ((θh n ω).2 - σ₀) (∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma 0 σ₀ (θh n ω) (X i ω))
    linarith

/-- Curve-restricted deviance minus `(t₀ · Sₙ)² / (t₀ᵀ I t₀)` converges to `0` in probability at
`ξ₀ = 0`. -/
theorem tendstoInMeasure_gpdCurveDeviance_sub_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P)
    {γ₁ γ₂ t₁ t₂ : ℝ → ℝ} {s₀ : ℝ} (hγ₁ : HasDerivAt γ₁ (t₁ s₀) s₀) (hγ₂ : HasDerivAt γ₂ (t₂ s₀) s₀)
    (ht₁ : ContinuousAt t₁ s₀) (ht₂ : ContinuousAt t₂ s₀) (hs₁ : γ₁ s₀ = 0) (hs₂ : γ₂ s₀ = σ₀)
    (hne : t₁ s₀ ≠ 0 ∨ t₂ s₀ ≠ 0)
    {θt : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θt n) P)
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θt n ω).2 + (θt n ω).1 * X i ω)
    (hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      0 ≤ 2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
        gpdLogLikN 0 σ₀ (fun i => X i ω) n))
    (hcurve : ∀ᵐ ω ∂P, ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 s₀) ∧ ∀ᶠ n in atTop,
      θt n ω = (γ₁ (s n), γ₂ (s n)) ∧
      t₁ (s n) * ∑ i ∈ Finset.range n, gpdScoreXiAll (θt n ω).1 (θt n ω).2 (X i ω) +
        t₂ (s n) * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) = 0) :
    TendstoInMeasure P (fun n ω =>
      2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
          gpdLogLikN 0 σ₀ (fun i => X i ω) n) -
        (t₁ s₀ * gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n +
          t₂ s₀ * gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n) ^ 2 /
            gpdInfoQuad 0 σ₀ (t₁ s₀) (t₂ s₀)) atTop (fun _ => 0) := by
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θt n ω) atTop (𝓝 (0, σ₀)) := by
    filter_upwards [hcurve] with ω ⟨s, hs, hev⟩
    have h1 : Tendsto (fun n => (γ₁ (s n), γ₂ (s n))) atTop (𝓝 (0, σ₀)) := by
      rw [← hs₁, ← hs₂]
      exact (hγ₁.continuousAt.tendsto.comp hs).prodMk_nhds (hγ₂.continuousAt.tendsto.comp hs)
    exact h1.congr' (hev.mono fun n hn => hn.1.symm)
  obtain ⟨hB₁₁, hB₁₂, hB₂₂, hC₁₁, hC₁₂, hC₂₂⟩ :=
    tendstoInMeasure_segHess_and_segHessW_zero hσ₀ hX hind hθm hcons hadm hnonneg
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hS₁m : ∀ n, AEMeasurable (fun ω => gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n) P := fun n => by
    have h1 : Measurable (expScoreXi σ₀) := by unfold expScoreXi; fun_prop
    refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul _
    simp only [gpdScoreXiAll_zero]
    exact h1.comp_aemeasurable (hXm i)
  have hBm : ∀ (S : (ℝ → ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ × ℝ → ℝ → ℝ) (H : ℝ → ℝ → ℝ → ℝ),
      (Measurable fun p : (ℝ × ℝ) × ℝ => S H 0 σ₀ p.1 p.2) →
      ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        S H 0 σ₀ (θt n ω) (X i ω)) P := fun S H hS n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hS.comp_aemeasurable ((hθm n).prodMk (hXm i))).const_mul _
  have hDm : ∀ n, AEMeasurable (fun ω => 2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
      gpdLogLikN 0 σ₀ (fun i => X i ω) n)) P := fun n => by
    have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
    have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (0, σ₀)) hX aemeasurable_const n
    simp only at h2; fun_prop
  have hpos := ae_forall_pos_of_gpd (ξ := 0) hσ₀ hX
  have hS₁b : IsBoundedInProbability P (fun n ω => gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreXiAll_zero] using isBoundedInProbability_lin_score_zero hσ₀ hX hind 1 0
  have hS₂b : IsBoundedInProbability P (fun n ω => gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n) := by
    simpa [gpdNormScoreSigma, gpdScoreSigma_zero] using
      isBoundedInProbability_lin_score_zero hσ₀ hX hind 0 1
  have hq : gpdInfoQuad 0 σ₀ (t₁ s₀) (t₂ s₀) =
      2 * t₁ s₀ ^ 2 + 2 * (1 / σ₀) * t₁ s₀ * t₂ s₀ + (1 / σ₀ ^ 2) * t₂ s₀ ^ 2 := by
    unfold gpdInfoQuad; ring
  have hc := gpdInfoQuad_pos (ξ := 0) (by norm_num) hσ₀ hne
  rw [hq] at hc
  have hmain := tendstoInMeasure_curve_deviance_of_converge (P := P)
    (A := 2) (B := 1 / σ₀) (C := 1 / σ₀ ^ 2) (t₁ := t₁ s₀) (t₂ := t₂ s₀) hc
    (S₁ := fun n ω => gpdNormScoreXiAll 0 σ₀ (fun i => X i ω) n)
    (S₂ := fun n ω => gpdNormScoreSigma 0 σ₀ (fun i => X i ω) n)
    hS₁m (aemeasurable_gpdNormScoreSigma hX)
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiXiAll₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessXiSigma₃))
    (hBm segHess _ (measurable_segHess measurable_gpdHessSigmaSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiXiAll₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessXiSigma₃))
    (hBm segHessW _ (measurable_segHessW measurable_gpdHessSigmaSigma₃))
    hDm hS₁b hS₂b hB₁₁ hB₁₂ hB₂₂ hC₁₁ hC₁₂ hC₂₂ ?_
  · convert hmain using 2 with n
    funext ω; rw [hq]
  · filter_upwards [hpos, hcons, hadm, hcurve] with ω hω hc_ω ha ⟨s, hs, hev⟩
    have hsl₁ : Tendsto (fun n => dslope γ₁ s₀ (s n)) atTop (𝓝 (t₁ s₀)) := by
      have := (continuousAt_dslope_same.2 hγ₁.differentiableAt).tendsto.comp hs
      rwa [dslope_same, hγ₁.deriv] at this
    have hsl₂ : Tendsto (fun n => dslope γ₂ s₀ (s n)) atTop (𝓝 (t₂ s₀)) := by
      have := (continuousAt_dslope_same.2 hγ₂.differentiableAt).tendsto.comp hs
      rwa [dslope_same, hγ₂.deriv] at this
    refine ⟨fun n => √(n : ℝ) * (s n - s₀), fun n => dslope γ₁ s₀ (s n), fun n => dslope γ₂ s₀ (s n),
      fun n => t₁ (s n), fun n => t₂ (s n), hsl₁, hsl₂, ht₁.tendsto.comp hs, ht₂.tendsto.comp hs, ?_⟩
    filter_upwards [hc_ω.eventually (gpdNbhdZero_mem_nhds hσ₀), ha, hev, eventually_gt_atTop 0]
      with n hnb han ⟨hγn, hrn⟩ hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsq_inv : √(n : ℝ) * (√(n : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)).ne'
    have hsq' : (√(n : ℝ))⁻¹ * n = √(n : ℝ) := by
      have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      field_simp; rw [hsq]
    have hU₁ : (θt n ω).1 - 0 = (s n - s₀) * dslope γ₁ s₀ (s n) := by
      have e := sub_smul_dslope γ₁ s₀ (s n); simp only [smul_eq_mul, hs₁] at e; rw [hγn, e]
    have hU₂ : (θt n ω).2 - σ₀ = (s n - s₀) * dslope γ₂ s₀ (s n) := by
      have e := sub_smul_dslope γ₂ s₀ (s n); simp only [smul_eq_mul, hs₂] at e; rw [hγn, e]
    have hexp := fun i (hi : i ∈ Finset.range n) =>
      gpdScoreAll_sub_eq_segHess hσ₀ hnb (han i (Finset.mem_range.1 hi))
    have e1 := Finset.sum_congr rfl fun i hi => (hexp i hi).1
    have e2 := Finset.sum_congr rfl fun i hi => (hexp i hi).2
    rw [Finset.sum_sub_distrib] at e1 e2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at e1 e2
    constructor
    · simp only [gpdNormScoreXiAll_zero, gpdNormScoreSigma, gpdScoreSigma_zero]
      have hsc1 : (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreXiAll (θt n ω).1 (θt n ω).2 (X i ω) =
          (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω) +
            √(n : ℝ) * (s n - s₀) * (dslope γ₁ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiXiAll 0 σ₀ (θt n ω) (X i ω)) +
              dslope γ₂ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma 0 σ₀ (θt n ω) (X i ω))) := by
        have hsum : ∑ i ∈ Finset.range n, gpdScoreXiAll (θt n ω).1 (θt n ω).2 (X i ω) =
            ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω) +
              ((θt n ω).1 - 0) * ∑ i ∈ Finset.range n, segHess gpdHessXiXiAll 0 σ₀ (θt n ω) (X i ω) +
              ((θt n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma 0 σ₀ (θt n ω) (X i ω) := by
          linarith
        rw [hsum, hU₁, hU₂]
        have hsq_eq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ :=
          calc √(n : ℝ) * (n : ℝ)⁻¹ = ((√(n : ℝ))⁻¹ * n) * (n : ℝ)⁻¹ := by rw [hsq']
            _ = (√(n : ℝ))⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn', mul_one]
        have hc1 : ∀ a b : ℝ, √(n : ℝ) * (s n - s₀) * (a * ((n : ℝ)⁻¹ * b)) =
            (√(n : ℝ))⁻¹ * ((s n - s₀) * a * b) := fun a b => by
          calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * ((s n - s₀) * a * b) := by ring
            _ = _ := by rw [hsq_eq]
        rw [mul_add (√(n : ℝ) * (s n - s₀)), hc1, hc1]; ring
      have hsc2 : (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) =
          (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω) +
            √(n : ℝ) * (s n - s₀) * (dslope γ₁ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma 0 σ₀ (θt n ω) (X i ω)) +
              dslope γ₂ s₀ (s n) *
              ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma 0 σ₀ (θt n ω) (X i ω))) := by
        have hsum : ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) =
            ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω) +
              ((θt n ω).1 - 0) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma 0 σ₀ (θt n ω) (X i ω) +
              ((θt n ω).2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma 0 σ₀ (θt n ω) (X i ω) := by
          linarith
        rw [hsum, hU₁, hU₂]
        have hsq_eq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ :=
          calc √(n : ℝ) * (n : ℝ)⁻¹ = ((√(n : ℝ))⁻¹ * n) * (n : ℝ)⁻¹ := by rw [hsq']
            _ = (√(n : ℝ))⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn', mul_one]
        have hc1 : ∀ a b : ℝ, √(n : ℝ) * (s n - s₀) * (a * ((n : ℝ)⁻¹ * b)) =
            (√(n : ℝ))⁻¹ * ((s n - s₀) * a * b) := fun a b => by
          calc _ = (√(n : ℝ) * (n : ℝ)⁻¹) * ((s n - s₀) * a * b) := by ring
            _ = _ := by rw [hsq_eq]
        rw [mul_add (√(n : ℝ) * (s n - s₀)), hc1, hc1]; ring
      rw [← hsc1, ← hsc2]
      linear_combination (√(n : ℝ))⁻¹ * hrn
    · simp only [gpdLogLikN, gpdNormScoreXiAll_zero, gpdNormScoreSigma, gpdScoreSigma_zero]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      have hterm := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
        two_mul_log_gpdDensity_sub_eq_segHessW_zero hσ₀ hnb (hω i).le (han i (Finset.mem_range.1 hi))
      rw [hterm]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hU₁, hU₂]
      have h1 : ∀ a c : ℝ, √(n : ℝ) * (s n - s₀) * (a * ((√(n : ℝ))⁻¹ * c)) = (s n - s₀) * a * c := fun a c => by
        calc _ = (√(n : ℝ) * (√(n : ℝ))⁻¹) * ((s n - s₀) * a * c) := by ring
          _ = _ := by rw [hsq_inv, one_mul]
      have h2 : ∀ a b c : ℝ, (√(n : ℝ) * (s n - s₀)) ^ 2 * (a * b * ((n : ℝ)⁻¹ * c)) =
          ((s n - s₀) * a) * ((s n - s₀) * b) * c := fun a b c => by
        calc _ = ((√(n : ℝ)) ^ 2 * (n : ℝ)⁻¹) * (((s n - s₀) * a) * ((s n - s₀) * b) * c) := by ring
          _ = _ := by rw [hsq, mul_inv_cancel₀ hn', one_mul]
      have p1 := h1 (dslope γ₁ s₀ (s n)) (∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω))
      have p2 := h1 (dslope γ₂ s₀ (s n)) (∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω))
      have q1 := h2 (dslope γ₁ s₀ (s n)) (dslope γ₁ s₀ (s n)) (∑ i ∈ Finset.range n, segHessW gpdHessXiXiAll 0 σ₀ (θt n ω) (X i ω))
      have q2 := h2 (dslope γ₁ s₀ (s n)) (dslope γ₂ s₀ (s n)) (∑ i ∈ Finset.range n, segHessW gpdHessXiSigma 0 σ₀ (θt n ω) (X i ω))
      have q3 := h2 (dslope γ₂ s₀ (s n)) (dslope γ₂ s₀ (s n)) (∑ i ∈ Finset.range n, segHessW gpdHessSigmaSigma 0 σ₀ (θt n ω) (X i ω))
      linarith

end DevianceNegZero

/-! ### Wilks' theorem and profile-likelihood coverage for ALL regular shapes `ξ₀ > -1/2` -/

section WilksReg

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {ξ₀ σ₀ : ℝ}

/-- Helper: value of the extended-real deviance for ANY `ξ₀ ∈ ℝ` when observations lie in the
support of `(ξ₀, σ₀)`. -/
private lemma deviance_le_iff_all {K₁ K₂ : Set (ℝ × ℝ)} (hσ₀ : 0 < σ₀)
    (h₁ : (ξ₀, σ₀) ∈ K₁) (h₂ : (ξ₀, σ₀) ∈ K₂) {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, 0 < x i ∧ 0 < σ₀ + ξ₀ * x i)
    {θ₁ θ₂ : ℝ × ℝ}
    (hm₁ : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K₁ θ₁)
    (hm₂ : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K₂ θ₂) (c : ℝ) :
    2 * (gpdLogLikE θ₁.1 θ₁.2 (fun i : Fin n => x i) -
        gpdLogLikE θ₂.1 θ₂.2 (fun i : Fin n => x i)) ≤ (c : EReal) ↔
      2 * (gpdLogLikN θ₁.1 θ₁.2 x n - gpdLogLikN θ₂.1 θ₂.2 x n) ≤ c := by
  have hx₀ : ∀ i : Fin n, 0 ≤ x i ∧ 0 < 1 + ξ₀ * x i / σ₀ := fun i =>
    ⟨(hx i).1.le, by
      have : 1 + ξ₀ * x i / σ₀ = (σ₀ + ξ₀ * x i) / σ₀ := by field_simp [hσ₀.ne']
      rw [this]; exact div_pos (hx i).2 hσ₀⟩
  have h₀ : gpdLogLikE ξ₀ σ₀ (fun i : Fin n => x i) ≠ ⊥ := by
    rw [gpdLogLikE_eq_coe' hx₀]; exact EReal.coe_ne_bot _
  have key : ∀ {K : Set (ℝ × ℝ)} {θ : ℝ × ℝ}, (ξ₀, σ₀) ∈ K →
      IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K θ →
      gpdLogLikE θ.1 θ.2 (fun i : Fin n => x i) = ((gpdLogLikN θ.1 θ.2 x n : ℝ) : EReal) := by
    intro K θ hK hm
    have hle : gpdLogLikE ξ₀ σ₀ (fun i : Fin n => x i) ≤ gpdLogLikE θ.1 θ.2 (fun i : Fin n => x i) :=
      hm hK
    rw [gpdLogLikE_eq_coe_of_ne_bot (ne_bot_of_le_ne_bot h₀ hle), gpdLogLikN,
      Fin.sum_univ_eq_sum_range (fun i => log (gpdDensity θ.1 θ.2 (x i))) n]
  rw [key h₁ hm₁, key h₂ hm₂, ← EReal.coe_sub,
    show (2 : EReal) = ((2 : ℝ) : EReal) from rfl, ← EReal.coe_mul, EReal.coe_le_coe_iff]

/-- Helper: finiteness of `gpdMaxLogLik` for ANY `ξ₀ ∈ ℝ` on support observations. -/
private lemma gpdMaxLogLik_finite_all {K : Set (ℝ × ℝ)} (hσ₀ : 0 < σ₀)
    (h₀K : (ξ₀, σ₀) ∈ K) {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, 0 < x i ∧ 0 < σ₀ + ξ₀ * x i)
    {θ : ℝ × ℝ} (hθ : θ ∈ K)
    (hm : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K θ) :
    gpdMaxLogLik K (fun i : Fin n => x i) ≠ ⊥ ∧ gpdMaxLogLik K (fun i : Fin n => x i) ≠ ⊤ := by
  have hx₀ : ∀ i : Fin n, 0 ≤ x i ∧ 0 < 1 + ξ₀ * x i / σ₀ := fun i =>
    ⟨(hx i).1.le, by
      have : 1 + ξ₀ * x i / σ₀ = (σ₀ + ξ₀ * x i) / σ₀ := by field_simp [hσ₀.ne']
      rw [this]; exact div_pos (hx i).2 hσ₀⟩
  have h₀ : gpdLogLikE ξ₀ σ₀ (fun i : Fin n => x i) ≠ ⊥ := by
    rw [gpdLogLikE_eq_coe' hx₀]; exact EReal.coe_ne_bot _
  have hle : gpdLogLikE ξ₀ σ₀ (fun i : Fin n => x i) ≤ gpdLogLikE θ.1 θ.2 (fun i : Fin n => x i) :=
    hm h₀K
  rw [gpdMaxLogLik_eq_of_isMaxOn hθ hm, gpdLogLikE_eq_coe_of_ne_bot (ne_bot_of_le_ne_bot h₀ hle)]
  exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩

/-- Helper: on support observations, any maximizer `θ` over `K ∋ (ξ₀, σ₀)` satisfies
`0 ≤ 2 (gpdLogLikN θ - gpdLogLikN θ₀)`. -/
private lemma two_mul_gpdLogLikN_sub_nonneg_of_isMaxOn {K : Set (ℝ × ℝ)} (hσ₀ : 0 < σ₀)
    (h₀K : (ξ₀, σ₀) ∈ K) {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, 0 < x i ∧ 0 < σ₀ + ξ₀ * x i)
    {θ : ℝ × ℝ}
    (hm : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K θ) :
    0 ≤ 2 * (gpdLogLikN θ.1 θ.2 x n - gpdLogLikN ξ₀ σ₀ x n) := by
  have hx₀ : ∀ i : Fin n, 0 ≤ x i ∧ 0 < 1 + ξ₀ * x i / σ₀ := fun i =>
    ⟨(hx i).1.le, by
      have : 1 + ξ₀ * x i / σ₀ = (σ₀ + ξ₀ * x i) / σ₀ := by field_simp [hσ₀.ne']
      rw [this]; exact div_pos (hx i).2 hσ₀⟩
  have h₀ : gpdLogLikE ξ₀ σ₀ (fun i : Fin n => x i) = ((gpdLogLikN ξ₀ σ₀ x n : ℝ) : EReal) := by
    rw [gpdLogLikE_eq_coe' hx₀, gpdLogLikN,
      Fin.sum_univ_eq_sum_range (fun i => log (gpdDensity ξ₀ σ₀ (x i))) n]
  have hle := hm h₀K
  simp only [mem_ofPred_eq] at hle
  have hθ : gpdLogLikE θ.1 θ.2 (fun i : Fin n => x i) = ((gpdLogLikN θ.1 θ.2 x n : ℝ) : EReal) := by
    rw [gpdLogLikE_eq_coe_of_ne_bot (ne_bot_of_le_ne_bot (by rw [h₀]; exact EReal.coe_ne_bot _) hle),
      gpdLogLikN, Fin.sum_univ_eq_sum_range (fun i => log (gpdDensity θ.1 θ.2 (x i))) n]
  rw [h₀, hθ, EReal.coe_le_coe_iff] at hle
  linarith

/-- **Wilks' theorem for the GPD, full parameter, ALL regular shapes `ξ₀ > -1/2`** ([Coles, §2.6.5];
[Smith 1985]; [van der Vaart, §16]). Covers `-1/2 < ξ₀ < 0`, `ξ₀ = 0`, and `ξ₀ > 0` uniformly:

  `D(θ₀) = 2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₂`. -/
theorem tendstoInDistribution_gpdDeviance_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 2) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n)) atTop Z (fun _ => P) P' := by
  rcases lt_trichotomy ξ₀ 0 with hneg | rfl | hpos
  · have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)) := by
      filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
      refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
        (Eventually.of_forall fun n => ?_)
      have := hmax n ω (interior_subset hθ₀); simp only [mem_ofPred_eq] at this; simpa using this
    have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
      ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
    have hadmAll : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
        0 ≤ X i ω ∧ 0 < 1 + (θh n ω).1 * X i ω / (θh n ω).2 :=
      hsupp.mono fun ω hω n => admissible_of_isMaxOn (interior_subset hθ₀) hσ₀ (fun i => hω i) (hmax n ω)
    have hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω :=
      hadmAll.mono fun ω hω => Eventually.of_forall fun n i hi => by
        have h := (hω n ⟨i, hi⟩).2; have hσ := (hKS _ (hθK n ω)).2
        have e : 1 + (θh n ω).1 * X i ω / (θh n ω).2 =
            ((θh n ω).2 + (θh n ω).1 * X i ω) / (θh n ω).2 := by field_simp
        rw [e] at h; exact (div_pos_iff_of_pos_right hσ).1 h
    have hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        0 ≤ 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) :=
      hsupp.mono fun ω hω => Eventually.of_forall fun n =>
        two_mul_gpdLogLikN_sub_nonneg_of_isMaxOn hσ₀ (interior_subset hθ₀) hω (hmax n ω)
    have hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
        ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0 := by
      filter_upwards [hadmAll, hcons] with ω hω hc
      filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
        hc.eventually (gpdNbhdNeg_mem_nhds hneg hσ₀)] with n h1 h2
      have hσ := (hKS _ (hθK n ω)).2
      have := score_eq_zero_of_isMaxOn' (x := fun i : Fin n => X i ω) h1 (by linarith [h2.1.2]) hσ
        (hω n) (hmax n ω)
      rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω)) n,
        Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n] at this
      exact this
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z
      (tendstoInDistribution_gpdInfoInvQuad_reg hξ₀ hσ₀ hX hind hZ)
      (tendstoInMeasure_gpdFullDeviance_sub_neg hξ₀ hneg hσ₀ hX hind hθm hcons hadm hnonneg hroot)
      fun n => by
        have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
        have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (ξ₀, σ₀)) hX aemeasurable_const n
        simp only at h2; fun_prop
  · have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (0, σ₀)) := by
      filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
      refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
        (Eventually.of_forall fun n => ?_)
      have := hmax n ω (interior_subset hθ₀); simp only [mem_ofPred_eq] at this; simpa using this
    have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + (0 : ℝ) * X i ω := ae_all_iff.2 fun i =>
      ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure (ξ := 0) hσ₀)
    have hadmAll : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
        0 ≤ X i ω ∧ 0 < 1 + (θh n ω).1 * X i ω / (θh n ω).2 :=
      hsupp.mono fun ω hω n => admissible_of_isMaxOn (interior_subset hθ₀) hσ₀ (fun i => hω i) (hmax n ω)
    have hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω :=
      hadmAll.mono fun ω hω => Eventually.of_forall fun n i hi => by
        have h := (hω n ⟨i, hi⟩).2; have hσ := (hKS _ (hθK n ω)).2
        have e : 1 + (θh n ω).1 * X i ω / (θh n ω).2 =
            ((θh n ω).2 + (θh n ω).1 * X i ω) / (θh n ω).2 := by field_simp
        rw [e] at h; exact (div_pos_iff_of_pos_right hσ).1 h
    have hnonneg : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        0 ≤ 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN 0 σ₀ (fun i => X i ω) n) :=
      hsupp.mono fun ω hω => Eventually.of_forall fun n =>
        two_mul_gpdLogLikN_sub_nonneg_of_isMaxOn hσ₀ (interior_subset hθ₀) hω (hmax n ω)
    have hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        ∑ i ∈ Finset.range n, gpdScoreXiAll (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
        ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0 := by
      filter_upwards [hadmAll, hcons] with ω hω hc
      filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀)] with n h1
      have hσ := (hKS _ (hθK n ω)).2
      have := scoreAll_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) h1 hσ (hω n) (hmax n ω)
      rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXiAll (θh n ω).1 (θh n ω).2 (X i ω)) n,
        Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n] at this
      exact this
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z
      (tendstoInDistribution_gpdInfoInvQuad_reg hξ₀ hσ₀ hX hind hZ)
      (tendstoInMeasure_gpdFullDeviance_sub_zero hσ₀ hX hind hθm hcons hadm hnonneg hroot)
      fun n => by
        have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
        have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (0, σ₀)) hX aemeasurable_const n
        simp only at h2; fun_prop
  · exact tendstoInDistribution_gpdDeviance hK hKS hθ₀ hpos hσ₀ hX hind hθm hθK hmax hZ

/-- **Wilks' theorem for the profile likelihood of the GPD, ALL regular shapes `ξ₀ > -1/2`**
([Coles, §2.6.6]; [Smith 1985]; [van der Vaart, §16]):

  `D_p(g θ₀) = 2 (ℓₙ(θ̂ₙ) - ℓₙ(θ̃ₙ)) ⇒ χ²₁`. -/
theorem tendstoInDistribution_gpdProfileDeviance_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) {s₀ : ℝ} {φ : ℝ × ℝ → ℝ} {γ₁ γ₂ t₁ t₂ : ℝ → ℝ}
    (hchart : IsGPDProfileChart g ξ₀ σ₀ s₀ φ γ₁ γ₂ t₁ t₂)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {θt : ℕ → Ω → ℝ × ℝ} (hθtm : ∀ n, AEMeasurable (θt n) P)
    (hθtK : ∀ n ω, θt n ω ∈ K ∩ g ⁻¹' {g (ξ₀, σ₀)})
    (hmaxt : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω))
      (K ∩ g ⁻¹' {g (ξ₀, σ₀)}) (θt n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n)) atTop Z (fun _ => P) P' := by
  rcases lt_trichotomy ξ₀ 0 with hneg | rfl | hpos
  · -- Case `-1/2 < ξ₀ < 0`
    set K' := K ∩ g ⁻¹' {g (ξ₀, σ₀)}
    have hK'c : IsCompact K' := hK.of_isClosed_subset
      (hg.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton) inter_subset_left
    have hK'S : ∀ p ∈ K', -1 < p.1 ∧ 0 < p.2 := fun p hp => hKS p hp.1
    have hθ₀K' : (ξ₀, σ₀) ∈ K' := ⟨interior_subset hθ₀, rfl⟩
    have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
      ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
    have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)) := by
      filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
      refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
        (Eventually.of_forall fun n => ?_)
      have := hmax n ω (interior_subset hθ₀); simp only [mem_ofPred_eq] at this; simpa using this
    have hconst : ∀ᵐ ω ∂P, Tendsto (fun n => θt n ω) atTop (𝓝 (ξ₀, σ₀)) := by
      filter_upwards [ae_tendsto_gpdMLE' (θ₀ := (ξ₀, σ₀)) hK'c hK'S hθ₀K' hX hind] with ω hω
      refine hω (fun n => θt n ω) (fun _ => 0) (fun n => hθtK n ω) tendsto_const_nhds
        (Eventually.of_forall fun n => ?_)
      have := hmaxt n ω hθ₀K'; simp only [mem_ofPred_eq] at this; simpa using this
    have hadmAll_h : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
        0 ≤ X i ω ∧ 0 < 1 + (θh n ω).1 * X i ω / (θh n ω).2 :=
      hsupp.mono fun ω hω n => admissible_of_isMaxOn (interior_subset hθ₀) hσ₀ (fun i => hω i) (hmax n ω)
    have hadmAll_t : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
        0 ≤ X i ω ∧ 0 < 1 + (θt n ω).1 * X i ω / (θt n ω).2 :=
      hsupp.mono fun ω hω n => admissible_of_isMaxOn hθ₀K' hσ₀ (fun i => hω i) (hmaxt n ω)
    have hadm_h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω :=
      hadmAll_h.mono fun ω hω => Eventually.of_forall fun n i hi => by
        have h := (hω n ⟨i, hi⟩).2; have hσ := (hKS _ (hθK n ω)).2
        have e : 1 + (θh n ω).1 * X i ω / (θh n ω).2 =
            ((θh n ω).2 + (θh n ω).1 * X i ω) / (θh n ω).2 := by field_simp
        rw [e] at h; exact (div_pos_iff_of_pos_right hσ).1 h
    have hadm_t : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θt n ω).2 + (θt n ω).1 * X i ω :=
      hadmAll_t.mono fun ω hω => Eventually.of_forall fun n i hi => by
        have h := (hω n ⟨i, hi⟩).2; have hσ := (hK'S _ (hθtK n ω)).2
        have e : 1 + (θt n ω).1 * X i ω / (θt n ω).2 =
            ((θt n ω).2 + (θt n ω).1 * X i ω) / (θt n ω).2 := by field_simp
        rw [e] at h; exact (div_pos_iff_of_pos_right hσ).1 h
    have hnn_h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        0 ≤ 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) :=
      hsupp.mono fun ω hω => Eventually.of_forall fun n =>
        two_mul_gpdLogLikN_sub_nonneg_of_isMaxOn hσ₀ (interior_subset hθ₀) hω (hmax n ω)
    have hnn_t : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        0 ≤ 2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) :=
      hsupp.mono fun ω hω => Eventually.of_forall fun n =>
        two_mul_gpdLogLikN_sub_nonneg_of_isMaxOn hσ₀ hθ₀K' hω (hmaxt n ω)
    have hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
        ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0 := by
      filter_upwards [hadmAll_h, hcons] with ω hω hc
      filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
        hc.eventually (gpdNbhdNeg_mem_nhds hneg hσ₀)] with n h1 h2
      have hσ := (hKS _ (hθK n ω)).2
      have := score_eq_zero_of_isMaxOn' (x := fun i : Fin n => X i ω) h1 (by linarith [h2.1.2]) hσ
        (hω n) (hmax n ω)
      rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω)) n,
        Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n] at this
      exact this
    have hchart₀ := hchart.curve_chart.self_of_nhds rfl
    rw [hchart.map_true] at hchart₀
    have hs₁ : γ₁ s₀ = ξ₀ := congrArg Prod.fst hchart₀
    have hs₂ : γ₂ s₀ = σ₀ := congrArg Prod.snd hchart₀
    have hcurve : ∀ᵐ ω ∂P, ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 s₀) ∧ ∀ᶠ n in atTop,
        θt n ω = (γ₁ (s n), γ₂ (s n)) ∧
        t₁ (s n) * ∑ i ∈ Finset.range n, gpdScoreXiAll (θt n ω).1 (θt n ω).2 (X i ω) +
          t₂ (s n) * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) = 0 := by
      filter_upwards [hadmAll_t, hconst] with ω hω hc
      have hs : Tendsto (fun n => φ (θt n ω)) atTop (𝓝 s₀) := by
        rw [← hchart.map_true]; exact hchart.continuousAt.tendsto.comp hc
      refine ⟨fun n => φ (θt n ω), hs, ?_⟩
      filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
        hs.eventually hchart.level.eventually_nhds, hs.eventually hchart.hasDerivAt₁.eventually_nhds,
        hs.eventually hchart.hasDerivAt₂.eventually_nhds, hc.eventually hchart.curve_chart]
        with n hint hlev hd₁ hd₂ hch
      have e : θt n ω = (γ₁ (φ (θt n ω)), γ₂ (φ (θt n ω))) := (hch (hθtK n ω).2).symm
      refine ⟨e, ?_⟩
      have d₁ := hd₁.self_of_nhds; have d₂ := hd₂.self_of_nhds
      have hmem : ∀ᶠ s' in 𝓝 (φ (θt n ω)), (γ₁ s', γ₂ s') ∈ K' := by
        have hcont : ContinuousAt (fun s' => (γ₁ s', γ₂ s')) (φ (θt n ω)) :=
          d₁.continuousAt.prodMk d₂.continuousAt
        have hint' : (γ₁ (φ (θt n ω)), γ₂ (φ (θt n ω))) ∈ interior K := by rw [← e]; exact hint
        filter_upwards [hcont.eventually (isOpen_interior.mem_nhds hint'), hlev] with s' h1 h2
        exact ⟨interior_subset h1, h2⟩
      have hmx := hmaxt n ω; rw [e] at hmx
      have hp₂ : 0 < γ₂ (φ (θt n ω)) := by
        have : (θt n ω).2 = γ₂ (φ (θt n ω)) := congrArg Prod.snd e
        rw [← this]; exact (hK'S _ (hθtK n ω)).2
      have hadm' : ∀ i : Fin n, 0 ≤ X i ω ∧ 0 < 1 + γ₁ (φ (θt n ω)) * X i ω / γ₂ (φ (θt n ω)) := by
        intro i
        have := hω n i
        rw [show (θt n ω).1 = γ₁ (φ (θt n ω)) from congrArg Prod.fst e,
          show (θt n ω).2 = γ₂ (φ (θt n ω)) from congrArg Prod.snd e] at this
        exact this
      have := curve_scoreAll_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) d₁ d₂ hp₂ hadm' hmem hmx
      rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXiAll _ _ (X i ω)) n,
        Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma _ _ (X i ω)) n] at this
      rw [show (θt n ω).1 = γ₁ (φ (θt n ω)) from congrArg Prod.fst e,
        show (θt n ω).2 = γ₂ (φ (θt n ω)) from congrArg Prod.snd e]
      exact this
    have h1 := tendstoInMeasure_gpdFullDeviance_sub_neg hξ₀ hneg hσ₀ hX hind hθm hcons hadm_h hnn_h hroot
    have h2 := tendstoInMeasure_gpdCurveDeviance_sub_neg hξ₀ hneg hσ₀ hX hind
      hchart.hasDerivAt₁.self_of_nhds hchart.hasDerivAt₂.self_of_nhds
      hchart.continuousAt₁ hchart.continuousAt₂ hs₁ hs₂ hchart.tangent_ne hθtm hadm_t hnn_t hcurve
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z
      (tendstoInDistribution_gpdInfoInvQuad_sub_reg hξ₀ hσ₀ hX hind hchart.tangent_ne hZ) ?_ fun n => by
        have ha := aemeasurable_gpdLogLikN hX (hθm n) n
        have hb := aemeasurable_gpdLogLikN hX (hθtm n) n; fun_prop
    have := tendstoInMeasure_comp₂ h1 h2 (φ := fun p => p.1 - p.2) continuous_sub.continuousAt
    simp only [sub_zero] at this
    convert this using 2 with n; funext ω; simp only [Pi.sub_apply]; ring
  · -- Case `ξ₀ = 0`
    set K' := K ∩ g ⁻¹' {g (0, σ₀)}
    have hK'c : IsCompact K' := hK.of_isClosed_subset
      (hg.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton) inter_subset_left
    have hK'S : ∀ p ∈ K', -1 < p.1 ∧ 0 < p.2 := fun p hp => hKS p hp.1
    have hθ₀K' : (0, σ₀) ∈ K' := ⟨interior_subset hθ₀, rfl⟩
    have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + (0 : ℝ) * X i ω := ae_all_iff.2 fun i =>
      ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure (ξ := 0) hσ₀)
    have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (0, σ₀)) := by
      filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
      refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
        (Eventually.of_forall fun n => ?_)
      have := hmax n ω (interior_subset hθ₀); simp only [mem_ofPred_eq] at this; simpa using this
    have hconst : ∀ᵐ ω ∂P, Tendsto (fun n => θt n ω) atTop (𝓝 (0, σ₀)) := by
      filter_upwards [ae_tendsto_gpdMLE' (θ₀ := (0, σ₀)) hK'c hK'S hθ₀K' hX hind] with ω hω
      refine hω (fun n => θt n ω) (fun _ => 0) (fun n => hθtK n ω) tendsto_const_nhds
        (Eventually.of_forall fun n => ?_)
      have := hmaxt n ω hθ₀K'; simp only [mem_ofPred_eq] at this; simpa using this
    have hadmAll_h : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
        0 ≤ X i ω ∧ 0 < 1 + (θh n ω).1 * X i ω / (θh n ω).2 :=
      hsupp.mono fun ω hω n => admissible_of_isMaxOn (interior_subset hθ₀) hσ₀ (fun i => hω i) (hmax n ω)
    have hadmAll_t : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
        0 ≤ X i ω ∧ 0 < 1 + (θt n ω).1 * X i ω / (θt n ω).2 :=
      hsupp.mono fun ω hω n => admissible_of_isMaxOn hθ₀K' hσ₀ (fun i => hω i) (hmaxt n ω)
    have hadm_h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω :=
      hadmAll_h.mono fun ω hω => Eventually.of_forall fun n i hi => by
        have h := (hω n ⟨i, hi⟩).2; have hσ := (hKS _ (hθK n ω)).2
        have e : 1 + (θh n ω).1 * X i ω / (θh n ω).2 =
            ((θh n ω).2 + (θh n ω).1 * X i ω) / (θh n ω).2 := by field_simp
        rw [e] at h; exact (div_pos_iff_of_pos_right hσ).1 h
    have hadm_t : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θt n ω).2 + (θt n ω).1 * X i ω :=
      hadmAll_t.mono fun ω hω => Eventually.of_forall fun n i hi => by
        have h := (hω n ⟨i, hi⟩).2; have hσ := (hK'S _ (hθtK n ω)).2
        have e : 1 + (θt n ω).1 * X i ω / (θt n ω).2 =
            ((θt n ω).2 + (θt n ω).1 * X i ω) / (θt n ω).2 := by field_simp
        rw [e] at h; exact (div_pos_iff_of_pos_right hσ).1 h
    have hnn_h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        0 ≤ 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN 0 σ₀ (fun i => X i ω) n) :=
      hsupp.mono fun ω hω => Eventually.of_forall fun n =>
        two_mul_gpdLogLikN_sub_nonneg_of_isMaxOn hσ₀ (interior_subset hθ₀) hω (hmax n ω)
    have hnn_t : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        0 ≤ 2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
          gpdLogLikN 0 σ₀ (fun i => X i ω) n) :=
      hsupp.mono fun ω hω => Eventually.of_forall fun n =>
        two_mul_gpdLogLikN_sub_nonneg_of_isMaxOn hσ₀ hθ₀K' hω (hmaxt n ω)
    have hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        ∑ i ∈ Finset.range n, gpdScoreXiAll (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
        ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0 := by
      filter_upwards [hadmAll_h, hcons] with ω hω hc
      filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀)] with n h1
      have hσ := (hKS _ (hθK n ω)).2
      have := scoreAll_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) h1 hσ (hω n) (hmax n ω)
      rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXiAll (θh n ω).1 (θh n ω).2 (X i ω)) n,
        Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n] at this
      exact this
    have hchart₀ := hchart.curve_chart.self_of_nhds rfl
    rw [hchart.map_true] at hchart₀
    have hs₁ : γ₁ s₀ = 0 := congrArg Prod.fst hchart₀
    have hs₂ : γ₂ s₀ = σ₀ := congrArg Prod.snd hchart₀
    have hcurve : ∀ᵐ ω ∂P, ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 s₀) ∧ ∀ᶠ n in atTop,
        θt n ω = (γ₁ (s n), γ₂ (s n)) ∧
        t₁ (s n) * ∑ i ∈ Finset.range n, gpdScoreXiAll (θt n ω).1 (θt n ω).2 (X i ω) +
          t₂ (s n) * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) = 0 := by
      filter_upwards [hadmAll_t, hconst] with ω hω hc
      have hs : Tendsto (fun n => φ (θt n ω)) atTop (𝓝 s₀) := by
        rw [← hchart.map_true]; exact hchart.continuousAt.tendsto.comp hc
      refine ⟨fun n => φ (θt n ω), hs, ?_⟩
      filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
        hs.eventually hchart.level.eventually_nhds, hs.eventually hchart.hasDerivAt₁.eventually_nhds,
        hs.eventually hchart.hasDerivAt₂.eventually_nhds, hc.eventually hchart.curve_chart]
        with n hint hlev hd₁ hd₂ hch
      have e : θt n ω = (γ₁ (φ (θt n ω)), γ₂ (φ (θt n ω))) := (hch (hθtK n ω).2).symm
      refine ⟨e, ?_⟩
      have d₁ := hd₁.self_of_nhds; have d₂ := hd₂.self_of_nhds
      have hmem : ∀ᶠ s' in 𝓝 (φ (θt n ω)), (γ₁ s', γ₂ s') ∈ K' := by
        have hcont : ContinuousAt (fun s' => (γ₁ s', γ₂ s')) (φ (θt n ω)) :=
          d₁.continuousAt.prodMk d₂.continuousAt
        have hint' : (γ₁ (φ (θt n ω)), γ₂ (φ (θt n ω))) ∈ interior K := by rw [← e]; exact hint
        filter_upwards [hcont.eventually (isOpen_interior.mem_nhds hint'), hlev] with s' h1 h2
        exact ⟨interior_subset h1, h2⟩
      have hmx := hmaxt n ω; rw [e] at hmx
      have hp₂ : 0 < γ₂ (φ (θt n ω)) := by
        have : (θt n ω).2 = γ₂ (φ (θt n ω)) := congrArg Prod.snd e
        rw [← this]; exact (hK'S _ (hθtK n ω)).2
      have hadm' : ∀ i : Fin n, 0 ≤ X i ω ∧ 0 < 1 + γ₁ (φ (θt n ω)) * X i ω / γ₂ (φ (θt n ω)) := by
        intro i
        have := hω n i
        rw [show (θt n ω).1 = γ₁ (φ (θt n ω)) from congrArg Prod.fst e,
          show (θt n ω).2 = γ₂ (φ (θt n ω)) from congrArg Prod.snd e] at this
        exact this
      have := curve_scoreAll_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) d₁ d₂ hp₂ hadm' hmem hmx
      rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXiAll _ _ (X i ω)) n,
        Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma _ _ (X i ω)) n] at this
      rw [show (θt n ω).1 = γ₁ (φ (θt n ω)) from congrArg Prod.fst e,
        show (θt n ω).2 = γ₂ (φ (θt n ω)) from congrArg Prod.snd e]
      exact this
    have h1 := tendstoInMeasure_gpdFullDeviance_sub_zero hσ₀ hX hind hθm hcons hadm_h hnn_h hroot
    have h2 := tendstoInMeasure_gpdCurveDeviance_sub_zero hσ₀ hX hind
      hchart.hasDerivAt₁.self_of_nhds hchart.hasDerivAt₂.self_of_nhds
      hchart.continuousAt₁ hchart.continuousAt₂ hs₁ hs₂ hchart.tangent_ne hθtm hadm_t hnn_t hcurve
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z
      (tendstoInDistribution_gpdInfoInvQuad_sub_reg hξ₀ hσ₀ hX hind hchart.tangent_ne hZ) ?_ fun n => by
        have ha := aemeasurable_gpdLogLikN hX (hθm n) n
        have hb := aemeasurable_gpdLogLikN hX (hθtm n) n; fun_prop
    have := tendstoInMeasure_comp₂ h1 h2 (φ := fun p => p.1 - p.2) continuous_sub.continuousAt
    simp only [sub_zero] at this
    convert this using 2 with n; funext ω; simp only [Pi.sub_apply]; ring
  · exact tendstoInDistribution_gpdProfileDeviance hK hKS hθ₀ hpos hσ₀ hX hind hg hchart
      hθm hθK hmax hθtm hθtK hmaxt hZ

/-- **Asymptotic coverage of the profile likelihood confidence set for ALL regular shapes
`ξ₀ > -1/2`** ([Coles, §2.6.6]): `P(g θ₀ ∈ {ψ : D_p(ψ) ≤ c}) → χ²₁((-∞, c])`. -/
theorem tendsto_measure_mem_gpdProfileInterval_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) {s₀ : ℝ} {φ : ℝ × ℝ → ℝ} {γ₁ γ₂ t₁ t₂ : ℝ → ℝ}
    (hchart : IsGPDProfileChart g ξ₀ σ₀ s₀ φ γ₁ γ₂ t₁ t₂) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | g (ξ₀, σ₀) ∈ gpdProfileInterval K g c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) := by
  set K' := K ∩ g ⁻¹' {g (ξ₀, σ₀)}
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    (hg.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton) inter_subset_left
  have hK'S : ∀ p ∈ K', -1 < p.1 ∧ 0 < p.2 := fun p hp => hKS p hp.1
  have hθ₀K' : (ξ₀, σ₀) ∈ K' := ⟨interior_subset hθ₀, rfl⟩
  choose G hGm hG using exists_measurable_gpdMLE hK hKS ⟨_, interior_subset hθ₀⟩
  choose G' hGm' hG' using exists_measurable_gpdMLE hK'c hK'S ⟨_, hθ₀K'⟩
  have hsam : ∀ n : ℕ, AEMeasurable (fun ω => (fun i : Fin n => X i ω)) P := fun n =>
    AEMeasurable.of_eval fun i => (hX i).aemeasurable
  have hD := tendstoInDistribution_gpdProfileDeviance_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind hg hchart
    (θh := fun n ω => G n fun i : Fin n => X i ω)
    (fun n => (hGm n).comp_aemeasurable (hsam n)) (fun n ω => (hG n _).1) (fun n ω => (hG n _).2)
    (θt := fun n ω => G' n fun i : Fin n => X i ω)
    (fun n => (hGm' n).comp_aemeasurable (hsam n)) (fun n ω => (hG' n _).1)
    (fun n ω => (hG' n _).2) (Z := id) (P' := chiSquared 1) HasLaw.id
  refine (hD.tendsto_measure_le_of_noAtoms HasLaw.id c).congr fun n => ?_
  refine measure_congr ?_
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  filter_upwards [hsupp] with ω hω
  apply propext
  obtain ⟨hne₁, hne₂⟩ := gpdMaxLogLik_finite_all (x := fun i => X i ω) hσ₀ (interior_subset hθ₀) hω
    (hG n _).1 (hG n _).2
  change 2 * (gpdLogLikN _ _ (fun i => X i ω) n - gpdLogLikN _ _ (fun i => X i ω) n) ≤ c ↔
    gpdMaxLogLik K (fun i : Fin n => X i ω) ≠ ⊥ ∧ gpdMaxLogLik K (fun i : Fin n => X i ω) ≠ ⊤ ∧
    2 * (gpdMaxLogLik K (fun i : Fin n => X i ω) -
      gpdProfileLogLik K g (g (ξ₀, σ₀)) (fun i : Fin n => X i ω)) ≤ (c : EReal)
  rw [and_iff_right hne₁, and_iff_right hne₂,
    gpdProfileLogLik, gpdMaxLogLik_eq_of_isMaxOn (hG n _).1 (hG n _).2,
    gpdMaxLogLik_eq_of_isMaxOn (hG' n _).1 (hG' n _).2,
    deviance_le_iff_all (x := fun i => X i ω) hσ₀ (interior_subset hθ₀) hθ₀K' hω (hG n _).2
      (hG' n _).2 c]

/-- **Asymptotic coverage of the profile likelihood confidence set at level `1 - α`**, all
`ξ₀ > -1/2`. -/
theorem exists_tendsto_measure_mem_gpdProfileInterval_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) {s₀ : ℝ} {φ : ℝ × ℝ → ℝ} {γ₁ γ₂ t₁ t₂ : ℝ → ℝ}
    (hchart : IsGPDProfileChart g ξ₀ σ₀ s₀ φ γ₁ γ₂ t₁ t₂) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ (chiSquared 1).real (Iic c) = 1 - α ∧
      Tendsto (fun n : ℕ => P {ω | g (ξ₀, σ₀) ∈ gpdProfileInterval K g c (fun i : Fin n => X i ω)})
        atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨c, hc, hq⟩ := exists_chiSquared_one_Iic_eq hα0 hα1
  refine ⟨c, hc, hq, ?_⟩
  rw [← hq, ofReal_measureReal]
  exact tendsto_measure_mem_gpdProfileInterval_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind hg hchart c

/-- **Profile likelihood interval for the shape `ξ`**, all regular shapes `ξ₀ > -1/2`. -/
theorem tendsto_measure_mem_gpdShapeProfileInterval_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | ξ₀ ∈ gpdProfileInterval K Prod.fst c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) :=
  tendsto_measure_mem_gpdProfileInterval_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind continuousOn_fst
    (isGPDProfileChart_shape ξ₀ σ₀) c

/-- **Profile likelihood interval for the scale `σ`**, all regular shapes `ξ₀ > -1/2`. -/
theorem tendsto_measure_mem_gpdScaleProfileInterval_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | σ₀ ∈ gpdProfileInterval K Prod.snd c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) :=
  tendsto_measure_mem_gpdProfileInterval_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind continuousOn_snd
    (isGPDProfileChart_scale ξ₀ σ₀) c

/-- **Profile likelihood interval for the POT return level**, all regular shapes `ξ₀ > -1/2`
(including `ξ₀ = 0`, [Coles, §2.6.6, §4.3.3]). -/
theorem tendsto_measure_mem_gpdReturnLevelProfileInterval_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) {u ζ N : ℝ}
    (hNζ : 1 < N * ζ) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gpdReturnLevel u ξ₀ σ₀ ζ N ∈
        gpdProfileInterval K (fun p => gpdReturnLevel u p.1 p.2 ζ N) c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) := by
  have hcont : Continuous fun p : ℝ × ℝ => gpdReturnLevel u p.1 p.2 ζ N := by
    unfold gpdReturnLevel
    exact continuous_const.add (continuous_snd.mul
      ((continuous_boxCox_shape (one_pos.trans hNζ)).comp continuous_fst))
  exact tendsto_measure_mem_gpdProfileInterval_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind hcont.continuousOn
    (isGPDProfileChart_returnLevel_all hNζ) c

/-- **Asymptotic coverage of the deviance region for the full GPD parameter**, all regular shapes
`ξ₀ > -1/2` ([Coles, §2.6.5]). -/
theorem tendsto_measure_mem_gpdDevianceRegion_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | (ξ₀, σ₀) ∈ gpdDevianceRegion K c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 2 (Iic c))) := by
  choose G hGm hG using exists_measurable_gpdMLE hK hKS ⟨_, interior_subset hθ₀⟩
  have hsam : ∀ n : ℕ, AEMeasurable (fun ω => (fun i : Fin n => X i ω)) P := fun n =>
    AEMeasurable.of_eval fun i => (hX i).aemeasurable
  have hD := tendstoInDistribution_gpdDeviance_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind
    (θh := fun n ω => G n fun i : Fin n => X i ω)
    (fun n => (hGm n).comp_aemeasurable (hsam n)) (fun n ω => (hG n _).1) (fun n ω => (hG n _).2)
    (Z := id) (P' := chiSquared 2) HasLaw.id
  refine (hD.tendsto_measure_le_of_noAtoms HasLaw.id c).congr fun n => ?_
  refine measure_congr ?_
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  filter_upwards [hsupp] with ω hω
  apply propext
  obtain ⟨hne₁, hne₂⟩ := gpdMaxLogLik_finite_all (x := fun i => X i ω) hσ₀ (interior_subset hθ₀) hω
    (hG n _).1 (hG n _).2
  change 2 * (gpdLogLikN _ _ (fun i => X i ω) n - gpdLogLikN _ _ (fun i => X i ω) n) ≤ c ↔
    (ξ₀, σ₀) ∈ K ∧
    gpdMaxLogLik K (fun i : Fin n => X i ω) ≠ ⊥ ∧ gpdMaxLogLik K (fun i : Fin n => X i ω) ≠ ⊤ ∧
    2 * (gpdMaxLogLik K (fun i : Fin n => X i ω) -
      gpdLogLikE ξ₀ σ₀ (fun i : Fin n => X i ω)) ≤ (c : EReal)
  rw [and_iff_right (interior_subset hθ₀), and_iff_right hne₁, and_iff_right hne₂]
  have hm₀ : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω))
      {(ξ₀, σ₀)} (ξ₀, σ₀) := isMaxOn_iff.2 fun p hp => by rw [mem_singleton_iff.1 hp]
  rw [gpdMaxLogLik_eq_of_isMaxOn (hG n _).1 (hG n _).2]
  exact (deviance_le_iff_all (x := fun i => X i ω) hσ₀ (interior_subset hθ₀) (mem_singleton _) hω
    (hG n _).2 hm₀ c).symm

/-- **The deviance region at level `1 - α`** ([Coles, §2.6.5]), all regular shapes `ξ₀ > -1/2`:
`P(θ₀ ∈ {θ : D(θ) ≤ -2 log α}) → 1 - α`. -/
theorem tendsto_measure_mem_gpdDevianceRegion_of_alpha_reg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    Tendsto (fun n : ℕ => P {ω | (ξ₀, σ₀) ∈
        gpdDevianceRegion K (-2 * log α) (fun i : Fin n => X i ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  rw [← chiSquared_two_real_Iic_log hα0 hα1, ofReal_measureReal]
  exact tendsto_measure_mem_gpdDevianceRegion_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind _

end WilksReg

end ExtremeValueTheory
