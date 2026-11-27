/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDMLENormality
import ExtremeValueTheory.Statistics.GEVGumbelLimit

/-!
# Joint asymptotic normality of the GPD maximum likelihood estimator at `ξ₀ = 0`

Let `X₀, X₁, …` be iid `GPD(0, σ₀) = Exp(1/σ₀)` with `σ₀ > 0`. We remove the `ξ₀ ≠ 0`
restriction from `ExtremeValueTheory.Statistics.GPDMLENormality`, proving that measurable
maximizers `θ̂ₙ = (ξ̂ₙ, σ̂ₙ)` of the two-parameter GPD log-likelihood over a compact set
`K ⊂ {ξ > -1, σ > 0}` containing `(0, σ₀)` in its interior satisfy

  `√n (θ̂ₙ - (0, σ₀)) ⇒ N(0, I(0, σ₀)⁻¹)`,

where `I(0, σ₀) = [[2, 1/σ₀], [1/σ₀, 1/σ₀²]]` and
`I(0, σ₀)⁻¹ = [[1, -σ₀], [-σ₀, 2σ₀²]] = gpdFisherInfoInv 0 σ₀` ([Smith 1985]; [Coles, §4.3.3]).

## Main results

* `log1pCube`, `continuousAt_log1pCube`, `abs_log1pCube_le_of_ge_neg_half`: third-order
  logarithmic expansion `(-2 log(1 + t) + 2 t/(1 + t) + t²/(1 + t)²)/t³` (continuous on
  `(-1, ∞)`, value `-2/3` at `0`).
* `gpdScoreXiAll`, `gpdHessXiXiAll`: continuous extensions of the GPD shape score and
  shape-shape Hessian across `ξ = 0`.
* `scoreAll_eq_zero_of_isMaxOn`: the continuous likelihood equations vanish at any interior
  maximizer (including `ξ = 0`).
* `tendstoInDistribution_gpdJointMLE_zero`: joint normality for consistent admissible roots
  at `ξ₀ = 0`.
* `tendstoInDistribution_gpdMLE_zero`: joint normality for maximizers over compact `K` at
  `ξ₀ = 0`.
* `tendstoInDistribution_gpdMLE_reg`, `exists_gpdMLE_tendstoInDistribution_reg`: unified
  asymptotic normality of the GPD MLE for **every** regular shape `ξ₀ > -1/2`, with no
  `ξ₀ ≠ 0` exclusion.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §4.3.3.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace ExtremeValueTheory

/-! ### Third-order logarithmic expansion `log1pCube` -/

section Log1pCube

/-- `(-2 log(1 + t) + 2 t/(1 + t) + t²/(1 + t)²) / t³`, extended by `-2/3` at `t = 0`. -/
noncomputable def log1pCube (t : ℝ) : ℝ :=
  if t = 0 then -(2 / 3)
  else (-2 * log (1 + t) + 2 * t / (1 + t) + t ^ 2 / (1 + t) ^ 2) / t ^ 3

lemma log1pCube_zero : log1pCube 0 = -(2 / 3) := by simp [log1pCube]

lemma log1pCube_of_ne {t : ℝ} (ht : t ≠ 0) :
    log1pCube t = (-2 * log (1 + t) + 2 * t / (1 + t) + t ^ 2 / (1 + t) ^ 2) / t ^ 3 := by
  simp [log1pCube, ht]

lemma measurable_log1pCube : Measurable log1pCube := by
  unfold log1pCube
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const (by fun_prop)

/-- `|log1pCube t - (-2/3)| ≤ 8 |t|` for `|t| ≤ 1/2`. -/
lemma abs_log1pCube_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |log1pCube t - -(2 / 3)| ≤ 8 * |t| := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [log1pCube]
  have hlt : |-t| < 1 := by rw [abs_neg]; linarith
  have hT := abs_log_sub_add_sum_range_le hlt 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hT
  norm_num at hT
  have h1t : 1 / 2 ≤ 1 + t := by linarith [neg_abs_le t]
  have hpos : 0 < 1 + t := by linarith
  have habs : 0 < |t| := abs_pos.2 h0
  have hden : 1 / 2 ≤ 1 - |t| := by linarith
  have hT' : |log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3| ≤ 2 * |t| ^ 4 := by
    have hT0 : |log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3| ≤ |t| ^ 4 / (1 - |t|) := by
      convert hT using 2
      ring
    calc |log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3|
        ≤ |t| ^ 4 / (1 - |t|) := hT0
      _ ≤ |t| ^ 4 / (1 / 2) := by gcongr
      _ = 2 * |t| ^ 4 := by ring
  have hR : |t ^ 4 / (1 + t) ^ 2| ≤ 4 * |t| ^ 4 := by
    rw [abs_div, abs_pow, abs_pow, abs_of_pos hpos, div_le_iff₀ (sq_pos_of_pos hpos)]
    have hsq : 1 / 4 ≤ (1 + t) ^ 2 := by nlinarith
    nlinarith [pow_pos habs 4]
  have e : log1pCube t - -(2 / 3) =
      (-2 * (log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3) + t ^ 4 / (1 + t) ^ 2) / t ^ 3 := by
    rw [log1pCube_of_ne h0]
    field_simp
    ring
  rw [e, abs_div, abs_pow, div_le_iff₀ (by positivity)]
  calc |-2 * (log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3) + t ^ 4 / (1 + t) ^ 2|
      ≤ |-2 * (log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3)| + |t ^ 4 / (1 + t) ^ 2| := abs_add_le _ _
    _ = 2 * |log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3| + |t ^ 4 / (1 + t) ^ 2| := by
        rw [abs_mul, abs_neg, abs_of_pos two_pos]
    _ ≤ 2 * (2 * |t| ^ 4) + 4 * |t| ^ 4 := add_le_add (by linarith) hR
    _ = 8 * |t| * |t| ^ 3 := by ring

lemma continuousAt_log1pCube_zero : ContinuousAt log1pCube 0 := by
  rw [ContinuousAt, log1pCube_zero]
  have h : Tendsto (fun t => log1pCube t - -(2 / 3)) (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul 8)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    rw [Real.norm_eq_abs]
    have ht' := Metric.mem_ball.1 ht
    rw [dist_zero_right, Real.norm_eq_abs] at ht'
    exact abs_log1pCube_sub_le ht'.le
  have := h.add_const (-(2 / 3))
  simp only [sub_add_cancel, zero_add] at this
  exact this

lemma continuousAt_log1pCube {t : ℝ} (ht : -1 < t) : ContinuousAt log1pCube t := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact continuousAt_log1pCube_zero
  · have hev : (fun s => (-2 * log (1 + s) + 2 * s / (1 + s) + s ^ 2 / (1 + s) ^ 2) / s ^ 3) =ᶠ[𝓝 t]
        log1pCube := by
      filter_upwards [isOpen_ne.mem_nhds h0] with s hs
      rw [log1pCube_of_ne hs]
    refine ContinuousAt.congr ?_ hev
    have h1t : 1 + t ≠ 0 := by linarith
    have h1t2 : (1 + t) ^ 2 ≠ 0 := pow_ne_zero 2 h1t
    have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 h0
    fun_prop (disch := assumption)

/-- Uniform bound `|log1pCube t| ≤ 32` for all `t ≥ -1/2`. -/
lemma abs_log1pCube_le_of_ge_neg_half {t : ℝ} (ht : -(1 / 2) ≤ t) : |log1pCube t| ≤ 32 := by
  by_cases hle : |t| ≤ 1 / 2
  · have h := abs_log1pCube_sub_le hle
    have h2 := abs_sub_abs_le_abs_sub (log1pCube t) (-(2 / 3))
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] at h2
    linarith
  · have htpos : 1 / 2 < t := by
      rcases lt_or_ge t 0 with hneg | hnn
      · exfalso; apply hle; rw [abs_of_neg hneg]; linarith
      · rw [abs_of_nonneg hnn] at hle; linarith
    have ht0 : 0 < t := by linarith
    have h1t : 0 < 1 + t := by linarith
    rw [log1pCube_of_ne ht0.ne', abs_div, abs_pow, abs_of_pos ht0, div_le_iff₀ (pow_pos ht0 3)]
    have hlog0 : 0 ≤ log (1 + t) := log_nonneg (by linarith)
    have hlog1 : log (1 + t) ≤ t := by linarith [log_le_sub_one_of_pos h1t]
    have hdiv1 : t / (1 + t) ≤ 1 := (div_le_one h1t).2 (by linarith)
    have hdiv2 : t ^ 2 / (1 + t) ^ 2 ≤ 1 := by
      rw [div_le_one (sq_pos_of_pos h1t)]; nlinarith
    have hnum : |-2 * log (1 + t) + 2 * t / (1 + t) + t ^ 2 / (1 + t) ^ 2| ≤ 2 * t + 3 := by
      have h1 : |-2 * log (1 + t)| = 2 * log (1 + t) := by
        rw [abs_mul, abs_neg, abs_of_pos two_pos, abs_of_nonneg hlog0]
      have h2 : |2 * t / (1 + t)| = 2 * (t / (1 + t)) := by
        rw [mul_div_assoc, abs_mul, abs_of_pos two_pos, abs_of_nonneg (by positivity)]
      have h3 : |t ^ 2 / (1 + t) ^ 2| = t ^ 2 / (1 + t) ^ 2 := abs_of_nonneg (by positivity)
      calc |-2 * log (1 + t) + 2 * t / (1 + t) + t ^ 2 / (1 + t) ^ 2|
          ≤ |-2 * log (1 + t) + 2 * t / (1 + t)| + |t ^ 2 / (1 + t) ^ 2| := abs_add_le _ _
        _ ≤ (|-2 * log (1 + t)| + |2 * t / (1 + t)|) + |t ^ 2 / (1 + t) ^ 2| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ ≤ 2 * t + 2 * 1 + 1 := by rw [h1, h2, h3]; linarith
        _ = 2 * t + 3 := by ring
    have ht2 : 1 / 4 ≤ t ^ 2 := by nlinarith
    have ht3 : t ≤ 4 * t ^ 3 := by nlinarith
    have h1le : 1 ≤ 8 * t ^ 3 := by nlinarith
    linarith

end Log1pCube

/-! ### Continuous GPD score and Hessian across `ξ = 0` -/

section ScoreHessAll

variable {ξ σ x : ℝ}

/-- The GPD shape score, extended continuously to `ξ = 0`. -/
noncomputable def gpdScoreXiAll (ξ σ x : ℝ) : ℝ :=
  if ξ = 0 then expScoreXi σ x else gpdScoreXi ξ σ x

lemma gpdScoreXiAll_zero (σ x : ℝ) : gpdScoreXiAll 0 σ x = expScoreXi σ x := by
  simp [gpdScoreXiAll]

lemma gpdScoreXiAll_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) (σ x : ℝ) :
    gpdScoreXiAll ξ σ x = gpdScoreXi ξ σ x := by
  simp [gpdScoreXiAll, hξ]

lemma gpdScoreSigma_zero (σ x : ℝ) : gpdScoreSigma 0 σ x = expScoreSigma σ x := by
  simp [gpdScoreSigma, expScoreSigma]

/-- The GPD shape score in the uniform form `(x/σ)² log1pQuad(ξ x/σ) - x/(σ + ξ x)`. -/
lemma gpdScoreXiAll_eq_log1pQuad (hσ : 0 < σ) (hu : 0 < σ + ξ * x) :
    gpdScoreXiAll ξ σ x = (x / σ) ^ 2 * log1pQuad (ξ * (x / σ)) - x / (σ + ξ * x) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [gpdScoreXiAll_zero, expScoreXi, zero_mul, log1pQuad, ↓reduceIte, add_zero]
    ring
  · rw [gpdScoreXiAll_of_ne hξ, gpdScoreXi]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have ht : ξ * (x / σ) ≠ 0 := mul_ne_zero hξ (div_ne_zero hx hσ.ne')
    rw [log1pQuad_of_ne ht]
    have h1 : 1 + ξ * (x / σ) = (σ + ξ * x) / σ := by field_simp
    have h2 : ξ * x / σ = ξ * (x / σ) := by ring
    rw [h2]
    have h1p : 1 + ξ * (x / σ) ≠ 0 := by rw [h1]; exact (div_pos hu hσ).ne'
    have hσ' : σ ≠ 0 := hσ.ne'
    have hu' : σ + ξ * x ≠ 0 := hu.ne'
    generalize log (1 + ξ * (x / σ)) = L
    field_simp
    ring

/-- The GPD shape-shape Hessian `∂²_ξ ℓ`, written uniformly across `ξ = 0`:
`(x/σ)³ log1pCube(ξ x/σ) + (x/(σ + ξ x))²`. -/
noncomputable def gpdHessXiXiAll (ξ σ x : ℝ) : ℝ :=
  (x / σ) ^ 3 * log1pCube (ξ * (x / σ)) + (x / (σ + ξ * x)) ^ 2

lemma gpdHessXiXiAll_zero (σ x : ℝ) :
    gpdHessXiXiAll 0 σ x = -(2 / 3) * (x / σ) ^ 3 + (x / σ) ^ 2 := by
  simp only [gpdHessXiXiAll, zero_mul, log1pCube_zero, add_zero]
  ring

lemma gpdHessXiXiAll_of_ne (hξ : ξ ≠ 0) (hσ : 0 < σ) (hu : 0 < σ + ξ * x) :
    gpdHessXiXiAll ξ σ x = gpdHessXiXi ξ σ x := by
  unfold gpdHessXiXiAll gpdHessXiXi
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have ht : ξ * (x / σ) ≠ 0 := mul_ne_zero hξ (div_ne_zero hx hσ.ne')
  rw [log1pCube_of_ne ht]
  have h1 : 1 + ξ * (x / σ) = (σ + ξ * x) / σ := by field_simp
  have h2 : ξ * x / σ = ξ * (x / σ) := by ring
  rw [h2]
  have h1p : 1 + ξ * (x / σ) ≠ 0 := by rw [h1]; exact (div_pos hu hσ).ne'
  have hσ' : σ ≠ 0 := hσ.ne'
  have hu' : σ + ξ * x ≠ 0 := hu.ne'
  generalize log (1 + ξ * (x / σ)) = L
  field_simp
  ring

lemma measurable_gpdHessXiXiAll₃ :
    Measurable fun q : ℝ × ℝ × ℝ => gpdHessXiXiAll q.1 q.2.1 q.2.2 := by
  unfold gpdHessXiXiAll
  have h1 : Measurable fun q : ℝ × ℝ × ℝ => log1pCube (q.1 * (q.2.2 / q.2.1)) :=
    measurable_log1pCube.comp (by fun_prop)
  fun_prop

lemma measurable_gpdHessXiXiAll (ξ σ : ℝ) : Measurable (gpdHessXiXiAll ξ σ) :=
  measurable_gpdHessXiXiAll₃.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

lemma continuousAt_gpdHessXiXiAll₃ {q : ℝ × ℝ × ℝ} (hσ : 0 < q.2.1)
    (hu : 0 < q.2.1 + q.1 * q.2.2) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => gpdHessXiXiAll q.1 q.2.1 q.2.2) q := by
  unfold gpdHessXiXiAll
  have ht : -1 < q.1 * (q.2.2 / q.2.1) := by
    have : 1 + q.1 * (q.2.2 / q.2.1) = (q.2.1 + q.1 * q.2.2) / q.2.1 := by field_simp
    have hpos : 0 < 1 + q.1 * (q.2.2 / q.2.1) := by rw [this]; exact div_pos hu hσ
    linarith
  have hc1 : ContinuousAt (fun p : ℝ × ℝ × ℝ => log1pCube (p.1 * (p.2.2 / p.2.1))) q :=
    (continuousAt_log1pCube ht).comp (f := fun p : ℝ × ℝ × ℝ => p.1 * (p.2.2 / p.2.1))
      (continuous_fst.continuousAt.mul (continuous_snd.snd.continuousAt.div
        continuous_snd.fst.continuousAt hσ.ne'))
  have hσ' : q.2.1 ≠ 0 := hσ.ne'
  have hu' : q.2.1 + q.1 * q.2.2 ≠ 0 := hu.ne'
  fun_prop (disch := assumption)

/-- Continuity of `r ↦ gpdScoreXiAll (r * a) (σ₀ + r * b) x` at `r = 0`. -/
lemma continuousAt_gpdScoreXiAll_line_zero {σ₀ a b : ℝ} (hσ₀ : 0 < σ₀) :
    ContinuousAt (fun r => gpdScoreXiAll (0 + r * a) (σ₀ + r * b) x) 0 := by
  have hev : (fun r => (x / (σ₀ + r * b)) ^ 2 * log1pQuad ((0 + r * a) * (x / (σ₀ + r * b))) -
      x / ((σ₀ + r * b) + (0 + r * a) * x)) =ᶠ[𝓝 (0 : ℝ)]
      fun r => gpdScoreXiAll (0 + r * a) (σ₀ + r * b) x := by
    have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < σ₀ + r * b :=
      (show Continuous fun r : ℝ => σ₀ + r * b by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using hσ₀))
    have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < (σ₀ + r * b) + (0 + r * a) * x :=
      (show Continuous fun r : ℝ => (σ₀ + r * b) + (0 + r * a) * x by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using hσ₀))
    filter_upwards [h1, h2] with r hr1 hr2
    exact (gpdScoreXiAll_eq_log1pQuad hr1 hr2).symm
  refine ContinuousAt.congr ?_ hev
  have hq : ContinuousAt (fun r : ℝ => log1pQuad ((0 + r * a) * (x / (σ₀ + r * b)))) 0 := by
    have harg : ContinuousAt (fun r : ℝ => (0 + r * a) * (x / (σ₀ + r * b))) 0 := by
      have hden : σ₀ + 0 * b ≠ 0 := by simpa using hσ₀.ne'
      fun_prop (disch := assumption)
    exact ContinuousAt.comp (g := log1pQuad) (by simpa using continuousAt_log1pQuad_zero) harg
  have hden1 : σ₀ + 0 * b ≠ 0 := by simpa using hσ₀.ne'
  have hden2 : (σ₀ + 0 * b) + (0 + 0 * a) * x ≠ 0 := by simpa using hσ₀.ne'
  fun_prop (disch := assumption)

/-- Derivative of `gpdScoreXiAll` along a line starting at `(0, σ₀)`, valid at every `s`
including `s = 0` and when `a = 0`. -/
lemma hasDerivAt_gpdScoreXiAll_line {σ₀ a b s : ℝ} (hσ : 0 < σ₀ + s * b)
    (hu : 0 < (σ₀ + s * b) + (0 + s * a) * x) :
    HasDerivAt (fun r => gpdScoreXiAll (0 + r * a) (σ₀ + r * b) x)
      (a * gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x +
        b * gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x) s := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [mul_zero, add_zero, zero_mul, gpdScoreXiAll_zero, expScoreXi, gpdHessXiSigma]
    have h1 : HasDerivAt (fun r => x / (σ₀ + r * b)) (-(x * b) / (σ₀ + s * b) ^ 2) s := by
      have hd : HasDerivAt (fun r => σ₀ + r * b) b s := by
        simpa using ((hasDerivAt_id s).mul_const b).const_add σ₀
      refine ((hasDerivAt_const s x).div hd hσ.ne').congr_deriv ?_; ring
    have h2 := ((h1.pow 2).div_const 2).sub h1
    refine h2.congr_deriv ?_
    have hσ' : σ₀ + s * b ≠ 0 := by simpa using hσ.ne'
    norm_num
    field_simp [hσ']
    ring
  · rcases eq_or_ne s 0 with rfl | hs
    · have hU : {r : ℝ | 0 < σ₀ + r * b ∧ 0 < (σ₀ + r * b) + (0 + r * a) * x} ∈ 𝓝 (0 : ℝ) := by
        have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < σ₀ + r * b :=
          (show Continuous fun r : ℝ => σ₀ + r * b by fun_prop).continuousAt.eventually
            (lt_mem_nhds hσ)
        have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < (σ₀ + r * b) + (0 + r * a) * x :=
          (show Continuous fun r : ℝ => (σ₀ + r * b) + (0 + r * a) * x by fun_prop).continuousAt.eventually
            (lt_mem_nhds hu)
        exact h1.and h2
      have hσ₀ : 0 < σ₀ := by simpa using hσ
      refine hasDerivAt_of_tendsto_punctured
        (g := fun r => a * gpdHessXiXiAll (0 + r * a) (σ₀ + r * b) x +
          b * gpdHessXiSigma (0 + r * a) (σ₀ + r * b) x)
        hU (fun r hr hr0 => ?_)
        (continuousAt_gpdScoreXiAll_line_zero hσ₀) ?_
      · have hra : 0 + r * a ≠ 0 := by simp [mul_ne_zero hr0 ha]
        have hev : (fun t => gpdScoreXiAll (0 + t * a) (σ₀ + t * b) x) =ᶠ[𝓝 r]
            fun t => gpdScoreXi (0 + t * a) (σ₀ + t * b) x := by
          have hc : ContinuousAt (fun t => 0 + t * a) r := by fun_prop
          filter_upwards [hc.eventually (isOpen_ne.mem_nhds hra)] with t ht
          exact gpdScoreXiAll_of_ne ht _ _
        rw [gpdHessXiXiAll_of_ne hra hr.1 hr.2]
        exact (hasDerivAt_gpdScoreXi_line hra hr.1 hr.2).congr_of_eventuallyEq hev
      · have hc1 : ContinuousAt (fun r => gpdHessXiXiAll (0 + r * a) (σ₀ + r * b) x) 0 :=
          (continuousAt_gpdHessXiXiAll₃ (q := (0 + 0 * a, σ₀ + 0 * b, x)) hσ hu).comp
            (f := fun r => (0 + r * a, σ₀ + r * b, x)) (by fun_prop)
        have hc2 : ContinuousAt (fun r => gpdHessXiSigma (0 + r * a) (σ₀ + r * b) x) 0 :=
          (continuousAt_gpdHessXiSigma₃ (q := (0 + 0 * a, σ₀ + 0 * b, x)) hσ hu).comp
            (f := fun r => (0 + r * a, σ₀ + r * b, x)) (by fun_prop)
        exact ((hc1.const_mul a).add (hc2.const_mul b)).tendsto.mono_left nhdsWithin_le_nhds
    · have hsa : 0 + s * a ≠ 0 := by simp [mul_ne_zero hs ha]
      have hev : (fun t => gpdScoreXiAll (0 + t * a) (σ₀ + t * b) x) =ᶠ[𝓝 s]
          fun t => gpdScoreXi (0 + t * a) (σ₀ + t * b) x := by
        have hc : ContinuousAt (fun t => 0 + t * a) s := by fun_prop
        filter_upwards [hc.eventually (isOpen_ne.mem_nhds hsa)] with t ht
        exact gpdScoreXiAll_of_ne ht _ _
      rw [gpdHessXiXiAll_of_ne hsa hσ hu]
      exact (hasDerivAt_gpdScoreXi_line hsa hσ hu).congr_of_eventuallyEq hev

/-- **The likelihood equations at an interior maximizer, for any shape `ξ ∈ ℝ`** (including `ξ = 0`). -/
theorem scoreAll_eq_zero_of_isMaxOn {K : Set (ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ}
    (hθK : θ ∈ interior K) (hθ₂ : 0 < θ.2)
    (hadm : ∀ i, 0 ≤ x i ∧ 0 < 1 + θ.1 * x i / θ.2)
    (hmax : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K θ) :
    ∑ i, gpdScoreXiAll θ.1 θ.2 (x i) = 0 ∧ ∑ i, gpdScoreSigma θ.1 θ.2 (x i) = 0 := by
  have hint := isOpen_interior.mem_nhds hθK
  have hnear : ∀ᶠ p in 𝓝 θ, 0 < p.2 ∧ ∀ i, 0 < 1 + p.1 * x i / p.2 := by
    refine (continuous_snd.continuousAt.eventually (lt_mem_nhds hθ₂)).and ?_
    refine eventually_all.2 fun i => ?_
    have hc : ContinuousAt (fun p : ℝ × ℝ => 1 + p.1 * x i / p.2) θ :=
      continuousAt_const.add ((continuous_fst.continuousAt.mul continuousAt_const).div
        continuous_snd.continuousAt hθ₂.ne')
    exact hc.eventually (lt_mem_nhds (hadm i).2)
  have hle : ∀ᶠ p in 𝓝 θ, ∑ i, log (gpdDensity p.1 p.2 (x i)) ≤
      ∑ i, log (gpdDensity θ.1 θ.2 (x i)) := by
    filter_upwards [hnear, hint] with p hp hpK
    have := hmax (interior_subset hpK)
    simp only [mem_ofPred_eq] at this
    rw [gpdLogLikE_eq_coe' (fun i => ⟨(hadm i).1, hp.2 i⟩), gpdLogLikE_eq_coe' hadm] at this
    exact EReal.coe_le_coe_iff.1 this
  have hpos_u : ∀ i, 0 < θ.2 + θ.1 * x i := fun i => by
    have h := (hadm i).2
    have e : 1 + θ.1 * x i / θ.2 = (θ.2 + θ.1 * x i) / θ.2 := by field_simp
    rw [e] at h
    exact (div_pos_iff_of_pos_right hθ₂).1 h
  constructor
  · have hd : HasDerivAt (fun ξ => ∑ i, log (gpdDensity ξ θ.2 (x i)))
        (∑ i, gpdScoreXiAll θ.1 θ.2 (x i)) θ.1 := by
      have := HasDerivAt.sum (u := Finset.univ) (A := fun i ξ => log (gpdDensity ξ θ.2 (x i)))
        (A' := fun i => gpdScoreXiAll θ.1 θ.2 (x i)) (x := θ.1) fun i _ => by
        rcases eq_or_ne θ.1 0 with h0 | h0
        · rw [h0, gpdScoreXiAll_zero]
          exact hasDerivAt_log_gpdDensity_xi_zero hθ₂ (hadm i).1
        · rw [gpdScoreXiAll_of_ne h0]
          exact hasDerivAt_log_gpdDensity_xi hθ₂ h0 (hadm i).1 (hpos_u i)
      convert this using 1
      funext ξ; simp
    have hloc : IsLocalMax (fun ξ => ∑ i, log (gpdDensity ξ θ.2 (x i))) θ.1 := by
      have hc : Tendsto (fun ξ : ℝ => (ξ, θ.2)) (𝓝 θ.1) (𝓝 θ) := by
        have := (continuous_id.prodMk continuous_const).continuousAt (f := fun ξ : ℝ => (ξ, θ.2))
          (x := θ.1)
        simpa using this.tendsto
      exact (hc.eventually hle).mono fun ξ h => h
    exact hloc.hasDerivAt_eq_zero hd
  · have hd : HasDerivAt (fun σ => ∑ i, log (gpdDensity θ.1 σ (x i)))
        (∑ i, gpdScoreSigma θ.1 θ.2 (x i)) θ.2 := by
      have := HasDerivAt.sum (u := Finset.univ) (A := fun i σ => log (gpdDensity θ.1 σ (x i)))
        (A' := fun i => gpdScoreSigma θ.1 θ.2 (x i)) fun i _ => by
        rcases eq_or_ne θ.1 0 with h0 | h0
        · rw [h0, gpdScoreSigma_zero]
          have hev : (fun s => log (gpdDensity 0 s (x i))) =ᶠ[𝓝 θ.2] fun s => -log s - x i / s := by
            filter_upwards [lt_mem_nhds hθ₂] with s hs
            exact log_gpdDensity_zero hs (hadm i).1
          refine HasDerivAt.congr_of_eventuallyEq ?_ hev
          have h1 : HasDerivAt (fun s => -log s) (-(θ.2⁻¹)) θ.2 := (hasDerivAt_log hθ₂.ne').neg
          have h2 : HasDerivAt (fun s => x i / s) (-(x i / θ.2 ^ 2)) θ.2 := by
            have := (hasDerivAt_inv hθ₂.ne').const_mul (x i)
            refine (this.congr_of_eventuallyEq (Eventually.of_forall fun s => by rw [div_eq_mul_inv])).congr_deriv ?_
            ring
          refine (h1.sub h2).congr_deriv ?_
          unfold expScoreSigma; have := hθ₂.ne'; field_simp; ring
        · exact hasDerivAt_log_gpdDensity_sigma hθ₂ h0 (hadm i).1 (hpos_u i)
      convert this using 1
      funext σ; simp
    have hloc : IsLocalMax (fun σ => ∑ i, log (gpdDensity θ.1 σ (x i))) θ.2 := by
      have hc : Tendsto (fun σ : ℝ => (θ.1, σ)) (𝓝 θ.2) (𝓝 θ) := by
        have := (continuous_const.prodMk continuous_id).continuousAt (f := fun σ : ℝ => (θ.1, σ))
          (x := θ.2)
        simpa using this.tendsto
      exact (hc.eventually hle).mono fun σ h => h
    exact hloc.hasDerivAt_eq_zero hd

end ScoreHessAll

/-! ### Neighbourhood, segment expansion, and bounds near `(0, σ₀)` -/

section ZeroNbhd

variable {σ₀ : ℝ}

/-- The closed neighbourhood `[-1/4, 1/4] × [7σ₀/8, 9σ₀/8]` of `(0, σ₀)`. -/
def gpdNbhdZero (σ₀ : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Icc (7 * σ₀ / 8) (9 * σ₀ / 8)

lemma convex_gpdNbhdZero : Convex ℝ (gpdNbhdZero σ₀) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

lemma isCompact_gpdNbhdZero : IsCompact (gpdNbhdZero σ₀) :=
  isCompact_Icc.prod isCompact_Icc

lemma gpdNbhdZero_mem_nhds (hσ₀ : 0 < σ₀) : gpdNbhdZero σ₀ ∈ 𝓝 (0, σ₀) :=
  prod_mem_nhds (Icc_mem_nhds (by norm_num) (by norm_num))
    (Icc_mem_nhds (by linarith) (by linarith))

lemma mem_gpdNbhdZero_self (hσ₀ : 0 < σ₀) : (0, σ₀) ∈ gpdNbhdZero σ₀ :=
  ⟨⟨by norm_num, by norm_num⟩, by linarith, by linarith⟩

lemma bounds_of_mem_gpdNbhdZero {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀) :
    -(1 / 4 : ℝ) ≤ θ.1 ∧ θ.1 ≤ 1 / 4 ∧ 7 * σ₀ / 8 ≤ θ.2 ∧ θ.2 ≤ 9 * σ₀ / 8 :=
  ⟨hθ.1.1, hθ.1.2, hθ.2.1, hθ.2.2⟩

lemma segment_mem_gpdNbhdZero (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀)) ∈ gpdNbhdZero σ₀ := by
  have h := convex_gpdNbhdZero (mem_gpdNbhdZero_self hσ₀) hθ (sub_nonneg.2 hs.2) hs.1 (by ring)
  convert h using 1
  ext
  · simp
  · simp; ring

/-- Exact FTC expansion of the continuous score along the segment from `(0, σ₀)` to `θ`. -/
theorem gpdScoreAll_sub_eq_segHess (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀)
    {x : ℝ} (h1 : 0 < θ.2 + θ.1 * x) :
    gpdScoreXiAll θ.1 θ.2 x - expScoreXi σ₀ x =
        (θ.1 - 0) * segHess gpdHessXiXiAll 0 σ₀ θ x +
          (θ.2 - σ₀) * segHess gpdHessXiSigma 0 σ₀ θ x ∧
    gpdScoreSigma θ.1 θ.2 x - expScoreSigma σ₀ x =
        (θ.1 - 0) * segHess gpdHessXiSigma 0 σ₀ θ x +
          (θ.2 - σ₀) * segHess gpdHessSigmaSigma 0 σ₀ θ x := by
  have h0 : 0 < σ₀ + 0 * x := by simpa using hσ₀
  set a := θ.1 - 0
  set b := θ.2 - σ₀
  have hseg : ∀ s ∈ uIcc (0 : ℝ) 1, 0 < σ₀ + s * b ∧
      0 < (σ₀ + s * b) + (0 + s * a) * x := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    have hmem := segment_mem_gpdNbhdZero hσ₀ hθ hs
    have hσs : 0 < σ₀ + s * b := by linarith [hmem.2.1]
    exact ⟨hσs, seg_support_pos (ξ₀ := 0) h0 h1 hs⟩
  have hcXX : ContinuousOn (fun s => gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs
    obtain ⟨hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessXiXiAll₃ (q := (0 + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun s => (0 + s * a, σ₀ + s * b, x)) (by fun_prop)).continuousWithinAt
  have hcXS : ContinuousOn (fun s => gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs
    obtain ⟨hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessXiSigma₃ (q := (0 + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun s => (0 + s * a, σ₀ + s * b, x)) (by fun_prop)).continuousWithinAt
  have hcSS : ContinuousOn (fun s => gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x) (uIcc 0 1) := by
    intro s hs
    obtain ⟨hσs, hus⟩ := hseg s hs
    exact ((continuousAt_gpdHessSigmaSigma₃ (q := (0 + s * a, σ₀ + s * b, x)) hσs hus).comp
      (f := fun s => (0 + s * a, σ₀ + s * b, x)) (by fun_prop)).continuousWithinAt
  have iXX : IntervalIntegrable (fun s => gpdHessXiXiAll (0 + s * a) (σ₀ + s * b) x) volume 0 1 :=
    hcXX.intervalIntegrable
  have iXS : IntervalIntegrable (fun s => gpdHessXiSigma (0 + s * a) (σ₀ + s * b) x) volume 0 1 :=
    hcXS.intervalIntegrable
  have iSS : IntervalIntegrable (fun s => gpdHessSigmaSigma (0 + s * a) (σ₀ + s * b) x) volume 0 1 :=
    hcSS.intervalIntegrable
  have e1 : 0 + 1 * a = θ.1 := by simp [a]
  have e2 : σ₀ + 1 * b = θ.2 := by simp [b]
  constructor
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => gpdScoreXiAll (0 + s * a) (σ₀ + s * b) x)
      (fun s hs => hasDerivAt_gpdScoreXiAll_line (hseg s hs).1 (hseg s hs).2)
      ((iXX.const_mul a).add (iXS.const_mul b))
    rw [intervalIntegral.integral_add (iXX.const_mul a) (iXS.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    simp only [e1, e2, zero_mul, add_zero, gpdScoreXiAll_zero] at hftc
    rw [← hftc]
    rfl
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => gpdScoreSigma (0 + s * a) (σ₀ + s * b) x)
      (fun s hs => hasDerivAt_gpdScoreSigma_line (hseg s hs).1 (hseg s hs).2)
      ((iXS.const_mul a).add (iSS.const_mul b))
    rw [intervalIntegral.integral_add (iXS.const_mul a) (iSS.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    simp only [e1, e2, zero_mul, add_zero, gpdScoreSigma_zero] at hftc
    rw [← hftc]
    rfl

/-! ### Dominating function and one-sided / two-sided Hessian bounds -/

/-- The cubic dominating function `1 + (x/σ₀)³`, integrable under `Exp(1/σ₀)`. -/
noncomputable def gpdDomZero (σ₀ x : ℝ) : ℝ := 1 + (x / σ₀) ^ 3

lemma measurable_gpdDomZero (σ₀ : ℝ) : Measurable (gpdDomZero σ₀) := by
  unfold gpdDomZero; fun_prop

lemma one_le_gpdDomZero (hσ₀ : 0 < σ₀) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ gpdDomZero σ₀ x := by
  unfold gpdDomZero
  have : 0 ≤ (x / σ₀) ^ 3 := by positivity
  linarith

/-- The safe-region constant `C₀ = 272 + 48/σ₀ + 32/σ₀²`. -/
noncomputable def gpdZeroConst (σ₀ : ℝ) : ℝ := 272 + 48 / σ₀ + 32 / σ₀ ^ 2

lemma gpdZeroConst_pos (hσ₀ : 0 < σ₀) : 0 < gpdZeroConst σ₀ := by
  unfold gpdZeroConst; positivity

lemma pow_le_one_add_cube {y : ℝ} (hy : 0 ≤ y) :
    y ≤ 1 + y ^ 3 ∧ y ^ 2 ≤ 1 + y ^ 3 := by
  rcases le_or_gt y 1 with h1 | h1
  · constructor <;> nlinarith [pow_nonneg hy 3, sq_nonneg y]
  · constructor
    · have : y ≤ y ^ 2 := by nlinarith
      have : y ^ 2 ≤ y ^ 3 := by nlinarith
      linarith
    · have : y ^ 2 ≤ y ^ 3 := by nlinarith
      linarith

/-- **Two-sided Hessian bound on the safe region `ξ x / σ ≥ -1/2`.** -/
lemma abs_gpdHessAll_le_of_ge_neg_half (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀)
    {x : ℝ} (hx : 0 ≤ x) (ht : -(1 / 2) ≤ θ.1 * (x / θ.2)) :
    |gpdHessXiXiAll θ.1 θ.2 x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x ∧
    |gpdHessXiSigma θ.1 θ.2 x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x ∧
    |gpdHessSigmaSigma θ.1 θ.2 x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x := by
  obtain ⟨hξ1, hξ2, hσ1, hσ2⟩ := bounds_of_mem_gpdNbhdZero hθ
  have hσ : 0 < θ.2 := by linarith
  set y := x / σ₀ with hy_def
  have hy0 : 0 ≤ y := div_nonneg hx hσ₀.le
  have hD : 0 < gpdDomZero σ₀ x := by linarith [one_le_gpdDomZero hσ₀ hx]
  obtain ⟨hy1, hy2⟩ := pow_le_one_add_cube hy0
  have hy3 : y ^ 3 ≤ 1 + y ^ 3 := by linarith
  have hxs : x / θ.2 ≤ 2 * y := by
    rw [hy_def, div_le_iff₀ hσ]
    have : 0 ≤ x / σ₀ := hy0
    have e : 2 * (x / σ₀) * θ.2 = x * (2 * θ.2 / σ₀) := by ring
    rw [e]
    have h2 : 1 ≤ 2 * θ.2 / σ₀ := by rw [one_le_div hσ₀]; linarith
    nlinarith
  have hxs0 : 0 ≤ x / θ.2 := div_nonneg hx hσ.le
  have hden : θ.2 / 2 ≤ θ.2 + θ.1 * x := by
    have h1 : 1 / 2 ≤ 1 + θ.1 * (x / θ.2) := by linarith
    have e : θ.2 + θ.1 * x = θ.2 * (1 + θ.1 * (x / θ.2)) := by field_simp
    rw [e]; nlinarith
  have hden_pos : 0 < θ.2 + θ.1 * x := by linarith
  set w := x / (θ.2 + θ.1 * x)
  have hw0 : 0 ≤ w := div_nonneg hx hden_pos.le
  have hw_le : w ≤ 4 * y := by
    have h1 : w ≤ 2 * (x / θ.2) := by
      rw [show w = x / (θ.2 + θ.1 * x) from rfl, div_le_iff₀ hden_pos]
      have e : 2 * (x / θ.2) * (θ.2 + θ.1 * x) = x * (2 * (θ.2 + θ.1 * x) / θ.2) := by ring
      rw [e]
      have h2 : 1 ≤ 2 * (θ.2 + θ.1 * x) / θ.2 := by rw [one_le_div hσ]; linarith
      nlinarith
    linarith
  have hinvσ : 1 / θ.2 ≤ 2 / σ₀ := by rw [div_le_div_iff₀ hσ hσ₀]; linarith
  have hinvσ2 : 1 / θ.2 ^ 2 ≤ 2 / σ₀ ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hσ) (sq_pos_of_pos hσ₀)]
    nlinarith
  have hC1 : 272 ≤ gpdZeroConst σ₀ := by
    unfold gpdZeroConst
    linarith [show (0 : ℝ) ≤ 48 / σ₀ + 32 / σ₀ ^ 2 by positivity]
  have hC2 : 48 / σ₀ ≤ gpdZeroConst σ₀ := by
    unfold gpdZeroConst
    linarith [show (0 : ℝ) ≤ 272 + 32 / σ₀ ^ 2 by positivity]
  have hC3 : 32 / σ₀ ^ 2 ≤ gpdZeroConst σ₀ := by
    unfold gpdZeroConst
    linarith [show (0 : ℝ) ≤ 272 + 48 / σ₀ by positivity]
  refine ⟨?_, ?_, ?_⟩
  · unfold gpdHessXiXiAll
    have hcube := abs_log1pCube_le_of_ge_neg_half ht
    have h1 : |(x / θ.2) ^ 3 * log1pCube (θ.1 * (x / θ.2))| ≤ 256 * y ^ 3 := by
      rw [abs_mul, abs_pow, abs_of_nonneg hxs0]
      have h3 : (x / θ.2) ^ 3 ≤ (2 * y) ^ 3 := pow_le_pow_left₀ hxs0 hxs 3
      calc (x / θ.2) ^ 3 * |log1pCube (θ.1 * (x / θ.2))|
          ≤ (2 * y) ^ 3 * 32 := mul_le_mul h3 hcube (abs_nonneg _) (by positivity)
        _ = 256 * y ^ 3 := by ring
    have h2 : |w ^ 2| ≤ 16 * y ^ 2 := by
      rw [abs_pow, abs_of_nonneg hw0]
      calc w ^ 2 ≤ (4 * y) ^ 2 := pow_le_pow_left₀ hw0 hw_le 2
        _ = 16 * y ^ 2 := by ring
    calc |(x / θ.2) ^ 3 * log1pCube (θ.1 * (x / θ.2)) + w ^ 2|
        ≤ |(x / θ.2) ^ 3 * log1pCube (θ.1 * (x / θ.2))| + |w ^ 2| := abs_add_le _ _
      _ ≤ 256 * y ^ 3 + 16 * y ^ 2 := add_le_add h1 h2
      _ ≤ 272 * (1 + y ^ 3) := by linarith
      _ ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x := by
          unfold gpdDomZero; rw [← hy_def]; exact mul_le_mul_of_nonneg_right hC1 (by positivity)
  · unfold gpdHessXiSigma
    rw [abs_div, abs_of_pos hσ, div_eq_mul_one_div]
    have hnum : |w - (1 + θ.1) * w ^ 2| ≤ 24 * (1 + y ^ 3) := by
      have hw2 : w ^ 2 ≤ 16 * y ^ 2 := by
        calc w ^ 2 ≤ (4 * y) ^ 2 := pow_le_pow_left₀ hw0 hw_le 2
          _ = 16 * y ^ 2 := by ring
      have h1 : |(1 + θ.1) * w ^ 2| ≤ 20 * y ^ 2 := by
        rw [abs_mul, abs_of_pos (by linarith : 0 < 1 + θ.1), abs_pow, abs_of_nonneg hw0]
        calc (1 + θ.1) * w ^ 2 ≤ (5 / 4) * (16 * y ^ 2) :=
              mul_le_mul (by linarith) hw2 (sq_nonneg _) (by norm_num)
          _ = 20 * y ^ 2 := by ring
      calc |w - (1 + θ.1) * w ^ 2| ≤ |w| + |(1 + θ.1) * w ^ 2| := abs_sub _ _
        _ = w + |(1 + θ.1) * w ^ 2| := by rw [abs_of_nonneg hw0]
        _ ≤ 4 * y + 20 * y ^ 2 := by linarith
        _ ≤ 24 * (1 + y ^ 3) := by linarith
    calc |w - (1 + θ.1) * w ^ 2| * (1 / θ.2)
        ≤ (24 * (1 + y ^ 3)) * (2 / σ₀) :=
          mul_le_mul hnum hinvσ (by positivity) (by positivity)
      _ = (48 / σ₀) * (1 + y ^ 3) := by ring
      _ ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x := by
          unfold gpdDomZero; rw [← hy_def]; exact mul_le_mul_of_nonneg_right hC2 (by positivity)
  · unfold gpdHessSigmaSigma
    rw [abs_div, abs_pow, abs_of_pos hσ, div_eq_mul_one_div]
    have hnum : |1 - 2 * (1 + θ.1) * w + θ.1 * (1 + θ.1) * w ^ 2| ≤ 16 * (1 + y ^ 3) := by
      have h1 : |2 * (1 + θ.1) * w| ≤ 10 * y := by
        rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos (by linarith : 0 < 1 + θ.1),
          abs_of_nonneg hw0]
        calc 2 * (1 + θ.1) * w ≤ (5 / 2) * (4 * y) :=
              mul_le_mul (by linarith) hw_le hw0 (by norm_num)
          _ = 10 * y := by ring
      have hw2 : w ^ 2 ≤ 16 * y ^ 2 := by
        calc w ^ 2 ≤ (4 * y) ^ 2 := pow_le_pow_left₀ hw0 hw_le 2
          _ = 16 * y ^ 2 := by ring
      have h2 : |θ.1 * (1 + θ.1) * w ^ 2| ≤ 5 * y ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 + θ.1), abs_pow, abs_of_nonneg hw0]
        have hξabs : |θ.1| ≤ 1 / 4 := abs_le.2 ⟨hξ1, hξ2⟩
        have h12 : |θ.1| * (1 + θ.1) ≤ 5 / 16 := by
          calc |θ.1| * (1 + θ.1) ≤ (1 / 4) * (5 / 4) :=
                mul_le_mul hξabs (by linarith) (by linarith) (by norm_num)
            _ = 5 / 16 := by norm_num
        calc |θ.1| * (1 + θ.1) * w ^ 2 ≤ (5 / 16) * (16 * y ^ 2) :=
              mul_le_mul h12 hw2 (sq_nonneg _) (by norm_num)
          _ = 5 * y ^ 2 := by ring
      calc |1 - 2 * (1 + θ.1) * w + θ.1 * (1 + θ.1) * w ^ 2|
          ≤ |1 - 2 * (1 + θ.1) * w| + |θ.1 * (1 + θ.1) * w ^ 2| := abs_add_le _ _
        _ ≤ (|1| + |2 * (1 + θ.1) * w|) + |θ.1 * (1 + θ.1) * w ^ 2| :=
            add_le_add (abs_sub _ _) le_rfl
        _ ≤ 1 + 10 * y + 5 * y ^ 2 := by rw [abs_one]; linarith
        _ ≤ 16 * (1 + y ^ 3) := by linarith [pow_nonneg hy0 3]
    calc |1 - 2 * (1 + θ.1) * w + θ.1 * (1 + θ.1) * w ^ 2| * (1 / θ.2 ^ 2)
        ≤ (16 * (1 + y ^ 3)) * (2 / σ₀ ^ 2) :=
          mul_le_mul hnum hinvσ2 (by positivity) (by positivity)
      _ = (32 / σ₀ ^ 2) * (1 + y ^ 3) := by ring
      _ ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x := by
          unfold gpdDomZero; rw [← hy_def]; exact mul_le_mul_of_nonneg_right hC3 (by positivity)

/-- **Uniform one-sided Hessian bound near `(0, σ₀)`** (all signs of `ξ` in `[-1/4, 1/4]`):
for any `θ ∈ gpdNbhdZero σ₀` and `x ≥ 0` with `σ + ξ x > 0`,
`tᵀ H(θ, x) t ≤ 2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * |t|²`. -/
lemma gpdHessAll_quad_le_zero (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀)
    {x : ℝ} (hx : 0 ≤ x) (hu : 0 < θ.2 + θ.1 * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * gpdHessXiXiAll θ.1 θ.2 x + 2 * t₁ * t₂ * gpdHessXiSigma θ.1 θ.2 x +
        t₂ ^ 2 * gpdHessSigmaSigma θ.1 θ.2 x ≤
      2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * (t₁ ^ 2 + t₂ ^ 2) := by
  by_cases ht : -(1 / 2) ≤ θ.1 * (x / θ.2)
  · obtain ⟨h1, h2, h3⟩ := abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht
    have hq := quad_le_of_abs_le h1 h2 h3 t₁ t₂
    linarith
  · push Not at ht
    obtain ⟨hξ1, hξ2, hσ1, hσ2⟩ := bounds_of_mem_gpdNbhdZero hθ
    have hσ : 0 < θ.2 := by linarith
    have hξneg : θ.1 < 0 := by
      by_contra hnn
      push Not at hnn
      have : 0 ≤ θ.1 * (x / θ.2) := by positivity
      linarith
    rw [gpdHessXiXiAll_of_ne hξneg.ne hσ hu]
    have hq := gpdHess_quad_le (by linarith) hξneg hσ hx hu t₁ t₂
    set y := x / σ₀ with hy_def
    have hy0 : 0 ≤ y := div_nonneg hx hσ₀.le
    have hxs : x / θ.2 ≤ 2 * y := by
      rw [hy_def, div_le_iff₀ hσ]
      have e : 2 * (x / σ₀) * θ.2 = x * (2 * θ.2 / σ₀) := by ring
      rw [e]
      have h2 : 1 ≤ 2 * θ.2 / σ₀ := by rw [one_le_div hσ₀]; linarith
      nlinarith
    set invξ := (-θ.1)⁻¹ with hinvξ_def
    have hnegξ : 0 < -θ.1 := neg_pos.2 hξneg
    have hinvξ_pos : 0 < invξ := inv_pos.2 hnegξ
    have hinvξ_ge4 : 4 ≤ invξ := by
      rw [hinvξ_def, le_inv_comm₀ four_pos hnegξ]; linarith
    have hinvξ_le : invξ ≤ 4 * y := by
      have h1 : 1 / 2 < (-θ.1) * (x / θ.2) := by linarith
      have h2 : invξ < 2 * (x / θ.2) := by
        rw [hinvξ_def, inv_eq_one_div, div_lt_iff₀ hnegξ]; linarith
      linarith
    have hy_gt1 : 1 ≤ y := by linarith
    have hden : 3 * invξ ≤ 4 * (-(1 + θ.1) / θ.1) := by
      have e : -(1 + θ.1) / θ.1 = (1 + θ.1) * invξ := by
        rw [hinvξ_def, div_eq_mul_inv, ← neg_inv]; ring
      rw [e]; nlinarith
    have hden_pos : 0 < 4 * (-(1 + θ.1) / θ.1) := by linarith
    set s := t₂ / θ.2
    have hlin : 2 / θ.1 ^ 2 * (t₁ - θ.1 * s) + (4 / θ.1 + 2) * s =
        (2 * invξ ^ 2) * t₁ + (2 - 2 * invξ) * s := by
      rw [hinvξ_def]
      have hne : θ.1 ≠ 0 := hξneg.ne
      field_simp
      ring
    have hnum_le : ((2 * invξ ^ 2) * t₁ + (2 - 2 * invξ) * s) ^ 2 ≤
        8 * invξ ^ 4 * t₁ ^ 2 + 18 * invξ ^ 2 * s ^ 2 := by
      have hsq : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := fun u v => by
        nlinarith [sq_nonneg (u - v)]
      have h1 := hsq ((2 * invξ ^ 2) * t₁) ((2 - 2 * invξ) * s)
      have h2 : (2 - 2 * invξ) ^ 2 ≤ 9 * invξ ^ 2 := by nlinarith
      have h3 : 2 * ((2 - 2 * invξ) * s) ^ 2 ≤ 18 * invξ ^ 2 * s ^ 2 := by
        rw [mul_pow]; nlinarith [sq_nonneg s]
      have h4 : 2 * ((2 * invξ ^ 2) * t₁) ^ 2 = 8 * invξ ^ 4 * t₁ ^ 2 := by ring
      linarith
    have hdiv_le : ((2 * invξ ^ 2) * t₁ + (2 - 2 * invξ) * s) ^ 2 / (4 * (-(1 + θ.1) / θ.1)) ≤
        (8 / 3) * invξ ^ 3 * t₁ ^ 2 + 6 * invξ * s ^ 2 := by
      have h1 : ((2 * invξ ^ 2) * t₁ + (2 - 2 * invξ) * s) ^ 2 / (4 * (-(1 + θ.1) / θ.1)) ≤
          (8 * invξ ^ 4 * t₁ ^ 2 + 18 * invξ ^ 2 * s ^ 2) / (3 * invξ) := by
        calc _ ≤ (8 * invξ ^ 4 * t₁ ^ 2 + 18 * invξ ^ 2 * s ^ 2) / (4 * (-(1 + θ.1) / θ.1)) :=
              div_le_div_of_nonneg_right hnum_le hden_pos.le
          _ ≤ (8 * invξ ^ 4 * t₁ ^ 2 + 18 * invξ ^ 2 * s ^ 2) / (3 * invξ) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      have e : (8 * invξ ^ 4 * t₁ ^ 2 + 18 * invξ ^ 2 * s ^ 2) / (3 * invξ) =
          (8 / 3) * invξ ^ 3 * t₁ ^ 2 + 6 * invξ * s ^ 2 := by
        field_simp [hinvξ_pos.ne']; ring
      linarith
    have hs2 : s ^ 2 ≤ 2 / σ₀ ^ 2 * t₂ ^ 2 := by
      simp only [s, div_pow]
      have hinvσ2 : 1 / θ.2 ^ 2 ≤ 2 / σ₀ ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hσ) (sq_pos_of_pos hσ₀)]
        have h1 : (7 * σ₀ / 8) ^ 2 ≤ θ.2 ^ 2 := pow_le_pow_left₀ (by positivity) hσ1 2
        linarith [show 0 ≤ σ₀ ^ 2 by positivity]
      calc t₂ ^ 2 / θ.2 ^ 2 = t₂ ^ 2 * (1 / θ.2 ^ 2) := by ring
        _ ≤ t₂ ^ 2 * (2 / σ₀ ^ 2) := mul_le_mul_of_nonneg_left hinvσ2 (sq_nonneg _)
        _ = 2 / σ₀ ^ 2 * t₂ ^ 2 := by ring
    have hinv3 : (8 / 3) * invξ ^ 3 ≤ 192 * (1 + y ^ 3) := by
      have h3 : invξ ^ 3 ≤ (4 * y) ^ 3 := pow_le_pow_left₀ hinvξ_pos.le hinvξ_le 3
      have h4 : (4 * y) ^ 3 = 64 * y ^ 3 := by ring
      linarith [pow_nonneg hy0 3]
    have hinv1 : 6 * invξ + 1 ≤ 25 * (1 + y ^ 3) := by
      have hy13 : y ≤ 1 + y ^ 3 := (pow_le_one_add_cube hy0).1
      linarith
    have ht1_le : (8 / 3) * invξ ^ 3 * t₁ ^ 2 ≤ 192 * (1 + y ^ 3) * t₁ ^ 2 :=
      mul_le_mul_of_nonneg_right hinv3 (sq_nonneg _)
    have ht2_le : (6 * invξ + 1) * s ^ 2 ≤ 50 / σ₀ ^ 2 * (1 + y ^ 3) * t₂ ^ 2 := by
      calc (6 * invξ + 1) * s ^ 2
          ≤ (25 * (1 + y ^ 3)) * (2 / σ₀ ^ 2 * t₂ ^ 2) :=
            mul_le_mul hinv1 hs2 (sq_nonneg _) (by positivity)
        _ = 50 / σ₀ ^ 2 * (1 + y ^ 3) * t₂ ^ 2 := by ring
    have h192 : 192 ≤ 2 * gpdZeroConst σ₀ := by
      unfold gpdZeroConst
      linarith [show (0 : ℝ) ≤ 48 / σ₀ + 32 / σ₀ ^ 2 by positivity]
    have h50 : 50 / σ₀ ^ 2 ≤ 2 * gpdZeroConst σ₀ := by
      unfold gpdZeroConst
      have h1 : 50 / σ₀ ^ 2 ≤ 64 / σ₀ ^ 2 := by gcongr; norm_num
      have h2 : 2 * (32 / σ₀ ^ 2) = 64 / σ₀ ^ 2 := by ring
      linarith [show (0 : ℝ) ≤ 272 + 48 / σ₀ by positivity]
    have hfinal : 192 * (1 + y ^ 3) * t₁ ^ 2 + 50 / σ₀ ^ 2 * (1 + y ^ 3) * t₂ ^ 2 ≤
        2 * gpdZeroConst σ₀ * (1 + y ^ 3) * (t₁ ^ 2 + t₂ ^ 2) := by
      have h1y3 : 0 ≤ 1 + y ^ 3 := by positivity
      have a1 : 192 * (1 + y ^ 3) * t₁ ^ 2 ≤ 2 * gpdZeroConst σ₀ * (1 + y ^ 3) * t₁ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h192 h1y3) (sq_nonneg _)
      have a2 : 50 / σ₀ ^ 2 * (1 + y ^ 3) * t₂ ^ 2 ≤ 2 * gpdZeroConst σ₀ * (1 + y ^ 3) * t₂ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h50 h1y3) (sq_nonneg _)
      linarith
    rw [hlin] at hq
    unfold gpdDomZero; rw [← hy_def]
    linarith

lemma segHess_quad_le_zero (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀)
    {x : ℝ} (hx : 0 ≤ x) (h1 : 0 < θ.2 + θ.1 * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * segHess gpdHessXiXiAll 0 σ₀ θ x +
        2 * t₁ * t₂ * segHess gpdHessXiSigma 0 σ₀ θ x +
        t₂ ^ 2 * segHess gpdHessSigmaSigma 0 σ₀ θ x ≤
      2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * (t₁ ^ 2 + t₂ ^ 2) := by
  have h0 : 0 < σ₀ + 0 * x := by simpa using hσ₀
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, 0 < σ₀ + s * (θ.2 - σ₀) ∧
      0 < (σ₀ + s * (θ.2 - σ₀)) + (0 + s * (θ.1 - 0)) * x := fun s hs =>
    ⟨by linarith [(segment_mem_gpdNbhdZero hσ₀ hθ hs).2.1], seg_support_pos (ξ₀ := 0) h0 h1 hs⟩
  have hi : ∀ (H : ℝ → ℝ → ℝ → ℝ),
      (∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
        ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
      IntervalIntegrable (fun s => H (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x) volume 0 1 := by
    intro H hH
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    intro s hs
    exact ((hH _ (hseg s hs).1 (hseg s hs).2).comp
      (f := fun s => (0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀), x)) (by fun_prop)).continuousWithinAt
  have iXX := hi gpdHessXiXiAll (fun _ h1 h2 => continuousAt_gpdHessXiXiAll₃ h1 h2)
  have iXS := hi gpdHessXiSigma (fun _ h1 h2 => continuousAt_gpdHessXiSigma₃ h1 h2)
  have iSS := hi gpdHessSigmaSigma (fun _ h1 h2 => continuousAt_gpdHessSigmaSigma₃ h1 h2)
  unfold segHess
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (iXX.const_mul _) (iXS.const_mul _),
    ← intervalIntegral.integral_add ((iXX.const_mul _).add (iXS.const_mul _)) (iSS.const_mul _)]
  have hconst : 2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * (t₁ ^ 2 + t₂ ^ 2) =
      ∫ _s in (0 : ℝ)..1, (2 * gpdZeroConst σ₀ * gpdDomZero σ₀ x * (t₁ ^ 2 + t₂ ^ 2)) := by
    simp
  rw [hconst]
  refine intervalIntegral.integral_mono_on zero_le_one
    (((iXX.const_mul _).add (iXS.const_mul _)).add (iSS.const_mul _))
    intervalIntegrable_const fun s hs => ?_
  exact gpdHessAll_quad_le_zero hσ₀ (segment_mem_gpdNbhdZero hσ₀ hθ hs) hx (hseg s hs).2 t₁ t₂

/-- Two-sided segment-averaged Hessian bound when `-(1/2) ≤ θ.1 * (x / θ.2)` (and `θ ∈ gpdNbhdZero`). -/
lemma abs_segHess_le_zero (hσ₀ : 0 < σ₀) {H : ℝ → ℝ → ℝ → ℝ}
    (hH : ∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    (hHb : ∀ θ ∈ gpdNbhdZero σ₀, ∀ x, 0 ≤ x → -(1 / 2) ≤ θ.1 * (x / θ.2) →
      |H θ.1 θ.2 x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdZero σ₀) {x : ℝ} (hx : 0 ≤ x)
    (hsafe : |θ.1| * x ≤ σ₀ / 4) :
    |segHess H 0 σ₀ θ x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x := by
  have hseg_safe : ∀ s ∈ Icc (0 : ℝ) 1,
      -(1 / 2) ≤ (0 + s * (θ.1 - 0)) * (x / (σ₀ + s * (θ.2 - σ₀))) ∧
      0 < σ₀ + s * (θ.2 - σ₀) ∧
      0 < (σ₀ + s * (θ.2 - σ₀)) + (0 + s * (θ.1 - 0)) * x := by
    intro s hs
    have hmem := segment_mem_gpdNbhdZero hσ₀ hθ hs
    have hσs : 7 * σ₀ / 8 ≤ σ₀ + s * (θ.2 - σ₀) := hmem.2.1
    have hσs_pos : 0 < σ₀ + s * (θ.2 - σ₀) := by linarith
    have habs : |(0 + s * (θ.1 - 0)) * x| ≤ σ₀ / 4 := by
      simp only [zero_add, sub_zero, abs_mul, abs_of_nonneg hs.1, abs_of_nonneg hx]
      calc s * |θ.1| * x = s * (|θ.1| * x) := by ring
        _ ≤ 1 * (σ₀ / 4) := mul_le_mul hs.2 hsafe (by positivity) zero_le_one
        _ = σ₀ / 4 := one_mul _
    have hlo : -(σ₀ / 4) ≤ (0 + s * (θ.1 - 0)) * x := (abs_le.1 habs).1
    have h1 : -(1 / 2) ≤ (0 + s * (θ.1 - 0)) * (x / (σ₀ + s * (θ.2 - σ₀))) := by
      rw [← mul_div_assoc, le_div_iff₀ hσs_pos]; linarith
    exact ⟨h1, hσs_pos, by linarith⟩
  unfold segHess
  rw [intervalIntegral.integral_of_le zero_le_one]
  calc |∫ s in Ioc (0 : ℝ) 1, H (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x|
      ≤ ∫ s in Ioc (0 : ℝ) 1, |H (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _s in Ioc (0 : ℝ) 1, (gpdZeroConst σ₀ * gpdDomZero σ₀ x) := by
        refine setIntegral_mono_on ?_ (integrableOn_const (hs := measure_Ioc_lt_top.ne))
          measurableSet_Ioc fun s hs => ?_
        · have hc : ContinuousOn (fun s => H (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x) (Icc 0 1) := by
            intro s hs
            exact ((hH _ (hseg_safe s hs).2.1 (hseg_safe s hs).2.2).comp
              (f := fun s => (0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀), x)) (by fun_prop)).continuousWithinAt
          exact (hc.norm.integrableOn_Icc).mono_set Ioc_subset_Icc_self
        · exact hHb _ (segment_mem_gpdNbhdZero hσ₀ hθ (Ioc_subset_Icc_self hs)) x hx
            (hseg_safe s (Ioc_subset_Icc_self hs)).1
    _ = gpdZeroConst σ₀ * gpdDomZero σ₀ x := by simp

end ZeroNbhd

/-! ### Moments, score CLT, and strong laws at `ξ₀ = 0` -/

section ZeroMoments

variable {σ₀ : ℝ}

/-- Integrability of `(x/σ₀)^k` under `GPD(0, σ₀)`. -/
lemma integrable_div_pow_gpdZero (hσ₀ : 0 < σ₀) (k : ℕ) :
    Integrable (fun x : ℝ => (x / σ₀) ^ k) (gpdMeasure 0 σ₀) := by
  have hm : Measurable fun x : ℝ => (x / σ₀) ^ k := by fun_prop
  rw [gpdMeasure, integrable_map_measure hm.aestronglyMeasurable
    (measurable_gpdTransform 0 σ₀).aemeasurable]
  refine (integrable_pow_expMeasure k).congr (ae_of_all _ fun t => ?_)
  simp [gpdTransform, mul_div_cancel_left₀ _ hσ₀.ne']

/-- `E[(X/σ₀)^k] = k!` for `X ~ GPD(0, σ₀)`. -/
lemma integral_div_pow_gpdZero (hσ₀ : 0 < σ₀) (k : ℕ) :
    ∫ x, (x / σ₀) ^ k ∂gpdMeasure 0 σ₀ = (k.factorial : ℝ) := by
  have hm : Measurable fun x : ℝ => (x / σ₀) ^ k := by fun_prop
  rw [gpdMeasure, integral_map (measurable_gpdTransform 0 σ₀).aemeasurable hm.aestronglyMeasurable]
  have e : (fun t => (gpdTransform 0 σ₀ t / σ₀) ^ k) = fun t => t ^ k := by
    funext t; simp [gpdTransform, mul_div_cancel_left₀ _ hσ₀.ne']
  rw [e, integral_pow_expMeasure k]

lemma integrable_gpdDomZero (hσ₀ : 0 < σ₀) :
    Integrable (gpdDomZero σ₀) (gpdMeasure 0 σ₀) :=
  (integrable_const (1 : ℝ)).add (integrable_div_pow_gpdZero hσ₀ 3)

/-- The tail `gpdDomZero · 1{M < x}` of the dominating function. -/
noncomputable def gpdDomZeroTail (σ₀ M x : ℝ) : ℝ :=
  Set.indicator {y | M < y} (gpdDomZero σ₀) x

lemma measurable_gpdDomZeroTail (σ₀ M : ℝ) : Measurable (gpdDomZeroTail σ₀ M) :=
  (measurable_gpdDomZero σ₀).indicator (measurableSet_lt measurable_const measurable_id)

lemma gpdDomZeroTail_of_le {M x : ℝ} (h : x ≤ M) : gpdDomZeroTail σ₀ M x = 0 :=
  Set.indicator_of_notMem (by simp only [mem_ofPred_eq, not_lt]; exact h) _

lemma gpdDomZeroTail_of_lt {M x : ℝ} (h : M < x) : gpdDomZeroTail σ₀ M x = gpdDomZero σ₀ x :=
  Set.indicator_of_mem (show x ∈ {y | M < y} from h) _

lemma gpdDomZeroTail_nonneg (hσ₀ : 0 < σ₀) {M x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gpdDomZeroTail σ₀ M x := by
  by_cases h : M < x
  · rw [gpdDomZeroTail_of_lt h]; linarith [one_le_gpdDomZero hσ₀ hx]
  · rw [gpdDomZeroTail_of_le (not_lt.1 h)]

lemma integrable_gpdDomZeroTail (hσ₀ : 0 < σ₀) (M : ℝ) :
    Integrable (gpdDomZeroTail σ₀ M) (gpdMeasure 0 σ₀) :=
  (integrable_gpdDomZero hσ₀).indicator (measurableSet_lt measurable_const measurable_id)

lemma tendsto_integral_gpdDomZeroTail (hσ₀ : 0 < σ₀) :
    Tendsto (fun k : ℕ => ∫ x, gpdDomZeroTail σ₀ (k : ℝ) x ∂gpdMeasure 0 σ₀) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun x => |gpdDomZero σ₀ x|)
    (F := fun (k : ℕ) x => gpdDomZeroTail σ₀ (k : ℝ) x) (f := fun _ => 0)
    (fun k => (measurable_gpdDomZeroTail σ₀ k).aestronglyMeasurable)
    (integrable_gpdDomZero hσ₀).abs
    (fun k => ae_of_all _ fun x =>
      (norm_indicator_le_norm_self (s := {y | (k : ℝ) < y}) (gpdDomZero σ₀) x).trans_eq
        (Real.norm_eq_abs _)) ?_
  · simpa using h
  filter_upwards with x
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (x + 1))] with k hk
  exact (gpdDomZeroTail_of_le (by linarith)).symm

/-- Moments of the score and Hessian at `ξ₀ = 0`. -/
lemma integral_expScoreXi (hσ₀ : 0 < σ₀) :
    ∫ x, expScoreXi σ₀ x ∂gpdMeasure 0 σ₀ = 0 := by
  unfold expScoreXi
  have h1 := integrable_div_pow_gpdZero hσ₀ 1
  have h2 := integrable_div_pow_gpdZero hσ₀ 2
  rw [integral_sub (h2.div_const 2) (h1.congr (ae_of_all _ fun x => by simp)),
    integral_div, integral_div_pow_gpdZero hσ₀ 2]
  have h1' : ∫ x, x / σ₀ ∂gpdMeasure 0 σ₀ = 1 := by
    simpa using integral_div_pow_gpdZero hσ₀ 1
  rw [h1']
  norm_num

lemma integral_expScoreSigma (hσ₀ : 0 < σ₀) :
    ∫ x, expScoreSigma σ₀ x ∂gpdMeasure 0 σ₀ = 0 := by
  unfold expScoreSigma
  have h1 : Integrable (fun x => x / σ₀) (gpdMeasure 0 σ₀) :=
    (integrable_div_pow_gpdZero hσ₀ 1).congr (ae_of_all _ fun x => by simp)
  rw [integral_div, integral_sub h1 (integrable_const 1)]
  have h1' : ∫ x, x / σ₀ ∂gpdMeasure 0 σ₀ = 1 := by
    simpa using integral_div_pow_gpdZero hσ₀ 1
  rw [h1', integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, zero_div]

lemma memLp_lin_expScore (hσ₀ : 0 < σ₀) (u v : ℝ) :
    MemLp (fun x => u * expScoreXi σ₀ x + v * expScoreSigma σ₀ x) 2 (gpdMeasure 0 σ₀) := by
  have hm : Measurable fun x => u * expScoreXi σ₀ x + v * expScoreSigma σ₀ x := by
    unfold expScoreXi expScoreSigma; fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have hpoly : ∀ x, (u * expScoreXi σ₀ x + v * expScoreSigma σ₀ x) ^ 2 =
      (u ^ 2 / 4) * (x / σ₀) ^ 4 + (u * (v / σ₀ - u)) * (x / σ₀) ^ 3 +
      ((v / σ₀ - u) ^ 2 - u * v / σ₀) * (x / σ₀) ^ 2 +
      (-2 * (v / σ₀) * (v / σ₀ - u)) * (x / σ₀) ^ 1 + (v / σ₀) ^ 2 := by
    intro x; unfold expScoreXi expScoreSigma; ring
  simp_rw [hpoly]
  exact (((((integrable_div_pow_gpdZero hσ₀ 4).const_mul _).add
    ((integrable_div_pow_gpdZero hσ₀ 3).const_mul _)).add
    ((integrable_div_pow_gpdZero hσ₀ 2).const_mul _)).add
    ((integrable_div_pow_gpdZero hσ₀ 1).const_mul _)).add (integrable_const _)

lemma integral_lin_expScore_sq (hσ₀ : 0 < σ₀) (u v : ℝ) :
    ∫ x, (u * expScoreXi σ₀ x + v * expScoreSigma σ₀ x) ^ 2 ∂gpdMeasure 0 σ₀ =
      gpdInfoQuad 0 σ₀ u v := by
  have hpoly : ∀ x, (u * expScoreXi σ₀ x + v * expScoreSigma σ₀ x) ^ 2 =
      (u ^ 2 / 4) * (x / σ₀) ^ 4 + (u * (v / σ₀ - u)) * (x / σ₀) ^ 3 +
      ((v / σ₀ - u) ^ 2 - u * v / σ₀) * (x / σ₀) ^ 2 +
      (-2 * (v / σ₀) * (v / σ₀ - u)) * (x / σ₀) ^ 1 + (v / σ₀) ^ 2 := by
    intro x; unfold expScoreXi expScoreSigma; ring
  simp_rw [hpoly]
  have i4 : Integrable (fun x : ℝ => (u ^ 2 / 4) * (x / σ₀) ^ 4) (gpdMeasure 0 σ₀) :=
    (integrable_div_pow_gpdZero hσ₀ 4).const_mul _
  have i3 : Integrable (fun x : ℝ => (u * (v / σ₀ - u)) * (x / σ₀) ^ 3) (gpdMeasure 0 σ₀) :=
    (integrable_div_pow_gpdZero hσ₀ 3).const_mul _
  have i2 : Integrable (fun x : ℝ => ((v / σ₀ - u) ^ 2 - u * v / σ₀) * (x / σ₀) ^ 2) (gpdMeasure 0 σ₀) :=
    (integrable_div_pow_gpdZero hσ₀ 2).const_mul _
  have i1 : Integrable (fun x : ℝ => (-2 * (v / σ₀) * (v / σ₀ - u)) * (x / σ₀) ^ 1) (gpdMeasure 0 σ₀) :=
    (integrable_div_pow_gpdZero hσ₀ 1).const_mul _
  have i0 : Integrable (fun _ : ℝ => (v / σ₀) ^ 2) (gpdMeasure 0 σ₀) := integrable_const _
  have i43 : Integrable (fun x : ℝ => (u ^ 2 / 4) * (x / σ₀) ^ 4 +
      (u * (v / σ₀ - u)) * (x / σ₀) ^ 3) (gpdMeasure 0 σ₀) := i4.add i3
  have i432 : Integrable (fun x : ℝ => (u ^ 2 / 4) * (x / σ₀) ^ 4 +
      (u * (v / σ₀ - u)) * (x / σ₀) ^ 3 +
      ((v / σ₀ - u) ^ 2 - u * v / σ₀) * (x / σ₀) ^ 2) (gpdMeasure 0 σ₀) := i43.add i2
  have i4321 : Integrable (fun x : ℝ => (u ^ 2 / 4) * (x / σ₀) ^ 4 +
      (u * (v / σ₀ - u)) * (x / σ₀) ^ 3 +
      ((v / σ₀ - u) ^ 2 - u * v / σ₀) * (x / σ₀) ^ 2 +
      (-2 * (v / σ₀) * (v / σ₀ - u)) * (x / σ₀) ^ 1) (gpdMeasure 0 σ₀) := i432.add i1
  rw [integral_add i4321 i0, integral_add i432 i1, integral_add i43 i2, integral_add i4 i3,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_div_pow_gpdZero hσ₀ 4, integral_div_pow_gpdZero hσ₀ 3,
    integral_div_pow_gpdZero hσ₀ 2, integral_div_pow_gpdZero hσ₀ 1,
    integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold gpdInfoQuad
  norm_num [Nat.factorial]
  field_simp [hσ₀.ne']
  ring

lemma integrable_gpdHessXiXiAll_zero (hσ₀ : 0 < σ₀) :
    Integrable (gpdHessXiXiAll 0 σ₀) (gpdMeasure 0 σ₀) := by
  have e : gpdHessXiXiAll 0 σ₀ = fun x => -(2 / 3) * (x / σ₀) ^ 3 + (x / σ₀) ^ 2 :=
    funext fun x => gpdHessXiXiAll_zero σ₀ x
  rw [e]
  exact ((integrable_div_pow_gpdZero hσ₀ 3).const_mul _).add (integrable_div_pow_gpdZero hσ₀ 2)

lemma integral_gpdHessXiXiAll_zero (hσ₀ : 0 < σ₀) :
    ∫ x, gpdHessXiXiAll 0 σ₀ x ∂gpdMeasure 0 σ₀ = -2 := by
  simp_rw [gpdHessXiXiAll_zero]
  rw [integral_add ((integrable_div_pow_gpdZero hσ₀ 3).const_mul _) (integrable_div_pow_gpdZero hσ₀ 2),
    integral_const_mul, integral_div_pow_gpdZero hσ₀ 3, integral_div_pow_gpdZero hσ₀ 2]
  norm_num [Nat.factorial]

lemma integrable_gpdHessXiSigma_zero (hσ₀ : 0 < σ₀) :
    Integrable (gpdHessXiSigma 0 σ₀) (gpdMeasure 0 σ₀) := by
  have e : gpdHessXiSigma 0 σ₀ = fun x => (x / σ₀ - (x / σ₀) ^ 2) / σ₀ := by
    funext x; simp [gpdHessXiSigma]
  rw [e]
  exact (((integrable_div_pow_gpdZero hσ₀ 1).congr (ae_of_all _ fun x => by simp)).sub
    (integrable_div_pow_gpdZero hσ₀ 2)).div_const σ₀

lemma integral_gpdHessXiSigma_zero (hσ₀ : 0 < σ₀) :
    ∫ x, gpdHessXiSigma 0 σ₀ x ∂gpdMeasure 0 σ₀ = -(1 / σ₀) := by
  have e : gpdHessXiSigma 0 σ₀ = fun x => (x / σ₀ - (x / σ₀) ^ 2) / σ₀ := by
    funext x; simp [gpdHessXiSigma]
  rw [e, integral_div, integral_sub
    ((integrable_div_pow_gpdZero hσ₀ 1).congr (ae_of_all _ fun x => by simp))
    (integrable_div_pow_gpdZero hσ₀ 2)]
  have h1 : ∫ x, x / σ₀ ∂gpdMeasure 0 σ₀ = 1 := by simpa using integral_div_pow_gpdZero hσ₀ 1
  rw [h1, integral_div_pow_gpdZero hσ₀ 2]
  norm_num [Nat.factorial]
  ring

lemma integrable_gpdHessSigmaSigma_zero (hσ₀ : 0 < σ₀) :
    Integrable (gpdHessSigmaSigma 0 σ₀) (gpdMeasure 0 σ₀) := by
  have e : gpdHessSigmaSigma 0 σ₀ = fun x => (1 - 2 * (x / σ₀)) / σ₀ ^ 2 := by
    funext x; simp [gpdHessSigmaSigma]
  rw [e]
  exact ((integrable_const 1).sub
    (((integrable_div_pow_gpdZero hσ₀ 1).congr (ae_of_all _ fun x => by simp)).const_mul 2)).div_const _

lemma integral_gpdHessSigmaSigma_zero (hσ₀ : 0 < σ₀) :
    ∫ x, gpdHessSigmaSigma 0 σ₀ x ∂gpdMeasure 0 σ₀ = -(1 / σ₀ ^ 2) := by
  have e : gpdHessSigmaSigma 0 σ₀ = fun x => (1 - 2 * (x / σ₀)) / σ₀ ^ 2 := by
    funext x; simp [gpdHessSigmaSigma]
  rw [e, integral_div, integral_sub (integrable_const 1)
    (((integrable_div_pow_gpdZero hσ₀ 1).congr (ae_of_all _ fun x => by simp)).const_mul 2),
    integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul]
  have h1 : ∫ x, x / σ₀ ∂gpdMeasure 0 σ₀ = 1 := by simpa using integral_div_pow_gpdZero hσ₀ 1
  rw [h1]; ring

/-! ### Score CLT at `ξ₀ = 0` -/

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- Linear image of the GPD score at `ξ = 0`. -/
noncomputable def gpdScoreLinZero (m₁₁ m₁₂ m₂₁ m₂₂ σ x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[m₁₁ * expScoreXi σ x + m₁₂ * expScoreSigma σ x,
    m₂₁ * expScoreXi σ x + m₂₂ * expScoreSigma σ x]

theorem tendstoInDistribution_lin_score_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P) (c₁ c₂ : ℝ)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (gpdInfoQuad 0 σ₀ c₁ c₂).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
      (c₁ * expScoreXi σ₀ (X i ω) + c₂ * expScoreSigma σ₀ (X i ω))) atTop Z (fun _ => P) P' := by
  set f : ℝ → ℝ := fun x => c₁ * expScoreXi σ₀ x + c₂ * expScoreSigma σ₀ x
  have hf : Measurable f := by unfold f expScoreXi expScoreSigma; fun_prop
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_lin_expScore hσ₀ _ _
  have hint : ∀ g : ℝ → ℝ, Measurable g → P[g ∘ X 0] = ∫ x, g x ∂gpdMeasure 0 σ₀ :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    simp only [f]
    rw [integral_add, integral_const_mul, integral_const_mul, integral_expScoreXi hσ₀,
      integral_expScoreSigma hσ₀, mul_zero, mul_zero, add_zero]
    · exact ((memLp_lin_expScore hσ₀ c₁ 0).integrable one_le_two).congr (ae_of_all _ fun x => by simp)
    · exact ((memLp_lin_expScore hσ₀ 0 c₂).integrable one_le_two).congr (ae_of_all _ fun x => by simp)
  have hvar : Var[Y 0; P] = gpdInfoQuad 0 σ₀ c₁ c₂ := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this ⊢
    rw [this, integral_lin_expScore_sq hσ₀]
  have hZt : HasLaw Z (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by rw [hvar]; exact hZ
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  simp [Y, f]

theorem isBoundedInProbability_lin_score_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P) (c₁ c₂ : ℝ) :
    IsBoundedInProbability P (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
      (c₁ * expScoreXi σ₀ (X i ω) + c₂ * expScoreSigma σ₀ (X i ω))) :=
  isBoundedInProbability_of_tendstoInDistribution
    (tendstoInDistribution_lin_score_zero (P' := gaussianReal 0 (gpdInfoQuad 0 σ₀ c₁ c₂).toNNReal)
      hσ₀ hX hind c₁ c₂ HasLaw.id)

theorem tendstoInDistribution_gpdScoreLin_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P)
    (m₁₁ m₁₂ m₂₁ m₂₂ : ℝ) {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef)
    (hQ : ∀ t : Fin 2 → ℝ, gpdInfoQuad 0 σ₀ (t 0 * m₁₁ + t 1 * m₂₁) (t 0 * m₁₂ + t 1 * m₂₂) =
      t ⬝ᵥ S *ᵥ t)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)} (hW : HasLaw W (multivariateGaussian 0 S) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
        gpdScoreLinZero m₁₁ m₁₂ m₂₁ m₂₂ σ₀ (X i ω))
      atTop W (fun _ => P) P' := by
  refine TendstoInDistribution.of_inner hW.aemeasurable (fun n => ?_) fun t => ?_
  · have : Measurable (gpdScoreLinZero m₁₁ m₁₂ m₂₁ m₂₂ σ₀) := by
      unfold gpdScoreLinZero
      refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
      have : Measurable (expScoreXi σ₀) := by unfold expScoreXi; fun_prop
      have : Measurable (expScoreSigma σ₀) := by unfold expScoreSigma; fun_prop
      fin_cases i <;> simp <;> fun_prop
    have := fun i => (hX i).aemeasurable
    fun_prop
  have hZt := hasLaw_inner_multivariateGaussian hS hW t
  rw [← hQ] at hZt
  have hclt := tendstoInDistribution_lin_score_zero hσ₀ hX hind _ _ hZt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp only [gpdScoreLinZero, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_inv₀]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [IsProbabilityMeasure P] in
/-- For iid `GPD(0, σ₀) = Exp(1/σ₀)` observations, `max_{i<n} Xᵢ / √n → 0` in probability. -/
theorem tendstoInMeasure_runMax_div_sqrt_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) :
    TendstoInMeasure P (fun (n : ℕ) ω => runMax (fun i => X i ω) n / √(n : ℝ))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * exp (-(ε * √(n : ℝ) / (2 * σ₀)))))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    have h1 : Tendsto (fun t : ℝ => t ^ 2 * exp (-(ε / (2 * σ₀)) * t)) atTop (𝓝 0) := by
      have hrate : 0 < ε / (2 * σ₀) := by positivity
      have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
      have hcomp := h.comp (tendsto_id.const_mul_atTop hrate)
      have hmul := hcomp.const_mul ((ε / (2 * σ₀))⁻¹ ^ 2)
      rw [mul_zero] at hmul
      refine hmul.congr fun t => ?_
      simp only [Function.comp_apply, id, mul_pow, inv_pow]
      field_simp [hrate.ne']
    refine (h1.comp (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).congr fun n => ?_
    simp only [Function.comp_apply, Real.sq_sqrt (Nat.cast_nonneg n)]
    congr 2; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hsub : {ω | ε ≤ ‖runMax (fun i => X i ω) n / √(n : ℝ) - 0‖} ⊆
      ⋃ i ∈ Finset.range n, {ω | ε * √(n : ℝ) / 2 < X i ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (runMax_nonneg _ _), abs_of_pos hsq, le_div_iff₀ hsq] at hω
    obtain ⟨i, hi, hle⟩ := exists_le_of_le_runMax (fun i => X i ω) (by positivity) hω
    have hpos : 0 < ε * √(n : ℝ) := mul_pos hε hsq
    exact mem_biUnion (Finset.mem_range.2 hi) (show ε * √(n : ℝ) / 2 < X i ω by linarith)
  have htail : ∀ i : ℕ, P {ω | ε * √(n : ℝ) / 2 < X i ω} =
      ENNReal.ofReal (exp (-(ε * √(n : ℝ) / (2 * σ₀)))) := fun i => by
    have hset : {ω | ε * √(n : ℝ) / 2 < X i ω} = X i ⁻¹' Ioi (ε * √(n : ℝ) / 2) := rfl
    rw [hset, ← Measure.map_apply_of_aemeasurable (hX i).aemeasurable measurableSet_Ioi,
      (hX i).map_eq, gpdMeasure_Ioi hσ₀ (by positivity : 0 ≤ ε * √(n : ℝ) / 2)]
    simp only [gpdSurvivalAll, ↓reduceIte, neg_div]
    congr 2; ring
  calc P {ω | ε ≤ ‖runMax (fun i => X i ω) n / √(n : ℝ) - 0‖}
      ≤ P (⋃ i ∈ Finset.range n, {ω | ε * √(n : ℝ) / 2 < X i ω}) := measure_mono hsub
    _ ≤ ∑ i ∈ Finset.range n, P {ω | ε * √(n : ℝ) / 2 < X i ω} := measure_biUnion_finset_le _ _
    _ = ∑ _i ∈ Finset.range n, ENNReal.ofReal (exp (-(ε * √(n : ℝ) / (2 * σ₀)))) :=
        Finset.sum_congr rfl fun i _ => htail i
    _ = ENNReal.ofReal ((n : ℝ) * exp (-(ε * √(n : ℝ) / (2 * σ₀)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

end ZeroMoments

/-! ### Deterministic Hessian convergence along `θₙ → (0, σ₀)` -/

section ZeroAvg

variable {σ₀ : ℝ}

/-- Uniform continuity of `segHess H 0 σ₀ θ x` on the good set `0 ≤ x ≤ M`. -/
lemma exists_delta_segHess_good_zero (hσ₀ : 0 < σ₀) {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    {M : ℝ} (hM : 0 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℝ × ℝ, gpdDist 0 σ₀ θ ≤ δ → ∀ x, 0 ≤ x → x ≤ M →
      |segHess H 0 σ₀ θ x - H 0 σ₀ x| ≤ ε := by
  set η := min (min (1 / 4 : ℝ) (σ₀ / 8)) (σ₀ / (4 * (M + 1))) with hη
  have hη0 : 0 < η := lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  have hη1 : η ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ σ₀ / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η * M ≤ σ₀ / 4 := by
    have hle : η ≤ σ₀ / (4 * (M + 1)) := min_le_right _ _
    have hM1 : 0 < M + 1 := by linarith
    calc η * M ≤ σ₀ / (4 * (M + 1)) * M := by gcongr
      _ ≤ σ₀ / (4 * (M + 1)) * (M + 1) := by gcongr; linarith
      _ = σ₀ / 4 := by field_simp
  set S : Set (ℝ × ℝ × ℝ) := Icc (-η) η ×ˢ (Icc (σ₀ - η) (σ₀ + η) ×ˢ Icc 0 M)
  have hSc : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hSpos : ∀ q ∈ S, 0 < q.2.1 ∧ 0 < q.2.1 + q.1 * q.2.2 := fun q hq => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hq
    have hσq : 7 * σ₀ / 8 ≤ q.2.1 := by linarith
    have hmul : -(η * M) ≤ q.1 * q.2.2 := by nlinarith
    exact ⟨by linarith, by linarith⟩
  have hcont : ContinuousOn (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) S := fun q hq =>
    (hH q (hSpos q hq).1 (hSpos q hq).2).continuousWithinAt
  obtain ⟨δ₁, hδ₁, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (hSc.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min η (δ₁ / 2), lt_min hη0 (by linarith), fun θ hθ x hx hxM => ?_⟩
  have hρ1 : gpdDist 0 σ₀ θ ≤ η := hθ.trans (min_le_left _ _)
  have hρ2 : gpdDist 0 σ₀ θ ≤ δ₁ / 2 := hθ.trans (min_le_right _ _)
  have hb : ∀ s ∈ Icc (0 : ℝ) 1,
      |H (0 + s * (θ.1 - 0)) (σ₀ + s * (θ.2 - σ₀)) x - H 0 σ₀ x| ≤ ε := fun s hs => by
    have hd := gpdDist_segment (ξ₀ := 0) (σ₀ := σ₀) θ hs
    unfold gpdDist at hd hρ1 hρ2
    have ha1 := abs_le.1 (show |0 + s * (θ.1 - 0) - 0| ≤ η by
      linarith [abs_nonneg (σ₀ + s * (θ.2 - σ₀) - σ₀)])
    have ha2 := abs_le.1 (show |σ₀ + s * (θ.2 - σ₀) - σ₀| ≤ η by
      linarith [abs_nonneg (0 + s * (θ.1 - 0) - 0)])
    have hmemA : (0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀), x) ∈ S :=
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hx, hxM⟩
    have hmemB : (0, σ₀, x) ∈ S :=
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hx, hxM⟩
    have hdist : dist (0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀), x) (0, σ₀, x) < δ₁ := by
      have := dist_triple_le (0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀), x) (0, σ₀, x)
      simp only [sub_self, abs_zero, add_zero] at this
      linarith
    have := hδ _ hmemA _ hmemB hdist
    rw [Real.dist_eq] at this
    exact this.le
  exact (intervalIntegrable_and_abs_integral_sub_le
    (hHm.comp (f := fun s => (0 + s * (θ.1 - 0), σ₀ + s * (θ.2 - σ₀), x)) (by fun_prop)) hb).2

/-- Deterministic two-sided convergence of an averaged segment Hessian entry at `ξ₀ = 0`,
provided `|θₙ.1| * xᵢ ≤ σ₀ / 4` for all `i < n`. -/
lemma eventually_abs_avg_segHess_sub_le_zero (hσ₀ : 0 < σ₀) {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    (hHb : ∀ θ ∈ gpdNbhdZero σ₀, ∀ x, 0 ≤ x → -(1 / 2) ≤ θ.1 * (x / θ.2) →
      |H θ.1 θ.2 x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x)
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (0, σ₀)))
    {m : ℝ} (hm : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (x i))
      atTop (𝓝 m))
    {d : ℕ → ℝ} (hD : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomZeroTail σ₀ (k : ℝ) (x i)) atTop (𝓝 (d k)))
    (hd : Tendsto d atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (∀ i < n, |(θs n).1| * x i ≤ σ₀ / 4) →
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess H 0 σ₀ (θs n) (x i) - m| ≤ ε := by
  set C := gpdZeroConst σ₀
  have hC : 0 < C := gpdZeroConst_pos hσ₀
  set A := 2 * C + 1
  have hA : 0 < A := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A * d k < ε / 4 := by
    have h := hd.const_mul A; rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  obtain ⟨δ, hδ, hgood⟩ := exists_delta_segHess_good_zero hσ₀ hHm hH (Nat.cast_nonneg k)
    (show 0 < ε / 4 by positivity)
  filter_upwards [tendsto_gpdDist hθ hδ, hθ.eventually (gpdNbhdZero_mem_nhds hσ₀),
    ((hD k).const_mul A).eventually (gt_mem_nhds hk),
    hm.eventually (Metric.ball_mem_nhds m (show 0 < ε / 4 by positivity)),
    eventually_gt_atTop 0] with n hn1 hn2 hn3 hn4 hn5 hsafe
  set tail : ℕ → ℝ := fun i => gpdDomZeroTail σ₀ (k : ℝ) (x i)
  have hdev : ∀ i < n, |segHess H 0 σ₀ (θs n) (x i) - H 0 σ₀ (x i)| ≤
      ε / 4 + 2 * C * tail i := fun i hi => by
    by_cases hle : x i ≤ (k : ℝ)
    · rw [show tail i = 0 from gpdDomZeroTail_of_le hle, mul_zero, add_zero]
      exact hgood _ hn1 _ (hx i) hle
    · rw [show tail i = gpdDomZero σ₀ (x i) from gpdDomZeroTail_of_lt (not_le.1 hle)]
      have h1 := abs_segHess_le_zero hσ₀ hH hHb hn2 (hx i) (hsafe i hi)
      have h2 := hHb (0, σ₀) (mem_gpdNbhdZero_self hσ₀) (x i) (hx i) (by simp)
      have := abs_sub (segHess H 0 σ₀ (θs n) (x i)) (H 0 σ₀ (x i))
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
  have h4 := abs_sub_le ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess H 0 σ₀ (θs n) (x i))
    ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (x i)) m
  linarith

/-- Deterministic eventual negative definiteness of the averaged segment Hessian at `ξ₀ = 0`,
using only admissibility `0 < σₙ + ξₙ xᵢ` and the one-sided Hessian bound. -/
lemma eventually_quad_avg_segHess_le_zero (hσ₀ : 0 < σ₀) {lam : ℝ} (hlam : 0 < lam)
    {m₁₁ m₁₂ m₂₂ : ℝ}
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
      t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiXiAll 0 σ₀ (θs n) (x i)) +
        2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma 0 σ₀ (θs n) (x i)) +
        t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma 0 σ₀ (θs n) (x i)) ≤
      -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2) := by
  set C := gpdZeroConst σ₀
  have hC : 0 < C := gpdZeroConst_pos hσ₀
  set A := 4 * C + 1
  have hA : 0 < A := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A * d k < lam / 8 := by
    have h := hd.const_mul A; rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  obtain ⟨δ₁, hδ₁, g₁⟩ := exists_delta_segHess_good_zero hσ₀ measurable_gpdHessXiXiAll₃
    (fun _ h1 h2 => continuousAt_gpdHessXiXiAll₃ h1 h2) (Nat.cast_nonneg k) (show 0 < lam / 16 by positivity)
  obtain ⟨δ₂, hδ₂, g₂⟩ := exists_delta_segHess_good_zero hσ₀ measurable_gpdHessXiSigma₃
    (fun _ h1 h2 => continuousAt_gpdHessXiSigma₃ h1 h2) (Nat.cast_nonneg k) (show 0 < lam / 16 by positivity)
  obtain ⟨δ₃, hδ₃, g₃⟩ := exists_delta_segHess_good_zero hσ₀ measurable_gpdHessSigmaSigma₃
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
      t₁ ^ 2 * segHess gpdHessXiXiAll 0 σ₀ (θs n) (x i) +
          2 * t₁ * t₂ * segHess gpdHessXiSigma 0 σ₀ (θs n) (x i) +
          t₂ ^ 2 * segHess gpdHessSigmaSigma 0 σ₀ (θs n) (x i) ≤
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
      have hq := segHess_quad_le_zero hσ₀ hn2 (hx i) (hn_adm i hi') t₁ t₂
      obtain ⟨b1, b2, b3⟩ := abs_gpdHessAll_le_of_ge_neg_half hσ₀ (mem_gpdNbhdZero_self hσ₀) (hx i) (by simp)
      rw [← abs_neg] at b1 b2 b3
      have hneg := quad_le_of_abs_le b1 b2 b3 t₁ t₂
      have he : 0 ≤ 2 * (lam / 16) * (t₁ ^ 2 + t₂ ^ 2) := by positivity
      nlinarith
  have havg_le : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      (t₁ ^ 2 * segHess gpdHessXiXiAll 0 σ₀ (θs n) (x i) +
        2 * t₁ * t₂ * segHess gpdHessXiSigma 0 σ₀ (θs n) (x i) +
        t₂ ^ 2 * segHess gpdHessSigmaSigma 0 σ₀ (θs n) (x i)) ≤
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
  have htail_lt : A * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) < lam / 8 := hn3
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

end ZeroAvg

/-! ### Joint asymptotic normality of the GPD MLE at `ξ₀ = 0` and for all `ξ₀ > -1/2` -/

section NormalityZero

variable {σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- **Joint asymptotic normality of GPD likelihood roots at `ξ₀ = 0`** ([Smith 1985];
[Coles, §4.3.3]). For iid `GPD(0, σ₀)` observations and measurable, strongly consistent,
admissible roots `θ̂ₙ` of the continuous likelihood equations `gpdScoreXiAll = 0`,
`gpdScoreSigma = 0`, `√n (θ̂ₙ - (0, σ₀)) ⇒ N(0, I(0, σ₀)⁻¹)`. -/
theorem tendstoInDistribution_gpdJointMLE_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (0, σ₀)))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω)
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXiAll (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv 0 σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - 0, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  have hξ : (-1 / 2 : ℝ) < 0 := by norm_num
  set j₁₁ : ℝ := 1
  set j₁₂ : ℝ := -σ₀
  set j₂₂ : ℝ := 2 * σ₀ ^ 2
  set I₁₁ : ℝ := 2
  set I₁₂ : ℝ := 1 / σ₀
  set I₂₂ : ℝ := 1 / σ₀ ^ 2
  set d : ℝ := I₁₁ * I₂₂ - I₁₂ ^ 2
  have hd_eq : d = 1 / σ₀ ^ 2 := by simp only [d, I₁₁, I₁₂, I₂₂]; field_simp; ring
  have hd : 0 < d := by rw [hd_eq]; positivity
  have hJ₁₁ : I₂₂ / d = j₁₁ := by rw [hd_eq]; simp only [I₂₂, j₁₁]; field_simp
  have hJ₁₂ : -I₁₂ / d = j₁₂ := by rw [hd_eq]; simp only [I₁₂, j₁₂]; field_simp
  have hJ₂₂ : I₁₁ / d = j₂₂ := by rw [hd_eq]; simp only [I₁₁, j₂₂]; field_simp
  -- CLT for `I(0, σ₀)⁻¹ × score`
  have hQ : ∀ t : Fin 2 → ℝ, gpdInfoQuad 0 σ₀ (t 0 * j₁₁ + t 1 * j₁₂) (t 0 * j₁₂ + t 1 * j₂₂) =
      t ⬝ᵥ gpdFisherInfoInv 0 σ₀ *ᵥ t := fun t => by
    simp only [gpdInfoQuad, gpdFisherInfoInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, j₁₁, j₁₂, j₂₂]
    field_simp [hσ₀.ne']
    ring
  have hV := tendstoInDistribution_gpdScoreLin_zero hσ₀ hX hind j₁₁ j₁₂ j₁₂ j₂₂
    (posDef_gpdFisherInfoInv hξ hσ₀).posSemidef hQ hW
  -- Random quantities
  set S₁ : ℕ → Ω → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
    (1 * expScoreXi σ₀ (X i ω) + 0 * expScoreSigma σ₀ (X i ω))
  set S₂ : ℕ → Ω → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
    (0 * expScoreXi σ₀ (X i ω) + 1 * expScoreSigma σ₀ (X i ω))
  set B₁₁ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    segHess gpdHessXiXiAll 0 σ₀ (θh n ω) (X i ω)
  set B₁₂ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    segHess gpdHessXiSigma 0 σ₀ (θh n ω) (X i ω)
  set B₂₂ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    segHess gpdHessSigmaSigma 0 σ₀ (θh n ω) (X i ω)
  set Dn : ℕ → Ω → ℝ := fun n ω => B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2
  set M₁₁ : ℕ → Ω → ℝ := fun n ω => -B₂₂ n ω / Dn n ω - j₁₁
  set M₁₂ : ℕ → Ω → ℝ := fun n ω => B₁₂ n ω / Dn n ω - j₁₂
  set M₂₂ : ℕ → Ω → ℝ := fun n ω => -B₁₁ n ω / Dn n ω - j₂₂
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin 2) :=
    fun n ω => √(n : ℝ) • !₂[(θh n ω).1 - 0, (θh n ω).2 - σ₀]
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin 2) := fun n ω => (√(n : ℝ))⁻¹ •
    ∑ i ∈ Finset.range n, gpdScoreLinZero j₁₁ j₁₂ j₁₂ j₂₂ σ₀ (X i ω)
  -- Measurability
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hBm : ∀ (H : ℝ → ℝ → ℝ → ℝ), (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
      ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        segHess H 0 σ₀ (θh n ω) (X i ω)) P := fun H hH n => by
    have h := measurable_segHess (ξ₀ := 0) (σ₀ := σ₀) hH
    have : ∀ i, AEMeasurable (fun ω => segHess H 0 σ₀ (θh n ω) (X i ω)) P := fun i =>
      h.comp_aemeasurable ((hθm n).prodMk (hXm i))
    exact (Finset.aemeasurable_fun_sum _ fun i _ => this i).const_mul _
  have hB₁₁m := hBm _ measurable_gpdHessXiXiAll₃
  have hB₁₂m := hBm _ measurable_gpdHessXiSigma₃
  have hB₂₂m := hBm _ measurable_gpdHessSigmaSigma₃
  have hSm : ∀ (c₁ c₂ : ℝ) (n : ℕ), AEMeasurable (fun ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
      (c₁ * expScoreXi σ₀ (X i ω) + c₂ * expScoreSigma σ₀ (X i ω))) P := fun c₁ c₂ n => by
    have h1 : Measurable (expScoreXi σ₀) := by unfold expScoreXi; fun_prop
    have h2 : Measurable (expScoreSigma σ₀) := by unfold expScoreSigma; fun_prop
    have : ∀ i, AEMeasurable (fun ω => c₁ * expScoreXi σ₀ (X i ω) +
        c₂ * expScoreSigma σ₀ (X i ω)) P := fun i => by have := hXm i; fun_prop
    exact (Finset.aemeasurable_fun_sum _ fun i _ => this i).const_mul _
  have hMm : ∀ (F : ℝ → ℝ → ℝ → ℝ), Measurable (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) →
      ∀ n, AEMeasurable (fun ω => F (B₁₁ n ω) (B₁₂ n ω) (B₂₂ n ω)) P := fun F hF n =>
    hF.comp_aemeasurable ((hB₁₁m n).prodMk ((hB₁₂m n).prodMk (hB₂₂m n)))
  have hM₁₁m : ∀ n, AEMeasurable (M₁₁ n) P := hMm (fun a b c => -c / (a * c - b ^ 2) - j₁₁) (by fun_prop)
  have hM₁₂m : ∀ n, AEMeasurable (M₁₂ n) P := hMm (fun a b c => b / (a * c - b ^ 2) - j₁₂) (by fun_prop)
  have hM₂₂m : ∀ n, AEMeasurable (M₂₂ n) P := hMm (fun a b c => -a / (a * c - b ^ 2) - j₂₂) (by fun_prop)
  have hTm : ∀ n, AEMeasurable (T n) P := fun n => by
    have hm : Measurable fun θ : ℝ × ℝ => (!₂[θ.1 - 0, θ.2 - σ₀] : EuclideanSpace ℝ (Fin 2)) :=
      (WithLp.measurable_toLp 2 _).comp (f := fun θ : ℝ × ℝ => ![θ.1 - 0, θ.2 - σ₀])
        (measurable_pi_iff.2 fun i => by fin_cases i <;> simp <;> fun_prop)
    exact (hm.comp_aemeasurable (hθm n)).const_smul (√(n : ℝ))
  have hVm : ∀ n, AEMeasurable (V n) P := hV.forall_aemeasurable
  have hS₁b := isBoundedInProbability_lin_score_zero hσ₀ hX hind 1 0
  have hS₂b := isBoundedInProbability_lin_score_zero hσ₀ hX hind 0 1
  -- Strong laws
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
  -- Negative definiteness of `-I(0, σ₀)`
  set lam := 1 / (4 * (1 + σ₀ ^ 2))
  have hlam : 0 < lam := by positivity
  have hnegI : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * (-I₁₁) + 2 * t₁ * t₂ * (-I₁₂) + t₂ ^ 2 * (-I₂₂) ≤
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
    have heq : t₁ ^ 2 * (-I₁₁) + 2 * t₁ * t₂ * (-I₁₂) + t₂ ^ 2 * (-I₂₂) =
        -(2 * t₁ ^ 2 + 2 * t₁ * s + s ^ 2) := by
      simp only [I₁₁, I₁₂, I₂₂, s]; field_simp [hσ₀.ne']; ring
    linarith
  -- Almost sure eventual negative definiteness and preliminary √n rate
  have hquad : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      t₁ ^ 2 * B₁₁ n ω + 2 * t₁ * t₂ * B₁₂ n ω + t₂ ^ 2 * B₂₂ n ω ≤
        -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2) := by
    filter_upwards [hpos, hcons, hadm, hs₁₁, hs₁₂, hs₂₂, hsD] with ω hω hc ha h1 h2 h3 hD
    exact eventually_quad_avg_segHess_le_zero hσ₀ hlam hnegI (fun i => (hω i).le) hc ha h1 h2 h3 hD hdlim
  have hDpos : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, 0 < Dn n ω :=
    hquad.mono fun ω hω => hω.mono fun n hn => det_pos_of_quad hlam hn
  have hlin : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      S₁ n ω = -(B₁₁ n ω * (√(n : ℝ) * ((θh n ω).1 - 0)) +
          B₁₂ n ω * (√(n : ℝ) * ((θh n ω).2 - σ₀))) ∧
      S₂ n ω = -(B₁₂ n ω * (√(n : ℝ) * ((θh n ω).1 - 0)) +
          B₂₂ n ω * (√(n : ℝ) * ((θh n ω).2 - σ₀))) := by
    filter_upwards [hcons, hadm, hroot] with ω hc ha hr
    filter_upwards [hc.eventually (gpdNbhdZero_mem_nhds hσ₀), ha, hr, eventually_gt_atTop 0]
      with n hnb han hrn hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    have hsq : (√(n : ℝ))⁻¹ * n = √(n : ℝ) := by
      have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      field_simp; rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    set a := (θh n ω).1 - 0
    set b := (θh n ω).2 - σ₀
    have eξ : ∑ i ∈ Finset.range n, expScoreXi σ₀ (X i ω) =
        -(a * (n * B₁₁ n ω) + b * (n * B₁₂ n ω)) := by
      have h := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
        (gpdScoreAll_sub_eq_segHess hσ₀ hnb (han i (Finset.mem_range.1 hi))).1
      rw [Finset.sum_sub_distrib, hrn.1] at h
      simp only [B₁₁, B₁₂, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← h]
      ring
    have eσ : ∑ i ∈ Finset.range n, expScoreSigma σ₀ (X i ω) =
        -(a * (n * B₁₂ n ω) + b * (n * B₂₂ n ω)) := by
      have h := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range n) =>
        (gpdScoreAll_sub_eq_segHess hσ₀ hnb (han i (Finset.mem_range.1 hi))).2
      rw [Finset.sum_sub_distrib, hrn.2] at h
      simp only [B₁₂, B₂₂, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← h]
      ring
    constructor
    · simp only [S₁, one_mul, zero_mul, add_zero]
      rw [eξ, show (√(n : ℝ))⁻¹ * -(a * (n * B₁₁ n ω) + b * (n * B₁₂ n ω)) =
        -(((√(n : ℝ))⁻¹ * n) * a * B₁₁ n ω + ((√(n : ℝ))⁻¹ * n) * b * B₁₂ n ω) by ring, hsq]
      ring
    · simp only [S₂, one_mul, zero_mul, zero_add]
      rw [eσ, show (√(n : ℝ))⁻¹ * -(a * (n * B₁₂ n ω) + b * (n * B₂₂ n ω)) =
        -(((√(n : ℝ))⁻¹ * n) * a * B₁₂ n ω + ((√(n : ℝ))⁻¹ * n) * b * B₂₂ n ω) by ring, hsq]
      ring
  have hrate : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      |√(n : ℝ) * ((θh n ω).1 - 0)| + |√(n : ℝ) * ((θh n ω).2 - σ₀)| ≤
        4 / lam * (|S₁ n ω| + |S₂ n ω|) := by
    filter_upwards [hquad, hlin] with ω hq hl
    filter_upwards [hq, hl] with n hqn hln
    exact abs_add_abs_le_of_quad hlam hqn hln.1 hln.2
  -- Safe-region control: `r n ω = (2 / σ₀) * |(θh n ω).1| * runMax X n → 0` in probability
  set Mx : ℕ → Ω → ℝ := fun n ω => runMax (fun i => X i ω) n
  have hMxm : ∀ n, AEMeasurable (Mx n) P := fun n => aemeasurable_runMax hXm n
  have hMx0 : TendstoInMeasure P (fun n ω => Mx n ω / √(n : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_runMax_div_sqrt_zero hσ₀ hX
  set r : ℕ → Ω → ℝ := fun n ω => (2 / σ₀) * |(θh n ω).1| * Mx n ω with hr_def
  have hrm : ∀ n, AEMeasurable (r n) P := fun n => by
    have := hθm n; have := hMxm n; simp only [hr_def]; fun_prop
  have hr : TendstoInMeasure P r atTop (fun _ => 0) := by
    set g : ℕ → Ω → ℝ := fun n ω => (2 / σ₀) * (4 / lam) *
      ((Mx n ω / √(n : ℝ)) * |S₁ n ω| + (Mx n ω / √(n : ℝ)) * |S₂ n ω|) with hg_def
    have hg : TendstoInMeasure P g atTop (fun _ => 0) := by
      have hS₁abs : IsBoundedInProbability P (fun n ω => |S₁ n ω|) := fun ε hε => by
        obtain ⟨M, hM⟩ := hS₁b ε hε
        exact ⟨M, hM.mono fun n hn => by simpa only [abs_abs] using hn⟩
      have hS₂abs : IsBoundedInProbability P (fun n ω => |S₂ n ω|) := fun ε hε => by
        obtain ⟨M, hM⟩ := hS₂b ε hε
        exact ⟨M, hM.mono fun n hn => by simpa only [abs_abs] using hn⟩
      have a₁ := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₁abs hMx0
      have a₂ := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₂abs hMx0
      have := tendstoInMeasure_comp (tendstoInMeasure_add_zero a₁ a₂)
        (φ := fun z => (2 / σ₀) * (4 / lam) * z) (by fun_prop)
      simpa only [mul_zero] using this
    have hgm : ∀ n, AEStronglyMeasurable (g n) P := fun n => by
      have := hMxm n; have := hSm 1 0 n; have := hSm 0 1 n
      exact (by fun_prop : AEMeasurable (g n) P).aestronglyMeasurable
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le (fun n => (hrm n).aestronglyMeasurable)
      hgm ?_ hg
    filter_upwards [hrate] with ω hω
    filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
    have hM0 : 0 ≤ Mx n ω := runMax_nonneg _ _
    have h1 : √(n : ℝ) * |(θh n ω).1| ≤ 4 / lam * (|S₁ n ω| + |S₂ n ω|) := by
      have e1 : |√(n : ℝ) * ((θh n ω).1 - 0)| = √(n : ℝ) * |(θh n ω).1| := by
        rw [sub_zero, abs_mul, abs_of_nonneg hsq.le]
      linarith [abs_nonneg (√(n : ℝ) * ((θh n ω).2 - σ₀))]
    have hr0 : 0 ≤ r n ω := by simp only [hr_def]; positivity
    rw [abs_of_nonneg hr0]
    simp only [hr_def, hg_def]
    have e : (2 / σ₀) * |(θh n ω).1| * Mx n ω =
        (2 / σ₀) * (√(n : ℝ) * |(θh n ω).1|) * (Mx n ω / √(n : ℝ)) := by
      field_simp
    rw [e]
    have hY0 : 0 ≤ Mx n ω / √(n : ℝ) := by positivity
    have h2 : (2 / σ₀) * (√(n : ℝ) * |(θh n ω).1|) * (Mx n ω / √(n : ℝ)) ≤
        (2 / σ₀) * (4 / lam * (|S₁ n ω| + |S₂ n ω|)) * (Mx n ω / √(n : ℝ)) := by gcongr
    refine h2.trans (le_of_eq ?_)
    ring
  -- Convergence in probability of the averaged segment Hessians via cutoff
  have hconv : ∀ (H : ℝ → ℝ → ℝ → ℝ) (m : ℝ),
      (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
      (∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
        ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q) →
      (∀ θ ∈ gpdNbhdZero σ₀, ∀ x, 0 ≤ x → -(1 / 2) ≤ θ.1 * (x / θ.2) →
        |H θ.1 θ.2 x| ≤ gpdZeroConst σ₀ * gpdDomZero σ₀ x) →
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H 0 σ₀ (X i ω))
        atTop (𝓝 m)) →
      TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        segHess H 0 σ₀ (θh n ω) (X i ω)) atTop (fun _ => m) := by
    intro H m hHm hH hHb hsm
    set f : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      segHess H 0 σ₀ (θh n ω) (X i ω) - m with hf
    have hfm : ∀ n, AEMeasurable (f n) P := fun n => (hBm H hHm n).sub_const m
    have h1 : TendstoInMeasure P (fun n ω => f n ω * cutoff (r n ω)) atTop (fun _ => 0) :=
      tendstoInMeasure_mul_cutoff f hr
    have h2 : TendstoInMeasure P (fun n ω => f n ω * (1 - cutoff (r n ω))) atTop
        (fun _ => 0) := by
      refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
      · exact ((hfm n).mul (aemeasurable_const.sub
          (continuous_cutoff.measurable.comp_aemeasurable (hrm n)))).aestronglyMeasurable
      filter_upwards [hpos, hcons, hsm, hsD] with ω hω hc hm hD
      refine Metric.tendsto_nhds.2 fun ε hε => ?_
      filter_upwards [eventually_abs_avg_segHess_sub_le_zero hσ₀ hHm hH hHb
        (fun i => (hω i).le) hc hm hD hdlim (ε := ε / 2) (by positivity)] with n hn
      rw [Real.dist_eq, sub_zero]
      by_cases hcut : cutoff (r n ω) = 1
      · rw [hcut, sub_self, mul_zero, abs_zero]; exact hε
      · have hr' : r n ω < 1 / 2 := by
          by_contra h; exact hcut (cutoff_of_ge (not_lt.1 h))
        have hsafe : ∀ i < n, |(θh n ω).1| * X i ω ≤ σ₀ / 4 := fun i hi => by
          have hxi : X i ω ≤ Mx n ω := le_runMax (fun j => X j ω) hi
          have hmul : |(θh n ω).1| * X i ω ≤ |(θh n ω).1| * Mx n ω :=
            mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
          have hr_lt : (2 / σ₀) * (|(θh n ω).1| * Mx n ω) < 1 / 2 := by
            simp only [hr_def] at hr'; linarith
          have : |(θh n ω).1| * Mx n ω < σ₀ / 4 := by
            have := mul_lt_mul_of_pos_left hr_lt (show 0 < σ₀ / 2 by positivity)
            have e1 : σ₀ / 2 * (2 / σ₀ * (|(θh n ω).1| * Mx n ω)) = |(θh n ω).1| * Mx n ω := by
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
    simp only [hf, sub_add_cancel, zero_add] at this
    exact this
  have hB₁₁ := hconv gpdHessXiXiAll _ measurable_gpdHessXiXiAll₃
    (fun _ h1 h2 => continuousAt_gpdHessXiXiAll₃ h1 h2)
    (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).1) hs₁₁
  have hB₁₂ := hconv gpdHessXiSigma _ measurable_gpdHessXiSigma₃
    (fun _ h1 h2 => continuousAt_gpdHessXiSigma₃ h1 h2)
    (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).2.1) hs₁₂
  have hB₂₂ := hconv gpdHessSigmaSigma _ measurable_gpdHessSigmaSigma₃
    (fun _ h1 h2 => continuousAt_gpdHessSigmaSigma₃ h1 h2)
    (fun θ hθ x hx ht => (abs_gpdHessAll_le_of_ge_neg_half hσ₀ hθ hx ht).2.2) hs₂₂
  have hDn : TendstoInMeasure P Dn atTop (fun _ => d) := by
    have h := tendstoInMeasure_comp₂ (tendstoInMeasure_mul hB₁₁ hB₂₂)
      (tendstoInMeasure_comp hB₁₂ (φ := fun z => z ^ 2) (by fun_prop))
      (φ := fun p => p.1 - p.2) (by fun_prop)
    convert h using 2
    simp only [d, I₁₁, I₂₂, I₁₂]; ring
  have hM₁₁ : TendstoInMeasure P M₁₁ atTop (fun _ => 0) := by
    have h := tendstoInMeasure_comp₂ hB₂₂ hDn (φ := fun p => -p.1 / p.2 - j₁₁)
      ((continuous_fst.neg.continuousAt.div continuous_snd.continuousAt hd.ne').sub continuousAt_const)
    convert h using 2
    rw [neg_neg, hJ₁₁]; simp only [j₁₁, sub_self]
  have hM₁₂ : TendstoInMeasure P M₁₂ atTop (fun _ => 0) := by
    have h := tendstoInMeasure_comp₂ hB₁₂ hDn (φ := fun p => p.1 / p.2 - j₁₂)
      ((continuous_fst.continuousAt.div continuous_snd.continuousAt hd.ne').sub continuousAt_const)
    convert h using 2
    rw [hJ₁₂]; simp only [j₁₂, sub_self]
  have hM₂₂ : TendstoInMeasure P M₂₂ atTop (fun _ => 0) := by
    have h := tendstoInMeasure_comp₂ hB₁₁ hDn (φ := fun p => -p.1 / p.2 - j₂₂)
      ((continuous_fst.neg.continuousAt.div continuous_snd.continuousAt hd.ne').sub continuousAt_const)
    convert h using 2
    rw [neg_neg, hJ₂₂]; simp only [j₂₂, sub_self]
  -- Dominating sequence and Slutsky conclusion
  set G : ℕ → Ω → ℝ := fun n ω => |M₁₁ n ω * S₁ n ω| + |M₁₂ n ω * S₂ n ω| +
    (|M₁₂ n ω * S₁ n ω| + |M₂₂ n ω * S₂ n ω|)
  have hG : TendstoInMeasure P G atTop (fun _ => 0) := by
    have a₁ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₁b hM₁₁)
    have a₂ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₂b hM₁₂)
    have a₃ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₁b hM₁₂)
    have a₄ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS₂b hM₂₂)
    exact tendstoInMeasure_add_zero (tendstoInMeasure_add_zero a₁ a₂)
      (tendstoInMeasure_add_zero a₃ a₄)
  have hdom : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |‖T n ω - V n ω‖| ≤ G n ω := by
    filter_upwards [hlin, hDpos] with ω hl hD
    filter_upwards [hl, hD] with n hln hDn
    obtain ⟨h₁, h₂⟩ := solve_two_by_two (j₁₁ := j₁₁) (j₁₂ := j₁₂) (j₂₂ := j₂₂) hln.1 hln.2 hDn.ne'
    have hV0 : V n ω 0 = j₁₁ * S₁ n ω + j₁₂ * S₂ n ω := by
      simp only [V, S₁, S₂, gpdScoreLinZero, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        smul_eq_mul, Matrix.cons_val_zero, one_mul, zero_mul, add_zero, zero_add,
        Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    have hV1 : V n ω 1 = j₁₂ * S₁ n ω + j₂₂ * S₂ n ω := by
      simp only [V, S₁, S₂, gpdScoreLinZero, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul, zero_mul, add_zero,
        zero_add, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    have hT0 : T n ω 0 = √(n : ℝ) * ((θh n ω).1 - 0) := by simp [T]
    have hT1 : T n ω 1 = √(n : ℝ) * ((θh n ω).2 - σ₀) := by simp [T]
    rw [abs_norm]
    refine (norm_euclidean_two_le _).trans ?_
    simp only [PiLp.sub_apply, hT0, hT1, hV0, hV1]
    rw [h₁, h₂]
    simp only [G, M₁₁, M₁₂, M₂₂, Dn]
    exact add_le_add (abs_add_le _ _) (abs_add_le _ _)
  have hdiff : TendstoInMeasure P (T - V) atTop 0 := by
    have hr := tendstoInMeasure_zero_of_ae_eventually_abs_le
      (f := fun n ω => ‖T n ω - V n ω‖)
      (fun n => ((hTm n).sub (hVm n)).norm.aestronglyMeasurable)
      (fun n => by
        have := hM₁₁m n; have := hM₁₂m n; have := hM₂₂m n
        have := hSm 1 0 n; have := hSm 0 1 n
        exact (by fun_prop : AEMeasurable (G n) P).aestronglyMeasurable) hdom hG
    rw [tendstoInMeasure_iff_norm] at hr ⊢
    intro ε hε
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_norm] using hr ε hε
  exact tendstoInDistribution_of_tendstoInMeasure_sub T W hV hdiff hTm

/-- **Joint asymptotic normality of the GPD maximum likelihood estimator at `ξ₀ = 0`**
([Smith 1985]; [Coles, §4.3.3]). Let `K ⊂ {ξ > -1, σ > 0}` be compact with `(0, σ₀)` in its
interior, let `X₀, X₁, …` be iid `GPD(0, σ₀)`, and let `θ̂ₙ` be measurable maximizers over `K`
of the two-parameter GPD log-likelihood. Then `√n (θ̂ₙ - (0, σ₀)) ⇒ N(0, I(0, σ₀)⁻¹)`. -/
theorem tendstoInDistribution_gpdMLE_zero {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (0, σ₀) ∈ interior K) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv 0 σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - 0, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (0, σ₀)) := by
    filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
    refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have := hmax n ω (interior_subset hθ₀)
    simp only [mem_ofPred_eq] at this
    simpa using this
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + (0 : ℝ) * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure (ξ := 0) hσ₀)
  have hadmAll : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
      0 ≤ X i ω ∧ 0 < 1 + (θh n ω).1 * X i ω / (θh n ω).2 := by
    filter_upwards [hsupp] with ω hω n
    exact admissible_of_isMaxOn (interior_subset hθ₀) hσ₀ (fun i => hω i) (hmax n ω)
  refine tendstoInDistribution_gpdJointMLE_zero hσ₀ hX hind hθm hcons ?_ ?_ hW
  · filter_upwards [hadmAll] with ω hω
    refine Eventually.of_forall fun n i hi => ?_
    have h := (hω n ⟨i, hi⟩).2
    have hσ := (hKS _ (hθK n ω)).2
    have e : 1 + (θh n ω).1 * X i ω / (θh n ω).2 =
        ((θh n ω).2 + (θh n ω).1 * X i ω) / (θh n ω).2 := by field_simp
    rw [e] at h
    exact (div_pos_iff_of_pos_right hσ).1 h
  · filter_upwards [hadmAll, hcons] with ω hω hc
    filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀)] with n h1
    have hσ := (hKS _ (hθK n ω)).2
    have := scoreAll_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) h1 hσ (hω n) (hmax n ω)
    rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXiAll (θh n ω).1 (θh n ω).2 (X i ω)) n,
      Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n]
      at this
    exact this

/-- **Joint asymptotic normality of the GPD maximum likelihood estimator for ALL regular shapes
`ξ₀ > -1/2`**, including `ξ₀ = 0` ([Smith 1985]; [Coles, §4.3.3]). -/
theorem tendstoInDistribution_gpdMLE_reg {ξ₀ : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  rcases eq_or_ne ξ₀ 0 with rfl | hξ₀0
  · exact tendstoInDistribution_gpdMLE_zero hK hKS hθ₀ hσ₀ hX hind hθm hθK hmax hW
  · exact tendstoInDistribution_gpdMLE_all hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind hθm hθK hmax hW

/-- **Unconditional asymptotic normality of the GPD MLE for ALL regular shapes `ξ₀ > -1/2`**,
including `ξ₀ = 0`: measurable maximizers exist and satisfy `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)`. -/
theorem exists_gpdMLE_tendstoInDistribution_reg {ξ₀ : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) P') :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K (g n x)) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) • !₂[(g n (fun i : Fin n => X i ω)).1 - ξ₀,
          (g n (fun i : Fin n => X i ω)).2 - σ₀])
        atTop W (fun _ => P) P' := by
  choose g hgm hg using exists_measurable_gpdMLE hK hKS ⟨_, interior_subset hθ₀⟩
  refine ⟨g, hgm, hg, ?_⟩
  exact tendstoInDistribution_gpdMLE_reg hK hKS hθ₀ hξ₀ hσ₀ hX hind
    (θh := fun n ω => g n (fun i : Fin n => X i ω))
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2) hW

end NormalityZero

end ExtremeValueTheory

