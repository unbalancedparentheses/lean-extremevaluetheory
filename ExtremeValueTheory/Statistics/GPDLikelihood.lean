/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Density
import ExtremeValueTheory.Statistics.HillNormality
import ExtremeValueTheory.GEV.Moments
import ExtremeValueTheory.PeaksOverThreshold.Balkema

/-!
# Likelihood theory for the generalized Pareto distribution

The **generalized Pareto law** `GPD(ξ, σ)` (`gpdMeasure`) is defined through its exponential
representation `X = σ (e^{ξ E} - 1)/ξ` (`X = σ E` for `ξ = 0`), `E` standard exponential. Its
survival function is `gpdSurvival' ξ σ` (`PeaksOverThreshold/Balkema.lean`) and its density is

  `g_{ξ,σ}(x) = σ⁻¹ (1 + ξ x / σ) ^ (-1/ξ - 1)` on `{x ≥ 0, 1 + ξ x / σ > 0}`
  (`σ⁻¹ e^{-x/σ}` for `ξ = 0`).

We develop the maximum likelihood theory of the scale parameter
([Smith 1985]; [Coles, §4.3]; [dHF, §3.4]).

## Main results

* *The law.* `gpdMeasure_Ioi` (survival function), `gpdMeasure_Iic` (distribution function
  `gpdCDF`), `hasDerivAt_gpdCDF` (the density is the derivative of the distribution function in
  the interior of the support), `gpdMeasure_eq_withDensity` (`GPD(ξ, σ) = g_{ξ,σ}(x) dx`),
  `integral_gpdDensity` (`∫ g_{ξ,σ} = 1`), and `gpdLogLik`, `log_gpdDensity`.
* *The exponential case `ξ = 0`.* `gpdLogLik_zero_lt_sampleMean`: the MLE of `σ` is the sample
  mean, the unique maximizer of the likelihood; `ae_tendsto_sampleMean_gpd_zero` (strong
  consistency) and `tendstoInDistribution_sampleMean_gpd_zero` (asymptotic normality
  `√n (σ̂ₙ - σ) ⇒ N(0, σ²)`).
* *Known shape `ξ > -1`, `ξ ≠ 0`.* The likelihood equation in `σ` is
  `(1 + ξ) ∑ᵢ xᵢ / (σ + ξ xᵢ) = n` (`hasDerivAt_gpdLogLik`). For positive observations it has a
  root among the admissible scales (`exists_gpdScaleScore_eq`), the root is unique
  (`gpdScaleScore_root_unique`), and it is the unique maximizer of the likelihood
  (`gpdLogLik_lt_of_score_eq`): the score is strictly decreasing, so the likelihood increases and
  then decreases. For iid `GPD(ξ, σ₀)` data these hold almost surely for every `n ≥ 1`
  (`ae_existsUnique_gpdScaleMLE`), and the MLE is strongly consistent
  (`ae_tendsto_gpdScaleMLE`).

The joint maximum likelihood estimator of `(ξ, σ)` on a compact parameter set is treated in
`ExtremeValueTheory.Statistics.Wald`.

## Proof of consistency for a known shape

The population score `σ ↦ E[X / (σ + ξ X)]` is strictly decreasing and equals `1/(1 + ξ)` at
the true scale `σ₀` (`integral_div_gpdMeasure`, computed on the exponential scale, where
`X / (σ₀ + ξ X) = (1 - e^{-ξ E}) / ξ`). By the strong law of large numbers at the countably many
scales `σ₀ ± 1/(k + 1)`, the empirical score eventually changes sign around `σ₀`, which traps the
root. For `ξ < 0` the scores below `σ₀` are not integrable, and the lower bound comes instead from
the admissibility constraint `σ̂ₙ > -ξ max_{i<n} Xᵢ`, together with `max_{i<n} Xᵢ → -σ₀/ξ`.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §4.3.
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006), §3.4.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### The standard exponential law -/

section StdExp

lemma stdExpMeasure_Ioi {c : ℝ} (hc : 0 ≤ c) :
    stdExpMeasure (Ioi c) = ENNReal.ofReal (exp (-c)) := by
  rw [stdExpMeasure, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict
    measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.2 hc, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_neg_Ioi c) (ae_of_all _ fun t ↦ (exp_pos (-t)).le), integral_exp_neg_Ioi]

instance : IsProbabilityMeasure stdExpMeasure := by
  constructor
  have h := stdExpMeasure_Ioi le_rfl
  rw [neg_zero, exp_zero, ENNReal.ofReal_one] at h
  rw [← h, stdExpMeasure, withDensity_apply _ MeasurableSet.univ, withDensity_apply _
    measurableSet_Ioi, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioi,
    inter_self]

/-- The measure `e^{-t} dt` on `(0, ∞)` is Mathlib's exponential law of rate `1`. -/
theorem stdExpMeasure_eq_expMeasure : stdExpMeasure = expMeasure 1 := by
  rw [stdExpMeasure, expMeasure, gammaMeasure, ← withDensity_indicator measurableSet_Ioi]
  refine withDensity_congr_ae ?_
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [h0] with x hx
  simp only [gammaPDF, gammaPDFReal, Set.indicator, mem_Ioi]
  rcases lt_or_gt_of_ne hx with h | h
  · simp [h.not_ge, h.not_gt]
  · simp [h.le, h]

end StdExp

/-! ### The generalized Pareto law -/

section GPD

variable {ξ σ x : ℝ}

/-- The quantile transform of the generalized Pareto law: `t ↦ σ (e^{ξ t} - 1) / ξ`
(`σ t` for `ξ = 0`), carrying the standard exponential law to `GPD(ξ, σ)`. -/
noncomputable def gpdTransform (ξ σ t : ℝ) : ℝ :=
  if ξ = 0 then σ * t else σ * (exp (ξ * t) - 1) / ξ

/-- The **generalized Pareto law** `GPD(ξ, σ)`, defined as the law of `σ (e^{ξ E} - 1) / ξ`
for a standard exponential `E`. Its survival function is `gpdSurvival' ξ σ`
(`gpdMeasure_Ioi`) and its density is `gpdDensity ξ σ` (`gpdMeasure_eq_withDensity`). -/
noncomputable def gpdMeasure (ξ σ : ℝ) : Measure ℝ := stdExpMeasure.map (gpdTransform ξ σ)

/-- The distribution function of `GPD(ξ, σ)`: `1 - gpdSurvival' ξ σ x` for `x ≥ 0`, and `0`
for `x < 0`. -/
noncomputable def gpdCDF (ξ σ x : ℝ) : ℝ := 1 - gpdSurvival' ξ σ (max x 0)

/-- The **density of the generalized Pareto law**:
`g_{ξ,σ}(x) = σ⁻¹ (1 + ξ x / σ) ^ (-1/ξ - 1)` (`σ⁻¹ e^{-x/σ}` for `ξ = 0`) on the support
`{x ≥ 0, 1 + ξ x / σ > 0}`, and `0` elsewhere. -/
noncomputable def gpdDensity (ξ σ x : ℝ) : ℝ :=
  if 0 ≤ x ∧ 0 < 1 + ξ * x / σ then
    (if ξ = 0 then σ⁻¹ * exp (-x / σ) else σ⁻¹ * (1 + ξ * x / σ) ^ (-(1 / ξ) - 1))
  else 0

lemma measurable_gpdTransform (ξ σ : ℝ) : Measurable (gpdTransform ξ σ) := by
  unfold gpdTransform; split_ifs <;> fun_prop

lemma gpdTransform_strictMono (hσ : 0 < σ) : StrictMono (gpdTransform ξ σ) := by
  intro s t hst
  unfold gpdTransform
  split_ifs with hξ
  · exact mul_lt_mul_of_pos_left hst hσ
  · rcases lt_or_gt_of_ne hξ with hneg | hpos
    · rw [div_lt_div_right_of_neg hneg]
      have : exp (ξ * t) < exp (ξ * s) := exp_lt_exp.2 (mul_lt_mul_of_neg_left hst hneg)
      nlinarith
    · rw [div_lt_div_iff_of_pos_right hpos]
      have : exp (ξ * s) < exp (ξ * t) := exp_lt_exp.2 (mul_lt_mul_of_pos_left hst hpos)
      nlinarith

lemma gpdTransform_pos (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) : 0 < gpdTransform ξ σ t := by
  have h0 : gpdTransform ξ σ 0 = 0 := by simp [gpdTransform]
  exact h0 ▸ gpdTransform_strictMono hσ ht

instance (ξ σ : ℝ) : IsProbabilityMeasure (gpdMeasure ξ σ) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_gpdTransform ξ σ).aemeasurable).2 inferInstance

/-- Inside the support, `1 + ξ T(t) / σ = e^{ξ t}`. -/
lemma one_add_mul_gpdTransform (hσ : 0 < σ) (hξ : ξ ≠ 0) (t : ℝ) :
    1 + ξ * gpdTransform ξ σ t / σ = exp (ξ * t) := by
  simp only [gpdTransform, hξ, ↓reduceIte]
  field_simp
  ring

/-- **Survival function of the GPD**: `P(X > x) = gpdSurvival' ξ σ x` for `x ≥ 0`. -/
theorem gpdMeasure_Ioi (hσ : 0 < σ) (hx : 0 ≤ x) :
    gpdMeasure ξ σ (Ioi x) = ENNReal.ofReal (gpdSurvival' ξ σ x) := by
  have hm := measurable_gpdTransform ξ σ
  have hS : MeasurableSet (gpdTransform ξ σ ⁻¹' Ioi x) := hm measurableSet_Ioi
  rw [gpdMeasure, Measure.map_apply hm measurableSet_Ioi]
  -- the preimage, inside `(0, ∞)`, is a half-line `(τ, ∞)`
  have key : ∀ τ : ℝ, 0 ≤ τ → gpdTransform ξ σ τ = x →
      stdExpMeasure (gpdTransform ξ σ ⁻¹' Ioi x) = ENNReal.ofReal (exp (-τ)) := by
    intro τ hτ hτx
    have : gpdTransform ξ σ ⁻¹' Ioi x = Ioi τ := by
      ext t
      simp only [mem_preimage, mem_Ioi, ← hτx]
      exact (gpdTransform_strictMono hσ).lt_iff_lt
    rw [this, stdExpMeasure_Ioi hτ]
  by_cases hξ : ξ = 0
  · subst hξ
    rw [key (x / σ) (div_nonneg hx hσ.le) (by simp [gpdTransform]; field_simp)]
    simp [neg_div]
  by_cases hu : 0 < 1 + ξ * x / σ
  · set τ := log (1 + ξ * x / σ) / ξ
    have hτ : 0 ≤ τ := by
      rcases lt_or_gt_of_ne hξ with hneg | hpos
      · refine div_nonneg_of_nonpos (log_nonpos hu.le ?_) hneg.le
        have : ξ * x / σ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hneg.le hx) hσ.le
        linarith
      · refine div_nonneg (log_nonneg ?_) hpos.le
        have : 0 ≤ ξ * x / σ := by positivity
        linarith
    have hτx : gpdTransform ξ σ τ = x := by
      simp only [gpdTransform, hξ, ↓reduceIte, τ]
      rw [mul_div_cancel₀ _ hξ, exp_log hu]
      field_simp
      ring
    rw [key τ hτ hτx, gpdSurvival', ite_eq_right hξ, max_eq_left hu.le, rpow_def_of_pos hu]
    congr 2
    simp only [τ]
    ring
  · -- beyond the right endpoint (`ξ < 0`): the preimage is empty
    have hneg : ξ < 0 := by
      by_contra h
      have : 0 ≤ ξ * x / σ := div_nonneg (mul_nonneg (not_lt.1 h) hx) hσ.le
      exact hu (by linarith)
    have hempty : gpdTransform ξ σ ⁻¹' Ioi x ∩ Ioi 0 = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro h _
      have h1 := one_add_mul_gpdTransform hσ hξ t
      have h2 : ξ * gpdTransform ξ σ t / σ < ξ * x / σ :=
        div_lt_div_of_pos_right (mul_lt_mul_of_neg_left h hneg) hσ
      have h3 := exp_pos (ξ * t)
      linarith
    have hne : -(1 / ξ) ≠ 0 := by simp [hξ]
    rw [stdExpMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS, hempty,
      Measure.restrict_empty, lintegral_zero_measure, gpdSurvival', ite_eq_right hξ,
      max_eq_right (not_lt.1 hu), zero_rpow hne, ENNReal.ofReal_zero]

/-- **Distribution function of the GPD**: `P(X ≤ x) = gpdCDF ξ σ x`. -/
theorem gpdMeasure_Iic (hσ : 0 < σ) (x : ℝ) :
    gpdMeasure ξ σ (Iic x) = ENNReal.ofReal (gpdCDF ξ σ x) := by
  have hS1 := gpdSurvival'_le_one (ξ := ξ) hσ (le_max_right x 0)
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, gpdCDF]
  rcases le_total 0 x with hx | hx
  · rw [gpdMeasure_Ioi hσ hx, max_eq_left hx, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (gpdSurvival'_nonneg ξ σ x)]
  · have h1 : gpdMeasure ξ σ (Ioi x) = 1 := by
      refine le_antisymm prob_le_one ?_
      calc (1 : ENNReal) = gpdMeasure ξ σ (Ioi 0) := by
            rw [gpdMeasure_Ioi hσ le_rfl, gpdSurvival'_zero_right, ENNReal.ofReal_one]
        _ ≤ gpdMeasure ξ σ (Ioi x) := measure_mono (Ioi_subset_Ioi hx)
    rw [h1, max_eq_right hx, gpdSurvival'_zero_right]
    simp

lemma continuous_gpdCDF (hσ : 0 < σ) : Continuous (gpdCDF ξ σ) := by
  unfold gpdCDF
  exact continuous_const.sub ((gpdSurvival'_continuousOn hσ).comp_continuous
    (continuous_id.max continuous_const) fun x => le_max_right x 0)

lemma gpdCDF_of_nonpos (hx : x ≤ 0) : gpdCDF ξ σ x = 0 := by
  simp [gpdCDF, max_eq_right hx, gpdSurvival'_zero_right]

lemma gpdDensity_nonneg (hσ : 0 < σ) (ξ x : ℝ) : 0 ≤ gpdDensity ξ σ x := by
  unfold gpdDensity
  split_ifs with h1 h2
  · positivity
  · exact mul_nonneg (inv_nonneg.2 hσ.le) (rpow_nonneg h1.2.le _)
  · exact le_rfl

lemma measurable_gpdDensity (ξ σ : ℝ) : Measurable (gpdDensity ξ σ) := by
  unfold gpdDensity
  have hg : Measurable fun x : ℝ =>
      if ξ = 0 then σ⁻¹ * exp (-x / σ) else σ⁻¹ * (1 + ξ * x / σ) ^ (-(1 / ξ) - 1) := by
    by_cases hξ : ξ = 0
    · simp only [hξ, ↓reduceIte]; fun_prop
    · simp only [hξ, ↓reduceIte]; fun_prop
  refine Measurable.ite ?_ hg measurable_const
  exact (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_lt measurable_const
      (show Measurable fun x : ℝ => 1 + ξ * x / σ by fun_prop))

/-- **The GPD density is the derivative of the distribution function** at every interior point
`x > 0`, `1 + ξ x / σ > 0` of the support. -/
theorem hasDerivAt_gpdCDF (hσ : 0 < σ) (hx : 0 < x) (hu : 0 < 1 + ξ * x / σ) :
    HasDerivAt (gpdCDF ξ σ) (gpdDensity ξ σ x) x := by
  have hev : ∀ᶠ y in 𝓝 x, 0 < y ∧ 0 < 1 + ξ * y / σ :=
    (lt_mem_nhds hx).and ((continuous_const.add ((continuous_const.mul continuous_id).div_const
      σ)).continuousAt.eventually (lt_mem_nhds hu))
  by_cases hξ : ξ = 0
  · subst hξ
    have heq : gpdCDF 0 σ =ᶠ[𝓝 x] fun y => 1 - exp (-y / σ) := by
      filter_upwards [hev] with y hy
      simp [gpdCDF, max_eq_left hy.1.le]
    have hd : HasDerivAt (fun y => 1 - exp (-y / σ)) (σ⁻¹ * exp (-x / σ)) x := by
      have := ((hasDerivAt_neg x).div_const σ).exp.const_sub 1
      convert this using 1
      field_simp
    simp only [gpdDensity, hx.le, hu, and_self, ↓reduceIte]
    exact hd.congr_of_eventuallyEq heq
  · have heq : gpdCDF ξ σ =ᶠ[𝓝 x] fun y => 1 - (1 + ξ * y / σ) ^ (-(1 / ξ)) := by
      filter_upwards [hev] with y hy
      simp [gpdCDF, gpdSurvival', hξ, max_eq_left hy.1.le, max_eq_left hy.2.le]
    have hd0 : HasDerivAt (fun y => 1 + ξ * y / σ) (ξ / σ) x := by
      simpa using (((hasDerivAt_id x).const_mul ξ).div_const σ).const_add 1
    have hd : HasDerivAt (fun y => 1 - (1 + ξ * y / σ) ^ (-(1 / ξ)))
        (σ⁻¹ * (1 + ξ * x / σ) ^ (-(1 / ξ) - 1)) x := by
      have := (hd0.rpow_const (p := -(1 / ξ)) (Or.inl hu.ne')).const_sub 1
      convert this using 1
      field_simp
    simp only [gpdDensity, hx.le, hu, and_self, ↓reduceIte, hξ]
    exact hd.congr_of_eventuallyEq heq

/-- Outside the two endpoints `0` and `-σ/ξ` the GPD distribution function is differentiable
with derivative the GPD density. -/
lemma hasDerivAt_gpdCDF_of_ne (hσ : 0 < σ) (h0 : x ≠ 0) (h1 : x ≠ -σ / ξ) :
    HasDerivAt (gpdCDF ξ σ) (gpdDensity ξ σ x) x := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have heq : gpdCDF ξ σ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hneg] with y hy
      exact gpdCDF_of_nonpos hy.le
    have : gpdDensity ξ σ x = 0 := by simp [gpdDensity, not_le.2 hneg]
    rw [this]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  rcases lt_trichotomy (1 + ξ * x / σ) 0 with hu | hu | hu
  · -- beyond the right endpoint
    have hξ : ξ ≠ 0 := by rintro rfl; simp at hu; linarith
    have hev : ∀ᶠ y in 𝓝 x, 0 < y ∧ 1 + ξ * y / σ < 0 :=
      (lt_mem_nhds hpos).and ((continuous_const.add ((continuous_const.mul continuous_id).div_const
        σ)).continuousAt.eventually (gt_mem_nhds hu))
    have hne : -(1 / ξ) ≠ 0 := by simp [hξ]
    have heq : gpdCDF ξ σ =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [hev] with y hy
      simp [gpdCDF, gpdSurvival', hξ, max_eq_left hy.1.le, max_eq_right hy.2.le]
    have : gpdDensity ξ σ x = 0 := by simp [gpdDensity, not_lt.2 hu.le]
    rw [this]
    exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq heq
  · exfalso
    have hξ : ξ ≠ 0 := by rintro rfl; simp at hu
    have : ξ * x = -σ := by field_simp at hu; linarith
    exact h1 (by rw [eq_div_iff hξ]; linarith)
  · exact hasDerivAt_gpdCDF hσ hpos hu

/-- **The GPD has density `gpdDensity`**: `GPD(ξ, σ) = g_{ξ,σ}(x) dx`. -/
theorem gpdMeasure_eq_withDensity (hσ : 0 < σ) :
    gpdMeasure ξ σ = volume.withDensity (fun x => ENNReal.ofReal (gpdDensity ξ σ x)) := by
  refine eq_withDensity_of_hasDerivAt_off (F := gpdCDF ξ σ) (c₁ := 0) (c₂ := -σ / ξ)
    (continuous_gpdCDF hσ) ?_ (gpdMeasure_Iic hσ) (fun x h0 h1 => hasDerivAt_gpdCDF_of_ne hσ h0 h1)
    (gpdDensity_nonneg hσ ξ)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_le_atBot 0] with x hx
  exact (gpdCDF_of_nonpos hx).symm

/-- **The GPD density integrates to one.** -/
theorem integral_gpdDensity (hσ : 0 < σ) : ∫ x, gpdDensity ξ σ x = 1 :=
  (integral_eq_one_of_eq_withDensity (gpdMeasure_eq_withDensity hσ) (gpdDensity_nonneg hσ ξ)
    (measurable_gpdDensity ξ σ).aestronglyMeasurable).2

/-- Integrals against `GPD(ξ, σ)` through the exponential representation. -/
theorem integral_gpdMeasure {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂gpdMeasure ξ σ = ∫ x, f (gpdTransform ξ σ x) ∂expMeasure 1 := by
  rw [gpdMeasure, stdExpMeasure_eq_expMeasure, integral_map
    (measurable_gpdTransform ξ σ).aemeasurable hf.aestronglyMeasurable]

/-- Integrability against `GPD(ξ, σ)` through the exponential representation. -/
theorem integrable_gpdMeasure_iff {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (gpdMeasure ξ σ) ↔ Integrable (fun t => f (gpdTransform ξ σ t)) (expMeasure 1) := by
  rw [gpdMeasure, stdExpMeasure_eq_expMeasure, integrable_map_measure hf.aestronglyMeasurable
    (measurable_gpdTransform ξ σ).aemeasurable]
  rfl

end GPD

/-! ### The log-likelihood -/

section LogLik

variable {ξ σ x : ℝ} {n : ℕ}

/-- The **GPD log-likelihood** `ℓ(ξ, σ; x) = ∑ᵢ log g_{ξ,σ}(xᵢ)` of a sample `x`.

This is the log-likelihood only for *admissible* parameters, i.e. when every `xᵢ` lies in the
support of `GPD(ξ, σ)` (and `σ > 0`). Off the support Lean's convention `log 0 = 0` turns each
offending term into the junk value `0` rather than `-∞`, and this junk can exceed the
log-likelihood at admissible parameters, so `gpdLogLik` must not be maximized over all
parameters. The maximum-likelihood results maximize within the admissible domain: the scale
MLE over `gpdScaleDomain ξ x`, and the joint MLE (`ae_tendsto_gpdMLE`) over compact sets of
parameters with `ξ > 0`, `σ > 0`, where every nonnegative observation is in the support. -/
noncomputable def gpdLogLik (ξ σ : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, log (gpdDensity ξ σ (x i))

/-- The log-density of the exponential law `GPD(0, σ)`: `-log σ - x / σ` for `x ≥ 0`. -/
lemma log_gpdDensity_zero (hσ : 0 < σ) (hx : 0 ≤ x) :
    log (gpdDensity 0 σ x) = -log σ - x / σ := by
  simp only [gpdDensity, hx, zero_mul, zero_div, add_zero, zero_lt_one, and_self, ↓reduceIte]
  rw [log_mul (inv_ne_zero hσ.ne') (exp_pos _).ne', log_inv, log_exp]
  ring

/-- The GPD log-density on the support: `-log σ - (1/ξ + 1) log (1 + ξ x / σ)`. -/
lemma log_gpdDensity (hσ : 0 < σ) (hξ : ξ ≠ 0) (hx : 0 ≤ x) (hu : 0 < 1 + ξ * x / σ) :
    log (gpdDensity ξ σ x) = -log σ - (1 / ξ + 1) * log (1 + ξ * x / σ) := by
  simp only [gpdDensity, hx, hu, and_self, ↓reduceIte, hξ]
  rw [log_mul (inv_ne_zero hσ.ne') (rpow_pos_of_pos hu _).ne', log_inv, log_rpow hu]
  ring

/-- The sample mean `(1/n) ∑ᵢ xᵢ`. -/
noncomputable def sampleMean (x : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i, x i

lemma natCast_mul_sampleMean (x : Fin n → ℝ) : n * sampleMean x = ∑ i, x i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sampleMean]
  · rw [sampleMean, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The exponential log-likelihood: `ℓ(0, σ; x) = -n log σ - n x̄ / σ` for a nonnegative sample. -/
lemma gpdLogLik_zero_eq (hσ : 0 < σ) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    gpdLogLik 0 σ x = -n * log σ - n * sampleMean x / σ := by
  rw [gpdLogLik, Finset.sum_congr rfl fun i _ => log_gpdDensity_zero hσ (hx i),
    natCast_mul_sampleMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_div]
  ring

/-- **The exponential MLE is the sample mean.** For a nonnegative sample with positive mean,
`σ̂ = x̄` is the unique maximizer over `σ > 0` of the `GPD(0, σ)` (exponential) log-likelihood. -/
theorem gpdLogLik_zero_lt_sampleMean {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hm : 0 < sampleMean x) (hσ : 0 < σ) (hne : σ ≠ sampleMean x) :
    gpdLogLik 0 σ x < gpdLogLik 0 (sampleMean x) x := by
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleMean] at hm
    · exact_mod_cast hn
  set m := sampleMean x
  rw [gpdLogLik_zero_eq hσ hx, gpdLogLik_zero_eq hm hx]
  have hr : 0 < m / σ := div_pos hm hσ
  have hr1 : m / σ ≠ 1 := fun h => hne ((div_eq_one_iff_eq hσ.ne').1 h).symm
  have hlog := log_lt_sub_one_of_pos hr hr1
  rw [log_div hm.ne' hσ.ne'] at hlog
  have : n * (log m - log σ) < n * (m / σ - 1) := mul_lt_mul_of_pos_left hlog hn
  have e : (n : ℝ) * m / m = n := by field_simp
  rw [e]
  have e2 : (n : ℝ) * m / σ = n * (m / σ) := by ring
  rw [e2]
  linarith

/-- The exponential MLE maximizes the likelihood. -/
theorem isMaxOn_gpdLogLik_zero {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hm : 0 < sampleMean x) :
    IsMaxOn (fun σ => gpdLogLik 0 σ x) (Ioi 0) (sampleMean x) := by
  intro σ hσ
  rcases eq_or_ne σ (sampleMean x) with h | h
  · simp [h]
  · exact (gpdLogLik_zero_lt_sampleMean hx hm hσ h).le

end LogLik

/-! ### The exponential case: consistency and asymptotic normality of the MLE -/

section Exponential

variable {σ : ℝ}

lemma gpdTransform_zero (σ : ℝ) : gpdTransform 0 σ = fun t => σ * t := by
  funext t; simp [gpdTransform]

lemma gpdMeasure_zero_eq_map (σ : ℝ) : gpdMeasure 0 σ = (expMeasure 1).map (fun t => σ * t) := by
  rw [gpdMeasure, stdExpMeasure_eq_expMeasure, gpdTransform_zero]

lemma integrable_id_gpdMeasure_zero (σ : ℝ) : Integrable id (gpdMeasure 0 σ) := by
  rw [integrable_gpdMeasure_iff measurable_id, gpdTransform_zero]
  simpa using (integrable_pow_expMeasure 1).const_mul σ

lemma integral_id_gpdMeasure_zero (σ : ℝ) : ∫ x, x ∂gpdMeasure 0 σ = σ := by
  have := integral_gpdMeasure (ξ := 0) (σ := σ) measurable_id
  simp only [id, gpdTransform_zero] at this
  rw [this, integral_const_mul, integral_id_expMeasure, mul_one]

lemma memLp_two_id_gpdMeasure_zero (σ : ℝ) : MemLp id 2 (gpdMeasure 0 σ) := by
  rw [gpdMeasure_zero_eq_map, memLp_map_measure_iff aestronglyMeasurable_id
    (by fun_prop)]
  exact memLp_two_id_expMeasure.const_mul σ

lemma variance_id_gpdMeasure_zero (σ : ℝ) : Var[id; gpdMeasure 0 σ] = σ ^ 2 := by
  rw [gpdMeasure_zero_eq_map, variance_map aemeasurable_id (by fun_prop), Function.id_comp,
    variance_const_mul, show (fun t : ℝ => t) = id from rfl, variance_id_expMeasure, mul_one]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

lemma sampleMean_eq_range (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleMean (fun i : Fin n => X i ω) = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
  rw [sampleMean, Fin.sum_univ_eq_sum_range (fun i => X i ω) n]

omit [IsProbabilityMeasure P] in
/-- **Strong consistency of the exponential MLE.** If `X₀, X₁, …` are iid `GPD(0, σ)`
(exponential with mean `σ`), the MLE `σ̂ₙ = X̄ₙ` converges to `σ` almost surely. -/
theorem ae_tendsto_sampleMean_gpd_zero (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ) P)
    (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sampleMean (fun i : Fin n => X i ω)) atTop (𝓝 σ) := by
  have hint : Integrable (X 0) P := (hX 0).integrable (integrable_id_gpdMeasure_zero σ)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [(hX i).map_eq, (hX 0).map_eq]⟩
  have hmean : P[X 0] = σ := by rw [(hX 0).integral_eq, integral_id_gpdMeasure_zero]
  filter_upwards [strong_law_ae X hint (fun i j hij => hind.indepFun hij) hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  rw [sampleMean_eq_range, smul_eq_mul]

/-- **Asymptotic normality of the exponential MLE.** If `X₀, X₁, …` are iid `GPD(0, σ)`, then
`√n (σ̂ₙ - σ) ⇒ N(0, σ²)`, where `σ̂ₙ = X̄ₙ` is the MLE. -/
theorem tendstoInDistribution_sampleMean_gpd_zero (hX : ∀ i, HasLaw (X i) (gpdMeasure 0 σ) P)
    (hind : iIndepFun X P) {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (σ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (sampleMean (fun i : Fin n => X i ω) - σ))
      atTop Z (fun _ => P) P' := by
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [(hX i).map_eq, (hX 0).map_eq]⟩
  have hmean : P[X 0] = σ := by rw [(hX 0).integral_eq, integral_id_gpdMeasure_zero]
  have hvar : Var[X 0; P] = σ ^ 2 := by rw [(hX 0).variance_eq, variance_id_gpdMeasure_zero]
  have hL2 : MemLp (X 0) 2 P := (hX 0).memLp (memLp_two_id_gpdMeasure_zero σ)
  have hZ' : HasLaw Z (gaussianReal 0 Var[X 0; P].toNNReal) P' := by rw [hvar]; exact hZ
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ' hL2 hind hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  rw [sampleMean_eq_range]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : √(n : ℝ) ^ 2 = n := sq_sqrt hn'.le
    have hs0 : √(n : ℝ) ≠ 0 := (sqrt_pos.2 hn').ne'
    field_simp
    rw [hs]

end Exponential

/-! ### The scale MLE for a known shape -/

section FixedShape

variable {ξ σ : ℝ} {n : ℕ} {x : Fin n → ℝ}

/-- The admissible scales for a sample `x` at shape `ξ`: the `σ > 0` such that every `xᵢ` lies in
the support of `GPD(ξ, σ)`, i.e. `σ + ξ xᵢ > 0`. Outside this set the likelihood vanishes. -/
def gpdScaleDomain (ξ : ℝ) (x : Fin n → ℝ) : Set ℝ := {σ | 0 < σ ∧ ∀ i, 0 < σ + ξ * x i}

/-- The **scale score** `∑ᵢ xᵢ / (σ + ξ xᵢ)`: the likelihood equation in `σ` for a known shape
`ξ` reads `(1 + ξ) ∑ᵢ xᵢ / (σ + ξ xᵢ) = n` (`hasDerivAt_gpdLogLik`). -/
noncomputable def gpdScaleScore (ξ σ : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, x i / (σ + ξ * x i)

lemma mem_gpdScaleDomain_of_le {τ : ℝ} (hσ : σ ∈ gpdScaleDomain ξ x)
    (h : σ ≤ τ) : τ ∈ gpdScaleDomain ξ x :=
  ⟨hσ.1.trans_le h, fun i => (hσ.2 i).trans_le (by linarith)⟩

lemma gpdScaleScore_anti (hx : ∀ i, 0 ≤ x i) {τ : ℝ} (hσ : σ ∈ gpdScaleDomain ξ x)
    (h : σ ≤ τ) : gpdScaleScore ξ τ x ≤ gpdScaleScore ξ σ x :=
  Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (hx i) (hσ.2 i) (by linarith)

lemma gpdScaleScore_strictAnti (hn : 0 < n) (hx : ∀ i, 0 < x i) {τ : ℝ}
    (hσ : σ ∈ gpdScaleDomain ξ x) (h : σ < τ) : gpdScaleScore ξ τ x < gpdScaleScore ξ σ x :=
  Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ =>
    div_lt_div_of_pos_left (hx i) (hσ.2 i) (by linarith)

lemma continuousOn_gpdScaleScore :
    ContinuousOn (fun s => gpdScaleScore ξ s x) (gpdScaleDomain ξ x) := by
  unfold gpdScaleScore
  refine continuousOn_finsetSum _ fun i _ => ?_
  exact continuousOn_const.div (continuousOn_id.add continuousOn_const) fun s hs => (hs.2 i).ne'

lemma eventually_mem_gpdScaleDomain (hσ : σ ∈ gpdScaleDomain ξ x) :
    ∀ᶠ s in 𝓝 σ, s ∈ gpdScaleDomain ξ x := by
  refine (lt_mem_nhds hσ.1).and (eventually_all.2 fun i => ?_)
  exact (continuous_id.add continuous_const).continuousAt.eventually (lt_mem_nhds (hσ.2 i))

/-- **The scale score is the derivative of the log-likelihood**: on the admissible scales,
`∂ℓ/∂σ = σ⁻¹ ((1 + ξ) ∑ᵢ xᵢ / (σ + ξ xᵢ) - n)`. -/
theorem hasDerivAt_gpdLogLik (hξ : ξ ≠ 0) (hx : ∀ i, 0 ≤ x i) (hσ : σ ∈ gpdScaleDomain ξ x) :
    HasDerivAt (fun s => gpdLogLik ξ s x)
      (σ⁻¹ * ((1 + ξ) * gpdScaleScore ξ σ x - n)) σ := by
  have heq : (fun s => gpdLogLik ξ s x) =ᶠ[𝓝 σ]
      fun s => ∑ i, (1 / ξ * log s - (1 / ξ + 1) * log (s + ξ * x i)) := by
    filter_upwards [eventually_mem_gpdScaleDomain hσ] with s hs
    refine Finset.sum_congr rfl fun i _ => ?_
    have hu : 1 + ξ * x i / s = (s + ξ * x i) / s := by field_simp [hs.1.ne']
    have hu' : 0 < 1 + ξ * x i / s := hu ▸ div_pos (hs.2 i) hs.1
    rw [log_gpdDensity hs.1 hξ (hx i) hu', hu, log_div (hs.2 i).ne' hs.1.ne']
    ring
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have hterm : ∀ i, HasDerivAt (fun s => 1 / ξ * log s - (1 / ξ + 1) * log (s + ξ * x i))
      (σ⁻¹ * ((1 + ξ) * (x i / (σ + ξ * x i)) - 1)) σ := by
    intro i
    have h1 := (hasDerivAt_log hσ.1.ne').const_mul (1 / ξ)
    have h2 := (((hasDerivAt_id σ).add_const (ξ * x i)).log (hσ.2 i).ne').const_mul (1 / ξ + 1)
    refine (h1.sub h2).congr_deriv ?_
    have := hσ.2 i
    have := hσ.1
    simp only [id]
    field_simp
    ring
  convert HasDerivAt.sum (u := Finset.univ) fun i _ => hterm i using 1
  · funext s; simp
  · rw [gpdScaleScore, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp

/-- Near the lower end of the admissible scales the score exceeds `n / (1 + ξ)`. -/
lemma exists_lt_gpdScaleScore (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hn : 0 < n) (hx : ∀ i, 0 < x i) :
    ∃ σ ∈ gpdScaleDomain ξ x, (n : ℝ) < (1 + ξ) * gpdScaleScore ξ σ x := by
  have h1ξ : 0 < 1 + ξ := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · -- `ξ < 0`: the term of the largest observation blows up at the lower end `-ξ max xᵢ`
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ x ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    set δ := x i₀ * (1 + ξ) / (2 * n)
    have hδ : 0 < δ := div_pos (mul_pos (hx i₀) h1ξ) (by positivity)
    have hmem : -ξ * x i₀ + δ ∈ gpdScaleDomain ξ x := by
      refine ⟨by nlinarith [hx i₀], fun i => ?_⟩
      have : ξ * x i₀ ≤ ξ * x i := mul_le_mul_of_nonpos_left (hi₀ i (Finset.mem_univ _)) hneg.le
      linarith
    refine ⟨_, hmem, ?_⟩
    have hsingle : x i₀ / (-ξ * x i₀ + δ + ξ * x i₀) ≤ gpdScaleScore ξ (-ξ * x i₀ + δ) x :=
      Finset.single_le_sum (f := fun i => x i / (-ξ * x i₀ + δ + ξ * x i))
        (fun i _ => div_nonneg (hx i).le (hmem.2 i).le) (Finset.mem_univ i₀)
    have he : x i₀ / (-ξ * x i₀ + δ + ξ * x i₀) = 2 * n / (1 + ξ) := by
      rw [show -ξ * x i₀ + δ + ξ * x i₀ = δ by ring]
      simp only [δ]
      field_simp [(hx i₀).ne']
    rw [he] at hsingle
    have : (1 + ξ) * (2 * n / (1 + ξ)) = 2 * n := by field_simp
    nlinarith
  · -- `ξ > 0`: the score is continuous at `σ = 0`, where it equals `n / ξ`
    have hcont : ContinuousAt (fun s => (1 + ξ) * gpdScaleScore ξ s x) 0 := by
      unfold gpdScaleScore
      refine continuousAt_const.mul (tendsto_finsetSum _ fun i _ => ?_)
      exact continuousAt_const.div (continuousAt_id.add continuousAt_const)
        (by simp; exact ⟨hpos.ne', (hx i).ne'⟩)
    have h0 : (n : ℝ) < (1 + ξ) * gpdScaleScore ξ 0 x := by
      have : gpdScaleScore ξ 0 x = n / ξ := by
        simp only [gpdScaleScore, zero_add]
        rw [Finset.sum_congr rfl fun i _ => show x i / (ξ * x i) = 1 / ξ by
          field_simp [(hx i).ne']]
        simp [div_eq_mul_inv]
      rw [this, ← sub_pos]
      have : (1 + ξ) * (n / ξ) - n = n / ξ := by field_simp; ring
      rw [this]; positivity
    obtain ⟨s, hs, hs0⟩ := (((hcont.eventually (lt_mem_nhds h0)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
    exact ⟨s, ⟨hs0, fun i => by have := hx i; positivity⟩, hs⟩

/-- **Existence of the scale MLE.** For a known shape `ξ > -1`, `ξ ≠ 0`, and a sample of
positive observations, the likelihood equation `(1 + ξ) ∑ᵢ xᵢ / (σ + ξ xᵢ) = n` has a root among
the admissible scales. -/
theorem exists_gpdScaleScore_eq (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hn : 0 < n) (hx : ∀ i, 0 < x i) :
    ∃ σ ∈ gpdScaleDomain ξ x, (1 + ξ) * gpdScaleScore ξ σ x = n := by
  obtain ⟨σ₁, hσ₁, h₁⟩ := exists_lt_gpdScaleScore hξ1 hξ hn hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlim : Tendsto (fun s => (1 + ξ) * gpdScaleScore ξ s x) atTop (𝓝 0) := by
    have : Tendsto (fun s => gpdScaleScore ξ s x) atTop (𝓝 0) := by
      unfold gpdScaleScore
      rw [show (0 : ℝ) = ∑ _i : Fin n, (0 : ℝ) by simp]
      exact tendsto_finsetSum _ fun i _ =>
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
    simpa using this.const_mul (1 + ξ)
  obtain ⟨σ₂, h₂, hle⟩ := ((hlim.eventually (gt_mem_nhds hn')).and
    (eventually_ge_atTop σ₁)).exists
  have hsub : Icc σ₁ σ₂ ⊆ gpdScaleDomain ξ x := fun s hs => mem_gpdScaleDomain_of_le hσ₁ hs.1
  have hcont : ContinuousOn (fun s => (1 + ξ) * gpdScaleScore ξ s x) (Icc σ₁ σ₂) :=
    (continuousOn_const.mul continuousOn_gpdScaleScore).mono hsub
  obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc' hle hcont ⟨h₂.le, h₁.le⟩
  exact ⟨σ, hsub hσ, hσeq⟩

/-- **Uniqueness of the root of the scale likelihood equation.** -/
theorem gpdScaleScore_root_unique (hξ1 : -1 < ξ) (hn : 0 < n) (hx : ∀ i, 0 < x i) {σ τ : ℝ}
    (hσ : σ ∈ gpdScaleDomain ξ x) (hτ : τ ∈ gpdScaleDomain ξ x)
    (hσe : (1 + ξ) * gpdScaleScore ξ σ x = n) (hτe : (1 + ξ) * gpdScaleScore ξ τ x = n) :
    σ = τ := by
  have h1ξ : 0 < 1 + ξ := by linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := mul_lt_mul_of_pos_left (gpdScaleScore_strictAnti hn hx hσ h) h1ξ
    linarith
  · have := mul_lt_mul_of_pos_left (gpdScaleScore_strictAnti hn hx hτ h) h1ξ
    linarith

/-- **The root of the scale likelihood equation is the unique maximizer of the likelihood.**
For a known shape `ξ > -1`, `ξ ≠ 0`, and positive observations, if `σ̂` solves
`(1 + ξ) ∑ᵢ xᵢ / (σ̂ + ξ xᵢ) = n`, then `ℓ(ξ, σ) < ℓ(ξ, σ̂)` for every other admissible `σ`. The
score `σ ↦ ∂ℓ/∂σ` changes sign exactly once, from `+` to `-`, at `σ̂`. -/
theorem gpdLogLik_lt_of_score_eq (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hn : 0 < n) (hx : ∀ i, 0 < x i)
    {σh : ℝ} (hσh : σh ∈ gpdScaleDomain ξ x) (hroot : (1 + ξ) * gpdScaleScore ξ σh x = n)
    (hσ : σ ∈ gpdScaleDomain ξ x) (hne : σ ≠ σh) : gpdLogLik ξ σ x < gpdLogLik ξ σh x := by
  have h1ξ : 0 < 1 + ξ := by linarith
  have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).le
  have hd := fun s (hs : s ∈ gpdScaleDomain ξ x) => hasDerivAt_gpdLogLik hξ hx0 hs
  have hcont : ∀ a b, a ∈ gpdScaleDomain ξ x →
      ContinuousOn (fun s => gpdLogLik ξ s x) (Icc a b) := fun a b ha s hs =>
    (hd s (mem_gpdScaleDomain_of_le ha hs.1)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with h | h
  · refine strictMonoOn_of_deriv_pos (convex_Icc σ σh) (hcont σ σh hσ) (fun t ht => ?_)
      ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h
    rw [interior_Icc] at ht
    have hst := mem_gpdScaleDomain_of_le hσ ht.1.le
    rw [(hd t hst).deriv]
    have := mul_lt_mul_of_pos_left (gpdScaleScore_strictAnti hn hx hst ht.2) h1ξ
    exact mul_pos (inv_pos.2 hst.1) (by linarith)
  · refine strictAntiOn_of_deriv_neg (convex_Icc σh σ) (hcont σh σ hσh) (fun t ht => ?_)
      ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h
    rw [interior_Icc] at ht
    have hst := mem_gpdScaleDomain_of_le hσh ht.1.le
    rw [(hd t hst).deriv]
    have := mul_lt_mul_of_pos_left (gpdScaleScore_strictAnti hn hx hσh ht.1) h1ξ
    exact mul_neg_of_pos_of_neg (inv_pos.2 hst.1) (by linarith)

end FixedShape

/-! ### Strong consistency of the scale MLE for a known shape -/

section Consistency

variable {ξ σ σ₀ : ℝ}

lemma ae_pos_expMeasure : ∀ᵐ t ∂expMeasure 1, 0 < t := by
  rw [← stdExpMeasure_eq_expMeasure, ae_iff]
  have h1 : {t : ℝ | ¬ 0 < t} = Iic 0 := by ext; simp
  have h2 : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := Set.ext fun t => by
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact id
  rw [h1, stdExpMeasure, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, h2, Measure.restrict_empty,
    lintegral_zero_measure]

/-- `GPD(ξ, σ)` is carried by its support `{x > 0, σ + ξ x > 0}`. -/
lemma ae_gpdMeasure (hσ : 0 < σ) : ∀ᵐ y ∂gpdMeasure ξ σ, 0 < y ∧ 0 < σ + ξ * y := by
  rw [gpdMeasure, stdExpMeasure_eq_expMeasure]
  refine (ae_map_iff (measurable_gpdTransform ξ σ).aemeasurable ?_).2 ?_
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_const (show Measurable fun y : ℝ => σ + ξ * y by fun_prop))
  · filter_upwards [ae_pos_expMeasure] with t ht
    refine ⟨gpdTransform_pos hσ ht, ?_⟩
    by_cases hξ : ξ = 0
    · simp [hξ, hσ]
    · have h := one_add_mul_gpdTransform hσ hξ t
      have : σ + ξ * gpdTransform ξ σ t = σ * exp (ξ * t) := by
        rw [← h]; field_simp
      rw [this]; positivity

/-- On the exponential scale, the score term at the true scale is explicit:
`T(t) / (σ + ξ T(t)) = (1 - e^{-ξ t}) / ξ`. -/
lemma gpdTransform_div (hσ : 0 < σ) (hξ : ξ ≠ 0) (t : ℝ) :
    gpdTransform ξ σ t / (σ + ξ * gpdTransform ξ σ t) = (1 - exp (-(ξ * t))) / ξ := by
  have h := one_add_mul_gpdTransform hσ hξ t
  have : σ + ξ * gpdTransform ξ σ t = σ * exp (ξ * t) := by
    rw [← h]; field_simp
  rw [this, exp_neg]
  simp only [gpdTransform, hξ, ↓reduceIte]
  field_simp

/-- **The population score equation**: under `GPD(ξ, σ)`, `E[X / (σ + ξ X)] = 1 / (1 + ξ)`. -/
theorem integral_div_gpdMeasure (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hσ : 0 < σ) :
    ∫ y, y / (σ + ξ * y) ∂gpdMeasure ξ σ = 1 / (1 + ξ) := by
  have h1ξ : 0 < 1 + ξ := by linarith
  rw [integral_gpdMeasure (by fun_prop)]
  simp_rw [gpdTransform_div hσ hξ]
  have heq : ∀ t : ℝ, exp (-(1 + ξ) * t) = exp (-t) * exp (-(ξ * t)) := fun t => by
    rw [← exp_add]; congr 1; ring
  have hint : Integrable (fun t => exp (-(ξ * t))) (expMeasure 1) := by
    rw [integrable_expMeasure_iff]
    exact (integrableOn_exp_mul_Ioi (a := -(1 + ξ)) (by linarith) 0).congr_fun
      (fun t _ => heq t) measurableSet_Ioi
  have hval : ∫ t, exp (-(ξ * t)) ∂expMeasure 1 = 1 / (1 + ξ) := by
    rw [integral_expMeasure, ← setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t)]
    exact integral_exp_neg_mul_Ioi h1ξ
  rw [integral_div, integral_sub (integrable_const 1) hint, integral_const, hval]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

/-- The score terms are integrable: for `ξ > 0` they are bounded by `1/ξ`, and for `ξ < 0`,
`σ > σ₀`, by `σ₀ / (-ξ (σ - σ₀))`. -/
lemma integrable_div_gpdMeasure (hσ₀ : 0 < σ₀) (h : 0 < ξ ∧ 0 < σ ∨ ξ < 0 ∧ σ₀ < σ) :
    Integrable (fun y => y / (σ + ξ * y)) (gpdMeasure ξ σ₀) := by
  have hm : AEStronglyMeasurable (fun y : ℝ => y / (σ + ξ * y)) (gpdMeasure ξ σ₀) :=
    (by fun_prop : Measurable fun y : ℝ => y / (σ + ξ * y)).aestronglyMeasurable
  rcases h with ⟨hξ, hσ⟩ | ⟨hξ, hσ⟩
  · refine Integrable.of_bound hm (1 / ξ) ?_
    filter_upwards [ae_gpdMeasure hσ₀] with y hy
    have hden : 0 < σ + ξ * y := by nlinarith [hy.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hy.1.le hden.le), div_le_div_iff₀ hden hξ]
    linarith
  · refine Integrable.of_bound hm (σ₀ / -ξ / (σ - σ₀)) ?_
    filter_upwards [ae_gpdMeasure hσ₀] with y hy
    have hden : 0 < σ + ξ * y := by linarith [hy.2]
    have hy' : y ≤ σ₀ / -ξ := by rw [le_div_iff₀ (by linarith)]; linarith [hy.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hy.1.le hden.le)]
    calc y / (σ + ξ * y) ≤ y / (σ - σ₀) :=
          div_le_div_of_nonneg_left hy.1.le (by linarith) (by linarith [hy.2])
      _ ≤ σ₀ / -ξ / (σ - σ₀) := div_le_div_of_nonneg_right hy' (by linarith)

private lemma integral_pos_of_ae_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : ∀ᵐ y ∂μ, 0 < f y) (hi : Integrable f μ) : 0 < ∫ y, f y ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae (hf.mono fun y hy => hy.le) hi]
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have : ∀ᵐ y ∂μ, f y = 0 := by
    rw [ae_iff]; simpa [Function.support] using h0
  obtain ⟨y, h1, h2⟩ := (hf.and this).exists
  linarith

/-- The population score `σ ↦ E[X / (σ + ξ X)]` is strictly decreasing. -/
lemma integral_div_gpdMeasure_lt {a b : ℝ} (hab : a < b)
    (hsupp : ∀ᵐ y ∂gpdMeasure ξ σ₀, 0 < y ∧ 0 < a + ξ * y)
    (ha : Integrable (fun y => y / (a + ξ * y)) (gpdMeasure ξ σ₀))
    (hb : Integrable (fun y => y / (b + ξ * y)) (gpdMeasure ξ σ₀)) :
    ∫ y, y / (b + ξ * y) ∂gpdMeasure ξ σ₀ < ∫ y, y / (a + ξ * y) ∂gpdMeasure ξ σ₀ := by
  have := integral_pos_of_ae_pos (μ := gpdMeasure ξ σ₀)
    (f := fun y => y / (a + ξ * y) - y / (b + ξ * y)) ?_ (ha.sub hb)
  · rw [integral_sub ha hb] at this; linarith
  · filter_upwards [hsupp] with y hy
    exact sub_pos.2 (div_lt_div_of_pos_left hy.1 hy.2 (by linarith))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The strong law of large numbers for a function of an iid sequence. -/
lemma ae_tendsto_avg_comp {α : Type*} {mα : MeasurableSpace α} {X : ℕ → Ω → α} {μ : Measure α}
    (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    {g : α → ℝ} (hg : Measurable g) (hgi : Integrable g μ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)) atTop
      (𝓝 (∫ y, g y ∂μ)) := by
  have hint : Integrable (g ∘ X 0) P := (hX 0).integrable_comp hgi
  have hind' : iIndepFun (fun i => g ∘ X i) P := hind.comp (fun _ => g) (fun _ => hg)
  have hident : ∀ i, IdentDistrib (g ∘ X i) (g ∘ X 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hg
  have hmean : P[g ∘ X 0] = ∫ y, g y ∂μ := (hX 0).integral_comp hg.aestronglyMeasurable
  filter_upwards [strong_law_ae (fun i => g ∘ X i) hint (fun i j hij => hind'.indepFun hij)
    hident] with ω hω
  rw [hmean] at hω
  simpa [smul_eq_mul] using hω

lemma gpdScaleScore_eq_range (ξ τ : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    gpdScaleScore ξ τ (fun i : Fin n => x i) = ∑ i ∈ Finset.range n, x i / (τ + ξ * x i) :=
  Fin.sum_univ_eq_sum_range (fun i => x i / (τ + ξ * x i)) n

/-- The deterministic upper bound: if the empirical score at `τ > σ₀` is eventually below
`1 / (1 + ξ)`, every root of the likelihood equation is eventually below `τ`. -/
private lemma eventually_lt_of_avg (hξ1 : -1 < ξ) (hσ₀ : 0 < σ₀) {x : ℕ → ℝ}
    (hx : ∀ i, 0 < x i ∧ 0 < σ₀ + ξ * x i) {τ m : ℝ} (hτ : σ₀ < τ) (hm : m < 1 / (1 + ξ))
    (havg : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i / (τ + ξ * x i))
      atTop (𝓝 m)) {s : ℕ → ℝ}
    (hs : ∀ᶠ n in atTop, s n ∈ gpdScaleDomain ξ (fun i : Fin n => x i) ∧
      (1 + ξ) * gpdScaleScore ξ (s n) (fun i : Fin n => x i) = n) :
    ∀ᶠ n in atTop, s n < τ := by
  have h1ξ : 0 < 1 + ξ := by linarith
  filter_upwards [hs, havg.eventually (gt_mem_nhds hm), eventually_gt_atTop 0]
    with n hn hlt hn0
  by_contra hge
  have hge := not_lt.1 hge
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hτD : τ ∈ gpdScaleDomain ξ (fun i : Fin n => x i) :=
    ⟨by linarith, fun i => by linarith [(hx i).2]⟩
  have hanti := gpdScaleScore_anti (fun i => (hx i).1.le) hτD hge
  have h1 : gpdScaleScore ξ (s n) (fun i : Fin n => x i) = n / (1 + ξ) := by
    rw [eq_div_iff h1ξ.ne', mul_comm, hn.2]
  have h2 := gpdScaleScore_eq_range ξ τ x n
  rw [inv_mul_lt_iff₀ hn'] at hlt
  have : (n : ℝ) / (1 + ξ) = n * (1 / (1 + ξ)) := by ring
  linarith

/-- The deterministic lower bound for `ξ > 0`. -/
private lemma eventually_gt_of_avg (hξ : 0 < ξ) {x : ℕ → ℝ} (hx : ∀ i, 0 < x i) {l m : ℝ}
    (hm : 1 / (1 + ξ) < m)
    (havg : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i / (l + ξ * x i))
      atTop (𝓝 m)) {s : ℕ → ℝ}
    (hs : ∀ᶠ n in atTop, s n ∈ gpdScaleDomain ξ (fun i : Fin n => x i) ∧
      (1 + ξ) * gpdScaleScore ξ (s n) (fun i : Fin n => x i) = n) :
    ∀ᶠ n in atTop, l < s n := by
  have h1ξ : 0 < 1 + ξ := by linarith
  filter_upwards [hs, havg.eventually (lt_mem_nhds hm), eventually_gt_atTop 0]
    with n hn hlt hn0
  by_contra hge
  have hge := not_lt.1 hge
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hanti := gpdScaleScore_anti (fun i => (hx i).le) hn.1 hge
  have h1 : gpdScaleScore ξ (s n) (fun i : Fin n => x i) = n / (1 + ξ) := by
    rw [eq_div_iff h1ξ.ne', mul_comm, hn.2]
  have h2 := gpdScaleScore_eq_range ξ l x n
  rw [lt_inv_mul_iff₀ hn'] at hlt
  have : (n : ℝ) / (1 + ξ) = n * (1 / (1 + ξ)) := by ring
  linarith

private lemma tendsto_of_bounds {s l u : ℕ → ℝ} {c : ℝ} (hl : Tendsto l atTop (𝓝 c))
    (hu : Tendsto u atTop (𝓝 c)) (hsl : ∀ k, ∀ᶠ n in atTop, l k < s n)
    (hsu : ∀ k, ∀ᶠ n in atTop, s n < u k) : Tendsto s atTop (𝓝 c) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk⟩ := (hl.eventually (lt_mem_nhds ha)).exists
    exact (hsl k).mono fun n hn => hk.trans hn
  · obtain ⟨k, hk⟩ := (hu.eventually (gt_mem_nhds hb)).exists
    exact (hsu k).mono fun n hn => hn.trans hk

/-- **Existence of the scale MLE, almost surely.** For iid `GPD(ξ, σ₀)` data with known shape
`ξ > -1`, `ξ ≠ 0`, almost surely the likelihood equation has, for every `n ≥ 1`, a unique
admissible root, which is the unique maximizer of the likelihood. -/
theorem ae_existsUnique_gpdScaleMLE (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) :
    ∀ᵐ ω ∂P, ∀ n, 0 < n → ∃! σ, σ ∈ gpdScaleDomain ξ (fun i : Fin n => X i ω) ∧
      (1 + ξ) * gpdScaleScore ξ σ (fun i : Fin n => X i ω) = n ∧
      ∀ τ ∈ gpdScaleDomain ξ (fun i : Fin n => X i ω), τ ≠ σ →
        gpdLogLik ξ τ (fun i : Fin n => X i ω) < gpdLogLik ξ σ (fun i : Fin n => X i ω) := by
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω := ae_all_iff.2 fun i =>
    (ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)).mono fun _ h => h.1
  filter_upwards [hsupp] with ω hω n hn
  have hx : ∀ i : Fin n, 0 < X i ω := fun i => hω i
  obtain ⟨σ, hσ, hroot⟩ := exists_gpdScaleScore_eq hξ1 hξ hn hx
  exact ⟨σ, ⟨hσ, hroot, fun τ hτ hne => gpdLogLik_lt_of_score_eq hξ1 hξ hn hx hσ hroot hτ hne⟩,
    fun τ hτ => gpdScaleScore_root_unique hξ1 hn hx hτ.1 hσ hτ.2.1 hroot⟩

/-- **Strong consistency of the scale MLE for a known shape.** Let `X₀, X₁, …` be iid
`GPD(ξ, σ₀)` with known shape `ξ > -1`, `ξ ≠ 0`. Almost surely, every sequence `σ̂ₙ` of admissible
roots of the likelihood equation `(1 + ξ) ∑_{i<n} Xᵢ / (σ̂ₙ + ξ Xᵢ) = n` (equivalently, by
`ae_existsUnique_gpdScaleMLE`, the MLEs of `σ`) converges to `σ₀`. -/
theorem ae_tendsto_gpdScaleMLE (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, ∀ s : ℕ → ℝ, (∀ᶠ n in atTop, s n ∈ gpdScaleDomain ξ (fun i : Fin n => X i ω) ∧
      (1 + ξ) * gpdScaleScore ξ (s n) (fun i : Fin n => X i ω) = n) →
      Tendsto s atTop (𝓝 σ₀) := by
  have h1ξ : 0 < 1 + ξ := by linarith
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  -- the upper bounds `u k = σ₀ + 1/(k+1)`
  set u : ℕ → ℝ := fun k => σ₀ + 1 / ((k : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝 σ₀) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add σ₀
    rw [add_zero] at this
    exact this
  have hσu : ∀ k, σ₀ < u k := fun k => by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    simp only [u]; linarith
  have hiu : ∀ k, Integrable (fun y => y / (u k + ξ * y)) (gpdMeasure ξ σ₀) := fun k => by
    rcases lt_or_gt_of_ne hξ with hneg | hpos
    · exact integrable_div_gpdMeasure hσ₀ (Or.inr ⟨hneg, hσu k⟩)
    · exact integrable_div_gpdMeasure hσ₀ (Or.inl ⟨hpos, hσ₀.trans (hσu k)⟩)
  have hmu : ∀ k, ∫ y, y / (u k + ξ * y) ∂gpdMeasure ξ σ₀ < 1 / (1 + ξ) := fun k => by
    rw [← integral_div_gpdMeasure hξ1 hξ hσ₀]
    refine integral_div_gpdMeasure_lt (hσu k) (ae_gpdMeasure hσ₀) ?_ (hiu k)
    rcases lt_or_gt_of_ne hξ with hneg | hpos
    · -- at the true scale the score term is integrable by the explicit formula
      by_contra hni
      have := integral_div_gpdMeasure hξ1 hξ hσ₀
      rw [integral_undef hni] at this
      exact (one_div_pos.2 h1ξ).ne' this.symm
    · exact integrable_div_gpdMeasure hσ₀ (Or.inl ⟨hpos, hσ₀⟩)
  have hslln_u : ∀ᵐ ω ∂P, ∀ k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, X i ω / (u k + ξ * X i ω)) atTop
      (𝓝 (∫ y, y / (u k + ξ * y) ∂gpdMeasure ξ σ₀)) := ae_all_iff.2 fun k =>
    ae_tendsto_avg_comp hX hind (by fun_prop) (hiu k)
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · -- `ξ < 0`: the lower bound comes from the sample maximum approaching the endpoint
    set xF := -σ₀ / ξ
    have hxF : 0 < xF := div_pos_of_neg_of_neg (by linarith) hneg
    set a : ℕ → ℝ := fun k => max 0 (xF - 1 / ((k : ℝ) + 1))
    have ha : Tendsto a atTop (𝓝 xF) := by
      have := (tendsto_const_nhds (x := (0 : ℝ))).max
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub xF)
      rw [sub_zero, max_eq_right hxF.le] at this
      exact this
    have haF : ∀ k, a k < xF := fun k => max_lt hxF (by
      have : (0 : ℝ) < 1 / (k + 1) := by positivity
      linarith)
    have hexists : ∀ᵐ ω ∂P, ∀ k, ∃ i, a k < X i ω := by
      refine ae_all_iff.2 fun k => ?_
      have hgi : Integrable ((Ioi (a k)).indicator (1 : ℝ → ℝ)) (gpdMeasure ξ σ₀) :=
        (integrable_const 1).indicator measurableSet_Ioi
      have hmean : 0 < ∫ y, (Ioi (a k)).indicator (1 : ℝ → ℝ) y ∂gpdMeasure ξ σ₀ := by
        rw [integral_indicator_one measurableSet_Ioi, measureReal_def,
          gpdMeasure_Ioi hσ₀ (le_max_left _ _), ENNReal.toReal_ofReal (gpdSurvival'_nonneg _ _ _)]
        have hpos' : 0 < 1 + ξ * a k / σ₀ := by
          have h := haF k
          have : ξ * xF / σ₀ = -1 := by simp only [xF]; field_simp
          have : ξ * xF < ξ * a k := mul_lt_mul_of_neg_left h hneg
          have : ξ * xF / σ₀ < ξ * a k / σ₀ := div_lt_div_of_pos_right this hσ₀
          linarith
        rw [gpdSurvival', ite_eq_right hξ, max_eq_left hpos'.le]
        exact rpow_pos_of_pos hpos' _
      filter_upwards [ae_tendsto_avg_comp hX hind (measurable_one.indicator measurableSet_Ioi)
        hgi] with ω hω
      by_contra hno
      simp only [not_exists, not_lt] at hno
      have h0 : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          (Ioi (a k)).indicator (1 : ℝ → ℝ) (X i ω) = 0 := fun n => by
        rw [Finset.sum_eq_zero fun i _ => indicator_of_notMem (s := Ioi (a k)) (show X i ω ∉ Ioi (a k) from not_lt.2 (hno i)) _, mul_zero]
      simp only [h0] at hω
      exact hmean.ne' (tendsto_nhds_unique hω tendsto_const_nhds)
    filter_upwards [hsupp, hslln_u, hexists] with ω hω hωu hωe s hs
    refine tendsto_of_bounds (l := fun k => -ξ * a k) (u := u) ?_ hu (fun k => ?_) (fun k => ?_)
    · have := ha.const_mul (-ξ)
      have e : -ξ * xF = σ₀ := by simp only [xF]; field_simp
      rwa [e] at this
    · obtain ⟨i, hi⟩ := hωe k
      filter_upwards [hs, eventually_gt_atTop i] with n hn hin
      have h := hn.1.2 ⟨i, hin⟩
      simp only at h
      have : ξ * X i ω < ξ * a k := mul_lt_mul_of_neg_left hi hneg
      linarith
    · exact eventually_lt_of_avg hξ1 hσ₀ hω (hσu k) (hmu k) (hωu k) hs
  · -- `ξ > 0`: the lower bounds `l k = σ₀ / (1 + 1/(k+1))` work as the upper ones
    set l : ℕ → ℝ := fun k => σ₀ / (1 + 1 / ((k : ℝ) + 1))
    have hl : Tendsto l atTop (𝓝 σ₀) := by
      have := (tendsto_const_nhds (x := σ₀)).div
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1) (by norm_num)
      rw [add_zero, div_one] at this
      exact this
    have hl0 : ∀ k, 0 < l k := fun k => by simp only [l]; positivity
    have hlσ : ∀ k, l k < σ₀ := fun k => by
      simp only [l]
      rw [div_lt_iff₀ (by positivity)]
      have : (0 : ℝ) < 1 / (k + 1) := by positivity
      nlinarith
    have hil : ∀ k, Integrable (fun y => y / (l k + ξ * y)) (gpdMeasure ξ σ₀) := fun k =>
      integrable_div_gpdMeasure hσ₀ (Or.inl ⟨hpos, hl0 k⟩)
    have hml : ∀ k, 1 / (1 + ξ) < ∫ y, y / (l k + ξ * y) ∂gpdMeasure ξ σ₀ := fun k => by
      rw [← integral_div_gpdMeasure hξ1 hξ hσ₀]
      refine integral_div_gpdMeasure_lt (hlσ k) ?_ (hil k)
        (integrable_div_gpdMeasure hσ₀ (Or.inl ⟨hpos, hσ₀⟩))
      filter_upwards [ae_gpdMeasure hσ₀] with y hy
      exact ⟨hy.1, by have := hl0 k; nlinarith [hy.1]⟩
    have hslln_l : ∀ᵐ ω ∂P, ∀ k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, X i ω / (l k + ξ * X i ω)) atTop
        (𝓝 (∫ y, y / (l k + ξ * y) ∂gpdMeasure ξ σ₀)) := ae_all_iff.2 fun k =>
      ae_tendsto_avg_comp hX hind (by fun_prop) (hil k)
    filter_upwards [hsupp, hslln_u, hslln_l] with ω hω hωu hωl s hs
    exact tendsto_of_bounds hl hu
      (fun k => eventually_gt_of_avg hpos (fun i => (hω i).1) (hml k) (hωl k) hs)
      (fun k => eventually_lt_of_avg hξ1 hσ₀ hω (hσu k) (hmu k) (hωu k) hs)

end Consistency

end ExtremeValueTheory
