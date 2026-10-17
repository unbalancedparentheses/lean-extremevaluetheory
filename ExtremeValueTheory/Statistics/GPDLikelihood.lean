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

TODO docstring
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

end ExtremeValueTheory
