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

/-! ### The log-likelihood -/

section LogLik

variable {ξ σ x : ℝ} {n : ℕ}

/-- The **GPD log-likelihood** `ℓ(ξ, σ; x) = ∑ᵢ log g_{ξ,σ}(xᵢ)` of a sample `x`. (Lean's
convention `log 0 = 0` only matters outside the support, where the likelihood vanishes.) -/
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

end ExtremeValueTheory
