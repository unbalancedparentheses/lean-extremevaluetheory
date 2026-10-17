/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Density
import ExtremeValueTheory.GEV.Moments

/-!
# The density and log-likelihood of the GEV law

The standard **generalized extreme value law** `H_ξ` (`ExtremeValueTheory.gevCDF`) has density

  `h_ξ(x) = (1 + ξ x) ^ (-1/ξ - 1) exp(-(1 + ξ x) ^ (-1/ξ))` on `{1 + ξ x > 0}`,
  `h_0(x) = e^{-x} exp(-e^{-x})`,

and the location-scale law `H_ξ((x - μ)/σ)` has density `σ⁻¹ h_ξ((x - μ)/σ)`. The GEV
log-likelihood of block maxima `x₁, …, xₙ` is `∑ᵢ log(σ⁻¹ h_ξ((xᵢ - μ)/σ))` ([Coles, §3.3.2]).

## Main results

* `ExtremeValueTheory.continuous_gevFun`: `H_ξ` is continuous (its law has no atoms).
* `ExtremeValueTheory.hasDerivAt_gevFun`: `H_ξ' = h_ξ` at every point other than the endpoint
  `-1/ξ` of the support.
* `ExtremeValueTheory.measure_gevCDF_eq_withDensity`: `H_ξ(dx) = h_ξ(x) dx`.
* `ExtremeValueTheory.integral_gevDensity`: `∫ h_ξ = 1`.
* `ExtremeValueTheory.gevLogLik`, `ExtremeValueTheory.log_gevLocScaleDensity`: the
  log-likelihood and the closed form
  `log(σ⁻¹ h_ξ(z)) = -log σ - (1/ξ + 1) log(1 + ξ z) - (1 + ξ z) ^ (-1/ξ)` on the support.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §3.3.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

variable {ξ x : ℝ}

/-- The **density of the standard GEV law** `H_ξ`. -/
noncomputable def gevDensity (ξ x : ℝ) : ℝ :=
  if ξ = 0 then exp (-x) * exp (-exp (-x))
  else if 0 < 1 + ξ * x then (1 + ξ * x) ^ (-1 / ξ - 1) * exp (-(1 + ξ * x) ^ (-1 / ξ))
  else 0

lemma gevDensity_nonneg (ξ x : ℝ) : 0 ≤ gevDensity ξ x := by
  unfold gevDensity
  split_ifs with h1 h2
  · positivity
  · exact mul_nonneg (rpow_nonneg h2.le _) (exp_pos _).le
  · exact le_rfl

lemma measurable_gevDensity (ξ : ℝ) : Measurable (gevDensity ξ) := by
  unfold gevDensity
  by_cases h : ξ = 0
  · simp only [h, ↓reduceIte]; fun_prop
  · simp only [h, ↓reduceIte]
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    exact measurableSet_lt measurable_const (show Measurable fun x : ℝ => 1 + ξ * x by fun_prop)

private lemma injOn_gevTransform (ξ : ℝ) : InjOn (gevTransform ξ) (Ioi 0) := by
  intro s hs t ht hst
  by_cases h : ξ = 0
  · simp only [gevTransform, h, ↓reduceIte, neg_inj] at hst
    exact log_injOn_pos hs ht hst
  · simp only [gevTransform, h, ↓reduceIte] at hst
    have : s ^ (-ξ) = t ^ (-ξ) := by
      have := (div_left_inj' h).1 hst
      linarith
    exact rpow_left_injOn (neg_ne_zero.2 h) (show (0 : ℝ) ≤ s from le_of_lt hs)
      (show (0 : ℝ) ≤ t from le_of_lt ht) this

/-- The GEV law has no atoms. -/
lemma measure_gevCDF_singleton (ξ x : ℝ) : (gevCDF ξ).measure {x} = 0 := by
  have hm := measurable_gevTransform ξ
  rw [measure_gevCDF_eq_map, Measure.map_apply hm (measurableSet_singleton x), stdExpMeasure]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply (hm (measurableSet_singleton x))]
  refine Set.Countable.measure_zero (Set.Subsingleton.countable ?_) _
  intro s hs t ht
  exact injOn_gevTransform ξ hs.2 ht.2 (hs.1.trans ht.1.symm)

/-- **The GEV distribution function is continuous.** -/
theorem continuous_gevFun (ξ : ℝ) : Continuous (gevFun ξ) := by
  rw [← coe_gevCDF]
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmono := (gevCDF ξ).mono
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h := measure_gevCDF_singleton ξ x
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at h
  exact le_antisymm (hmono.leftLim_le le_rfl) (by linarith)

/-- **The GEV density is the derivative of the distribution function** outside the endpoint
`-1/ξ` of the support. -/
theorem hasDerivAt_gevFun (hx : 1 + ξ * x ≠ 0 ∨ ξ = 0) :
    HasDerivAt (gevFun ξ) (gevDensity ξ x) x := by
  by_cases hξ : ξ = 0
  · subst hξ
    have heq : gevFun 0 = fun y => exp (-exp (-y)) := funext fun y => by simp [gevFun]
    rw [heq]
    have := ((hasDerivAt_neg x).exp.neg).exp
    convert this using 1
    simp [gevDensity, mul_comm]
  have hx' : 1 + ξ * x ≠ 0 := hx.resolve_right hξ
  have hcont : Continuous fun y : ℝ => 1 + ξ * y := by fun_prop
  rcases lt_or_gt_of_ne hx' with hneg | hpos
  · -- outside the support `gevFun` is locally constant
    have heq : gevFun ξ =ᶠ[𝓝 x] fun _ => if 0 < ξ then 0 else 1 := by
      filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hneg)] with y hy
      simp [gevFun, hξ, not_lt.2 hy.le]
    have : gevDensity ξ x = 0 := by simp [gevDensity, hξ, not_lt.2 hneg.le]
    rw [this]
    exact (hasDerivAt_const x _).congr_of_eventuallyEq heq
  · have heq : gevFun ξ =ᶠ[𝓝 x] fun y => exp (-(1 + ξ * y) ^ (-1 / ξ)) := by
      filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hpos)] with y hy
      simp [gevFun, hξ, hy]
    have hd0 : HasDerivAt (fun y => 1 + ξ * y) ξ x := by
      simpa using ((hasDerivAt_id x).const_mul ξ).const_add 1
    have hd := ((hd0.rpow_const (p := -1 / ξ) (Or.inl hpos.ne')).neg).exp
    have : gevDensity ξ x = exp (-(1 + ξ * x) ^ (-1 / ξ)) *
        -(ξ * (-1 / ξ) * (1 + ξ * x) ^ (-1 / ξ - 1)) := by
      simp only [gevDensity, hξ, hpos, ↓reduceIte]
      field_simp
    rw [this]
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    convert hd using 1

/-- **The GEV law has density `gevDensity`**: `H_ξ(dx) = h_ξ(x) dx`. -/
theorem measure_gevCDF_eq_withDensity (ξ : ℝ) :
    (gevCDF ξ).measure = volume.withDensity (fun x => ENNReal.ofReal (gevDensity ξ x)) := by
  refine eq_withDensity_of_hasDerivAt_off (F := gevFun ξ) (c₁ := -1 / ξ) (c₂ := -1 / ξ)
    (continuous_gevFun ξ) ?_ (fun x => ?_) (fun x h _ => hasDerivAt_gevFun ?_)
    (gevDensity_nonneg ξ)
  · rw [← coe_gevCDF]; exact (gevCDF ξ).tendsto_atBot
  · rw [StieltjesFunction.measure_Iic _ (gevCDF ξ).tendsto_atBot, sub_zero]
    rw [gevCDF_apply]
  · by_cases hξ : ξ = 0
    · exact Or.inr hξ
    · refine Or.inl fun h0 => h ?_
      field_simp
      linarith

/-- **The GEV density integrates to one.** -/
theorem integral_gevDensity (ξ : ℝ) : ∫ x, gevDensity ξ x = 1 :=
  (integral_eq_one_of_eq_withDensity (measure_gevCDF_eq_withDensity ξ) (gevDensity_nonneg ξ)
    (measurable_gevDensity ξ).aestronglyMeasurable).2

/-- The density of the location-scale GEV law `H_ξ((x - μ)/σ)`: `σ⁻¹ h_ξ((x - μ)/σ)`. -/
noncomputable def gevLocScaleDensity (ξ μ σ x : ℝ) : ℝ := σ⁻¹ * gevDensity ξ ((x - μ) / σ)

/-- The **GEV log-likelihood** `ℓ(ξ, μ, σ; x) = ∑ᵢ log(σ⁻¹ h_ξ((xᵢ - μ)/σ))` of block maxima
`x₁, …, xₙ` ([Coles, §3.3.2]).

This is the log-likelihood only for *admissible* parameters, i.e. `σ > 0` and every
`1 + ξ (xᵢ - μ)/σ > 0` (all data in the support). Off the support Lean's convention `log 0 = 0`
turns each offending term into the junk value `0` rather than `-∞`, and this junk can exceed the
log-likelihood at admissible parameters, so `gevLogLik` must not be maximized over all
parameters; maximum-likelihood statements must restrict to the admissible domain. -/
noncomputable def gevLogLik {n : ℕ} (ξ μ σ : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, log (gevLocScaleDensity ξ μ σ (x i))

/-- The GEV log-density on the support, `ξ ≠ 0`:
`log(σ⁻¹ h_ξ(z)) = -log σ - (1/ξ + 1) log(1 + ξ z) - (1 + ξ z) ^ (-1/ξ)`, `z = (x - μ)/σ`. -/
theorem log_gevLocScaleDensity {μ σ : ℝ} (hσ : 0 < σ) (hξ : ξ ≠ 0)
    (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    log (gevLocScaleDensity ξ μ σ x) = -log σ - (1 / ξ + 1) * log (1 + ξ * ((x - μ) / σ)) -
      (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) := by
  simp only [gevLocScaleDensity, gevDensity, hξ, hu, ↓reduceIte]
  rw [log_mul (inv_ne_zero hσ.ne') (mul_pos (rpow_pos_of_pos hu _) (exp_pos _)).ne',
    log_mul (rpow_pos_of_pos hu _).ne' (exp_pos _).ne', log_inv, log_exp, log_rpow hu]
  ring

/-- The Gumbel log-density: `log(σ⁻¹ h_0(z)) = -log σ - z - e^{-z}`, `z = (x - μ)/σ`. -/
theorem log_gevLocScaleDensity_zero {μ σ : ℝ} (hσ : 0 < σ) :
    log (gevLocScaleDensity 0 μ σ x) = -log σ - (x - μ) / σ - exp (-((x - μ) / σ)) := by
  simp only [gevLocScaleDensity, gevDensity, ↓reduceIte]
  rw [log_mul (inv_ne_zero hσ.ne') (mul_pos (exp_pos _) (exp_pos _)).ne',
    log_mul (exp_pos _).ne' (exp_pos _).ne', log_inv, log_exp, log_exp]
  ring

end ExtremeValueTheory
