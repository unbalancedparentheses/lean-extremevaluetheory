/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Breiman
import ExtremeValueTheory.Minimality.ClassicalKaramata
import ExtremeValueTheory.CumulativeDistributionFunction
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Independence.Basic

/-!
# Minimality: the moment condition in Breiman's lemma

`ExtremeValueTheory.tendsto_measure_mul_div_measure` (Breiman's lemma) assumes
`E[Y ^ (α + ε)] < ∞` for some `ε > 0`, and concludes `P(XY > x) / P(X > x) → E[Y ^ α]`. The
natural minimal condition would be `E[Y ^ α] < ∞` (needed for the limit to be finite). We show
that `E[Y ^ α] < ∞` alone is **not** sufficient (cf. Denisov and Zwart, *On a theorem of
Breiman and a class of random difference equations*, J. Appl. Probab. 44 (2007), and Jessen and
Mikosch 2006, who give the same kind of example).

## The counterexample

Let `ν₃`, `ν₂` be the laws with survival functions `logTail 3`, `logTail 2`
(`P(V > v) = 1 / (v (log v)^a)` for `v ≥ e`, `ExtremeValueTheory.Minimality.logTail`). On
`ν₃ ⊗ ν₂` put `X = max V₁ e ^ (1/α)` and `Y = max V₂ 0 ^ (1/α)`. Then

* `X`, `Y` are independent, `Y ≥ 0`;
* `P(X > x) = 1 / (x^α (α log x)³)` for large `x`, regularly varying with index `-α`;
* `E[Y ^ α] = E[max V₂ 0] < ∞` (by the layer-cake formula, since `∫_e^∞ dt / (t (log t)²) < ∞`);
* but `X ≥ 1`, so `P(XY > x) ≥ P(Y > x) = 1 / (x^α (α log x)²)` and
  `P(XY > x) / P(X > x) ≥ α log x → ∞`.

So the conclusion of Breiman's lemma fails although every hypothesis but the `α + ε` moment
holds, with `E[Y^α] < ∞` (`breiman_counterexample`). By Breiman's lemma itself,
`E[Y ^ (α + ε)] = ∞` for every `ε > 0` (`not_integrable_breimanY_rpow`).

## Summary

| hypothesis | status |
|---|---|
| `E[Y ^ (α + ε)] < ∞` for some `ε > 0` | cannot be weakened to `E[Y ^ α] < ∞`: `breiman_counterexample` |
| sharp condition (Denisov–Zwart: `P(Y > x) = o(P(X > x))` plus `E Y^α < ∞`) | open (not formalized) |
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory.Minimality

variable {α : ℝ}

/-- Composition with a power: if `f` is regularly varying with index `ρ` and `α > 0`, then
`x ↦ f (x ^ α)` is regularly varying with index `ρ * α`. -/
theorem isRegularlyVarying_comp_rpow {f : ℝ → ℝ} {ρ : ℝ} (hf : IsRegularlyVarying f ρ)
    (hα : 0 < α) : IsRegularlyVarying (fun x => f (x ^ α)) (ρ * α) := by
  have ht : Tendsto (fun x : ℝ => x ^ α) atTop atTop := tendsto_rpow_atTop hα
  refine ⟨ht.eventually hf.1, fun c hc => ?_⟩
  have h := (hf.2 (c ^ α) (rpow_pos_of_pos hc α)).comp ht
  rw [← rpow_mul hc.le, mul_comm α ρ] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  simp only [Function.comp_apply, mul_rpow hc.le hx]

/-! ### The laws with survival function `logTail a` -/

theorem rightContinuous_logTail (a : ℕ) (x : ℝ) :
    ContinuousWithinAt (logTail a) (Ici x) x := by
  by_cases hx : x < exp 1
  · refine (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq ?_ (logTail_of_lt hx)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with t ht
    exact logTail_of_lt ht
  · push Not at hx
    refine ((continuousOn_logTail a x hx).mono (Ici_subset_Ici.2 hx)).congr
      (fun t ht => logTail_of_ge (hx.trans ht)) (logTail_of_ge hx)

/-- The c.d.f. `1 - logTail a`. -/
noncomputable def logCDF (a : ℕ) : CumulativeDistributionFunction where
  toFun t := 1 - logTail a t
  mono' := fun _ _ h => sub_le_sub_left (antitone_logTail a h) 1
  right_continuous' := fun x => continuousWithinAt_const.sub (rightContinuous_logTail a x)
  tendsto_atTop := by simpa using (tendsto_logTail_atTop a).const_sub (1 : ℝ)
  tendsto_atBot := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot (exp 1)] with t ht
    rw [logTail_of_lt ht, sub_self]

/-- The law with survival function `logTail a`. -/
noncomputable def logLaw (a : ℕ) : Measure ℝ := (logCDF a).measure

instance (a : ℕ) : IsProbabilityMeasure (logLaw a) :=
  CumulativeDistributionFunction.isProbabilityMeasure_measure_coe (logCDF a)

theorem logLaw_Ioi (a : ℕ) (x : ℝ) : logLaw a (Ioi x) = ENNReal.ofReal (logTail a x) := by
  rw [logLaw, StieltjesFunction.measure_Ioi _ (logCDF a).tendsto_atTop x]
  congr 1
  change 1 - (1 - logTail a x) = _
  ring

/-! ### The counterexample -/

/-- The probability measure `ν₃ ⊗ ν₂` on `ℝ × ℝ`. -/
noncomputable def breimanP : Measure (ℝ × ℝ) := (logLaw 3).prod (logLaw 2)

instance : IsProbabilityMeasure breimanP := by unfold breimanP; infer_instance

/-- `X = max V₁ e ^ (1/α)`. -/
noncomputable def breimanX (α : ℝ) (ω : ℝ × ℝ) : ℝ := max ω.1 (exp 1) ^ α⁻¹

/-- `Y = max V₂ 0 ^ (1/α)`. -/
noncomputable def breimanY (α : ℝ) (ω : ℝ × ℝ) : ℝ := max ω.2 0 ^ α⁻¹

theorem measurable_breimanX (α : ℝ) : Measurable (breimanX α) := by
  unfold breimanX; fun_prop

theorem measurable_breimanY (α : ℝ) : Measurable (breimanY α) := by
  unfold breimanY; fun_prop

theorem one_le_breimanX (hα : 0 < α) (ω : ℝ × ℝ) : 1 ≤ breimanX α ω :=
  one_le_rpow ((one_le_exp zero_le_one).trans (le_max_right _ _)) (inv_nonneg.2 hα.le)

theorem breimanY_nonneg (ω : ℝ × ℝ) : 0 ≤ breimanY α ω :=
  rpow_nonneg (le_max_right _ _) _

theorem indepFun_breimanX_breimanY : IndepFun (breimanX α) (breimanY α) breimanP :=
  indepFun_prod (X := fun v : ℝ => max v (exp 1) ^ α⁻¹) (Y := fun v : ℝ => max v 0 ^ α⁻¹)
    (by fun_prop) (by fun_prop)

theorem breimanX_tail (hα : 0 < α) {x : ℝ} (hx : 0 < x) (hxe : exp 1 ≤ x ^ α) :
    breimanP {ω | x < breimanX α ω} = ENNReal.ofReal (logTail 3 (x ^ α)) := by
  have hset : {ω : ℝ × ℝ | x < breimanX α ω} = Ioi (x ^ α) ×ˢ univ := by
    ext ω
    simp only [breimanX, mem_ofPred_eq, mem_prod, mem_Ioi, mem_univ, and_true]
    rw [lt_rpow_inv_iff_of_pos hx.le ((exp_pos 1).le.trans (le_max_right _ _)) hα,
      lt_max_iff]
    exact ⟨fun h => h.resolve_right (not_lt.2 hxe), Or.inl⟩
  rw [hset, breimanP, Measure.prod_prod, measure_univ, mul_one, logLaw_Ioi]

theorem breimanY_tail (hα : 0 < α) {x : ℝ} (hx : 0 < x) :
    breimanP {ω | x < breimanY α ω} = ENNReal.ofReal (logTail 2 (x ^ α)) := by
  have hset : {ω : ℝ × ℝ | x < breimanY α ω} = univ ×ˢ Ioi (x ^ α) := by
    ext ω
    simp only [breimanY, mem_ofPred_eq, mem_prod, mem_Ioi, mem_univ, true_and]
    rw [lt_rpow_inv_iff_of_pos hx.le (le_max_right _ _) hα, lt_max_iff]
    exact ⟨fun h => h.resolve_right (not_lt.2 (rpow_pos_of_pos hx α).le), Or.inl⟩
  rw [hset, breimanP, Measure.prod_prod, measure_univ, one_mul, logLaw_Ioi]

/-- The tail of `X` is regularly varying with index `-α`. -/
theorem isRegularlyVarying_breimanX (hα : 0 < α) :
    IsRegularlyVarying (fun x => (breimanP {ω | x < breimanX α ω}).toReal) (-α) := by
  have h := isRegularlyVarying_comp_rpow (isRegularlyVarying_logTail 3) hα
  rw [neg_one_mul] at h
  refine h.congr ?_
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_rpow_atTop hα).eventually (eventually_ge_atTop (exp 1))] with x hx hxe
  rw [breimanX_tail hα hx hxe, ENNReal.toReal_ofReal (logTail_pos 3 _).le]

/-- `E[Y ^ α] < ∞`. -/
theorem integrable_breimanY_rpow (hα : 0 < α) :
    Integrable (fun ω => breimanY α ω ^ α) breimanP := by
  have heq : (fun ω => breimanY α ω ^ α) = fun ω : ℝ × ℝ => max ω.2 0 := by
    funext ω
    exact rpow_inv_rpow (le_max_right _ _) hα.ne'
  rw [heq]
  refine Integrable.comp_snd (f := fun v : ℝ => max v 0) ?_ (logLaw 3)
  refine ⟨(measurable_id.max measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun v => le_max_right v 0),
    lintegral_eq_lintegral_meas_lt _ (ae_of_all _ fun v => le_max_right v 0)
      (measurable_id.max measurable_const).aemeasurable]
  have : ∀ t ∈ Ioi (0 : ℝ), logLaw 2 {v | t < max v 0} = ENNReal.ofReal (logTail 2 t) := by
    intro t ht
    have : {v : ℝ | t < max v 0} = Ioi t := by
      ext v
      simp only [mem_ofPred_eq, mem_Ioi, lt_max_iff]
      exact ⟨fun h => h.resolve_right (not_lt.2 (le_of_lt ht)), Or.inl⟩
    rw [this, logLaw_Ioi]
  rw [setLIntegral_congr_fun measurableSet_Ioi this]
  exact (integrableOn_Ioi_logTail_two 0).lintegral_lt_top

/-- `P(XY > x) / P(X > x) → ∞`. -/
theorem tendsto_breiman_ratio_atTop (hα : 0 < α) :
    Tendsto (fun x => (breimanP {ω | x < breimanX α ω * breimanY α ω}).toReal /
      (breimanP {ω | x < breimanX α ω}).toReal) atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log (x ^ α)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_rpow_atTop hα)
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_rpow_atTop hα).eventually (eventually_ge_atTop (exp 1))] with x hx hxe
  have hsub : {ω | x < breimanY α ω} ⊆ {ω | x < breimanX α ω * breimanY α ω} := by
    intro ω (h : x < breimanY α ω)
    exact h.trans_le (le_mul_of_one_le_left (breimanY_nonneg ω) (one_le_breimanX hα ω))
  have h1 : logTail 2 (x ^ α) ≤ (breimanP {ω | x < breimanX α ω * breimanY α ω}).toReal := by
    have := measure_mono (μ := breimanP) hsub
    rw [breimanY_tail hα hx] at this
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 this
  rw [breimanX_tail hα hx hxe, ENNReal.toReal_ofReal (logTail_pos 3 _).le,
    le_div_iff₀ (logTail_pos 3 _)]
  refine le_trans ?_ h1
  have hl : 0 < Real.log (x ^ α) := one_pos.trans_le (one_le_log_of_ge hxe)
  have hc : 0 < x ^ α := rpow_pos_of_pos hx α
  rw [logTail_of_ge hxe, logTail_of_ge hxe]
  field_simp
  rfl

/-- **`E[Y ^ α] < ∞` is not enough in Breiman's lemma.** On `breimanP`, `X = breimanX α` and
`Y = breimanY α` are independent, `Y ≥ 0`, `P(X > x)` is regularly varying with index `-α` and
`E[Y ^ α] < ∞`, yet `P(XY > x) / P(X > x) → ∞`: it converges to no real number, in particular
not to `E[Y ^ α]`. -/
theorem breiman_counterexample (hα : 0 < α) :
    Measurable (breimanX α) ∧ Measurable (breimanY α) ∧
      IndepFun (breimanX α) (breimanY α) breimanP ∧ (∀ᵐ ω ∂breimanP, 0 ≤ breimanY α ω) ∧
      IsRegularlyVarying (fun x => (breimanP {ω | x < breimanX α ω}).toReal) (-α) ∧
      Integrable (fun ω => breimanY α ω ^ α) breimanP ∧
      Tendsto (fun x => (breimanP {ω | x < breimanX α ω * breimanY α ω}).toReal /
        (breimanP {ω | x < breimanX α ω}).toReal) atTop atTop ∧
      ∀ L, ¬ Tendsto (fun x => (breimanP {ω | x < breimanX α ω * breimanY α ω}).toReal /
        (breimanP {ω | x < breimanX α ω}).toReal) atTop (𝓝 L) :=
  ⟨measurable_breimanX α, measurable_breimanY α, indepFun_breimanX_breimanY,
    ae_of_all _ breimanY_nonneg, isRegularlyVarying_breimanX hα, integrable_breimanY_rpow hα,
    tendsto_breiman_ratio_atTop hα,
    fun L => not_tendsto_nhds_of_tendsto_atTop (tendsto_breiman_ratio_atTop hα) L⟩

/-- In the counterexample, `E[Y ^ (α + ε)] = ∞` for every `ε > 0` (otherwise Breiman's lemma
would apply). -/
theorem not_integrable_breimanY_rpow (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ¬ Integrable (fun ω => breimanY α ω ^ (α + ε)) breimanP := fun hmom =>
  (breiman_counterexample hα).2.2.2.2.2.2.2 _
    (tendsto_measure_mul_div_measure (measurable_breimanX α) (measurable_breimanY α)
      indepFun_breimanX_breimanY (ae_of_all _ breimanY_nonneg) hα hε
      (isRegularlyVarying_breimanX hα) hmom)

end ExtremeValueTheory.Minimality
