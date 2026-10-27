/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Breiman
import ExtremeValueTheory.HeavyTails.LinearProcessSeries
import ExtremeValueTheory.Minimality.ClassicalKaramata
import ExtremeValueTheory.CumulativeDistributionFunction
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Independence.Basic
import ExtremeValueTheory.CDFBridge

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

## A positive result

When the slowly varying factor converges, `x ^ α P(X > x) → c > 0`, the `ε` can be dropped:
`E[Y ^ α] < ∞` suffices (`tendsto_measure_mul_div_measure_of_tendsto_rpow_mul`). The domination
is then `F̄(x / y) / F̄(x) ≤ K y ^ α`, without Potter bounds.

## Summary

| hypothesis | status |
|---|---|
| `E[Y ^ (α + ε)] < ∞` for some `ε > 0` | cannot be weakened to `E[Y ^ α] < ∞` in general: `breiman_counterexample` |
| same, when `x ^ α P(X > x) → c > 0` | dropped to `E[Y ^ α] < ∞`: `tendsto_measure_mul_div_measure_of_tendsto_rpow_mul` |
| general Denisov–Zwart condition (`P(Y > x) = o(P(X > x))` plus `E Y^α < ∞`) | open (not formalized) |
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory.Minimality

variable {α : ℝ}

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
  rw [logLaw, CumulativeDistributionFunction.measure_Ioi]
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
  have h := (isRegularlyVarying_logTail 3).comp_rpow hα
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

/-! ### Dropping `ε` when the slowly varying factor converges -/

/-- Analytic core of Breiman's lemma **without the extra `ε`**, for tails `F x ∼ c x^{-α}`:
if `F` is antitone, `x ^ α * F x → c > 0`, and `μ` is a finite measure on `[0, ∞)` with
`∫ y ^ α dμ < ∞`, then `(∫ y, (if 0 < y then F (x / y) else 0) ∂μ) / F x → ∫ y, y ^ α ∂μ`. -/
theorem tendsto_integral_div_of_tendsto_rpow_mul {F : ℝ → ℝ} (hF : Antitone F) (hα : 0 < α)
    {c : ℝ} (hc : 0 < c) (hpar : Tendsto (fun x => x ^ α * F x) atTop (𝓝 c))
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : ∀ᵐ y ∂μ, 0 ≤ y)
    (hint : Integrable (fun y => y ^ α) μ) :
    Tendsto (fun x => (∫ y, (if 0 < y then F (x / y) else 0) ∂μ) / F x) atTop
      (𝓝 (∫ y, y ^ α ∂μ)) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    (hpar.eventually (Icc_mem_nhds (by linarith : c / 2 < c) (by linarith : c < 2 * c)))
  set x₁ := max x₀ 1 with hx₁
  have hx₁0 : 0 < x₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB : ∀ x ≥ x₁, c / 2 ≤ x ^ α * F x ∧ x ^ α * F x ≤ 2 * c := fun x hx =>
    hx₀ x ((le_max_left _ _).trans hx)
  have hFpos : ∀ t, 0 < F t := by
    intro t
    set s := max t x₁
    have hs0 : 0 < s := hx₁0.trans_le (le_max_right _ _)
    have h1 := (hB s (le_max_right _ _)).1
    have : 0 < F s := by
      by_contra h
      push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (rpow_pos_of_pos hs0 α).le h
      linarith
    exact this.trans_le (hF (le_max_left _ _))
  -- the key identity
  have hid : ∀ x > 0, ∀ y > 0, F (x / y) / F x =
      ((x / y) ^ α * F (x / y)) / (x ^ α * F x) * y ^ α := by
    intro x hx y hy
    have := hFpos x
    have := hFpos (x / y)
    rw [div_rpow hx.le hy.le]
    have : 0 < x ^ α := rpow_pos_of_pos hx α
    have : 0 < y ^ α := rpow_pos_of_pos hy α
    field_simp
  set K := max 4 (2 * F 0 * x₁ ^ α / c) with hK
  rw [show (fun x => (∫ y, (if 0 < y then F (x / y) else 0) ∂μ) / F x) =
      fun x => ∫ y, (if 0 < y then F (x / y) else 0) / F x ∂μ from
    funext fun x => (integral_div _ _).symm]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => K * y ^ α) ?_ ?_
    (hint.const_mul K) ?_
  · refine Eventually.of_forall fun x => ?_
    exact ((Measurable.ite measurableSet_Ioi (hF.measurable.comp
      (measurable_const.div measurable_id)) measurable_const).div_const _).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop x₁] with x hx
    filter_upwards [hμ] with y hy
    have hx0 : 0 < x := hx₁0.trans_le hx
    rcases hy.eq_or_lt with h0 | hy0
    · subst h0
      simp only [lt_irrefl, ↓reduceIte, zero_div, norm_zero]
      exact mul_nonneg ((le_max_left _ _).trans' (by norm_num)) (rpow_nonneg le_rfl _)
    simp only [hy0, ↓reduceIte]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (hFpos _) (hFpos _))]
    have hyα : 0 < y ^ α := rpow_pos_of_pos hy0 α
    have hBx := hB x hx
    rcases le_or_gt x₁ (x / y) with hxy | hxy
    · have hA := (hB (x / y) hxy).2
      rw [hid x hx0 y hy0]
      have : ((x / y) ^ α * F (x / y)) / (x ^ α * F x) ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      calc ((x / y) ^ α * F (x / y)) / (x ^ α * F x) * y ^ α ≤ 4 * y ^ α :=
            mul_le_mul_of_nonneg_right this hyα.le
        _ ≤ K * y ^ α := mul_le_mul_of_nonneg_right (le_max_left _ _) hyα.le
    · have hF0 : F (x / y) ≤ F 0 := hF (div_pos hx0 hy0).le
      have hxle : x ≤ x₁ * y := by rw [div_lt_iff₀ hy0] at hxy; linarith
      have hxα : x ^ α ≤ x₁ ^ α * y ^ α := by
        rw [← mul_rpow hx₁0.le hy0.le]; exact rpow_le_rpow hx0.le hxle hα.le
      have hFx : c / 2 ≤ x ^ α * F x := hBx.1
      have hxα0 : 0 < x ^ α := rpow_pos_of_pos hx0 α
      have h1 : F (x / y) / F x ≤ F 0 / F x := div_le_div_of_nonneg_right hF0 (hFpos x).le
      have h2 : F 0 / F x ≤ 2 * F 0 * x ^ α / c := by
        rw [div_le_div_iff₀ (hFpos x) hc]
        have := hFpos 0
        nlinarith
      have h3 : 2 * F 0 * x ^ α / c ≤ 2 * F 0 * x₁ ^ α / c * y ^ α := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc, mul_assoc (2 * F 0)]
        exact mul_le_mul_of_nonneg_left hxα (by have := hFpos 0; positivity)
      calc F (x / y) / F x ≤ 2 * F 0 * x₁ ^ α / c * y ^ α := h1.trans (h2.trans h3)
        _ ≤ K * y ^ α := mul_le_mul_of_nonneg_right (le_max_right _ _) hyα.le
  · filter_upwards [hμ] with y hy
    rcases hy.eq_or_lt with h0 | hy0
    · subst h0
      simp only [lt_irrefl, ↓reduceIte, zero_div, zero_rpow hα.ne']
      exact tendsto_const_nhds
    simp only [hy0, ↓reduceIte]
    have hlim : Tendsto (fun x => ((x / y) ^ α * F (x / y)) / (x ^ α * F x) * y ^ α) atTop
        (𝓝 (c / c * y ^ α)) :=
      ((hpar.comp (tendsto_id.atTop_div_const hy0)).div hpar hc.ne').mul_const _
    rw [div_self hc.ne', one_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (hid x hx y hy0).symm

/-- **Breiman's lemma with `E[Y ^ α] < ∞` only, for asymptotically Pareto tails.** If `X`, `Y`
are independent, `Y ≥ 0`, `x ^ α P(X > x) → c > 0` and `E[Y ^ α] < ∞`, then
`P(XY > x) / P(X > x) → E[Y ^ α]`. Together with `breiman_counterexample` (where
`x ^ α P(X > x) → 0`), this locates the role of the extra `ε` in
`tendsto_measure_mul_div_measure`: it compensates for a non-convergent slowly varying factor. -/
theorem tendsto_measure_mul_div_measure_of_tendsto_rpow_mul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y P) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) (hα : 0 < α) {c : ℝ}
    (hc : 0 < c) (hpar : Tendsto (fun x => x ^ α * (P {ω | x < X ω}).toReal) atTop (𝓝 c))
    (hmom : Integrable (fun ω => Y ω ^ α) P) :
    Tendsto (fun x => (P {ω | x < X ω * Y ω}).toReal / (P {ω | x < X ω}).toReal) atTop
      (𝓝 (∫ ω, Y ω ^ α ∂P)) := by
  set F : ℝ → ℝ := fun x => (P {ω | x < X ω}).toReal with hF_def
  have hFanti : Antitone F := by
    intro a b hab
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    exact lt_of_le_of_lt hab hω
  set μ := P.map Y with hμ_def
  have hμ : ∀ᵐ y ∂μ, 0 ≤ y := (ae_map_iff hY.aemeasurable measurableSet_Ici).2 hY0
  have hint : Integrable (fun y => y ^ α) μ :=
    (integrable_map_measure (continuous_id.rpow_const fun _ => Or.inr hα.le
      ).measurable.aestronglyMeasurable hY.aemeasurable).2 hmom
  have hcore := tendsto_integral_div_of_tendsto_rpow_mul hFanti hα hc hpar hμ hint
  have hlim : ∫ y, y ^ α ∂μ = ∫ ω, Y ω ^ α ∂P :=
    integral_map hY.aemeasurable (continuous_id.rpow_const fun _ => Or.inr hα.le
      ).measurable.aestronglyMeasurable
  rw [hlim] at hcore
  refine hcore.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  congr 1
  -- Conditioning on `Y` (as in `tendsto_measure_mul_div_measure`).
  set S : Set (ℝ × ℝ) := {p | x < p.1 * p.2} with hS_def
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_fst.mul measurable_snd)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have h1 : P {ω | x < X ω * Y ω} = ∫⁻ y, (P.map X) ((fun a => (a, y)) ⁻¹' S) ∂μ := by
    rw [← Measure.prod_apply_symm hS, ← hprod, Measure.map_apply (hX.prodMk hY) hS]
    rfl
  rw [h1, ← integral_toReal (measurable_measure_prodMk_right hS).aemeasurable
    (Eventually.of_forall fun _ => measure_lt_top _ _)]
  refine integral_congr_ae ?_
  filter_upwards [hμ] with y hy
  rcases hy.eq_or_lt with h0 | hy0
  · subst h0
    have : (fun a : ℝ => (a, (0 : ℝ))) ⁻¹' S = ∅ := by
      ext a; simp [hS_def, hx.not_gt]
    simp [this]
  · have : (fun a : ℝ => (a, y)) ⁻¹' S = Ioi (x / y) := by
      ext a; simp [hS_def, div_lt_iff₀ hy0]
    simp only [hy0, ↓reduceIte]
    rw [this, Measure.map_apply hX measurableSet_Ioi]
    rfl

end ExtremeValueTheory.Minimality
