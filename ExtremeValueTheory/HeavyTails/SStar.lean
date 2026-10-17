/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.Ruin
import ExtremeValueTheory.HeavyTails.Examples
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The class `𝒮*` of Klüppelberg

A probability measure `μ` on `[0, ∞)` with positive tail `F̄` and finite mean
`m = ∫₀^∞ F̄(y) dy` belongs to **`𝒮*`** ([Klüppelberg 1988]; [FKZ, Ch. 3]) if

  `∫₀ˣ F̄(x - y) F̄(y) dy / F̄(x) → 2 m`  as `x → ∞`.

Equivalently, the density `F̄ / m` of the integrated tail law `F_I` is "subexponential as a
density". We prove Klüppelberg's theorem: **`𝒮*` laws are subexponential and so are their
integrated tails**, which feeds the Embrechts–Veraverbeke theorem (`Ruin.lean`). Regularly
varying tails with index `-α`, `α > 1`, are in `𝒮*`.

## Main definitions

* `ExtremeValueTheory.tailConvInt μ x = ∫₀ˣ F̄(x - y) F̄(y) dy`.
* `ExtremeValueTheory.IsSStar μ`: the class `𝒮*`.

## Main results

* `IsSStar.tendsto_tail_sub_div`: `𝒮*` laws are long-tailed.
* `IsSStar.isSubexponential`: `𝒮* ⊆ 𝒮` ([Klüppelberg 1988, Theorem 3.2]; [FKZ, Ch. 3]).
* `IsSStar.isSubexponential_integratedTail`: `F ∈ 𝒮* ⇒ F_I ∈ 𝒮` ([Klüppelberg 1988,
  Theorem 3.2]; [FKZ, Ch. 3]).
* `IsSStar.tendsto_pkRuin_div`: Embrechts–Veraverbeke for `𝒮*` claims.
* `IsSStar.of_isRegularlyVarying`: `F̄ ∈ RV_{-α}`, `α > 1` ⇒ `F ∈ 𝒮*`.
* `isSStar_paretoMeasure`: Pareto laws with index `r > 1` are in `𝒮*`.

## References

* [EKM] Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events for Insurance and
  Finance* (Springer, 1997).
* [FKZ] Foss, Korshunov and Zachary, *An Introduction to Heavy-Tailed and Subexponential
  Distributions* (2nd ed., Springer, 2013).
* [Klüppelberg 1988] C. Klüppelberg, *Subexponential distributions and integrated tails*,
  J. Appl. Probab. 25 (1988), 132–141.

## Proof outline

Write `K(x, y) = F̄(x - y) F̄(y)` and `I(x) = ∫₀ˣ K(x, ·)`. By the symmetry `y ↦ x - y`,
`I(x) = 2 ∫₀^{x/2} K(x, ·)`.

* *Long tail.* For `t ≤ x / 2`, `I(x) ≥ 2 F̄(x) ∫₀ᵗ F̄ + 2 F̄(x - t) ∫ₜ^{x/2} F̄`, which forces
  `limsup F̄(x - t) / F̄(x) ≤ (m - ∫₀ᵗ F̄) / ∫ₜ^∞ F̄ = 1`.
* *`𝒮* ⊆ 𝒮`.* Split `F̄^{*2}(x) = ∫_{y ≤ v} + ∫_{v < y ≤ x - v} + ∫_{x - v < y ≤ x} F̄(x - y) dF(y)
  + F̄(x)`. The outer pieces are `≤ 2 F̄(x - v) ~ 2 F̄(x)`; the middle piece is compared to the
  Lebesgue integral `∫_{v-2}^{x-v-1} K(x, ·)` by smearing each atom `y` over `(y - 2, y - 1]`
  (Tonelli + long tail), and `∫_w^{x-w} K(x, ·) ≤ I(x) - 2 F̄(x) ∫₀ʷ F̄ = o(1) F̄(x) + 2 F̄(x) ∫_w^∞ F̄`.
* *`F_I ∈ 𝒮`.* `F_I ∗ F_I` has density `f_I ⋆ f_I = m⁻² I` (Mathlib's
  `conv_withDensity_eq_lconvolution`), and `f_I ⋆ f_I / f_I → 2` integrates to
  `F̄_I^{*2} / F̄_I → 2`.
-/

open Filter Topology Set Real MeasureTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

open Subexp

/-- `I(x) = ∫₀ˣ F̄(x - y) F̄(y) dy`, the tail-convolution integral defining `𝒮*`. -/
noncomputable def tailConvInt (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, tail μ (x - y) * tail μ y

/-- **The class `𝒮*`** ([Klüppelberg 1988]; [FKZ, Ch. 3]): `μ` is concentrated on `[0, ∞)`, has
positive tail `F̄` and finite mean `m = ∫₀^∞ F̄`, and `∫₀ˣ F̄(x - y) F̄(y) dy / F̄(x) → 2 m`. -/
structure IsSStar (μ : Measure ℝ) : Prop where
  nonneg : μ (Iio 0) = 0
  tail_pos : ∀ x, 0 < tail μ x
  integrableOn_tail : IntegrableOn (tail μ) (Ioi 0)
  tendsto_tailConvInt_div :
    Tendsto (fun x => tailConvInt μ x / tail μ x) atTop (𝓝 (2 * ∫ t in Ioi 0, tail μ t))

section Basic

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

private theorem intervalIntegrable_tail (a b : ℝ) : IntervalIntegrable (tail μ) volume a b :=
  tail_antitone.intervalIntegrable

private theorem measurable_K (x : ℝ) : Measurable fun y => tail μ (x - y) * tail μ y :=
  (tail_measurable.comp (measurable_const.sub measurable_id)).mul tail_measurable

omit [IsProbabilityMeasure μ] in
private theorem K_nonneg (x y : ℝ) : 0 ≤ tail μ (x - y) * tail μ y :=
  mul_nonneg (tail_nonneg _) (tail_nonneg _)

private theorem K_le_one (x y : ℝ) : tail μ (x - y) * tail μ y ≤ 1 :=
  by nlinarith [tail_le_one (μ := μ) (x - y), tail_le_one (μ := μ) y, tail_nonneg (μ := μ) (x - y),
    tail_nonneg (μ := μ) y]

private theorem intervalIntegrable_K (x a b : ℝ) :
    IntervalIntegrable (fun y => tail μ (x - y) * tail μ y) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    (measurable_K x).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  show ‖tail μ (x - y) * tail μ y‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (K_nonneg x y)]
  exact K_le_one x y

/-- Symmetry: `I(x) = 2 ∫₀^{x/2} F̄(x - y) F̄(y) dy`. -/
theorem tailConvInt_eq_two_mul (x : ℝ) :
    tailConvInt μ x = 2 * ∫ y in (0 : ℝ)..x / 2, tail μ (x - y) * tail μ y := by
  rw [tailConvInt, ← intervalIntegral.integral_add_adjacent_intervals (b := x / 2)
    (intervalIntegrable_K x _ _) (intervalIntegrable_K x _ _)]
  have h := intervalIntegral.integral_comp_sub_left (a := x / 2) (b := x)
    (fun z => tail μ z * tail μ (x - z)) x
  simp only [sub_sub_cancel, sub_self, show x - x / 2 = x / 2 by ring] at h
  rw [h]
  have : (∫ y in (0 : ℝ)..x / 2, tail μ y * tail μ (x - y)) =
      ∫ y in (0 : ℝ)..x / 2, tail μ (x - y) * tail μ y :=
    intervalIntegral.integral_congr fun y _ => mul_comm _ _
  rw [this]; ring

/-- Lower bound on a piece of `I(x)`: if `F̄(x - y) ≥ c ≥ 0` on `[a, b]`, then
`∫_a^b F̄(x - y) F̄(y) dy ≥ c ∫_a^b F̄`. -/
private theorem integral_K_ge {x a b c : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Icc a b, c ≤ tail μ (x - y)) :
    c * ∫ y in a..b, tail μ y ≤ ∫ y in a..b, tail μ (x - y) * tail μ y := by
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hab ((intervalIntegrable_tail a b).const_mul c)
    (intervalIntegrable_K x a b) fun y hy =>
      mul_le_mul_of_nonneg_right (h y hy) (tail_nonneg _)

omit [IsProbabilityMeasure μ] in
/-- Reflection `y ↦ x - y`: `∫_a^b F̄(x - y) F̄(y) dy = ∫_{x-b}^{x-a} F̄(x - y) F̄(y) dy`. -/
private theorem integral_K_reflect (x a b : ℝ) :
    ∫ y in a..b, tail μ (x - y) * tail μ y = ∫ y in x - b..x - a, tail μ (x - y) * tail μ y := by
  have h := intervalIntegral.integral_comp_sub_left (a := a) (b := b)
    (fun z => tail μ z * tail μ (x - z)) x
  simp only [sub_sub_cancel] at h
  rw [h]
  exact intervalIntegral.integral_congr fun y _ => mul_comm _ _

omit [IsProbabilityMeasure μ] in
/-- **Smearing atoms over unit intervals** (Tonelli):
`∫_{(a, b]} ∫_{(y-2, y-1]} g(s) ds dμ(y) ≤ ∫_{(a-2, b-1]} g(s) μ(s, ∞) ds`. -/
private theorem lintegral_smear_le [SFinite μ] {g : ℝ → ℝ≥0∞} (hg : Measurable g) (a b : ℝ) :
    ∫⁻ y in Ioc a b, (∫⁻ s in Ioc (y - 2) (y - 1), g s) ∂μ ≤
      ∫⁻ s in Ioc (a - 2) (b - 1), g s * μ (Ioi s) := by
  set S : Set (ℝ × ℝ) := {p | a < p.1} ∩ ({p | p.1 ≤ b} ∩ ({p | p.1 - 2 < p.2} ∩
    {p | p.2 ≤ p.1 - 1})) with hS_def
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_lt (measurable_fst.sub_const _) measurable_snd).inter
          (measurableSet_le measurable_snd (measurable_fst.sub_const _))))
  have hmem : ∀ y s, (y, s) ∈ S ↔ y ∈ Ioc a b ∧ s ∈ Ioc (y - 2) (y - 1) := by
    intro y s; simp only [hS_def, mem_inter_iff, mem_ofPred_eq, mem_Ioc]; tauto
  have hL : ∫⁻ y in Ioc a b, (∫⁻ s in Ioc (y - 2) (y - 1), g s) ∂μ =
      ∫⁻ y, (∫⁻ s, S.indicator (fun p => g p.2) (y, s)) ∂μ := by
    rw [← lintegral_indicator measurableSet_Ioc]
    congr 1; funext y
    by_cases hy : y ∈ Ioc a b
    · rw [indicator_of_mem hy, ← lintegral_indicator measurableSet_Ioc]
      congr 1; funext s
      by_cases hs : s ∈ Ioc (y - 2) (y - 1)
      · rw [indicator_of_mem hs, indicator_of_mem ((hmem y s).2 ⟨hy, hs⟩)]
      · rw [indicator_of_notMem hs, indicator_of_notMem fun h => hs ((hmem y s).1 h).2]
    · rw [indicator_of_notMem hy]
      symm
      refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun s => ?_)
      exact indicator_of_notMem (fun h => hy ((hmem y s).1 h).1) _
  have hmeas : AEMeasurable (Function.uncurry fun y s => S.indicator (fun p => g p.2) (y, s))
      (μ.prod volume) := ((hg.comp measurable_snd).indicator hS).aemeasurable
  rw [hL, lintegral_lintegral_swap hmeas, ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_mono fun s => ?_
  by_cases hs : s ∈ Ioc (a - 2) (b - 1)
  · rw [indicator_of_mem hs, ← lintegral_indicator_const measurableSet_Ioi]
    refine lintegral_mono fun y => ?_
    by_cases hys : (y, s) ∈ S
    · obtain ⟨-, hs2⟩ := (hmem y s).1 hys
      rw [indicator_of_mem hys, indicator_of_mem (show y ∈ Ioi s from by
        simp only [mem_Ioi]; linarith [hs2.2])]
    · rw [indicator_of_notMem hys]; exact bot_le
  · rw [indicator_of_notMem hs]
    refine (lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun y => ?_)).le
    refine indicator_of_notMem (fun h => hs ?_) _
    obtain ⟨hy, hs2⟩ := (hmem y s).1 h
    exact ⟨by linarith [hy.1, hs2.1], by linarith [hy.2, hs2.2]⟩

end Basic

namespace IsSStar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem tendsto_intervalIntegral_tail (h : IsSStar μ) {b : ℝ → ℝ} (hb : Tendsto b atTop atTop) :
    Tendsto (fun x => ∫ y in (0 : ℝ)..b x, tail μ y) atTop (𝓝 (∫ t in Ioi 0, tail μ t)) :=
  intervalIntegral_tendsto_integral_Ioi 0 h.integrableOn_tail hb

/-- **`𝒮*` laws are long-tailed** ([Klüppelberg 1988]; [FKZ, Ch. 3]): `F̄(x - t) / F̄(x) → 1` for every `t`. -/
theorem tendsto_tail_sub_div_of_nonneg (h : IsSStar μ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun x => tail μ (x - t) / tail μ x) atTop (𝓝 1) := by
  set m := ∫ s in Ioi 0, tail μ s
  set A := ∫ y in (0 : ℝ)..t, tail μ y
  set B : ℝ → ℝ := fun x => ∫ y in t..x / 2, tail μ y
  have hF := h.tail_pos
  -- `B x → m - A`
  have hB : Tendsto B atTop (𝓝 (m - A)) := by
    refine ((h.tendsto_intervalIntegral_tail (tendsto_id.atTop_div_const two_pos)).sub_const
      A).congr fun x => ?_
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_tail _ _)
      (intervalIntegrable_tail _ _)
  -- `m - A ≥ F̄(t + 1) > 0`
  have hBpos : 0 < m - A := by
    refine (hF (t + 1)).trans_le (ge_of_tendsto hB ?_)
    filter_upwards [eventually_ge_atTop (2 * (t + 1))] with x hx
    have h1 : ∫ _ in t..t + 1, tail μ (t + 1) ≤ ∫ y in t..t + 1, tail μ y :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (intervalIntegrable_tail _ _) fun y hy => tail_antitone hy.2
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, one_mul] at h1
    have h2 : ∫ y in t..t + 1, tail μ y ≤ B x := by
      simp only [B]
      have e := intervalIntegral.integral_add_adjacent_intervals (a := t) (b := t + 1) (c := x / 2)
        (intervalIntegrable_tail (μ := μ) _ _) (intervalIntegrable_tail _ _)
      have := intervalIntegral.integral_nonneg (μ := volume) (a := t + 1) (b := x / 2) (by linarith)
        fun y _ => tail_nonneg (μ := μ) y
      linarith
    nlinarith
  -- the key lower bound `I(x) / F̄(x) ≥ 2 A + 2 (F̄(x - t) / F̄(x)) B(x)`
  have hkey : ∀ x, 2 * t ≤ x →
      2 * A + 2 * (tail μ (x - t) / tail μ x) * B x ≤ tailConvInt μ x / tail μ x := by
    intro x hx
    have hFx := hF x
    rw [tailConvInt_eq_two_mul, ← intervalIntegral.integral_add_adjacent_intervals (b := t)
      (intervalIntegrable_K x _ _) (intervalIntegrable_K x _ _)]
    have h1 := integral_K_ge (μ := μ) (x := x) (a := 0) (b := t) (c := tail μ x) ht
      fun y hy => tail_antitone (by linarith [hy.1])
    have h2 := integral_K_ge (μ := μ) (x := x) (a := t) (b := x / 2) (c := tail μ (x - t))
      (by linarith) fun y hy => tail_antitone (by linarith [hy.1])
    rw [le_div_iff₀ hFx]
    have e : 2 * (tail μ (x - t) / tail μ x) * B x * tail μ x = 2 * (tail μ (x - t) * B x) := by
      field_simp
    rw [add_mul, e]
    simp only [B, A] at h1 h2 ⊢
    nlinarith
  have hup : Tendsto (fun x => (tailConvInt μ x / tail μ x - 2 * A) / (2 * B x)) atTop
      (𝓝 ((2 * m - 2 * A) / (2 * (m - A)))) :=
    (h.tendsto_tailConvInt_div.sub_const _).div (hB.const_mul 2) (by positivity)
  rw [show (2 * m - 2 * A) / (2 * (m - A)) = 1 by field_simp] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall fun x => (one_le_div (hF x)).2 (tail_antitone (by linarith))
  · filter_upwards [eventually_ge_atTop (2 * t), (tendsto_order.1 hB).1 0 hBpos] with x hx hBx
    rw [le_div_iff₀ (by positivity)]
    have := hkey x hx
    linarith

/-- **`𝒮*` laws are long-tailed**: `F̄(x - y) / F̄(x) → 1` for every `y ∈ ℝ`. -/
theorem tendsto_tail_sub_div (h : IsSStar μ) (y : ℝ) :
    Tendsto (fun x => tail μ (x - y) / tail μ x) atTop (𝓝 1) := by
  rcases le_total 0 y with hy | hy
  · exact h.tendsto_tail_sub_div_of_nonneg hy
  · have h1 := ((h.tendsto_tail_sub_div_of_nonneg (t := -y) (by linarith)).inv₀
      one_ne_zero).comp (tendsto_atTop_add_const_right _ (-y) tendsto_id)
    simp only [inv_one] at h1
    refine h1.congr fun x => ?_
    simp only [Function.comp_apply, id, inv_div, sub_neg_eq_add]
    ring_nf

/-- **`𝒮* ⊆ 𝒮`** ([Klüppelberg 1988, Theorem 3.2]; [FKZ, Ch. 3]): a law in the class
`𝒮*` is subexponential. -/
theorem isSubexponential (h : IsSStar μ) : IsSubexponential μ := by
  have hF := h.tail_pos
  have h0 := h.nonneg
  set m := ∫ t in Ioi 0, tail μ t with hm
  refine ⟨h0, hF, ?_⟩
  rw [tendsto_order]
  constructor
  · intro b hb
    have hlim : Tendsto (fun x => 2 - tail μ x) atTop (𝓝 (2 - 0)) :=
      (tendsto_tail_atTop (μ := μ)).const_sub 2
    filter_upwards [(tendsto_order.1 hlim).1 b (by linarith)] with x hx
    refine hx.trans_le ?_
    have := tail_conv_self_ge h0 (le_refl x)
    rw [le_div_iff₀ (hF x)]
    nlinarith [tail_nonneg (μ := μ) (x - x)]
  intro b hb
  set ε := (b - 2) / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  -- `∫₀ʷ F̄ ≥ m - ε`
  obtain ⟨w, hw, hw0⟩ := (((tendsto_order.1 (h.tendsto_intervalIntegral_tail tendsto_id)).1
    (m - ε) (by linarith)).and (eventually_ge_atTop (0 : ℝ))).exists
  simp only [id] at hw
  -- long tail: `F̄(z - 2) ≤ 2 F̄(z)` for `z ≥ z₁`
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, ∀ z ≥ z₁, tail μ (z - 2) ≤ 2 * tail μ z := by
    obtain ⟨z₁, hz⟩ := eventually_atTop.1 ((tendsto_order.1 (h.tendsto_tail_sub_div 2)).2 2
      (by norm_num))
    exact ⟨z₁, fun z hz' => by have := hz z hz'; rw [div_lt_iff₀ (hF z)] at this; linarith⟩
  set v := max (w + 2) z₁ with hv
  have hvw : w + 2 ≤ v := le_max_left _ _
  have hvz : z₁ ≤ v := le_max_right _ _
  have hlim : Tendsto (fun x => 2 * (tail μ (x - v) / tail μ x) +
      2 * (tailConvInt μ x / tail μ x - 2 * (m - ε))) atTop
      (𝓝 (2 * 1 + 2 * (2 * m - 2 * (m - ε)))) :=
    ((h.tendsto_tail_sub_div v).const_mul 2).add
      ((h.tendsto_tailConvInt_div.sub_const _).const_mul 2)
  filter_upwards [(tendsto_order.1 hlim).2 b (by rw [hε]; linarith),
    eventually_ge_atTop (2 * v + 2)] with x hx hxv
  refine lt_of_le_of_lt ?_ hx
  have hFx := hF x
  rw [div_le_iff₀ hFx]
  -- the middle part `M = ∫_w^{x-w} F̄(x - y) F̄(y) dy`
  set M := ∫ y in w..x - w, tail μ (x - y) * tail μ y with hM
  have hMle : M ≤ tailConvInt μ x - 2 * tail μ x * (m - ε) := by
    have hsplit : tailConvInt μ x = (∫ y in (0 : ℝ)..w, tail μ (x - y) * tail μ y) + M +
        ∫ y in x - w..x, tail μ (x - y) * tail μ y := by
      rw [tailConvInt, intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_K x _ _)
        (intervalIntegrable_K x _ _), intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_K x _ _) (intervalIntegrable_K x _ _)]
    have h1 := integral_K_ge (μ := μ) (x := x) (a := 0) (b := w) (c := tail μ x) hw0
      fun y hy => tail_antitone (by linarith [hy.1])
    have h2 : ∫ y in x - w..x, tail μ (x - y) * tail μ y =
        ∫ y in (0 : ℝ)..w, tail μ (x - y) * tail μ y := by
      rw [integral_K_reflect]; simp
    have : tail μ x * (m - ε) ≤ tail μ x * ∫ y in (0 : ℝ)..w, tail μ y :=
      mul_le_mul_of_nonneg_left hw.le hFx.le
    rw [hsplit, h2]; nlinarith
  -- the middle part of the convolution, smeared
  have hJ2 : ∫ y in Ioc v (x - v), tail μ (x - y) ∂μ ≤ 2 * M := by
    have hint : IntegrableOn (fun s => tail μ (x - s) * tail μ s) (Ioc (v - 2) (x - v - 1)) :=
      (intervalIntegrable_K x _ _).1
    have hK : ∫ s in Ioc (v - 2) (x - v - 1), tail μ (x - s) * tail μ s ≤ M := by
      rw [hM, intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_mono_set (intervalIntegrable_K (μ := μ) x w (x - w)).1
        (ae_of_all _ fun s => K_nonneg x s)
        (Ioc_subset_Ioc (by linarith) (by linarith)).eventuallyLE
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hK zero_le_two)
    rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg zero_le_two
        (setIntegral_nonneg measurableSet_Ioc fun s _ => K_nonneg x s)),
      ofReal_integral_eq_lintegral_ofReal (integrable_tail_sub x).integrableOn
        (ae_of_all _ fun _ => tail_nonneg _),
      ENNReal.ofReal_mul zero_le_two, ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun s => K_nonneg x s), ENNReal.ofReal_ofNat]
    have hgm : Measurable fun s => ENNReal.ofReal (tail μ (x - s)) :=
      ENNReal.measurable_ofReal.comp (tail_measurable.comp (measurable_const.sub measurable_id))
    calc ∫⁻ y in Ioc v (x - v), ENNReal.ofReal (tail μ (x - y)) ∂μ
        ≤ ∫⁻ y in Ioc v (x - v), 2 * (∫⁻ s in Ioc (y - 2) (y - 1),
            ENNReal.ofReal (tail μ (x - s))) ∂μ := by
          refine setLIntegral_mono' measurableSet_Ioc fun y hy => ?_
          have hy2 : tail μ (x - y) ≤ 2 * tail μ (x - y + 2) := by
            have := hz₁ (x - y + 2) (by linarith [hy.2])
            rwa [add_sub_cancel_right] at this
          have hlow : ENNReal.ofReal (tail μ (x - y + 2)) ≤
              ∫⁻ s in Ioc (y - 2) (y - 1), ENNReal.ofReal (tail μ (x - s)) := by
            have := setLIntegral_mono' (μ := volume) (s := Ioc (y - 2) (y - 1))
              (f := fun _ => ENNReal.ofReal (tail μ (x - y + 2)))
              (g := fun s => ENNReal.ofReal (tail μ (x - s))) measurableSet_Ioc
              fun s hs => ENNReal.ofReal_le_ofReal (tail_antitone (by linarith [hs.1]))
            rwa [setLIntegral_const, Real.volume_Ioc, show y - 1 - (y - 2) = 1 by ring,
              ENNReal.ofReal_one, mul_one] at this
          calc ENNReal.ofReal (tail μ (x - y)) ≤ ENNReal.ofReal (2 * tail μ (x - y + 2)) :=
                ENNReal.ofReal_le_ofReal hy2
            _ = 2 * ENNReal.ofReal (tail μ (x - y + 2)) := by
                rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
            _ ≤ _ := by gcongr
      _ = 2 * ∫⁻ y in Ioc v (x - v), (∫⁻ s in Ioc (y - 2) (y - 1),
            ENNReal.ofReal (tail μ (x - s))) ∂μ := lintegral_const_mul' _ _ (by simp)
      _ ≤ 2 * ∫⁻ s in Ioc (v - 2) (x - v - 1), ENNReal.ofReal (tail μ (x - s)) * μ (Ioi s) :=
          mul_le_mul_of_nonneg_left (lintegral_smear_le hgm v (x - v)) bot_le
      _ = 2 * ∫⁻ s in Ioc (v - 2) (x - v - 1), ENNReal.ofReal (tail μ (x - s) * tail μ s) := by
          congr 1
          refine lintegral_congr fun s => ?_
          rw [ENNReal.ofReal_mul (tail_nonneg _)]
          congr 1
          rw [tail, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- assemble
  have hsplit := tail_conv_split (μ := μ) (ν := μ) h0 (a := v) (x := x) (by linarith)
  have hunion : ∫ y in Ioc v x, tail μ (x - y) ∂μ = (∫ y in Ioc v (x - v), tail μ (x - y) ∂μ) +
      ∫ y in Ioc (x - v) x, tail μ (x - y) ∂μ := by
    rw [← Ioc_union_Ioc_eq_Ioc (b := x - v) (by linarith) (by linarith),
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (integrable_tail_sub x).integrableOn (integrable_tail_sub x).integrableOn]
  have hJ1 : ∫ y in Iic v, tail μ (x - y) ∂μ ≤ tail μ (x - v) := by
    have := setIntegral_mono_on (μ := μ) (s := Iic v) (integrable_tail_sub x).integrableOn
      (integrableOn_const (C := tail μ (x - v))) measurableSet_Iic
      fun y hy => tail_antitone (by linarith [show y ≤ v from hy])
    rw [setIntegral_const, smul_eq_mul] at this
    have h1 : μ.real (Iic v) ≤ 1 := measureReal_le_one
    nlinarith [tail_nonneg (μ := μ) (x - v)]
  have hJ3 : ∫ y in Ioc (x - v) x, tail μ (x - y) ∂μ ≤ tail μ (x - v) - tail μ x := by
    have := setIntegral_tail_sub_le (μ := μ) (ν := μ) (measurableSet_Ioc (a := x - v) (b := x)) x
    rwa [measureReal_Ioc_eq (by linarith)] at this
  have e : (2 * (tail μ (x - v) / tail μ x) + 2 * (tailConvInt μ x / tail μ x - 2 * (m - ε))) *
      tail μ x = 2 * tail μ (x - v) + 2 * (tailConvInt μ x - 2 * tail μ x * (m - ε)) := by
    field_simp
  rw [e, hsplit, hunion]
  linarith

/-! ### The integrated tail of an `𝒮*` law is subexponential -/

/-- The density of `F_I`: `f_I = m⁻¹ F̄` on `(0, ∞)`. -/
private noncomputable def itDensity (μ : Measure ℝ) : ℝ → ℝ≥0∞ :=
  ENNReal.ofReal (∫ t in Ioi 0, tail μ t)⁻¹ • (Ioi 0).indicator fun t => ENNReal.ofReal (tail μ t)

private theorem measurable_itDensity : Measurable (itDensity μ) :=
  ((ENNReal.measurable_ofReal.comp tail_measurable).indicator measurableSet_Ioi).const_smul _

private theorem integratedTail_eq_withDensity :
    integratedTail μ = volume.withDensity (itDensity μ) := by
  have hg : Measurable fun t => ENNReal.ofReal (tail μ t) :=
    ENNReal.measurable_ofReal.comp tail_measurable
  rw [itDensity, withDensity_smul _ (hg.indicator measurableSet_Ioi),
    withDensity_indicator measurableSet_Ioi, integratedTail]

omit [IsProbabilityMeasure μ] in
private theorem itDensity_of_pos {u : ℝ} (hu : 0 < u) :
    itDensity μ u = ENNReal.ofReal (∫ t in Ioi 0, tail μ t)⁻¹ * ENNReal.ofReal (tail μ u) := by
  rw [itDensity, Pi.smul_apply, indicator_of_mem (show u ∈ Ioi 0 from hu), smul_eq_mul]

/-- The density of `F_I ∗ F_I` is `m⁻² I(u)` on `(0, ∞)`. -/
private theorem lconvolution_itDensity {u : ℝ} (hu : 0 < u) :
    (itDensity μ ⋆ₗ itDensity μ) u =
      ENNReal.ofReal (∫ t in Ioi 0, tail μ t)⁻¹ * ENNReal.ofReal (∫ t in Ioi 0, tail μ t)⁻¹ *
        ENNReal.ofReal (tailConvInt μ u) := by
  set c := ENNReal.ofReal (∫ t in Ioi 0, tail μ t)⁻¹
  have hpt : ∀ y, itDensity μ y * itDensity μ (-y + u) =
      c * c * (Ioo 0 u).indicator (fun y => ENNReal.ofReal (tail μ (u - y) * tail μ y)) y := by
    intro y
    simp only [itDensity, Pi.smul_apply, smul_eq_mul]
    by_cases hy : y ∈ Ioo 0 u
    · rw [indicator_of_mem (show y ∈ Ioi 0 from hy.1),
        indicator_of_mem (show -y + u ∈ Ioi 0 by simp only [mem_Ioi]; linarith [hy.2]),
        indicator_of_mem hy, neg_add_eq_sub, ENNReal.ofReal_mul (tail_nonneg _)]
      ring
    · rw [indicator_of_notMem hy]
      simp only [mem_Ioo, not_and_or, not_lt] at hy
      rcases hy with hy | hy
      · rw [indicator_of_notMem (show y ∉ Ioi 0 by simpa using hy)]; simp
      · rw [indicator_of_notMem (show -y + u ∉ Ioi 0 by simp only [mem_Ioi]; linarith)]; simp
  rw [lconvolution_def]
  simp_rw [hpt]
  have hm : Measurable fun y =>
      (Ioo 0 u).indicator (fun y => ENNReal.ofReal (tail μ (u - y) * tail μ y)) y :=
    (ENNReal.measurable_ofReal.comp (measurable_K u)).indicator measurableSet_Ioo
  rw [lintegral_const_mul _ hm, lintegral_indicator measurableSet_Ioo,
    ← ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_K (μ := μ) u 0 u).1.mono_set Ioo_subset_Ioc_self)
      (ae_of_all _ fun y => K_nonneg u y)]
  rw [tailConvInt, intervalIntegral.integral_of_le hu.le, integral_Ioc_eq_integral_Ioo]

/-- The mean `m = ∫₀^∞ F̄` of an `𝒮*` law is positive. -/
theorem integral_tail_pos (h : IsSStar μ) : 0 < ∫ t in Ioi 0, tail μ t := by
  have h1 : ∫ _ in (0 : ℝ)..1, tail μ 1 ≤ ∫ y in (0 : ℝ)..1, tail μ y :=
    intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
      (intervalIntegrable_tail _ _) fun y hy => tail_antitone hy.2
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul,
    intervalIntegral.integral_of_le zero_le_one] at h1
  have h2 : ∫ y in Ioc (0 : ℝ) 1, tail μ y ≤ ∫ y in Ioi (0 : ℝ), tail μ y :=
    setIntegral_mono_set h.integrableOn_tail (ae_of_all _ fun y => tail_nonneg y)
      Ioc_subset_Ioi_self.eventuallyLE
  linarith [h.tail_pos 1]

/-- **Integrated tails of `𝒮*` laws are subexponential** ([Klüppelberg 1988, Theorem 3.2];
[FKZ, Ch. 3]): if `F ∈ 𝒮*` then `F_I ∈ 𝒮`, where `F_I` has density `F̄ / m` on
`(0, ∞)`. -/
theorem isSubexponential_integratedTail (h : IsSStar μ) :
    IsSubexponential (integratedTail μ) := by
  have hm := h.integral_tail_pos
  set m := ∫ t in Ioi 0, tail μ t with hm_def
  have := isProbabilityMeasure_integratedTail h.integrableOn_tail hm
  set ν := integratedTail μ
  set c := ENNReal.ofReal m⁻¹ with hc
  have hν : ν = volume.withDensity (itDensity μ) := integratedTail_eq_withDensity
  have hνν : ν ∗ ν = volume.withDensity (itDensity μ ⋆ₗ itDensity μ) := by
    rw [hν]; exact conv_withDensity_eq_lconvolution measurable_itDensity measurable_itDensity
  -- tails of `ν` are positive
  have hpos : ∀ x, 0 < tail ν x := by
    intro x
    rcases lt_or_ge x 0 with hx | hx
    · rw [tail_of_neg integratedTail_Iio_zero hx]; exact one_pos
    rw [tail_integratedTail h.integrableOn_tail hx]
    refine mul_pos (inv_pos.2 hm) ?_
    have h1 : ∫ _ in x..x + 1, tail μ (x + 1) ≤ ∫ y in x..x + 1, tail μ y :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (intervalIntegrable_tail _ _) fun y hy => tail_antitone hy.2
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, one_mul,
      intervalIntegral.integral_of_le (by linarith)] at h1
    have h2 : ∫ y in Ioc x (x + 1), tail μ y ≤ ∫ y in Ioi x, tail μ y :=
      setIntegral_mono_set (h.integrableOn_tail.mono_set (Ioi_subset_Ioi hx))
        (ae_of_all _ fun y => tail_nonneg y) Ioc_subset_Ioi_self.eventuallyLE
    linarith [h.tail_pos (x + 1)]
  -- the two-sided comparison for large `x`
  have hcmp : ∀ ε, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop,
      (2 - ε) * tail ν x ≤ tail (ν ∗ ν) x ∧ tail (ν ∗ ν) x ≤ (2 + ε) * tail ν x := by
    intro ε hε hε1
    have hlim := h.tendsto_tailConvInt_div
    have hlo := (tendsto_order.1 hlim).1 ((2 - ε) * m) (by nlinarith)
    have hhi := (tendsto_order.1 hlim).2 ((2 + ε) * m) (by nlinarith)
    obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 ((hlo.and hhi).and (eventually_gt_atTop 0))
    filter_upwards [eventually_ge_atTop x₁] with x hx
    -- pointwise comparison of densities on `(x, ∞)`
    have hpt : ∀ u ∈ Ioi x, ENNReal.ofReal (2 - ε) * itDensity μ u ≤
        (itDensity μ ⋆ₗ itDensity μ) u ∧
        (itDensity μ ⋆ₗ itDensity μ) u ≤ ENNReal.ofReal (2 + ε) * itDensity μ u := by
      intro u hu
      obtain ⟨⟨hl, hh⟩, hu0⟩ := hx₁ u (hx.trans (le_of_lt hu))
      have hFu := h.tail_pos u
      rw [lt_div_iff₀ hFu] at hl
      rw [div_lt_iff₀ hFu] at hh
      rw [itDensity_of_pos hu0, lconvolution_itDensity hu0]
      have e1 : c * c * ENNReal.ofReal (tailConvInt μ u) =
          c * ENNReal.ofReal (m⁻¹ * tailConvInt μ u) := by
        rw [hc, mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hm.le)]
      rw [e1, mul_left_comm, mul_left_comm _ c]
      constructor
      · refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [← ENNReal.ofReal_mul (by linarith)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_inv_mul_iff₀ hm]; nlinarith
      · refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [← ENNReal.ofReal_mul (by linarith)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_mul_le_iff₀ hm]; nlinarith
    have hA : ν (Ioi x) = ∫⁻ u in Ioi x, itDensity μ u := by
      rw [hν, withDensity_apply _ measurableSet_Ioi]
    have hB : (ν ∗ ν) (Ioi x) = ∫⁻ u in Ioi x, (itDensity μ ⋆ₗ itDensity μ) u := by
      rw [hνν, withDensity_apply _ measurableSet_Ioi]
    have hlow : ENNReal.ofReal (2 - ε) * ν (Ioi x) ≤ (ν ∗ ν) (Ioi x) := by
      rw [hA, hB, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_Ioi fun u hu => (hpt u hu).1
    have hhigh : (ν ∗ ν) (Ioi x) ≤ ENNReal.ofReal (2 + ε) * ν (Ioi x) := by
      rw [hA, hB, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_Ioi fun u hu => (hpt u hu).2
    have hε2 : 0 ≤ 2 + ε := by linarith
    constructor
    · rcases le_total (2 - ε) 0 with hneg | hnn
      · exact (mul_nonpos_of_nonpos_of_nonneg hneg (tail_nonneg _)).trans (tail_nonneg _)
      · have := ENNReal.toReal_mono (measure_ne_top _ _) hlow
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn] at this
    · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _)) hhigh
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε2] at this
  refine ⟨integratedTail_Iio_zero, hpos, ?_⟩
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [hcmp (min ((2 - b) / 2) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)]
      with x hx
    rw [lt_div_iff₀ (hpos x)]
    have : min ((2 - b) / 2) 1 ≤ (2 - b) / 2 := min_le_left _ _
    nlinarith [hx.1, hpos x]
  · intro b hb
    filter_upwards [hcmp (min ((b - 2) / 2) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)]
      with x hx
    have : min ((b - 2) / 2) 1 ≤ (b - 2) / 2 := min_le_left _ _
    rw [div_lt_iff₀ (hpos x)]
    nlinarith [hx.2, hpos x]

/-- **Embrechts–Veraverbeke for `𝒮*` claims** ([EKM, Theorem 1.3.6]; [Klüppelberg 1988]): if
the claim size law is in `𝒮*` and the safety loading is `ρ > 0`, the Pollaczek–Khinchine ruin
probability satisfies `ψ(u) / F̄_I(u) → 1 / ρ`. -/
theorem tendsto_pkRuin_div (h : IsSStar μ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun u => pkRuin ρ (integratedTail μ) u / tail (integratedTail μ) u) atTop
      (𝓝 (1 / ρ)) := by
  have := isProbabilityMeasure_integratedTail h.integrableOn_tail h.integral_tail_pos
  exact h.isSubexponential_integratedTail.tendsto_pkRuin_div hρ

/-- **Regularly varying tails with index `-α`, `α > 1`, are in `𝒮*`** ([Klüppelberg 1988];
[FKZ, Ch. 3]). -/
theorem of_isRegularlyVarying (h0 : μ (Iio 0) = 0) {α : ℝ}
    (hRV : IsRegularlyVarying (tail μ) (-α)) (hα : 1 < α) : IsSStar μ := by
  have hS := IsSubexponential.of_isRegularlyVarying h0 hRV
  have hF := hS.tail_pos
  have hint := IsRegularlyVarying.integrableOn_Ioi tail_antitone hRV hα 0
  refine ⟨h0, hF, hint, ?_⟩
  -- `I(x) / F̄(x) = 2 ∫_{(0, x/2]} (F̄(x - y) / F̄(x)) F̄(y) dy`
  have hI : ∀ x, 0 ≤ x → tailConvInt μ x / tail μ x = 2 * ∫ y in Ioi 0,
      (Ioc 0 (x / 2)).indicator (fun y => tail μ (x - y) / tail μ x * tail μ y) y := by
    intro x hx
    rw [tailConvInt_eq_two_mul, intervalIntegral.integral_of_le (by linarith),
      setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self,
      mul_div_assoc, ← integral_div]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc fun y _ => by ring
  -- a bound `F̄(x / 2) / F̄(x) ≤ C` for large `x`
  set C := (1 / 2 : ℝ) ^ (-α) + 1
  have hC : ∀ᶠ x in atTop, tail μ (x / 2) / tail μ x ≤ C := by
    have := (tendsto_order.1 (hRV.2 (1 / 2) (by norm_num))).2 C (by simp only [C]; linarith)
    filter_upwards [this] with x hx
    rw [show x / 2 = 1 / 2 * x by ring]; exact hx.le
  have hDCT : Tendsto (fun x => ∫ y in Ioi 0,
      (Ioc 0 (x / 2)).indicator (fun y => tail μ (x - y) / tail μ x * tail μ y) y) atTop
      (𝓝 (∫ y in Ioi 0, tail μ y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => C * tail μ y)
      (Eventually.of_forall fun x => ?_) ?_ (hint.const_mul C) ?_
    · exact ((((tail_measurable.comp (measurable_const.sub measurable_id)).div_const _).mul
        tail_measurable).indicator measurableSet_Ioc).aestronglyMeasurable
    · filter_upwards [hC] with x hx
      refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ Ioc 0 (x / 2)
      · rw [indicator_of_mem hy, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (div_nonneg (tail_nonneg _) (hF x).le) (tail_nonneg _))]
        refine mul_le_mul_of_nonneg_right ?_ (tail_nonneg _)
        refine le_trans ?_ hx
        exact div_le_div_of_nonneg_right (tail_antitone (by linarith [hy.2])) (hF x).le
      · rw [indicator_of_notMem hy, norm_zero]
        exact mul_nonneg (by simp only [C]; positivity) (tail_nonneg _)
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun y (hy : 0 < y) => ?_
      have := (hS.tendsto_tail_sub_div y).mul_const (tail μ y)
      rw [one_mul] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop (2 * y)] with x hx
      rw [indicator_of_mem (show y ∈ Ioc 0 (x / 2) from ⟨hy, by linarith⟩)]
  refine (hDCT.const_mul 2).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact (hI x hx).symm

end IsSStar

/-- **Pareto laws with index `r > 1` are in `𝒮*`**; in particular their integrated tails are
subexponential. -/
theorem isSStar_paretoMeasure {t r : ℝ} (ht : 0 < t) (hr : 1 < r) :
    IsSStar (ProbabilityTheory.paretoMeasure t r) := by
  have := ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht (by linarith : 0 < r)
  exact IsSStar.of_isRegularlyVarying (paretoMeasure_Iio_zero ht)
    (isRegularlyVarying_tail_paretoMeasure ht (by linarith)) hr

end ExtremeValueTheory
