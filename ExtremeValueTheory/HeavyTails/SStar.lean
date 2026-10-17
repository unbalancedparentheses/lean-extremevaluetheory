/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.Ruin
import ExtremeValueTheory.HeavyTails.StretchedExponential
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The class `𝒮*` of Klüppelberg

A probability measure `μ` on `[0, ∞)` with positive tail `F̄` and finite mean
`m = ∫₀^∞ F̄(y) dy` belongs to **`𝒮*`** ([Klüppelberg 1988]; [EKM, Definition A3.? / §1.4];
[FKZ, §3.6]) if

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
* `IsSStar.isSubexponential`: `𝒮* ⊆ 𝒮` ([Klüppelberg 1988, Theorem 3.2(a)]; [FKZ, Theorem 3.27]).
* `IsSStar.isSubexponential_integratedTail`: `F ∈ 𝒮* ⇒ F_I ∈ 𝒮` ([Klüppelberg 1988,
  Theorem 3.2(b)]; [FKZ, Theorem 3.28]; [EKM, Theorem A3.? / Example 1.4.?]).
* `IsSStar.tendsto_pkRuin_div`: Embrechts–Veraverbeke for `𝒮*` claims.
* `IsSStar.of_isRegularlyVarying`: `F̄ ∈ RV_{-α}`, `α > 1` ⇒ `F ∈ 𝒮*`.

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

/-- **The class `𝒮*`** ([Klüppelberg 1988]; [FKZ, §3.6]): `μ` is concentrated on `[0, ∞)`, has
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

end Basic

namespace IsSStar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem tendsto_intervalIntegral_tail (h : IsSStar μ) {b : ℝ → ℝ} (hb : Tendsto b atTop atTop) :
    Tendsto (fun x => ∫ y in (0 : ℝ)..b x, tail μ y) atTop (𝓝 (∫ t in Ioi 0, tail μ t)) :=
  intervalIntegral_tendsto_integral_Ioi 0 h.integrableOn_tail hb

/-- **`𝒮*` laws are long-tailed** ([FKZ, Lemma 3.25]): `F̄(x - t) / F̄(x) → 1` for every `t`. -/
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

end IsSStar

end ExtremeValueTheory
