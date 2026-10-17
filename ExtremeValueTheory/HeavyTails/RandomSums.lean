/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.Subexponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Closure properties of subexponential distributions and random sums

## Main results

* `IsSubexponential.tendsto_tail_conv_div_of_tendsto`: if `μ` is subexponential and
  `F̄_{νᵢ}(x) / F̄_μ(x) → cᵢ > 0` (`i = 1, 2`), then `F̄_{ν₁∗ν₂}(x) / F̄_μ(x) → c₁ + c₂`
  ([EKM, Lemma A3.15] / Foss–Korshunov–Zachary, Corollary 3.18).
* `IsSubexponential.of_tendsto_tail_div`: subexponentiality is a tail-equivalence class
  property: if `μ ∈ 𝒮` and `F̄_ν ~ c F̄_μ` with `c > 0`, then `ν ∈ 𝒮` ([EKM, Lemma A3.15]).
* `IsSubexponential.convPow`: `μ ∈ 𝒮 ⟹ μ^{*n} ∈ 𝒮` for `n ≥ 1`.
* `IsSubexponential.tendsto_tsum_tail_convPow_div`: **random sums** ([EKM, Lemma 1.3.5(c)
  ⟹ Theorem A3.20]): if `pₙ ≥ 0` and `∑ pₙ (1 + ε)ⁿ < ∞` for some `ε > 0`, then
  `(∑ₙ pₙ F̄^{*n}(x)) / F̄(x) → ∑ₙ n pₙ`.
* `compound μ p = ∑ₙ pₙ μ^{*n}` is the compound law (the law of `S_N = X₁ + ⋯ + X_N` with
  `N ∼ p` independent of the i.i.d. `Xᵢ ∼ μ`), and `IsSubexponential.tendsto_tail_compound_div`
  states `P(S_N > x) / F̄(x) → E N`.

Here [EKM] is Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events for Insurance and
Finance* (Springer, 1997).

## Proof outline

For the convolution of two tail-equivalent laws `A, B` we split
`F̄_{A∗B}(x) = ∫_{t ≤ x - v} F̄_B(x - t) dA + ∫_{x - v < t ≤ x} F̄_B(x - t) dA + F̄_A(x)`.
On `t ≤ x - v`, `F̄_B(x - t)` is within `(c₂ ± ε) F̄_μ(x - t)`, and the integral
`∫_{t ≤ x - v} F̄_μ(x - t) dA` is computed from `F̄_{μ∗A} = F̄_{A∗μ}` (which is known from
`IsSubexponential.tendsto_tail_conv_div`): it is `~ (c₁ + 1 - c₁) F̄_μ(x) = F̄_μ(x)`. The middle
term is bounded by `F̄_A(x - v) - F̄_A(x) = o(F̄_μ(x))` by long-tailedness.

Random sums follow from `F̄^{*n}/F̄ → n` and Kesten's bound by dominated convergence for series
(`tendsto_tsum_of_dominated_convergence`).
-/

open Filter Topology Set Real MeasureTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

open Subexp

namespace IsSubexponential

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- If `F̄_A / F̄_μ → c` and `μ` is long-tailed, then `F̄_A(x - v) / F̄_μ(x) → c`. -/
theorem tendsto_tail_sub_div_of_tendsto (h : IsSubexponential μ) {A : Measure ℝ} {c : ℝ}
    (hA : Tendsto (fun x => tail A x / tail μ x) atTop (𝓝 c)) (v : ℝ) :
    Tendsto (fun x => tail A (x - v) / tail μ x) atTop (𝓝 c) := by
  have h1 := hA.comp (tendsto_atTop_add_const_right _ (-v) tendsto_id)
  have h2 := (h1.mul (h.tendsto_tail_sub_div v))
  rw [mul_one] at h2
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply, id, ← sub_eq_add_neg]
  rw [div_mul_div_cancel₀ (h.tail_pos _).ne']

/-- The two-sided estimate behind `tendsto_tail_conv_div_of_tendsto`. -/
private theorem conv_bounds' {A B : Measure ℝ} [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (h : IsSubexponential μ) (hB0 : B (Iio 0) = 0) {c ε v : ℝ} (hcε : 0 ≤ c - ε) (hε : 0 ≤ ε)
    (hv : 0 ≤ v) (hG : ∀ s ≥ v, |tail B s / tail μ s - c| < ε) (x : ℝ) :
    tail (A ∗ B) x ≤ (c + ε) * (tail (μ ∗ A) x - tail A x) + tail A (x - v) ∧
      (c - ε) * (tail (μ ∗ A) x - tail A (x - v)) + tail A x ≤ tail (A ∗ B) x := by
  have hax : x - v ≤ x := by linarith
  have hT := tail_conv_split (μ := A) hB0 hax
  have hS := tail_conv_split (μ := A) h.nonneg hax
  rw [Measure.conv_comm] at hS
  have hiG := (integrable_tail_sub (μ := A) (ν := B) x).integrableOn (s := Iic (x - v))
  have hiF := (integrable_tail_sub (μ := A) (ν := μ) x).integrableOn (s := Iic (x - v))
  have hpt : ∀ t ∈ Iic (x - v), (c - ε) * tail μ (x - t) ≤ tail B (x - t) ∧
      tail B (x - t) ≤ (c + ε) * tail μ (x - t) := by
    intro t ht
    have hs : v ≤ x - t := by have : t ≤ x - v := ht; linarith
    have h1 := hG _ hs
    have hFp := h.tail_pos (x - t)
    rw [abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, lt_div_iff₀ hFp, div_lt_iff₀ hFp] at h1
    constructor <;> nlinarith
  have hup : ∫ t in Iic (x - v), tail B (x - t) ∂A ≤
      (c + ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂A := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hiG (hiF.const_mul _) measurableSet_Iic fun t ht => (hpt t ht).2
  have hlo : (c - ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂A ≤
      ∫ t in Iic (x - v), tail B (x - t) ∂A := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hiF.const_mul _) hiG measurableSet_Iic fun t ht => (hpt t ht).1
  have hMG := setIntegral_tail_sub_le (μ := A) (ν := B) (measurableSet_Ioc (a := x - v) (b := x)) x
  have hMG0 := setIntegral_tail_sub_nonneg (μ := A) (ν := B)
    (measurableSet_Ioc (a := x - v) (b := x)) x
  have hMF := setIntegral_tail_sub_le (μ := A) (ν := μ) (measurableSet_Ioc (a := x - v) (b := x)) x
  have hMF0 := setIntegral_tail_sub_nonneg (μ := A) (ν := μ)
    (measurableSet_Ioc (a := x - v) (b := x)) x
  rw [measureReal_Ioc_eq hax] at hMG hMF
  have hPF0 : 0 ≤ ∫ t in Iic (x - v), tail μ (x - t) ∂A :=
    setIntegral_tail_sub_nonneg measurableSet_Iic x
  constructor
  · have : (c + ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂A ≤
        (c + ε) * (tail (μ ∗ A) x - tail A x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  · have : (c - ε) * (tail (μ ∗ A) x - tail A (x - v)) ≤
        (c - ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂A :=
      mul_le_mul_of_nonneg_left (by linarith) hcε
    linarith

/-- **Convolution of tail-equivalent laws ([EKM, Lemma A3.15]).** Let `μ` be subexponential and
let `A, B` be probability measures on `[0, ∞)` with `F̄_A(x) / F̄_μ(x) → c₁ > 0` and
`F̄_B(x) / F̄_μ(x) → c₂ > 0`. Then `F̄_{A∗B}(x) / F̄_μ(x) → c₁ + c₂`. -/
theorem tendsto_tail_conv_div_of_tendsto {A B : Measure ℝ} [IsProbabilityMeasure A]
    [IsProbabilityMeasure B] (h : IsSubexponential μ) (hA0 : A (Iio 0) = 0)
    (hB0 : B (Iio 0) = 0) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hA : Tendsto (fun x => tail A x / tail μ x) atTop (𝓝 c₁))
    (hB : Tendsto (fun x => tail B x / tail μ x) atTop (𝓝 c₂)) :
    Tendsto (fun x => tail (A ∗ B) x / tail μ x) atTop (𝓝 (c₁ + c₂)) := by
  have hF := h.tail_pos
  have hμA := h.tendsto_tail_conv_div hA0 hc₁ hA
  have hv : ∀ ε > 0, ∃ v, 0 ≤ v ∧ ∀ s ≥ v, |tail B s / tail μ s - c₂| < ε := by
    intro ε hε
    obtain ⟨v₀, hv₀⟩ := Metric.tendsto_atTop.1 hB ε hε
    exact ⟨max v₀ 0, le_max_right _ _, fun s hs => hv₀ s ((le_max_left _ _).trans hs)⟩
  rw [tendsto_order]
  constructor
  · intro b hb
    set ε := min c₂ ((c₁ + c₂ - b) / 2) with hε_def
    have hε : 0 < ε := lt_min hc₂ (by linarith)
    have hεc : ε ≤ c₂ := min_le_left _ _
    have hε2 : ε ≤ (c₁ + c₂ - b) / 2 := min_le_right _ _
    obtain ⟨v, hv0, hvG⟩ := hv ε hε
    have hlim : Tendsto (fun x => (c₂ - ε) * (tail (μ ∗ A) x / tail μ x -
        tail A (x - v) / tail μ x) + tail A x / tail μ x) atTop
        (𝓝 ((c₂ - ε) * ((c₁ + 1) - c₁) + c₁)) :=
      ((hμA.sub (h.tendsto_tail_sub_div_of_tendsto hA v)).const_mul _).add hA
    filter_upwards [(tendsto_order.1 hlim).1 b (by nlinarith)] with x hx
    have hb := (conv_bounds' (A := A) h hB0 (by linarith) hε.le hv0 hvG x).2
    have hFx := hF x
    refine hx.trans_le ?_
    rw [le_div_iff₀ hFx]
    calc ((c₂ - ε) * (tail (μ ∗ A) x / tail μ x - tail A (x - v) / tail μ x) +
          tail A x / tail μ x) * tail μ x
        = (c₂ - ε) * (tail (μ ∗ A) x - tail A (x - v)) + tail A x := by
          field_simp
      _ ≤ _ := hb
  · intro b hb
    set ε := (b - (c₁ + c₂)) / 2 with hε_def
    have hε : 0 < ε := by linarith
    obtain ⟨v, hv0, hvG⟩ := hv (min ε c₂) (lt_min hε hc₂)
    have hlim : Tendsto (fun x => (c₂ + min ε c₂) * (tail (μ ∗ A) x / tail μ x -
        tail A x / tail μ x) + tail A (x - v) / tail μ x) atTop
        (𝓝 ((c₂ + min ε c₂) * ((c₁ + 1) - c₁) + c₁)) :=
      ((hμA.sub hA).const_mul _).add (h.tendsto_tail_sub_div_of_tendsto hA v)
    have hm := min_le_left ε c₂
    filter_upwards [(tendsto_order.1 hlim).2 b (by nlinarith)] with x hx
    have hb := (conv_bounds' (A := A) h hB0 (ε := min ε c₂) (by linarith [min_le_right ε c₂])
      (le_min hε.le hc₂.le) hv0 hvG x).1
    have hFx := hF x
    refine lt_of_le_of_lt ?_ hx
    rw [div_le_iff₀ hFx]
    calc tail (A ∗ B) x
        ≤ (c₂ + min ε c₂) * (tail (μ ∗ A) x - tail A x) + tail A (x - v) := hb
      _ = ((c₂ + min ε c₂) * (tail (μ ∗ A) x / tail μ x - tail A x / tail μ x) +
          tail A (x - v) / tail μ x) * tail μ x := by
          field_simp

/-- **Subexponentiality is a property of the tail-equivalence class ([EKM, Lemma A3.15]).**
If `μ` is subexponential and `ν` is a probability measure on `[0, ∞)` with
`F̄_ν(x) / F̄_μ(x) → c > 0`, then `ν` is subexponential. -/
theorem of_tendsto_tail_div {ν : Measure ℝ} [IsProbabilityMeasure ν] (h : IsSubexponential μ)
    (hν0 : ν (Iio 0) = 0) {c : ℝ} (hc : 0 < c)
    (hν : Tendsto (fun x => tail ν x / tail μ x) atTop (𝓝 c)) : IsSubexponential ν := by
  have hpos : ∀ x, 0 < tail ν x := by
    intro t
    have hev : ∀ᶠ x in atTop, 0 < tail ν x := by
      filter_upwards [(tendsto_order.1 hν).1 0 hc] with x hx
      exact (div_pos_iff_of_pos_right (h.tail_pos x)).1 hx
    obtain ⟨s, hs, hts⟩ := (hev.and (eventually_ge_atTop t)).exists
    exact hs.trans_le (tail_antitone hts)
  refine ⟨hν0, hpos, ?_⟩
  have h2 := (h.tendsto_tail_conv_div_of_tendsto hν0 hν0 hc hc hν hν).div hν hc.ne'
  rw [show (c + c) / c = 2 by field_simp; ring] at h2
  refine h2.congr fun x => ?_
  rw [Pi.div_apply, div_div_div_cancel_right₀ (h.tail_pos x).ne']

/-- **Convolution powers of a subexponential law are subexponential.** -/
theorem convPow (h : IsSubexponential μ) {n : ℕ} (hn : 1 ≤ n) :
    IsSubexponential (Subexp.convPow μ n) :=
  h.of_tendsto_tail_div (convPow_Iio_zero h.nonneg n) (by exact_mod_cast hn)
    (h.tendsto_tail_convPow_div hn)

end IsSubexponential

end ExtremeValueTheory
