/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Subexponential distributions

A probability measure `μ` on `[0, ∞)` with tail (survival function) `F̄ x = μ (x, ∞)` is
*subexponential* if `F̄^{*2}(x) / F̄(x) → 2` as `x → ∞`, where `F̄^{*2}` is the tail of the
convolution `μ ∗ μ`, i.e. of the law of `X₁ + X₂` for independent `X₁, X₂ ∼ μ`.

We follow Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events for Insurance and
Finance* (Springer, 1997), §1.3 [EKM], and Foss, Korshunov and Zachary, *An Introduction to
Heavy-Tailed and Subexponential Distributions* (2nd ed., Springer, 2013).

## Conventions

* Measures live on `ℝ`; "concentrated on `[0, ∞)`" is `μ (Iio 0) = 0`.
* `ExtremeValueTheory.tail μ x = μ.real (Ioi x) = (μ (Ioi x)).toReal`.
* Convolution is Mathlib's `MeasureTheory.Measure.conv` (`μ ∗ ν`, the push-forward of
  `μ.prod ν` under addition); `convPow μ n` is the `n`-fold power `μ^{*n}` (`μ^{*0} = δ₀`).
  `map_pi_sum_eq_convPow` identifies it with the law of `X₁ + ⋯ + Xₙ` under the product
  measure `Measure.pi (fun _ : Fin n => μ)`, which is our model for i.i.d. variables.

## Main definitions

* `ExtremeValueTheory.IsSubexponential μ` ([EKM, Definition 1.3.3]).
* `ExtremeValueTheory.convPow μ n`.

## Main results

* `IsSubexponential.of_isRegularlyVarying`: regularly varying tails are subexponential
  ([EKM, Corollary 1.3.2]).
* `IsSubexponential.tendsto_tail_sub_div`: subexponential distributions are long-tailed,
  `F̄(x - y) / F̄(x) → 1` ([EKM, Lemma 1.3.5(a)]).
* `IsSubexponential.tendsto_tail_convPow_div`: `F̄^{*n}(x) / F̄(x) → n` for `n ≥ 1`
  ([EKM, Lemma 1.3.4]); `IsSubexponential.tendsto_measure_sum_div_tail` is the same statement
  for `P(X₁ + ⋯ + Xₙ > x)`.
* `tendsto_measure_max_div_tail`: `P(max(X₁, …, Xₙ) > x) / F̄(x) → n`, and
  `IsSubexponential.tendsto_measure_sum_div_measure_max`: the *single big jump* principle
  `P(X₁ + ⋯ + Xₙ > x) ~ P(max(X₁, …, Xₙ) > x)` ([EKM, Lemma 1.3.1(a) and Lemma 1.3.4]).
* `IsSubexponential.kesten_bound`: Kesten's bound `F̄^{*n}(x) ≤ K (1 + ε)ⁿ F̄(x)`
  ([EKM, Lemma 1.3.5(c)]).

## Proof outline

Everything is driven by the convolution formula `F̄_{μ∗ν}(x) = ∫ F̄_ν(x - t) dμ(t)`
(`Subexp.tail_conv`), split as `∫_{t ≤ a} + ∫_{a < t ≤ x} + F̄_μ(x)` (`Subexp.tail_conv_split`).
The induction step `F̄_ν / F̄_μ → c ⟹ F̄_{μ∗ν} / F̄_μ → c + 1` (`tendsto_tail_conv_div`) uses the
split at `a = x - v` together with long-tailedness, as in [EKM, proof of Lemma 1.3.4].
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

/-- The survival function (tail) `F̄ x = μ (x, ∞)` of a measure `μ` on `ℝ`. -/
noncomputable def tail (μ : Measure ℝ) (x : ℝ) : ℝ := μ.real (Ioi x)

namespace Subexp

variable {μ ν : Measure ℝ}

theorem tail_nonneg (x : ℝ) : 0 ≤ tail μ x := measureReal_nonneg

theorem tail_le_one [IsProbabilityMeasure μ] (x : ℝ) : tail μ x ≤ 1 := measureReal_le_one

theorem tail_antitone [IsFiniteMeasure μ] : Antitone (tail μ) := fun _ _ h =>
  measureReal_mono (Ioi_subset_Ioi h)

theorem tail_measurable [IsFiniteMeasure μ] : Measurable (tail μ) :=
  tail_antitone.measurable

theorem tail_of_neg [IsProbabilityMeasure μ] (h0 : μ (Iio 0) = 0) {x : ℝ} (hx : x < 0) :
    tail μ x = 1 := by
  apply le_antisymm (tail_le_one x)
  have h1 : μ.real (Ici 0) = 1 := by
    rw [← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio, measureReal_def, h0]; simp
  rw [← h1]; exact measureReal_mono (fun t (ht : 0 ≤ t) => (show x < t by linarith))

theorem tendsto_tail_atTop [IsFiniteMeasure μ] : Tendsto (tail μ) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun x : ℝ => Ioi x)
    (fun _ => measurableSet_Ioi.nullMeasurableSet) (fun _ _ h => Ioi_subset_Ioi h)
    ⟨0, measure_ne_top _ _⟩
  have he : (⋂ x : ℝ, Ioi x) = ∅ := by
    ext t; simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨t, le_rfl⟩
  rw [he, measure_empty] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at this
  exact this

theorem measureReal_Ioc_eq [IsFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    μ.real (Ioc a b) = tail μ a - tail μ b := by
  have : Ioi a = Ioc a b ∪ Ioi b := (Ioc_union_Ioi_eq_Ioi hab).symm
  rw [tail, tail, this, measureReal_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi]; ring

theorem measureReal_Iic_eq [IsProbabilityMeasure μ] (a : ℝ) : μ.real (Iic a) = 1 - tail μ a := by
  rw [← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi]; rfl

/-- The convolution formula `(μ ∗ ν)(s) = ∫ ν (s - a) dμ(a)`. -/
theorem conv_apply [SFinite ν] {s : Set ℝ} (hs : MeasurableSet s) :
    (μ ∗ ν) s = ∫⁻ a, ν ((fun b => a + b) ⁻¹' s) ∂μ := by
  rw [Measure.conv, Measure.map_apply measurable_add hs, Measure.prod_apply (measurable_add hs)]
  rfl

theorem tail_conv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (x : ℝ) :
    tail (μ ∗ ν) x = ∫ a, tail ν (x - a) ∂μ := by
  rw [tail, measureReal_def, conv_apply measurableSet_Ioi,
    ← integral_toReal _ (Eventually.of_forall fun _ => measure_lt_top _ _)]
  · refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    have : (fun b => a + b) ⁻¹' Ioi x = Ioi (x - a) := by
      ext b; simp only [mem_preimage, mem_Ioi]; constructor <;> intro <;> linarith
    simp only [this, tail, measureReal_def]
  · exact (measurable_measure_prodMk_left (measurable_add measurableSet_Ioi)).aemeasurable

theorem conv_Iio_zero [SFinite ν] (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0) :
    (μ ∗ ν) (Iio 0) = 0 := by
  rw [conv_apply measurableSet_Iio]
  have hae : ∀ᵐ a ∂μ, 0 ≤ a := by
    rw [ae_iff]; simp only [not_le]; exact hμ
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hae] with a ha
  refine measure_mono_null (fun b (hb : a + b < 0) => (show b < 0 by linarith)) hν

section Split

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem integrable_tail_sub (x : ℝ) : Integrable (fun t => tail ν (x - t)) μ := by
  refine Integrable.of_bound ((tail_measurable.comp (measurable_const.sub measurable_id)
    ).aestronglyMeasurable) 1 (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tail_nonneg _)]; exact tail_le_one _

/-- Splitting the convolution integral at `a ≤ x`:
`F̄_{μ∗ν}(x) = ∫_{t ≤ a} G(x - t) dμ + ∫_{a < t ≤ x} G(x - t) dμ + F̄_μ(x)`, `G = F̄_ν`. -/
theorem tail_conv_split (hν : ν (Iio 0) = 0) {a x : ℝ} (hax : a ≤ x) :
    tail (μ ∗ ν) x = (∫ t in Iic a, tail ν (x - t) ∂μ) + (∫ t in Ioc a x, tail ν (x - t) ∂μ)
      + tail μ x := by
  have hi := integrable_tail_sub (μ := μ) (ν := ν) x
  rw [tail_conv, ← integral_add_compl (measurableSet_Iic (a := x)) hi, compl_Iic,
    ← Iic_union_Ioc_eq_Iic hax, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      hi.integrableOn hi.integrableOn]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (1 : ℝ)), setIntegral_const,
    smul_eq_mul, mul_one, tail]
  intro t (ht : x < t)
  exact tail_of_neg hν (by linarith)

theorem setIntegral_tail_sub_le {s : Set ℝ} (hs : MeasurableSet s) (x : ℝ) :
    ∫ t in s, tail ν (x - t) ∂μ ≤ μ.real s := by
  have := setIntegral_mono_on (μ := μ) (integrable_tail_sub (μ := μ) (ν := ν) x).integrableOn
    (integrableOn_const (C := (1 : ℝ))) hs (fun t _ => tail_le_one (x - t))
  rwa [setIntegral_const, smul_eq_mul, mul_one] at this

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem setIntegral_tail_sub_nonneg {s : Set ℝ} (hs : MeasurableSet s) (x : ℝ) :
    0 ≤ ∫ t in s, tail ν (x - t) ∂μ :=
  setIntegral_nonneg hs fun _ _ => tail_nonneg _

/-- Lower bound for `F̄^{*2}`: for `a ≤ x`,
`F̄^{*2}(x) ≥ F̄(x) (1 - F̄(a)) + F̄(x - a) (F̄(a) - F̄(x)) + F̄(x)`. -/
theorem tail_conv_self_ge (h0 : μ (Iio 0) = 0) {a x : ℝ} (hax : a ≤ x) :
    tail μ x * (1 - tail μ a) + tail μ (x - a) * (tail μ a - tail μ x) + tail μ x ≤
      tail (μ ∗ μ) x := by
  rw [tail_conv_split h0 hax]
  have hae : ∀ᵐ t ∂μ, 0 ≤ t := by
    rw [ae_iff]; simp only [not_le]; exact h0
  have hi := integrable_tail_sub (μ := μ) (ν := μ) x
  have h1 : tail μ x * (1 - tail μ a) ≤ ∫ t in Iic a, tail μ (x - t) ∂μ := by
    have := setIntegral_mono_on_ae (μ := μ) (s := Iic a) (integrableOn_const (C := tail μ x))
      hi.integrableOn measurableSet_Iic
      (by filter_upwards [hae] with t ht _ using tail_antitone (by linarith))
    rwa [setIntegral_const, smul_eq_mul, measureReal_Iic_eq, mul_comm] at this
  have h2 : tail μ (x - a) * (tail μ a - tail μ x) ≤ ∫ t in Ioc a x, tail μ (x - t) ∂μ := by
    have := setIntegral_mono_on (μ := μ) (s := Ioc a x) (integrableOn_const (C := tail μ (x - a)))
      hi.integrableOn measurableSet_Ioc (fun t ht => tail_antitone (by linarith [ht.1]))
    rwa [setIntegral_const, smul_eq_mul, measureReal_Ioc_eq hax, mul_comm] at this
  linarith

end Split

/-- The `n`-fold convolution power `μ^{*n}` (with `μ^{*0} = δ₀`), i.e. the law of
`X₁ + ⋯ + Xₙ` for i.i.d. `Xᵢ ∼ μ` (see `ExtremeValueTheory.map_pi_sum_eq_convPow`). -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => μ ∗ convPow μ n

@[simp] theorem convPow_zero (μ : Measure ℝ) : convPow μ 0 = Measure.dirac 0 := rfl

theorem convPow_succ (μ : Measure ℝ) (n : ℕ) : convPow μ (n + 1) = μ ∗ convPow μ n := rfl

/-- The convolution powers of a point mass: `δₓ^{*n} = δ_{n x}`, the law of a sum of `n` copies
of the constant `x`. -/
theorem convPow_dirac (x : ℝ) (n : ℕ) : convPow (Measure.dirac x) n = Measure.dirac (n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [convPow_succ, ih, Measure.dirac_conv_dirac]
    push_cast; ring_nf

instance isProbabilityMeasure_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; infer_instance

theorem convPow_one (μ : Measure ℝ) [SFinite μ] : convPow μ 1 = μ := by
  rw [convPow_succ, convPow_zero, Measure.conv_dirac_zero]

theorem convPow_Iio_zero [IsProbabilityMeasure μ] (h0 : μ (Iio 0) = 0) (n : ℕ) :
    convPow μ n (Iio 0) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [convPow_succ]; exact conv_Iio_zero h0 ih

end Subexp

open Subexp

/-- A probability measure `μ` on `ℝ` is **subexponential** ([EKM, Definition 1.3.3]) if it is
concentrated on `[0, ∞)`, its tail `F̄ x = μ (x, ∞)` is positive everywhere, and
`F̄^{*2}(x) / F̄(x) → 2` as `x → ∞`, where `F̄^{*2}` is the tail of the convolution `μ ∗ μ`
(the law of `X₁ + X₂` for independent `X₁, X₂ ∼ μ`). -/
structure IsSubexponential (μ : Measure ℝ) : Prop where
  nonneg : μ (Iio 0) = 0
  tail_pos : ∀ x, 0 < tail μ x
  tendsto_tail_conv_self : Tendsto (fun x => tail (μ ∗ μ) x / tail μ x) atTop (𝓝 2)

namespace IsSubexponential

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ]

private theorem tendsto_tail_sub_div_of_nonneg (h : IsSubexponential μ) {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun x => tail μ (x - y) / tail μ x) atTop (𝓝 1) := by
  have hF := h.tail_pos
  have hlim : Tendsto (fun x => (tail (μ ∗ μ) x / tail μ x - 2 + tail μ y) /
      (tail μ y - tail μ x)) atTop (𝓝 1) := by
    have := ((h.tendsto_tail_conv_self.sub_const 2).add_const (tail μ y)).div
      ((tendsto_tail_atTop (μ := μ)).const_sub (tail μ y)) (by simpa using (hF y).ne')
    simp only [sub_self, zero_add, sub_zero, div_self (hF y).ne'] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun x =>
      (one_le_div (hF x)).2 (tail_antitone (by linarith))
  · filter_upwards [(tendsto_order.1 (tendsto_tail_atTop (μ := μ))).2 _ (hF y),
      eventually_ge_atTop y] with x hx hyx
    have hLB := tail_conv_self_ge h.nonneg hyx
    have hFx := hF x
    rw [le_div_iff₀ (by linarith), div_mul_eq_mul_div, div_le_iff₀ hFx]
    rw [div_sub' hFx.ne', div_add' _ _ _ hFx.ne', div_mul_eq_mul_div, le_div_iff₀ hFx]
    nlinarith

/-- **Subexponential distributions are long-tailed** ([EKM, Lemma 1.3.5(a)]):
`F̄(x - y) / F̄(x) → 1` as `x → ∞`, for every `y`. -/
theorem tendsto_tail_sub_div (h : IsSubexponential μ) (y : ℝ) :
    Tendsto (fun x => tail μ (x - y) / tail μ x) atTop (𝓝 1) := by
  rcases le_total 0 y with hy | hy
  · exact h.tendsto_tail_sub_div_of_nonneg hy
  · have h1 := ((h.tendsto_tail_sub_div_of_nonneg (y := -y) (by linarith)).inv₀
      one_ne_zero).comp (tendsto_atTop_add_const_right _ (-y) tendsto_id)
    simp only [inv_one] at h1
    refine h1.congr fun x => ?_
    simp only [Function.comp_apply, id, inv_div, sub_neg_eq_add]
    ring_nf

/-- The two-sided estimate behind the induction step of [EKM, Lemma 1.3.4]. -/
private theorem conv_bounds [IsProbabilityMeasure ν] (h : IsSubexponential μ)
    (hν : ν (Iio 0) = 0) {c ε v : ℝ} (hcε : 0 ≤ c - ε) (hε : 0 ≤ ε) (hv : 0 ≤ v)
    (hG : ∀ s ≥ v, |tail ν s / tail μ s - c| < ε) (x : ℝ) :
    tail (μ ∗ ν) x ≤ (c + ε) * (tail (μ ∗ μ) x - tail μ x) + tail μ (x - v) ∧
      (c - ε) * (tail (μ ∗ μ) x - tail μ (x - v)) + tail μ x ≤ tail (μ ∗ ν) x := by
  have hax : x - v ≤ x := by linarith
  have hT := tail_conv_split (μ := μ) hν hax
  have hS := tail_conv_split (μ := μ) h.nonneg hax
  have hiG := (integrable_tail_sub (μ := μ) (ν := ν) x).integrableOn (s := Iic (x - v))
  have hiF := (integrable_tail_sub (μ := μ) (ν := μ) x).integrableOn (s := Iic (x - v))
  have hpt : ∀ t ∈ Iic (x - v), (c - ε) * tail μ (x - t) ≤ tail ν (x - t) ∧
      tail ν (x - t) ≤ (c + ε) * tail μ (x - t) := by
    intro t ht
    have hs : v ≤ x - t := by have : t ≤ x - v := ht; linarith
    have h1 := hG _ hs
    have hFp := h.tail_pos (x - t)
    rw [abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, lt_div_iff₀ hFp, div_lt_iff₀ hFp] at h1
    constructor <;> nlinarith
  have hup : ∫ t in Iic (x - v), tail ν (x - t) ∂μ ≤
      (c + ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hiG (hiF.const_mul _) measurableSet_Iic fun t ht => (hpt t ht).2
  have hlo : (c - ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂μ ≤
      ∫ t in Iic (x - v), tail ν (x - t) ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hiF.const_mul _) hiG measurableSet_Iic fun t ht => (hpt t ht).1
  have hMG := setIntegral_tail_sub_le (μ := μ) (ν := ν) (measurableSet_Ioc (a := x - v) (b := x)) x
  have hMG0 := setIntegral_tail_sub_nonneg (μ := μ) (ν := ν)
    (measurableSet_Ioc (a := x - v) (b := x)) x
  have hMF := setIntegral_tail_sub_le (μ := μ) (ν := μ) (measurableSet_Ioc (a := x - v) (b := x)) x
  have hMF0 := setIntegral_tail_sub_nonneg (μ := μ) (ν := μ)
    (measurableSet_Ioc (a := x - v) (b := x)) x
  rw [measureReal_Ioc_eq hax] at hMG hMF
  have hPF0 : 0 ≤ ∫ t in Iic (x - v), tail μ (x - t) ∂μ :=
    setIntegral_tail_sub_nonneg measurableSet_Iic x
  constructor
  · have : (c + ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂μ ≤
        (c + ε) * (tail (μ ∗ μ) x - tail μ x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  · have : (c - ε) * (tail (μ ∗ μ) x - tail μ (x - v)) ≤
        (c - ε) * ∫ t in Iic (x - v), tail μ (x - t) ∂μ :=
      mul_le_mul_of_nonneg_left (by linarith) hcε
    linarith

/-- **Induction step of [EKM, Lemma 1.3.4].** If `μ` is subexponential and `ν` is a probability
measure on `[0, ∞)` with `F̄_ν(x) / F̄_μ(x) → c > 0`, then `F̄_{μ∗ν}(x) / F̄_μ(x) → c + 1`. -/
theorem tendsto_tail_conv_div [IsProbabilityMeasure ν] (h : IsSubexponential μ)
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 < c)
    (hνc : Tendsto (fun x => tail ν x / tail μ x) atTop (𝓝 c)) :
    Tendsto (fun x => tail (μ ∗ ν) x / tail μ x) atTop (𝓝 (c + 1)) := by
  have hF := h.tail_pos
  have hS := h.tendsto_tail_conv_self
  -- choice of the cut-off `v` for a given `ε`
  have hv : ∀ ε > 0, ∃ v, 0 ≤ v ∧ ∀ s ≥ v, |tail ν s / tail μ s - c| < ε := by
    intro ε hε
    obtain ⟨v₀, hv₀⟩ := Metric.tendsto_atTop.1 hνc ε hε
    exact ⟨max v₀ 0, le_max_right _ _, fun s hs => hv₀ s ((le_max_left _ _).trans hs)⟩
  rw [tendsto_order]
  constructor
  · intro b hb
    set ε := min c ((c + 1 - b) / 2) with hε_def
    have hε : 0 < ε := lt_min hc (by linarith)
    have hεc : ε ≤ c := min_le_left _ _
    have hε2 : ε ≤ (c + 1 - b) / 2 := min_le_right _ _
    obtain ⟨v, hv0, hvG⟩ := hv ε hε
    have hlim : Tendsto (fun x => (c - ε) * (tail (μ ∗ μ) x / tail μ x -
        tail μ (x - v) / tail μ x) + 1) atTop (𝓝 ((c - ε) * (2 - 1) + 1)) :=
      ((hS.sub (h.tendsto_tail_sub_div v)).const_mul _).add_const 1
    filter_upwards [(tendsto_order.1 hlim).1 b (by nlinarith)]
      with x hx
    have hb := (conv_bounds h hν (by linarith) hε.le hv0 hvG x).2
    have hFx := hF x
    refine hx.trans_le ?_
    rw [le_div_iff₀ hFx]
    calc ((c - ε) * (tail (μ ∗ μ) x / tail μ x - tail μ (x - v) / tail μ x) + 1) * tail μ x
        = (c - ε) * (tail (μ ∗ μ) x - tail μ (x - v)) + tail μ x := by
          field_simp
      _ ≤ _ := hb
  · intro b hb
    set ε := (b - (c + 1)) / 2 with hε_def
    have hε : 0 < ε := by linarith
    obtain ⟨v, hv0, hvG⟩ := hv (min ε c) (lt_min hε hc)
    have hvG' : ∀ s ≥ v, |tail ν s / tail μ s - c| < ε := fun s hs =>
      (hvG s hs).trans_le (min_le_left _ _)
    have hlim : Tendsto (fun x => (c + ε) * (tail (μ ∗ μ) x / tail μ x - 1) +
        tail μ (x - v) / tail μ x) atTop (𝓝 ((c + ε) * (2 - 1) + 1)) :=
      ((hS.sub_const 1).const_mul _).add (h.tendsto_tail_sub_div v)
    filter_upwards [(tendsto_order.1 hlim).2 b (by nlinarith)]
      with x hx
    have hb := (conv_bounds h hν (ε := min ε c) (by linarith [min_le_right ε c])
      (le_min hε.le hc.le) hv0 hvG x).1
    have hFx := hF x
    refine lt_of_le_of_lt ?_ hx
    rw [div_le_iff₀ hFx]
    calc tail (μ ∗ ν) x ≤ (c + min ε c) * (tail (μ ∗ μ) x - tail μ x) + tail μ (x - v) := hb
      _ ≤ (c + ε) * (tail (μ ∗ μ) x - tail μ x) + tail μ (x - v) := by
          have : 0 ≤ tail (μ ∗ μ) x - tail μ x := by
            have := tail_conv_split (μ := μ) h.nonneg (le_refl x)
            have := setIntegral_tail_sub_nonneg (μ := μ) (ν := μ) (measurableSet_Iic (a := x)) x
            have := setIntegral_tail_sub_nonneg (μ := μ) (ν := μ)
              (measurableSet_Ioc (a := x) (b := x)) x
            linarith
          have := min_le_left ε c
          nlinarith
      _ = ((c + ε) * (tail (μ ∗ μ) x / tail μ x - 1) + tail μ (x - v) / tail μ x) * tail μ x := by
          field_simp

/-- **[EKM, Lemma 1.3.4].** If `μ` is subexponential, then `F̄^{*n}(x) / F̄(x) → n` for every
`n ≥ 1`, where `F̄^{*n}` is the tail of the `n`-fold convolution `μ^{*n}`. -/
theorem tendsto_tail_convPow_div (h : IsSubexponential μ) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun x => tail (convPow μ n) x / tail μ x) atTop (𝓝 n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [convPow_one, Nat.cast_one]
    exact tendsto_const_nhds.congr fun x => (div_self (h.tail_pos x).ne').symm
  | succ n hn ih =>
    rw [convPow_succ, Nat.cast_succ]
    exact h.tendsto_tail_conv_div (convPow_Iio_zero h.nonneg n) (by exact_mod_cast hn) ih

/-- If `F̄_ν ≤ a F̄_μ` everywhere, then `F̄_{μ∗ν}(x) ≤ a (F̄^{*2}(x) - F̄(x)) + F̄(x)`. -/
private theorem tail_conv_le_of_le [IsProbabilityMeasure ν] (h : IsSubexponential μ)
    (hν : ν (Iio 0) = 0) {a : ℝ} (hle : ∀ s, tail ν s ≤ a * tail μ s) (x : ℝ) :
    tail (μ ∗ ν) x ≤ a * (tail (μ ∗ μ) x - tail μ x) + tail μ x := by
  have hT := tail_conv_split (μ := μ) hν (le_refl x)
  have hS := tail_conv_split (μ := μ) h.nonneg (le_refl x)
  simp only [Ioc_self, Measure.restrict_empty, integral_zero_measure, add_zero] at hT hS
  have : ∫ t in Iic x, tail ν (x - t) ∂μ ≤ a * ∫ t in Iic x, tail μ (x - t) ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (integrable_tail_sub (μ := μ) (ν := ν) x).integrableOn
      ((integrable_tail_sub (μ := μ) (ν := μ) x).integrableOn.const_mul _) measurableSet_Iic
      fun t _ => hle _
  rw [hT, hS, add_sub_cancel_right]
  linarith

/-- **Kesten's bound ([EKM, Lemma 1.3.5(c)]).** If `μ` is subexponential, then for every
`ε > 0` there is `K` such that `F̄^{*n}(x) ≤ K (1 + ε)ⁿ F̄(x)` for all `n` and all `x`. -/
theorem kesten_bound (h : IsSubexponential μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (n : ℕ) (x : ℝ), tail (convPow μ n) x ≤ K * (1 + ε) ^ n * tail μ x := by
  have hF := h.tail_pos
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    ((tendsto_order.1 h.tendsto_tail_conv_self).2 (2 + ε) (by linarith))
  set A := 1 + 1 / tail μ x₀ with hA_def
  have hA : 0 ≤ A := by have := hF x₀; positivity
  set K := 1 + A / ε with hK_def
  have hAε : 0 ≤ A / ε := div_nonneg hA hε.le
  have key : ∀ n : ℕ, ∀ x, tail (convPow μ n) x ≤ (K * (1 + ε) ^ n - A / ε) * tail μ x := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [pow_zero, mul_one, hK_def, add_sub_cancel_right, one_mul, convPow_zero]
      rcases lt_or_ge x 0 with hx | hx
      · rw [tail_of_neg h.nonneg hx]; exact tail_le_one x
      · have : tail (Measure.dirac (0 : ℝ)) x = 0 := by
          simp [tail, measureReal_def, Measure.dirac_apply' _ measurableSet_Ioi, not_lt.2 hx]
        rw [this]; exact tail_nonneg x
    | succ n ih =>
      intro x
      have hpow : 1 ≤ (1 + ε) ^ n := one_le_pow₀ (by linarith)
      have ha : 1 ≤ K * (1 + ε) ^ n - A / ε := by
        have : K ≤ K * (1 + ε) ^ n := le_mul_of_one_le_right (by linarith) hpow
        linarith
      have hb := tail_conv_le_of_le h (convPow_Iio_zero h.nonneg n) ih x
      rw [convPow_succ]
      have hFx := hF x
      have hgoal : (K * (1 + ε) ^ (n + 1) - A / ε) =
          (K * (1 + ε) ^ n - A / ε) * (1 + ε) + A := by
        rw [pow_succ]; field_simp; ring
      rw [hgoal]
      rcases le_or_gt x₀ x with hx | hx
      · have h2 := hx₀ x hx
        rw [div_lt_iff₀ hFx] at h2
        have : (K * (1 + ε) ^ n - A / ε) * (tail (μ ∗ μ) x - tail μ x) ≤
            (K * (1 + ε) ^ n - A / ε) * ((1 + ε) * tail μ x) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have : tail μ x ≤ A * tail μ x := le_mul_of_one_le_left hFx.le (by
          have := hF x₀; rw [hA_def]; have : 0 ≤ 1 / tail μ x₀ := by positivity
          linarith)
        nlinarith
      · have h1 : tail (μ ∗ convPow μ n) x ≤ 1 := tail_le_one x
        have h2 : 1 ≤ A * tail μ x := by
          have hx0 := hF x₀
          have hmono : tail μ x₀ ≤ tail μ x := tail_antitone hx.le
          have : 1 ≤ 1 / tail μ x₀ * tail μ x := by
            rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hx0, one_mul]; exact hmono
          have : 0 ≤ tail μ x := hFx.le
          nlinarith
        have : 0 ≤ (K * (1 + ε) ^ n - A / ε) * (1 + ε) * tail μ x := by
          have := mul_nonneg (by linarith : (0 : ℝ) ≤ K * (1 + ε) ^ n - A / ε) (by linarith :
            (0 : ℝ) ≤ 1 + ε)
          exact mul_nonneg this hFx.le
        nlinarith
  refine ⟨K, fun n x => (key n x).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (tail_nonneg x)

/-- `F̄^{*2}(x) ≤ 2 F̄(c x) + F̄((1 - c) x)²`: if `X₁ + X₂ > x` then `X₁ > c x`, or `X₂ > c x`,
or both `X₁, X₂ > (1 - c) x`. -/
private theorem tail_conv_self_le (c x : ℝ) :
    tail (μ ∗ μ) x ≤ 2 * tail μ (c * x) + tail μ ((1 - c) * x) ^ 2 := by
  rw [tail, Measure.conv, map_measureReal_apply measurable_add measurableSet_Ioi]
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ioi x ⊆
      (Ioi (c * x) ×ˢ univ ∪ univ ×ˢ Ioi (c * x)) ∪
        Ioi ((1 - c) * x) ×ˢ Ioi ((1 - c) * x) := by
    intro p (hp : x < p.1 + p.2)
    by_contra hn
    simp only [mem_union, mem_prod, mem_Ioi, mem_univ, and_true, true_and, not_or,
      not_and_or, not_lt] at hn
    obtain ⟨⟨h1, h2⟩, h3 | h3⟩ := hn <;> nlinarith
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  refine (add_le_add_left (measureReal_union_le _ _) _).trans ?_
  simp only [measureReal_prod_prod, probReal_univ, mul_one, one_mul]
  rw [tail, tail]; nlinarith

/-- **Regularly varying tails are subexponential ([EKM, Corollary 1.3.2]).** If `μ` is a
probability measure on `[0, ∞)` whose tail `F̄` is regularly varying with index `-α`, then `μ`
is subexponential. (Necessarily `α ≥ 0`, since `F̄` is bounded and antitone; no assumption on
`α` is needed.) -/
theorem of_isRegularlyVarying (h0 : μ (Iio 0) = 0) {α : ℝ}
    (hRV : IsRegularlyVarying (tail μ) (-α)) : IsSubexponential μ := by
  have hF : ∀ x, 0 < tail μ x := fun t => by
    obtain ⟨s, hs, hts⟩ := (hRV.1.and (eventually_ge_atTop t)).exists
    exact hs.trans_le (tail_antitone hts)
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
  · intro b hb
    -- choose `c ∈ (0, 1)` close to `1` with `2 c ^ (-α) < b`
    have hcont : Tendsto (fun c : ℝ => 2 * c ^ (-α)) (𝓝[<] 1) (𝓝 (2 * 1 ^ (-α))) :=
      ((continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)).tendsto.const_mul 2).mono_left
        nhdsWithin_le_nhds
    rw [one_rpow, mul_one] at hcont
    obtain ⟨c, hcb, hc⟩ :=
      ((tendsto_order.1 hcont).2 b hb |>.and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
    have hc0 : 0 < c := hc.1
    have hc1 : 0 < 1 - c := by linarith [hc.2]
    have hlim : Tendsto (fun x => 2 * (tail μ (c * x) / tail μ x) +
        tail μ ((1 - c) * x) / tail μ x * tail μ ((1 - c) * x)) atTop
        (𝓝 (2 * c ^ (-α) + (1 - c) ^ (-α) * 0)) :=
      ((hRV.2 c hc0).const_mul 2).add ((hRV.2 (1 - c) hc1).mul
        ((tendsto_tail_atTop (μ := μ)).comp (tendsto_id.const_mul_atTop hc1)))
    rw [mul_zero, add_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).2 b hcb] with x hx
    refine lt_of_le_of_lt ?_ hx
    have := tail_conv_self_le (μ := μ) c x
    have hFx := hF x
    rw [div_le_iff₀ hFx]
    calc tail (μ ∗ μ) x ≤ 2 * tail μ (c * x) + tail μ ((1 - c) * x) ^ 2 := this
      _ = _ := by field_simp

end IsSubexponential

section IID

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The law of `X₁ + ⋯ + Xₙ` under the product measure `μ^{⊗n}` is the convolution power
`μ^{*n}`. -/
theorem map_pi_sum_eq_convPow (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ).map (fun ω => ∑ i, ω i) = convPow μ n := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Measure.map_const, measure_univ, one_smul,
      convPow_zero]
  | succ n ih =>
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have hsum : (fun ω : Fin (n + 1) → ℝ => ∑ i, ω i) =
        ((fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (id : ℝ → ℝ) (fun ω : Fin n → ℝ => ∑ i, ω i)) ∘
          MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 := by
      funext ω
      simp [Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
    have hms : Measurable fun ω : Fin n → ℝ => ∑ i, ω i :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    rw [hsum, ← Measure.map_map (measurable_add.comp (measurable_id.prodMap hms))
      he.measurable, he.map_eq, ← Measure.map_map measurable_add (measurable_id.prodMap hms),
      ← Measure.map_prod_map _ _ measurable_id hms, Measure.map_id, ih, convPow_succ]
    rfl

/-- Tail of the maximum of `n` i.i.d. variables: `P(max(X₁, …, Xₙ) > x) / F̄(x) → n`
([EKM, proof of Lemma 1.3.1]). Here `X₁, …, Xₙ` are the coordinates under `μ^{⊗n}`. -/
theorem tendsto_measure_max_div_tail (hpos : ∀ x, 0 < tail μ x) (n : ℕ) :
    Tendsto (fun x => (Measure.pi fun _ : Fin n => μ).real {ω | ∃ i, x < ω i} / tail μ x)
      atTop (𝓝 n) := by
  have hset : ∀ x : ℝ, {ω : Fin n → ℝ | ∃ i, x < ω i} = (univ.pi fun _ => Iic x)ᶜ := by
    intro x; ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_univ_pi, mem_Iic, not_forall, not_le]
  have hval : ∀ x, (Measure.pi fun _ : Fin n => μ).real {ω | ∃ i, x < ω i} / tail μ x =
      ∑ i ∈ Finset.range n, (1 - tail μ x) ^ i := by
    intro x
    rw [hset, probReal_compl_eq_one_sub (MeasurableSet.univ_pi fun _ => measurableSet_Iic),
      measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    simp only [← measureReal_def, measureReal_Iic_eq, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [div_eq_iff (hpos x).ne']
    have := geom_sum_mul (1 - tail μ x) n
    linarith
  simp_rw [hval]
  have : Tendsto (fun x => ∑ i ∈ Finset.range n, (1 - tail μ x) ^ i) atTop
      (𝓝 (∑ i ∈ Finset.range n, (1 - 0 : ℝ) ^ i)) :=
    tendsto_finsetSum _ fun i _ => ((tendsto_tail_atTop (μ := μ)).const_sub 1).pow i
  simpa using this

namespace IsSubexponential

/-- **[EKM, Lemma 1.3.4], random-variable form.** For i.i.d. `X₁, …, Xₙ ∼ μ` with `μ`
subexponential (the coordinates under `μ^{⊗n}`), `P(X₁ + ⋯ + Xₙ > x) / F̄(x) → n`. -/
theorem tendsto_measure_sum_div_tail (h : IsSubexponential μ) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun x => (Measure.pi fun _ : Fin n => μ).real {ω | x < ∑ i, ω i} / tail μ x)
      atTop (𝓝 n) := by
  refine (h.tendsto_tail_convPow_div hn).congr fun x => ?_
  rw [← map_pi_sum_eq_convPow, tail, map_measureReal_apply
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurableSet_Ioi]
  rfl

/-- **Single big jump principle ([EKM, Lemma 1.3.1(a)] / Lemma 1.3.4).** For i.i.d.
`X₁, …, Xₙ ∼ μ` with `μ` subexponential and `n ≥ 1`,
`P(X₁ + ⋯ + Xₙ > x) / P(max(X₁, …, Xₙ) > x) → 1`. -/
theorem tendsto_measure_sum_div_measure_max (h : IsSubexponential μ) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun x => (Measure.pi fun _ : Fin n => μ).real {ω | x < ∑ i, ω i} /
      (Measure.pi fun _ : Fin n => μ).real {ω | ∃ i, x < ω i}) atTop (𝓝 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have := (h.tendsto_measure_sum_div_tail hn).div
    (tendsto_measure_max_div_tail h.tail_pos n) hn0
  rw [div_self hn0] at this
  refine this.congr fun x => ?_
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (h.tail_pos x).ne']

end IsSubexponential

end IID

end ExtremeValueTheory
