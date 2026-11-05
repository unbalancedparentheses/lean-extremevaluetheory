/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Representation
import ExtremeValueTheory.RegularVariation.UniformConvergenceTails

/-!
# The representation theorem for regularly varying functions of index `ρ`

`ExtremeValueTheory.RegularVariation.Representation` proves the representation theorem ([BGT,
Theorem 1.3.1]) for slowly varying functions on all of `ℝ`. This file states it for every index
`ρ`, for functions measurable near `∞`: `f` is regularly varying of index `ρ` if and only if
`f x = c x * exp (∫ t in a..x, r t / t)` for `x ≥ a`, with `c x → c₀ ∈ (0, ∞)` and `r x → ρ`.

## Main results

* `IsRegularlyVarying.of_representation`: (⇐), for arbitrary `f`, `c`, `r`.
* `IsRegularlyVarying.exists_representation`: (⇒), for `f` measurable near `∞`, with `r` bounded on
  `[a, ∞)`.
* `isRegularlyVarying_iff_exists_representation`: the equivalence.

Here [BGT] is Bingham, Goldie and Teugels, *Regular Variation* (Cambridge University Press, 1987).
-/

open Filter Topology Set Real MeasureTheory intervalIntegral

namespace ExtremeValueTheory

variable {f : ℝ → ℝ} {ρ : ℝ}

/-- `t⁻¹` is interval integrable between positive points. -/
private lemma intervalIntegrable_inv_of_pos' {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun t : ℝ => t⁻¹) volume u v :=
  intervalIntegrable_inv (fun _ ht => ((lt_min hu hv).trans_le ht.1).ne') continuousOn_id

/-- `∫ t in a..x, (ε t + ρ) / t = ∫ t in a..x, ε t / t + ρ log (x / a)`, for positive `a ≤ x`. -/
private lemma integral_add_const_div {ε : ℝ → ℝ} {a x : ℝ} (ρ : ℝ) (ha : 0 < a) (hx : a ≤ x)
    (hint : IntervalIntegrable (fun t => ε t / t) volume a x) :
    IntervalIntegrable (fun t => (ε t + ρ) / t) volume a x ∧
      ∫ t in a..x, (ε t + ρ) / t = (∫ t in a..x, ε t / t) + ρ * log (x / a) := by
  have hx0 : 0 < x := ha.trans_le hx
  have hinv := (intervalIntegrable_inv_of_pos' ha hx0).const_mul ρ
  have heq : (fun t => (ε t + ρ) / t) = fun t => ε t / t + ρ * t⁻¹ := by
    funext t
    rw [add_div, div_eq_mul_inv ρ]
  rw [heq]
  refine ⟨hint.add hinv, ?_⟩
  rw [integral_add hint hinv, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hx0]

/-- **Representation theorem for index `ρ`**, direction (⇐) ([BGT, Theorem 1.3.1]): if
`f x = c x * exp (∫ t in a..x, r t / t)` for `x ≥ a > 0`, where `c x → c₀ > 0`, `r x → ρ` and the
integrals exist, then `f` is regularly varying with index `ρ`. No measurability is assumed. -/
theorem IsRegularlyVarying.of_representation {c r : ℝ → ℝ} {a c₀ : ℝ} (ha : 0 < a) (hc₀ : 0 < c₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hr : Tendsto r atTop (𝓝 ρ))
    (hint : ∀ x ≥ a, IntervalIntegrable (fun t => r t / t) volume a x)
    (hf : ∀ x ≥ a, f x = c x * exp (∫ t in a..x, r t / t)) : IsRegularlyVarying f ρ := by
  have hεint : ∀ x ≥ a, IntervalIntegrable (fun t => (r t - ρ) / t) volume a x := fun x hx =>
    (integral_add_const_div (ε := r) (-ρ) ha hx (hint x hx)).1
  have hL : IsSlowlyVarying fun x => f x * x ^ (-ρ) := by
    refine IsSlowlyVarying.of_representation (c := fun x => c x * a ^ (-ρ)) (a := a)
      (ε := fun t => r t - ρ) (mul_pos hc₀ (rpow_pos_of_pos ha _)) (hc.mul_const _)
      (by simpa using hr.sub_const ρ) hεint fun x hx => ?_
    have hx0 : 0 < x := ha.trans_le hx
    have h := (integral_add_const_div (ε := r) (-ρ) ha hx (hint x hx)).2
    have e : ∫ t in a..x, (r t - ρ) / t = (∫ t in a..x, r t / t) + -ρ * log (x / a) := by
      simpa only [sub_eq_add_neg] using h
    rw [e, exp_add, hf x hx, mul_comm (-ρ), ← rpow_def_of_pos (div_pos hx0 ha),
      div_rpow hx0.le ha.le]
    have := (rpow_pos_of_pos ha (-ρ)).ne'
    field_simp
  have := hL.isRegularlyVarying.mul (IsRegularlyVarying.rpow_id ρ)
  rw [zero_add] at this
  refine this.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [mul_assoc, ← rpow_add hx, neg_add_cancel, rpow_zero, mul_one]

/-- **Representation theorem for index `ρ`**, direction (⇒) ([BGT, Theorem 1.3.1] with
[BGT, Theorem 1.4.1]): if `f` is measurable near `∞` and regularly varying with index `ρ`, then
`f x = c x * exp (∫ t in a..x, r t / t)` for `x ≥ a`, with `a > 0`, `c` and `r` measurable,
`c x → c₀ ∈ (0, ∞)`, `r x → ρ`, and `r` bounded on `[a, ∞)`. -/
theorem IsRegularlyVarying.exists_representation (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) :
    ∃ a : ℝ, 0 < a ∧ ∃ c r : ℝ → ℝ, Measurable c ∧ Measurable r ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ Tendsto c atTop (𝓝 c₀)) ∧ Tendsto r atTop (𝓝 ρ) ∧
      (∃ B : ℝ, ∀ t ≥ a, |r t| ≤ B) ∧
      (∀ x ≥ a, IntervalIntegrable (fun t => r t / t) volume a x) ∧
      ∀ x ≥ a, f x = c x * exp (∫ t in a..x, r t / t) := by
  obtain ⟨X, hX⟩ := hm
  set g : ℝ → ℝ := (Ici X).indicator f with hg
  have hLm : Measurable fun x : ℝ => x ^ (-ρ) * g x := (by fun_prop : Measurable fun x : ℝ =>
    x ^ (-ρ)).mul hX
  have hL : IsSlowlyVarying fun x : ℝ => x ^ (-ρ) * g x := by
    have := (IsRegularlyVarying.rpow_id (-ρ)).mul (hf.indicator_Ici X)
    rw [neg_add_cancel] at this
    exact this.isSlowlyVarying
  obtain ⟨a₀, ha₀, c, ε, hcm, hεm, ⟨c₀, hc₀, hc⟩, hε, hint, hrep⟩ := hL.exists_representation hLm
  -- move the base point to a point `a` where `|ε| ≤ 1`, `f = g` and `a ≥ a₀`
  have hε1 : ∀ᶠ t in atTop, |ε t| ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.1 hε 1 one_pos] with t ht
    rw [Real.dist_eq, sub_zero] at ht
    exact ht.le
  obtain ⟨T, hT⟩ := eventually_atTop.1 hε1
  set a := max (max a₀ X) T with ha_def
  have ha₀a : a₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hXa : X ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have hTa : T ≤ a := le_max_right _ _
  have ha : 0 < a := ha₀.trans_le ha₀a
  set κ := exp (∫ t in a₀..a, ε t / t) with hκ
  have hint' : ∀ x ≥ a, IntervalIntegrable (fun t => ε t / t) volume a x := fun x hx =>
    (hint a ha₀a).symm.trans (hint x (ha₀a.trans hx))
  refine ⟨a, ha, fun x => a ^ ρ * κ * c x, fun t => ε t + ρ, (hcm.const_mul _),
    hεm.add_const ρ, ⟨a ^ ρ * κ * c₀, by positivity, hc.const_mul _⟩,
    by simpa using hε.add_const ρ, ⟨1 + |ρ|, fun t ht => ?_⟩,
    fun x hx => (integral_add_const_div ρ ha hx (hint' x hx)).1, fun x hx => ?_⟩
  · exact (abs_add_le _ _).trans (by linarith [hT t (hTa.trans ht)])
  · have hx0 : 0 < x := ha.trans_le hx
    have hgx : g x = f x := indicator_of_mem (mem_Ici.2 (hXa.trans hx)) f
    have h1 := hrep x (ha₀a.trans hx)
    rw [hgx] at h1
    have hsplit := integral_add_adjacent_intervals (hint a ha₀a) (hint' x hx)
    have hfx : f x = x ^ ρ * (x ^ (-ρ) * f x) := by
      rw [← mul_assoc, ← rpow_add hx0, add_neg_cancel, rpow_zero, one_mul]
    rw [(integral_add_const_div ρ ha hx (hint' x hx)).2, hfx, h1, ← hsplit, exp_add, exp_add,
      mul_comm ρ, ← rpow_def_of_pos (div_pos hx0 ha), div_rpow hx0.le ha.le, ← hκ]
    have := (rpow_pos_of_pos ha ρ).ne'
    field_simp

/-- **Karamata representation theorem for index `ρ`** ([BGT, Theorem 1.3.1] with [BGT, Theorem
1.4.1]): a function `f` measurable near `∞` is regularly varying with index `ρ` if and only if there
are `a > 0` and measurable functions `c`, `r` with `c x → c₀ ∈ (0, ∞)`, `r x → ρ` and
`f x = c x * exp (∫ t in a..x, r t / t)` for all `x ≥ a`. -/
theorem isRegularlyVarying_iff_exists_representation (hm : MeasurableNearTop f) :
    IsRegularlyVarying f ρ ↔ ∃ a : ℝ, 0 < a ∧ ∃ c r : ℝ → ℝ, Measurable c ∧ Measurable r ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ Tendsto c atTop (𝓝 c₀)) ∧ Tendsto r atTop (𝓝 ρ) ∧
      (∀ x ≥ a, IntervalIntegrable (fun t => r t / t) volume a x) ∧
      ∀ x ≥ a, f x = c x * exp (∫ t in a..x, r t / t) := by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨a, ha, c, r, hcm, hrm, hc, hr, -, hint, hrep⟩ := hf.exists_representation hm
    exact ⟨a, ha, c, r, hcm, hrm, hc, hr, hint, hrep⟩
  · rintro ⟨a, ha, c, r, -, -, ⟨c₀, hc₀, hc⟩, hr, hint, hrep⟩
    exact IsRegularlyVarying.of_representation ha hc₀ hc hr hint hrep

end ExtremeValueTheory
