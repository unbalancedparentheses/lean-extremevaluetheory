/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Regularly and slowly varying functions

A positive function `f : ℝ → ℝ` is *regularly varying (at `+∞`) with index `ρ`* if for every
`c > 0` we have `f (c * x) / f x → c ^ ρ` as `x → ∞`; it is *slowly varying* if the limit is `1`
for every `c > 0` (i.e. it is regularly varying with index `0`).

This file develops the basic theory, following Bingham, Goldie and Teugels,
*Regular Variation* (Cambridge University Press, 1987), henceforth [BGT].

## Main definitions

* `ExtremeValueTheory.IsSlowlyVarying f`: `f` is slowly varying at `+∞` ([BGT, §1.2]).
* `ExtremeValueTheory.IsRegularlyVarying f ρ`: `f` is regularly varying at `+∞` with index `ρ`
  ([BGT, §1.4]).

## Main results

* `IsRegularlyVarying.rpow_id`, `IsRegularlyVarying.const`, `isSlowlyVarying_log`: basic
  examples.
* `IsRegularlyVarying.mul`, `IsRegularlyVarying.inv`, `IsRegularlyVarying.div`,
  `IsRegularlyVarying.rpow`: closure properties.
* `isRegularlyVarying_iff_exists_isSlowlyVarying`: the representation `f x = x ^ ρ * L x` with
  `L` slowly varying ([BGT, Theorem 1.4.1]).
* `IsRegularlyVarying.tendstoUniformlyOn_of_isCompact`: the uniform convergence theorem for
  eventually monotone (or antitone) regularly varying functions ([BGT, §1.5.2 and
  Theorem 1.5.2]). For monotone functions an elementary sandwich argument suffices, and no
  measurability / Egorov-type argument is needed.
* `IsRegularlyVarying.potter_bound`: Potter-type bounds for eventually monotone (or antitone)
  regularly varying functions ([BGT, Theorem 1.5.6]).
-/

open Filter Topology Set Real

namespace ExtremeValueTheory

/-- A function `f : ℝ → ℝ` is *slowly varying* (at `+∞`) if it is eventually positive and
`f (c * x) / f x → 1` as `x → ∞`, for every `c > 0`. See [BGT, §1.2]. -/
def IsSlowlyVarying (f : ℝ → ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < f x) ∧ ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 1)

/-- A function `f : ℝ → ℝ` is *regularly varying with index `ρ`* (at `+∞`) if it is eventually
positive and `f (c * x) / f x → c ^ ρ` as `x → ∞`, for every `c > 0`. See [BGT, §1.4]. -/
def IsRegularlyVarying (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < f x) ∧ ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ ρ))

variable {f g : ℝ → ℝ} {ρ σ : ℝ}

/-- Slowly varying functions are exactly the regularly varying functions of index `0`. -/
theorem isSlowlyVarying_iff_isRegularlyVarying_zero :
    IsSlowlyVarying f ↔ IsRegularlyVarying f 0 := by
  simp [IsSlowlyVarying, IsRegularlyVarying, Real.rpow_zero]

alias ⟨IsSlowlyVarying.isRegularlyVarying, IsRegularlyVarying.isSlowlyVarying⟩ :=
  isSlowlyVarying_iff_isRegularlyVarying_zero

namespace IsRegularlyVarying

theorem eventually_pos (hf : IsRegularlyVarying f ρ) : ∀ᶠ x in atTop, 0 < f x := hf.1

theorem tendsto (hf : IsRegularlyVarying f ρ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ ρ)) := hf.2 c hc

/-- Regular variation only depends on the germ of the function at `+∞`. -/
theorem congr (hf : IsRegularlyVarying f ρ) (hfg : f =ᶠ[atTop] g) : IsRegularlyVarying g ρ := by
  refine ⟨(hf.1.and hfg).mono fun x hx => hx.2 ▸ hx.1, fun c hc => ?_⟩
  refine (hf.2 c hc).congr' ?_
  filter_upwards [hfg, (tendsto_id.const_mul_atTop hc).eventually hfg] with x h1 h2
  simp only [id] at h2
  rw [h1, h2]

/-- The power function `x ↦ x ^ ρ` is regularly varying with index `ρ`. -/
theorem rpow_id (ρ : ℝ) : IsRegularlyVarying (fun x => x ^ ρ) ρ := by
  refine ⟨(eventually_gt_atTop 0).mono fun x hx => rpow_pos_of_pos hx ρ, fun c hc => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [mul_rpow hc.le hx.le, mul_div_assoc, div_self (rpow_pos_of_pos hx ρ).ne', mul_one]

/-- A positive constant is regularly varying with index `0`. -/
theorem const {a : ℝ} (ha : 0 < a) : IsRegularlyVarying (fun _ => a) 0 := by
  refine ⟨Eventually.of_forall fun _ => ha, fun c _ => ?_⟩
  simp [div_self ha.ne']

/-- The product of regularly varying functions is regularly varying, and the indices add. -/
theorem mul (hf : IsRegularlyVarying f ρ) (hg : IsRegularlyVarying g σ) :
    IsRegularlyVarying (fun x => f x * g x) (ρ + σ) := by
  refine ⟨(hf.1.and hg.1).mono fun x hx => mul_pos hx.1 hx.2, fun c hc => ?_⟩
  rw [rpow_add hc]
  refine ((hf.2 c hc).mul (hg.2 c hc)).congr' (Eventually.of_forall fun x => ?_)
  exact (mul_div_mul_comm _ _ _ _).symm

/-- The reciprocal of a regularly varying function of index `ρ` is regularly varying of index
`-ρ`. -/
theorem inv (hf : IsRegularlyVarying f ρ) : IsRegularlyVarying (fun x => (f x)⁻¹) (-ρ) := by
  refine ⟨hf.1.mono fun x hx => inv_pos.2 hx, fun c hc => ?_⟩
  rw [rpow_neg hc.le]
  refine ((hf.2 c hc).inv₀ (rpow_pos_of_pos hc ρ).ne').congr' (Eventually.of_forall fun x => ?_)
  simp only
  rw [inv_div, inv_div_inv]

/-- The quotient of regularly varying functions is regularly varying, and the indices
subtract. -/
theorem div (hf : IsRegularlyVarying f ρ) (hg : IsRegularlyVarying g σ) :
    IsRegularlyVarying (fun x => f x / g x) (ρ - σ) := by
  simpa [div_eq_mul_inv, sub_eq_add_neg] using hf.mul hg.inv

/-- A real power of a regularly varying function of index `ρ` is regularly varying of index
`ρ * r`. -/
theorem rpow (hf : IsRegularlyVarying f ρ) (r : ℝ) :
    IsRegularlyVarying (fun x => f x ^ r) (ρ * r) := by
  refine ⟨hf.1.mono fun x hx => rpow_pos_of_pos hx r, fun c hc => ?_⟩
  rw [rpow_mul hc.le]
  refine ((hf.2 c hc).rpow_const (Or.inl (rpow_pos_of_pos hc ρ).ne')).congr' ?_
  filter_upwards [hf.1, (tendsto_id.const_mul_atTop hc).eventually hf.1] with x h1 h2
  exact div_rpow h2.le h1.le r

/-- Multiplying by a positive constant does not change regular variation. -/
theorem const_mul (hf : IsRegularlyVarying f ρ) {a : ℝ} (ha : 0 < a) :
    IsRegularlyVarying (fun x => a * f x) ρ := by
  simpa using (const ha).mul hf

end IsRegularlyVarying

namespace IsSlowlyVarying

/-- A positive constant is slowly varying. -/
theorem const {a : ℝ} (ha : 0 < a) : IsSlowlyVarying (fun _ => a) :=
  (IsRegularlyVarying.const ha).isSlowlyVarying

theorem mul (hf : IsSlowlyVarying f) (hg : IsSlowlyVarying g) :
    IsSlowlyVarying (fun x => f x * g x) := by
  have := hf.isRegularlyVarying.mul hg.isRegularlyVarying
  rw [add_zero] at this
  exact this.isSlowlyVarying

theorem inv (hf : IsSlowlyVarying f) : IsSlowlyVarying (fun x => (f x)⁻¹) := by
  have := hf.isRegularlyVarying.inv
  rw [neg_zero] at this
  exact this.isSlowlyVarying

theorem div (hf : IsSlowlyVarying f) (hg : IsSlowlyVarying g) :
    IsSlowlyVarying (fun x => f x / g x) := by
  have := hf.isRegularlyVarying.div hg.isRegularlyVarying
  rw [sub_zero] at this
  exact this.isSlowlyVarying

theorem rpow (hf : IsSlowlyVarying f) (r : ℝ) : IsSlowlyVarying (fun x => f x ^ r) := by
  have := hf.isRegularlyVarying.rpow r
  rw [zero_mul] at this
  exact this.isSlowlyVarying

end IsSlowlyVarying

/-- The logarithm is slowly varying. -/
theorem isSlowlyVarying_log : IsSlowlyVarying Real.log := by
  refine ⟨(eventually_gt_atTop 1).mono fun x hx => log_pos hx, fun c hc => ?_⟩
  have h : Tendsto (fun x => log c / log x + 1) atTop (𝓝 (0 + 1)) :=
    (tendsto_const_nhds.div_atTop tendsto_log_atTop).add_const 1
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [log_mul hc.ne' (by linarith), add_div, div_self (log_pos hx).ne']

/-- **Representation of regularly varying functions** ([BGT, Theorem 1.4.1]): `f` is regularly
varying with index `ρ` if and only if `f x = x ^ ρ * L x` for large `x`, with `L` slowly
varying. -/
theorem isRegularlyVarying_iff_exists_isSlowlyVarying :
    IsRegularlyVarying f ρ ↔ ∃ L : ℝ → ℝ, IsSlowlyVarying L ∧ ∀ᶠ x in atTop, f x = x ^ ρ * L x := by
  constructor
  · intro hf
    refine ⟨fun x => x ^ (-ρ) * f x, ?_, ?_⟩
    · have := (IsRegularlyVarying.rpow_id (-ρ)).mul hf
      rw [neg_add_cancel] at this
      exact this.isSlowlyVarying
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← mul_assoc, ← rpow_add hx, add_neg_cancel, rpow_zero, one_mul]
  · rintro ⟨L, hL, hfL⟩
    have := (IsRegularlyVarying.rpow_id ρ).mul hL.isRegularlyVarying
    rw [add_zero] at this
    exact this.congr (hfL.mono fun x hx => hx.symm)

/-! ### The uniform convergence theorem for monotone regularly varying functions -/

private lemma abs_sub_le_max_of_between {a b y z : ℝ} (h1 : min a b ≤ y) (h2 : y ≤ max a b) :
    |y - z| ≤ max |a - z| |b - z| := by
  have ha1 := neg_abs_le (a - z)
  have ha2 := le_abs_self (a - z)
  have hb1 := neg_abs_le (b - z)
  have hb2 := le_abs_self (b - z)
  have hm1 := le_max_left |a - z| |b - z|
  have hm2 := le_max_right |a - z| |b - z|
  rw [abs_le]
  rcases le_total a b with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    constructor <;> linarith
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    constructor <;> linarith

/-- The sandwich property satisfied by eventually monotone or antitone functions. -/
private lemma sandwich_of_monotoneOn_or_antitoneOn (hpos : ∀ᶠ x in atTop, 0 < f x) {a : ℝ}
    (hmono : MonotoneOn f (Ici a) ∨ AntitoneOn f (Ici a)) :
    ∀ c₁ : ℝ, 0 < c₁ → ∀ᶠ x in atTop, ∀ c c₂ : ℝ, c₁ ≤ c → c ≤ c₂ →
      min (f (c₁ * x) / f x) (f (c₂ * x) / f x) ≤ f (c * x) / f x ∧
      f (c * x) / f x ≤ max (f (c₁ * x) / f x) (f (c₂ * x) / f x) := by
  intro c₁ hc₁
  filter_upwards [hpos, eventually_ge_atTop (a / c₁), eventually_gt_atTop 0] with x hx hxa hx0
  intro c c₂ h1 h2
  have ha1 : c₁ * x ∈ Ici a := by
    rw [mem_Ici]
    rwa [div_le_iff₀' hc₁] at hxa
  have hm1 : c₁ * x ≤ c * x := mul_le_mul_of_nonneg_right h1 hx0.le
  have hm2 : c * x ≤ c₂ * x := mul_le_mul_of_nonneg_right h2 hx0.le
  have ha2 : c * x ∈ Ici a := le_trans ha1 hm1
  have ha3 : c₂ * x ∈ Ici a := le_trans ha2 hm2
  rcases hmono with hm | hm
  · have e1 := div_le_div_of_nonneg_right (hm ha1 ha2 hm1) hx.le
    have e2 := div_le_div_of_nonneg_right (hm ha2 ha3 hm2) hx.le
    exact ⟨(min_le_left _ _).trans e1, e2.trans (le_max_right _ _)⟩
  · have e1 := div_le_div_of_nonneg_right (hm ha1 ha2 hm1) hx.le
    have e2 := div_le_div_of_nonneg_right (hm ha2 ha3 hm2) hx.le
    exact ⟨(min_le_right _ _).trans e2, e1.trans (le_max_left _ _)⟩

namespace IsRegularlyVarying

/-- **Uniform convergence theorem** (monotone case), locally uniform version: if `f` is
regularly varying with index `ρ` and monotone or antitone on some interval `[a, ∞)`, then
`f (c * x) / f x → c ^ ρ` locally uniformly in `c ∈ (0, ∞)`. Compare [BGT, Theorem 1.5.2]. -/
theorem tendstoLocallyUniformlyOn (hf : IsRegularlyVarying f ρ) {a : ℝ}
    (hmono : MonotoneOn f (Ici a) ∨ AntitoneOn f (Ici a)) :
    TendstoLocallyUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop (Ioi 0) := by
  have hsand := sandwich_of_monotoneOn_or_antitoneOn hf.1 hmono
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε c₀ hc₀
  rw [mem_Ioi] at hc₀
  have hcont : ContinuousAt (fun c : ℝ => c ^ ρ) c₀ :=
    continuousAt_rpow_const _ _ (Or.inl hc₀.ne')
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont (ε / 3) (by positivity)
  set η := min δ c₀ / 2 with hη_def
  have hη : 0 < η := by positivity
  have hηδ : η < δ := by have := min_le_left δ c₀; linarith
  have hηc : η < c₀ := by have := min_le_right δ c₀; linarith
  have hc₁ : 0 < c₀ - η := by linarith
  have hc₂ : 0 < c₀ + η := by linarith
  refine ⟨Icc (c₀ - η) (c₀ + η),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  have h1 := Metric.tendsto_nhds.1 (hf.2 _ hc₁) (ε / 3) (by positivity)
  have h2 := Metric.tendsto_nhds.1 (hf.2 _ hc₂) (ε / 3) (by positivity)
  filter_upwards [h1, h2, hsand _ hc₁] with x hx1 hx2 hx3
  intro c hc
  have key := abs_sub_le_max_of_between (z := c₀ ^ ρ) (hx3 c (c₀ + η) hc.1 hc.2).1
    (hx3 c (c₀ + η) hc.1 hc.2).2
  have g1 : dist ((c₀ - η) ^ ρ) (c₀ ^ ρ) < ε / 3 :=
    hδε (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have g2 : dist ((c₀ + η) ^ ρ) (c₀ ^ ρ) < ε / 3 :=
    hδε (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have g3 : dist (c ^ ρ) (c₀ ^ ρ) < ε / 3 :=
    hδε (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  rw [Real.dist_eq] at g1 g2 g3 hx1 hx2 ⊢
  have k1 : |f ((c₀ - η) * x) / f x - c₀ ^ ρ| < 2 * ε / 3 := by
    rw [abs_lt] at g1 hx1 ⊢; constructor <;> linarith
  have k2 : |f ((c₀ + η) * x) / f x - c₀ ^ ρ| < 2 * ε / 3 := by
    rw [abs_lt] at g2 hx2 ⊢; constructor <;> linarith
  have k3 := lt_of_le_of_lt key (max_lt k1 k2)
  rw [abs_lt] at g3 k3 ⊢
  constructor <;> linarith

/-- **Uniform convergence theorem** (monotone case) ([BGT, Theorem 1.5.2]): if `f` is
regularly varying with index `ρ` and monotone or antitone on some interval `[a, ∞)`, then
`f (c * x) / f x → c ^ ρ` uniformly in `c` on every compact subset `K` of `(0, ∞)`.

For (eventually) monotone `f` this follows from an elementary sandwich argument, see
[BGT, §1.5.2]; the general measurable case is not needed here. -/
theorem tendstoUniformlyOn_of_isCompact (hf : IsRegularlyVarying f ρ) {a : ℝ}
    (hmono : MonotoneOn f (Ici a) ∨ AntitoneOn f (Ici a)) {K : Set ℝ} (hK : IsCompact K)
    (hK0 : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    ((hf.tendstoLocallyUniformlyOn hmono).mono hK0)

/-- The uniform convergence theorem (monotone case) on a compact interval `[b₁, b₂] ⊆ (0, ∞)`. -/
theorem tendstoUniformlyOn_Icc (hf : IsRegularlyVarying f ρ) {a : ℝ}
    (hmono : MonotoneOn f (Ici a) ∨ AntitoneOn f (Ici a)) {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop (Icc b₁ b₂) :=
  hf.tendstoUniformlyOn_of_isCompact hmono isCompact_Icc fun _ hc => hb₁.trans_le hc.1

/-- **Potter bounds from uniform convergence on `[1, 2]`** ([BGT, Theorem 1.5.6]): if `f` is
regularly varying with index `ρ` and `f (c x) / f x → c ^ ρ` uniformly for `c ∈ [1, 2]`, then
for every `δ > 0` and `A > 1` there is `x₀ > 0` such that `f > 0` on `[x₀, ∞)` and
`f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ))` for all `x, y ≥ x₀`. The uniform
convergence holds for eventually monotone `f` (`potter_bound`) and for measurable `f`
(`potter_bound_of_measurable`). -/
theorem potter_bound_of_tendstoUniformlyOn_Icc (hf : IsRegularlyVarying f ρ)
    (hunif : TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop (Icc 1 2))
    {δ A : ℝ} (hδ : 0 < δ) (hA : 1 < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < f x) ∧ ∀ x ≥ x₀, ∀ y ≥ x₀,
      f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) := by
  obtain ⟨η, hη, hηA, hηA'⟩ : ∃ η : ℝ, 0 < η ∧ 1 + η ≤ A ∧ A⁻¹ ≤ 1 - η := by
    have hAinv : A⁻¹ < 1 := inv_lt_one_of_one_lt₀ hA
    refine ⟨min (A - 1) (1 - A⁻¹), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have := min_le_left (A - 1) (1 - A⁻¹); linarith
    · have := min_le_right (A - 1) (1 - A⁻¹); linarith
  have hη1 : η < 1 := by have := inv_pos.2 (zero_lt_one.trans hA); linarith
  obtain ⟨m, hm, hmt⟩ : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc (1 : ℝ) 2, m ≤ t ^ ρ := by
    refine ⟨min 1 ((2 : ℝ) ^ ρ), lt_min one_pos (rpow_pos_of_pos two_pos ρ), fun t ht => ?_⟩
    rcases le_total 0 ρ with hρ | hρ
    · exact (min_le_left _ _).trans (one_le_rpow ht.1 hρ)
    · exact (min_le_right _ _).trans (rpow_le_rpow_of_nonpos (by linarith [ht.1]) ht.2 hρ)
  have hU := Metric.tendstoUniformlyOn_iff.1 hunif (η * m) (by positivity)
  have hS1 : ∀ᶠ x in atTop, f (2 * x) / f x < 2 ^ (ρ + δ) :=
    (hf.2 2 two_pos).eventually_lt_const (rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith))
  have hS2 : ∀ᶠ x in atTop, 2 ^ (ρ - δ) < f (2 * x) / f x :=
    (hf.2 2 two_pos).eventually_const_lt (rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith))
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1
    ((hU.and (hS1.and hS2)).and (hf.1.and (eventually_gt_atTop 0)))
  have hpos : ∀ x ≥ x₁, 0 < f x := fun x hx => (hx₁ x hx).2.1
  have hx₁pos : 0 < x₁ := (hx₁ x₁ le_rfl).2.2
  -- the bounds for `t ∈ [1, 2]`, from the uniform convergence theorem
  have hloc : ∀ x ≥ x₁, ∀ t ∈ Icc (1 : ℝ) 2,
      f (t * x) / f x ≤ (1 + η) * t ^ (ρ + δ) ∧ (1 - η) * t ^ (ρ - δ) ≤ f (t * x) / f x := by
    intro x hx t ht
    have h := (hx₁ x hx).1.1 t ht
    rw [Real.dist_eq, abs_lt] at h
    have hmt' := mul_le_mul_of_nonneg_left (hmt t ht) hη.le
    have e1 : t ^ ρ ≤ t ^ (ρ + δ) := rpow_le_rpow_of_exponent_le ht.1 (by linarith)
    have e2 : t ^ (ρ - δ) ≤ t ^ ρ := rpow_le_rpow_of_exponent_le ht.1 (by linarith)
    have e1' := mul_le_mul_of_nonneg_left e1 (by linarith : (0 : ℝ) ≤ 1 + η)
    have e2' := mul_le_mul_of_nonneg_left e2 (by linarith : (0 : ℝ) ≤ 1 - η)
    constructor <;> linarith
  -- iterate using the doubling bounds
  have hind : ∀ n : ℕ, ∀ x ≥ x₁, ∀ t : ℝ, 1 ≤ t → t ≤ 2 ^ n →
      f (t * x) / f x ≤ (1 + η) * t ^ (ρ + δ) ∧ (1 - η) * t ^ (ρ - δ) ≤ f (t * x) / f x := by
    intro n
    induction n with
    | zero =>
      intro x hx t h1 h2
      exact hloc x hx t ⟨h1, by simp at h2; linarith⟩
    | succ n ih =>
      intro x hx t h1 h2
      rcases le_or_gt t 2 with ht2 | ht2
      · exact hloc x hx t ⟨h1, ht2⟩
      · have hx0 : 0 < x := hx₁pos.trans_le hx
        have hx2 : 2 * x ≥ x₁ := by linarith
        have h' := ih (2 * x) hx2 (t / 2) (by rw [le_div_iff₀ two_pos]; linarith)
          (by rw [div_le_iff₀ two_pos, ← pow_succ]; exact h2)
        have hfx := hpos x hx
        have hf2x := hpos (2 * x) hx2
        have htx : x₁ ≤ t / 2 * (2 * x) := by
          have : t / 2 * (2 * x) = t * x := by ring
          rw [this]; nlinarith
        have hftx := hpos _ htx
        have eq : f (t * x) / f x = f (t / 2 * (2 * x)) / f (2 * x) * (f (2 * x) / f x) := by
          rw [show t / 2 * (2 * x) = t * x by ring, div_mul_div_cancel₀ hf2x.ne']
        have hs := (hx₁ x hx).1.2
        have pw : ∀ p : ℝ, t ^ p = (t / 2) ^ p * 2 ^ p := fun p => by
          rw [← mul_rpow (by linarith) zero_le_two, div_mul_cancel₀ t two_ne_zero]
        constructor
        · rw [eq, pw (ρ + δ), ← mul_assoc (1 + η)]
          exact mul_le_mul h'.1 hs.1.le (div_pos hf2x hfx).le
            (mul_nonneg (by linarith) (rpow_nonneg (by linarith) _))
        · rw [eq, pw (ρ - δ), ← mul_assoc (1 - η)]
          exact mul_le_mul h'.2 hs.2.le (rpow_nonneg zero_le_two _) (div_pos hftx hf2x).le
  refine ⟨x₁, hx₁pos, hpos, fun x hx y hy => ?_⟩
  have hx0 : 0 < x := hx₁pos.trans_le hx
  have hy0 : 0 < y := hx₁pos.trans_le hy
  have hfx := hpos x hx
  have hfy := hpos y hy
  rcases le_total x y with hxy | hxy
  · have ht1 : 1 ≤ y / x := by rw [le_div_iff₀ hx0]; linarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (y / x) one_lt_two
    have h := (hind n x hx (y / x) ht1 hn.le).1
    rw [div_mul_cancel₀ y hx0.ne'] at h
    calc f y / f x ≤ (1 + η) * (y / x) ^ (ρ + δ) := h
      _ ≤ A * (y / x) ^ (ρ + δ) := mul_le_mul_of_nonneg_right hηA (rpow_nonneg (by linarith) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  · have ht1 : 1 ≤ x / y := by rw [le_div_iff₀ hy0]; linarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / y) one_lt_two
    have h := (hind n y hy (x / y) ht1 hn.le).2
    rw [div_mul_cancel₀ x hy0.ne'] at h
    have hyx : 0 < y / x := div_pos hy0 hx0
    have hs : 0 < (y / x) ^ (ρ - δ) := rpow_pos_of_pos hyx _
    have htinv : (x / y) ^ (ρ - δ) = ((y / x) ^ (ρ - δ))⁻¹ := by
      rw [← inv_rpow hyx.le, inv_div]
    have h2 : A⁻¹ * ((y / x) ^ (ρ - δ))⁻¹ ≤ f x / f y := by
      refine le_trans ?_ h
      rw [htinv]
      exact mul_le_mul_of_nonneg_right hηA' (inv_pos.2 hs).le
    have h3 := inv_anti₀ (mul_pos (inv_pos.2 (zero_lt_one.trans hA)) (inv_pos.2 hs)) h2
    rw [inv_div, mul_inv, inv_inv, inv_inv] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))

/-- **Potter bounds** for eventually monotone (or antitone) regularly varying functions
([BGT, Theorem 1.5.6]): if `f` is regularly varying with index `ρ` and monotone or antitone on
some `[a, ∞)`, then for every `δ > 0` and `A > 1` there is `x₀ > 0` such that `f > 0` on
`[x₀, ∞)` and
`f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ))` for all `x, y ≥ x₀`. -/
theorem potter_bound (hf : IsRegularlyVarying f ρ) {a : ℝ}
    (hmono : MonotoneOn f (Ici a) ∨ AntitoneOn f (Ici a)) {δ A : ℝ} (hδ : 0 < δ) (hA : 1 < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < f x) ∧ ∀ x ≥ x₀, ∀ y ≥ x₀,
      f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) :=
  hf.potter_bound_of_tendstoUniformlyOn_Icc
    (hf.tendstoUniformlyOn_Icc hmono (b₁ := 1) (b₂ := 2) one_pos) hδ hA

end IsRegularlyVarying

/-- If `f / g → L > 0` and `g` is regularly varying with index `ρ`, then so is `f`. -/
theorem IsRegularlyVarying.of_tendsto_div {f g : ℝ → ℝ} {ρ L : ℝ} (hg : IsRegularlyVarying g ρ)
    (hfg : Tendsto (fun x => f x / g x) atTop (𝓝 L)) (hL : 0 < L) : IsRegularlyVarying f ρ := by
  have hpos : ∀ᶠ x in atTop, 0 < f x := by
    filter_upwards [(tendsto_order.1 hfg).1 0 hL, hg.1] with x h1 h2
    exact (div_pos_iff_of_pos_right h2).1 h1
  refine ⟨hpos, fun c hc => ?_⟩
  have hcx : Tendsto (fun x => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h := ((hfg.comp hcx).mul (hg.2 c hc)).div hfg hL.ne'
  rw [mul_div_cancel_left₀ _ hL.ne'] at h
  refine h.congr' ?_
  filter_upwards [hg.1, hcx.eventually hg.1, hpos] with x h1 h2 h3
  simp only [Function.comp_apply, Pi.div_apply]
  field_simp

end ExtremeValueTheory
