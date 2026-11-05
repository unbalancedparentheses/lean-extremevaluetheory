/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.UniformConvergence

/-!
# The uniform convergence theorem: measurability near infinity, and the two tails

`ExtremeValueTheory.RegularVariation.UniformConvergence` proves the compact part of the uniform
convergence theorem for functions measurable on all of `ℝ`. This file completes it, following
Bingham, Goldie and Teugels, *Regular Variation* (Cambridge University Press, 1987), henceforth
[BGT]:

* measurability is asked only on some `[X, ∞)`, which is the hypothesis in the book;
* the two remaining ranges of [BGT, Theorem 1.5.2] are added: `[a, ∞)` for `ρ < 0`, and `(0, b]`
  for `ρ > 0` when `f` is bounded on each `(0, b]`.

"Measurable" means Borel measurable. A function that is only Lebesgue measurable is not covered.

## Main definitions

* `ExtremeValueTheory.MeasurableNearTop f`: `f` is Borel measurable on some `[X, ∞)`.

## Main results

* `IsRegularlyVarying.tendstoUniformlyOn_of_measurableNearTop`: compact part of [BGT, Theorem 1.5.2].
* `IsRegularlyVarying.potter_bound_of_measurableNearTop`,
  `IsRegularlyVarying.potter_bounds_of_measurableNearTop`: [BGT, Theorem 1.5.6].
* `IsRegularlyVarying.tendsto_atTop_of_measurableNearTop`, `..tendsto_zero_of_measurableNearTop`:
  `ρ > 0` gives `f → ∞`, `ρ < 0` gives `f → 0`.
* `IsRegularlyVarying.tendstoUniformlyOn_Ici_of_measurableNearTop`: uniformity on `[a, ∞)`, `ρ < 0`.
* `IsRegularlyVarying.tendstoUniformlyOn_Ioc_of_measurableNearTop`: uniformity on `(0, b]`, `ρ > 0`,
  with `f` bounded on each `(0, b]`.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

/-- `f` is **measurable near `∞`**: its restriction to some `[X, ∞)` is Borel measurable, written
as measurability of the function equal to `f` on `[X, ∞)` and to `0` elsewhere. Nothing is asked of
`f` below `X`. -/
def MeasurableNearTop (f : ℝ → ℝ) : Prop :=
  ∃ X : ℝ, Measurable ((Ici X).indicator f)

/-- A measurable function is measurable near `∞`. -/
theorem _root_.Measurable.measurableNearTop {f : ℝ → ℝ} (hm : Measurable f) : MeasurableNearTop f :=
  ⟨0, hm.indicator measurableSet_Ici⟩

/-- A function that is monotone on some `[a, ∞)` is measurable near `∞`. -/
theorem _root_.MonotoneOn.measurableNearTop {f : ℝ → ℝ} {a : ℝ} (hf : MonotoneOn f (Ici a)) :
    MeasurableNearTop f := by
  have hg : Monotone fun t => f (max t a) := fun s t hst =>
    hf (mem_Ici.2 (le_max_right s a)) (mem_Ici.2 (le_max_right t a)) (max_le_max hst le_rfl)
  have heq : (Ici a).indicator f = (Ici a).indicator fun t => f (max t a) := by
    refine indicator_congr fun t ht => ?_
    rw [max_eq_left (mem_Ici.1 ht)]
  refine ⟨a, ?_⟩
  rw [heq]
  exact hg.measurable.indicator measurableSet_Ici

/-- A function that is antitone on some `[a, ∞)` is measurable near `∞`. -/
theorem _root_.AntitoneOn.measurableNearTop {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a)) :
    MeasurableNearTop f := by
  have hg : Antitone fun t => f (max t a) := fun s t hst =>
    hf (mem_Ici.2 (le_max_right s a)) (mem_Ici.2 (le_max_right t a)) (max_le_max hst le_rfl)
  have heq : (Ici a).indicator f = (Ici a).indicator fun t => f (max t a) := by
    refine indicator_congr fun t ht => ?_
    rw [max_eq_left (mem_Ici.1 ht)]
  refine ⟨a, ?_⟩
  rw [heq]
  exact hg.measurable.indicator measurableSet_Ici

namespace IsRegularlyVarying

variable {f : ℝ → ℝ} {ρ : ℝ}

/-- `f` agrees with its truncation at `X` near `∞`. -/
theorem indicator_Ici_eventuallyEq (f : ℝ → ℝ) (X : ℝ) : (Ici X).indicator f =ᶠ[atTop] f := by
  filter_upwards [eventually_ge_atTop X] with x hx
  exact indicator_of_mem (mem_Ici.2 hx) f

/-- The truncation of a regularly varying function at `X` is regularly varying. -/
theorem indicator_Ici (hf : IsRegularlyVarying f ρ) (X : ℝ) :
    IsRegularlyVarying ((Ici X).indicator f) ρ :=
  hf.congr (indicator_Ici_eventuallyEq f X).symm

/-- **Uniform convergence theorem**, compact part ([BGT, Theorem 1.5.2]), for `f` measurable near
`∞`: `f (c * x) / f x → c ^ ρ` uniformly in `c` on every compact subset `K` of `(0, ∞)`. -/
theorem tendstoUniformlyOn_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop K := by
  obtain ⟨X, hX⟩ := hm
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  refine ((hf.indicator_Ici X).tendstoUniformlyOn_of_measurable hX hK hK0).congr ?_
  obtain ⟨m, hmK, hm'⟩ := hK.exists_isMinOn hKne continuousOn_id
  have hm0 : 0 < m := hK0 hmK
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop (X / m), eventually_gt_atTop 0]
    with x hxX hxm hx0 c hc
  have hcm : m ≤ c := hm' hc
  have hcx : X ≤ c * x := by
    rw [div_le_iff₀ hm0] at hxm
    have := mul_le_mul_of_nonneg_right hcm hx0.le
    linarith [mul_comm m x]
  simp only [indicator_of_mem (mem_Ici.2 hcx), indicator_of_mem (mem_Ici.2 hxX)]

/-- **Potter bounds** ([BGT, Theorem 1.5.6 (iii)]), for `f` measurable near `∞`: for every `δ > 0`
and `A > 1` there is `x₀ > 0` such that `f > 0` on `[x₀, ∞)` and
`f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ))` for all `x, y ≥ x₀`. -/
theorem potter_bound_of_measurableNearTop (hf : IsRegularlyVarying f ρ) (hm : MeasurableNearTop f)
    {δ A : ℝ} (hδ : 0 < δ) (hA : 1 < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < f x) ∧ ∀ x ≥ x₀, ∀ y ≥ x₀,
      f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) :=
  hf.potter_bound_of_tendstoUniformlyOn_Icc
    (hf.tendstoUniformlyOn_of_measurableNearTop hm (isCompact_Icc (a := 1) (b := 2))
      fun _ hc => one_pos.trans_le hc.1) hδ hA

/-- **Potter bounds**, two-sided form ([BGT, Theorem 1.5.6 (iii)]), for `f` measurable near `∞`. -/
theorem potter_bounds_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) {δ A : ℝ} (hδ : 0 < δ) (hA : 1 < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < f x) ∧ ∀ x ≥ x₀, ∀ y ≥ x₀,
      A⁻¹ * min ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) ≤ f y / f x ∧
      f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) := by
  obtain ⟨X, hX⟩ := hm
  obtain ⟨x₀, hx₀, hpos, hP⟩ := (hf.indicator_Ici X).potter_bounds_of_measurable hX hδ hA
  set x₁ := max x₀ X with hx₁
  have h₀ : x₀ ≤ x₁ := le_max_left _ _
  have hXx : X ≤ x₁ := le_max_right _ _
  have hg : ∀ x ≥ x₁, (Ici X).indicator f x = f x := fun x hx =>
    indicator_of_mem (mem_Ici.2 (hXx.trans hx)) f
  refine ⟨x₁, hx₀.trans_le h₀, fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [← hg x hx]
    exact hpos x (h₀.trans hx)
  · have := hP x (h₀.trans hx) y (h₀.trans hy)
    rwa [hg x hx, hg y hy] at this

/-- **A regularly varying function of positive index tends to `∞`** (compare [BGT, Proposition
1.5.1]), for `f` measurable near `∞`. No monotonicity is assumed. Some measurability is needed for
the proof, which goes through the Potter bounds. -/
theorem tendsto_atTop_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) (hρ : 0 < ρ) : Tendsto f atTop atTop := by
  have hδ : 0 < ρ / 2 := by linarith
  obtain ⟨x₀, hx₀, hpos, hP⟩ := hf.potter_bounds_of_measurableNearTop hm hδ one_lt_two
  have hfx₀ := hpos x₀ le_rfl
  have hlim : Tendsto (fun y : ℝ => f x₀ * 2⁻¹ * (y / x₀) ^ (ρ / 2)) atTop atTop :=
    ((tendsto_rpow_atTop hδ).comp (tendsto_id.atTop_div_const hx₀)).const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_ge_atTop x₀] with y hy
  have h := (hP x₀ le_rfl y hy).1
  have hu : 1 ≤ y / x₀ := (one_le_div hx₀).2 hy
  rw [min_eq_right (rpow_le_rpow_of_exponent_le hu (by linarith)),
    show ρ - ρ / 2 = ρ / 2 by ring, le_div_iff₀ hfx₀] at h
  linarith

/-- **A regularly varying function of negative index tends to `0`** (compare [BGT, Proposition
1.5.1]), for `f` measurable near `∞`. No monotonicity is assumed. -/
theorem tendsto_zero_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) (hρ : ρ < 0) : Tendsto f atTop (𝓝 0) := by
  have hm' : MeasurableNearTop fun x => (f x)⁻¹ := by
    obtain ⟨X, hX⟩ := hm
    refine ⟨X, ?_⟩
    have : (Ici X).indicator (fun x => (f x)⁻¹) = fun x => ((Ici X).indicator f x)⁻¹ := by
      funext x
      by_cases hx : x ∈ Ici X <;> simp [hx]
    rw [this]
    exact hX.inv
  have h := hf.inv.tendsto_atTop_of_measurableNearTop hm' (by linarith)
  exact h.inv_tendsto_atTop.congr fun x => by simp

/-- **Uniform convergence on `[a, ∞)` for `ρ < 0`** (a part of [BGT, Theorem 1.5.2]): if `f` is
measurable near `∞` and regularly varying with index `ρ < 0`, then `f (c * x) / f x → c ^ ρ`
uniformly in `c ∈ [a, ∞)`, for every `a > 0`. -/
theorem tendstoUniformlyOn_Ici_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) (hρ : ρ < 0) {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop (Ici a) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < -ρ / 2 := by linarith
  obtain ⟨x₀, hx₀, hpos, hP⟩ := hf.potter_bound_of_measurableNearTop hm hδ one_lt_two
  have hlim : Tendsto (fun M : ℝ => 2 * M ^ (ρ / 2)) atTop (𝓝 (2 * 0)) := by
    refine Tendsto.const_mul 2 ?_
    have := tendsto_rpow_neg_atTop (y := -ρ / 2) hδ
    simpa [neg_div] using this
  rw [mul_zero] at hlim
  obtain ⟨M, hM1, hMa, hMε⟩ := ((eventually_ge_atTop 1).and ((eventually_ge_atTop a).and
    (hlim.eventually (gt_mem_nhds hε)))).exists
  have hU := Metric.tendstoUniformlyOn_iff.1 (hf.tendstoUniformlyOn_of_measurableNearTop hm
    (isCompact_Icc (a := a) (b := M)) fun _ hc => ha.trans_le hc.1) ε hε
  filter_upwards [hU, eventually_ge_atTop x₀] with x h1 hx c hc
  rcases le_total c M with hcM | hMc
  · exact h1 c ⟨hc, hcM⟩
  have hc1 : 1 ≤ c := hM1.trans hMc
  have hc0 : 0 < c := by linarith
  have hx0 : 0 < x := hx₀.trans_le hx
  have hcx : x₀ ≤ c * x := hx.trans (le_mul_of_one_le_left hx0.le hc1)
  have hP' := hP x hx (c * x) hcx
  rw [mul_div_cancel_right₀ _ hx0.ne', max_eq_left (rpow_le_rpow_of_exponent_le hc1 (by linarith)),
    show ρ + -ρ / 2 = ρ / 2 by ring] at hP'
  have hratio : 0 < f (c * x) / f x := div_pos (hpos _ hcx) (hpos _ hx)
  have hmono : c ^ (ρ / 2) ≤ M ^ (ρ / 2) :=
    rpow_le_rpow_of_nonpos (by linarith) hMc (by linarith)
  have hcpos : 0 < c ^ (ρ / 2) := rpow_pos_of_pos hc0 _
  have h2 : c ^ ρ ≤ c ^ (ρ / 2) := rpow_le_rpow_of_exponent_le hc1 (by linarith)
  have h3 : 0 < c ^ ρ := rpow_pos_of_pos hc0 _
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Uniform convergence on `(0, b]` for `ρ > 0`** (a part of [BGT, Theorem 1.5.2]): if `f` is
measurable near `∞`, regularly varying with index `ρ > 0`, and bounded on each `(0, b]`, then
`f (c * x) / f x → c ^ ρ` uniformly in `c ∈ (0, b]`.

The boundedness hypothesis is necessary: on `c ∈ (0, b]` the argument `c * x` runs over all of
`(0, b x]`, so the behaviour of `f` near `0` matters. -/
theorem tendstoUniformlyOn_Ioc_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) (hρ : 0 < ρ) (hbd : ∀ b : ℝ, ∃ B : ℝ, ∀ y ∈ Ioc 0 b, |f y| ≤ B)
    (b : ℝ) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop (Ioc 0 b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ρ / 2 := by linarith
  obtain ⟨x₀, hx₀, hpos, hP⟩ := hf.potter_bound_of_measurableNearTop hm hδ one_lt_two
  obtain ⟨B, hB⟩ := hbd x₀
  -- choose `η ∈ (0, 1]` with `2 η ^ (ρ / 2) < ε`
  have hlim : Tendsto (fun η : ℝ => 2 * η ^ (ρ / 2)) (𝓝[>] 0) (𝓝 (2 * 0)) := by
    refine Tendsto.const_mul 2 ?_
    have := (continuousAt_rpow_const (0 : ℝ) (ρ / 2) (Or.inr hδ.le)).tendsto
    rw [zero_rpow hδ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [mul_zero] at hlim
  obtain ⟨η, hηε, hη1, hη0⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
    ((eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds one_pos)).and
      self_mem_nhdsWithin)).exists
  have hη0 : 0 < η := hη0
  have hU := Metric.tendstoUniformlyOn_iff.1 (hf.tendstoUniformlyOn_of_measurableNearTop hm
    (isCompact_Icc (a := η) (b := b)) fun _ hc => hη0.trans_le hc.1) ε hε
  have hfinf := hf.tendsto_atTop_of_measurableNearTop hm hρ
  filter_upwards [hU, eventually_ge_atTop x₀, hfinf.eventually_gt_atTop (|B| / (ε / 2))] with x h1 hx hxB
    c hc
  rcases le_total η c with hηc | hcη
  · exact h1 c ⟨hηc, hc.2⟩
  have hc0 : 0 < c := hc.1
  have hc1 : c ≤ 1 := by linarith
  have hx0 : 0 < x := hx₀.trans_le hx
  have hcpow : c ^ (ρ / 2) ≤ η ^ (ρ / 2) := rpow_le_rpow hc0.le hcη hδ.le
  have hcpos : 0 < c ^ (ρ / 2) := rpow_pos_of_pos hc0 _
  have hρc : c ^ ρ ≤ c ^ (ρ / 2) := rpow_le_rpow_of_exponent_ge hc0 hc1 (by linarith)
  have hρpos : 0 < c ^ ρ := rpow_pos_of_pos hc0 _
  have hfx : 0 < f x := hpos x hx
  rw [Real.dist_eq]
  rcases le_or_gt x₀ (c * x) with hcx | hcx
  · have hP' := hP x hx (c * x) hcx
    rw [mul_div_cancel_right₀ _ hx0.ne', max_eq_right (rpow_le_rpow_of_exponent_ge hc0 hc1
      (by linarith)), show ρ - ρ / 2 = ρ / 2 by ring] at hP'
    have hratio : 0 < f (c * x) / f x := div_pos (hpos _ hcx) hfx
    rw [abs_lt]
    constructor <;> linarith
  · have hy : c * x ∈ Ioc 0 x₀ := ⟨mul_pos hc0 hx0, hcx.le⟩
    have hBy := hB _ hy
    have hsmall : |f (c * x) / f x| < ε / 2 := by
      rw [abs_div, abs_of_pos hfx, div_lt_iff₀ hfx]
      have h2 : |B| < f x * (ε / 2) := by
        rwa [div_lt_iff₀ (half_pos hε)] at hxB
      have := le_abs_self B
      linarith
    rw [abs_lt] at hsmall ⊢
    constructor <;> linarith

end IsRegularlyVarying

end ExtremeValueTheory
