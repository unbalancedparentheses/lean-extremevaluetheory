/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Basic
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The uniform convergence theorem for measurable regularly varying functions

Following Bingham, Goldie and Teugels, *Regular Variation* (Cambridge University Press, 1987),
henceforth [BGT], we prove the **uniform convergence theorem** ([BGT, Theorem 1.2.1]) for
*measurable* slowly varying functions, without any monotonicity assumption, together with its
version for regularly varying functions ([BGT, Theorem 1.5.2]) and the general **Potter bounds**
([BGT, Theorem 1.5.6]). The Karamata representation theorem ([BGT, Theorem 1.3.1]) is proved in
`ExtremeValueTheory.RegularVariation.Representation`.

## Main results

* `ExtremeValueTheory.tendstoUniformlyOn_sub_of_measurable`: additive form. If `h : ℝ → ℝ` is
  measurable and `h (x + u) - h x → 0` as `x → ∞` for every `u`, then the convergence is uniform
  in `u` on compact sets.
* `ExtremeValueTheory.IsSlowlyVarying.tendstoUniformlyOn_of_measurable`: [BGT, Theorem 1.2.1].
* `ExtremeValueTheory.IsRegularlyVarying.tendstoUniformlyOn_of_measurable`: [BGT, Theorem 1.5.2].
* `ExtremeValueTheory.IsRegularlyVarying.potter_bound_of_measurable`: [BGT, Theorem 1.5.6].

## Proof

We work additively. Fix `ε > 0` and let `A x = {u ∈ [0, 2] | ε / 2 ≤ |h (x + u) - h x|}`. These
are measurable sets whose indicators tend to `0` pointwise, so by dominated convergence their
Lebesgue measures tend to `0`. If `x` is large then `|A x| < 1/2` and `|A (x + ξ)| < 1/2` for
`ξ ∈ [0, 1]`; since `[1, 2]` has measure `1`, some `u ∈ [1, 2]` lies neither in `A x` nor in
`A (x + ξ) + ξ`, and then `|h (x + ξ) - h x| ≤ |h (x + u) - h x| + |h (x + u) - h (x + ξ)| < ε`.
This is the measure-theoretic (Steinhaus-type) core of the classical proofs, cf. [BGT, §1.2.1].
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

variable {h : ℝ → ℝ}

/-- The core of the uniform convergence theorem: uniformity on `[0, 1]`. -/
private lemma eventually_forall_Icc_zero_one (hm : Measurable h)
    (hh : ∀ u : ℝ, Tendsto (fun x => h (x + u) - h x) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∀ ξ ∈ Icc (0 : ℝ) 1, |h (x + ξ) - h x| < ε := by
  set A : ℝ → Set ℝ := fun x => Icc 0 2 ∩ {u | ε / 2 ≤ |h (x + u) - h x|} with hA
  have hAm : ∀ x, MeasurableSet (A x) := fun x =>
    measurableSet_Icc.inter (measurableSet_le measurable_const
      (continuous_abs.measurable.comp ((hm.comp (measurable_const_add x)).sub_const _)))
  have hlim : Tendsto (fun x => volume (A x)) atTop (𝓝 (volume (∅ : Set ℝ))) := by
    refine tendsto_measure_of_tendsto_indicator atTop hAm measurableSet_Icc
      (by simp [Real.volume_Icc]) (Eventually.of_forall fun x => inter_subset_left) fun u => ?_
    filter_upwards [(hh u).abs.eventually (gt_mem_nhds (by simp; linarith : |(0:ℝ)| < ε / 2))]
      with x hx
    simp only [hA, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    exact fun _ => hx
  rw [measure_empty] at hlim
  have hev : ∀ᶠ x in atTop, volume (A x) < 2⁻¹ :=
    (tendsto_order.1 hlim).2 _ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop X] with x hx ξ hξ
  by_contra hcon
  rw [not_lt] at hcon
  have hy : X ≤ x + ξ := by linarith [hξ.1]
  have hsub : Icc (1 : ℝ) 2 ⊆ A x ∪ (fun u => u + -ξ) ⁻¹' A (x + ξ) := by
    intro u hu
    by_cases h1 : ε / 2 ≤ |h (x + u) - h x|
    · exact Or.inl ⟨⟨by linarith [hu.1], hu.2⟩, h1⟩
    · refine Or.inr ⟨⟨by linarith [hu.1, hξ.2], by linarith [hu.2, hξ.1]⟩, ?_⟩
      rw [not_le] at h1
      show ε / 2 ≤ |h (x + ξ + (u + -ξ)) - h (x + ξ)|
      rw [show x + ξ + (u + -ξ) = x + u by ring]
      have := abs_sub_le (h (x + ξ)) (h (x + u)) (h x)
      rw [abs_sub_comm (h (x + ξ)) (h (x + u))] at this
      linarith
  have h1 := measure_mono (μ := volume) hsub
  have h2 := measure_union_le (μ := volume) (A x) ((fun u => u + -ξ) ⁻¹' A (x + ξ))
  rw [measure_preimage_add_right] at h2
  rw [Real.volume_Icc] at h1
  have h3 : volume (A x) + volume (A (x + ξ)) < 2⁻¹ + 2⁻¹ :=
    ENNReal.add_lt_add (hX x hx) (hX _ hy)
  rw [ENNReal.inv_two_add_inv_two] at h3
  have : ENNReal.ofReal (2 - 1) = 1 := by norm_num
  rw [this] at h1
  exact lt_irrefl _ (h1.trans_lt (h2.trans_lt h3))

/-- Uniformity on `[-N, N]`. -/
private lemma eventually_forall_Icc (hm : Measurable h)
    (hh : ∀ u : ℝ, Tendsto (fun x => h (x + u) - h x) atTop (𝓝 0)) (N : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∀ u ∈ Icc (-N) N, |h (x + u) - h x| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_ge N
  set η := ε / (n + 1) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨X, hX⟩ := eventually_atTop.1 (eventually_forall_Icc_zero_one hm hh hη0)
  have hind : ∀ k : ℕ, ∀ x ≥ X, ∀ u ∈ Icc (0 : ℝ) k, |h (x + u) - h x| ≤ k * η := by
    intro k
    induction k with
    | zero =>
      intro x _ u hu
      have : u = 0 := le_antisymm (by simpa using hu.2) hu.1
      simp [this]
    | succ k ih =>
      intro x hx u hu
      push_cast at hu ⊢
      rcases le_or_gt u 1 with hu1 | hu1
      · have := hX x hx u ⟨hu.1, hu1⟩
        have : (0 : ℝ) ≤ k * η := by positivity
        linarith
      · have h1 := ih (x + 1) (by linarith) (u - 1) ⟨by linarith, by linarith [hu.2]⟩
        have h2 := hX x hx 1 ⟨zero_le_one, le_rfl⟩
        rw [show x + 1 + (u - 1) = x + u by ring] at h1
        have := abs_sub_le (h (x + u)) (h (x + 1)) (h x)
        linarith
  have hnη : (n : ℝ) * η < ε := by
    rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith
  filter_upwards [eventually_ge_atTop (X + n)] with x hx u hu
  rcases le_total 0 u with h0 | h0
  · exact (hind n x (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) u
      ⟨h0, hu.2.trans hn⟩).trans_lt hnη
  · have := hind n (x + u) (by linarith [hu.1]) (-u) ⟨by linarith, by linarith [hu.1]⟩
    rw [show x + u + -u = x by ring, abs_sub_comm] at this
    exact this.trans_lt hnη

/-- **Uniform convergence theorem**, additive form ([BGT, Theorem 1.2.1], in the form of
[BGT, §1.2.1]): if `h : ℝ → ℝ` is measurable and `h (x + u) - h x → 0` as `x → ∞` for every
`u ∈ ℝ`, then the convergence is uniform in `u` on every compact set `K ⊆ ℝ`. -/
theorem tendstoUniformlyOn_sub_of_measurable (hm : Measurable h)
    (hh : ∀ u : ℝ, Tendsto (fun x => h (x + u) - h x) atTop (𝓝 0)) {K : Set ℝ}
    (hK : IsCompact K) :
    TendstoUniformlyOn (fun x u => h (x + u) - h x) (fun _ => 0) atTop K := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hr
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_Icc hm hh r hε] with x hx u hu
  rw [dist_comm, Real.dist_eq, sub_zero]
  exact hx u (hr hu)

namespace IsRegularlyVarying

variable {f : ℝ → ℝ} {ρ : ℝ}

/-- The additive form `h t = log (f (exp t)) - ρ * t` of a regularly varying function `f` satisfies
`h (t + u) - h t → 0` for every `u`. -/
theorem tendsto_log_comp_exp_sub (hf : IsRegularlyVarying f ρ) (u : ℝ) :
    Tendsto (fun t => (log (f (exp (t + u))) - ρ * (t + u)) - (log (f (exp t)) - ρ * t))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => f (exp u * exp t) / f (exp t)) atTop (𝓝 (exp u ^ ρ)) :=
    (hf.2 _ (exp_pos u)).comp tendsto_exp_atTop
  have h2 := (h1.log (rpow_pos_of_pos (exp_pos u) ρ).ne').sub_const (ρ * u)
  rw [log_rpow (exp_pos u), log_exp, mul_comm, sub_self] at h2
  refine h2.congr' ?_
  have hpos := hf.1
  filter_upwards [tendsto_exp_atTop.eventually hpos,
    (tendsto_exp_atTop.const_mul_atTop (exp_pos u)).eventually hpos] with t ht1 ht2
  rw [exp_add, mul_comm (exp t), log_div ht2.ne' ht1.ne']
  ring

/-- **Uniform convergence theorem** for measurable regularly varying functions
([BGT, Theorem 1.5.2], deduced from [BGT, Theorem 1.2.1]): if `f` is measurable and regularly
varying with index `ρ`, then `f (c * x) / f x → c ^ ρ` uniformly in `c` on every compact subset
`K` of `(0, ∞)`. No monotonicity is assumed. -/
theorem tendstoUniformlyOn_of_measurable (hf : IsRegularlyVarying f ρ) (hm : Measurable f)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  set g : ℝ → ℝ := fun t => log (f (exp t)) - ρ * t with hg
  have hgm : Measurable g :=
    (measurable_log.comp (hm.comp measurable_exp)).sub (measurable_const.mul measurable_id)
  have hK' : IsCompact (log '' K) :=
    hK.image_of_continuousOn (continuousOn_log.mono fun c hc => (ne_of_gt (hK0 hc)))
  have hU := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_sub_of_measurable hgm (tendsto_log_comp_exp_sub hf) hK')
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun c : ℝ => c ^ ρ)
    (fun c hc => (continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (hK0 hc)))).continuousWithinAt)
  obtain ⟨c₀, hc₀⟩ := hKne
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c₀ hc₀)
  obtain ⟨m, hmK, hm'⟩ := hK.exists_isMinOn ⟨c₀, hc₀⟩ continuousOn_id
  have hm0 : 0 < m := hK0 hmK
  obtain ⟨Y, hY⟩ := eventually_atTop.1 hf.1
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set ε' := min 1 (ε / (2 * (M + 1))) with hε'
  have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
  filter_upwards [tendsto_log_atTop.eventually (hU ε' hε'0), eventually_gt_atTop 0,
    eventually_ge_atTop Y, eventually_ge_atTop (Y / m)] with x hx hx0 hxY hxYm c hc
  have hc0 : 0 < c := hK0 hc
  have hfx : 0 < f x := hY x hxY
  have hcx : Y ≤ c * x := by
    rw [div_le_iff₀ hm0] at hxYm
    have := mul_le_mul_of_nonneg_right (hm' hc) hx0.le
    simp only [id] at this
    linarith
  have hfcx : 0 < f (c * x) := hY _ hcx
  have hd := hx (log c) (mem_image_of_mem _ hc)
  rw [dist_comm, Real.dist_eq, sub_zero] at hd
  simp only [hg] at hd
  rw [exp_add, exp_log hx0, exp_log hc0, mul_comm x c] at hd
  set d := log (f (c * x)) - ρ * (log x + log c) - (log (f x) - ρ * log x) with hd_def
  have heq : f (c * x) / f x = c ^ ρ * exp d := by
    rw [rpow_def_of_pos hc0, ← exp_add, hd_def,
      show log c * ρ + (log (f (c * x)) - ρ * (log x + log c) - (log (f x) - ρ * log x)) =
        log (f (c * x)) - log (f x) by ring, exp_sub, exp_log hfcx, exp_log hfx]
  have hd1 : |d| ≤ 1 := hd.le.trans (min_le_left _ _)
  have hexp := abs_exp_sub_one_le hd1
  have hcρ : 0 < c ^ ρ := rpow_pos_of_pos hc0 ρ
  have hcM : c ^ ρ ≤ M := by
    have := hM c hc
    rwa [Real.norm_eq_abs, abs_of_pos hcρ] at this
  rw [Real.dist_eq, heq, show c ^ ρ - c ^ ρ * exp d = -(c ^ ρ * (exp d - 1)) by ring, abs_neg,
    abs_mul, abs_of_pos hcρ]
  calc c ^ ρ * |exp d - 1| ≤ (M + 1) * (2 * |d|) :=
        mul_le_mul (by linarith) hexp (abs_nonneg _) (by linarith)
    _ < (M + 1) * (2 * (ε / (2 * (M + 1)))) := by
        gcongr
        exact hd.trans_le (min_le_right _ _)
    _ = ε := by field_simp

/-- Locally uniform version of `IsRegularlyVarying.tendstoUniformlyOn_of_measurable`. -/
theorem tendstoLocallyUniformlyOn_of_measurable (hf : IsRegularlyVarying f ρ)
    (hm : Measurable f) :
    TendstoLocallyUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop (Ioi 0) :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).2 fun _ hK0 hK =>
    hf.tendstoUniformlyOn_of_measurable hm hK hK0

/-- **Potter bounds** for measurable regularly varying functions ([BGT, Theorem 1.5.6 (iii)]):
if `f` is measurable and regularly varying with index `ρ`, then for every `δ > 0` and `A > 1`
there is `x₀ > 0` such that `f > 0` on `[x₀, ∞)` and
`f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ))` for all `x, y ≥ x₀`.
No monotonicity is assumed (compare `IsRegularlyVarying.potter_bound`). -/
theorem potter_bound_of_measurable (hf : IsRegularlyVarying f ρ) (hfm : Measurable f) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 1 < A) :
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
  have hU := Metric.tendstoUniformlyOn_iff.1
    (hf.tendstoUniformlyOn_of_measurable hfm (isCompact_Icc (a := 1) (b := 2))
      fun _ hc => one_pos.trans_le hc.1) (η * m) (by positivity)
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

/-- **Potter bounds**, two-sided form ([BGT, Theorem 1.5.6 (iii)]): if `f` is measurable and
regularly varying with index `ρ`, then for every `δ > 0` and `A > 1` there is `x₀ > 0` such
that, for all `x, y ≥ x₀`,
`A⁻¹ * min ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) ≤ f y / f x` and
`f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ))`. -/
theorem potter_bounds_of_measurable (hf : IsRegularlyVarying f ρ) (hm : Measurable f)
    {δ A : ℝ} (hδ : 0 < δ) (hA : 1 < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < f x) ∧ ∀ x ≥ x₀, ∀ y ≥ x₀,
      A⁻¹ * min ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) ≤ f y / f x ∧
      f y / f x ≤ A * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) := by
  obtain ⟨x₀, hx₀, hpos, hP⟩ := hf.potter_bound_of_measurable hm hδ hA
  refine ⟨x₀, hx₀, hpos, fun x hx y hy => ⟨?_, hP x hx y hy⟩⟩
  have hx0 : 0 < x := hx₀.trans_le hx
  have hy0 : 0 < y := hx₀.trans_le hy
  have hfx := hpos x hx
  have hfy := hpos y hy
  have hyx : 0 < y / x := div_pos hy0 hx0
  have h := hP y hy x hx
  have e : ∀ p : ℝ, (x / y) ^ p = ((y / x) ^ p)⁻¹ := fun p => by
    rw [← inv_rpow hyx.le, inv_div]
  rw [e, e] at h
  have hA0 : 0 < A := zero_lt_one.trans hA
  have h1 : 0 < (y / x) ^ (ρ + δ) := rpow_pos_of_pos hyx _
  have h2 : 0 < (y / x) ^ (ρ - δ) := rpow_pos_of_pos hyx _
  have hmin : 0 < min ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) := lt_min h1 h2
  have hmax : max ((y / x) ^ (ρ + δ))⁻¹ ((y / x) ^ (ρ - δ))⁻¹ =
      (min ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)))⁻¹ := by
    rcases le_total ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) with hle | hle
    · rw [min_eq_left hle, max_eq_left ((inv_le_inv₀ h2 h1).2 hle)]
    · rw [min_eq_right hle, max_eq_right ((inv_le_inv₀ h1 h2).2 hle)]
  rw [hmax] at h
  have h3 := inv_anti₀ (div_pos hfx hfy) h
  rw [inv_div, mul_inv, inv_inv] at h3
  exact h3

end IsRegularlyVarying

namespace IsSlowlyVarying

variable {L : ℝ → ℝ}

/-- **Uniform convergence theorem** ([BGT, Theorem 1.2.1]): if `L` is measurable and slowly
varying, then `L (c * x) / L x → 1` uniformly in `c` on every compact subset `K` of `(0, ∞)`.
No monotonicity is assumed. -/
theorem tendstoUniformlyOn_of_measurable (hL : IsSlowlyVarying L) (hm : Measurable L)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun x c => L (c * x) / L x) (fun _ => 1) atTop K := by
  simpa using hL.isRegularlyVarying.tendstoUniformlyOn_of_measurable hm hK hK0

/-- Locally uniform version of `IsSlowlyVarying.tendstoUniformlyOn_of_measurable`. -/
theorem tendstoLocallyUniformlyOn_of_measurable (hL : IsSlowlyVarying L) (hm : Measurable L) :
    TendstoLocallyUniformlyOn (fun x c => L (c * x) / L x) (fun _ => 1) atTop (Ioi 0) := by
  simpa using hL.isRegularlyVarying.tendstoLocallyUniformlyOn_of_measurable hm

/-- **Potter bounds** for measurable slowly varying functions ([BGT, Theorem 1.5.6 (i)]): if `L`
is measurable and slowly varying, then for every `δ > 0` and `A > 1` there is `x₀ > 0` such that
`L > 0` on `[x₀, ∞)` and `L y / L x ≤ A * max ((y / x) ^ δ) ((y / x) ^ (-δ))` for all
`x, y ≥ x₀`. -/
theorem potter_bound_of_measurable (hL : IsSlowlyVarying L) (hm : Measurable L) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 1 < A) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < L x) ∧ ∀ x ≥ x₀, ∀ y ≥ x₀,
      L y / L x ≤ A * max ((y / x) ^ δ) ((y / x) ^ (-δ)) := by
  simpa using hL.isRegularlyVarying.potter_bound_of_measurable hm hδ hA

end IsSlowlyVarying

end ExtremeValueTheory
