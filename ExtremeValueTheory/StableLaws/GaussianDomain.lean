/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.StableIndex
import ExtremeValueTheory.StableLaws.GaussianDomain.Necessity

/-!
# The domain of attraction of the normal law

We complete the converse of the generalized central limit theorem in the Gaussian case: when the
converse index is `2` (equivalently, the truncated second moment `U(x) = E[X² 1{|X| ≤ x}]` is
slowly varying), every non-degenerate weak limit of `(Sₙ - bₙ) / aₙ` is Gaussian, and we prove
the classical criterion of Lévy, Feller and Khinchine: `X` is in the domain of attraction of the
normal law iff `U` is slowly varying ([Feller, Vol. II, §IX.8, Theorem 1 and §XVII.5],
[GK, §35, Theorem 1]).

## Method

Everything goes through the centered characteristic function
`wₙ(t) = φ_{X / aₙ - τₙ}(t) - 1`, `τₙ = E[clip (X / aₙ)]` (`GCLTConverse.wfun`). Under the
Lindeberg-type conditions

* `aₙ → ∞`, `n P(|X| > ε aₙ) → 0` for every `ε > 0`, and
* `n Var (clip (X / aₙ)) → σ²`,

a second-order Taylor bound gives `n wₙ(t) → -σ² t² / 2` (`tendsto_mul_wfun_of_lindeberg`),
hence `(Sₙ - n aₙ τₙ) / aₙ → N(0, σ²)`, and by convergence of types every limit of
`(Sₙ - bₙ) / aₙ` is a shifted `N(0, σ²)`. In the converse, the symmetrized scaling limit
`n E[min (1, (X - X')² / (aₙ x)²)] → K x⁻²` yields the Lindeberg conditions with `σ² = K / 2`:
the tails from `P(|Z| > 2y) ≤ (4 E[min (1, Z² / (2y)²)] - E[min (1, Z² / y²)]) / 3` and the weak
symmetrization inequality, the variance from `2 Var f(X) = E (f(X) - f(X'))²`. For the
sufficiency, slow variation of `U` passes to `E[min (x², (X - X')²)]`, and the normalization
`n E[min (1, (X - X')² / aₙ²)] = 2` (intermediate value theorem) puts us in the same situation.

## Main results

* `tendsto_mul_wfun_of_lindeberg`, `tendsto_map_convPow_gaussianReal_of_lindeberg`,
  `exists_eq_gaussianReal_of_lindeberg`: the CLT under Lindeberg-type conditions and the
  identification of Gaussian limits.
* `lindeberg_of_tendsto_mul_sqRatio_two`: the Lindeberg conditions from the index-`2` converse.
* `exists_eq_gaussianReal_of_tendsto_mul_sqRatio_two`,
  `exists_eq_gaussianReal_of_isRegularlyVarying_truncSecondMoment`: **the Gaussian case of the
  converse**: with converse index `2` (`U` slowly varying), a non-degenerate limit is Gaussian.
* `exists_isStableIndex_or_gaussian_of_tendsto`, `isStable_of_tendsto`: every non-degenerate
  limit of normalized sums is stable — of index `α < 2`, or Gaussian.
* `IsStableIndex.exists_eq_gaussianReal`, `isStableIndex_two_iff`: the stable laws of index `2`
  are exactly the non-degenerate Gaussian laws.
* `exists_tendsto_gaussianReal_of_isRegularlyVarying`: sufficiency, with limit `N(0, 1)`.
* `domainOfAttraction_gaussianReal_iff`: **`X ∈ DOA(N)` iff `μ` is not a Dirac mass and `U` is
  slowly varying**; `domainOfAttraction_isStable_two_iff`, the same with a plain `IsStable`
  limit of `stableIndex 2`.

## File layout

This file holds the final part of the development and imports the others:

* `ExtremeValueTheory.StableLaws.GaussianDomain.Lindeberg`: the CLT under Lindeberg-type conditions
  and the identification of Gaussian limits.
* `ExtremeValueTheory.StableLaws.GaussianDomain.Necessity`: the Lindeberg conditions from the
  index-`2` converse, Gaussian limits, and the stable laws of index `2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

open Subexp GCLT StableIntegral GCLTConverse

section Sufficiency

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- `E[min (x², Z²)] > 0` for `x > 0` unless `Z = 0` a.s. -/
theorem minSqMoment_pos_of_ne_dirac_zero (h : ν ≠ Measure.dirac 0) {x : ℝ} (hx : 0 < x) :
    0 < minSqMoment ν x := by
  rw [minSqMoment]
  refine (integral_pos_iff_support_of_nonneg (fun y => le_min (sq_nonneg _) (sq_nonneg _))
    (integrable_min_sq x)).2 ?_
  have hs : Function.support (fun y : ℝ => min (x ^ 2) (y ^ 2)) = {0}ᶜ := by
    ext y
    simp only [Function.mem_support, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro h rfl; simp at h; exact absurd h (not_lt.2 (sq_nonneg x))
    · intro hy
      exact (lt_min (by positivity) (by positivity)).ne'
  rw [hs]
  by_contra h0
  have hx' : ν {0}ᶜ = 0 := le_antisymm (not_lt.1 h0) zero_le
  apply h
  have h1 : ν {0} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton 0)).1 hx'
  rw [← Measure.restrict_eq_self_of_ae_mem (μ := ν) (s := {0}) (by
    rw [ae_iff]; convert hx' using 2), Measure.restrict_singleton, h1, one_smul]

theorem min_sq_le_two_mul_min_sq_sub (x y z : ℝ) :
    min (x ^ 2) (z ^ 2) ≤ 2 * min (x ^ 2) ((z - y) ^ 2) + 2 * y ^ 2 := by
  rcases le_total ((z - y) ^ 2) (x ^ 2) with h | h
  · rw [min_eq_right h]
    nlinarith [min_le_right (x ^ 2) (z ^ 2), sq_nonneg (z - 2 * y)]
  · rw [min_eq_left h]
    nlinarith [min_le_left (x ^ 2) (z ^ 2), sq_nonneg y, sq_nonneg x]

/-- **Truncated second moments through the symmetrization**: if `P(|X| > u) ≤ 1 / 2` then
`E[min (x², X²)] ≤ 4 E[min (x², (X - X')²)] + 4 u²`. -/
theorem minSqMoment_le_symmLaw {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ}
    (hu : absTail μ u ≤ 1 / 2) (x : ℝ) :
    minSqMoment μ x ≤ 4 * minSqMoment (symmLaw μ) x + 4 * u ^ 2 := by
  set B := {y : ℝ | |y| ≤ u}
  have hB : MeasurableSet B := measurableSet_abs_le' u
  have hBc : μ.real B = 1 - absTail μ u := by
    have : B = {y : ℝ | u < |y|}ᶜ := by ext y; simp [B]
    rw [this, probReal_compl_eq_one_sub (measurableSet_abs_gt u)]; rfl
  set g : ℝ → ℝ := B.indicator (fun _ => (1 : ℝ))
  have hg : ∫ y, g y ∂μ = μ.real B := by
    rw [integral_indicator_const _ hB, smul_eq_mul, mul_one]
  have hi : ∀ (f : ℝ × ℝ → ℝ), Measurable f →
      Integrable (fun p : ℝ × ℝ => min (x ^ 2) (f p ^ 2)) (μ.prod μ) := by
    intro f hf
    refine (integrable_const (x ^ 2)).mono' (by fun_prop) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_left _ _
  have hlhs : ∫ p : ℝ × ℝ, min (x ^ 2) (p.1 ^ 2) * g p.2 ∂(μ.prod μ) =
      minSqMoment μ x * μ.real B := by
    rw [integral_prod_mul (fun y => min (x ^ 2) (y ^ 2)) g, hg, minSqMoment]
  have hrhs : ∫ p : ℝ × ℝ, (2 * min (x ^ 2) ((p.1 - p.2) ^ 2) + 2 * u ^ 2) ∂(μ.prod μ) =
      2 * minSqMoment (symmLaw μ) x + 2 * u ^ 2 := by
    rw [integral_add ((hi _ measurable_fst_sub_snd).const_mul 2) (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, one_smul, minSqMoment, symmLaw,
      integral_map measurable_fst_sub_snd.aemeasurable (by fun_prop)]
  have hgi : Integrable (fun p : ℝ × ℝ => min (x ^ 2) (p.1 ^ 2) * g p.2) (μ.prod μ) := by
    refine Integrable.of_bound (((by fun_prop : Measurable fun p : ℝ × ℝ =>
      min (x ^ 2) (p.1 ^ 2)).mul ((measurable_const.indicator hB).comp
        measurable_snd)).aestronglyMeasurable) (x ^ 2) (ae_of_all _ fun p => ?_)
    simp only [g, Real.norm_eq_abs]
    have h0 : 0 ≤ min (x ^ 2) (p.1 ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    have h1 := min_le_left (x ^ 2) (p.1 ^ 2)
    by_cases h : p.2 ∈ B
    · rw [Set.indicator_of_mem h, mul_one, abs_of_nonneg h0]; exact h1
    · rw [Set.indicator_of_notMem h, mul_zero, abs_zero]; positivity
  have hle : ∫ p : ℝ × ℝ, min (x ^ 2) (p.1 ^ 2) * g p.2 ∂(μ.prod μ) ≤
      ∫ p : ℝ × ℝ, (2 * min (x ^ 2) ((p.1 - p.2) ^ 2) + 2 * u ^ 2) ∂(μ.prod μ) := by
    refine integral_mono hgi (((hi _ measurable_fst_sub_snd).const_mul 2).add
      (integrable_const _)) fun p => ?_
    simp only [g]
    by_cases h : p.2 ∈ B
    · rw [Set.indicator_of_mem h, mul_one]
      have h1 := min_sq_le_two_mul_min_sq_sub x p.2 p.1
      have h2 : p.2 ^ 2 ≤ u ^ 2 := by
        have : |p.2| ≤ u := h
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      linarith
    · rw [Set.indicator_of_notMem h, mul_zero]
      positivity
  rw [hlhs, hrhs, hBc] at hle
  have hZ := minSqMoment_nonneg (μ := μ) x
  nlinarith

/-- The elementary Tauberian step in the slowly varying case: if `x² P(|X| > x) / Z(x) → 0`
then `Z(x) = E[min (x², X²)]` is slowly varying. -/
theorem isRegularlyVarying_minSqMoment_zero (hZpos : ∀ᶠ x in atTop, 0 < minSqMoment ν x)
    (hr : Tendsto (fun x => x ^ 2 * absTail ν x / minSqMoment ν x) atTop (𝓝 0)) :
    IsRegularlyVarying (minSqMoment ν) 0 := by
  have hge : ∀ l : ℝ, 1 ≤ l →
      Tendsto (fun x => minSqMoment ν (l * x) / minSqMoment ν x) atTop (𝓝 1) := by
    intro l hl
    have hup : Tendsto (fun x => 1 + (l ^ 2 - 1) * (x ^ 2 * absTail ν x / minSqMoment ν x))
        atTop (𝓝 (1 + (l ^ 2 - 1) * 0)) := (hr.const_mul _).const_add 1
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hZpos, eventually_ge_atTop 0] with x hx hx0
      rw [le_div_iff₀ hx, one_mul]
      exact minSqMoment_mono hx0 (le_mul_of_one_le_left hx0 hl)
    · filter_upwards [hZpos, eventually_ge_atTop 0] with x hx hx0
      have := minSqMoment_sub_le (μ := ν) hx0 hl
      rw [div_le_iff₀ hx, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hx.ne']
      nlinarith
  refine ⟨hZpos, fun l hl => ?_⟩
  rw [Real.rpow_zero]
  rcases le_total 1 l with h1 | h1
  · exact hge l h1
  · have h := (hge l⁻¹ (one_le_inv₀ hl |>.2 h1)).comp (tendsto_id.const_mul_atTop hl)
    have h' := h.inv₀ one_ne_zero
    rw [inv_one] at h'
    refine h'.congr' ?_
    filter_upwards with x
    simp only [Function.comp, id, inv_div]
    rw [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]

/-- **Slow variation passes to the symmetrization**: if `μ` is not a Dirac mass and
`U(x) = E[X² 1{|X| ≤ x}]` is slowly varying, then so is `E[min (x², (X - X')²)]`. -/
theorem isRegularlyVarying_minSqMoment_symmLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hnd : ∀ x, μ ≠ Measure.dirac x) (hU : IsRegularlyVarying (truncSecondMoment μ) 0) :
    IsRegularlyVarying (minSqMoment (symmLaw μ)) 0 := by
  have hZ : IsRegularlyVarying (minSqMoment μ) 0 :=
    hU.of_tendsto_div (tendsto_minSqMoment_div_truncSecondMoment (by norm_num) hU)
      (by norm_num)
  have hr := tendsto_sq_mul_absTail_div_minSqMoment hZ
  rw [zero_div] at hr
  have hρpos : ∀ x, 0 < x → 0 < minSqMoment (symmLaw μ) x :=
    fun x hx => minSqMoment_pos_of_ne_dirac_zero (symmLaw_ne_dirac hnd) hx
  obtain ⟨u₀, hu₀⟩ := (eventually_atTop.1 ((tendsto_order.1 (tendsto_absTail_zero (μ := μ))).2
    (1 / 2) (by norm_num)))
  have hu : absTail μ u₀ ≤ 1 / 2 := (hu₀ u₀ le_rfl).le
  set c₀ := minSqMoment (symmLaw μ) 1
  have hc₀ : 0 < c₀ := hρpos 1 one_pos
  set C := 4 + 4 * u₀ ^ 2 / c₀
  have hC : 0 < C := by positivity
  have hcomp : ∀ x, 1 ≤ x → minSqMoment μ x ≤ C * minSqMoment (symmLaw μ) x := by
    intro x hx
    have h1 := minSqMoment_le_symmLaw hu x
    have h2 : c₀ ≤ minSqMoment (symmLaw μ) x := minSqMoment_mono zero_le_one hx
    have h3 : 4 * u₀ ^ 2 ≤ 4 * u₀ ^ 2 / c₀ * minSqMoment (symmLaw μ) x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    simp only [C]; nlinarith
  have hZρpos : ∀ᶠ x in atTop, 0 < minSqMoment (symmLaw μ) x :=
    (eventually_gt_atTop 0).mono fun x hx => hρpos x hx
  refine isRegularlyVarying_minSqMoment_zero hZρpos ?_
  have hhalf : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hr2 := (hr.comp hhalf).const_mul (12 * C)
  rw [mul_zero] at hr2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr2 ?_ ?_
  · filter_upwards [hZρpos] with x hx
    exact div_nonneg (mul_nonneg (sq_nonneg _) measureReal_nonneg) hx.le
  · filter_upwards [eventually_ge_atTop 2, hhalf.eventually hZ.1, hZρpos] with x hx hZh hZr
    simp only [Function.comp]
    set A := absTail μ (x / 2)
    set Zh := minSqMoment μ (x / 2)
    set Zr := minSqMoment (symmLaw μ) x
    have hA0 : 0 ≤ A := measureReal_nonneg
    have hA1 : A ≤ 1 := absTail_le_one _
    have hTr : absTail (symmLaw μ) x ≤ 3 * A := by
      have h := absTail_symmLaw_le (μ := μ) (s := x / 2) (u := x / 2)
      rw [add_halves] at h
      nlinarith
    have hZle : Zh ≤ C * Zr :=
      (minSqMoment_mono (by linarith) (by linarith)).trans (hcomp x (by linarith))
    rw [div_le_iff₀ hZr]
    have hq : (x / 2) ^ 2 * A / Zh * Zr ≥ (x / 2) ^ 2 * A / C := by
      rw [div_mul_eq_mul_div, ge_iff_le, div_le_div_iff₀ hC hZh]
      have := mul_le_mul_of_nonneg_left hZle (mul_nonneg (sq_nonneg (x / 2)) hA0)
      nlinarith
    have hq' : 12 * C * ((x / 2) ^ 2 * A / Zh) * Zr ≥ 3 * x ^ 2 * A := by
      have : 12 * C * ((x / 2) ^ 2 * A / Zh) * Zr = 12 * C * ((x / 2) ^ 2 * A / Zh * Zr) := by
        ring
      rw [this]
      have h12 : 12 * C * ((x / 2) ^ 2 * A / C) = 3 * x ^ 2 * A := by field_simp; ring
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hTr (sq_nonneg x)]

theorem continuousOn_sqRatio : ContinuousOn (sqRatio ν) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀' : (0 : ℝ) < x₀ := hx₀
  refine ContinuousAt.continuousWithinAt ?_
  have hev : ∀ᶠ x in 𝓝 x₀, 0 < x := isOpen_Ioi.mem_nhds hx₀'
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝 x₀)
    (F := fun x y => y ^ 2 / max (y ^ 2) (x ^ 2)) (f := fun y => y ^ 2 / max (y ^ 2) (x₀ ^ 2))
    (fun _ => (1 : ℝ))
    (hev.mono fun x hx => (integrable_sq_div_max hx.ne').aestronglyMeasurable)
    (hev.mono fun x hx => ae_of_all _ fun y => by
      have hM : 0 < max (y ^ 2) (x ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hM.le), div_le_one hM]
      exact le_max_left _ _)
    (integrable_const _)
    (ae_of_all _ fun y => by
      have hM : 0 < max (y ^ 2) (x₀ ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      have hc : ContinuousAt (fun x : ℝ => y ^ 2 / max (y ^ 2) (x ^ 2)) x₀ :=
        continuousAt_const.div ((continuous_const.max (continuous_pow 2)).continuousAt) hM.ne'
      exact hc.tendsto)
  exact h

theorem tendsto_sqRatio_atTop : Tendsto (sqRatio ν) atTop (𝓝 0) := by
  have hev : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := atTop)
    (F := fun x y => y ^ 2 / max (y ^ 2) (x ^ 2)) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (hev.mono fun x hx => (integrable_sq_div_max hx.ne').aestronglyMeasurable)
    (hev.mono fun x hx => ae_of_all _ fun y => by
      have hM : 0 < max (y ^ 2) (x ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hM.le), div_le_one hM]
      exact le_max_left _ _)
    (integrable_const _)
    (ae_of_all _ fun y => by
      have h1 : Tendsto (fun x : ℝ => y ^ 2 / x ^ 2) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
      · exact Eventually.of_forall fun x => div_nonneg (sq_nonneg _)
          (le_max_of_le_left (sq_nonneg _))
      · filter_upwards [hev] with x hx
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (le_max_right _ _))
  simp only [integral_zero] at h
  exact h

/-- **A normalizing sequence for the Gaussian case**: if `sqRatio ν` is positive, there are
`aₙ > 0` with `n E[min (1, Z² / aₙ²)] = c` for all large `n` (intermediate value theorem). -/
theorem exists_seq_mul_sqRatio_eq {c : ℝ} (hc : 0 < c) (hpos : ∀ x, 0 < x → 0 < sqRatio ν x) :
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio ν (a n) = c := by
  set s₀ := sqRatio ν 1
  have hs₀ : 0 < s₀ := hpos 1 one_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (c / s₀)
  have hex : ∀ n : ℕ, ∃ y : ℝ, 0 < y ∧ (N ≤ n → (n : ℝ) * sqRatio ν y = c) := by
    intro n
    by_cases hn : N ≤ n
    · have hn0 : (0 : ℝ) < n := by
        have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hc.le hs₀.le) hN
        exact this.trans_le (by exact_mod_cast hn)
      have hcn : 0 < c / n := div_pos hc hn0
      have hcn1 : c / n ≤ s₀ := by
        rw [div_le_iff₀ hn0]
        rw [div_lt_iff₀ hs₀] at hN
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      obtain ⟨x₁, hx₁⟩ := (eventually_atTop.1 ((tendsto_order.1 (tendsto_sqRatio_atTop
        (ν := ν))).2 _ hcn))
      set x₂ := max x₁ 1
      have hx₂ : sqRatio ν x₂ ≤ c / n := (hx₁ x₂ (le_max_left _ _)).le
      have hIVT := intermediate_value_Icc' (le_max_right x₁ 1 : (1 : ℝ) ≤ x₂)
        ((continuousOn_sqRatio (ν := ν)).mono fun x hx => lt_of_lt_of_le one_pos hx.1)
      obtain ⟨y, hy, hyc⟩ := hIVT ⟨hx₂, hcn1⟩
      refine ⟨y, lt_of_lt_of_le one_pos hy.1, fun _ => ?_⟩
      rw [hyc]; field_simp
    · exact ⟨1, one_pos, fun h => absurd h hn⟩
  choose a ha hac using hex
  exact ⟨a, ha, (eventually_ge_atTop N).mono fun n hn => hac n hn⟩

/-- **Sufficiency for the domain of attraction of the normal law**
([Feller, Vol. II, §IX.8, Theorem 1 and §XVII.5], [GK, §35, Theorem 1], Lévy, Khinchine).
If `μ` is not a Dirac mass and `U(x) = E[X² 1{|X| ≤ x}]` is slowly varying, there are
`aₙ > 0` such that `(Sₙ - n aₙ τₙ) / aₙ → N(0, 1)`, `τₙ = E[clip (X / aₙ)]`. -/
theorem exists_tendsto_gaussianReal_of_isRegularlyVarying {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hnd : ∀ x, μ ≠ Measure.dirac x)
    (hU : IsRegularlyVarying (truncSecondMoment μ) 0) :
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - n * a n * ctr μ a n)), inferInstance⟩) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have hZρ := isRegularlyVarying_minSqMoment_symmLaw hnd hU
  have hpos : ∀ x, 0 < x → 0 < sqRatio (symmLaw μ) x := by
    intro x hx
    rw [sqRatio_eq_div hx.ne']
    exact div_pos (minSqMoment_pos_of_ne_dirac_zero (symmLaw_ne_dirac hnd) hx) (by positivity)
  obtain ⟨a, ha, hea⟩ := exists_seq_mul_sqRatio_eq (ν := symmLaw μ) two_pos hpos
  have hS : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n)) atTop (𝓝 2) :=
    tendsto_const_nhds.congr' (hea.mono fun n hn => hn.symm)
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_of_tendsto_mul_comp (T := sqRatio (symmLaw μ)) (L := fun _ => 2)
      sqRatio_antitoneOn hpos ha hS
  have hRV : IsRegularlyVarying (sqRatio (symmLaw μ)) (-2) := by
    have := hZρ.mul (IsRegularlyVarying.rpow_id (-2))
    rw [zero_add] at this
    refine this.congr ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqRatio_eq_div hx.ne', Real.rpow_neg hx.le, Real.rpow_two, div_eq_mul_inv]
  have hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x))
      atTop (𝓝 (2 * x ^ (-(2 : ℝ)))) := fun x hx =>
    tendsto_mul_comp_mul_of_tendsto hRV hatop hS hx
  obtain ⟨-, hT, hV⟩ := lindeberg_of_tendsto_mul_sqRatio_two ha two_pos hL
  refine ⟨a, ha, ?_⟩
  have h := tendsto_map_convPow_gaussianReal_of_lindeberg ha hatop hT hV
  have e : ((2 : ℝ) / 2).toNNReal = 1 := by norm_num
  rwa [e] at h

end Sufficiency

section Iff

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- A limit of normalized sums of a Dirac law has a characteristic function of modulus `1`. -/
theorem norm_charFun_eq_one_of_tendsto_dirac {c : ℝ} {a b : ℕ → ℝ} {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow (Measure.dirac c) n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop
      (𝓝 ν)) (t : ℝ) : ‖charFun (ν : Measure ℝ) t‖ = 1 := by
  have h := ((continuous_norm.tendsto _).comp
    (((continuous_charFun_probabilityMeasure t).tendsto ν).comp hconv))
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr fun n => ?_)
  simp only [Function.comp, ProbabilityMeasure.coe_mk]
  have e : (fun x => (a n)⁻¹ * (x - b n)) = fun x => (a n)⁻¹ * x + (-((a n)⁻¹ * b n)) := by
    funext x; ring
  rw [e, charFun_map_mul_add, charFun_convPow, norm_mul, norm_pow, charFun_dirac,
    show (((-((a n)⁻¹ * b n) : ℝ) : ℂ) * (t : ℂ) * Complex.I) =
      ((-((a n)⁻¹ * b n) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]
  simp [Complex.norm_exp]

/-- **The domain of attraction of the normal law** ([Feller, Vol. II, §IX.8, Theorem 1 and
§XVII.5, Theorem 2], [GK, §35, Theorem 1]; Lévy, Feller, Khinchine). The normalized sums
`(X₁ + ⋯ + Xₙ - bₙ) / aₙ` converge weakly to a non-degenerate Gaussian law for some `aₙ > 0`
and `bₙ` iff `μ` is not a Dirac mass and the truncated second moment
`U(x) = E[X² 1{|X| ≤ x}]` is slowly varying. In that case one can take the limit `N(0, 1)`
(`exists_tendsto_gaussianReal_of_isRegularlyVarying`). -/
theorem domainOfAttraction_gaussianReal_iff :
    (∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ b : ℕ → ℝ, ∃ m : ℝ, ∃ v : ℝ≥0, v ≠ 0 ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop
        (𝓝 ⟨gaussianReal m v, inferInstance⟩)) ↔
      (∀ x, μ ≠ Measure.dirac x) ∧ IsRegularlyVarying (truncSecondMoment μ) 0 := by
  constructor
  · rintro ⟨a, ha, b, m, v, hv, hconv⟩
    have hnd' : ∀ x, (gaussianReal m v : Measure ℝ) ≠ Measure.dirac x :=
      (isStable_gaussianReal m hv).ne_dirac
    refine ⟨fun c hc => ?_, ?_⟩
    · subst hc
      have h1 := norm_charFun_eq_one_of_tendsto_dirac hconv 1
      have h2 := norm_charFun_gaussianReal_one_lt m hv
      simp only [ProbabilityMeasure.coe_mk] at h1
      linarith
    · rcases exists_isStableIndex_or_gaussian_of_tendsto (ν := ⟨gaussianReal m v, inferInstance⟩)
        ha hnd' hconv with ⟨α, -, hlt, -, hα⟩ | ⟨hU, -⟩
      · have := hα.index_eq (isStableIndex_two_gaussianReal m hv)
        linarith
      · exact hU
  · rintro ⟨hnd, hU⟩
    obtain ⟨a, ha, h⟩ := exists_tendsto_gaussianReal_of_isRegularlyVarying hnd hU
    exact ⟨a, ha, _, 0, 1, one_ne_zero, h⟩

/-- **Domain of attraction of a stable law of index `2`**, with a plain `IsStable` limit: the
limit is stable with `stableIndex = 2` iff `μ` is not a Dirac mass and `U` is slowly
varying. -/
theorem domainOfAttraction_isStable_two_iff :
    (∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ b : ℕ → ℝ, ∃ ν : ProbabilityMeasure ℝ,
      IsStable ν ∧ stableIndex ν = 2 ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) ↔
      (∀ x, μ ≠ Measure.dirac x) ∧ IsRegularlyVarying (truncSecondMoment μ) 0 := by
  rw [← domainOfAttraction_gaussianReal_iff]
  constructor
  · rintro ⟨a, ha, b, ν, hs, hi, hconv⟩
    obtain ⟨m, v, hv, hν⟩ := (isStableIndex_iff_stableIndex_eq.2 ⟨hs, hi⟩).exists_eq_gaussianReal
    refine ⟨a, ha, b, m, v, hv, ?_⟩
    have : ν = ⟨gaussianReal m v, inferInstance⟩ := Subtype.ext hν
    rwa [← this]
  · rintro ⟨a, ha, b, m, v, hv, hconv⟩
    have h2 := isStableIndex_two_gaussianReal m hv
    exact ⟨a, ha, b, ⟨gaussianReal m v, inferInstance⟩, h2.1, h2.stableIndex_eq, hconv⟩

end Iff

end ExtremeValueTheory
