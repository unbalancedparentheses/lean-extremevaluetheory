/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.Subexponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weibull-type (stretched exponential) tails are subexponential

A distribution with tail `F̄(x) = exp(-x^τ)`, `0 < τ < 1`, is subexponential ([EKM, Example
1.4.3 and Table 1.4.4]; [EKM, Proposition A3.16] via Pitman's criterion). We prove this through a
general dominated-convergence criterion.

## Main results

* `IsSubexponential.of_dominated`: a probability measure `μ` on `[0, ∞)` with positive tail is
  subexponential if it is long-tailed (`F̄(x - t) / F̄(x) → 1` for every `t ≥ 0`),
  `F̄(x / 2)² / F̄(x) → 0`, and the ratios `F̄(x - t) / F̄(x)`, `0 ≤ t ≤ x / 2`, are dominated by a
  `μ`-integrable function of `t`. This is the dominated-convergence form of Pitman's argument
  ([EKM, proof of Proposition A3.16]; Foss–Korshunov–Zachary, Theorem 3.30).
* `IsSubexponential.of_tail_eq_exp_neg_rpow`: **Weibull-type tails** `F̄(x) = exp(-x^τ)`,
  `0 < τ < 1`, are subexponential.

Here [EKM] is Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events for Insurance and
Finance* (Springer, 1997).

## Proof outline

If `X₁ + X₂ > x`, then `X₁ ≤ x/2`, or `X₂ ≤ x/2`, or both exceed `x/2`; by symmetry
`F̄^{*2}(x) ≤ 2 ∫_{t ≤ x/2} F̄(x - t) dμ(t) + F̄(x/2)²`. Dividing by `F̄(x)`, dominated
convergence and long-tailedness give `limsup F̄^{*2}/F̄ ≤ 2`; the bound `≥ 2 - F̄(x)` holds for
every law on `[0, ∞)`.

For `F̄(x) = exp(-x^τ)` and `0 ≤ t ≤ x/2`, Bernoulli's inequality for the concave power gives
`x^τ - (x - t)^τ ≤ τ t (x - t)^{τ - 1} ≤ τ t^τ`, so the ratio is dominated by `exp(τ t^τ)`,
which is `μ`-integrable since `τ < 1`.
-/

open Filter Topology Set Real MeasureTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

open Subexp

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- `(μ ⊗ μ){p | p.1 ≤ a, x < p.1 + p.2} = ∫_{t ≤ a} F̄(x - t) dμ(t)`. -/
private theorem prod_real_fst_le (a x : ℝ) :
    (μ.prod μ).real {p : ℝ × ℝ | p.1 ≤ a ∧ x < p.1 + p.2} = ∫ t in Iic a, tail μ (x - t) ∂μ := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a ∧ x < p.1 + p.2} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
  have hmono : Monotone fun t => μ (Ioi (x - t)) := fun t t' h =>
    measure_mono (Ioi_subset_Ioi (by linarith))
  rw [measureReal_def, Measure.prod_apply hm]
  have : (fun t => μ (Prod.mk t ⁻¹' {p : ℝ × ℝ | p.1 ≤ a ∧ x < p.1 + p.2})) =
      (Iic a).indicator fun t => μ (Ioi (x - t)) := by
    funext t
    by_cases ht : t ≤ a
    · rw [indicator_of_mem (show t ∈ Iic a from ht)]
      congr 1; ext s; simp only [mem_preimage, mem_ofPred_eq, mem_Ioi]
      constructor
      · rintro ⟨-, h⟩; linarith
      · intro h; exact ⟨ht, by linarith⟩
    · rw [indicator_of_notMem (show t ∉ Iic a from ht)]
      convert measure_empty (μ := μ)
      ext s; simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h ht
  rw [this, lintegral_indicator measurableSet_Iic, ← integral_toReal hmono.measurable.aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)]
  rfl

/-- `F̄^{*2}(x) ≤ 2 ∫_{t ≤ x/2} F̄(x - t) dμ(t) + F̄(x/2)²`. -/
private theorem tail_conv_self_le_half (x : ℝ) :
    tail (μ ∗ μ) x ≤ 2 * ∫ t in Iic (x / 2), tail μ (x - t) ∂μ + tail μ (x / 2) ^ 2 := by
  rw [tail, Measure.conv, map_measureReal_apply measurable_add measurableSet_Ioi]
  set A := {p : ℝ × ℝ | p.1 ≤ x / 2 ∧ x < p.1 + p.2}
  set B := {p : ℝ × ℝ | p.2 ≤ x / 2 ∧ x < p.1 + p.2}
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ioi x ⊆
      (A ∪ B) ∪ Ioi (x / 2) ×ˢ Ioi (x / 2) := by
    intro p (hp : x < p.1 + p.2)
    by_cases h1 : p.1 ≤ x / 2
    · exact Or.inl (Or.inl ⟨h1, hp⟩)
    by_cases h2 : p.2 ≤ x / 2
    · exact Or.inl (Or.inr ⟨h2, hp⟩)
    exact Or.inr ⟨not_le.1 h1, not_le.1 h2⟩
  have hB : (μ.prod μ).real B = (μ.prod μ).real A := by
    have hBm : MeasurableSet B := (measurableSet_le measurable_snd measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
    conv_lhs => rw [← Measure.prod_swap]
    rw [map_measureReal_apply measurable_swap hBm]
    congr 1; ext p; simp only [A, B, mem_preimage, mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap]
    rw [add_comm]
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  refine (add_le_add_left (measureReal_union_le _ _) _).trans ?_
  rw [hB, measureReal_prod_prod, prod_real_fst_le, ← tail]
  linarith

namespace IsSubexponential

/-- **A dominated-convergence criterion for subexponentiality** ([EKM, proof of
Proposition A3.16]). Let `μ` be a probability measure on `[0, ∞)` with positive tail `F̄` such
that
* `F̄(x - t) / F̄(x) → 1` for every `t ≥ 0` (long tail),
* `F̄(x - t) / F̄(x) ≤ g(t)` whenever `0 ≤ t ≤ x / 2`, for some `μ`-integrable `g`,
* `F̄(x / 2)² / F̄(x) → 0`.

Then `μ` is subexponential. -/
theorem of_dominated (h0 : μ (Iio 0) = 0) (hpos : ∀ x, 0 < tail μ x)
    (hlong : ∀ t, 0 ≤ t → Tendsto (fun x => tail μ (x - t) / tail μ x) atTop (𝓝 1))
    {g : ℝ → ℝ} (hg : Integrable g μ)
    (hdom : ∀ x t, 0 ≤ t → t ≤ x / 2 → tail μ (x - t) / tail μ x ≤ g t)
    (hsq : Tendsto (fun x => tail μ (x / 2) ^ 2 / tail μ x) atTop (𝓝 0)) :
    IsSubexponential μ := by
  have hae : ∀ᵐ t ∂μ, 0 ≤ t := by
    rw [ae_iff]; simp only [not_le]; exact h0
  -- dominated convergence for `∫_{t ≤ x/2} F̄(x - t) / F̄(x) dμ(t)`
  have hDCT : Tendsto (fun x => ∫ t, (Iic (x / 2)).indicator
      (fun t => tail μ (x - t) / tail μ x) t ∂μ) atTop (𝓝 (∫ _, (1 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence g
      (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) hg ?_
    · exact (((tail_measurable.comp (measurable_const.sub measurable_id)).div_const _).indicator
        measurableSet_Iic).aestronglyMeasurable
    · filter_upwards [hae] with t ht
      have hgt : 0 ≤ g t := by
        have := hdom (2 * t) t ht (by linarith)
        exact (div_nonneg (tail_nonneg _) (hpos _).le).trans this
      by_cases hx : t ≤ x / 2
      · rw [indicator_of_mem (show t ∈ Iic (x / 2) from hx), Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (tail_nonneg _) (hpos _).le)]
        exact hdom x t ht hx
      · rw [indicator_of_notMem (show t ∉ Iic (x / 2) from hx), norm_zero]; exact hgt
    · filter_upwards [hae] with t ht
      refine (hlong t ht).congr' ?_
      filter_upwards [eventually_ge_atTop (2 * t)] with x hx
      rw [indicator_of_mem (show t ∈ Iic (x / 2) from by simp only [mem_Iic]; linarith)]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hDCT
  have hI : ∀ x, ∫ t, (Iic (x / 2)).indicator (fun t => tail μ (x - t) / tail μ x) t ∂μ =
      (∫ t in Iic (x / 2), tail μ (x - t) ∂μ) / tail μ x := by
    intro x; rw [integral_indicator measurableSet_Iic, integral_div]
  simp_rw [hI] at hDCT
  refine ⟨h0, hpos, ?_⟩
  have hup : Tendsto (fun x => 2 * ((∫ t in Iic (x / 2), tail μ (x - t) ∂μ) / tail μ x) +
      tail μ (x / 2) ^ 2 / tail μ x) atTop (𝓝 (2 * 1 + 0)) := (hDCT.const_mul 2).add hsq
  have hlo : Tendsto (fun x => 2 - tail μ x) atTop (𝓝 (2 - 0)) :=
    (tendsto_tail_atTop (μ := μ)).const_sub 2
  rw [mul_one, add_zero] at hup
  rw [sub_zero] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun x => ?_) (fun x => ?_)
  · have := tail_conv_self_ge h0 (le_refl x)
    simp only at this ⊢
    rw [le_div_iff₀ (hpos x)]
    nlinarith [tail_nonneg (μ := μ) (x - x)]
  · have := tail_conv_self_le_half (μ := μ) x
    simp only
    rw [div_le_iff₀ (hpos x)]
    calc tail (μ ∗ μ) x ≤ _ := this
      _ = _ := by
          rw [add_mul, mul_assoc, div_mul_cancel₀ _ (hpos x).ne', div_mul_cancel₀ _ (hpos x).ne']

end IsSubexponential

/-! ### Weibull-type tails -/

section Weibull

variable {τ : ℝ}

/-- For `0 ≤ t ≤ x/2` and `0 < τ ≤ 1`: `x^τ - (x - t)^τ ≤ τ t (x - t)^{τ - 1}`
(Bernoulli's inequality for the concave power), when `t < x`. -/
private theorem rpow_sub_rpow_le (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {x t : ℝ} (ht : 0 ≤ t)
    (htx : t < x) : x ^ τ - (x - t) ^ τ ≤ τ * t * (x - t) ^ (τ - 1) := by
  set y := x - t with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hx : x = y * (1 + t / y) := by field_simp; ring
  have hB := rpow_one_add_le_one_add_mul_self (s := t / y)
    (by have : 0 ≤ t / y := div_nonneg ht hy0.le; linarith) hτ0.le hτ1
  rw [hx, mul_rpow hy0.le (by positivity), rpow_sub hy0, rpow_one]
  have hyτ : 0 ≤ y ^ τ := rpow_nonneg hy0.le τ
  calc y ^ τ * (1 + t / y) ^ τ - y ^ τ ≤ y ^ τ * (1 + τ * (t / y)) - y ^ τ := by
        gcongr
    _ = τ * t * (y ^ τ / y) := by field_simp; ring

private theorem rpow_sub_rpow_nonneg (hτ0 : 0 < τ) {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) :
    0 ≤ x ^ τ - (x - t) ^ τ :=
  sub_nonneg.2 (rpow_le_rpow (by linarith) (by linarith) hτ0.le)

/-- The ratio bound `x^τ - (x - t)^τ ≤ τ t^τ` for `0 ≤ t ≤ x / 2`. -/
private theorem rpow_sub_rpow_le_mul_rpow (hτ0 : 0 < τ) (hτ1 : τ < 1) {x t : ℝ} (ht : 0 ≤ t)
    (htx : t ≤ x / 2) : x ^ τ - (x - t) ^ τ ≤ τ * t ^ τ := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp [zero_rpow hτ0.ne']
  have h1 := rpow_sub_rpow_le hτ0 hτ1.le ht (by linarith)
  have h2 : (x - t) ^ (τ - 1) ≤ t ^ (τ - 1) :=
    rpow_le_rpow_of_nonpos ht' (by linarith) (by linarith)
  calc x ^ τ - (x - t) ^ τ ≤ τ * t * (x - t) ^ (τ - 1) := h1
    _ ≤ τ * t * t ^ (τ - 1) := by gcongr
    _ = τ * t ^ τ := by rw [mul_assoc, ← rpow_one_add' ht'.le (by linarith)]; ring_nf

/-- `∑ₖ exp(-δ k^τ) < ∞` for `δ, τ > 0`. -/
private theorem summable_exp_neg_mul_rpow {δ : ℝ} (hδ : 0 < δ) (hτ0 : 0 < τ) :
    Summable fun k : ℕ => exp (-(δ * (k : ℝ) ^ τ)) := by
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ) ^ τ) ^ (2 / τ) * exp (-δ * (k : ℝ) ^ τ)) atTop
      (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 / τ) δ hδ).comp
      ((tendsto_rpow_atTop hτ0).comp tendsto_natCast_atTop_atTop)
  refine summable_of_isBigO_nat (g := fun k : ℕ => 1 / (k : ℝ) ^ (2 : ℕ))
    (Real.summable_one_div_nat_pow.2 one_lt_two) ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [(tendsto_order.1 hlim).2 1 one_pos, eventually_gt_atTop 0] with k hk hk0
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  rw [← rpow_mul hk0'.le, mul_div_cancel₀ _ hτ0.ne', rpow_two, neg_mul] at hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _), one_mul,
    abs_of_pos (by positivity), le_div_iff₀ (by positivity)]
  linarith

/-- `exp(τ t^τ)` is integrable for a law with tail `exp(-x^τ)` on `[0, ∞)`, `0 < τ < 1`. -/
private theorem integrable_exp_mul_rpow (h0 : μ (Iio 0) = 0) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (htail : ∀ x, 0 ≤ x → tail μ x = exp (-x ^ τ)) :
    Integrable (fun t => exp (τ * t ^ τ)) μ := by
  have hae : ∀ᵐ t ∂μ, 0 ≤ t := by
    rw [ae_iff]; simp only [not_le]; exact h0
  have hmeas : Measurable fun t : ℝ => exp (τ * t ^ τ) := by fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => (exp_pos _).le)]
  set a : ℕ → ℝ := fun k => exp (τ * (k : ℝ) ^ τ) with ha
  -- pointwise bound by a sum over unit bins `(k - 1, k]`
  have hpt : ∀ᵐ t ∂μ, ENNReal.ofReal (exp (τ * t ^ τ)) ≤
      ∑' k : ℕ, (Ioc ((k : ℝ) - 1) k).indicator (fun _ => ENNReal.ofReal (a k)) t := by
    filter_upwards [hae] with t ht
    refine le_trans ?_ (ENNReal.le_tsum ⌈t⌉₊)
    have hmem : t ∈ Ioc ((⌈t⌉₊ : ℝ) - 1) ⌈t⌉₊ :=
      ⟨by linarith [Nat.ceil_lt_add_one ht], Nat.le_ceil t⟩
    rw [indicator_of_mem hmem]
    refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
    gcongr
    exact Nat.le_ceil t
  refine (lintegral_mono_ae hpt).trans_lt ?_
  rw [lintegral_tsum fun k => (aemeasurable_const.indicator measurableSet_Ioc)]
  simp_rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const]
  -- each bin has mass at most `F̄(k - 1)`
  set b : ℕ → ℝ := fun k => a k * tail μ ((k : ℝ) - 1) with hb
  have hbin : ∀ k : ℕ, ENNReal.ofReal (a k) * μ (Ioc ((k : ℝ) - 1) k) ≤ ENNReal.ofReal (b k) := by
    intro k
    rw [hb, ENNReal.ofReal_mul (exp_pos _).le, tail, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    gcongr
    exact Ioc_subset_Ioi_self
  have hb0 : ∀ k, 0 ≤ b k := fun k => mul_nonneg (exp_pos _).le (tail_nonneg _)
  have hbs : Summable b := by
    rw [← summable_nat_add_iff 1]
    have hs := (summable_exp_neg_mul_rpow (δ := 1 - τ) (by linarith) hτ0).mul_left (exp τ)
    refine hs.of_nonneg_of_le (fun k => hb0 _) fun k => ?_
    simp only [hb, ha, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [htail _ (Nat.cast_nonneg k), ← exp_add, ← exp_add]
    refine exp_le_exp.2 ?_
    -- `(k + 1)^τ ≤ k^τ + 1`
    have hsub : ((k : ℝ) + 1) ^ τ ≤ (k : ℝ) ^ τ + 1 := by
      have := NNReal.rpow_add_le_add_rpow (k : ℝ≥0) 1 hτ0.le hτ1.le
      rw [NNReal.one_rpow] at this
      exact_mod_cast this
    nlinarith
  calc ∑' k : ℕ, ENNReal.ofReal (a k) * μ (Ioc ((k : ℝ) - 1) k)
      ≤ ∑' k : ℕ, ENNReal.ofReal (b k) := ENNReal.tsum_le_tsum hbin
    _ = ENNReal.ofReal (∑' k, b k) := (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- **Weibull-type tails are subexponential ([EKM, Example 1.4.3, Proposition A3.16]).** A
probability measure on `[0, ∞)` with tail `F̄(x) = exp(-x^τ)` for `x ≥ 0`, where `0 < τ < 1`,
is subexponential. -/
theorem IsSubexponential.of_tail_eq_exp_neg_rpow (h0 : μ (Iio 0) = 0) (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (htail : ∀ x, 0 ≤ x → tail μ x = exp (-x ^ τ)) : IsSubexponential μ := by
  have hpos : ∀ x, 0 < tail μ x := by
    intro x
    rcases lt_or_ge x 0 with hx | hx
    · rw [tail_of_neg h0 hx]; exact one_pos
    · rw [htail x hx]; exact exp_pos _
  have hratio : ∀ x t, 0 ≤ t → t ≤ x → tail μ (x - t) / tail μ x = exp (x ^ τ - (x - t) ^ τ) := by
    intro x t ht htx
    rw [htail _ (by linarith), htail _ (by linarith), ← exp_sub]
    ring_nf
  refine IsSubexponential.of_dominated h0 hpos (fun t ht => ?_)
    (integrable_exp_mul_rpow h0 hτ0 hτ1 htail) (fun x t ht htx => ?_) ?_
  · -- long tail
    have hlim : Tendsto (fun x => τ * t * (x - t) ^ (τ - 1)) atTop (𝓝 (τ * t * 0)) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - τ) (by linarith)).comp
        (tendsto_atTop_add_const_right _ (-t) tendsto_id)
      simp only [neg_sub] at this
      exact this.const_mul _ |>.congr fun x => by simp [sub_eq_add_neg]
    rw [mul_zero] at hlim
    have hsq : Tendsto (fun x => x ^ τ - (x - t) ^ τ) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [eventually_ge_atTop t] with x hx using rpow_sub_rpow_nonneg hτ0 ht hx
      · filter_upwards [eventually_gt_atTop t] with x hx using rpow_sub_rpow_le hτ0 hτ1.le ht hx
    have := (continuous_exp.tendsto 0).comp hsq
    rw [exp_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop t] with x hx
    rw [Function.comp_apply, hratio x t ht hx]
  · -- domination by `exp(τ t^τ)`
    rw [hratio x t ht (by linarith)]
    exact exp_le_exp.2 (rpow_sub_rpow_le_mul_rpow hτ0 hτ1 ht htx)
  · -- `F̄(x/2)² / F̄(x) = exp(-(2^{1-τ} - 1) x^τ) → 0`
    have hc : 0 < (2 : ℝ) ^ (1 - τ) - 1 := by
      have : (1 : ℝ) < 2 ^ (1 - τ) := one_lt_rpow (by norm_num) (by linarith)
      linarith
    have hlim : Tendsto (fun x : ℝ => exp (-(((2 : ℝ) ^ (1 - τ) - 1) * x ^ τ))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_rpow_atTop hτ0).const_mul_atTop hc)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [htail _ (by linarith), htail _ hx, ← exp_nat_mul, ← exp_sub, div_rpow hx (by norm_num),
      rpow_sub (by norm_num : (0 : ℝ) < 2), rpow_one]
    congr 1
    field_simp
    ring

end Weibull

end ExtremeValueTheory
