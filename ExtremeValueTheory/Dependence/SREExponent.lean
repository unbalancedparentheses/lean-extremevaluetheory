/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.SREMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence and uniqueness of the Kesten exponent

skeleton
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped ENNReal

namespace ExtremeValueTheory

namespace SRE

/-- `log a ≤ (a^t - 1) / t` for `a > 0`, `t > 0`. -/
theorem log_le_rpow_sub_one_div {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    log a ≤ (a ^ t - 1) / t := by
  rw [le_div_iff₀ ht, rpow_def_of_pos ha]
  linarith [add_one_le_exp (log a * t)]

/-- The slopes `t ↦ (a^t - 1) / t` are monotone (convexity of `t ↦ a^t`). -/
theorem rpow_sub_one_div_le {a t S : ℝ} (ha : 0 < a) (ht : 0 < t) (htS : t ≤ S) :
    (a ^ t - 1) / t ≤ (a ^ S - 1) / S := by
  have hS : 0 < S := ht.trans_le htS
  have hc := convexOn_exp.2 (mem_univ (log a * S)) (mem_univ 0)
    (div_nonneg ht.le hS.le) (sub_nonneg.2 ((div_le_one hS).2 htS)) (add_sub_cancel _ _)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hc
  rw [div_le_div_iff₀ ht hS, rpow_def_of_pos ha, rpow_def_of_pos ha]
  have he : t / S * (log a * S) = log a * t := by field_simp
  rw [he] at hc
  have := mul_le_mul_of_nonneg_left hc hS.le
  have e2 : S * (t / S * exp (log a * S) + (1 - t / S)) = t * exp (log a * S) + S - t := by
    field_simp; ring
  rw [e2] at this
  nlinarith

theorem rpow_le_one_add_rpow {x t S : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (htS : t ≤ S) :
    x ^ t ≤ 1 + x ^ S := by
  rcases le_total x 1 with h | h
  · linarith [rpow_le_one hx h ht, rpow_nonneg hx S]
  · linarith [rpow_le_rpow_of_exponent_le h htS]

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]

theorem integrable_abs_rpow_of_le {S : ℝ} (hSi : Integrable (fun p : ℝ × ℝ => |p.1| ^ S) ν)
    {t : ℝ} (ht : 0 ≤ t) (htS : t ≤ S) : Integrable (fun p : ℝ × ℝ => |p.1| ^ t) ν :=
  ((integrable_const 1).add hSi).mono' (by fun_prop) (ae_of_all _ fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
    exact rpow_le_one_add_rpow (abs_nonneg _) ht htS)

/-- If `E log |A| < 0` (and `A ≠ 0` a.s.), then `E|A|^t < 1` for some small `t > 0`: the right
derivative of `t ↦ E|A|^t` at `0` is `E log |A|`. -/
theorem exists_integral_abs_rpow_lt_one (hA0 : ∀ᵐ p ∂ν, p.1 ≠ 0)
    (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν) (hneg : ∫ p, log |p.1| ∂ν < 0)
    {S : ℝ} (hS : 0 < S) (hSi : Integrable (fun p : ℝ × ℝ => |p.1| ^ S) ν) :
    ∃ t ∈ Ioo 0 S, ∫ p, |p.1| ^ t ∂ν < 1 := by
  set F : ℝ → ℝ × ℝ → ℝ := fun t p => (|p.1| ^ t - 1) / t
  have hFS : Integrable (F S) ν := ((hSi.sub (integrable_const 1)).div_const S)
  have hlim : Tendsto (fun t => ∫ p, F t p ∂ν) (𝓝[>] 0) (𝓝 (∫ p, log |p.1| ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => abs (log |p.1|) + abs (F S p))
      (Eventually.of_forall fun t =>
      ((((continuous_abs.measurable.comp measurable_fst :
        Measurable fun p : ℝ × ℝ => |p.1|).pow_const t).sub_const 1).div_const t).aestronglyMeasurable) ?_ (hA.abs.add hFS.abs) ?_
    · filter_upwards [Ioo_mem_nhdsGT hS] with t ht
      filter_upwards [hA0] with p hp
      have hp' : 0 < |p.1| := abs_pos.2 hp
      have h1 := log_le_rpow_sub_one_div hp' ht.1
      have h2 := rpow_sub_one_div_le hp' ht.1 ht.2.le
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> [linarith [neg_abs_le (log |p.1|), abs_nonneg (F S p)];
        linarith [le_abs_self (F S p), abs_nonneg (log |p.1|)]]
    · filter_upwards [hA0] with p hp
      have hp' : 0 < |p.1| := abs_pos.2 hp
      have hd : HasDerivAt (fun t => exp (log |p.1| * t)) (exp (log |p.1| * 0) * (log |p.1| * 1)) 0 :=
        ((hasDerivAt_id 0).const_mul (log |p.1|)).exp
      simp only [mul_zero, exp_zero, mul_one, one_mul] at hd
      refine hd.tendsto_slope_zero_right.congr fun t => ?_
      simp only [F, zero_add, smul_eq_mul, mul_zero, exp_zero, rpow_def_of_pos hp']
      ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ p, F t p ∂ν < 0 := hlim.eventually (gt_mem_nhds hneg)
  obtain ⟨t, h1, h2⟩ := (hev.and (Ioo_mem_nhdsGT hS)).exists
  refine ⟨t, h2, ?_⟩
  have hti := integrable_abs_rpow_of_le hSi h2.1.le h2.2.le
  have : ∫ p, F t p ∂ν = ((∫ p, |p.1| ^ t ∂ν) - 1) / t := by
    simp only [F]
    rw [integral_div, integral_sub hti (integrable_const 1), integral_const, probReal_univ,
      one_smul]
  rw [this, div_neg_iff] at h1
  rcases h1 with h | h
  · linarith [h.2, h2.1]
  · linarith [h.1]

end SRE

end ExtremeValueTheory
