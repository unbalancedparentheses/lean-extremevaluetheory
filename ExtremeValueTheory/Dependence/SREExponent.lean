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

section Generic

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  {A : α → ℝ}

theorem integrable_abs_rpow_of_le (hAm : Measurable A) {S : ℝ} (hSi : Integrable (fun p => |A p| ^ S) μ)
    {t : ℝ} (ht : 0 ≤ t) (htS : t ≤ S) : Integrable (fun p => |A p| ^ t) μ :=
  ((integrable_const 1).add hSi).mono' (by fun_prop) (ae_of_all _ fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
    exact rpow_le_one_add_rpow (abs_nonneg _) ht htS)

/-- If `E log |A| < 0` (and `A ≠ 0` a.s.), then `E|A|^t < 1` for some small `t > 0`: the right
derivative of `t ↦ E|A|^t` at `0` is `E log |A|`. -/
theorem exists_integral_abs_rpow_lt_one (hAm : Measurable A) (hA0 : ∀ᵐ p ∂μ, A p ≠ 0)
    (hA : Integrable (fun p => log |A p|) μ) (hneg : ∫ p, log |A p| ∂μ < 0)
    {S : ℝ} (hS : 0 < S) (hSi : Integrable (fun p => |A p| ^ S) μ) :
    ∃ t ∈ Ioo 0 S, ∫ p, |A p| ^ t ∂μ < 1 := by
  set F : ℝ → α → ℝ := fun t p => (|A p| ^ t - 1) / t
  have hFS : Integrable (F S) μ := ((hSi.sub (integrable_const 1)).div_const S)
  have hlim : Tendsto (fun t => ∫ p, F t p ∂μ) (𝓝[>] 0) (𝓝 (∫ p, log |A p| ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => abs (log |A p|) + abs (F S p))
      (Eventually.of_forall fun t =>
      ((((continuous_abs.measurable.comp hAm :
        Measurable fun p => |A p|).pow_const t).sub_const 1).div_const t).aestronglyMeasurable) ?_ (hA.abs.add hFS.abs) ?_
    · filter_upwards [Ioo_mem_nhdsGT hS] with t ht
      filter_upwards [hA0] with p hp
      have hp' : 0 < |A p| := abs_pos.2 hp
      have h1 := log_le_rpow_sub_one_div hp' ht.1
      have h2 := rpow_sub_one_div_le hp' ht.1 ht.2.le
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> [linarith [neg_abs_le (log |A p|), abs_nonneg (F S p)];
        linarith [le_abs_self (F S p), abs_nonneg (log |A p|)]]
    · filter_upwards [hA0] with p hp
      have hp' : 0 < |A p| := abs_pos.2 hp
      have hd : HasDerivAt (fun t => exp (log |A p| * t)) (exp (log |A p| * 0) * (log |A p| * 1)) 0 :=
        ((hasDerivAt_id 0).const_mul (log |A p|)).exp
      simp only [mul_zero, exp_zero, mul_one, one_mul] at hd
      refine hd.tendsto_slope_zero_right.congr fun t => ?_
      simp only [F, zero_add, smul_eq_mul, mul_zero, exp_zero, rpow_def_of_pos hp']
      ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ p, F t p ∂μ < 0 := hlim.eventually (gt_mem_nhds hneg)
  obtain ⟨t, h1, h2⟩ := (hev.and (Ioo_mem_nhdsGT hS)).exists
  refine ⟨t, h2, ?_⟩
  have hti := integrable_abs_rpow_of_le hAm hSi h2.1.le h2.2.le
  have : ∫ p, F t p ∂μ = ((∫ p, |A p| ^ t ∂μ) - 1) / t := by
    simp only [F]
    rw [integral_div, integral_sub hti (integrable_const 1), integral_const, probReal_univ,
      one_smul]
  rw [this, div_neg_iff] at h1
  rcases h1 with h | h
  · linarith [h.2, h2.1]
  · linarith [h.1]

/-- `t ↦ E|A|^t` is continuous on `[t₀, S]`, `t₀ > 0`, when `E|A|^S < ∞`. -/
theorem continuousOn_integral_abs_rpow (hAm : Measurable A) {S t₀ : ℝ} (ht₀ : 0 < t₀)
    (hSi : Integrable (fun p => |A p| ^ S) μ) :
    ContinuousOn (fun t => ∫ p, |A p| ^ t ∂μ) (Icc t₀ S) := by
  refine continuousOn_of_dominated (bound := fun p => 1 + |A p| ^ S)
    (fun t _ => (((continuous_abs.measurable.comp hAm :
      Measurable fun p => |A p|).pow_const t).aestronglyMeasurable))
    (fun t ht => ae_of_all _ fun p => ?_) ((integrable_const 1).add hSi)
    (ae_of_all _ fun p => fun t ht => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
    exact rpow_le_one_add_rpow (abs_nonneg _) (ht₀.le.trans ht.1) ht.2
  · exact (continuousAt_const_rpow' (ht₀.trans_le ht.1).ne').continuousWithinAt

/-- **Existence of the Kesten exponent** ([BDM16, §2.4]; [EKM, §8.4]): if `A ≠ 0` a.s.,
`E log |A| < 0` and `E|A|^S > 1` for some `S > 0` with `E|A|^S < ∞`, then `E|A|^κ = 1` for some
`κ ∈ (0, S)`. -/
theorem exists_integral_abs_rpow_eq_one (hAm : Measurable A) (hA0 : ∀ᵐ p ∂μ, A p ≠ 0)
    (hA : Integrable (fun p => log |A p|) μ) (hneg : ∫ p, log |A p| ∂μ < 0)
    {S : ℝ} (hS : 0 < S) (hSi : Integrable (fun p => |A p| ^ S) μ)
    (hS1 : 1 < ∫ p, |A p| ^ S ∂μ) :
    ∃ κ ∈ Ioo 0 S, ∫ p, |A p| ^ κ ∂μ = 1 := by
  obtain ⟨t, ht, ht1⟩ := exists_integral_abs_rpow_lt_one hAm hA0 hA hneg hS hSi
  obtain ⟨κ, hκ, hκ1⟩ := intermediate_value_Icc ht.2.le
    (continuousOn_integral_abs_rpow hAm ht.1 hSi) ⟨ht1.le, hS1.le⟩
  refine ⟨κ, ⟨ht.1.trans_le hκ.1, lt_of_le_of_ne hκ.2 ?_⟩, hκ1⟩
  rintro rfl
  linarith

end Generic

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- The `ℝ≥0∞`-valued moment `∫⁻ ‖A‖ₑ^κ` equals `1` when the real one does. -/
theorem lintegral_enorm_rpow_eq_one_of_integral {κ : ℝ} (hκ : 0 ≤ κ)
    (hi : Integrable (fun p : ℝ × ℝ => |p.1| ^ κ) ν) (h1 : ∫ p, |p.1| ^ κ ∂ν = 1) :
    ∫⁻ p, ‖p.1‖ₑ ^ κ ∂ν = 1 := by
  rw [lintegral_congr fun p : ℝ × ℝ => enorm_rpow_eq_ofReal p.1 hκ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun p => rpow_nonneg (abs_nonneg _) _), h1, ENNReal.ofReal_one]

/-- **Uniqueness of the Kesten exponent**: if `|A|` is not a.s. `1`, there is at most one
`κ > 0` with `E|A|^κ = 1`. -/
theorem kesten_exponent_unique (hnd : ¬ ∀ᵐ p ∂ν, |p.1| = 1) {κ κ' : ℝ} (hκ : 0 < κ)
    (hκ' : 0 < κ') (h1 : ∫⁻ p, ‖p.1‖ₑ ^ κ ∂ν = 1) (h1' : ∫⁻ p, ‖p.1‖ₑ ^ κ' ∂ν = 1) :
    κ = κ' := by
  rcases lt_trichotomy κ κ' with h | h | h
  · exact absurd h1' (one_lt_lintegral_enorm_rpow hκ h1 hnd h).ne'
  · exact h
  · exact absurd h1 (one_lt_lintegral_enorm_rpow hκ' h1' hnd h).ne'

end SRE

end ExtremeValueTheory
