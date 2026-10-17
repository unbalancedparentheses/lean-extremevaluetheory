/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Karamata's theorem for tail integrals

Let `F : ℝ → ℝ` be antitone and regularly varying at `+∞` with index `-α`, where `α > 1`
(typically `F` is the survival function `1 - G` of a distribution function `G` in the domain of
attraction of the Fréchet law). Karamata's theorem ([BGT, Proposition 1.5.10], the "direct half"
of Karamata's theorem, [BGT, Theorem 1.5.11]) states that

  `(∫ t in Ioi x, F t) / (x * F x) → 1 / (α - 1)` as `x → ∞`.

Here [BGT] is Bingham, Goldie and Teugels, *Regular Variation* (Cambridge University Press,
1987).

## Main results

* `ExtremeValueTheory.IsRegularlyVarying.integrableOn_Ioi`: such an `F` is integrable on every
  `Ioi x`.
* `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div`: Karamata's theorem.

## Proof

After the substitution `t = x * u`,
`(∫ t in Ioi x, F t) / (x * F x) = ∫ u in Ioi 1, F (x * u) / F x`.
The integrand tends to `u ^ (-α)` pointwise, and by the Potter bounds
(`IsRegularlyVarying.potter_bound`) it is dominated by `2 * u ^ (-α + δ)` with
`δ = (α - 1) / 2`, which is integrable on `Ioi 1`. Dominated convergence finishes the proof, since
`∫ u in Ioi 1, u ^ (-α) = 1 / (α - 1)`.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

namespace IsRegularlyVarying

variable {F : ℝ → ℝ} {α : ℝ}

/-- An antitone, eventually positive function is positive everywhere. -/
theorem pos_of_antitone (hF : Antitone F) (hpos : ∀ᶠ x in atTop, 0 < F x) (t : ℝ) : 0 < F t := by
  obtain ⟨s, hs, hts⟩ := (hpos.and (eventually_ge_atTop t)).exists
  exact hs.trans_le (hF hts)

/-- An antitone function which is regularly varying of index `-α` with `α > 1` is integrable on
every half-line `Ioi x`. -/
theorem integrableOn_Ioi (hF : Antitone F) (hRV : IsRegularlyVarying F (-α)) (hα : 1 < α)
    (x : ℝ) : IntegrableOn F (Ioi x) := by
  set δ := (α - 1) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨x₀, hx₀, -, hP⟩ :=
    hRV.potter_bound (a := 0) (Or.inr (hF.antitoneOn _)) hδ (one_lt_two)
  set b := max x x₀ with hb_def
  have hb0 : 0 < b := hx₀.trans_le (le_max_right _ _)
  have hFb := pos_of_antitone hF hRV.1 b
  have hsplit : Ioi x ⊆ Icc x b ∪ Ioi b := by
    intro t ht
    rcases le_or_gt t b with h | h
    · exact Or.inl ⟨(mem_Ioi.1 ht).le, h⟩
    · exact Or.inr h
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsplit
  · exact (hF.antitoneOn _).integrableOn_isCompact isCompact_Icc
  · have hexp : -α + δ < -1 := by rw [hδ_def]; linarith
    have hint : IntegrableOn (fun t => (2 * F b / b ^ (-α + δ)) * t ^ (-α + δ)) (Ioi b) :=
      (integrableOn_Ioi_rpow_of_lt hexp hb0).const_mul _
    refine Integrable.mono' hint hF.measurable.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht' : b < t := ht
    have ht0 : 0 < t := hb0.trans ht'
    have hFt := pos_of_antitone hF hRV.1 t
    have h := hP b (le_max_right _ _) t (by linarith [le_max_right x x₀])
    have hu : 1 ≤ t / b := by rw [le_div_iff₀ hb0]; linarith
    rw [max_eq_left (rpow_le_rpow_of_exponent_le hu (by linarith)), div_le_iff₀ hFb,
      div_rpow ht0.le hb0.le] at h
    rw [Real.norm_eq_abs, abs_of_pos hFt]
    calc F t ≤ 2 * (t ^ (-α + δ) / b ^ (-α + δ)) * F b := h
      _ = 2 * F b / b ^ (-α + δ) * t ^ (-α + δ) := by ring

/-- **Karamata's theorem** for tail integrals ([BGT, Proposition 1.5.10]; see also
[BGT, Theorem 1.5.11]). Let `F` be antitone and regularly varying with index `-α`, where
`α > 1` (regular variation includes eventual positivity of `F`). Then
`(∫ t in Ioi x, F t) / (x * F x) → 1 / (α - 1)` as `x → ∞`.

In particular, if `F` is the survival function of a random variable, the mean excess
over a high threshold `x` is asymptotically `x / (α - 1)`. -/
theorem tendsto_integral_Ioi_div (hF : Antitone F) (hRV : IsRegularlyVarying F (-α))
    (hα : 1 < α) :
    Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 (1 / (α - 1))) := by
  set δ := (α - 1) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hexp : -α + δ < -1 := by rw [hδ_def]; linarith
  obtain ⟨x₀, hx₀, -, hP⟩ :=
    hRV.potter_bound (a := 0) (Or.inr (hF.antitoneOn _)) hδ (one_lt_two)
  have hFpos := pos_of_antitone hF hRV.1
  have hFm : Measurable F := hF.measurable
  -- Change of variables `t = x * u`.
  have hsub : ∀ᶠ x in atTop,
      ∫ u in Ioi (1 : ℝ), F (x * u) / F x = (∫ t in Ioi x, F t) / (x * F x) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [integral_div, integral_comp_mul_left_Ioi F 1 hx, mul_one, smul_eq_mul, inv_mul_eq_div,
      div_div]
  -- The value of the limit.
  have hlim : ∫ u in Ioi (1 : ℝ), u ^ (-α) = 1 / (α - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, one_rpow]
    rw [show -α + 1 = -(α - 1) by ring, neg_div_neg_eq]
  rw [← hlim]
  refine Tendsto.congr' hsub ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun u => 2 * u ^ (-α + δ)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      ((hFm.comp (measurable_id.const_mul x)).div_const _).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop x₀] with x hx
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu : 1 < u := hu
    have hx0 : 0 < x := hx₀.trans_le hx
    have hxu : x₀ ≤ x * u := by nlinarith
    have h := hP x hx (x * u) hxu
    rw [mul_div_cancel_left₀ u hx0.ne',
      max_eq_left (rpow_le_rpow_of_exponent_le hu.le (by linarith))] at h
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (hFpos _) (hFpos _))]
    exact h
  · exact (integrableOn_Ioi_rpow_of_lt hexp one_pos).const_mul 2
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu : (0 : ℝ) < u := zero_lt_one.trans hu
    exact (hRV.2 u hu).congr fun x => by rw [mul_comm]

end IsRegularlyVarying

end ExtremeValueTheory
