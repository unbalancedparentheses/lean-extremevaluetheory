/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.LinearProcess
import ExtremeValueTheory.RegularVariation.KaramataConverse
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Tails of infinite linear processes with regularly varying noise, `α < 1`

Let `(Z_j)_{j ≥ 0}` be iid copies of `Z₀`, with `P(|Z₀| > x)` regularly varying with index `-α`,
`0 < α < 1`, and tail balance `P(Z₀ > x) / P(|Z₀| > x) → p`. Let `(ψ_j)` be real coefficients with
`∑ |ψ_j|^δ < ∞` for some `0 < δ < α`. Then the series `X = ∑_j ψ_j Z_j` converges absolutely
almost surely, and

  `P(X > x) / P(|Z₀| > x) → ∑_j |ψ_j|^α (p 1{ψ_j > 0} + (1 - p) 1{ψ_j < 0})`.

This is the case `α < 1` of [EKM, Lemma A3.26] / [DR85] / [KS20, Chapter 15], with the classical
summability condition of Cline (1983) and Mikosch–Samorodnitsky (2000). The case `α ≥ 1` needs a
centering / second-moment argument for the remainder and is not treated here.

## Main results

* `LinearProcess.exists_lintegral_trunc_le`: Karamata's bound
  `E[|Z| 1{|Z| ≤ y}] ≤ K y P(|Z| > y)` for large `y` (`α < 1`).
* `LinearProcess.exists_measure_tsum_gt_le`: the uniform remainder bound: there are `K`, `x₀`
  with `P(∑_j |c_j| |Z_j| > x) ≤ K (∑_j |c_j|^δ) P(|Z₀| > x)` for `x ≥ x₀`, for every coefficient
  sequence with `|c_j| ≤ 1`.
* `LinearProcess.ae_summable_mul`: almost sure absolute convergence of `∑ ψ_j Z_j`.
* `LinearProcess.tendsto_measureReal_tsum_mul_div`: the tail asymptotics of `X`.

## Proof

For the remainder we split on whether some term exceeds `x`:
`P(∑ W_j > x) ≤ ∑ P(W_j > x) + x⁻¹ ∑ E[W_j 1{W_j ≤ x}]`, `W_j = |c_j| |Z_j|`. Potter bounds give
`P(|Z| > x/|c|) ≤ 2 |c|^δ P(|Z| > x)` for `|c| ≤ 1`, and Karamata's theorem gives
`E[|Z| 1{|Z| ≤ y}] ≤ K y P(|Z| > y)` (this is where `α < 1` is used). The finite moving average
`∑_{j < m} ψ_j Z_j` is handled by `tendsto_measureReal_sum_mul_div`, and the remainder is
negligible uniformly as `m → ∞`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtremeValueTheory

namespace LinearProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The tail `x ↦ P(x < |Z|)` is antitone. -/
theorem antitone_measureReal_lt_abs [IsFiniteMeasure P] (Z : Ω → ℝ) :
    Antitone fun x => P.real {ω | x < |Z ω|} := fun _ _ h =>
  measureReal_mono fun _ (hω : _ < _) => lt_of_le_of_lt h hω

/-- **Truncated first moment** (Karamata, `α < 1`): if `P(|Z| > x)` is regularly varying with
index `-α`, `α < 1`, there are `K > 0` and `x₀ > 0` with
`E[|Z| 1{|Z| ≤ y}] ≤ K y P(|Z| > y)` for `y ≥ x₀`. -/
theorem exists_lintegral_trunc_le [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {α : ℝ} (hα1 : α < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z ω|}) (-α)) :
    ∃ K x₀ : ℝ, 0 < K ∧ 0 < x₀ ∧ ∀ y ≥ x₀,
      ∫⁻ ω, ENNReal.ofReal (if |Z ω| ≤ y then |Z ω| else 0) ∂P ≤
        ENNReal.ofReal (K * y * P.real {ω | y < |Z ω|}) := by
  set L : ℝ → ℝ := fun x => P.real {ω | x < |Z ω|} with hL_def
  have hanti : Antitone L := antitone_measureReal_lt_abs Z
  have hK := hL.tendsto_integral_zero_div hanti.measurable (by linarith)
    (fun x => hanti.intervalIntegrable)
  set K := 1 / (-α + 1) + 1 with hK_def
  have hK0 : 0 < K := by
    have : 0 < 1 / (-α + 1) := by apply div_pos one_pos; linarith
    linarith
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ((hK.eventually (gt_mem_nhds (show 1 / (-α + 1) < K by
    linarith))).and (hL.1.and (eventually_gt_atTop 0)))
  refine ⟨K, x₀, hK0, (hx₀ x₀ le_rfl).2.2, fun y hy => ?_⟩
  obtain ⟨hratio, hLy, hy0⟩ := hx₀ y hy
  have hZa : Measurable fun ω => |Z ω| := continuous_abs.measurable.comp hZ
  -- the truncated variable is at most `min |Z| y`
  have h1 : ∫⁻ ω, ENNReal.ofReal (if |Z ω| ≤ y then |Z ω| else 0) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (min |Z ω| y) ∂P := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    split_ifs with h
    · exact le_min le_rfl h
    · exact le_min (abs_nonneg _) hy0.le
  -- layer cake
  have h2 : ∫⁻ ω, ENNReal.ofReal (min |Z ω| y) ∂P ≤
      ∫⁻ t in Ioc 0 y, ENNReal.ofReal (L t) := by
    rw [lintegral_eq_lintegral_meas_lt P (Eventually.of_forall fun ω =>
      le_min (abs_nonneg _) hy0.le) (hZa.min measurable_const).aemeasurable]
    calc ∫⁻ t in Ioi 0, P {a | t < min |Z a| y}
        ≤ ∫⁻ t in Ioi 0, (Iic y).indicator (fun t => ENNReal.ofReal (L t)) t := by
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ Iic y
          · rw [indicator_of_mem ht, hL_def, ofReal_measureReal (measure_ne_top _ _)]
            exact measure_mono fun ω (hω : t < min |Z ω| y) =>
              (show t < |Z ω| from lt_of_lt_of_le hω (min_le_left _ _))
          · rw [indicator_of_notMem ht]
            have : {a | t < min |Z a| y} = ∅ := by
              ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
              exact (min_le_right _ _).trans (not_le.1 (show ¬ t ≤ y from ht)).le
            rw [this, measure_empty]
      _ = ∫⁻ t in Ioc 0 y, ENNReal.ofReal (L t) := by
          rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
            Iic_inter_Ioi]
  have h3 : ∫⁻ t in Ioc 0 y, ENNReal.ofReal (L t) = ENNReal.ofReal (∫ t in (0 : ℝ)..y, L t) := by
    rw [intervalIntegral.integral_of_le hy0.le, ofReal_integral_eq_lintegral_ofReal]
    · exact (hanti.intervalIntegrable (a := 0) (b := y)).1
    · exact Eventually.of_forall fun t => measureReal_nonneg
  refine h1.trans (h2.trans (h3.le.trans (ENNReal.ofReal_le_ofReal ?_)))
  have hpos : 0 < y * L y := mul_pos hy0 hLy
  rw [div_lt_iff₀ hpos] at hratio
  have : (1 / (-α + 1)) * (y * L y) ≤ K * (y * L y) := by
    apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
  rw [mul_assoc]
  linarith

end LinearProcess

end ExtremeValueTheory
