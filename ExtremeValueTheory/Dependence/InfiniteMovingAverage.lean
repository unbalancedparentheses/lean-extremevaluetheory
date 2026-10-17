/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MDependentExamples
import ExtremeValueTheory.HeavyTails.LinearProcessSeries

/-!
# The extremal index of an infinite moving average

Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative random variables with `P(Z_0 > x)` regularly varying with
index `-α`, and let `ψ_j ≥ 0`, `j ∈ ℕ`, be coefficients, not all zero, with `∑ ψ_j^δ < ∞` for
some `0 < δ < α < 1`. The infinite moving average

  `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}`

converges almost surely (`LinearProcess.ae_summable_mul`), and has extremal index

  `θ = sup_j ψ_j^α / ∑_j ψ_j^α`

([DR85], [EKM, §8.1], [KS20, Chapter 15]). We prove this by approximation with the finite moving
averages `X^{(m)}_t = ∑_{j ≤ m} ψ_j Z_{t-j}`, which are `m`-dependent and whose extremal index
`max_{j ≤ m} ψ_j^α / ∑_{j ≤ m} ψ_j^α` is `MovingAverage.hasExtremalIndex` (derived through the
main theorem `θ = ϑ`).

## Main results

* `InfiniteMovingAverage.tendsto_measureReal_process_div`:
  `P(X_0 > x) / P(Z_0 > x) → ∑_j ψ_j^α`.
* `InfiniteMovingAverage.exists_measureReal_abs_sub_gt_le`: the remainder bound
  `P(|X_t - X^{(m)}_t| > y) ≤ K (∑_{j > m} ψ_j^δ) P(Z_0 > y)`, uniformly in `t`, `m ≥ m₀` and
  `y ≥ x₀`.
* `InfiniteMovingAverage.hasExtremalIndex`: the extremal index of `X` is
  `(sup_j ψ_j)^α / ∑_j ψ_j^α`.
* `InfiniteMovingAverage.hasExtremalIndex_ar1`: the AR(1) process `X_t = φ X_{t-1} + Z_t`,
  `0 < φ < 1`, i.e. `ψ_j = φ^j`, has extremal index `1 - φ^α` ([EKM, Example 8.1.?], [KS20]).

## Hypotheses

The restriction `α < 1` is inherited from `LinearProcess.exists_measure_tsum_gt_le` (the uniform
remainder bound uses Karamata's theorem for the truncated first moment). The noise is nonnegative
and the coefficients are nonnegative, as for `MovingAverage.hasExtremalIndex`.

## Proof

Write `M_n`, `M^{(m)}_n` for the partial maxima, `u_n` a level sequence with
`n P(X_0 > u_n) → τ`, and `L(x) = P(Z_0 > x)`. Then `u_n → ∞` and `n L(u_n) → τ / ∑ψ^α`. For
`m` beyond an index `j*` where `sup ψ = ψ_{j*}` is attained, and `c > 0`,
`n P(X^{(m)}_0 > c u_n) → c^{-α} τ ∑_{j ≤ m} ψ_j^α / ∑ ψ^α`, so the finite theorem gives
`P(M^{(m)}_n ≤ c u_n) → exp(-ϑ τ c^{-α})`. On the complement of
`bad_n = {∃ t < n, |X_t - X^{(m)}_t| > ε u_n}`,

  `M^{(m)}_n ≤ (1 - ε) u_n ⟹ M_n ≤ u_n ⟹ M^{(m)}_n ≤ (1 + ε) u_n`,

and `P(bad_n) ≤ n K T_m L(ε u_n) → K T_m ε^{-α} τ / ∑ψ^α`, `T_m = ∑_{j > m} ψ_j^δ → 0`.
Choosing first `ε`, then `m`, the limit follows.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal

namespace ExtremeValueTheory

namespace InfiniteMovingAverage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The infinite moving average `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` (the `tsum` is `0` where the
series does not converge, a null event under the hypotheses of `LinearProcess.ae_summable_mul`). -/
noncomputable def process (ψ : ℕ → ℝ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  ∑' j : ℕ, ψ j * Z (t - j) ω

variable [IsProbabilityMeasure P] {Z : ℤ → Ω → ℝ} {ψ : ℕ → ℝ} {α δ : ℝ}

theorem setOf_lt_abs_eq (hZ0 : ∀ i ω, 0 ≤ Z i ω) (x : ℝ) :
    {ω | x < |Z 0 ω|} = {ω | x < Z 0 ω} := by
  ext ω; simp [abs_of_nonneg (hZ0 0 ω)]

theorem summable_abs_rpow (hψ0 : ∀ j, 0 ≤ ψ j) (hψ : Summable fun j => ψ j ^ δ) :
    Summable fun j => |ψ j| ^ δ := by
  simpa only [abs_of_nonneg (hψ0 _)] using hψ

/-- `∑ ψ_j^α < ∞` when `∑ ψ_j^δ < ∞`, `0 < δ ≤ α`. -/
theorem summable_rpow (hψ0 : ∀ j, 0 ≤ ψ j) (hδ : 0 < δ) (hδα : δ ≤ α)
    (hψ : Summable fun j => ψ j ^ δ) : Summable fun j => ψ j ^ α := by
  have := LinearProcess.summable_tailWeight (p := 1) hδ hδα zero_le_one le_rfl
    (summable_abs_rpow hψ0 hψ)
  refine this.congr fun j => ?_
  rcases (hψ0 j).eq_or_lt with h0 | hpos
  · rw [← h0, LinearProcess.tailWeight_zero, Real.zero_rpow (hδ.trans_le hδα).ne']
  · rw [LinearProcess.tailWeight_of_pos hpos, mul_one]

/-- **Tail of the infinite moving average**: `P(X_0 > x) / P(Z_0 > x) → ∑_j ψ_j^α`
(`0 < δ < α < 1`, `∑ ψ_j^δ < ∞`). -/
theorem tendsto_measureReal_process_div (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) :
    Tendsto (fun x => P.real {ω | x < process ψ Z 0 ω} / P.real {ω | x < Z 0 ω}) atTop
      (𝓝 (∑' j, ψ j ^ α)) := by
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [setOf_lt_abs_eq hZ0] using hL
  have hp : Tendsto (fun x => P.real {ω | x < Z 0 ω} / P.real {ω | x < |Z 0 ω|}) atTop
      (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hL.1] with x hx
    rw [setOf_lt_abs_eq hZ0, div_self hx.ne']
  have hinj : Function.Injective fun i : ℕ => (0 : ℤ) - i := fun a b h => by
    simpa using h
  have h := LinearProcess.tendsto_measureReal_tsum_mul_div (Z := fun i : ℕ => Z (0 - i))
    (fun i => hZ _) (hZ 0) (hind.precomp hinj) (fun i => hident _) hδ hδα hα1 hL' hp
    (summable_abs_rpow hψ0 hψ)
  simp only [setOf_lt_abs_eq hZ0] at h
  have hW : ∑' j, ψ j ^ α = ∑' j, LinearProcess.tailWeight α 1 (ψ j) := by
    refine tsum_congr fun j => ?_
    rcases (hψ0 j).eq_or_lt with h0 | hpos
    · rw [← h0, LinearProcess.tailWeight_zero, Real.zero_rpow (hδ.trans hδα).ne']
    · rw [LinearProcess.tailWeight_of_pos hpos, mul_one]
  rw [hW]
  exact h

/-- **Uniform remainder bound** (`0 < δ < α < 1`): there are `K, x₀ > 0` and `m₀` such that for
all `m ≥ m₀`, `t ∈ ℤ` and `y ≥ x₀`,
`P(|X_t - X^{(m)}_t| > y) ≤ K (∑_{j > m} ψ_j^δ) P(Z_0 > y)`. Independence is not needed. -/
theorem exists_measureReal_abs_sub_gt_le (hZ : ∀ i, Measurable (Z i))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) :
    ∃ K x₀ : ℝ, ∃ m₀ : ℕ, 0 < K ∧ 0 < x₀ ∧ ∀ m ≥ m₀, ∀ t : ℤ, ∀ y ≥ x₀,
      P.real {ω | y < |process ψ Z t ω - MovingAverage.process m ψ Z t ω|} ≤
        K * (∑' j, ψ (j + (m + 1)) ^ δ) * P.real {ω | y < Z 0 ω} := by
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [setOf_lt_abs_eq hZ0] using hL
  obtain ⟨K, x₀, hK, hx₀, hR⟩ := LinearProcess.exists_measure_tsum_gt_le (hZ 0) hδα hα1 hL'
  obtain ⟨m₀, hm₀⟩ := LinearProcess.exists_abs_le_one hδ (summable_abs_rpow hψ0 hψ)
  refine ⟨K, x₀, m₀, hK, hx₀, fun m hm t y hy => ?_⟩
  have hy0 : 0 ≤ y := hx₀.le.trans hy
  have h := hR (fun j => Z (t - ((j + (m + 1) : ℕ) : ℤ))) (fun j => hZ _) (fun j => hident _)
    (fun j => ψ (j + (m + 1))) (fun j => hm₀ _ (by omega))
    ((summable_nat_add_iff (m + 1)).2 (summable_abs_rpow hψ0 hψ)) y hy
  simp only [abs_of_nonneg (hψ0 _), setOf_lt_abs_eq hZ0] at h
  have hsub : {ω | y < |process ψ Z t ω - MovingAverage.process m ψ Z t ω|} ⊆
      {ω | ENNReal.ofReal y <
        ∑' j, ENNReal.ofReal (ψ (j + (m + 1)) * |Z (t - ((j + (m + 1) : ℕ) : ℤ)) ω|)} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra hle
    push Not at hle
    have := (LinearProcess.abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z (t - j) ω)
      (m := m + 1) hy0 (by simpa only [abs_of_nonneg (hψ0 _)] using hle)).2
    exact absurd this (not_le.2 hω)
  have hT0 : 0 ≤ ∑' j, ψ (j + (m + 1)) ^ δ := tsum_nonneg fun j => Real.rpow_nonneg (hψ0 _) _
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (ENNReal.toReal_le_of_le_ofReal (by positivity) h)

end InfiniteMovingAverage

end ExtremeValueTheory
