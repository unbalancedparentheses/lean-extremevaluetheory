/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A dyadic chaining maximal inequality

For a finite sequence `y 0, …, y (2 ^ q)` the binary expansion of `j ≤ 2 ^ q` gives a path from
`0` to `j` that uses at most one increment of each dyadic level `ℓ = 1, …, q`, the increments of
level `ℓ` being `y ((i + 1) 2 ^ (q - ℓ)) - y (i 2 ^ (q - ℓ))`, `i < 2 ^ ℓ`. Hence if every
increment of level `ℓ` is at most `λ ℓ` in absolute value, then `|y j - y 0| ≤ ∑_ℓ λ ℓ` for all
`j ≤ 2 ^ q` (`abs_sub_le_sum_of_dyadic`).

Combined with a union bound and Markov's inequality for fourth moments this gives a maximal
inequality for random sequences `Y j` with controlled fourth moments of the dyadic increments
(`measureReal_exists_lt_abs_sub_le`), the chaining argument behind Kolmogorov's continuity
criterion and moment criteria for tightness in `C` and `D`
([Billingsley, *Convergence of Probability Measures*, §7, §10]).

## Main statements

* `abs_sub_le_sum_of_dyadic`: the deterministic chaining bound.
* `MeasureTheory.measureReal_exists_lt_abs_sub_le`: the maximal inequality
  `P (∃ j ≤ 2 ^ q, ∑_ℓ λ ℓ < |Y j - Y 0|) ≤ ∑_ℓ 2 ^ ℓ B ℓ / λ ℓ ^ 4`, where `B ℓ` bounds the
  fourth moments of the increments of level `ℓ`.
-/

@[expose] public section

open Finset

/-- **Dyadic chaining.** If all increments of level `ℓ ≤ q` of `y` along the dyadic grid of
`[0, 2 ^ q]` are bounded by `λ ℓ`, then `|y j - y 0| ≤ ∑_{ℓ ≤ q} λ ℓ` for every `j ≤ 2 ^ q`. -/
theorem abs_sub_le_sum_of_dyadic (q : ℕ) (y : ℕ → ℝ) (lam : ℕ → ℝ)
    (h : ∀ ℓ ∈ range (q + 1), ∀ i < 2 ^ ℓ,
      |y ((i + 1) * 2 ^ (q - ℓ)) - y (i * 2 ^ (q - ℓ))| ≤ lam ℓ) :
    ∀ j ≤ 2 ^ q, |y j - y 0| ≤ ∑ ℓ ∈ range (q + 1), lam ℓ := by
  induction q generalizing y with
  | zero =>
    intro j hj
    simp only [pow_zero] at hj
    interval_cases j
    · simpa using (abs_nonneg _).trans (h 0 (by simp) 0 (by simp))
    · simpa using h 0 (by simp) 0 (by simp)
  | succ q ih =>
    intro j hj
    -- the coarser levels, through the even points
    have hz := ih (fun m ↦ y (2 * m)) (fun ℓ hℓ i hi ↦ by
      have hℓ' : ℓ ∈ range (q + 1 + 1) := by
        simp only [mem_range] at hℓ ⊢; omega
      have e1 : (i + 1) * 2 ^ (q + 1 - ℓ) = 2 * ((i + 1) * 2 ^ (q - ℓ)) := by
        simp only [mem_range] at hℓ
        rw [show q + 1 - ℓ = (q - ℓ) + 1 by omega, pow_succ]; ring
      have e2 : i * 2 ^ (q + 1 - ℓ) = 2 * (i * 2 ^ (q - ℓ)) := by
        simp only [mem_range] at hℓ
        rw [show q + 1 - ℓ = (q - ℓ) + 1 by omega, pow_succ]; ring
      have := h ℓ hℓ' i hi
      rwa [e1, e2] at this) (j / 2) (by rw [pow_succ] at hj; omega)
    simp only [mul_zero] at hz
    rw [Finset.sum_range_succ]
    -- the finest level, from `2 ⌊j / 2⌋` to `j`
    have hfine : |y j - y (2 * (j / 2))| ≤ lam (q + 1) := by
      rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
      · rw [show 2 * (j / 2) = j by omega, sub_self, abs_zero]
        exact (abs_nonneg _).trans (h (q + 1) (by simp) 0 (by positivity))
      · have := h (q + 1) (by simp) (2 * m) (by rw [pow_succ] at hj; omega)
        rw [Nat.sub_self, pow_zero, mul_one, mul_one] at this
        rw [show 2 * (j / 2) = 2 * m by omega, hm]
        exact this
    calc |y j - y 0| ≤ |y j - y (2 * (j / 2))| + |y (2 * (j / 2)) - y 0| :=
          abs_sub_le _ _ _
      _ ≤ lam (q + 1) + ∑ ℓ ∈ range (q + 1), lam ℓ := add_le_add hfine hz
      _ = _ := add_comm _ _

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- Markov's inequality for fourth moments. -/
lemma measureReal_lt_abs_le_integral_pow_four_div {Z : Ω → ℝ} (hZ : Integrable (fun ω ↦ Z ω ^ 4) P)
    {lam : ℝ} (hlam : 0 < lam) :
    P.real {ω | lam < |Z ω|} ≤ (∫ ω, Z ω ^ 4 ∂P) / lam ^ 4 := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := P) (Filter.Eventually.of_forall fun ω ↦
    (by positivity : (0 : ℝ) ≤ Z ω ^ 4)) hZ (lam ^ 4)
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono fun ω hω ↦ ?_) (by positivity)) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  calc lam ^ 4 ≤ |Z ω| ^ 4 := pow_le_pow_left₀ hlam.le hω.le 4
    _ = Z ω ^ 4 := Even.pow_abs (by decide) _

/-- **Dyadic chaining maximal inequality.** If the fourth moments of the increments of level
`ℓ ≤ q` of `Y` along the dyadic grid of `[0, 2 ^ q]` are bounded by `B ℓ`, then
`P (∃ j ≤ 2 ^ q, ∑_ℓ λ ℓ < |Y j - Y 0|) ≤ ∑_{ℓ ≤ q} 2 ^ ℓ B ℓ / λ ℓ ^ 4`. -/
theorem measureReal_exists_lt_abs_sub_le (q : ℕ) {Y : ℕ → Ω → ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ ℓ, 0 < lam ℓ) {B : ℕ → ℝ}
    (hint : ∀ ℓ ∈ range (q + 1), ∀ i < 2 ^ ℓ,
      Integrable (fun ω ↦ (Y ((i + 1) * 2 ^ (q - ℓ)) ω - Y (i * 2 ^ (q - ℓ)) ω) ^ 4) P)
    (hB : ∀ ℓ ∈ range (q + 1), ∀ i < 2 ^ ℓ,
      ∫ ω, (Y ((i + 1) * 2 ^ (q - ℓ)) ω - Y (i * 2 ^ (q - ℓ)) ω) ^ 4 ∂P ≤ B ℓ) :
    P.real {ω | ∃ j ≤ 2 ^ q, ∑ ℓ ∈ range (q + 1), lam ℓ < |Y j ω - Y 0 ω|} ≤
      ∑ ℓ ∈ range (q + 1), 2 ^ ℓ * (B ℓ / lam ℓ ^ 4) := by
  have hsub : {ω | ∃ j ≤ 2 ^ q, ∑ ℓ ∈ range (q + 1), lam ℓ < |Y j ω - Y 0 ω|} ⊆
      ⋃ ℓ ∈ range (q + 1), ⋃ i ∈ range (2 ^ ℓ),
        {ω | lam ℓ < |Y ((i + 1) * 2 ^ (q - ℓ)) ω - Y (i * 2 ^ (q - ℓ)) ω|} := by
    intro ω ⟨j, hj, hlt⟩
    by_contra hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_range, not_exists, not_lt] at hω
    exact (not_le.2 hlt) (abs_sub_le_sum_of_dyadic q (fun m ↦ Y m ω) lam
      (fun ℓ hℓ i hi ↦ hω ℓ (mem_range.1 hℓ) i hi) j hj)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum fun ℓ hℓ ↦ ((measureReal_biUnion_finset_le _ _).trans ?_)))
  calc ∑ i ∈ range (2 ^ ℓ), P.real {ω | lam ℓ < |Y ((i + 1) * 2 ^ (q - ℓ)) ω -
        Y (i * 2 ^ (q - ℓ)) ω|}
      ≤ ∑ i ∈ range (2 ^ ℓ), B ℓ / lam ℓ ^ 4 := Finset.sum_le_sum fun i hi ↦
        (measureReal_lt_abs_le_integral_pow_four_div (hint ℓ hℓ i (mem_range.1 hi))
          (hlam ℓ)).trans (div_le_div_of_nonneg_right (hB ℓ hℓ i (mem_range.1 hi))
            (by positivity))
    _ = 2 ^ ℓ * (B ℓ / lam ℓ ^ 4) := by simp

end MeasureTheory
