/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.MeasureTheory.Measure.Real

/-!
# The second Bonferroni inequality

For measurable sets `A 0, …, A (n - 1)` of finite measure,
`∑ i, μ (A i) - ∑_{i < j} μ (A i ∩ A j) ≤ μ (⋃ i, A i)`.
Together with the union bound `μ (⋃ i, A i) ≤ ∑ i, μ (A i)` this is the inclusion–exclusion
estimate of order two.

## Main results

* `MeasureTheory.sum_measureReal_sub_sum_inter_le_measureReal_biUnion`: the second Bonferroni
  inequality, stated with `Measure.real`.
-/

open Finset

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- **Second Bonferroni inequality**: the measure of a finite union is at least the sum of the
measures minus the sum of the measures of the pairwise intersections. -/
theorem sum_measureReal_sub_sum_inter_le_measureReal_biUnion [IsFiniteMeasure μ]
    {A : ℕ → Set α} (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    ∑ i ∈ range n, μ.real (A i) - ∑ j ∈ range n, ∑ i ∈ range j, μ.real (A i ∩ A j) ≤
      μ.real (⋃ i ∈ range n, A i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hU : (⋃ i ∈ range (n + 1), A i) = (⋃ i ∈ range n, A i) ∪ A n := by
      ext x; simp only [Set.mem_iUnion, mem_range, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨i, hi, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · exact Or.inl ⟨i, h, hx⟩
        · exact Or.inr hx
      · rintro (⟨i, hi, hx⟩ | hx)
        · exact ⟨i, by omega, hx⟩
        · exact ⟨n, by omega, hx⟩
    have hinter : μ.real ((⋃ i ∈ range n, A i) ∩ A n) ≤ ∑ i ∈ range n, μ.real (A i ∩ A n) := by
      rw [Set.iUnion₂_inter]
      exact measureReal_biUnion_finset_le _ _
    have hadd := measureReal_union_add_inter (μ := μ) (s := ⋃ i ∈ range n, A i) (hA n)
      (measure_ne_top _ _) (measure_ne_top _ _)
    rw [hU, sum_range_succ, sum_range_succ]
    linarith

end MeasureTheory
