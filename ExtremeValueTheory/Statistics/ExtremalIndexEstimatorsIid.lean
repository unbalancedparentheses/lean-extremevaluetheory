/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ExtremalIndexEstimators

/-!
# Block and run probabilities of an iid sequence

For an iid sequence with exceedance probability `p = P(X₀ > u)`, the events behind the blocks and
runs estimators of the extremal index have explicit probabilities:

* a block of length `r` contains an exceedance with probability `1 - (1 - p)^r`;
* an exceedance followed by `r` non-exceedances has probability `p (1 - p)^r`.

Hence the population block cluster ratio `(1 - (1 - p)^r) / (r p)` and runs ratio `(1 - p)^r`
tend to the extremal index `θ = 1` when `r p → 0`.

## Main results

* `measureReal_blockEvent_of_iIndepFun`: `P(block j has an exceedance) = 1 - (1 - p)^r`.
* `measureReal_runEvent_of_iIndepFun`: `P(X_i > u, X_{i+1}, …, X_{i+r} ≤ u) = p (1 - p)^r`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events for Insurance and
  Finance*, Springer (1997), §8.1.
-/

open MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- `P(X₀ ≤ v) = 1 - P(X₀ > v)`. -/
private theorem measureReal_le_eq_one_sub (hX : ∀ i, Measurable (X i)) (v : ℝ) :
    P.real {ω | X 0 ω ≤ v} = 1 - P.real {ω | v < X 0 ω} := by
  rw [← probReal_compl_eq_one_sub (measurableSet_lt measurable_const (hX 0))]
  congr 1
  ext ω; simp

/-- **Block probability of an iid sequence**: the block `{j r, …, j r + r - 1}` contains an
exceedance of `u` with probability `1 - (1 - p)^r`, `p = P(X₀ > u)`. -/
theorem measureReal_blockEvent_of_iIndepFun (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (r j : ℕ) (u : ℝ) :
    P.real (blockEvent X r j u) = 1 - (1 - P.real {ω | u < X 0 ω}) ^ r := by
  rw [blockEvent, probReal_compl_eq_one_sub (measurableSet_maxLE hX _ u),
    measureReal_maxLE_of_iIndepFun hind hid, measureReal_le_eq_one_sub hX]
  simp

/-- **Run probability of an iid sequence**: an exceedance of `u` at time `i` followed by `r`
non-exceedances has probability `p (1 - p)^r`, `p = P(X₀ > u)`. -/
theorem measureReal_runEvent_of_iIndepFun (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (r i : ℕ) (u : ℝ) :
    P.real (runEvent X r i u) = P.real {ω | u < X 0 ω} * (1 - P.real {ω | u < X 0 ω}) ^ r := by
  set f : ℕ → Set ℝ := fun t => if t = 0 then Set.Ioi u else Set.Iic u
  have hY : iIndepFun (fun t => X (i + t)) P :=
    hind.precomp (g := fun t => i + t) (add_right_injective i)
  have e : runEvent X r i u = ⋂ t ∈ range (r + 1), X (i + t) ⁻¹' f t := by
    ext ω
    simp only [runEvent, maxLE, Set.mem_inter_iff, Finset.mem_Ioc, Set.mem_iInter,
      Finset.mem_range, Set.mem_preimage, f, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h⟩ t ht
      split_ifs with h'
      · subst h'; simpa using h0
      · exact h (i + t) ⟨by omega, by omega⟩
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun t ht => ?_⟩
      have := h (t - i) (by omega)
      rw [if_neg (by omega), show i + (t - i) = t by omega] at this
      exact this
  have hmeas : ∀ t ∈ range (r + 1), MeasurableSet (f t) := fun t _ => by
    simp only [f]; split_ifs <;> measurability
  rw [e, measureReal_def, hY.measure_inter_preimage_eq_mul _ hmeas, ENNReal.toReal_prod,
    Finset.prod_range_succ']
  have h1 : ∀ t ∈ range r, (P (X (i + (t + 1)) ⁻¹' f (t + 1))).toReal =
      1 - P.real {ω | u < X 0 ω} := by
    intro t _
    simp only [f, if_neg (Nat.succ_ne_zero t)]
    rw [(hid (i + (t + 1))).measure_mem_eq measurableSet_Iic, ← measureReal_le_eq_one_sub hX]
    rfl
  rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_range, mul_comm]
  simp only [f, if_pos rfl, add_zero]
  rw [(hid i).measure_mem_eq measurableSet_Ioi]
  rfl

end ExtremeValueTheory
