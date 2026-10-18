/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.BlockOscillation
public import ExtremeValueTheory.ForMathlib.Probability.SkorokhodWeakConvergence

/-!
# Tightness in `D([0, 1], ℝ)` via the block oscillation

A sequence of probability measures `μ_n` on `D([0, 1], ℝ)` is tight if the initial values
`x 0` are tight and, for all `ε, η > 0`, there is a mesh `1/m` such that eventually
`μ_n {x | ε ≤ blockOscillation x m} ≤ η`. This follows from Billingsley's criterion
`SkorokhodSpace.isTightMeasureSet_of_cadlagModulus`
([Billingsley, *Convergence of Probability Measures*, Theorem 13.2][billingsley1999]),
since the block oscillation controls both the càdlàg modulus `w'` and the sup norm.

## Main statements

* `SkorokhodSpace.isTightMeasureSet_of_blockOscillation`.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

@[expose] public section

open Filter Set Topology MeasureTheory unitInterval
open scoped ENNReal

namespace SkorokhodSpace

/-- **Tightness in `D([0, 1], ℝ)` from the block oscillation.** -/
theorem isTightMeasureSet_of_blockOscillation {μs : ℕ → Measure (SkorokhodSpace ℝ)}
    [∀ n, IsProbabilityMeasure (μs n)]
    (h0 : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ᶠ n in atTop, μs n {x | a < |x 0|} ≤ η)
    (hblock : ∀ ε : ℝ≥0∞, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ m > 0,
      ∀ᶠ n in atTop, μs n {x | ε ≤ blockOscillation (⇑x) m} ≤ η) :
    IsTightMeasureSet (range μs) := by
  refine isTightMeasureSet_of_cadlagModulus (fun η hη ↦ ?_) (fun ε hε η hη ↦ ?_)
  · have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
    obtain ⟨a, ha⟩ := h0 _ hη2
    obtain ⟨m, hm, hb⟩ := hblock 1 one_pos _ hη2
    refine ⟨Metric.closedBall 0 (a + m), (isCompact_closedBall _ _).totallyBounded, ?_⟩
    filter_upwards [ha, hb] with n han hbn
    have hsub : {x : SkorokhodSpace ℝ | ∃ t, x t ∉ Metric.closedBall 0 (a + m)} ⊆
        {x | a < |x 0|} ∪ {x | 1 ≤ blockOscillation (⇑x) m} := by
      intro x ⟨t, ht⟩
      by_contra hx
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hx
      have he : edist (x t) (x 0) ≤ ENNReal.ofReal m := by
        refine (edist_apply_le_mul_blockOscillation (⇑x) hm t).trans ?_
        rw [ENNReal.ofReal_natCast]
        calc (m : ℝ≥0∞) * blockOscillation (⇑x) m ≤ m * 1 := by
              gcongr; exact (not_le.1 hx.2).le
          _ = m := mul_one _
      have hd : dist (x t) (x 0) ≤ m := (edist_le_ofReal (Nat.cast_nonneg _)).1 he
      apply ht
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      calc |x t| ≤ |x t - x 0| + |x 0| := by
            simpa using abs_add_le (x t - x 0) (x 0)
        _ ≤ m + a := add_le_add (by rwa [← Real.dist_eq]) hx.1
        _ = a + m := add_comm _ _
    calc μs n {x | ∃ t, x t ∉ Metric.closedBall 0 (a + m)}
        ≤ μs n {x | a < |x 0|} + μs n {x | 1 ≤ blockOscillation (⇑x) m} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ η / 2 + η / 2 := add_le_add han hbn
      _ = η := ENNReal.add_halves η
  · obtain ⟨m, hm, hb⟩ := hblock (ε / 2) (ENNReal.half_pos hε.ne') η hη
    have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
    refine ⟨1 / (2 * m), by positivity, ?_⟩
    filter_upwards [hb] with n hbn
    refine (measure_mono fun x hx ↦ ?_).trans hbn
    simp only [mem_ofPred_eq] at hx ⊢
    by_contra hlt
    push Not at hlt
    have hδ : 1 / (2 * (m : ℝ)) < 1 / m :=
      one_div_lt_one_div_of_lt hm' (by linarith)
    have h2 := cadlagModulus_le_two_mul_blockOscillation (⇑x) hm hδ
    have : blockOscillation (⇑x) m * 2 < ε := ENNReal.mul_lt_of_lt_div hlt
    exact (not_lt.2 hx) (h2.trans_lt (by rwa [mul_comm]))

end SkorokhodSpace
