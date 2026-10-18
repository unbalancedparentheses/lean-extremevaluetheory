/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Probability.SkorokhodLaw
public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Complete
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Weak convergence in the Skorokhod space: finite-dimensional convergence and tightness

Let `μ_n`, `μ` be Borel probability measures on the Skorokhod space `D([0, 1], E)`, `E` a
complete separable metric space. If `{μ_n}` is tight and the finite-dimensional distributions
of `μ_n` converge to those of `μ` at all times of a set `T` with countable complement and
containing `1`, then `μ_n → μ` weakly
([Billingsley, *Convergence of Probability Measures*, Theorem 13.1][billingsley1999]).

The proof is the standard one: by Prokhorov's theorem the closure of `{μ_n}` is compact, so it
suffices that every cluster point `ν` equals `μ`. Along a subsequence converging to `ν`, the
finite-dimensional projections `π_J` with `J ⊆ T ∩ T_ν` are `ν`-a.e. continuous, where `T_ν` is
the co-countable set of times that are not fixed discontinuities of `ν`
(`SkorokhodSpace.countable_setOf_measure_not_continuousAt_ne_zero`); so by the continuous
mapping theorem `ν π_J⁻¹ = μ π_J⁻¹`. Since `T ∩ T_ν` is dense and contains `1`, the
finite-dimensional distributions on it determine the law (`SkorokhodSpace.ext_of_forall_map_restrict_eq`).

## Main statements

* `unitInterval.dense_compl_of_countable`: a countable subset of `[0, 1]` has dense complement.
* `SkorokhodSpace.tendsto_of_tendsto_map_restrict_of_isTight`: **Billingsley, Theorem 13.1**.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

@[expose] public section

open Filter Set Topology MeasureTheory unitInterval
open scoped ENNReal

/-- A countable subset of the unit interval has dense complement. -/
lemma unitInterval.dense_compl_of_countable {s : Set I} (hs : s.Countable) : Dense sᶜ := by
  have hR : Dense ((Subtype.val '' s : Set ℝ)ᶜ) := (hs.image _).dense_compl ℝ
  refine dense_iff_inter_open.2 fun U hU ⟨t, htU⟩ ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t htU
  set a : ℝ := max ((t : ℝ) - ε) 0
  set b : ℝ := min ((t : ℝ) + ε) 1
  have hab : a < b := by
    simp only [a, b, max_lt_iff, lt_min_iff]
    have := t.2.1
    have := t.2.2
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num <;> linarith
  obtain ⟨y, hyab, hys⟩ := hR.inter_open_nonempty (Ioo a b) isOpen_Ioo (nonempty_Ioo.2 hab)
  have hy0 : 0 ≤ y := (le_max_right _ _).trans hyab.1.le
  have hy1 : y ≤ 1 := hyab.2.le.trans (min_le_right _ _)
  refine ⟨⟨y, hy0, hy1⟩, hball ?_, fun hy ↦ hys ⟨_, hy, rfl⟩⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
  constructor
  · linarith [le_max_left ((t : ℝ) - ε) 0, hyab.1]
  · linarith [min_le_left ((t : ℝ) + ε) 1, hyab.2]

namespace SkorokhodSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- The finite-dimensional projection `π_J` is continuous at every path that is continuous at
each time of `J` other than `1`. -/
lemma continuousAt_restrict_of_ne_one {J : Finset I} {x : SkorokhodSpace E}
    (hx : ∀ t ∈ J, t ≠ 1 → ContinuousAt x t) :
    ContinuousAt (fun y : SkorokhodSpace E ↦ fun t : J ↦ y t) x := by
  refine continuousAt_pi.2 fun t ↦ ?_
  by_cases ht : (t : I) = 1
  · rw [ht]
    exact continuous_apply_one.continuousAt
  · exact tendsto_apply_of_continuousAt (x := fun y : SkorokhodSpace E ↦ y) tendsto_id
      (hx t t.2 ht)

/-- **Billingsley, Theorem 13.1.** Let `μ_n`, `μ` be probability measures on the Skorokhod space
`D([0, 1], E)`. If `{μ_n}` is tight and the finite-dimensional distributions of `μ_n` converge
to those of `μ` at the times of a set `T` with countable complement and containing `1`, then
`μ_n → μ` weakly. -/
theorem tendsto_of_tendsto_map_restrict_of_isTight
    {μs : ℕ → ProbabilityMeasure (SkorokhodSpace E)} {μ : ProbabilityMeasure (SkorokhodSpace E)}
    {T : Set I} (hT : Tᶜ.Countable) (h1 : (1 : I) ∈ T)
    (hfdd : ∀ J : Finset I, (J : Set I) ⊆ T →
      Tendsto (fun n ↦ (μs n).map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t)) atTop
        (𝓝 (μ.map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t))))
    (htight : IsTightMeasureSet (range fun n ↦ (μs n : Measure (SkorokhodSpace E)))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hS : IsCompact (closure (range μs)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight using 2
    ext ν
    simp
  refine hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun n ↦
    subset_closure (mem_range_self n)) fun ν _ hν ↦ ?_
  obtain ⟨ψ, hψ, hψν⟩ := hν.tendsto_subseq
  -- the good times: in `T` and not fixed discontinuities of `ν`, or `1`
  set T' : Set I := T ∩ ({1} ∪ {t | (ν : Measure (SkorokhodSpace E)) {x | ¬ ContinuousAt (⇑x) t} = 0})
    with hT'
  have hT'c : T'ᶜ.Countable := by
    refine (hT.union (countable_setOf_measure_not_continuousAt_ne_zero
      (ν : Measure (SkorokhodSpace E)))).mono fun t ht ↦ ?_
    simp only [hT', mem_compl_iff, mem_inter_iff, mem_union, mem_singleton_iff, mem_ofPred_eq,
      not_and_or, not_or] at ht
    rcases ht with ht | ⟨-, ht⟩
    · exact Or.inl ht
    · exact Or.inr ht
  have hT'd : Dense T' := by simpa using dense_compl_of_countable hT'c
  have h1' : (1 : I) ∈ T' := ⟨h1, Or.inl rfl⟩
  refine ProbabilityMeasure.toMeasure_injective (ext_of_forall_map_restrict_eq hT'd h1'
    fun J hJ ↦ ?_)
  have hm : Measurable fun x : SkorokhodSpace E ↦ fun t : J ↦ x t :=
    measurable_pi_iff.2 fun t ↦ measurable_apply t.1
  -- along the subsequence, `π_J` is `ν`-a.e. continuous
  have hcont : ∀ᵐ x ∂(ν : Measure (SkorokhodSpace E)),
      ContinuousAt (fun y : SkorokhodSpace E ↦ fun t : J ↦ y t) x := by
    have hnull : ∀ t ∈ J, t ≠ 1 →
        ∀ᵐ x ∂(ν : Measure (SkorokhodSpace E)), ContinuousAt (⇑(x : SkorokhodSpace E)) t := by
      intro t ht ht1
      rcases (hJ ht).2 with h | h
      · exact absurd h ht1
      · rw [ae_iff]
        exact h
    have : ∀ᵐ x ∂(ν : Measure (SkorokhodSpace E)), ∀ t ∈ J, t ≠ 1 →
        ContinuousAt (⇑(x : SkorokhodSpace E)) t := by
      rw [Filter.eventually_all_finset]
      exact fun t ht ↦ by
        by_cases ht1 : t = 1
        · exact Eventually.of_forall fun _ h ↦ absurd ht1 h
        · exact (hnull t ht ht1).mono fun _ h _ ↦ h
    exact this.mono fun x hx ↦ continuousAt_restrict_of_ne_one hx
  have hlim1 := ProbabilityMeasure.tendsto_map_of_ae_continuousAt hψν hm hcont
  have hlim2 := (hfdd J fun t ht ↦ (hJ ht).1).comp hψ.tendsto_atTop
  have := tendsto_nhds_unique hlim1 hlim2
  have := congrArg ProbabilityMeasure.toMeasure this
  simpa using this

end SkorokhodSpace
