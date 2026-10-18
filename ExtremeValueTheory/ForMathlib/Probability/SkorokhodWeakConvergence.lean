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

/-- The *continuity times* `T_ν` of a measure `ν` on the Skorokhod space: `1`, and the times
`t` at which `ν`-almost every path is continuous. Their complement is countable
(`SkorokhodSpace.countable_compl_continuityTimes`) and the projections `π_J` with `J ⊆ T_ν`
are `ν`-a.e. continuous. -/
def continuityTimes (ν : Measure (SkorokhodSpace E)) : Set I :=
  {1} ∪ {t | ν {x | ¬ ContinuousAt (⇑x) t} = 0}

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma one_mem_continuityTimes (ν : Measure (SkorokhodSpace E)) : (1 : I) ∈ continuityTimes ν :=
  Or.inl rfl

lemma countable_compl_continuityTimes (ν : Measure (SkorokhodSpace E)) [IsFiniteMeasure ν] :
    (continuityTimes ν)ᶜ.Countable :=
  (countable_setOf_measure_not_continuousAt_ne_zero ν).mono fun _ ht h ↦
    ht (Or.inr h)

omit [SecondCountableTopology E] in
lemma measurable_restrict_finset (J : Finset I) :
    Measurable fun x : SkorokhodSpace E ↦ fun t : J ↦ x t :=
  measurable_pi_iff.2 fun t ↦ measurable_apply t.1

/-- **Continuous mapping for finite-dimensional projections**: if `μ_n → ν` weakly, then the
finite-dimensional distributions converge at the continuity times of `ν`. -/
theorem tendsto_map_restrict_of_tendsto {μs : ℕ → ProbabilityMeasure (SkorokhodSpace E)}
    {ν : ProbabilityMeasure (SkorokhodSpace E)} (h : Tendsto μs atTop (𝓝 ν)) {J : Finset I}
    (hJ : (J : Set I) ⊆ continuityTimes (ν : Measure (SkorokhodSpace E))) :
    Tendsto (fun n ↦ (μs n).map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t)) atTop
      (𝓝 (ν.map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t))) := by
  refine ProbabilityMeasure.tendsto_map_of_ae_continuousAt h (measurable_restrict_finset J) ?_
  have : ∀ᵐ x ∂(ν : Measure (SkorokhodSpace E)), ∀ t ∈ J, t ≠ 1 →
      ContinuousAt (⇑(x : SkorokhodSpace E)) t := by
    rw [Filter.eventually_all_finset]
    intro t ht
    rcases hJ ht with h1 | h0
    · exact Eventually.of_forall fun _ h ↦ absurd h1 h
    · rw [ae_iff] at *
      exact measure_mono_null (fun x hx ↦ (not_imp.1 hx).2) h0
  exact this.mono fun x hx ↦ continuousAt_restrict_of_ne_one hx

/-- A cluster point `ν` of a sequence `μ_n` whose finite-dimensional distributions converge to
those of `μ` on a co-countable set `T ∋ 1` is equal to `μ`. -/
lemma eq_of_mapClusterPt {μs : ℕ → ProbabilityMeasure (SkorokhodSpace E)}
    {μ ν : ProbabilityMeasure (SkorokhodSpace E)} {T : Set I} (hT : Tᶜ.Countable)
    (h1 : (1 : I) ∈ T)
    (hfdd : ∀ J : Finset I, (J : Set I) ⊆ T →
      Tendsto (fun n ↦ (μs n).map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t)) atTop
        (𝓝 (μ.map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t))))
    (hν : MapClusterPt ν atTop μs) : ν = μ := by
  obtain ⟨ψ, hψ, hψν⟩ := hν.tendsto_subseq
  set T' : Set I := T ∩ continuityTimes (ν : Measure (SkorokhodSpace E)) with hT'
  have hT'c : T'ᶜ.Countable := by
    rw [hT', compl_inter]
    exact hT.union (countable_compl_continuityTimes _)
  have hT'd : Dense T' := by simpa using dense_compl_of_countable hT'c
  have h1' : (1 : I) ∈ T' := ⟨h1, one_mem_continuityTimes _⟩
  refine ProbabilityMeasure.toMeasure_injective (ext_of_forall_map_restrict_eq hT'd h1'
    fun J hJ ↦ ?_)
  have hlim1 := tendsto_map_restrict_of_tendsto hψν fun t ht ↦ (hJ ht).2
  have hlim2 := (hfdd J fun t ht ↦ (hJ ht).1).comp hψ.tendsto_atTop
  have := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hlim1 hlim2)
  simpa using this

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma isCompact_closure_range {μs : ℕ → ProbabilityMeasure (SkorokhodSpace E)}
    (htight : IsTightMeasureSet (range fun n ↦ (μs n : Measure (SkorokhodSpace E)))) :
    IsCompact (closure (range μs)) := by
  refine isCompact_closure_of_isTightMeasureSet ?_
  convert htight using 2
  ext ν
  simp

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
    Tendsto μs atTop (𝓝 μ) :=
  (isCompact_closure_range htight).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n ↦ subset_closure (mem_range_self n))
    fun _ _ hν ↦ eq_of_mapClusterPt hT h1 hfdd hν

/-- **Existence of the limit** (Billingsley, Theorem 13.1, existence form). If `{μ_n}` is tight
and, for every finite set of times `J` in a co-countable set `T ∋ 1`, the finite-dimensional
distributions `μ_n π_J⁻¹` converge to some `ρ J`, then `μ_n` converges weakly to a probability
measure `μ` with `μ π_J⁻¹ = ρ J` whenever `J ⊆ T` consists of continuity times of `μ`. -/
theorem exists_tendsto_of_tendsto_map_restrict_of_isTight
    {μs : ℕ → ProbabilityMeasure (SkorokhodSpace E)} {T : Set I} (hT : Tᶜ.Countable)
    (h1 : (1 : I) ∈ T) (ρ : ∀ J : Finset I, ProbabilityMeasure (J → E))
    (hfdd : ∀ J : Finset I, (J : Set I) ⊆ T →
      Tendsto (fun n ↦ (μs n).map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t)) atTop
        (𝓝 (ρ J)))
    (htight : IsTightMeasureSet (range fun n ↦ (μs n : Measure (SkorokhodSpace E)))) :
    ∃ μ : ProbabilityMeasure (SkorokhodSpace E), Tendsto μs atTop (𝓝 μ) ∧
      ∀ J : Finset I, (J : Set I) ⊆ T ∩ continuityTimes (μ : Measure (SkorokhodSpace E)) →
        μ.map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t) = ρ J := by
  obtain ⟨μ, -, hμ⟩ := (isCompact_closure_range htight).exists_mapClusterPt
    (f := atTop) (u := μs) (tendsto_principal.2 (Eventually.of_forall fun n ↦ subset_closure (mem_range_self n)))
  obtain ⟨ψ, hψ, hψμ⟩ := hμ.tendsto_subseq
  have hρ : ∀ J : Finset I, (J : Set I) ⊆ T ∩ continuityTimes (μ : Measure (SkorokhodSpace E)) →
      μ.map (fun x : SkorokhodSpace E ↦ fun t : J ↦ x t) = ρ J := fun J hJ ↦
    tendsto_nhds_unique (tendsto_map_restrict_of_tendsto hψμ fun t ht ↦ (hJ ht).2)
      ((hfdd J fun t ht ↦ (hJ ht).1).comp hψ.tendsto_atTop)
  have hc : (T ∩ continuityTimes (μ : Measure (SkorokhodSpace E)))ᶜ.Countable := by
    rw [compl_inter]
    exact hT.union (countable_compl_continuityTimes _)
  refine ⟨μ, tendsto_of_tendsto_map_restrict_of_isTight hc ⟨h1, one_mem_continuityTimes _⟩
    (fun J hJ ↦ (hρ J hJ) ▸ hfdd J fun t ht ↦ (hJ ht).1) htight, hρ⟩

end SkorokhodSpace
