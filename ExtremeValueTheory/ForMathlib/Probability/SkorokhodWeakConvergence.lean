/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Probability.SkorokhodLaw
public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.ModulusCompact
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
finite-dimensional distributions on it determine the law
(`SkorokhodSpace.ext_of_forall_map_restrict_eq`).

## Main statements

* `unitInterval.dense_compl_of_countable`: a countable subset of `[0, 1]` has dense complement.
* `SkorokhodSpace.tendsto_of_tendsto_map_restrict_of_isTight`: **Billingsley, Theorem 13.1**.
* `SkorokhodSpace.exists_tendsto_of_tendsto_map_restrict_of_isTight`: the existence form: tightness
  and convergence of the finite-dimensional distributions give a weak limit.
* `SkorokhodSpace.isTightMeasureSet_of_cadlagModulus`: **Billingsley, Theorem 13.2**
  (sufficiency): tightness from the boundedness condition and the càdlàg modulus `w'`.

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
  (countable_setOf_measure_not_continuousAt_ne_zero ν).mono (by intro _ ht h; exact ht (Or.inr h))

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

/-- **Continuous mapping for families of times**: if `μ_n → ν` weakly and the times `τ i` are
continuity times of `ν`, then the laws of `(x (τ i))_i` converge. -/
theorem tendsto_map_comp_of_tendsto {ι : Type*} [Fintype ι]
    {μs : ℕ → ProbabilityMeasure (SkorokhodSpace E)} {ν : ProbabilityMeasure (SkorokhodSpace E)}
    (h : Tendsto μs atTop (𝓝 ν)) {τ : ι → I}
    (hτ : ∀ i, τ i ∈ continuityTimes (ν : Measure (SkorokhodSpace E))) :
    Tendsto (fun n ↦ (μs n).map (fun x : SkorokhodSpace E ↦ fun i ↦ x (τ i))) atTop
      (𝓝 (ν.map (fun x : SkorokhodSpace E ↦ fun i ↦ x (τ i)))) := by
  refine ProbabilityMeasure.tendsto_map_of_ae_continuousAt h
    (measurable_pi_iff.2 fun i ↦ measurable_apply (τ i)) ?_
  have : ∀ᵐ x ∂(ν : Measure (SkorokhodSpace E)), ∀ i, τ i ≠ 1 →
      ContinuousAt (⇑(x : SkorokhodSpace E)) (τ i) := by
    rw [ae_all_iff]
    intro i
    rcases hτ i with h1 | h0
    · exact Eventually.of_forall fun _ h ↦ absurd h1 h
    · rw [ae_iff] at *
      exact measure_mono_null (fun x hx ↦ (not_imp.1 hx).2) h0
  refine this.mono fun x hx ↦ continuousAt_pi.2 fun i ↦ ?_
  by_cases hi : τ i = 1
  · simp only [hi]
    exact continuous_apply_one.continuousAt
  · exact tendsto_apply_of_continuousAt (x := fun y : SkorokhodSpace E ↦ y) tendsto_id (hx i hi)

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
    (f := atTop) (u := μs)
    (tendsto_principal.2 (Eventually.of_forall fun n ↦ subset_closure (mem_range_self n)))
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

/-! ### Tightness via the càdlàg modulus -/

section Tight

variable [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A single finite measure on the Skorokhod space is tight (the space is Polish). -/
lemma exists_isCompact_measure_compl_le (μ : Measure (SkorokhodSpace E)) [IsFiniteMeasure μ]
    {η : ℝ≥0∞} (hη : 0 < η) : ∃ K : Set (SkorokhodSpace E), IsCompact K ∧ μ Kᶜ ≤ η := by
  obtain ⟨K, hK, h⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := μ)) η hη
  exact ⟨K, hK, h μ rfl⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_totallyBounded_measure_le (μ : Measure (SkorokhodSpace E)) [IsFiniteMeasure μ]
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ C : Set E, TotallyBounded C ∧ μ {x | ∃ t, x t ∉ C} ≤ η := by
  obtain ⟨K, hK, hμK⟩ := exists_isCompact_measure_compl_le μ hη
  obtain ⟨C, hC, hKC⟩ := exists_totallyBounded_of_isCompact hK
  refine ⟨C, hC, (measure_mono (show {x : SkorokhodSpace E | ∃ t, x t ∉ C} ⊆ Kᶜ from
    fun x hx hxK ↦ hx.elim fun t ht ↦ ht (hKC x hxK t))).trans hμK⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_cadlagModulus_measure_le (μ : Measure (SkorokhodSpace E)) [IsFiniteMeasure μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, μ {x | ε ≤ cadlagModulus (⇑x) δ} ≤ η := by
  obtain ⟨K, hK, hμK⟩ := exists_isCompact_measure_compl_le μ hη
  obtain ⟨δ, hδ, hKδ⟩ := exists_forall_cadlagModulus_lt_of_isCompact hK hε
  exact ⟨δ, hδ, (measure_mono (by intro x hx hxK; exact not_le.2 (hKδ x hxK) hx)).trans hμK⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Billingsley, Theorem 13.2** (sufficiency). A sequence of probability measures `μ_n` on the
Skorokhod space `D([0, 1], E)` is tight if
1. for every `η > 0` there is a totally bounded `C ⊆ E` such that eventually
   `μ_n {x | ∃ t, x t ∉ C} ≤ η`, and
2. for all `ε, η > 0` there is `δ > 0` such that eventually `μ_n {x | ε ≤ w'_x(δ)} ≤ η`,
where `w'` is the càdlàg modulus `cadlagModulus`. (No measurability of the sets involved is
needed: the measures are applied as outer measures.) -/
theorem isTightMeasureSet_of_cadlagModulus {μs : ℕ → Measure (SkorokhodSpace E)}
    [∀ n, IsProbabilityMeasure (μs n)]
    (hbdd : ∀ η : ℝ≥0∞, 0 < η → ∃ C : Set E, TotallyBounded C ∧
      ∀ᶠ n in atTop, μs n {x | ∃ t, x t ∉ C} ≤ η)
    (hmod : ∀ ε : ℝ≥0∞, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ > 0,
      ∀ᶠ n in atTop, μs n {x | ε ≤ cadlagModulus (⇑x) δ} ≤ η) :
    IsTightMeasureSet (range μs) := by
  classical
  -- upgrade the eventual bounds to bounds for every `n`, using the tightness of each `μ_n`
  have hbdd' : ∀ η : ℝ≥0∞, 0 < η → ∃ C : Set E, TotallyBounded C ∧
      ∀ n, μs n {x | ∃ t, x t ∉ C} ≤ η := by
    intro η hη
    obtain ⟨C₀, hC₀, hev⟩ := hbdd η hη
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    choose C hC hμC using fun n ↦ exists_totallyBounded_measure_le (μs n) hη
    refine ⟨C₀ ∪ ⋃ n ∈ Finset.range N, C n, hC₀.union
      (totallyBounded_biUnion (Finset.range N).finite_toSet |>.2 fun n _ ↦ hC n), fun n ↦ ?_⟩
    rcases lt_or_ge n N with hn | hn
    · refine (measure_mono (by
        intro x hx
        exact hx.imp fun t ht h ↦
          ht (Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hn)) h)))).trans (hμC n)
    · exact (measure_mono (by intro x hx; exact hx.imp fun t ht h ↦ ht (Or.inl h))).trans (hN n hn)
  have hmod' : ∀ ε : ℝ≥0∞, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ > 0,
      ∀ n, μs n {x | ε ≤ cadlagModulus (⇑x) δ} ≤ η := by
    intro ε hε η hη
    obtain ⟨δ₀, hδ₀, hev⟩ := hmod ε hε η hη
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    choose δ' hδ' hμδ using fun n ↦ exists_cadlagModulus_measure_le (μs n) hε hη
    set S : Finset ℝ := insert δ₀ ((Finset.range N).image δ')
    have hSne : S.Nonempty := Finset.insert_nonempty _ _
    refine ⟨S.min' hSne, (Finset.lt_min'_iff _ _).2 fun r hr ↦ ?_, fun n ↦ ?_⟩
    · rcases Finset.mem_insert.1 hr with rfl | hr
      · exact hδ₀
      · obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hr
        exact hδ' n
    · rcases lt_or_ge n N with hn | hn
      · refine (measure_mono (by
          intro x hx
          exact hx.trans (cadlagModulus_mono _ (S.min'_le _
            (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 hn))))))).trans
          (hμδ n)
      · exact (measure_mono (by
          intro x hx
          exact hx.trans (cadlagModulus_mono _ (S.min'_le _ (Finset.mem_insert_self _ _))))).trans
          (hN n hn)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨C, hC, hμC⟩ := hbdd' (η / 2) hη2
  have hηj (j : ℕ) : 0 < η / 2 / 2 * 2⁻¹ ^ j :=
    ENNReal.mul_pos (ENNReal.half_pos hη2.ne').ne' (pow_ne_zero _ (by simp))
  have hεj (j : ℕ) : 0 < ((j : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
  choose δ hδ hμδ using fun j ↦ hmod' _ (hεj j) _ (hηj j)
  set K : Set (SkorokhodSpace E) := {x | ∀ t, x t ∈ C} ∩
    ⋂ j : ℕ, {x | cadlagModulus (⇑x) (δ j) < ((j : ℝ≥0∞) + 1)⁻¹} with hKdef
  have hKc : IsCompact (closure K) := by
    refine isCompact_closure_of_cadlagModulus hC (fun x hx ↦ hx.1) fun ε hε ↦ ?_
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine ⟨δ j, hδ j, fun x hx ↦ (mem_iInter.1 hx.2 j).trans_le ?_⟩
    exact (ENNReal.inv_le_inv.2 le_self_add).trans hj.le
  refine ⟨closure K, hKc, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hsub : (closure K)ᶜ ⊆ {x | ∃ t, x t ∉ C} ∪
      ⋃ j : ℕ, {x | ((j : ℝ≥0∞) + 1)⁻¹ ≤ cadlagModulus (⇑x) (δ j)} := by
    intro x hx
    have hxK : x ∉ K := fun h ↦ hx (subset_closure h)
    simp only [hKdef, mem_inter_iff, mem_ofPred_eq, mem_iInter, not_and_or, not_forall,
      not_lt] at hxK
    rcases hxK with ⟨t, ht⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨t, ht⟩
    · exact Or.inr (mem_iUnion.2 ⟨j, hj⟩)
  calc μs n (closure K)ᶜ
      ≤ μs n {x | ∃ t, x t ∉ C} +
        ∑' j : ℕ, μs n {x | ((j : ℝ≥0∞) + 1)⁻¹ ≤ cadlagModulus (⇑x) (δ j)} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_iUnion_le _)))
    _ ≤ η / 2 + ∑' j : ℕ, η / 2 / 2 * 2⁻¹ ^ j :=
        add_le_add (hμC n) (ENNReal.tsum_le_tsum fun j ↦ hμδ j n)
    _ = η := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two,
          ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, ENNReal.add_halves]

end Tight

end SkorokhodSpace
