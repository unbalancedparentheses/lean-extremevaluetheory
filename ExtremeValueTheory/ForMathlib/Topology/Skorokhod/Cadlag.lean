/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.Order.T5
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Order.Interval.Set.OrdConnectedComponent
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Càdlàg functions on a compact interval

Let `X` be a compact, densely ordered, conditionally complete linear order with the order
topology (for instance the unit interval `[0, 1]`), and let `f : X → E` be càdlàg with values
in a pseudo extended metric space. We prove the basic structure theorem for such functions,
[Billingsley, *Convergence of Probability Measures*, Lemma 12.1][billingsley1999]: for every
`ε > 0` there are finitely many points such that `f` oscillates by less than `ε` on every cell of
the induced partition of `X` into half-open intervals `[tᵢ₋₁, tᵢ)`.

We encode the partition by a finite set `s` of cut points: two points `t ≤ u` lie in the same
cell when no cut point lies in `(t, u]`.

## Main statements

* `IsCadlag.exists_finset_edist_lt`: Billingsley's Lemma 12.1.
* `IsCadlag.exists_finite_range_edist_lt`: a càdlàg function is a uniform limit of functions
  with finitely many values (step functions).
* `IsCadlag.measurable`: a càdlàg function is Borel measurable.
* `IsCadlag.finite_setOf_lt_edist_leftLim`: a càdlàg function has only finitely many jumps of
  size larger than `ε`.
* `IsCadlag.countable_setOf_edist_leftLim_ne_zero`, `IsCadlag.countable_setOf_leftLim_ne`:
  a càdlàg function has at most countably many jumps.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

public section

open Filter Set Topology Metric
open scoped ENNReal

/-- An order connected component of an open set in a linear order is open. -/
lemma IsOpen.ordConnectedComponent {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {s : Set α} (hs : IsOpen s) (x : α) :
    IsOpen (ordConnectedComponent s x) := by
  refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
  rw [ordConnectedComponent_eq (mem_ordConnectedComponent.1 hy)]
  exact ordConnectedComponent_mem_nhds.2
    (hs.mem_nhds (mem_ordConnectedComponent.1 hy right_mem_uIcc))

variable {X E : Type*} [ConditionallyCompleteLinearOrder X] [DenselyOrdered X]
  [TopologicalSpace X] [OrderTopology X] [CompactSpace X] [PseudoEMetricSpace E] {f : X → E}

/-- **Billingsley, Lemma 12.1.** For a càdlàg function `f` on a compact interval and `ε > 0`
there is a finite set `s` of cut points such that `f` oscillates by less than `ε` on every cell
of the induced partition: `edist (f t) (f u) < ε` whenever `t ≤ u` and no point of `s` lies in
`(t, u]`. -/
theorem IsCadlag.exists_finset_edist_lt (hf : IsCadlag f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : Finset X, ∀ t u, t ≤ u → (∀ r ∈ s, r ≤ t ∨ u < r) → edist (f t) (f u) < ε := by
  have hε₂ : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hδ : 0 < ε / 2 / 2 := ENNReal.half_pos hε₂.ne'
  choose l hl using hf.tendsto_nhdsLT
  -- `U c`: the points to the right of `c` where `f` is close to `f c`, and the points to the left
  -- of `c` where `f` is close to the left limit `l c`.
  set U : X → Set X := fun c ↦
    {u | (c ≤ u → edist (f u) (f c) < ε / 2 / 2) ∧ (u < c → edist (f u) (l c) < ε / 2 / 2)}
  have hU (c : X) : U c ∈ 𝓝 c := by
    rw [← nhdsLT_sup_nhdsGE, mem_sup]
    constructor
    · filter_upwards [self_mem_nhdsWithin, (hl c).eventually (eball_mem_nhds _ hδ)] with u hu h
      exact ⟨fun h' ↦ absurd hu (not_lt.2 h'), fun _ ↦ h⟩
    · filter_upwards [self_mem_nhdsWithin, (continuousWithinAt_Ioi_iff_Ici.1
        (hf.isRightContinuous c)).tendsto.eventually (eball_mem_nhds _ hδ)] with u hu h
      exact ⟨fun _ ↦ h, fun h' ↦ absurd (mem_Ici.1 hu) (not_le.2 h')⟩
  have hright (c v w : X) (hv : v ∈ U c) (hw : w ∈ U c) (hcv : c ≤ v) (hcw : c ≤ w) :
      edist (f v) (f w) < ε / 2 := by
    rw [← ENNReal.add_halves (ε / 2)]
    exact (edist_triangle_right _ _ (f c)).trans_lt (ENNReal.add_lt_add (hv.1 hcv) (hw.1 hcw))
  have hleft (c v w : X) (hv : v ∈ U c) (hw : w ∈ U c) (hcv : v < c) (hcw : w < c) :
      edist (f v) (f w) < ε / 2 := by
    rw [← ENNReal.add_halves (ε / 2)]
    exact (edist_triangle_right _ _ (l c)).trans_lt (ENNReal.add_lt_add (hv.2 hcv) (hw.2 hcw))
  -- `V c`: an open order connected neighbourhood of `c` inside `U c`.
  set V : X → Set X := fun c ↦ ordConnectedComponent (interior (U c)) c
  have hVo (c : X) : IsOpen (V c) := isOpen_interior.ordConnectedComponent c
  have hVc (c : X) : c ∈ V c :=
    self_mem_ordConnectedComponent.2 (mem_interior_iff_mem_nhds.2 (hU c))
  have hVU (c : X) : V c ⊆ U c := ordConnectedComponent_subset.trans interior_subset
  obtain ⟨T, -, hT⟩ := isCompact_univ.elim_nhds_subcover V fun c _ ↦ (hVo c).mem_nhds (hVc c)
  have hcover (m : X) : ∃ c ∈ T, m ∈ V c := by simpa using hT (mem_univ m)
  have hVconv (c : X) : (V c).OrdConnected := inferInstance
  refine ⟨T, fun t u htu hs ↦ ?_⟩
  obtain ⟨c₁, hc₁T, htc₁⟩ := hcover t
  obtain ⟨c₂, hc₂T, huc₂⟩ := hcover u
  rcases hs c₁ hc₁T with hc₁ | hc₁
  · rcases hs c₂ hc₂T with hc₂ | hc₂
    · -- `c₂ ≤ t ≤ u`: both points lie to the right of `c₂` in `V c₂`.
      have ht : t ∈ V c₂ := (hVconv c₂).out (hVc c₂) huc₂ ⟨hc₂, htu⟩
      exact (hright c₂ t u (hVU _ ht) (hVU _ huc₂) hc₂ (hc₂.trans htu)).trans_le
        ENNReal.half_le_self
    · -- `c₁ ≤ t ≤ u < c₂`: by connectedness of `[t, u]` some `m ∈ [t, u]` lies both in a
      -- neighbourhood `V c` with `c ≤ t` and in a neighbourhood `V c'` with `u < c'`.
      have hsub : Icc t u ⊆ (⋃ c ∈ T, ⋃ (_ : c ≤ t), V c) ∪ ⋃ c ∈ T, ⋃ (_ : u < c), V c := by
        intro m _
        obtain ⟨c, hcT, hmc⟩ := hcover m
        rcases hs c hcT with h | h
        · exact Or.inl (mem_iUnion₂.2 ⟨c, hcT, mem_iUnion.2 ⟨h, hmc⟩⟩)
        · exact Or.inr (mem_iUnion₂.2 ⟨c, hcT, mem_iUnion.2 ⟨h, hmc⟩⟩)
      obtain ⟨m, hm, hmL, hmR⟩ := isPreconnected_Icc _ _
        (isOpen_biUnion fun c _ ↦ isOpen_iUnion fun _ ↦ hVo c)
        (isOpen_biUnion fun c _ ↦ isOpen_iUnion fun _ ↦ hVo c) hsub
        ⟨t, left_mem_Icc.2 htu, mem_iUnion₂.2 ⟨c₁, hc₁T, mem_iUnion.2 ⟨hc₁, htc₁⟩⟩⟩
        ⟨u, right_mem_Icc.2 htu, mem_iUnion₂.2 ⟨c₂, hc₂T, mem_iUnion.2 ⟨hc₂, huc₂⟩⟩⟩
      simp only [mem_iUnion] at hmL hmR
      obtain ⟨c, -, hct, hmc⟩ := hmL
      obtain ⟨c', -, huc', hmc'⟩ := hmR
      have ht : t ∈ V c := (hVconv c).out (hVc c) hmc ⟨hct, hm.1⟩
      have hu : u ∈ V c' := (hVconv c').out hmc' (hVc c') ⟨hm.2, huc'.le⟩
      calc edist (f t) (f u) ≤ edist (f t) (f m) + edist (f m) (f u) := edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add
          (hright c t m (hVU _ ht) (hVU _ hmc) hct (hct.trans hm.1))
          (hleft c' m u (hVU _ hmc') (hVU _ hu) (hm.2.trans_lt huc') huc')
        _ = ε := ENNReal.add_halves ε
  · -- `t ≤ u < c₁`: both points lie to the left of `c₁` in `V c₁`.
    have hu : u ∈ V c₁ := (hVconv c₁).out htc₁ (hVc c₁) ⟨htu, hc₁.le⟩
    exact (hleft c₁ t u (hVU _ htc₁) (hVU _ hu) (htu.trans_lt hc₁) hc₁).trans_le
      ENNReal.half_le_self

/-- A càdlàg function on a compact interval is uniformly close to a function of the form `f ∘ p`
with `p : X → X` monotone with finite range: `p t` is the last cut point of Lemma 12.1 before `t`.
-/
theorem IsCadlag.exists_monotone_finite_range_edist_lt (hf : IsCadlag f) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ p : X → X, Monotone p ∧ (range p).Finite ∧ ∀ t, edist (f t) (f (p t)) < ε := by
  classical
  obtain ⟨s, hs⟩ := hf.exists_finset_edist_lt hε
  -- `p t` is the last cut point before `t`, or the minimum of `X` if there is none.
  let p : X → X := fun t ↦
    if h : (s.filter (· ≤ t)).Nonempty then (s.filter (· ≤ t)).max' h else sInf univ
  have hbot (t : X) : sInf univ ≤ t := csInf_le isCompact_univ.bddBelow (mem_univ t)
  have hp (t : X) : p t ≤ t ∧ ∀ r ∈ s, r ≤ p t ∨ t < r := by
    simp only [p]
    split_ifs with h
    · refine ⟨(Finset.mem_filter.1 (Finset.max'_mem _ h)).2, fun r hr ↦ ?_⟩
      by_cases hrt : r ≤ t
      · exact Or.inl (Finset.le_max' _ r (Finset.mem_filter.2 ⟨hr, hrt⟩))
      · exact Or.inr (not_le.1 hrt)
    · refine ⟨hbot t, fun r hr ↦ Or.inr (not_le.1 ?_)⟩
      exact fun hrt ↦ h ⟨r, Finset.mem_filter.2 ⟨hr, hrt⟩⟩
  have hmono : Monotone p := by
    intro t t' htt'
    have hsub : s.filter (· ≤ t) ⊆ s.filter (· ≤ t') := fun r hr ↦ by
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, hr.2.trans htt'⟩
    simp only [p]
    split_ifs with h h'
    · exact Finset.max'_subset h hsub
    · exact absurd (h.mono hsub) h'
    · exact hbot _
    · exact le_rfl
  have hrange : range p ⊆ insert (sInf univ) (s : Set X) := by
    rintro _ ⟨t, rfl⟩
    simp only [p]
    split_ifs with h
    · exact Or.inr (Finset.mem_filter.1 (Finset.max'_mem _ h)).1
    · exact Or.inl rfl
  refine ⟨p, hmono, (s.finite_toSet.insert _).subset hrange, fun t ↦ ?_⟩
  rw [edist_comm]
  exact hs _ _ (hp t).1 (hp t).2

/-- A càdlàg function on a compact interval is a uniform limit of functions with finitely many
values: for every `ε > 0` there is a step function `g` with `edist (f t) (g t) < ε` for all
`t` ([Billingsley, §12][billingsley1999]). -/
theorem IsCadlag.exists_finite_range_edist_lt (hf : IsCadlag f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : X → E, (range g).Finite ∧ ∀ t, edist (f t) (g t) < ε := by
  obtain ⟨p, -, hp, hfp⟩ := hf.exists_monotone_finite_range_edist_lt hε
  exact ⟨f ∘ p, by rw [range_comp]; exact hp.image f, hfp⟩

/-- A càdlàg function on a compact second countable interval is Borel measurable. -/
theorem IsCadlag.measurable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace E] [BorelSpace E] (hf : IsCadlag f) : Measurable f := by
  have hε (n : ℕ) : (0 : ℝ≥0∞) < (n + 1 : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 (by simp)
  choose p hpm hpr hfp using fun n : ℕ ↦ hf.exists_monotone_finite_range_edist_lt (hε n)
  refine measurable_of_tendsto_metrizable (f := fun n ↦ f ∘ p n) (fun n B _ ↦ ?_)
    (tendsto_pi_nhds.2 fun t ↦ ?_)
  · rw [preimage_comp, ← preimage_inter_range]
    exact (hpm n).measurable (((hpr n).subset inter_subset_right).measurableSet)
  · refine EMetric.tendsto_atTop.2 fun ε hε' ↦ ?_
    obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hε'.ne'
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [edist_comm]
    refine (hfp n t).trans (lt_of_le_of_lt ?_ hN)
    gcongr
    exact le_add_right (by exact_mod_cast hn)

/-- A càdlàg function on a compact interval has only finitely many jumps of size larger than
`ε` ([Billingsley, §12][billingsley1999]). -/
theorem IsCadlag.finite_setOf_lt_edist_leftLim (hf : IsCadlag f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    {t | ε < edist (Function.leftLim f t) (f t)}.Finite := by
  obtain ⟨s, hs⟩ := hf.exists_finset_edist_lt hε
  refine s.finite_toSet.subset fun t ht ↦ ?_
  by_contra hts
  refine (not_le.2 (show ε < _ from ht)) ?_
  rcases eq_or_neBot (𝓝[<] t) with h | h
  · simp [leftLim_eq_of_eq_bot _ h]
  have hev : ∀ᶠ u in 𝓝[<] t, edist (f u) (f t) < ε := by
    have : ∀ᶠ u in 𝓝[<] t, ∀ r ∈ s, r ≤ u ∨ t < r := by
      refine (Finset.eventually_all s).2 fun r hr ↦ ?_
      rcases lt_or_gt_of_ne (fun h : r = t ↦ hts (h ▸ hr)) with hrt | hrt
      · exact (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hrt)).mono
          fun u hu ↦ Or.inl hu.le
      · exact Eventually.of_forall fun _ ↦ Or.inr hrt
    filter_upwards [this, self_mem_nhdsWithin] with u hu hut
    exact hs u t (le_of_lt hut) hu
  exact le_of_tendsto ((hf.tendsto_nhdsLT_leftLim t).edist tendsto_const_nhds)
    (hev.mono fun _ h ↦ h.le)

/-- A càdlàg function on a compact interval has at most countably many jumps
([Billingsley, §12][billingsley1999]). -/
theorem IsCadlag.countable_setOf_edist_leftLim_ne_zero (hf : IsCadlag f) :
    {t | edist (Function.leftLim f t) (f t) ≠ 0}.Countable := by
  refine (countable_iUnion fun n : ℕ ↦
    (hf.finite_setOf_lt_edist_leftLim (ε := (n : ℝ≥0∞)⁻¹)
      (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))).countable).mono fun t ht ↦ ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt ht
  exact mem_iUnion.2 ⟨n, hn⟩

/-- A càdlàg function on a compact interval has at most countably many discontinuities of the
first kind, i.e. points where the left limit differs from the value. -/
theorem IsCadlag.countable_setOf_leftLim_ne {E : Type*} [EMetricSpace E] {f : X → E}
    (hf : IsCadlag f) : {t | Function.leftLim f t ≠ f t}.Countable :=
  hf.countable_setOf_edist_leftLim_ne_zero.mono fun _ ht h ↦ ht (edist_eq_zero.1 h)
