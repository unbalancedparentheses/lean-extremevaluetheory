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
* `IsCadlag.finite_setOf_lt_edist_leftLim`: a càdlàg function has only finitely many jumps of
  size larger than `ε`.
* `IsCadlag.countable_setOf_leftLim_ne`: a càdlàg function has at most countably many jumps.

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
  have hVc (c : X) : c ∈ V c := self_mem_ordConnectedComponent.2 (mem_interior_iff_mem_nhds.2 (hU c))
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
