/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Joel Kronqvist, ...
Modified by Federico Carrone, 2026, from kkytola/ExtremeValueProject (commit f7c9a8ce260d):
ported to Lean/Mathlib v4.35.0 and renamed `ExtremeValueProject` to `ExtremeValueTheory`.
-/
import Mathlib
import ExtremeValueTheory.AffineTransformation

section cauchy_hamel_functional_equation

open Real Set Pointwise MeasureTheory

lemma eq_iUnion_connectedComponentIn (U : Set ℝ) :
    U = ⋃ x ∈ U, connectedComponentIn U x := by
  apply subset_antisymm
  · intro x x_in_U
    simpa using ⟨x, x_in_U, mem_connectedComponentIn x_in_U⟩
  · simp only [iUnion_subset_iff]
    intro x x_in_U
    exact connectedComponentIn_subset U x

lemma eq_sUnion_connectedComponentIn (U : Set ℝ) :
    U = ⋃₀ {C | ∃ x ∈ U, C = connectedComponentIn U x} := by
  apply subset_antisymm
  · intro x x_in_U
    simpa using ⟨x, x_in_U, mem_connectedComponentIn x_in_U⟩
  · simp only [sUnion_subset_iff, mem_setOf_eq, forall_exists_index, and_imp]
    intro C x x_in_U hC
    simpa [hC] using connectedComponentIn_subset U x

-- TODO: This seems to be missing in Mathlib. Compare with `connectedComponent_disjoint`.
lemma connectedComponentIn_disjoint {α : Type*} [TopologicalSpace α] {s : Set α} {x y : α}
    (h : connectedComponentIn s x ≠ connectedComponentIn s y) :
    Disjoint (connectedComponentIn s x) (connectedComponentIn s y) :=
  Set.disjoint_left.2 fun _ hzx hzy ↦
    h <| (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm

-- TODO: Maybe not really needed; we have `connectedComponentIn_disjoint`.
lemma pairwise_disjoint_connectedComponentIn (U : Set ℝ) :
    {C | ∃ x ∈ U, C = connectedComponentIn U x}.Pairwise Disjoint := by
  intro C hC D hD hCD
  obtain ⟨x, x_in_U, C_eq⟩ := hC
  obtain ⟨y, y_in_U, D_eq⟩ := hD
  rw [C_eq, D_eq] at hCD ⊢
  exact connectedComponentIn_disjoint hCD

-- TODO: Is this missing from Mathlib?
lemma IsOpen.isOpen_connectedComponentIn {α : Type*} [TopologicalSpace α]
    {s : Set α} (s_loc_conn : LocallyConnectedSpace s) (s_open : IsOpen s) {x : α} :
    IsOpen (connectedComponentIn s x) := by
  by_cases hxs : x ∉ s
  · simp [connectedComponentIn, hxs]
  rw [not_not] at hxs
  simp only [connectedComponentIn, hxs, ↓reduceDIte]
  obtain ⟨U, U_open, hU⟩ := @isOpen_connectedComponent s _ s_loc_conn ⟨x, hxs⟩
  have obs : Subtype.val '' connectedComponent ⟨x, hxs⟩ = U ∩ s := by
    ext y
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, mem_inter_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨y_in_s, hy⟩
      exact ⟨by simpa [← hU] using hy, y_in_s⟩
    · intro ⟨y_in_U, y_in_s⟩
      exact ⟨y_in_s, by simpa [← hU] using y_in_U⟩
  simpa [obs] using U_open.inter s_open

private lemma TopologicalSpace.SeparableSpace.countable_of_disjoint_of_isOpen_of_nonempty
    {α : Type*} [TopologicalSpace α] (sep : SeparableSpace α) {As : Set (Set α)}
    (As_disj : As.Pairwise Disjoint) (As_open : ∀ A ∈ As, IsOpen A)
    (As_nonemp : ∀ A ∈ As, A.Nonempty)  :
    As.Countable := by
  obtain ⟨s, s_ctble, s_dense⟩ := sep.exists_countable_dense
  have aux (A) (hA : A ∈ As) : ∃ x ∈ s, x ∈ A :=
    s_dense.exists_mem_open (As_open A hA) (As_nonemp A hA)
  set g : As → s := fun A ↦ ⟨(aux A.val A.prop).choose, (aux A.val A.prop).choose_spec.1⟩ with def_g
  have hg (A : As) : (g A).val ∈ A.val := (aux A.val A.prop).choose_spec.2
  have g_inj : Function.Injective g := by
    intro A B hAB
    by_contra maybe_ne
    apply (As_disj A.prop B.prop (Subtype.coe_ne_coe.mpr maybe_ne)).notMem_of_mem_left (hg A)
    simpa [← hAB] using (hg B)
  rw [Set.countable_iff_exists_injective] at s_ctble ⊢
  obtain ⟨f, f_inj⟩ := s_ctble
  refine ⟨f ∘ g, f_inj.comp g_inj⟩

-- TODO: Is this missing from Mathlib?
lemma TopologicalSpace.SeparableSpace.countable_of_disjoint_of_isOpen
    {α : Type*} [TopologicalSpace α] (sep : SeparableSpace α) {As : Set (Set α)}
    (As_disj : As.Pairwise Disjoint) (As_open : ∀ A ∈ As, IsOpen A) :
    As.Countable := by
  suffices (As \ {∅}).Countable from
    Countable.mono (show As ⊆ (As \ {∅}) ∪ {∅} by simp) (this.union (countable_singleton ∅))
  apply countable_of_disjoint_of_isOpen_of_nonempty sep
  · exact As_disj.mono sdiff_subset
  · exact fun A hA ↦ As_open A (mem_of_mem_sdiff hA)
  · intro A hA
    simp only [mem_sdiff, mem_singleton_iff] at hA
    exact nonempty_iff_ne_empty.mpr hA.2

lemma ConnectedComponents.mk_eq_mk_iff {α : Type*} [TopologicalSpace α] {x y : α} :
    ConnectedComponents.mk x = ConnectedComponents.mk y
      ↔ connectedComponent x = connectedComponent y := by
  simp_all only [coe_eq_coe]

lemma ConnectedComponents.mk_out_eq {α : Type*} [TopologicalSpace α] (C : ConnectedComponents α) :
    ConnectedComponents.mk (Quot.out C) = C :=
  Quotient.out_eq _

--lemma ConnectedComponents.out_mem_connectedComponent {α : Type*} [TopologicalSpace α] (C : ConnectedComponents α) :
--    (Quot.out C) ∈ connectedComponent (Quot.out C) := by
--  exact mem_connectedComponent

lemma TopologicalSpace.SeparableSpace.countable_connectedComponents {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] (sep : SeparableSpace α) :
    Countable (ConnectedComponents α) := by
  set φ : ConnectedComponents α → Set α := (fun A ↦ connectedComponent (Quot.out A)) with def_φ
  set As : Set (Set α) := Set.range φ with def_As
  have key := @countable_of_disjoint_of_isOpen α _ sep As ?_ ?_
  · obtain ⟨f, f_inj⟩ := Set.countable_iff_exists_injective.mp key
    apply (countable_iff_exists_injective _).mpr ⟨fun C ↦ f (rangeFactorization φ C), f_inj.comp ?_⟩
    intro C₁ C₂ hC
    simp only [rangeFactorization, Subtype.mk.injEq, φ, As] at hC
    exact Quotient.out_equiv_out.mp hC
  · intro A₁ hA₁ A₂ hA₂ hA_ne
    simp only [mem_range, As, φ] at hA₁ hA₂
    obtain ⟨C₁, hC₁⟩ := hA₁
    obtain ⟨C₂, hC₂⟩ := hA₂
    rw [← hC₁, ← hC₂] at hA_ne ⊢
    exact connectedComponent_disjoint hA_ne
  · intro A hA
    simp only [def_As, mem_range, As, φ] at hA
    obtain ⟨C, hAC⟩ := hA
    simpa [← hAC] using isOpen_connectedComponent

-- TODO: Missing from Mathlib?
open TopologicalSpace in
lemma IsOpen.separableSpace {α : Type*} [TopologicalSpace α] [SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    SeparableSpace s := by
  obtain ⟨c, c_ctble, c_dense⟩ := ‹SeparableSpace α›.exists_countable_dense
  refine ⟨⟨(↑) ⁻¹' c, c_ctble.preimage Subtype.val_injective, ?_⟩⟩
  simpa [Subtype.dense_iff] using c_dense.open_subset_closure_inter s_open

open TopologicalSpace in
lemma IsOpen.countable_setOf_connectedComponentIn
    {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α] [sep : SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    Countable {C : Set α | ∃ x ∈ s, C = connectedComponentIn s x} := by
  have : LocallyConnectedSpace s := s_open.locallyConnectedSpace
  have sep_s : SeparableSpace s := s_open.separableSpace
  have key := SeparableSpace.countable_connectedComponents (α := s) inferInstance
  let ψ : {C : Set α | ∃ x ∈ s, C = connectedComponentIn s x} → ConnectedComponents s :=
    fun C ↦ ConnectedComponents.mk
            ⟨(mem_setOf_eq.mp C.prop).choose, (mem_setOf_eq.mp C.prop).choose_spec.1⟩
  have ψ_inj : Function.Injective ψ := by
    intro C₁ C₂ hψC
    ext1
    have aux₁ := (mem_setOf_eq.mp C₁.prop).choose_spec
    have aux₂ := (mem_setOf_eq.mp C₂.prop).choose_spec
    rw [aux₁.2, aux₂.2]
    simp only [ψ, ConnectedComponents.coe_eq_coe] at hψC
    rw [connectedComponentIn_eq_image aux₁.1, connectedComponentIn_eq_image aux₂.1]
    exact congr_arg (Subtype.val '' ·) hψC
  exact Function.Injective.countable ψ_inj

-- TODO: Hopefully this is not needed and `Real.convex_iff_isPreconnected` is enough.
lemma Real.eq_Ioo_or_Iio_or_Ioi_or_univ_of_isOpen_of_isConnected
    {U : Set ℝ} (U_open : IsOpen U) (U_conn : IsConnected U) :
    (∃ a b, U = Ioo a b) ∨ (∃ b, U = Iio b) ∨ (∃ a, U = Ioi a) ∨ U = univ := by
  have inf_notMem (hb : BddBelow U) : sInf U ∉ U := by
    intro h
    obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.mp U_open _ h
    have : sInf U - ε / 2 ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith [csInf_le hb this]
  have sup_notMem (ha : BddAbove U) : sSup U ∉ U := by
    intro h
    obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.mp U_open _ h
    have : sSup U + ε / 2 ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith [le_csSup ha this]
  by_cases hb : BddBelow U <;> by_cases ha : BddAbove U
  · refine Or.inl ⟨sInf U, sSup U, subset_antisymm (fun x hx ↦ ?_)
      (U_conn.Ioo_csInf_csSup_subset hb ha)⟩
    refine ⟨lt_of_le_of_ne (csInf_le hb hx) ?_, lt_of_le_of_ne (le_csSup ha hx) ?_⟩
    · rintro rfl; exact inf_notMem hb hx
    · rintro rfl; exact sup_notMem ha hx
  · refine Or.inr (Or.inr (Or.inl ⟨sInf U, subset_antisymm (fun x hx ↦ ?_)
      (U_conn.isPreconnected.Ioi_csInf_subset hb ha)⟩))
    refine lt_of_le_of_ne (csInf_le hb hx) ?_
    rintro rfl; exact inf_notMem hb hx
  · refine Or.inr (Or.inl ⟨sSup U, subset_antisymm (fun x hx ↦ ?_)
      (U_conn.isPreconnected.Iio_csSup_subset hb ha)⟩)
    refine lt_of_le_of_ne (le_csSup ha hx) ?_
    rintro rfl; exact sup_notMem ha hx
  · exact Or.inr (Or.inr (Or.inr (U_conn.isPreconnected.eq_univ_of_unbounded hb ha)))

-- Corrected from upstream: the conclusion had `(interior A).Nonempty` (false for a fat Cantor
-- set `A`); the intended condition is that the interval `J` is nontrivial.
lemma exists_interval_measure_inter_gt_mul_measure
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A) (A_fin : volume A < ⊤)
    {r : ENNReal} (r_lt_one : r < 1) :
    ∃ (J : Set ℝ), IsConnected J ∧ (interior J).Nonempty ∧ volume (J ∩ A) > r * volume J := by
  -- Not needed downstream: the Steinhaus-type results below use Mathlib's
  -- `MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos`.
  -- Proof: take a Lebesgue density point `x` of `A` and a small ball around it.
  have hne : volume.restrict A ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact A_pos.ne'
  have := ae_neBot.2 hne
  obtain ⟨x, hx⟩ := (Besicovitch.ae_tendsto_measure_inter_div volume A).exists
  obtain ⟨ε, hε, hεr⟩ := ((hx.eventually (lt_mem_nhds r_lt_one)).and
    self_mem_nhdsWithin).exists
  have ε_pos : (0 : ℝ) < ε := hεr
  refine ⟨Metric.closedBall x ε, ?_, ?_, ?_⟩
  · rw [Real.closedBall_eq_Icc]
    exact isConnected_Icc (by linarith)
  · rw [Real.closedBall_eq_Icc, interior_Icc]
    exact ⟨x, by linarith, by linarith⟩
  · have h0 : volume (Metric.closedBall x ε) ≠ 0 := by
      rw [Real.volume_closedBall]; simpa using ε_pos
    have hT : volume (Metric.closedBall x ε) ≠ ⊤ := measure_closedBall_lt_top.ne
    rw [inter_comm, gt_iff_lt, ← ENNReal.lt_div_iff_mul_lt (Or.inl h0) (Or.inl hT)]
    exact hε

lemma isPreconnected_of_Ioo_subset_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (J_ge : Ioo a b ⊆ J) (J_le : J ⊆ Icc a b) :
    IsPreconnected J := by
  rw [isPreconnected_iff_ordConnected]
  refine ⟨fun x hx y hy z hz ↦ ?_⟩
  rcases eq_or_lt_of_le hz.1 with h | h
  · exact h ▸ hx
  rcases eq_or_lt_of_le hz.2 with h' | h'
  · exact h' ▸ hy
  exact J_ge ⟨lt_of_le_of_lt (J_le hx).1 h, lt_of_lt_of_le h' (J_le hy).2⟩

lemma isConnected_of_Ioo_subset_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (hab : a < b) (J_ge : Ioo a b ⊆ J) (J_le : J ⊆ Icc a b) :
    IsConnected J :=
  ⟨(nonempty_Ioo.mpr hab).mono J_ge, isPreconnected_of_Ioo_subset_of_subset_Icc J_ge J_le⟩

lemma union_add_self_subset_Icc_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (J_le : J ⊆ Icc a b) (t : ℝ) :
    J ∪ ({t} + J) ⊆ Icc (min a (a + t)) (max b (b + t)) := by
  intro x hx
  cases' hx with hx hx
  · exact ⟨min_le_of_left_le (J_le hx).1, le_max_of_le_left (J_le hx).2⟩
  · refine ⟨min_le_of_right_le ?_, le_max_of_le_right ?_⟩
    · simp only [singleton_add, image_add_left, mem_preimage] at hx
      linarith [(J_le hx).1]
    · simp only [singleton_add, image_add_left, mem_preimage] at hx
      linarith [(J_le hx).2]

lemma Ioo_subset_union_add_self_of_Ioo_subset
    {J : Set ℝ} {a b : ℝ} (J_ge : Ioo a b ⊆ J) (t : ℝ) (ht : |t| < b - a) :
    Ioo (min a (a + t)) (max b (b + t)) ⊆ J ∪ ({t} + J) := by
  intro x hx
  have mem_add : x - t ∈ J → x ∈ {t} + J := fun h ↦ by
    simp only [singleton_add, image_add_left, mem_preimage]
    convert h using 1; ring
  rcases le_or_gt 0 t with t_nn | t_neg
  · rw [abs_of_nonneg t_nn] at ht
    rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hx
    by_cases hxb : x < b
    · exact Or.inl (J_ge ⟨hx.1, hxb⟩)
    · exact Or.inr (mem_add (J_ge ⟨by linarith, by linarith [hx.2]⟩))
  · rw [abs_of_neg t_neg] at ht
    rw [min_eq_right (by linarith), max_eq_left (by linarith)] at hx
    by_cases hxa : a < x
    · exact Or.inl (J_ge ⟨hxa, hx.2⟩)
    · exact Or.inr (mem_add (J_ge ⟨by linarith [hx.1], by linarith⟩))

lemma volume_union_add_self_ge_of_Ioo_subset
    {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (J_ge : Ioo a b ⊆ J) (t : ℝ) (ht : |t| < b - a) :
    ENNReal.ofReal (b - a + |t|) ≤ volume (J ∪ ({t} + J)) := by
  refine le_trans (le_of_eq ?_) (measure_mono (Ioo_subset_union_add_self_of_Ioo_subset J_ge t ht))
  rw [Real.volume_Ioo]
  congr 1
  rcases le_or_gt 0 t with t_nn | t_neg
  · rw [abs_of_nonneg t_nn, min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [abs_of_neg t_neg, min_eq_right (by linarith), max_eq_left (by linarith)]; ring

lemma volume_union_add_self_le_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (J_le : J ⊆ Icc a b) (t : ℝ) :
    volume (J ∪ ({t} + J)) ≤ ENNReal.ofReal (b - a + |t|) := by
  refine le_trans (measure_mono (union_add_self_subset_Icc_of_subset_Icc J_le t)) (le_of_eq ?_)
  rw [Real.volume_Icc]
  congr 1
  rcases le_or_gt 0 t with t_nn | t_neg
  · rw [abs_of_nonneg t_nn, min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [abs_of_neg t_neg, min_eq_right (by linarith), max_eq_left (by linarith)]; ring

lemma exists_Ioo_subset_diff_self_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ δ > 0, Ioo (-δ) δ ⊆ A - A := by
  have key := MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume A A_mble A_pos
  obtain ⟨δ, δ_pos, hδ⟩ := Metric.mem_nhds_iff.mp key
  refine ⟨δ, δ_pos, ?_⟩
  convert hδ using 1
  rw [Real.ball_eq_Ioo]
  simp

/-- Auxiliary: for sets of positive measure, some translate of the first meets the second in
a set of positive measure. -/
private lemma exists_measure_preimage_add_inter_pos {A B : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    (B_mble : MeasurableSet B) (B_pos : 0 < volume B) :
    ∃ x : ℝ, 0 < volume ((fun y ↦ x + y) ⁻¹' A ∩ B) := by
  set S : Set (ℝ × ℝ) := {p | p.1 + p.2 ∈ A ∧ p.2 ∈ B} with def_S
  have S_mble : MeasurableSet S :=
    (A_mble.preimage (measurable_fst.add measurable_snd)).inter (B_mble.preimage measurable_snd)
  have h₁ : (volume.prod volume) S = volume A * volume B := by
    rw [Measure.prod_apply_symm S_mble]
    have : ∀ y : ℝ, volume ((fun x ↦ (x, y)) ⁻¹' S) = B.indicator (fun _ ↦ volume A) y := by
      intro y
      by_cases hy : y ∈ B
      · simp only [indicator_of_mem hy]
        have : (fun x ↦ (x, y)) ⁻¹' S = (fun x ↦ x + y) ⁻¹' A := by
          ext x; simp [def_S, hy]
        rw [this, measure_preimage_add_right]
      · simp only [indicator_of_notMem hy]
        have : (fun x ↦ (x, y)) ⁻¹' S = ∅ := by
          ext x; simp [def_S, hy]
        rw [this, measure_empty]
    simp_rw [this]
    rw [lintegral_indicator B_mble, setLIntegral_const, mul_comm]
  by_contra con
  push_neg at con
  have h₂ : (volume.prod volume) S = 0 := by
    rw [Measure.prod_apply S_mble]
    have : ∀ x : ℝ, volume (Prod.mk x ⁻¹' S) = 0 := by
      intro x
      have : Prod.mk x ⁻¹' S = (fun y ↦ x + y) ⁻¹' A ∩ B := by
        ext y; simp [def_S]
      rw [this]
      exact le_antisymm (con x) bot_le
    simp [this]
  rw [h₁] at h₂
  exact (mul_ne_zero A_pos.ne' B_pos.ne') h₂

lemma exists_Ioo_subset_diff_of_measure_pos {A B : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    (B_mble : MeasurableSet B) (B_pos : 0 < volume B) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A - B := by
  obtain ⟨x, hx⟩ := exists_measure_preimage_add_inter_pos A_mble A_pos B_mble B_pos
  have C_mble : MeasurableSet ((fun y ↦ x + y) ⁻¹' A ∩ B) :=
    (A_mble.preimage (measurable_const_add x)).inter B_mble
  obtain ⟨δ, δ_pos, hδ⟩ := exists_Ioo_subset_diff_self_of_measure_pos C_mble hx
  refine ⟨x - δ, x + δ, by linarith, fun z hz ↦ ?_⟩
  obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := hδ (show z - x ∈ Ioo (-δ) δ from
    ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  refine ⟨x + c₁, hc₁.1, c₂, hc₂.2, ?_⟩
  simp only at hc ⊢
  linarith

lemma exists_Ioo_subset_add_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A + A := by
  obtain ⟨a, b, a_lt_b, hab⟩ := exists_Ioo_subset_diff_of_measure_pos
        A_mble A_pos A_mble.neg (by simpa only [Measure.measure_neg] using A_pos)
  refine ⟨a, b, a_lt_b, by simpa only [sub_neg_eq_add] using hab⟩

lemma eq_top_of_subgroup_of_measure_pos {S : AddSubgroup ℝ}
    {A : Set ℝ} (A_le_S : A ⊆ S) (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    S = ⊤ := by
  obtain ⟨δ, δ_pos, hδ⟩ := exists_Ioo_subset_diff_self_of_measure_pos A_mble A_pos
  have small : ∀ y ∈ Ioo (-δ) δ, y ∈ S := by
    intro y hy
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hδ hy
    exact S.sub_mem (A_le_S ha₁) (A_le_S ha₂)
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn⟩ := exists_nat_gt (|x| / δ)
  have n_pos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg x) δ_pos.le) hn
  have hxn : x / n ∈ Ioo (-δ) δ := by
    rw [mem_Ioo, ← abs_lt, abs_div, abs_of_pos n_pos, div_lt_iff₀ n_pos]
    rwa [div_lt_iff₀ δ_pos, mul_comm] at hn
  have := S.nsmul_mem (small _ hxn) n
  rwa [nsmul_eq_mul, mul_div_cancel₀ _ n_pos.ne'] at this

lemma exists_forall_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ δ > 0, ∃ c, ∀ x ∈ Ioo (-δ) δ, |f x| ≤ c := by
  obtain ⟨a, b, hab, hI⟩ := exists_Ioo_subset_add_of_measure_pos A_mble A_pos
  have f_le : ∀ y ∈ Ioo a b, f y ≤ 2 * M := by
    intro y hy
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hI hy
    simp only
    rw [f_add]
    linarith [f_bdd_on_A a₁ ha₁, f_bdd_on_A a₂ ha₂]
  have f_zero : f 0 = 0 := by
    have h := f_add 0 0
    rw [add_zero] at h
    linarith
  have f_neg : ∀ x, f (-x) = - f x := by
    intro x
    have := f_add x (-x)
    rw [add_neg_cancel, f_zero] at this
    linarith
  set m := (a + b) / 2 with hm
  refine ⟨(b - a) / 2, by linarith, 2 * M - f m, fun x hx ↦ ?_⟩
  have h₁ : f (m + x) ≤ 2 * M := f_le _ ⟨by linarith [hx.1, hm], by linarith [hx.2, hm]⟩
  have h₂ : f (m + -x) ≤ 2 * M := f_le _ ⟨by linarith [hx.2, hm], by linarith [hx.1, hm]⟩
  rw [f_add] at h₁ h₂
  rw [f_neg] at h₂
  rw [abs_le]
  constructor <;> linarith

open Topology in
lemma exists_nhd_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ B ∈ 𝓝 (0 : ℝ), ∃ c, ∀ x ∈ B, |f x| ≤ c := by
  obtain ⟨δ, δ_pos, hδ⟩ :=
    exists_forall_abs_le_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  exact ⟨Ioo (-δ) δ, Ioo_mem_nhds (by linarith) δ_pos, hδ⟩

lemma linear_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) (x : ℝ) :
    f x = (f 1) * x := by
  obtain ⟨δ, δ_pos, c, hc⟩ :=
    exists_forall_abs_le_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  let F : ℝ →+ ℝ := AddMonoidHom.mk' f f_add
  have F_apply : ∀ y, F y = f y := fun _ ↦ rfl
  have c_nn : 0 ≤ c := le_trans (abs_nonneg _) (hc 0 ⟨by linarith, δ_pos⟩)
  have F_contAt : ContinuousAt F 0 := by
    rw [Metric.continuousAt_iff]
    intro ε ε_pos
    obtain ⟨n, hn⟩ := exists_nat_gt (c / ε)
    have n_pos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg c_nn ε_pos.le) hn
    refine ⟨δ / n, div_pos δ_pos n_pos, fun y hy ↦ ?_⟩
    rw [Real.dist_eq, sub_zero] at hy
    rw [Real.dist_eq, map_zero, sub_zero, F_apply]
    have hny : (n : ℝ) * y ∈ Ioo (-δ) δ := by
      rw [mem_Ioo, ← abs_lt, abs_mul, abs_of_pos n_pos]
      rwa [lt_div_iff₀ n_pos, mul_comm] at hy
    have key := hc _ hny
    have : f ((n : ℝ) * y) = n * f y := by
      rw [← F_apply, ← F_apply y, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    rw [this, abs_mul, abs_of_pos n_pos] at key
    rw [div_lt_iff₀ ε_pos] at hn
    by_contra con
    push_neg at con
    nlinarith
  have F_cont : Continuous F := continuous_of_continuousAt_zero F F_contAt
  have := map_real_smul F F_cont x 1
  simp only [smul_eq_mul, mul_one, F_apply] at this
  rw [this, mul_comm]

open ENNReal in
lemma linear_of_additive_of_measurable
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂) (f_mble : Measurable f) (x : ℝ) :
    f x = (f 1) * x := by
  set As : ℕ → Set ℝ := fun n ↦ {y | f y ≤ n} with def_As
  have cover : ⋃ n, As n = ⊤ := by
    ext x
    simp [exists_nat_ge (f x), def_As]
  have As_mble (n : ℕ) : MeasurableSet (As n) := f_mble measurableSet_Iic
  obtain ⟨n, hn⟩ : ∃ n, 0 < volume (As n) := by
    apply exists_measure_pos_of_not_measure_iUnion_null
    simp [cover]
  exact linear_of_additive_of_le_on_measure_pos f_add (As_mble n) hn (M := n) (by simp [def_As]) x

/-- A measurable additive map ℝ → ℝ is linear.
(The only measurable solutions to the Cauchy-Hamel functional equation are the obvious ones.) -/
lemma eq_const_mul_of_additive_of_measurable {f : ℝ → ℝ}
    (f_add : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ + f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ α * s := by
  use f 1
  ext x
  exact linear_of_additive_of_measurable f_add f_mble x

/-- A measurable multiplicative map ℝ → (0,+∞) is of the form s ↦ exp(α * s) for some α ∈ ℝ.
(The only measurable solutions to the multiplicative version of the Cauchy-Hamel functional
equation are the obvious ones.) -/
lemma eq_exp_const_mul_of_multiplicative_of_measurable {f : ℝ → ℝ} (f_pos : ∀ s, 0 < f s)
    (f_multiplicative : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ * f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ exp (α * s) := by
  let g := fun s ↦ log (f s)
  have f_eq_exp_g (s) : f s = exp (g s) := by
    simpa [g] using (exp_log (f_pos s)).symm
  have g_mble : Measurable g := measurable_log.comp f_mble
  have g_additive (s₁ s₂) : g (s₁ + s₂) = g s₁ + g s₂ := by
    simpa only [g, f_multiplicative] using log_mul (f_pos _).ne.symm (f_pos _).ne.symm
  obtain ⟨α, key⟩ := eq_const_mul_of_additive_of_measurable g_additive g_mble
  refine ⟨α, by ext s ; rw [f_eq_exp_g, key]⟩

lemma eq_const_mul_one_sub_exp_of_multiplicative_with_scaling_of_measurable
    {α : ℝ} (α_ne_zero : α ≠ 0) {b : ℝ → ℝ}
    (b_eqn : ∀ s t : ℝ, b (s + t) = rexp (α * s) * b t + b s) :
    ∃ c : ℝ, ∀ t : ℝ, b t = c * (1 - rexp (α * t)) := by
  have b_zero : b 0 = 0 := by simpa using b_eqn 0 0
  let c := - (b 1 / (rexp (α * 1) - 1))
  have refactored (s t : ℝ) :
      (rexp (α * s) - 1) * b t = (rexp (α * t) - 1) * b s := calc
        (rexp (α * s) - 1) * b t
    _ = rexp (α * s) * b t + b s - b t - b s := by ring
    _ = b (s + t) - b t - b s                := by rw [b_eqn]
    _ = b (t + s) - b t - b s                := by rw [add_comm s t]
    _ = rexp (α * t) * b s + b t - b t - b s := by rw [b_eqn]
    _ = (rexp (α * t) - 1) * b s             := by ring
  use c
  intro t
  by_cases t_zero : t = 0
  · simp [t_zero, b_zero]
  · have aux : (rexp (α * 1) - 1) ≠ 0 := by simp [sub_eq_zero, α_ne_zero]
    calc  b t
      _ = b t * ((rexp (α * 1) - 1) / (rexp (α * 1) - 1))     := by rw [div_self aux] ; ring
      _ = (rexp (α * 1) - 1) * b t / (rexp (α * 1) - 1)       := by ring
      _ = (rexp (α * t) - 1) * b 1 / (rexp (α * 1) - 1)       :=
        congrArg (· / (rexp (α * 1) - 1)) (refactored 1 t)
      _ = c * (1 - rexp (α * t))                              := by ring

end cauchy_hamel_functional_equation


section one_parameter_subgroups_of_affine_transformations

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where `Aₛ x = x + β * s`.
(`β` is a real parameter: each `β` gives a different (but related) homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex₀ (β : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs zero_lt_one (β * s.toAdd)
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp
    ring

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where
`Aₛ x = exp(α * s) * (x - c) + c`.
(`α c` are real parameters: each `α c` give a different homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex (α c : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs (show 0 < Real.exp (α * s.toAdd) from Real.exp_pos _)
              (c * (1 - Real.exp (α * s.toAdd)))
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp [mul_add, Real.exp_add]
    ring

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_fst {β s : ℝ} :
    (homOfIndex₀ β s).coefs.1 = 1 := by
  simp [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs]

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_snd {β s : ℝ} :
    (homOfIndex₀ β s).coefs.2 = β * s := by
  simp only [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

-- Ported to Mathlib v4.35: `Multiplicative ℝ` variants (see `homOfIndex_coefs_fst'`).
@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_fst' {β : ℝ} {s : Multiplicative ℝ} :
    (homOfIndex₀ β s).coefs.1 = 1 :=
  homOfIndex₀_coefs_fst (s := s.toAdd)

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_snd' {β : ℝ} {s : Multiplicative ℝ} :
    (homOfIndex₀ β s).coefs.2 = β * s.toAdd :=
  homOfIndex₀_coefs_snd (s := s.toAdd)

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_fst {α c s : ℝ} :
    (homOfIndex α c s).coefs.1 = Real.exp (α * s) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs, Real.exp_eq_exp]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_snd {α c s : ℝ} :
    (homOfIndex α c s).coefs.2 = c * (1 - Real.exp (α * s)) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

-- Ported to Mathlib v4.35: variants stated on `Multiplicative ℝ`, since the defeq between `ℝ`
-- and `Multiplicative ℝ` is no longer used by `simp`.
@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_fst' {α c : ℝ} {s : Multiplicative ℝ} :
    (homOfIndex α c s).coefs.1 = Real.exp (α * s.toAdd) :=
  homOfIndex_coefs_fst (s := s.toAdd)

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_snd' {α c : ℝ} {s : Multiplicative ℝ} :
    (homOfIndex α c s).coefs.2 = c * (1 - Real.exp (α * s.toAdd)) :=
  homOfIndex_coefs_snd (s := s.toAdd)

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero' (β : ℝ) :
    homOfIndex₀ β (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero (β : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex₀_zero_apply' (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_zero_apply (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_add (β : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex₀ β (s₁ + s₂) = homOfIndex₀ β s₁ * homOfIndex₀ β s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_inv (β : ℝ) (s : ℝ) :
    (homOfIndex₀ β s)⁻¹ = homOfIndex₀ β (-s) := by
  have obs := homOfIndex₀_add β s (-s)
  simp only [add_neg_cancel, homOfIndex₀_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex₀_add_apply {β : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex₀ β (s₁ + s₂) x = homOfIndex₀ β s₁ (homOfIndex₀ β s₂ x) := by
  simp only [homOfIndex₀_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex₀_eq_homOfIndex₀_one_mul {β s : ℝ} :
    homOfIndex₀ β s = homOfIndex₀ 1 (β * s) := by
  ext x
  simp [mul_comm]

lemma AffineIncrEquiv.conjugate_homOfIndex₀ (A : AffineIncrEquiv) (β : ℝ) (s : ℝ) :
    A * homOfIndex₀ β s * A⁻¹ = homOfIndex₀ (β * A.coefs.1) s := by
  have ha : A.coefs.1 ≠ 0 := A.coefs_fst_pos.ne'
  ext x
  rw [mul_apply_eq_comp_apply, mul_apply_eq_comp_apply]
  simp only [apply_eq, homOfIndex₀_coefs_fst, homOfIndex₀_coefs_snd,
    inv_coefs_fst, inv_coefs_snd]
  field_simp
  ring

@[simp] lemma AffineIncrEquiv.homOfIndex_zero' (α c : ℝ) :
    homOfIndex α c (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex_zero (α c : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex_zero_apply' (α c : ℝ) (x : ℝ) :
    homOfIndex α c (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_zero_apply (α c : ℝ) (x : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_add (α c : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex α c (s₁ + s₂) = homOfIndex α c s₁ * homOfIndex α c s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex_inv (α c : ℝ) (s : ℝ) :
    (homOfIndex α c s)⁻¹ = homOfIndex α c (-s) := by
  have obs := homOfIndex_add α c s (-s)
  simp only [add_neg_cancel, homOfIndex_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex_add_apply {α c : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex α c (s₁ + s₂) x = homOfIndex α c s₁ (homOfIndex α c s₂ x) := by
  simp only [homOfIndex_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex_eq_homOfIndex_one_mul {α c s : ℝ} :
    homOfIndex α c s = homOfIndex 1 c (α * s) := by
  ext x
  simp

lemma AffineIncrEquiv.conjugate_homOfIndex (A : AffineIncrEquiv) (α c : ℝ) (s : ℝ) :
    A * homOfIndex α c s * A⁻¹ = homOfIndex α (A c) s := by
  have ha : A.coefs.1 ≠ 0 := A.coefs_fst_pos.ne'
  ext x
  rw [mul_apply_eq_comp_apply, mul_apply_eq_comp_apply]
  simp only [apply_eq, homOfIndex_coefs_fst, homOfIndex_coefs_snd,
    inv_coefs_fst, inv_coefs_snd]
  field_simp
  ring

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + β * s`, where `s ∈ ℝ`.
(`β` is a real parameter: each `β ≠ 0` in fact gives the same subgroup) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀' (β : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ β) ⊤

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + s`, where `s ∈ ℝ`. -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀ :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ 1) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_of_ne_zero {β : ℝ} (hβ : β ≠ 0) :
    AffineIncrEquiv.subGroupOfIndex₀' β = AffineIncrEquiv.subGroupOfIndex₀ := by
  ext A
  simp only [subGroupOfIndex₀', subGroupOfIndex₀, Subgroup.mem_map, Subgroup.mem_top, true_and]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨Multiplicative.ofAdd (β * s.toAdd), ?_⟩
    ext x
    simp
  · rintro ⟨s, rfl⟩
    refine ⟨Multiplicative.ofAdd (s.toAdd / β), ?_⟩
    ext x
    simp only [apply_eq, homOfIndex₀_coefs_fst', homOfIndex₀_coefs_snd', toAdd_ofAdd]
    field_simp

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_bot :
    AffineIncrEquiv.subGroupOfIndex₀' 0 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro A ⟨s, -, rfl⟩
  ext x
  simp

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex₀_of_no_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) (hA : ∀ x, A x ≠ x) :
    A ∈ subGroupOfIndex₀ := by
  have a_eq_one : A.coefs.1 = 1 := by
    by_contra h
    have h' : 1 - A.coefs.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    apply hA (A.coefs.2 / (1 - A.coefs.1))
    rw [apply_eq]
    field_simp
    ring
  refine ⟨Multiplicative.ofAdd A.coefs.2, trivial, ?_⟩
  ext x
  simp [a_eq_one]

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = exp(α * s) * (x - c) + c` where `s ∈ ℝ`.
(`α c` are real parameters) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex (α c : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex α c) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex_eq_bot (c : ℝ) :
    subGroupOfIndex 0 c = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro A ⟨s, -, rfl⟩
  ext x
  simp

@[simp] lemma AffineIncrEquiv.fixed_point_of_mem_subGroupOfIndex (A : AffineIncrEquiv)
    {α c : ℝ} (hA : A ∈ subGroupOfIndex α c):
    A c = c := by
  obtain ⟨s, _, hs⟩ := hA
  simp only [← hs, apply_eq, homOfIndex_coefs_fst', homOfIndex_coefs_snd']
  ring

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex_iff_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    A ∈ subGroupOfIndex α c ↔ A c = c := by
  refine ⟨fun h ↦ fixed_point_of_mem_subGroupOfIndex A h, fun h ↦ ?_⟩
  rw [apply_eq] at h
  refine ⟨Multiplicative.ofAdd (Real.log A.coefs.1 / α), trivial, ?_⟩
  have hexp : Real.exp (α * (Real.log A.coefs.1 / α)) = A.coefs.1 := by
    rw [mul_div_cancel₀ _ hα, Real.exp_log A.coefs_fst_pos]
  ext x
  simp only [apply_eq, homOfIndex_coefs_fst', homOfIndex_coefs_snd', toAdd_ofAdd, hexp]
  linarith

/-- Functional equation for scaling coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_fst
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.1 = (f s₁).coefs.1 * (f s₂).coefs.1 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ from f.map_mul s₁ s₂]

/-- Functional equation for translation coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_snd
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.2 = (f s₁).coefs.1 * (f s₂).coefs.2 + (f s₁).coefs.2 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ from f.map_mul s₁ s₂]

open Real

lemma eq_of_functional_eqn_of_ne_zero {f : ℝ → ℝ} {α : ℝ} (α_ne_zero : α ≠ 0)
    (f_eqn : ∀ s₁ s₂, f (s₁ + s₂) = exp (α * s₁) * f s₂ + f s₁) :
    ∃ c, f = fun s ↦ c * (1 - exp (α * s)) := by
  obtain ⟨c, hc⟩ :=
    eq_const_mul_one_sub_exp_of_multiplicative_with_scaling_of_measurable α_ne_zero f_eqn
  exact ⟨c, funext hc⟩

/-- We endow the space of orientation-preserving affine isomorphisms of `ℝ` with the Borel
σ-algebra of the topology of pointwise convergence. -/
instance : MeasurableSpace AffineIncrEquiv := borel AffineIncrEquiv

instance : BorelSpace AffineIncrEquiv := ⟨rfl⟩

lemma AffineIncrEquiv.measurable_coefs_fst :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.1) :=
  continuous_coefs_fst.measurable

lemma AffineIncrEquiv.measurable_coefs_snd :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.2) :=
  continuous_coefs_snd.measurable

lemma AffineIncrEquiv.continuous_mkOfCoefs :
    Continuous fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  apply (continuous_induced_rng ..).mpr
  exact continuous_pi (by continuity)

lemma AffineIncrEquiv.measurable_mkOfCoefs :
    Measurable fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  have _bs1 : BorelSpace {a : ℝ // 0 < a} := Subtype.borelSpace _
  have _bs2 : BorelSpace ({a : ℝ // 0 < a} × ℝ) := Prod.borelSpace
  exact continuous_mkOfCoefs.measurable

lemma AffineIncrEquiv.continuous_of_continuous_coefs {Z : Type*} [TopologicalSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Continuous fun z ↦ (f z).coefs.1)
    (f_snd_cont : Continuous fun z ↦ (f z).coefs.2) :
    Continuous f := by
  convert AffineIncrEquiv.continuous_mkOfCoefs.comp <|
    show Continuous fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      continuity
  ext z x
  simp

lemma AffineIncrEquiv.measurable_of_measurable_coefs {Z : Type*} [MeasurableSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Measurable fun z ↦ (f z).coefs.1)
    (f_snd_cont : Measurable fun z ↦ (f z).coefs.2) :
    Measurable f := by
  convert AffineIncrEquiv.measurable_mkOfCoefs.comp <|
    show Measurable fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      measurability
  ext z x
  simp

instance : MeasurableSpace (Multiplicative ℝ) := borel (Multiplicative ℝ)

instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

lemma measurable_toAdd :
    Measurable (fun (s : Multiplicative ℝ) ↦ s.toAdd) :=
  continuous_toAdd.measurable

lemma measurable_toMultiplicative :
    Measurable (fun (s : ℝ) ↦ Multiplicative.ofAdd s) :=
  continuous_ofAdd.measurable

/-- Characterization of homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (f_mble : Measurable f) :
    (∃ β, f = homOfIndex₀ β) ∨ (∃ α c, f = homOfIndex α c) := by
  let a (s : ℝ) : ℝ := (f s).coefs.1
  let b (s : ℝ) : ℝ := (f s).coefs.2
  have a_pos (s : ℝ) : 0 < a s := (f s).coefs_fst_pos
  have a_hom (s t : ℝ) : a (s + t) = a s * a t :=
    AffineIncrEquiv.homomorphism_coef_eqn_fst f s t
  have b_hom (s t : ℝ) : b (s + t) = a s * b t + b s :=
    AffineIncrEquiv.homomorphism_coef_eqn_snd f s t
  have a_mble : Measurable a := AffineIncrEquiv.measurable_coefs_fst.comp f_mble
  have b_mble : Measurable b := AffineIncrEquiv.measurable_coefs_snd.comp f_mble
  obtain ⟨α, a_eq_exp_α_s⟩ : ∃ α, a = fun s ↦ rexp (α * s) :=
    eq_exp_const_mul_of_multiplicative_of_measurable a_pos a_hom a_mble
  by_cases α_zero : α = 0
  · left
    have a_eq_one : a = 1 := by
      ext t
      simp [a_eq_exp_α_s, α_zero]
    have b_hom' (s t : ℝ) : b (s + t) = b s + b t := by
      simpa [a_eq_exp_α_s, α_zero, add_comm t s] using b_hom t s
    obtain ⟨β, b_eq_β_mul_s⟩ : ∃ α, b = fun s => α * s :=
      eq_const_mul_of_additive_of_measurable b_hom' b_mble
    use β
    suffices h : ∀ (s x : ℝ), (f s).coefs.1 * x + (f s).coefs.2 = x + β * s by
      refine MonoidHom.ext fun s ↦ AffineIncrEquiv.ext fun x ↦ ?_
      simp only [apply_eq, homOfIndex₀_coefs_fst', homOfIndex₀_coefs_snd', one_mul]
      exact h s.toAdd x
    exact fun s x ↦ show a s * x + b s = x + β * s by simp [a_eq_one, b_eq_β_mul_s]
  · right
    rw [a_eq_exp_α_s] at b_hom
    obtain ⟨c, b_eq_c_mul_exp⟩ :=
      eq_const_mul_one_sub_exp_of_multiplicative_with_scaling_of_measurable α_zero b_hom
    use α, c
    suffices ∀ (s : ℝ), f s = homOfIndex α c s by ext s : 2 ; exact this s
    refine fun s ↦ AffineIncrEquiv.ext_of_coefs (Prod.eq_iff_fst_eq_snd_eq.mpr ?_)
    exact ⟨by simpa using congr_fun a_eq_exp_α_s s, by simpa using b_eq_c_mul_exp s⟩

/-- Characterization of nontrivial homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization_of_nontrivial
    {f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv} (f_nontriv : ¬ f = 1)
    (f_mble : Measurable f) :
    (∃ β, β ≠ 0 ∧ f = homOfIndex₀ β) ∨ (∃ α c, α ≠ 0 ∧ f = homOfIndex α c) := by
  cases' homomorphism_from_Real_characterization f f_mble with h₀ h₁
  · obtain ⟨β, hβ⟩ := h₀
    refine Or.inl ⟨β, ?_, hβ⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [hβ, maybe_zero]
  · obtain ⟨α, c, h⟩ := h₁
    refine Or.inr ⟨α, c, ?_, h⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [h, maybe_zero]

end one_parameter_subgroups_of_affine_transformations
