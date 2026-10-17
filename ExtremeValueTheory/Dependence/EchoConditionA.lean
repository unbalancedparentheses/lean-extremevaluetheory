/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.EchoProcess
import ExtremeValueTheory.Dependence.Mixing

/-!
# The block condition `𝒜(uₙ)` for the echo process

TODO docstring
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section EchoConditionA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

/-- The *truncated quiet event*: no source of an exceedance of `u` at a time `t ∈ A` with
echo index `j ≤ l`. It only depends on the innovations `Z_s`, `s ∈ echoWindow A l`. -/
def echoQuiet (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (A : Finset ℕ) (u : ℝ) (l : ℕ) : Set Ω :=
  {ω | ∀ t ∈ A, ∀ j ≤ l, ω ∉ echoSource L Z t u j}

/-- The innovation times `t - j`, `t ∈ A`, `j ≤ l`, on which `echoQuiet L Z A u l` depends. -/
def echoWindow (A : Finset ℕ) (l : ℕ) : Set ℤ := {s | ∃ t ∈ A, ∃ j ≤ l, s = (t : ℤ) - j}

/-- The *long echo event*: some exceedance of `u` at a time `t < n` is the echo of an innovation
with echo lag `j > l`. -/
def echoLong (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (n : ℕ) (u : ℝ) (l : ℕ) : Set Ω :=
  {ω | ∃ t < n, ∃ j, l < j ∧ ω ∈ echoSource L Z t u j}

theorem echoQuiet_union (A B : Finset ℕ) (u : ℝ) (l : ℕ) :
    echoQuiet L Z (A ∪ B) u l = echoQuiet L Z A u l ∩ echoQuiet L Z B u l := by
  ext ω
  simp only [echoQuiet, Finset.mem_union, mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨h1, h2⟩ t (ht | ht)
    exacts [h1 t ht, h2 t ht]

theorem measurableSet_echoQuiet (hLm : Measurable L) (A : Finset ℕ) (u : ℝ) (l : ℕ) :
    MeasurableSet[⨆ s ∈ echoWindow A l, MeasurableSpace.comap (Z s) inferInstance]
      (echoQuiet L Z A u l) := by
  set m := ⨆ s ∈ echoWindow A l, MeasurableSpace.comap (Z s) inferInstance
  have e : echoQuiet L Z A u l =
      ⋂ t ∈ A, ⋂ j ∈ Finset.range (l + 1), (echoSource L Z t u j)ᶜ := by
    ext ω
    simp only [echoQuiet, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_compl_iff]
    exact forall₂_congr fun t _ => forall_congr' fun j => by
      constructor
      · exact fun h hj => h (by omega)
      · exact fun h hj => h (by omega)
  rw [e]
  refine @Finset.measurableSet_biInter _ _ m _ A fun t ht => ?_
  refine @Finset.measurableSet_biInter _ _ m _ _ fun j hj => ?_
  refine @MeasurableSet.compl _ _ m ?_
  have hle : MeasurableSpace.comap (Z ((t : ℤ) - j)) inferInstance ≤ m :=
    le_iSup₂ (f := fun s (_ : s ∈ echoWindow A l) =>
      MeasurableSpace.comap (Z s) inferInstance) ((t : ℤ) - j)
      ⟨t, ht, j, by simpa [Nat.lt_succ_iff] using hj, rfl⟩
  exact hle _ ⟨_, measurableSet_echoSourceSet hLm u j, (echoSource_eq _ _ _).symm⟩

theorem disjoint_echoWindow {A B : Finset ℕ} {l : ℕ} (hAB : ∀ a ∈ A, ∀ b ∈ B, a + (l + 1) ≤ b) :
    Disjoint (echoWindow A l) (echoWindow B l) := by
  rw [Set.disjoint_left]
  rintro s ⟨a, ha, i, hi, rfl⟩ ⟨b, hb, j, hj, he⟩
  have := hAB a ha b hb
  omega

omit [IsProbabilityMeasure P] in
/-- **Truncated quiet events of separated blocks are independent.** -/
theorem measureReal_echoQuiet_union (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hLm : Measurable L) {A B : Finset ℕ} {l : ℕ} (hAB : ∀ a ∈ A, ∀ b ∈ B, a + (l + 1) ≤ b)
    (u : ℝ) :
    P.real (echoQuiet L Z (A ∪ B) u l) =
      P.real (echoQuiet L Z A u l) * P.real (echoQuiet L Z B u l) := by
  have hI := indep_iSup_of_disjoint (m := fun s => MeasurableSpace.comap (Z s) inferInstance)
    (fun s => (hZ s).comap_le) hind.iIndep (disjoint_echoWindow hAB)
  have h := (Indep_iff _ _ _).1 hI _ _ (measurableSet_echoQuiet hLm A u l)
    (measurableSet_echoQuiet hLm B u l)
  rw [echoQuiet_union, measureReal_def, h, ENNReal.toReal_mul]
  rfl

omit [IsProbabilityMeasure P] in
/-- An exceedance-free block has no source with index `≤ l`, on the almost sure event that only
finitely many innovations echo into each time. -/
theorem maxLE_echoProcess_subset_echoQuiet {A : Finset ℕ} {u : ℝ} {l : ℕ} {ω : Ω}
    (hb : ∀ t, BddAbove (range fun j => echoTerm L Z t j ω))
    (hω : ω ∈ maxLE (fun k : ℕ => |echoProcess L Z k|) A u) : ω ∈ echoQuiet L Z A u l := by
  intro t ht j _ hmem
  have h1 := lt_echoProcess_of_mem_echoSource (hb t) hmem
  have h2 : |echoProcess L Z t ω| ≤ u := hω t ht
  have := le_abs_self (echoProcess L Z t ω)
  linarith

omit [IsProbabilityMeasure P] in
/-- A quiet block either has no exceedance or contains the echo of an innovation with lag `> l`. -/
theorem echoQuiet_subset (hpos : ∀ t ω, 0 ≤ Z t ω) {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range n) {u : ℝ} (hu : 0 ≤ u) (l : ℕ) :
    echoQuiet L Z A u l ⊆
      maxLE (fun k : ℕ => |echoProcess L Z k|) A u ∪ echoLong L Z n u l := by
  intro ω hω
  by_contra hcon
  simp only [mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [maxLE, mem_ofPred_eq, not_forall, not_le] at h1
  obtain ⟨t, ht, hlt⟩ := h1
  change u < |echoProcess L Z t ω| at hlt
  rw [abs_of_nonneg (echoProcess_nonneg hpos _ _)] at hlt
  obtain ⟨j, hj⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (L := L) (Z := Z) hu t hlt)
  by_cases hjl : j ≤ l
  · exact hω t ht j hjl hj
  · exact h2 ⟨t, Finset.mem_range.1 (hA ht), j, by omega, hj⟩

/-- `P(echoLong) ≤ n P(L(Z) > l)`. -/
theorem measureReal_echoLong_le (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hLm : Measurable L) (n : ℕ) (u : ℝ)
    (l : ℕ) :
    P.real (echoLong L Z n u l) ≤ n * (paretoMeasure 1 α).real {z | l + 1 ≤ L z} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set ν := paretoMeasure 1 α
  set D : ℕ → Set ℝ := fun i => L ⁻¹' {i + l + 1}
  have hD : ∀ i, MeasurableSet (D i) := fun i => hLm (measurableSet_singleton _)
  have hsum : HasSum (fun i => ν.real (D i)) (ν.real {z | l + 1 ≤ L z}) := by
    have hU : (⋃ i, D i) = {z | l + 1 ≤ L z} := by
      ext z
      simp only [D, mem_iUnion, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨i, hi⟩; omega
      · intro h; exact ⟨L z - (l + 1), by omega⟩
    rw [← hU]
    exact hasSum_measureReal_iUnion hD fun i j hij =>
      Disjoint.preimage _ (Set.disjoint_singleton.2 (by omega))
  set E : ℕ → ℕ → Set Ω := fun t i => Z ((t : ℤ) - ((i + l + 1 : ℕ) : ℤ)) ⁻¹' D i
  have hsub : echoLong L Z n u l ⊆ ⋃ t ∈ Finset.range n, ⋃ i, E t i := by
    rintro ω ⟨t, ht, j, hj, -, hL⟩
    refine mem_iUnion₂.2 ⟨t, Finset.mem_range.2 ht, mem_iUnion.2 ⟨j - (l + 1), ?_⟩⟩
    have hj' : j - (l + 1) + l + 1 = j := by omega
    simp only [E, D, mem_preimage, mem_singleton_iff, hj']
    exact hL.resolve_left (by omega)
  have ht : ∀ t : ℕ, P.real (⋃ i, E t i) ≤ ν.real {z | l + 1 ≤ L z} := by
    intro t
    have he : ∀ i, P.real (E t i) = ν.real (D i) :=
      fun i => measureReal_preimage_eq hZ hlaw _ (hD i)
    have hs : Summable fun i => P.real (E t i) := by
      simp_rw [he]; exact hsum.summable
    refine (measureReal_iUnion_le_tsum hs).trans (le_of_eq ?_)
    simp_rw [he]
    exact hsum.tsum_eq
  calc P.real (echoLong L Z n u l) ≤ P.real (⋃ t ∈ Finset.range n, ⋃ i, E t i) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ t ∈ Finset.range n, P.real (⋃ i, E t i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Finset.range n, ν.real {z | l + 1 ≤ L z} := Finset.sum_le_sum fun t _ => ht t
    _ = n * ν.real {z | l + 1 ≤ L z} := by simp

/-- **The factorization bound for the echo process.** For blocks `A, B ⊆ {0, …, n - 1}` at
distance `> l` and `u ≥ 0`,
`|P(max_{A ∪ B} X ≤ u) - P(max_A X ≤ u) P(max_B X ≤ u)| ≤ 2 n P(L(Z) > l)`: up to the event that
an echo of lag `> l` lands in `{0, …, n - 1}`, the two block events are functions of disjoint
sets of innovations. -/
theorem abs_measureReal_maxLE_echoProcess_le (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L) {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.range n) (hB : B ⊆ Finset.range n) {l : ℕ}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a + (l + 1) ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    |P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) (A ∪ B) u) -
        P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) A u) *
          P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) B u)| ≤
      2 * (n * (paretoMeasure 1 α).real {z | l + 1 ≤ L z}) := by
  set Y : ℕ → Ω → ℝ := fun k => |echoProcess L Z k|
  set g := P.real (echoLong L Z n u l)
  have hg := measureReal_echoLong_le hα hZ hlaw hLm (P := P) n u l
  have hb := ae_bddAbove_echoTerm hα hZ hlaw hLm (P := P)
  have hbounds : ∀ C : Finset ℕ, C ⊆ Finset.range n →
      P.real (echoQuiet L Z C u l) - g ≤ P.real (maxLE Y C u) ∧
        P.real (maxLE Y C u) ≤ P.real (echoQuiet L Z C u l) := by
    intro C hC
    constructor
    · have := (measureReal_mono (μ := P) (echoQuiet_subset hpos hC hu l)).trans
        (measureReal_union_le _ _)
      linarith
    · refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [hb] with ω hω h
      exact maxLE_echoProcess_subset_echoQuiet hω h
  obtain ⟨h1, h2⟩ := hbounds (A ∪ B) (Finset.union_subset hA hB)
  obtain ⟨h3, h4⟩ := hbounds A hA
  obtain ⟨h5, h6⟩ := hbounds B hB
  rw [measureReal_echoQuiet_union hZ hind hLm hAB] at h1 h2
  set p := P.real (echoQuiet L Z A u l)
  set q := P.real (echoQuiet L Z B u l)
  set a := P.real (maxLE Y A u)
  set b := P.real (maxLE Y B u)
  have hg0 : 0 ≤ g := measureReal_nonneg
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hb1 : b ≤ 1 := measureReal_le_one
  have hp1 : p ≤ 1 := measureReal_le_one
  have hab1 : a * b ≤ p * q := mul_le_mul h4 h6 hb0 (ha0.trans h4)
  have hab2 : p * q - 2 * g ≤ a * b := by
    nlinarith [mul_nonneg (show 0 ≤ a - (p - g) by linarith) hb0,
      mul_nonneg (ha0.trans h4) (show 0 ≤ b - (q - g) by linarith),
      mul_le_mul_of_nonneg_left hb1 hg0, mul_le_mul_of_nonneg_left hp1 hg0]
  rw [abs_le]
  constructor <;> linarith

end EchoConditionA

end ExtremeValueTheory
