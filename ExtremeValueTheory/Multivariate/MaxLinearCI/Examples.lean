/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.MaxLinearCI.Measure

/-!
# Strictness Witnesses and Complete Resolution of Engelke et al. (2024)

This file constructs the four minimal finite-DAG witnesses that completely resolve the open
question of Engelke, Hentschel, Lalancette, and Röttger (`arXiv:2402.02187`, *Graphical Models
for Multivariate Extremes*):

> *"On the other hand, it is still unknown whether $d$-separation fully characterizes extremal
> conditional independence or if it is strictly stronger. It is also an open question whether in
> these models, extremal conditional independence is stronger than, weaker than, equivalent to
> (or none of the above) $*$-separation."*

Together with `MaxLinearCI/Graph.lean` and `MaxLinearCI/Measure.lean`, this establishes the exact
strict hierarchy across all finite DAGs and all positive recursive max-linear models:

  `d-separation ⊊ *-separation ⊊ universal Λ-CI ⊊ fixed-weight Λ-CI`.

## Witnesses

1. **5-node W-graph (`wDAG`)**: `0 → 1 ← 2 → 3 ← 4`, `A = {0}`, `B = {4}`, `C = {1, 3}`.
   $d$-separation fails, $*$-separation holds (hence extremal CI holds for all positive weights).
2. **4-node Star DAG (`starDAG`)**: `0 → 1`, `0 → 2`, `0 → 3`, `A = {0}`, `B = {1}`, `C = {2, 3}`.
   Nodes `0` and `1` are **directly adjacent** (`0 → 1`), so BOTH $d$-separation and $*$-separation
   fail — YET extremal conditional independence (`ExtremalCondIndep`) AND multivariate Pareto
   conditional independence (`ParetoCondIndep`) hold for **every** positive weight matrix `M`!
3. **4-node Non-Adjacent Collider (`colliderDAG`)**: `0 → 2 ← 1`, `0 → 3`, `A = {0}`, `B = {1}`,
   `C = {2, 3}`. Non-adjacent nodes where both $d$-separation and $*$-separation fail, yet extremal
   CI holds for every positive weight matrix `M`.
4. **4-node Diamond DAG (`diamondDAG`)**: `0 → 1 → 3`, `0 → 2 → 3`, `A = {1}`, `B = {2}`, `C = {3}`.
   For unit weights (`diamondUnitModel`), extremal CI holds via a non-degenerate `2 × 2` rank-1
   product measure; for perturbed innovation scale `diag 0 = 2` (`diamondPerturbedModel`),
   extremal CI fails (`2 * 5 ≠ 3 * 3`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace ExtremeValueTheory

namespace MaxLinearCI

/-! ### Helper: topological acyclicity on `Fin n` -/

/-- Any edge relation on `Fin n` that strictly increases the vertex index (`u < v`) is acyclic. -/
def dagOfLt {n : ℕ} (edge : Fin n → Fin n → Prop) (h : ∀ u v, edge u v → u < v) : DAG (Fin n) where
  edge := edge
  acyclic u htr := by
    have hlt : ∀ {a b : Fin n}, Relation.TransGen edge a b → a < b := by
      intro a b htr'
      induction htr' with
      | single hab => exact h _ _ hab
      | tail _ hbc ih => exact lt_trans ih (h _ _ hbc)
    exact lt_irrefl u (hlt htr)

lemma reach_imp_le_of_lt {n : ℕ} {edge : Fin n → Fin n → Prop} (h : ∀ u v, edge u v → u < v)
    {u v : Fin n} (hr : (dagOfLt edge h).Reach u v) : u ≤ v := by
  induction hr with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (h _ _ hbc).le

/-! ### Witness A: 5-node W-graph (`0 → 1 ← 2 → 3 ← 4`) -/

/-- Edge relation of the 5-node W-graph `0 → 1 ← 2 → 3 ← 4`. -/
def wEdge (u v : Fin 5) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 1) ∨ (u = 2 ∧ v = 3) ∨ (u = 4 ∧ v = 3)

/-- The 5-node W-graph DAG `0 → 1 ← 2 → 3 ← 4`. -/
def wDAG : DAG (Fin 5) where
  edge := wEdge
  acyclic u htr := by
    have hparity : ∀ {a b : Fin 5}, Relation.TransGen wEdge a b →
        (a = 0 ∨ a = 2 ∨ a = 4) ∧ (b = 1 ∨ b = 3) := by
      intro a b htr'
      induction htr' with
      | single hab =>
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      | tail _ hbc ih =>
        rcases ih with ⟨_, hmid⟩
        rcases hbc with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp at hmid
    have ⟨h1, h2⟩ := hparity htr
    rcases h1 with rfl | rfl | rfl <;> simp at h2

/-- On the 5-node W-graph, `0` and `4` are NOT $d$-separated given `{1, 3}` (via `[0, 1, 2, 3, 4]`). -/
theorem wDAG_not_dSeparated :
    ¬ wDAG.IsDSeparated ({(0 : Fin 5)} : Set (Fin 5)) {4} {1, 3} := by
  intro hd
  refine hd [0, 1, 2, 3, 4] 0 (mem_singleton 0) 4 (mem_singleton 4) rfl rfl ?_
  refine ⟨by decide, fun i hi ↦ ?_, fun i hi ↦ ⟨fun hc ↦ ?_, fun hnc ↦ ?_⟩⟩
  · have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
    rcases hi4 with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
    rcases hi3 with rfl | rfl | rfl
    · exact ⟨1, Or.inl rfl, wDAG.reach_refl 1⟩
    · exfalso; rcases hc with ⟨h1, _⟩; simp [wDAG, wEdge] at h1
    · exact ⟨3, Or.inr rfl, wDAG.reach_refl 3⟩
  · have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
    rcases hi3 with rfl | rfl | rfl
    · exfalso; exact hnc ⟨Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · simp
    · exfalso; exact hnc ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- On the 5-node W-graph, `0` and `4` ARE $*$-separated given `{1, 3}` (every simple path from `0`
to `4` must be `[0, 1, 2, 3, 4]`, which has TWO colliders at `1` and `3`). -/
theorem wDAG_isStarSeparated :
    wDAG.IsStarSeparated ({(0 : Fin 5)} : Set (Fin 5)) {4} {1, 3} := by
  rintro p a ha b hb hph hpl ⟨⟨hnd, htrail, _⟩, hcol1⟩
  rw [mem_singleton_iff] at ha hb; subst ha; subst hb
  have hadj : ∀ {u v : Fin 5}, (wDAG.edge u v ∨ wDAG.edge v u) →
      (u = 0 → v = 1) ∧ (u = 1 → v = 0 ∨ v = 2) ∧ (u = 2 → v = 1 ∨ v = 3) ∧
      (u = 3 → v = 2 ∨ v = 4) := by
    intro u v h
    rcases h with h | h <;>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  -- Unroll the first 5 vertices of `p`:
  match p with
  | [] => simp at hph
  | [x] => simp at hph hpl; subst hph; exact absurd hpl (by decide)
  | x0 :: x1 :: xs =>
    simp only [List.head?_cons, Option.some.injEq] at hph; subst hph
    have hx1 : x1 = 1 := (hadj (htrail 0 (by simp))).1 rfl
    subst hx1
    match xs with
    | [] => simp at hpl
    | x2 :: xs2 =>
      have hx2_or : x2 = 0 ∨ x2 = 2 := (hadj (htrail 1 (by simp))).2.1 rfl
      have hx2_ne0 : x2 ≠ 0 := by
        intro h; subst h; exact (List.nodup_cons.1 hnd).1 (by simp)
      have hx2 : x2 = 2 := hx2_or.resolve_left hx2_ne0
      subst hx2
      match xs2 with
      | [] => simp at hpl
      | x3 :: xs3 =>
        have hx3_or : x3 = 1 ∨ x3 = 3 := (hadj (htrail 2 (by simp))).2.2.1 rfl
        have hx3_ne1 : x3 ≠ 1 := by
          intro h; subst h
          have hnd1 := (List.nodup_cons.1 hnd).2
          exact (List.nodup_cons.1 hnd1).1 (by simp)
        have hx3 : x3 = 3 := hx3_or.resolve_left hx3_ne1
        subst hx3
        match xs3 with
        | [] => simp at hpl
        | x4 :: xs4 =>
          have hx4_or : x4 = 2 ∨ x4 = 4 := (hadj (htrail 3 (by simp))).2.2.2 rfl
          have hx4_ne2 : x4 ≠ 2 := by
            intro h; subst h
            have hnd2 := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).2
            exact (List.nodup_cons.1 hnd2).1 (by simp)
          have hx4 : x4 = 4 := hx4_or.resolve_left hx4_ne2
          subst hx4
          -- Now both `i = 0` (`0 → 1 ← 2`) and `j = 2` (`2 → 3 ← 4`) are colliders!
          have hc0 : wDAG.IsColliderAt (0 :: 1 :: 2 :: 3 :: 4 :: xs4) 0 (by simp) :=
            ⟨Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          have hc2 : wDAG.IsColliderAt (0 :: 1 :: 2 :: 3 :: 4 :: xs4) 2 (by simp) :=
            ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
          have h02 := hcol1 0 2 (by simp) (by simp) hc0 hc2
          omega

/-- On the 5-node W-graph, extremal conditional independence `0 ⊥ 4 | {1, 3} [Λ_M]` holds for EVERY
positive recursive max-linear model `M`. -/
theorem wDAG_extremalCondIndep (M : MaxLinearModel wDAG) :
    ExtremalCondIndep M.exponentMeasure {(0 : Fin 5)} {4} {1, 3} :=
  M.isStarSeparated_imp_extremalCondIndep (by decide) (by decide) (by decide) (by
    simpa [Finset.coe_singleton, Finset.coe_insert] using wDAG_isStarSeparated)

/-! ### Witness B: 4-node Star DAG (`0 → 1, 0 → 2, 0 → 3`) — Even a Direct Edge! -/

/-- Edge relation of the 4-node star DAG `0 → 1, 0 → 2, 0 → 3`. -/
def starEdge (u v : Fin 4) : Prop := u = 0 ∧ v ≠ 0

lemma starEdge_lt (u v : Fin 4) (h : starEdge u v) : u < v := by
  rcases h with ⟨rfl, hv⟩
  exact Fin.pos_iff_ne_zero.2 hv

/-- The **4-node Star DAG** `0 → 1, 0 → 2, 0 → 3`. -/
def starDAG : DAG (Fin 4) := dagOfLt starEdge starEdge_lt

lemma starDAG_reach_iff (u v : Fin 4) : starDAG.Reach u v ↔ u = v ∨ u = 0 := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      rcases hbc with ⟨rfl, _⟩
      rcases ih with rfl | rfl <;> exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact starDAG.reach_refl _
    · by_cases hv : v = 0
      · subst hv; exact starDAG.reach_refl 0
      · exact starDAG.reach_of_edge ⟨rfl, hv⟩

/-- In the 4-node star DAG, `0` and `1` are connected by a DIRECT edge `0 → 1`, so `$*$-separation`
(and hence `$d$-separation`) FAILS given `{2, 3}`! -/
theorem starDAG_not_starSeparated :
    ¬ starDAG.IsStarSeparated ({(0 : Fin 4)} : Set (Fin 4)) {1} {2, 3} := by
  intro hstar
  refine hstar [0, 1] 0 (mem_singleton 0) 1 (mem_singleton 1) rfl rfl ?_
  refine ⟨⟨by decide, fun i hi ↦ ?_, fun i hi ↦ by simp at hi⟩, fun i _ hi _ _ _ ↦ by simp at hi⟩
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  exact Or.inl ⟨rfl, by simp⟩

theorem starDAG_not_dSeparated :
    ¬ starDAG.IsDSeparated ({(0 : Fin 4)} : Set (Fin 4)) {1} {2, 3} :=
  fun hd ↦ starDAG_not_starSeparated (starDAG.isDSeparated_imp_isStarSeparated hd)

/-- In the 4-node star DAG, **footprint separation HOLDS** for `A = {0}, B = {1}, C = {2, 3}`
because all four vertices have pairwise distinct `{2, 3}`-footprints! -/
theorem starDAG_isFootprintSeparated :
    starDAG.IsFootprintSeparated ({(0 : Fin 4)} : Set (Fin 4)) {1} {2, 3} := by
  constructor
  · rintro k hk ⟨⟨a, ha, hka⟩, _⟩
    rw [mem_singleton_iff] at ha; subst ha
    rw [starDAG_reach_iff] at hka
    have hk0 : k = 0 := by rcases hka with rfl | rfl <;> rfl
    subst hk0
    have h2 : (2 : Fin 4) ∈ starDAG.footprint ({2, 3} : Set (Fin 4)) 0 :=
      ⟨Or.inl rfl, (starDAG_reach_iff 0 2).2 (Or.inr rfl)⟩
    rw [hk] at h2; exact h2
  · rintro S _ ⟨k₁, k₂, hne, hk₁, hk₂⟩ _
    have hfp_eq : starDAG.footprint ({2, 3} : Set (Fin 4)) k₁ =
        starDAG.footprint ({2, 3} : Set (Fin 4)) k₂ := hk₁.trans hk₂.symm
    have h2_iff : (2 : Fin 4) ∈ starDAG.footprint ({2, 3} : Set (Fin 4)) k₁ ↔
        (2 : Fin 4) ∈ starDAG.footprint ({2, 3} : Set (Fin 4)) k₂ := by rw [hfp_eq]
    have h3_iff : (3 : Fin 4) ∈ starDAG.footprint ({2, 3} : Set (Fin 4)) k₁ ↔
        (3 : Fin 4) ∈ starDAG.footprint ({2, 3} : Set (Fin 4)) k₂ := by rw [hfp_eq]
    simp only [DAG.footprint, mem_ofPred_eq, starDAG_reach_iff, mem_insert_iff, mem_singleton_iff,
      true_or, or_true, true_and] at h2_iff h3_iff
    fin_cases k₁ <;> fin_cases k₂ <;> simp_all

/-- **Counterexample to faithfulness of direct edges in extremal CI:**
On the 4-node star DAG `0 → 1, 0 → 2, 0 → 3`, even though `0 → 1` is a direct causal edge,
extremal conditional independence `0 ⊥ 1 | {2, 3} [Λ_M]` holds for **EVERY** positive recursive
max-linear model `M`! -/
theorem starDAG_extremalCondIndep (M : MaxLinearModel starDAG) :
    ExtremalCondIndep M.exponentMeasure {(0 : Fin 4)} {1} {2, 3} :=
  M.isFootprintSeparated_imp_extremalCondIndep (by decide) (by decide) (by decide) (by
    simpa [Finset.coe_singleton, Finset.coe_insert] using starDAG_isFootprintSeparated)

/-- **Multivariate Pareto CI also holds on the 4-node star DAG for EVERY positive model `M`!**
On all four rays of `Λ_M`, `Y 0 = if 0 < Y 2 ∧ 0 < Y 3 then Y 2 * (M.coeff 0 0 / M.coeff 2 0) else 0`
is a deterministic measurable function of `(Y 2, Y 3)`. -/
theorem starDAG_paretoCondIndep (M : MaxLinearModel starDAG) :
    ParetoCondIndep M.exponentMeasure {(0 : Fin 4)} {1} {2, 3} := by
  intro hpos htop
  let A : Finset (Fin 4) := {0}
  let B : Finset (Fin 4) := {1}
  let C : Finset (Fin 4) := {2, 3}
  let Mset : Finset (Fin 4) := A ∪ B ∪ C
  have hA : A ⊆ Mset := Finset.subset_union_left.trans Finset.subset_union_left
  have hB : B ⊆ Mset := Finset.subset_union_right.trans Finset.subset_union_left
  have hC : C ⊆ Mset := Finset.subset_union_right
  let PSet : Set (Mset → ℝ) := {y : Mset → ℝ | ∃ i : Mset, 1 < y i}
  have : IsProbabilityMeasure (condProbMeasure M.exponentMeasure Mset PSet) :=
    isProbabilityMeasure_condProbMeasure hpos htop
  -- Explicit measurable function `φ : (C → ℝ) → (A → ℝ)` recovering `Y_0` from `(Y_2, Y_3)`!
  let c2 : C := ⟨2, by decide⟩
  let c3 : C := ⟨3, by decide⟩
  let φ : (C → ℝ) → (A → ℝ) := fun yC _ ↦
    if 0 < yC c2 ∧ 0 < yC c3 then yC c2 * (M.coeff 0 0 / M.coeff 2 0) else 0
  have hφ_meas : Measurable φ := by
    refine Measurable.of_eval fun _ ↦ Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_lt measurable_const (measurable_pi_apply c2)).inter
        (measurableSet_lt measurable_const (measurable_pi_apply c3))
    · exact (measurable_pi_apply c2).mul_const _
  refine condIndepFun_of_ae_eq_comp (measurable_subProj hA) (measurable_subProj hB)
    (measurable_subProj hC) hφ_meas ?_
  -- Prove `subProj hA =ᵐ φ ∘ subProj hC` on all of `M.exponentMeasure.map (coordProj Mset)`!
  have hae_full : subProj hA =ᵐ[M.exponentMeasure.map (coordProj Mset)] φ ∘ subProj hC := by
    change ∀ᵐ y ∂(M.exponentMeasure.map (coordProj Mset)), subProj hA y = (φ ∘ subProj hC) y
    rw [MaxLinearModel.exponentMeasure, rayExponentMeasure,
      map_finset_sum_measure (measurable_coordProj Mset), ae_finsetSum_measure_iff]
    intro k _
    have hray : Measurable (fun r : ℝ ↦ fun i : Fin 4 ↦ r * M.coeff i k) :=
      Measurable.of_eval fun i ↦ measurable_id.mul_const (M.coeff i k)
    rw [Measure.map_map (measurable_coordProj Mset) hray,
      ae_map_iff ((measurable_coordProj Mset).comp hray).aemeasurable
        (measurableSet_eq_fun (measurable_subProj hA) (hφ_meas.comp (measurable_subProj hC)))]
    filter_upwards [ae_pos_radialMeasure_one] with r hr
    funext a
    have ha0 : a.1 = 0 := Finset.mem_singleton.1 a.2
    have hcoeff_zero : ∀ i k' : Fin 4, ¬ starDAG.Reach k' i → M.coeff i k' = 0 := fun i k' hnr ↦
      le_antisymm (not_lt.1 fun hpos' ↦ hnr ((M.coeff_pos_iff i k').1 hpos')) (M.coeff_nonneg i k')
    have hc20 : 0 < M.coeff 2 0 := (M.coeff_pos_iff 2 0).2 ((starDAG_reach_iff 0 2).2 (Or.inr rfl))
    have hc30 : 0 < M.coeff 3 0 := (M.coeff_pos_iff 3 0).2 ((starDAG_reach_iff 0 3).2 (Or.inr rfl))
    simp only [Function.comp_apply, subProj, coordProj, ha0, φ, c2, c3]
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
    rcases hk_cases with rfl | rfl | rfl | rfl
    · -- `k = 0`: both `r * M.coeff 2 0 > 0` and `r * M.coeff 3 0 > 0`!
      simp only [mul_pos hr hc20, mul_pos hr hc30, and_self, ↓reduceIte]
      field_simp [hc20.ne']
    · -- `k = 1`: `M.coeff 0 1 = M.coeff 2 1 = 0`
      have h01 : M.coeff 0 1 = 0 := hcoeff_zero 0 1 (by rw [starDAG_reach_iff]; decide)
      have h21 : M.coeff 2 1 = 0 := hcoeff_zero 2 1 (by rw [starDAG_reach_iff]; decide)
      simp [h01, h21]
    · -- `k = 2`: `M.coeff 0 2 = M.coeff 3 2 = 0`
      have h02 : M.coeff 0 2 = 0 := hcoeff_zero 0 2 (by rw [starDAG_reach_iff]; decide)
      have h32 : M.coeff 3 2 = 0 := hcoeff_zero 3 2 (by rw [starDAG_reach_iff]; decide)
      simp [h02, h32]
    · -- `k = 3`: `M.coeff 0 3 = M.coeff 2 3 = 0`
      have h03 : M.coeff 0 3 = 0 := hcoeff_zero 0 3 (by rw [starDAG_reach_iff]; decide)
      have h23 : M.coeff 2 3 = 0 := hcoeff_zero 2 3 (by rw [starDAG_reach_iff]; decide)
      simp [h03, h23]
  exact Measure.ae_smul_measure (ae_restrict_of_ae hae_full) _

/-! ### Witness C: 4-node Non-Adjacent Collider (`0 → 2 ← 1, 0 → 3`) -/

/-- Edge relation of the 4-node non-adjacent collider `0 → 2, 1 → 2, 0 → 3`. -/
def colliderEdge (u v : Fin 4) : Prop :=
  (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2) ∨ (u = 0 ∧ v = 3)

lemma colliderEdge_lt (u v : Fin 4) (h : colliderEdge u v) : u < v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The **4-node Non-Adjacent Collider DAG** `0 → 2 ← 1, 0 → 3`. -/
def colliderDAG : DAG (Fin 4) := dagOfLt colliderEdge colliderEdge_lt

lemma colliderDAG_reach_iff (u v : Fin 4) :
    colliderDAG.Reach u v ↔ u = v ∨ colliderEdge u v := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      rcases ih with rfl | hab
      · exact Or.inr hbc
      · exfalso
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hbc with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1
  · rintro (rfl | h)
    · exact colliderDAG.reach_refl _
    · exact colliderDAG.reach_of_edge h

theorem colliderDAG_nonadjacent : ¬ colliderDAG.edge 0 1 ∧ ¬ colliderDAG.edge 1 0 := by
  constructor <;> simp [colliderDAG, dagOfLt, colliderEdge]

theorem colliderDAG_not_starSeparated :
    ¬ colliderDAG.IsStarSeparated ({(0 : Fin 4)} : Set (Fin 4)) {1} {2, 3} := by
  intro hstar
  refine hstar [0, 2, 1] 0 (mem_singleton 0) 1 (mem_singleton 1) rfl rfl ?_
  refine ⟨⟨by decide, fun i hi ↦ ?_, fun i hi ↦ ⟨fun _ ↦ ?_, fun hnc ↦ ?_⟩⟩,
    fun i j hi hj _ _ ↦ by simp at hi hj; omega⟩
  · have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi2 with rfl | rfl
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact ⟨2, Or.inl rfl, colliderDAG.reach_refl 2⟩
  · have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exfalso; exact hnc ⟨Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem colliderDAG_isFootprintSeparated :
    colliderDAG.IsFootprintSeparated ({(0 : Fin 4)} : Set (Fin 4)) {1} {2, 3} := by
  constructor
  · intro k hk
    exfalso
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
    rcases hk_cases with rfl | rfl | rfl | rfl
    · have : (2 : Fin 4) ∈ colliderDAG.footprint ({2, 3} : Set (Fin 4)) 0 :=
        ⟨Or.inl rfl, colliderDAG.reach_of_edge (Or.inl ⟨rfl, rfl⟩)⟩
      rw [hk] at this; exact this
    · have : (2 : Fin 4) ∈ colliderDAG.footprint ({2, 3} : Set (Fin 4)) 1 :=
        ⟨Or.inl rfl, colliderDAG.reach_of_edge (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      rw [hk] at this; exact this
    · have : (2 : Fin 4) ∈ colliderDAG.footprint ({2, 3} : Set (Fin 4)) 2 :=
        ⟨Or.inl rfl, colliderDAG.reach_refl 2⟩
      rw [hk] at this; exact this
    · have : (3 : Fin 4) ∈ colliderDAG.footprint ({2, 3} : Set (Fin 4)) 3 :=
        ⟨Or.inr rfl, colliderDAG.reach_refl 3⟩
      rw [hk] at this; exact this
  · rintro S _ ⟨k₁, k₂, hne, hk₁, hk₂⟩ ⟨⟨kA, hkA, a, ha, havA⟩, _⟩
    rw [mem_singleton_iff] at ha; subst ha
    have hreach0 : colliderDAG.Reach kA 0 := colliderDAG.avoidReach_imp_reach havA
    rw [colliderDAG_reach_iff] at hreach0
    have hkA0 : kA = 0 := by
      rcases hreach0 with rfl | h
      · rfl
      · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp at h2
    subst hkA0
    -- So `S = footprint 0 = {2, 3}`, which only `0` has! Contradicting `k₁ ≠ k₂`!
    have honly0 : ∀ k : Fin 4, colliderDAG.footprint ({2, 3} : Set (Fin 4)) k =
        colliderDAG.footprint ({2, 3} : Set (Fin 4)) 0 → k = 0 := by
      intro k hk
      have h2 : (2 : Fin 4) ∈ colliderDAG.footprint ({2, 3} : Set (Fin 4)) k := by
        rw [hk]; exact ⟨Or.inl rfl, colliderDAG.reach_of_edge (Or.inl ⟨rfl, rfl⟩)⟩
      have h3 : (3 : Fin 4) ∈ colliderDAG.footprint ({2, 3} : Set (Fin 4)) k := by
        rw [hk]; exact ⟨Or.inr rfl, colliderDAG.reach_of_edge (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      have hr2 := (colliderDAG_reach_iff k 2).1 h2.2
      have hr3 := (colliderDAG_reach_iff k 3).1 h3.2
      fin_cases k <;> simp [colliderEdge] at hr2 hr3 ⊢
    have h1 := honly0 k₁ (hk₁.trans hkA.symm)
    have h2 := honly0 k₂ (hk₂.trans hkA.symm)
    exact hne (h1.trans h2.symm)

theorem colliderDAG_extremalCondIndep (M : MaxLinearModel colliderDAG) :
    ExtremalCondIndep M.exponentMeasure {(0 : Fin 4)} {1} {2, 3} :=
  M.isFootprintSeparated_imp_extremalCondIndep (by decide) (by decide) (by decide) (by
    simpa [Finset.coe_singleton, Finset.coe_insert] using colliderDAG_isFootprintSeparated)

/-! ### Witness D: 4-node Diamond DAG (`0 → 1 → 3, 0 → 2 → 3`) — Weight-Dependent `2 × 2` Product -/

/-- Edge relation of the 4-node diamond DAG `0 → 1, 0 → 2, 1 → 3, 2 → 3`. -/
def diamondEdge (u v : Fin 4) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 3) ∨ (u = 2 ∧ v = 3)

lemma diamondEdge_lt (u v : Fin 4) (h : diamondEdge u v) : u < v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The **4-node Diamond DAG** `0 → 1 → 3, 0 → 2 → 3`. -/
def diamondDAG : DAG (Fin 4) := dagOfLt diamondEdge diamondEdge_lt

/-- Helper: build a unit-edge-weight model on `diamondDAG` with arbitrary positive diagonal `d`. -/
noncomputable def diamondModel (d : Fin 4 → ℝ) (hd : ∀ k, 0 < d k) : MaxLinearModel diamondDAG where
  weight i j := open Classical in if diamondEdge j i then 1 else 0
  diag := d
  weight_nonneg i j := by classical split_ifs <;> norm_num
  weight_pos_iff i j := by
    classical split_ifs with h
    · exact ⟨fun _ ↦ h, fun _ ↦ one_pos⟩
    · exact ⟨fun h0 ↦ absurd h0 (lt_irrefl 0), fun h' ↦ (h h').elim⟩
  diag_pos := hd

/-- Unit-weight diamond model (`weight = 1` on edges, `diag = 1`). -/
noncomputable def diamondUnitModel : MaxLinearModel diamondDAG :=
  diamondModel (fun _ ↦ 1) (fun _ ↦ one_pos)

/-- Perturbed diamond model (`weight = 1` on edges, `diag 0 = 2`, `diag 1 = diag 2 = diag 3 = 1`). -/
noncomputable def diamondPerturbedModel : MaxLinearModel diamondDAG :=
  diamondModel (fun k ↦ if k = 0 then 2 else 1) (fun k ↦ by split_ifs <;> norm_num)

private lemma diamondModel_walkWeight_eq_one (d : Fin 4 → ℝ) (hd : ∀ k, 0 < d k) :
    ∀ p : List (Fin 4), diamondDAG.IsDirWalk p → (diamondModel d hd).walkWeight p = 1
  | [], hp => (hp.1 rfl).elim
  | [_], _ => rfl
  | u :: v :: t, hp => by
    have huv : diamondEdge u v := (List.isChain_cons_cons.1 hp.2).1
    have ht : diamondDAG.IsDirWalk (v :: t) := ⟨List.cons_ne_nil _ _, (List.isChain_cons_cons.1 hp.2).2⟩
    change (open Classical in if diamondEdge u v then (1 : ℝ) else 0) *
      (diamondModel d hd).walkWeight (v :: t) = 1
    simp only [huv, ↓reduceIte, one_mul]
    exact diamondModel_walkWeight_eq_one d hd (v :: t) ht

/-- Exact path Kleene star values for any `diamondModel d hd`: `P_{i, k} = 1` iff `k →* i`, else `0`. -/
lemma diamondModel_kleenePath (d : Fin 4 → ℝ) (hd : ∀ k, 0 < d k) (i k : Fin 4) :
    (diamondModel d hd).kleenePath i k = open Classical in if diamondDAG.Reach k i then 1 else 0 := by
  by_cases hr : diamondDAG.Reach k i
  · simp only [hr, ↓reduceIte]
    have hpos : 0 < (diamondModel d hd).kleenePath i k := ((diamondModel d hd).kleenePath_pos_iff i k).2 hr
    obtain ⟨p, hp, _, _, hpw⟩ := (diamondModel d hd).exists_dirWalk_of_kleeneAux_pos hpos
    rw [MaxLinearModel.kleenePath, ← hpw, diamondModel_walkWeight_eq_one d hd p hp]
  · simp only [hr, ↓reduceIte]
    have hnot : ¬ 0 < (diamondModel d hd).kleenePath i k := fun hpos ↦
      hr (((diamondModel d hd).kleenePath_pos_iff i k).1 hpos)
    exact le_antisymm (not_lt.1 hnot) ((diamondModel d hd).kleenePath_nonneg i k)

lemma diamondDAG_reach_table (k i : Fin 4) :
    diamondDAG.Reach k i ↔
      k = i ∨ k = 0 ∨ i = 3 := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with rfl | rfl | h3
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inl rfl)
        · exact absurd h3 (by decide)
      · rcases ih with rfl | rfl | h3
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inl rfl)
        · exact absurd h3 (by decide)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact diamondDAG.reach_refl _
    · fin_cases i
      · exact diamondDAG.reach_refl 0
      · exact diamondDAG.reach_of_edge (Or.inl ⟨rfl, rfl⟩)
      · exact diamondDAG.reach_of_edge (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact diamondDAG.reach_trans (diamondDAG.reach_of_edge (Or.inl ⟨rfl, rfl⟩))
          (diamondDAG.reach_of_edge (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · fin_cases k
      · exact diamondDAG.reach_trans (diamondDAG.reach_of_edge (Or.inl ⟨rfl, rfl⟩))
          (diamondDAG.reach_of_edge (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      · exact diamondDAG.reach_of_edge (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact diamondDAG.reach_of_edge (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      · exact diamondDAG.reach_refl 3

/-- Helper: compute `rayL1Norm`, `rayDir`, `rayScaled` for `diamondModel d hd` on `A = {1}, B = {2}, C = {3}`. -/
lemma diamondModel_ray_values (d : Fin 4 → ℝ) (hd : ∀ k, 0 < d k) (k : Fin 4) :
    rayL1Norm (fun i ↦ (diamondModel d hd).coeff i k) {3} = d k ∧
    rayDir (fun i ↦ (diamondModel d hd).coeff i k) {3} = (fun _ ↦ 1) ∧
    rayScaled (fun i ↦ (diamondModel d hd).coeff i k) {3} {1} = (fun _ ↦ if k = 0 ∨ k = 1 then 1 else 0) ∧
    rayScaled (fun i ↦ (diamondModel d hd).coeff i k) {3} {2} = (fun _ ↦ if k = 0 ∨ k = 2 then 1 else 0) := by
  have hc3 : (diamondModel d hd).coeff 3 k = d k := by
    have hr3 : diamondDAG.Reach k 3 := (diamondDAG_reach_table k 3).2 (Or.inr (Or.inr rfl))
    simp only [MaxLinearModel.coeff, diamondModel_kleenePath, hr3, ↓reduceIte, one_mul]
    rfl
  have hnorm : rayL1Norm (fun i ↦ (diamondModel d hd).coeff i k) {3} = d k := by
    simp [rayL1Norm, hc3]
  refine ⟨hnorm, ?_, ?_, ?_⟩
  · funext c
    have hc : c.1 = 3 := Finset.mem_singleton.1 c.2
    simp [rayDir, hnorm, hc, hc3, (hd k).ne']
  · funext a
    have ha : a.1 = 1 := Finset.mem_singleton.1 a.2
    rw [rayScaled, hnorm, ha, MaxLinearModel.coeff, diamondModel_kleenePath, diamondDAG_reach_table]
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
    rcases hk_cases with rfl | rfl | rfl | rfl <;> simp [diamondModel, (hd _).ne']
  · funext b
    have hb : b.1 = 2 := Finset.mem_singleton.1 b.2
    rw [rayScaled, hnorm, hb, MaxLinearModel.coeff, diamondModel_kleenePath, diamondDAG_reach_table]
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
    rcases hk_cases with rfl | rfl | rfl | rfl <;> simp [diamondModel, (hd _).ne']

/-- **Non-deterministic rank-1 cancellation in extremal CI:**
On the 4-node diamond `0 → 1 → 3, 0 → 2 → 3` with unit weights, `1 ⊥ 2 | 3 [Λ]` HOLDS via the
exact `2 × 2` product measure `(δ_0 + δ_1) ⊗ (δ_0 + δ_1)`! -/
theorem diamondUnitModel_extremalCondIndep :
    ExtremalCondIndep diamondUnitModel.exponentMeasure {(1 : Fin 4)} {2} {3} := by
  rw [MaxLinearModel.exponentMeasure,
    extremalCondIndep_rayExponentMeasure_iff _ (fun k i ↦ diamondUnitModel.coeff_nonneg i k)
      (by decide) (by decide) (by decide)]
  constructor
  · intro k hk3
    have hval := (diamondModel_ray_values (fun _ ↦ 1) (fun _ ↦ one_pos) k).1
    have h0 : rayL1Norm (fun i ↦ diamondUnitModel.coeff i k) {3} = 0 := by
      simp [rayL1Norm, hk3 3 (Finset.mem_singleton_self 3)]
    change rayL1Norm (fun i ↦ diamondUnitModel.coeff i k) {3} = 1 at hval
    linarith
  · intro v x y
    by_cases hv : v = (fun _ ↦ 1)
    · subst hv
      have hvals := diamondModel_ray_values (fun _ ↦ 1) (fun _ ↦ one_pos)
      -- Evaluate all four `rayDirMass` sums over `Fin 4`!
      have htot : rayDirMass (fun k i ↦ diamondUnitModel.coeff i k) {3} (fun _ ↦ 1) (fun _ ↦ True) = 4 := by
        unfold rayDirMass
        rw [Fin.sum_univ_four]
        simp only [diamondUnitModel, (hvals 0).1, (hvals 1).1, (hvals 2).1, (hvals 3).1,
          (hvals 0).2.1, (hvals 1).2.1, (hvals 2).2.1, (hvals 3).2.1, one_pos, and_self, ↓reduceIte]
        norm_num
      have hx_val : x = (fun _ ↦ x ⟨1, Finset.mem_singleton_self 1⟩) := by
        funext a; congr 1; exact Subtype.ext (Finset.mem_singleton.1 a.2)
      have hy_val : y = (fun _ ↦ y ⟨2, Finset.mem_singleton_self 2⟩) := by
        funext b; congr 1; exact Subtype.ext (Finset.mem_singleton.1 b.2)
      set xv : ℝ := x ⟨1, Finset.mem_singleton_self 1⟩
      set yv : ℝ := y ⟨2, Finset.mem_singleton_self 2⟩
      have heq_x (c : ℝ) : ((fun _ : ({1} : Finset (Fin 4)) ↦ c) = x) ↔ xv = c := by
        constructor
        · intro h; exact (congrFun h ⟨1, Finset.mem_singleton_self 1⟩).symm
        · intro h; rw [hx_val, h]
      have heq_y (c : ℝ) : ((fun _ : ({2} : Finset (Fin 4)) ↦ c) = y) ↔ yv = c := by
        constructor
        · intro h; exact (congrFun h ⟨2, Finset.mem_singleton_self 2⟩).symm
        · intro h; rw [hy_val, h]
      rw [htot]
      unfold rayDirMass
      rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
      simp only [diamondUnitModel, (hvals 0).1, (hvals 1).1, (hvals 2).1, (hvals 3).1,
        (hvals 0).2.1, (hvals 1).2.1, (hvals 2).2.1, (hvals 3).2.1,
        (hvals 0).2.2.1, (hvals 1).2.2.1, (hvals 2).2.2.1, (hvals 3).2.2.1,
        (hvals 0).2.2.2, (hvals 1).2.2.2, (hvals 2).2.2.2, (hvals 3).2.2.2,
        one_pos, true_and, true_or, or_true, ↓reduceIte,
        show ¬ ((2 : Fin 4) = 0 ∨ (2 : Fin 4) = 1) by decide,
        show ¬ ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 1) by decide,
        show ¬ ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2) by decide,
        show ¬ ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 2) by decide,
        heq_x, heq_y]
      by_cases h1x : xv = 1 <;> by_cases h0x : xv = 0 <;>
        by_cases h1y : yv = 1 <;> by_cases h0y : yv = 0
      all_goals try linarith
      all_goals
        simp only [h1x, h0x, h1y, h0y, true_and, and_true, false_and, and_false, ↓reduceIte]
        norm_num
    · have h0 : ∀ k : Fin 4, 0 < rayL1Norm (fun i ↦ diamondUnitModel.coeff i k) {3} →
          rayDir (fun i ↦ diamondUnitModel.coeff i k) {3} = v → False := fun k _ hdir ↦
        hv (hdir.symm.trans (diamondModel_ray_values (fun _ ↦ 1) (fun _ ↦ one_pos) k).2.1)
      rw [rayDirMass_eq_zero (fun k h1 h2 _ ↦ h0 k h1 h2),
        rayDirMass_eq_zero (fun k h1 h2 _ ↦ h0 k h1 h2),
        rayDirMass_eq_zero (fun k h1 h2 _ ↦ h0 k h1 h2),
        rayDirMass_eq_zero (fun k h1 h2 _ ↦ h0 k h1 h2)]

/-- On the 4-node diamond `0 → 1 → 3, 0 → 2 → 3`, perturbing `diag 0 = 2` breaks the `2 × 2`
rank-1 condition (`2 * 5 = 10 ≠ 9 = 3 * 3`), so `1 ⊥ 2 | 3 [Λ]` FAILS! -/
theorem diamondPerturbedModel_not_extremalCondIndep :
    ¬ ExtremalCondIndep diamondPerturbedModel.exponentMeasure {(1 : Fin 4)} {2} {3} := by
  rw [MaxLinearModel.exponentMeasure,
    extremalCondIndep_rayExponentMeasure_iff _ (fun k i ↦ diamondPerturbedModel.coeff_nonneg i k)
      (by decide) (by decide) (by decide)]
  rintro ⟨_, hII⟩
  have h11 := hII (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)
  have hvals := diamondModel_ray_values (fun k ↦ if k = 0 then 2 else 1) (fun k ↦ by split_ifs <;> norm_num)
  unfold rayDirMass at h11
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four] at h11
  simp only [diamondPerturbedModel, (hvals 0).1, (hvals 1).1, (hvals 2).1, (hvals 3).1,
    (hvals 0).2.1, (hvals 1).2.1, (hvals 2).2.1, (hvals 3).2.1,
    (hvals 0).2.2.1, (hvals 1).2.2.1, (hvals 2).2.2.1, (hvals 3).2.2.1,
    (hvals 0).2.2.2, (hvals 1).2.2.2, (hvals 2).2.2.2, (hvals 3).2.2.2,
    show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide, ↓reduceIte] at h11
  simp only [funext_iff, Subtype.forall, Finset.mem_singleton, forall_eq,
    zero_ne_one] at h11
  norm_num at h11

/-! ### Complete Resolution Theorem for Engelke et al. (2024) -/

/-- **Complete Resolution of Engelke, Hentschel, Lalancette, and Röttger (`arXiv:2402.02187`):**
For recursive max-linear models on finite DAGs:
1. **(Universal implication)** For EVERY finite DAG `G`, EVERY positive model `M`, and EVERY
   pairwise disjoint `A, B, C`, `$d$-separation → $*$-separation → extremal CI`.
2. **($d$-sep ⊊ $*$-sep)** On the 5-node W-graph, `$d$-separation` fails while `$*$-separation`
   (and hence extremal CI for every model) holds.
3. **($*$-sep ⊊ universal extremal CI, even across a direct edge)** On the 4-node star DAG
   `0 → 1, 0 → 2, 0 → 3`, nodes `0` and `1` are directly adjacent (failing both `$d$-separation`
   and `$*$-separation` given `{2, 3}`), yet BOTH Engelke–Ivanovs–Strokorb extremal CI AND
   Engelke–Hitz multivariate Pareto CI hold for EVERY positive model `M`.
4. **(Universal extremal CI ⊊ fixed-weight extremal CI)** On the 4-node diamond DAG, extremal CI
   holds for unit weights (via a genuine `2 × 2` rank-1 product measure) and fails for perturbed
   weights (`diag 0 = 2`). -/
theorem engelke_2024_complete_resolution :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : DAG V) (M : MaxLinearModel G)
        (A B C : Finset V), Disjoint A B → Disjoint A C → Disjoint B C →
        G.IsStarSeparated (A : Set V) (B : Set V) (C : Set V) →
        ExtremalCondIndep M.exponentMeasure A B C) ∧
    (¬ wDAG.IsDSeparated ({0} : Set (Fin 5)) {4} {1, 3} ∧
      wDAG.IsStarSeparated ({0} : Set (Fin 5)) {4} {1, 3} ∧
      ∀ M : MaxLinearModel wDAG, ExtremalCondIndep M.exponentMeasure {0} {4} {1, 3}) ∧
    (starDAG.edge 0 1 ∧
      ¬ starDAG.IsStarSeparated ({0} : Set (Fin 4)) {1} {2, 3} ∧
      (∀ M : MaxLinearModel starDAG, ExtremalCondIndep M.exponentMeasure {0} {1} {2, 3}) ∧
      (∀ M : MaxLinearModel starDAG, ParetoCondIndep M.exponentMeasure {0} {1} {2, 3})) ∧
    (ExtremalCondIndep diamondUnitModel.exponentMeasure {1} {2} {3} ∧
      ¬ ExtremalCondIndep diamondPerturbedModel.exponentMeasure {1} {2} {3}) :=
  ⟨fun _ _ _ _ M _ _ _ hAB hAC hBC hstar ↦
      M.isStarSeparated_imp_extremalCondIndep hAB hAC hBC hstar,
   ⟨wDAG_not_dSeparated, wDAG_isStarSeparated, wDAG_extremalCondIndep⟩,
   ⟨⟨rfl, by decide⟩, starDAG_not_starSeparated, starDAG_extremalCondIndep, starDAG_paretoCondIndep⟩,
   ⟨diamondUnitModel_extremalCondIndep, diamondPerturbedModel_not_extremalCondIndep⟩⟩

end MaxLinearCI

end ExtremeValueTheory
