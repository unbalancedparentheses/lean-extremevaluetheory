/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Graphical Separation and Tropical Kleene Star for Recursive Max-Linear Models

This file formalizes the graph-theoretic and tropical-algebraic foundations needed to resolve the
open problem of Engelke, Hentschel, Lalancette, and Röttger (`arXiv:2402.02187`, *Graphical Models
for Multivariate Extremes*): how $d$-separation and $*$-separation compare to extremal conditional
independence in recursive max-linear models on a directed acyclic graph (DAG).

## Main definitions

* `DAG V`: a directed acyclic graph on a vertex type `V` (acyclic in the sense that the transitive
  closure of the edge relation is irreflexive).
* `DAG.Reach G u v`: directed reachability (`u →* v`).
* `DAG.AvoidReach G C u v`: directed reachability via a path whose vertices all avoid `C`.
* `DAG.IsDSeparated G A B C`: Pearl's $d$-separation between `A` and `B` given `C`.
* `DAG.IsStarSeparated G A B C`: $*$-separation of Améndola–Klüppelberg–Lauritzen–Tran
  (`arXiv:2002.09233`), allowing at most one collider on any connecting simple path.
* `DAG.IsFootprintSeparated G A B C`: footprint separation, strictly weaker than $*$-separation yet
  still sufficient for extremal conditional independence under all positive edge weights.
* `MaxLinearModel G`: a recursive max-linear model on a finite DAG `G` with positive edge weights
  and positive innovation scales, together with its tropical Kleene star `kleenePath` and
  coefficient matrix `coeff`.
* `RayCICondition b A B C`: the exact algebraic/measure-theoretic criterion on ray vectors `b`
  that characterizes extremal conditional independence (proved equivalent to Engelke–Ivanovs–Strokorb
  Definition 3.1 in `MaxLinearCI/Measure.lean`).

## Main results

* `DAG.isDSeparated_imp_isStarSeparated`: $d$-separation implies $*$-separation.
* `DAG.isStarSeparated_imp_isFootprintSeparated`: $*$-separation implies footprint separation
  (proved via a topologically minimal conditioning vertex and walk-to-simple-path shortening).
* `MaxLinearModel.isFootprintSeparated_imp_rayCICondition`: footprint separation implies
  `RayCICondition` for every positive weight matrix on `G`.
-/

open Set

namespace ExtremeValueTheory

namespace MaxLinearCI

/-! ### Directed acyclic graphs and directed paths -/

/-- A directed acyclic graph on a vertex type `V`. -/
structure DAG (V : Type*) where
  /-- `edge u v` represents a directed edge `u → v`. -/
  edge : V → V → Prop
  /-- Acyclicity: no vertex has a non-empty directed path back to itself. -/
  acyclic : ∀ u, ¬ Relation.TransGen edge u u

namespace DAG

variable {V : Type*} (G : DAG V)

/-- Directed reachability `u →* v` (reflexive transitive closure of `G.edge`). -/
def Reach (u v : V) : Prop := Relation.ReflTransGen G.edge u v

lemma reach_refl (u : V) : G.Reach u u := Relation.ReflTransGen.refl

lemma reach_trans {u v w : V} (h1 : G.Reach u v) (h2 : G.Reach v w) : G.Reach u w :=
  Relation.ReflTransGen.trans h1 h2

lemma reach_of_edge {u v : V} (h : G.edge u v) : G.Reach u v :=
  Relation.ReflTransGen.single h

lemma not_edge_self (u : V) : ¬ G.edge u u :=
  fun h ↦ G.acyclic u (Relation.TransGen.single h)

lemma not_edge_symm {u v : V} (h1 : G.edge u v) (h2 : G.edge v u) : False :=
  G.acyclic u (Relation.TransGen.trans (Relation.TransGen.single h1) (Relation.TransGen.single h2))

lemma reach_antisymm {u v : V} (h1 : G.Reach u v) (h2 : G.Reach v u) : u = v := by
  rcases Relation.ReflTransGen.cases_head h1 with rfl | ⟨w, huw, hwv⟩
  · rfl
  · exfalso
    have htr1 : Relation.TransGen G.edge u v := Relation.TransGen.head' huw hwv
    rcases Relation.ReflTransGen.cases_head h2 with hvu | ⟨w', hvw', hw'u⟩
    · subst hvu; exact G.acyclic _ htr1
    · exact G.acyclic u (Relation.TransGen.trans htr1 (Relation.TransGen.head' hvw' hw'u))

/-- A directed walk in `G` represented as a non-empty vertex list `p` whose consecutive entries are
linked by `G.edge`. -/
def IsDirWalk (p : List V) : Prop :=
  p ≠ [] ∧ p.IsChain G.edge

lemma isDirWalk_singleton (u : V) : G.IsDirWalk [u] := ⟨List.cons_ne_nil _ _, List.isChain_singleton u⟩

lemma isDirWalk_cons {u v : V} {t : List V} (he : G.edge u v) (ht : G.IsDirWalk (v :: t)) :
    G.IsDirWalk (u :: v :: t) :=
  ⟨List.cons_ne_nil _ _, List.isChain_cons_cons.2 ⟨he, ht.2⟩⟩

lemma reach_of_isDirWalk_get {p : List V} (hp : G.IsDirWalk p) {i j : ℕ}
    (hij : i ≤ j) (hj : j < p.length) : G.Reach p[i] p[j] := by
  induction j with
  | zero =>
    have hi : i = 0 := Nat.eq_zero_of_le_zero hij
    subst hi; exact G.reach_refl _
  | succ j ih =>
    rcases hij.eq_or_lt with rfl | hlt
    · exact G.reach_refl _
    · have hj' : j < p.length := Nat.lt_of_succ_lt hj
      have h1 : G.Reach p[i] p[j] := ih (Nat.lt_succ_iff.1 hlt) hj'
      have h2 : G.edge p[j] p[j + 1] := List.isChain_iff_getElem.1 hp.2 j hj
      exact G.reach_trans h1 (G.reach_of_edge h2)

lemma transGen_of_isDirWalk_get_lt {p : List V} (hp : G.IsDirWalk p) {i j : ℕ}
    (hij : i < j) (hj : j < p.length) : Relation.TransGen G.edge p[i] p[j] := by
  have hstep : G.edge p[i] p[i + 1] := List.isChain_iff_getElem.1 hp.2 i (Nat.lt_of_le_of_lt hij hj)
  exact Relation.TransGen.head' hstep (G.reach_of_isDirWalk_get hp hij hj)

/-- In a DAG, every directed walk is automatically simple (has no repeated vertices). -/
lemma isDirWalk_nodup {p : List V} (hp : G.IsDirWalk p) : p.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hEq
  ext
  rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
  · have htr := G.transGen_of_isDirWalk_get_lt hp hlt j.2
    rw [show p[i.1] = p[j.1] from hEq] at htr
    exact (G.acyclic _ htr).elim
  · exact heq
  · have htr := G.transGen_of_isDirWalk_get_lt hp hgt i.2
    rw [show p[i.1] = p[j.1] from hEq] at htr
    exact (G.acyclic _ htr).elim

/-- Helper: extract the first element from `p.head? = some u`. -/
lemma getElem_zero_of_head? {p : List V} {u : V} (hp : p ≠ []) (hh : p.head? = some u) :
    p[0]'(List.length_pos_iff.2 hp) = u := by
  cases p with
  | nil => exact (hp rfl).elim
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    exact hh

/-- Helper: extract the last element from `p.getLast? = some v`. -/
lemma getElem_last_of_getLast? {p : List V} {v : V} (hp : p ≠ []) (hl : p.getLast? = some v) :
    p[p.length - 1]'(Nat.sub_lt (List.length_pos_iff.2 hp) Nat.one_pos) = v := by
  have hgl : p.getLast? = p[p.length - 1]? := List.getLast?_eq_getElem?
  rw [hl, List.getElem?_eq_getElem (Nat.sub_lt (List.length_pos_iff.2 hp) Nat.one_pos)] at hgl
  exact Option.some.inj hgl.symm

/-- Reachability `u →* v` is equivalent to the existence of a directed walk from `u` to `v`. -/
lemma reach_iff_exists_dirWalk {u v : V} :
    G.Reach u v ↔ ∃ p : List V, G.IsDirWalk p ∧ p.head? = some u ∧ p.getLast? = some v := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[v], G.isDirWalk_singleton v, rfl, rfl⟩
    | @head a b hab _ ih =>
      rcases ih with ⟨p, hp, hhead, hlast⟩
      cases p with
      | nil => exact (hp.1 rfl).elim
      | cons x xs =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        refine ⟨a :: x :: xs, G.isDirWalk_cons hab hp, rfl, ?_⟩
        simpa using hlast
  · rintro ⟨p, hp, hhead, hlast⟩
    have h0 := getElem_zero_of_head? hp.1 hhead
    have hl := getElem_last_of_getLast? hp.1 hlast
    have hreach := G.reach_of_isDirWalk_get hp (Nat.zero_le (p.length - 1))
      (Nat.sub_lt (List.length_pos_iff.2 hp.1) Nat.one_pos)
    rwa [h0, hl] at hreach

/-- Directed reachability from `u` to `v` avoiding a set `C` (every vertex on the path is outside
`C`). -/
def AvoidReach (C : Set V) (u v : V) : Prop :=
  ∃ p : List V, G.IsDirWalk p ∧ p.head? = some u ∧ p.getLast? = some v ∧ ∀ x ∈ p, x ∉ C

lemma avoidReach_imp_reach {C : Set V} {u v : V} (h : G.AvoidReach C u v) : G.Reach u v := by
  rcases h with ⟨p, hp, hh, hl, _⟩
  exact G.reach_iff_exists_dirWalk.2 ⟨p, hp, hh, hl⟩

lemma avoidReach_refl {C : Set V} {u : V} (hu : u ∉ C) : G.AvoidReach C u u :=
  ⟨[u], G.isDirWalk_singleton u, rfl, rfl, fun x hx ↦ by simpa [List.mem_singleton.1 hx] using hu⟩

/-- Concatenation of two directed walks meeting at an endpoint. -/
lemma isDirWalk_append_tail {p q : List V} {w : V}
    (hp : G.IsDirWalk p) (hq : G.IsDirWalk q) (hpl : p.getLast? = some w)
    (hqh : q.head? = some w) :
    G.IsDirWalk (p ++ q.tail) ∧ (p ++ q.tail).head? = p.head? ∧
      (p ++ q.tail).getLast? = q.getLast? := by
  cases q with
  | nil => exact (hq.1 rfl).elim
  | cons y ys =>
    simp only [List.head?_cons, Option.some.injEq] at hqh
    subst hqh
    cases ys with
    | nil =>
      refine ⟨by simpa using hp, by simp, ?_⟩
      simpa using hpl
    | cons z zs =>
      have hyz : G.edge y z := (List.isChain_cons_cons.1 hq.2).1
      have hzs : (z :: zs).IsChain G.edge := (List.isChain_cons_cons.1 hq.2).2
      have hne : p ++ (z :: zs) ≠ [] := by simp [hp.1]
      have hchain : (p ++ (z :: zs)).IsChain G.edge := by
        rw [List.isChain_append]
        refine ⟨hp.2, hzs, fun a ha b hb ↦ ?_⟩
        rw [hpl] at ha
        simp only [Option.mem_def, Option.some.injEq] at ha
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst ha; subst hb; exact hyz
      refine ⟨⟨hne, hchain⟩, ?_, ?_⟩
      · cases p with
        | nil => exact (hp.1 rfl).elim
        | cons a as => simp
      · simp [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil z zs)]

/-- Prefix of a directed walk up to index `i`. -/
lemma isDirWalk_take {p : List V} (hp : G.IsDirWalk p) {i : ℕ} (hi : i < p.length) :
    G.IsDirWalk (p.take (i + 1)) ∧ (p.take (i + 1)).head? = p.head? ∧
      (p.take (i + 1)).getLast? = some p[i] := by
  have hne : p.take (i + 1) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [Nat.min_eq_left (Nat.succ_le_of_lt hi)] at this
  have hch : (p.take (i + 1)).IsChain G.edge := hp.2.take _
  refine ⟨⟨hne, hch⟩, ?_, ?_⟩
  · cases p with
    | nil => exact (hp.1 rfl).elim
    | cons a as => simp
  · rw [List.getLast?_eq_getElem?]
    have hlen : (p.take (i + 1)).length = i + 1 := List.length_take_of_le (Nat.succ_le_of_lt hi)
    rw [hlen, Nat.add_sub_cancel, List.getElem?_take_of_lt (Nat.lt_succ_self i),
      List.getElem?_eq_getElem hi]

/-- Suffix of a directed walk starting at index `i`. -/
lemma isDirWalk_drop {p : List V} (hp : G.IsDirWalk p) {i : ℕ} (hi : i < p.length) :
    G.IsDirWalk (p.drop i) ∧ (p.drop i).head? = some p[i] ∧
      (p.drop i).getLast? = p.getLast? := by
  have hne : p.drop i ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_drop, List.length_nil] at this
    omega
  have hch : (p.drop i).IsChain G.edge := hp.2.drop _
  refine ⟨⟨hne, hch⟩, ?_, ?_⟩
  · rw [List.head?_drop, List.getElem?_eq_getElem hi]
  · rw [List.getLast?_drop, ite_eq_right_iff]
    intro hle; omega

/-! ### $d$-separation, $*$-separation, and footprint separation -/

/-- Adjacent vertices in `p` are connected by an edge of `G` in either direction. -/
def IsUndirTrail (p : List V) : Prop :=
  ∀ i (h : i + 1 < p.length), G.edge p[i] p[i + 1] ∨ G.edge p[i + 1] p[i]

/-- Internal position `i + 1` of `p` is a collider (`p[i] → p[i+1] ← p[i+2]`). -/
def IsColliderAt (p : List V) (i : ℕ) (h : i + 2 < p.length) : Prop :=
  G.edge p[i] p[i + 1] ∧ G.edge p[i + 2] p[i + 1]

/-- A simple path `p` is $d$-connecting given `C`: every collider is an ancestor of `C` and every
non-collider lies outside `C`. -/
def IsDConnectingPath (C : Set V) (p : List V) : Prop :=
  p.Nodup ∧
  G.IsUndirTrail p ∧
  ∀ i (h : i + 2 < p.length),
    (G.IsColliderAt p i h → ∃ c ∈ C, G.Reach p[i + 1] c) ∧
    (¬ G.IsColliderAt p i h → p[i + 1] ∉ C)

/-- A simple path `p` is $*$-connecting given `C` (Améndola–Klüppelberg–Lauritzen–Tran 2022):
it is $d$-connecting given `C` and contains at most one collider. -/
def IsStarConnectingPath (C : Set V) (p : List V) : Prop :=
  G.IsDConnectingPath C p ∧
  ∀ i j (hi : i + 2 < p.length) (hj : j + 2 < p.length),
    G.IsColliderAt p i hi → G.IsColliderAt p j hj → i = j

/-- Pearl's **$d$-separation**: no simple $d$-connecting path from `A` to `B` given `C`. -/
def IsDSeparated (A B C : Set V) : Prop :=
  ∀ p : List V, ∀ a ∈ A, ∀ b ∈ B, p.head? = some a → p.getLast? = some b →
    ¬ G.IsDConnectingPath C p

/-- **$*$-separation** (Améndola–Klüppelberg–Lauritzen–Tran 2022): no simple $*$-connecting path
from `A` to `B` given `C`. -/
def IsStarSeparated (A B C : Set V) : Prop :=
  ∀ p : List V, ∀ a ∈ A, ∀ b ∈ B, p.head? = some a → p.getLast? = some b →
    ¬ G.IsStarConnectingPath C p

/-- The **$C$-footprint** of a vertex `k`: the subset of `C` reachable from `k`. -/
def footprint (C : Set V) (k : V) : Set V := {c ∈ C | G.Reach k c}

/-- **Footprint separation** `IsFootprintSeparated G A B C`:
1. No vertex with empty `C`-footprint can reach both `A` and `B`.
2. For every non-empty `C`-footprint `S` shared by at least two vertices `k₁ ≠ k₂`, either no vertex
   with footprint `S` has a `C`-avoiding directed path to `A`, or none has a `C`-avoiding directed
   path to `B`. -/
def IsFootprintSeparated (A B C : Set V) : Prop :=
  (∀ k, G.footprint C k = ∅ → ¬ ((∃ a ∈ A, G.Reach k a) ∧ (∃ b ∈ B, G.Reach k b))) ∧
  (∀ S : Set V, S.Nonempty →
    (∃ k₁ k₂, k₁ ≠ k₂ ∧ G.footprint C k₁ = S ∧ G.footprint C k₂ = S) →
    ¬ ((∃ k₁, G.footprint C k₁ = S ∧ ∃ a ∈ A, G.AvoidReach C k₁ a) ∧
       (∃ k₂, G.footprint C k₂ = S ∧ ∃ b ∈ B, G.AvoidReach C k₂ b)))

/-- $d$-separation implies $*$-separation. -/
theorem isDSeparated_imp_isStarSeparated {A B C : Set V} (h : G.IsDSeparated A B C) :
    G.IsStarSeparated A B C :=
  fun p a ha b hb hh hl hstar ↦ h p a ha b hb hh hl hstar.1

/-! ### Helper lemmas for walk-to-simple-path shortening -/

/-- A 0-collider trek: given two `C`-avoiding directed walks `pA : k →* a` and `pB : k →* b`,
there exists a simple $*$-connecting path from `a` to `b` with 0 colliders. -/
lemma exists_zeroCollider_starConnecting {C : Set V} {k a b : V}
    (pA pB : List V) (hpA : G.IsDirWalk pA) (hpB : G.IsDirWalk pB)
    (hAh : pA.head? = some k) (hAl : pA.getLast? = some a)
    (hBh : pB.head? = some k) (hBl : pB.getLast? = some b)
    (hAC : ∀ x ∈ pA, x ∉ C) (hBC : ∀ x ∈ pB, x ∉ C) :
    ∃ p : List V, p.head? = some a ∧ p.getLast? = some b ∧ G.IsStarConnectingPath C p := by
  classical
  -- Find the last index `i` of `pA` whose vertex lies in `pB`.
  have hS_ne : (Finset.univ.filter fun i : Fin pA.length ↦ pA[i.1] ∈ pB).Nonempty := by
    have hlen : 0 < pA.length := List.length_pos_iff.2 hpA.1
    refine ⟨⟨0, hlen⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    have h0 := getElem_zero_of_head? hpA.1 hAh
    have h0B := getElem_zero_of_head? hpB.1 hBh
    change pA[0] ∈ pB
    rw [h0, ← h0B]
    exact List.getElem_mem _
  let i₀ : Fin pA.length := (Finset.univ.filter fun i : Fin pA.length ↦ pA[i.1] ∈ pB).max' hS_ne
  have hi₀_mem : pA[i₀.1] ∈ pB := (Finset.mem_filter.1 (Finset.max'_mem _ hS_ne)).2
  have hi₀_max : ∀ i : Fin pA.length, pA[i.1] ∈ pB → i ≤ i₀ :=
    fun i hi ↦ Finset.le_max' _ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  obtain ⟨j₀, hj₀, hEq⟩ := List.getElem_of_mem hi₀_mem
  -- Suffixes `rA = pA.drop i₀.1` and `rB = pB.drop j₀` meet only at `pA[i₀.1]`.
  let rA := pA.drop i₀.1
  let rB := pB.drop j₀
  have hrA_len_eq : rA.length = pA.length - i₀.1 := List.length_drop
  have hrA := G.isDirWalk_drop hpA i₀.2
  have hrB := G.isDirWalk_drop hpB hj₀
  have hrA_walk : G.IsDirWalk rA := hrA.1
  have hrB_walk : G.IsDirWalk rB := hrB.1
  have hrA_head : rA.head? = some pA[i₀.1] := hrA.2.1
  have hrA_last : rA.getLast? = some a := hrA.2.2.trans hAl
  have hrB_head : rB.head? = some pA[i₀.1] := hrB.2.1.trans (congrArg some hEq)
  have hrB_last : rB.getLast? = some b := hrB.2.2.trans hBl
  let p := rA.reverse ++ rB.tail
  have hrA_nodup : rA.Nodup := G.isDirWalk_nodup hrA_walk
  have hrB_nodup : rB.Nodup := G.isDirWalk_nodup hrB_walk
  have hdisj : ∀ x ∈ rA.reverse, x ∉ rB.tail := by
    intro x hxA hxB
    rw [List.mem_reverse] at hxA
    have hxB' : x ∈ rB := List.mem_of_mem_tail hxB
    have hx_pB : x ∈ pB := List.mem_of_mem_drop hxB'
    obtain ⟨m, hm, hxm⟩ := List.getElem_of_mem hxA
    have hidx : i₀.1 + m < pA.length := by omega
    have hEqA : pA[i₀.1 + m] = x := by simpa [rA] using hxm
    have hle : (⟨i₀.1 + m, hidx⟩ : Fin pA.length) ≤ i₀ :=
      hi₀_max ⟨i₀.1 + m, hidx⟩ (hEqA.symm ▸ hx_pB)
    have hm0 : m = 0 := by have : i₀.1 + m ≤ i₀.1 := hle; omega
    subst hm0
    have hxw : x = pA[i₀.1] := by simpa using hEqA.symm
    cases h : rB with
    | nil => exact hrB_walk.1 h
    | cons y ys =>
      have hy : y = pA[i₀.1] := by rw [h] at hrB_head; simpa using hrB_head
      rw [h] at hrB_nodup hxB
      simp only [List.tail_cons] at hxB
      rw [hxw, ← hy] at hxB
      exact (List.nodup_cons.1 hrB_nodup).1 hxB
  have hp_nodup : p.Nodup := by
    refine List.nodup_append.2 ⟨List.nodup_reverse.2 hrA_nodup, hrB_nodup.tail, fun x hxA y hyB hxy ↦ ?_⟩
    subst hxy; exact hdisj x hxA hyB
  have hp_head : p.head? = some a := by
    have hrA_rev_ne : rA.reverse ≠ [] := by simp [hrA_walk.1]
    rw [List.head?_append_of_ne_nil _ hrA_rev_ne, List.head?_reverse, hrA_last]
  have hp_last : p.getLast? = some b := by
    cases h : rB with
    | nil => exact (hrB_walk.1 h).elim
    | cons y ys =>
      cases ys with
      | nil =>
        have hyb : y = b := by rw [h] at hrB_last; simpa using hrB_last
        have hyw : y = pA[i₀.1] := by rw [h] at hrB_head; simpa using hrB_head
        have hlast : p.getLast? = rA.head? := by
          simp only [p, h, List.tail_cons, List.append_nil, List.getLast?_reverse]
        rw [hlast, hrA_head, ← hyw, hyb]
      | cons z zs =>
        have hne : (z :: zs) ≠ [] := List.cons_ne_nil _ _
        simp only [p, h, List.tail_cons]
        rw [List.getLast?_append_of_ne_nil _ hne]
        rw [h] at hrB_last; simpa using hrB_last
  have hlenA : 0 < rA.length := List.length_pos_iff.2 hrA_walk.1
  have hrev_len : rA.reverse.length = rA.length := List.length_reverse
  have hp_len : p.length = rA.length + rB.tail.length := by simp [p, hrev_len]
  have hdir_left : ∀ t (ht : t + 1 < rA.length),
      G.edge (p[t + 1]'(by omega)) (p[t]'(by omega)) := by
    intro t ht
    have h1 : p[t]'(by omega) = rA[rA.length - 1 - t]'(by omega) := by
      simp only [p, List.getElem_append_left (by omega : t < rA.reverse.length), List.getElem_reverse]
    have h2 : p[t + 1]'(by omega) = rA[rA.length - 1 - (t + 1)]'(by omega) := by
      simp only [p, List.getElem_append_left (by omega : t + 1 < rA.reverse.length), List.getElem_reverse]
    rw [h1, h2]
    have hk : rA.length - 1 - (t + 1) + 1 = rA.length - 1 - t := by omega
    have hedge := List.isChain_iff_getElem.1 hrA_walk.2 (rA.length - 1 - (t + 1)) (by omega)
    simpa [hk] using hedge
  have hdir_right : ∀ t (ht1 : rA.length ≤ t + 1) (ht2 : t + 1 < p.length),
      G.edge (p[t]'(by omega)) (p[t + 1]'ht2) := by
    intro t ht1 ht2
    cases h : rB with
    | nil => exact (hrB_walk.1 h).elim
    | cons y ys =>
      have hyw : y = pA[i₀.1] := by rw [h] at hrB_head; simpa using hrB_head
      have hrA0 : rA[0]'hlenA = y := (getElem_zero_of_head? hrA_walk.1 hrA_head).trans hyw.symm
      have hys_len : rB.tail.length = ys.length := by simp [h]
      rcases (Nat.le_iff_lt_or_eq.1 ht1) with hlt | heq
      · have ht_ge : rA.reverse.length ≤ t := by omega
        have h1 : p[t]'(by omega) = (y :: ys)[t - rA.length + 1]'(by simp; omega) := by
          simp only [p, h, List.tail_cons, List.getElem_append_right ht_ge, hrev_len,
            List.getElem_cons_succ]
        have h2 : p[t + 1]'ht2 = (y :: ys)[t - rA.length + 1 + 1]'(by simp; omega) := by
          have : t + 1 - rA.length = t - rA.length + 1 := by omega
          simp only [p, h, List.tail_cons,
            List.getElem_append_right (by omega : rA.reverse.length ≤ t + 1), hrev_len, this,
            List.getElem_cons_succ]
        rw [h1, h2]
        have hch := hrB_walk.2; rw [h] at hch
        exact List.isChain_iff_getElem.1 hch (t - rA.length + 1) (by simp; omega)
      · have h1 : p[t]'(by omega) = y := by
          have ht_lt : t < rA.reverse.length := by omega
          simp only [p, List.getElem_append_left ht_lt, List.getElem_reverse]
          have : rA.length - 1 - t = 0 := by omega
          simpa [this] using hrA0
        have h2 : p[t + 1]'ht2 = (y :: ys)[1]'(by simp; omega) := by
          have hge : rA.reverse.length ≤ t + 1 := by omega
          have hsub : t + 1 - rA.reverse.length = 0 := by omega
          simp only [p, h, List.tail_cons, List.getElem_append_right hge, hsub,
            List.getElem_cons_succ]
        rw [h1, h2]
        have hch := hrB_walk.2; rw [h] at hch
        exact List.isChain_iff_getElem.1 hch 0 (by simp; omega)
  have hno_col : ∀ i (hi : i + 2 < p.length), ¬ G.IsColliderAt p i hi := by
    intro i hi ⟨h1, h2⟩
    by_cases hlt : i + 1 < rA.length
    · exact G.not_edge_symm h1 (hdir_left i hlt)
    · exact G.not_edge_symm h2 (hdir_right (i + 1) (by omega) hi)
  have hp_not_C : ∀ x ∈ p, x ∉ C := by
    intro x hx
    rcases List.mem_append.1 hx with hxA | hxB
    · rw [List.mem_reverse] at hxA
      exact hAC x (List.mem_of_mem_drop hxA)
    · exact hBC x (List.mem_of_mem_drop (List.mem_of_mem_tail hxB))
  refine ⟨p, hp_head, hp_last, ⟨hp_nodup, fun i hi ↦ ?_, fun i hi ↦ ⟨fun hc ↦ (hno_col i hi hc).elim,
    fun _ ↦ hp_not_C _ (List.getElem_mem _)⟩⟩, fun i _ hi _ hc _ ↦ (hno_col i hi hc).elim⟩
  by_cases hlt : i + 1 < rA.length
  · exact Or.inr (hdir_left i hlt)
  · exact Or.inl (hdir_right i (by omega) hi)

/-- Gluing a 1-collider simple path `a ←* u₁ →* w ←* u₂ →* b` from four directed walks whose
vertices are pairwise disjoint except at the junctions `u₁, w, u₂`, with `r₂` and `r₃` having
length ≥ 2 (`u₁ ≠ w`, `u₂ ≠ w`). -/
lemma exists_oneCollider_starConnecting {C : Set V} {a b u₁ u₂ w : V}
    (r1 r2 r3 r4 : List V)
    (hr1 : G.IsDirWalk r1) (hr2 : G.IsDirWalk r2) (hr3 : G.IsDirWalk r3) (hr4 : G.IsDirWalk r4)
    (h1h : r1.head? = some u₁) (h1l : r1.getLast? = some a)
    (h2h : r2.head? = some u₁) (h2l : r2.getLast? = some w)
    (h3h : r3.head? = some u₂) (h3l : r3.getLast? = some w)
    (h4h : r4.head? = some u₂) (h4l : r4.getLast? = some b)
    (hw1 : u₁ ≠ w) (hw2 : u₂ ≠ w)
    (h12 : ∀ x ∈ r1, x ∈ r2 → x = u₁)
    (h34 : ∀ x ∈ r3, x ∈ r4 → x = u₂)
    (h23 : ∀ x ∈ r2, x ∈ r3 → x = w)
    (h14 : ∀ x ∈ r1, x ∉ r4) (h13 : ∀ x ∈ r1, x ∉ r3) (h24 : ∀ x ∈ r2, x ∉ r4)
    (h1C : ∀ x ∈ r1, x ∉ C) (h4C : ∀ x ∈ r4, x ∉ C)
    (h2C : ∀ x ∈ r2, x ≠ w → x ∉ C) (h3C : ∀ x ∈ r3, x ≠ w → x ∉ C)
    (hwC : ∃ c ∈ C, G.Reach w c) :
    ∃ p : List V, p.head? = some a ∧ p.getLast? = some b ∧ G.IsStarConnectingPath C p := by
  have hlen1 : 0 < r1.length := List.length_pos_iff.2 hr1.1
  have hlen2 : 2 ≤ r2.length := by
    cases r2 with
    | nil => exact (hr2.1 rfl).elim
    | cons x xs =>
      cases xs with
      | nil =>
        simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h2h h2l
        exact (hw1 (h2h.symm.trans h2l)).elim
      | cons _ _ => simp
  have hlen3 : 2 ≤ r3.length := by
    cases r3 with
    | nil => exact (hr3.1 rfl).elim
    | cons x xs =>
      cases xs with
      | nil =>
        simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h3h h3l
        exact (hw2 (h3h.symm.trans h3l)).elim
      | cons _ _ => simp
  have hlen4 : 0 < r4.length := List.length_pos_iff.2 hr4.1
  let s1 := r1.reverse
  let s2 := r2.tail
  let s3 := r3.reverse.tail
  let s4 := r4.tail
  let p := s1 ++ s2 ++ s3 ++ s4
  have hnd1 : r1.Nodup := G.isDirWalk_nodup hr1
  have hnd2 : r2.Nodup := G.isDirWalk_nodup hr2
  have hnd3 : r3.Nodup := G.isDirWalk_nodup hr3
  have hnd4 : r4.Nodup := G.isDirWalk_nodup hr4
  have hnot_u1_s2 : u₁ ∉ s2 := by
    cases h : r2 with
    | nil => exact (hr2.1 h).elim
    | cons x xs =>
      rw [h] at h2h hnd2; simp only [List.head?_cons, Option.some.injEq] at h2h; subst h2h
      simpa [s2, h] using (List.nodup_cons.1 hnd2).1
  have hnot_w_s3 : w ∉ s3 := by
    cases h : r3.reverse with
    | nil =>
      have := congrArg List.length h; simp only [List.length_reverse, List.length_nil] at this; omega
    | cons x xs =>
      have hx : x = w := by
        have := congrArg List.head? h
        rw [List.head?_reverse, h3l] at this; simpa using this.symm
      have hnd3r : (x :: xs).Nodup := h ▸ List.nodup_reverse.2 hnd3
      have hs3_eq : s3 = xs := by simp only [s3, h, List.tail_cons]
      rw [← hx, hs3_eq]
      exact (List.nodup_cons.1 hnd3r).1
  have hnot_u2_s4 : u₂ ∉ s4 := by
    cases h : r4 with
    | nil => exact (hr4.1 h).elim
    | cons x xs =>
      rw [h] at h4h hnd4; simp only [List.head?_cons, Option.some.injEq] at h4h; subst h4h
      simpa [s4, h] using (List.nodup_cons.1 hnd4).1
  have hs1_mem : ∀ {x}, x ∈ s1 → x ∈ r1 := fun hx ↦ List.mem_reverse.1 hx
  have hs2_mem : ∀ {x}, x ∈ s2 → x ∈ r2 := fun hx ↦ List.mem_of_mem_tail hx
  have hs3_mem : ∀ {x}, x ∈ s3 → x ∈ r3 := fun hx ↦ List.mem_reverse.1 (List.mem_of_mem_tail hx)
  have hs4_mem : ∀ {x}, x ∈ s4 → x ∈ r4 := fun hx ↦ List.mem_of_mem_tail hx
  have hd12 : ∀ x ∈ s1, ∀ y ∈ s2, x ≠ y := fun x hx1 y hx2 hxy ↦
    hnot_u1_s2 ((h12 x (hs1_mem hx1) (hs2_mem (hxy ▸ hx2))) ▸ (hxy ▸ hx2))
  have hd23 : ∀ x ∈ s2, ∀ y ∈ s3, x ≠ y := fun x hx2 y hx3 hxy ↦
    hnot_w_s3 ((h23 x (hs2_mem hx2) (hs3_mem (hxy ▸ hx3))) ▸ (hxy ▸ hx3))
  have hd34 : ∀ x ∈ s3, ∀ y ∈ s4, x ≠ y := fun x hx3 y hx4 hxy ↦
    hnot_u2_s4 ((h34 x (hs3_mem hx3) (hs4_mem (hxy ▸ hx4))) ▸ (hxy ▸ hx4))
  have hd13 : ∀ x ∈ s1, ∀ y ∈ s3, x ≠ y := fun x hx1 y hx3 hxy ↦ h13 x (hs1_mem hx1) (hs3_mem (hxy ▸ hx3))
  have hd14 : ∀ x ∈ s1, ∀ y ∈ s4, x ≠ y := fun x hx1 y hx4 hxy ↦ h14 x (hs1_mem hx1) (hs4_mem (hxy ▸ hx4))
  have hd24 : ∀ x ∈ s2, ∀ y ∈ s4, x ≠ y := fun x hx2 y hx4 hxy ↦ h24 x (hs2_mem hx2) (hs4_mem (hxy ▸ hx4))
  have hp_nodup : p.Nodup := by
    have h12' : (s1 ++ s2).Nodup := List.nodup_append.2 ⟨List.nodup_reverse.2 hnd1, hnd2.tail, hd12⟩
    have h123' : (s1 ++ s2 ++ s3).Nodup := List.nodup_append.2
      ⟨h12', (List.nodup_reverse.2 hnd3).tail,
       fun x hx y hy3 ↦ (List.mem_append.1 hx).elim (fun h ↦ hd13 x h y hy3) (fun h ↦ hd23 x h y hy3)⟩
    exact List.nodup_append.2 ⟨h123', hnd4.tail, fun x hx y hy4 ↦ by
      rcases List.mem_append.1 hx with hx12 | hx3
      · exact (List.mem_append.1 hx12).elim (fun h ↦ hd14 x h y hy4) (fun h ↦ hd24 x h y hy4)
      · exact hd34 x hx3 y hy4⟩
  let L1 := r1.length
  let L2 := L1 + (r2.length - 1)
  let L3 := L2 + (r3.length - 1)
  have hls1 : s1.length = L1 := List.length_reverse
  have hls2 : s2.length = r2.length - 1 := List.length_tail
  have hls3 : s3.length = r3.length - 1 := by simp [s3]
  have hls4 : s4.length = r4.length - 1 := List.length_tail
  have hlp : p.length = L3 + (r4.length - 1) := by
    simp only [p, List.length_append, hls1, hls2, hls3, hls4, L1, L2, L3]
  have hp_head : p.head? = some a := by
    have hs1_ne : s1 ≠ [] := by simp [s1, hr1.1]
    have h12_ne : s1 ++ s2 ≠ [] := List.append_ne_nil_of_left_ne_nil hs1_ne s2
    have h123_ne : s1 ++ s2 ++ s3 ≠ [] := List.append_ne_nil_of_left_ne_nil h12_ne s3
    rw [List.head?_append_of_ne_nil _ h123_ne, List.head?_append_of_ne_nil _ h12_ne,
      List.head?_append_of_ne_nil _ hs1_ne, List.head?_reverse, h1l]
  have hp_last : p.getLast? = some b := by
    cases h : r4 with
    | nil => exact (hr4.1 h).elim
    | cons y ys =>
      cases ys with
      | nil =>
        have hyb : y = b := by rw [h] at h4l; simpa using h4l
        have hyu : y = u₂ := by rw [h] at h4h; simpa using h4h
        have hs4_nil : s4 = [] := by simp [s4, h]
        have hs3_ne : s3 ≠ [] := by
          intro h0; have := congrArg List.length h0; rw [hls3] at this; simp at this; omega
        simp only [p, hs4_nil, List.append_nil]
        rw [List.getLast?_append_of_ne_nil _ hs3_ne]
        cases hr3r : r3.reverse with
        | nil =>
          have h0 := congrArg List.length hr3r; simp only [List.length_reverse, List.length_nil] at h0; omega
        | cons z zs =>
          cases zs with
          | nil =>
            have h1 := congrArg List.length hr3r; simp only [List.length_reverse, List.length_singleton] at h1; omega
          | cons z' zs' =>
            have hs3_eq : s3 = z' :: zs' := by simp only [s3, hr3r, List.tail_cons]
            have hgl : (z' :: zs').getLast? = some u₂ := by
              have hrev : (z :: z' :: zs').getLast? = some u₂ := by
                rw [← hr3r, List.getLast?_reverse, h3h]
              simpa using hrev
            rw [hs3_eq, hgl, ← hyu, hyb]
      | cons z zs =>
        have hs4_ne : s4 ≠ [] := by simp [s4, h]
        rw [List.getLast?_append_of_ne_nil _ hs4_ne]
        rw [h] at h4l
        simpa [s4, h] using h4l
  have hp_seg1 : ∀ t (ht : t < L1), p[t]'(by omega) = r1[L1 - 1 - t]'(by omega) := by
    intro t ht
    have h1 : t < (s1 ++ s2 ++ s3).length := by simp [hls1, hls2, hls3]; omega
    have h2 : t < (s1 ++ s2).length := by simp [hls1, hls2]; omega
    have h3 : t < s1.length := by omega
    simp only [p, List.getElem_append_left h1, List.getElem_append_left h2,
      List.getElem_append_left h3, s1, List.getElem_reverse, L1]
  have hp_seg2 : ∀ t (ht1 : L1 - 1 ≤ t) (ht2 : t < L2),
      p[t]'(by omega) = r2[t - (L1 - 1)]'(by omega) := by
    intro t ht1 ht2
    rcases ht1.eq_or_lt with rfl | hlt
    · rw [hp_seg1 (L1 - 1) (by omega)]
      have h1 : r1[0]'hlen1 = u₁ := getElem_zero_of_head? hr1.1 h1h
      have h2 : r2[0]'(by omega) = u₁ := getElem_zero_of_head? hr2.1 h2h
      simp [h1, h2]
    · have h1 : t < (s1 ++ s2 ++ s3).length := by simp [hls1, hls2, hls3]; omega
      have h2 : t < (s1 ++ s2).length := by simp [hls1, hls2]; omega
      have h3 : s1.length ≤ t := by omega
      simp only [p, List.getElem_append_left h1, List.getElem_append_left h2,
        List.getElem_append_right h3, s2, List.getElem_tail, hls1]
      congr 1; omega
  have hp_seg3 : ∀ t (ht1 : L2 - 1 ≤ t) (ht2 : t < L3),
      p[t]'(by omega) = r3[r3.length - 1 - (t - (L2 - 1))]'(by omega) := by
    intro t ht1 ht2
    rcases ht1.eq_or_lt with rfl | hlt
    · rw [hp_seg2 (L2 - 1) (by omega) (by omega)]
      have hsub1 : L2 - 1 - (L1 - 1) = r2.length - 1 := by omega
      have hw_r2 : r2[r2.length - 1]'(by omega) = w := getElem_last_of_getLast? hr2.1 h2l
      have hw_r3 : r3[r3.length - 1]'(by omega) = w := getElem_last_of_getLast? hr3.1 h3l
      simp [hsub1, hw_r2, hw_r3]
    · have h1 : t < (s1 ++ s2 ++ s3).length := by simp [hls1, hls2, hls3]; omega
      have h2 : (s1 ++ s2).length ≤ t := by simp [hls1, hls2]; omega
      simp only [p, List.getElem_append_left h1, List.getElem_append_right h2, s3,
        List.getElem_tail, List.getElem_reverse, List.length_append, hls1, hls2]
      congr 1; omega
  have hp_seg4 : ∀ t (ht1 : L3 - 1 ≤ t) (ht2 : t < p.length),
      p[t]'ht2 = r4[t - (L3 - 1)]'(by omega) := by
    intro t ht1 ht2
    rcases ht1.eq_or_lt with rfl | hlt
    · rw [hp_seg3 (L3 - 1) (by omega) (by omega)]
      have hsub1 : r3.length - 1 - (L3 - 1 - (L2 - 1)) = 0 := by omega
      have hu2_r3 : r3[0]'(by omega) = u₂ := getElem_zero_of_head? hr3.1 h3h
      have hu2_r4 : r4[0]'hlen4 = u₂ := getElem_zero_of_head? hr4.1 h4h
      simp [hsub1, hu2_r3, hu2_r4]
    · have h1 : (s1 ++ s2 ++ s3).length ≤ t := by simp [hls1, hls2, hls3]; omega
      simp only [p, List.getElem_append_right h1, s4, List.getElem_tail, List.length_append,
        hls1, hls2, hls3]
      congr 1; omega
  have hedge1 : ∀ t (ht : t + 1 < L1), G.edge (p[t + 1]'(by omega)) (p[t]'(by omega)) := by
    intro t ht
    rw [hp_seg1 t (by omega), hp_seg1 (t + 1) ht]
    have hstep := List.isChain_iff_getElem.1 hr1.2 (L1 - 1 - (t + 1)) (by omega)
    have hk : L1 - 1 - (t + 1) + 1 = L1 - 1 - t := by omega
    simpa [hk] using hstep
  have hedge2 : ∀ t (ht1 : L1 - 1 ≤ t) (ht2 : t + 1 < L2),
      G.edge (p[t]'(by omega)) (p[t + 1]'(by omega)) := by
    intro t ht1 ht2
    rw [hp_seg2 t ht1 (by omega), hp_seg2 (t + 1) (by omega) ht2]
    have hstep := List.isChain_iff_getElem.1 hr2.2 (t - (L1 - 1)) (by omega)
    have hk : t - (L1 - 1) + 1 = t + 1 - (L1 - 1) := by omega
    simpa [hk] using hstep
  have hedge3 : ∀ t (ht1 : L2 - 1 ≤ t) (ht2 : t + 1 < L3),
      G.edge (p[t + 1]'(by omega)) (p[t]'(by omega)) := by
    intro t ht1 ht2
    rw [hp_seg3 t ht1 (by omega), hp_seg3 (t + 1) (by omega) ht2]
    have hstep := List.isChain_iff_getElem.1 hr3.2 (r3.length - 1 - (t + 1 - (L2 - 1))) (by omega)
    have hk : r3.length - 1 - (t + 1 - (L2 - 1)) + 1 = r3.length - 1 - (t - (L2 - 1)) := by omega
    simpa [hk] using hstep
  have hedge4 : ∀ t (ht1 : L3 - 1 ≤ t) (ht2 : t + 1 < p.length),
      G.edge (p[t]'(by omega)) (p[t + 1]'ht2) := by
    intro t ht1 ht2
    rw [hp_seg4 t ht1 (by omega), hp_seg4 (t + 1) (by omega) ht2]
    have hstep := List.isChain_iff_getElem.1 hr4.2 (t - (L3 - 1)) (by omega)
    have hk : t - (L3 - 1) + 1 = t + 1 - (L3 - 1) := by omega
    simpa [hk] using hstep
  have hcol_only : ∀ i (hi : i + 2 < p.length), G.IsColliderAt p i hi → i + 1 = L2 - 1 := by
    intro i hi ⟨h1, h2⟩
    by_cases hc1 : i + 1 < L1
    · exact (G.not_edge_symm h1 (hedge1 i hc1)).elim
    · by_cases hc2 : i + 2 < L2
      · exact (G.not_edge_symm h2 (hedge2 (i + 1) (by omega) hc2)).elim
      · by_cases hc2' : i + 1 = L2 - 1
        · exact hc2'
        · by_cases hc3 : i + 1 < L3 - 1
          · exact (G.not_edge_symm h1 (hedge3 i (by omega) (by omega))).elim
          · exact (G.not_edge_symm h2 (hedge4 (i + 1) (by omega) hi)).elim
  have hp_w : p[L2 - 1]'(by omega) = w := by
    rw [hp_seg2 (L2 - 1) (by omega) (by omega)]
    have hsub : L2 - 1 - (L1 - 1) = r2.length - 1 := by omega
    have hw_r2 : r2[r2.length - 1]'(by omega) = w := getElem_last_of_getLast? hr2.1 h2l
    simpa [hsub] using hw_r2
  have hp_not_C : ∀ t (ht : t < p.length), t ≠ L2 - 1 → p[t]'ht ∉ C := by
    intro t ht hne
    have hpw_ne : p[t]'ht ≠ w := by
      intro heq
      have hidx := (List.nodup_iff_injective_getElem.1 hp_nodup)
        (a₁ := ⟨t, ht⟩) (a₂ := ⟨L2 - 1, by omega⟩) (heq.trans hp_w.symm)
      exact hne (congrArg Fin.val hidx)
    by_cases h1 : t < L1
    · rw [hp_seg1 t h1]; exact h1C _ (List.getElem_mem _)
    · by_cases h2 : t < L2
      · rw [hp_seg2 t (by omega) h2]
        exact h2C _ (List.getElem_mem _) (by simpa [hp_seg2 t (by omega) h2] using hpw_ne)
      · by_cases h3 : t < L3
        · rw [hp_seg3 t (by omega) h3]
          exact h3C _ (List.getElem_mem _) (by simpa [hp_seg3 t (by omega) h3] using hpw_ne)
        · rw [hp_seg4 t (by omega) ht]; exact h4C _ (List.getElem_mem _)
  refine ⟨p, hp_head, hp_last, ⟨hp_nodup, fun t ht ↦ ?_, fun i hi ↦ ⟨fun hc ↦ ?_, fun hnc ↦ ?_⟩⟩,
    fun i j hi hj hci hcj ↦ ?_⟩
  · by_cases h1 : t + 1 < L1
    · exact Or.inr (hedge1 t h1)
    · by_cases h2 : t + 1 < L2
      · exact Or.inl (hedge2 t (by omega) h2)
      · by_cases h3 : t + 1 < L3
        · exact Or.inr (hedge3 t (by omega) h3)
        · exact Or.inl (hedge4 t (by omega) ht)
  · have heq := hcol_only i hi hc
    simpa [heq, hp_w] using hwC
  · apply hp_not_C (i + 1) (by omega)
    intro heq
    apply hnc
    exact ⟨hedge2 i (by omega) (by omega), hedge3 (i + 1) (by omega) (by omega)⟩
  · have h1 := hcol_only i hi hci
    have h2 := hcol_only j hj hcj
    omega

/-- In a finite DAG, every non-empty set `S` has a topologically minimal element under `G.Reach`. -/
lemma exists_minimal_reach [Fintype V] {S : Set V} (hS : S.Nonempty) :
    ∃ c ∈ S, ∀ c' ∈ S, G.Reach c' c → c' = c := by
  classical
  let f : V → ℕ := fun c ↦ (Finset.univ.filter fun x ↦ G.Reach x c).card
  let Sf : Finset V := Finset.univ.filter (· ∈ S)
  have hSf : Sf.Nonempty := by
    rcases hS with ⟨c, hc⟩
    exact ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
  obtain ⟨c, hcSf, hmin⟩ := Sf.exists_min_image f hSf
  have hcS : c ∈ S := (Finset.mem_filter.1 hcSf).2
  refine ⟨c, hcS, fun c' hc'S hreach ↦ ?_⟩
  have hsub : (Finset.univ.filter fun x ↦ G.Reach x c') ⊆
      (Finset.univ.filter fun x ↦ G.Reach x c) := by
    intro x hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      G.reach_trans (Finset.mem_filter.1 hx).2 hreach⟩
  have hle : f c ≤ f c' := hmin c' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc'S⟩)
  have heq : (Finset.univ.filter fun x ↦ G.Reach x c') =
      (Finset.univ.filter fun x ↦ G.Reach x c) :=
    Finset.eq_of_subset_of_card_le hsub hle
  have hc_mem : c ∈ Finset.univ.filter fun x ↦ G.Reach x c' := by
    rw [heq]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, G.reach_refl c⟩
  exact G.reach_antisymm hreach (Finset.mem_filter.1 hc_mem).2

/-- **Key graphical theorem:** in any finite DAG, $*$-separation implies footprint separation. -/
theorem isStarSeparated_imp_isFootprintSeparated [Fintype V] {A B C : Set V}
    (hstar : G.IsStarSeparated A B C) : G.IsFootprintSeparated A B C := by
  classical
  constructor
  · -- Condition (G1): no `k` with empty `C`-footprint can reach both `A` and `B`.
    rintro k hk ⟨⟨a, ha, hka⟩, ⟨b, hb, hkb⟩⟩
    obtain ⟨pA, hpA, hAh, hAl⟩ := G.reach_iff_exists_dirWalk.1 hka
    obtain ⟨pB, hpB, hBh, hBl⟩ := G.reach_iff_exists_dirWalk.1 hkb
    have hAC : ∀ x ∈ pA, x ∉ C := by
      intro x hx hxC
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have h0 := getElem_zero_of_head? hpA.1 hAh
      have hkx : G.Reach k pA[i] := by simpa [h0] using G.reach_of_isDirWalk_get hpA (Nat.zero_le i) hi
      have hmem : pA[i] ∈ G.footprint C k := ⟨hxC, hkx⟩
      rw [hk] at hmem; exact hmem
    have hBC : ∀ x ∈ pB, x ∉ C := by
      intro x hx hxC
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have h0 := getElem_zero_of_head? hpB.1 hBh
      have hkx : G.Reach k pB[i] := by simpa [h0] using G.reach_of_isDirWalk_get hpB (Nat.zero_le i) hi
      have hmem : pB[i] ∈ G.footprint C k := ⟨hxC, hkx⟩
      rw [hk] at hmem; exact hmem
    obtain ⟨p, hph, hpl, hpstar⟩ :=
      G.exists_zeroCollider_starConnecting pA pB hpA hpB hAh hAl hBh hBl hAC hBC
    exact hstar p a ha b hb hph hpl hpstar
  · -- Condition (G2): for any non-empty `S`, not both a `C`-avoiding path to `A` and to `B`.
    rintro S hS _ ⟨⟨k₁, hk₁, a, ha, ⟨pA, hpA, hAh, hAl, hAC⟩⟩,
      ⟨k₂, hk₂, b, hb, ⟨pB, hpB, hBh, hBl, hBC⟩⟩⟩
    obtain ⟨cmin, hcminS, hcmin_min⟩ := G.exists_minimal_reach hS
    have hcminC : cmin ∈ C := (hk₁.symm ▸ hcminS).1
    have hk1_c : G.Reach k₁ cmin := (hk₁.symm ▸ hcminS).2
    have hk2_c : G.Reach k₂ cmin := (hk₂.symm ▸ hcminS).2
    obtain ⟨q1, hq1, hq1h, hq1l⟩ := G.reach_iff_exists_dirWalk.1 hk1_c
    obtain ⟨q2, hq2, hq2h, hq2l⟩ := G.reach_iff_exists_dirWalk.1 hk2_c
    have hq1_C : ∀ x ∈ q1, x ≠ cmin → x ∉ C := by
      intro x hx hne hxC
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have h0 := getElem_zero_of_head? hq1.1 hq1h
      have hlast := getElem_last_of_getLast? hq1.1 hq1l
      have hk1x : G.Reach k₁ q1[i] := by simpa [h0] using G.reach_of_isDirWalk_get hq1 (Nat.zero_le i) hi
      have hxc : G.Reach q1[i] cmin := by
        simpa [hlast] using G.reach_of_isDirWalk_get hq1 (Nat.le_sub_one_of_lt hi)
          (Nat.sub_lt (List.length_pos_iff.2 hq1.1) Nat.one_pos)
      have hxS : q1[i] ∈ S := hk₁ ▸ ⟨hxC, hk1x⟩
      exact hne (hcmin_min _ hxS hxc)
    have hq2_C : ∀ x ∈ q2, x ≠ cmin → x ∉ C := by
      intro x hx hne hxC
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have h0 := getElem_zero_of_head? hq2.1 hq2h
      have hlast := getElem_last_of_getLast? hq2.1 hq2l
      have hk2x : G.Reach k₂ q2[i] := by simpa [h0] using G.reach_of_isDirWalk_get hq2 (Nat.zero_le i) hi
      have hxc : G.Reach q2[i] cmin := by
        simpa [hlast] using G.reach_of_isDirWalk_get hq2 (Nat.le_sub_one_of_lt hi)
          (Nat.sub_lt (List.length_pos_iff.2 hq2.1) Nat.one_pos)
      have hxS : q2[i] ∈ S := hk₂ ▸ ⟨hxC, hk2x⟩
      exact hne (hcmin_min _ hxS hxc)
    -- Case 1: `pA` and `pB` intersect.
    by_cases hAB : ∃ x ∈ pA, x ∈ pB
    · rcases hAB with ⟨x, hxA, hxB⟩
      obtain ⟨iA, hiA, rfl⟩ := List.getElem_of_mem hxA
      obtain ⟨iB, hiB, hEq⟩ := List.getElem_of_mem hxB
      have hdA := G.isDirWalk_drop hpA hiA
      have hdB := G.isDirWalk_drop hpB hiB
      obtain ⟨p, hph, hpl, hpstar⟩ := G.exists_zeroCollider_starConnecting
        (pA.drop iA) (pB.drop iB) hdA.1 hdB.1 hdA.2.1 (hdA.2.2.trans hAl)
        (hdB.2.1.trans (congrArg some hEq)) (hdB.2.2.trans hBl)
        (fun y hy ↦ hAC y (List.mem_of_mem_drop hy))
        (fun y hy ↦ hBC y (List.mem_of_mem_drop hy))
      exact hstar p a ha b hb hph hpl hpstar
    push Not at hAB
    -- Case 2: `q1` intersects `pB`.
    by_cases hQ1B : ∃ x ∈ q1, x ∈ pB
    · rcases hQ1B with ⟨x, hxq1, hxB⟩
      obtain ⟨i1, hi1, rfl⟩ := List.getElem_of_mem hxq1
      obtain ⟨iB, hiB, hEq⟩ := List.getElem_of_mem hxB
      have ht1 := G.isDirWalk_take hq1 hi1
      have hdB := G.isDirWalk_drop hpB hiB
      have hcat := G.isDirWalk_append_tail ht1.1 hdB.1 ht1.2.2
        (hdB.2.1.trans (congrArg some hEq))
      have hcat_C : ∀ y ∈ q1.take (i1 + 1) ++ (pB.drop iB).tail, y ∉ C := by
        intro y hy
        rcases List.mem_append.1 hy with hy1 | hy2
        · have hyq1 : y ∈ q1 := List.mem_of_mem_take hy1
          apply hq1_C y hyq1
          intro hyeq
          obtain ⟨m, hm, hym⟩ := List.getElem_of_mem hy1
          have hlen_t : (q1.take (i1 + 1)).length = i1 + 1 := List.length_take_of_le (Nat.succ_le_of_lt hi1)
          have hmi1 : m ≤ i1 := by omega
          have hq1_m : q1[m]'(by omega) = cmin := by rw [← hyeq, ← hym]; exact List.getElem_take.symm
          have hreach_cm : G.Reach cmin q1[i1] := by
            simpa [hq1_m] using G.reach_of_isDirWalk_get hq1 hmi1 hi1
          have hlast := getElem_last_of_getLast? hq1.1 hq1l
          have hreach_i1 : G.Reach q1[i1] cmin := by
            simpa [hlast] using G.reach_of_isDirWalk_get hq1 (Nat.le_sub_one_of_lt hi1)
              (Nat.sub_lt (List.length_pos_iff.2 hq1.1) Nat.one_pos)
          have heqc : q1[i1] = cmin := G.reach_antisymm hreach_i1 hreach_cm
          exact hBC cmin (heqc ▸ hxB) hcminC
        · exact hBC y (List.mem_of_mem_drop (List.mem_of_mem_tail hy2))
      obtain ⟨p, hph, hpl, hpstar⟩ := G.exists_zeroCollider_starConnecting
        pA (q1.take (i1 + 1) ++ (pB.drop iB).tail) hpA hcat.1 hAh hAl
        (hcat.2.1.trans (ht1.2.1.trans hq1h)) (hcat.2.2.trans (hdB.2.2.trans hBl)) hAC hcat_C
      exact hstar p a ha b hb hph hpl hpstar
    push Not at hQ1B
    -- Case 3: `q2` intersects `pA`.
    by_cases hQ2A : ∃ x ∈ q2, x ∈ pA
    · rcases hQ2A with ⟨x, hxq2, hxA⟩
      obtain ⟨i2, hi2, rfl⟩ := List.getElem_of_mem hxq2
      obtain ⟨iA, hiA, hEq⟩ := List.getElem_of_mem hxA
      have ht2 := G.isDirWalk_take hq2 hi2
      have hdA := G.isDirWalk_drop hpA hiA
      have hcat := G.isDirWalk_append_tail ht2.1 hdA.1 ht2.2.2
        (hdA.2.1.trans (congrArg some hEq))
      have hcat_C : ∀ y ∈ q2.take (i2 + 1) ++ (pA.drop iA).tail, y ∉ C := by
        intro y hy
        rcases List.mem_append.1 hy with hy1 | hy2
        · have hyq2 : y ∈ q2 := List.mem_of_mem_take hy1
          apply hq2_C y hyq2
          intro hyeq
          obtain ⟨m, hm, hym⟩ := List.getElem_of_mem hy1
          have hlen_t : (q2.take (i2 + 1)).length = i2 + 1 := List.length_take_of_le (Nat.succ_le_of_lt hi2)
          have hmi2 : m ≤ i2 := by omega
          have hq2_m : q2[m]'(by omega) = cmin := by rw [← hyeq, ← hym]; exact List.getElem_take.symm
          have hreach_cm : G.Reach cmin q2[i2] := by
            simpa [hq2_m] using G.reach_of_isDirWalk_get hq2 hmi2 hi2
          have hlast := getElem_last_of_getLast? hq2.1 hq2l
          have hreach_i2 : G.Reach q2[i2] cmin := by
            simpa [hlast] using G.reach_of_isDirWalk_get hq2 (Nat.le_sub_one_of_lt hi2)
              (Nat.sub_lt (List.length_pos_iff.2 hq2.1) Nat.one_pos)
          have heqc : q2[i2] = cmin := G.reach_antisymm hreach_i2 hreach_cm
          exact hAC cmin (heqc ▸ hxA) hcminC
        · exact hAC y (List.mem_of_mem_drop (List.mem_of_mem_tail hy2))
      obtain ⟨p, hph, hpl, hpstar⟩ := G.exists_zeroCollider_starConnecting
        (q2.take (i2 + 1) ++ (pA.drop iA).tail) pB hcat.1 hpB
        (hcat.2.1.trans (ht2.2.1.trans hq2h)) (hcat.2.2.trans (hdA.2.2.trans hAl)) hBh hBl hcat_C hBC
      exact hstar p a ha b hb hph hpl hpstar
    push Not at hQ2A
    -- Case 4: `pA ∩ pB = ∅`, `q1 ∩ pB = ∅`, `q2 ∩ pA = ∅`. Build the 1-collider path!
    have hS1_ne : (Finset.univ.filter fun i : Fin q1.length ↦ q1[i.1] ∈ pA).Nonempty := by
      have hlen : 0 < q1.length := List.length_pos_iff.2 hq1.1
      refine ⟨⟨0, hlen⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      change q1[0] ∈ pA
      rw [getElem_zero_of_head? hq1.1 hq1h, ← getElem_zero_of_head? hpA.1 hAh]
      exact List.getElem_mem _
    let i1 : Fin q1.length := (Finset.univ.filter fun i : Fin q1.length ↦ q1[i.1] ∈ pA).max' hS1_ne
    have hi1_mem : q1[i1.1] ∈ pA := (Finset.mem_filter.1 (Finset.max'_mem _ hS1_ne)).2
    have hi1_max : ∀ i : Fin q1.length, q1[i.1] ∈ pA → i ≤ i1 :=
      fun i hi ↦ Finset.le_max' _ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    obtain ⟨jA, hjA, hEqA⟩ := List.getElem_of_mem hi1_mem
    have hS2_ne : (Finset.univ.filter fun i : Fin q2.length ↦ q2[i.1] ∈ pB).Nonempty := by
      have hlen : 0 < q2.length := List.length_pos_iff.2 hq2.1
      refine ⟨⟨0, hlen⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      change q2[0] ∈ pB
      rw [getElem_zero_of_head? hq2.1 hq2h, ← getElem_zero_of_head? hpB.1 hBh]
      exact List.getElem_mem _
    let i2 : Fin q2.length := (Finset.univ.filter fun i : Fin q2.length ↦ q2[i.1] ∈ pB).max' hS2_ne
    have hi2_mem : q2[i2.1] ∈ pB := (Finset.mem_filter.1 (Finset.max'_mem _ hS2_ne)).2
    have hi2_max : ∀ i : Fin q2.length, q2[i.1] ∈ pB → i ≤ i2 :=
      fun i hi ↦ Finset.le_max' _ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    obtain ⟨jB, hjB, hEqB⟩ := List.getElem_of_mem hi2_mem
    let q1' := q1.drop i1.1
    let q2' := q2.drop i2.1
    have hq1'_len_eq : q1'.length = q1.length - i1.1 := List.length_drop
    have hq2'_len_eq : q2'.length = q2.length - i2.1 := List.length_drop
    have hq1' := G.isDirWalk_drop hq1 i1.2
    have hq2' := G.isDirWalk_drop hq2 i2.2
    have hq1'_walk : G.IsDirWalk q1' := hq1'.1
    have hq2'_walk : G.IsDirWalk q2' := hq2'.1
    have hq1'_last : q1'.getLast? = some cmin := hq1'.2.2.trans hq1l
    have hq2'_last : q2'.getLast? = some cmin := hq2'.2.2.trans hq2l
    have hW_ne : (Finset.univ.filter fun m : Fin q1'.length ↦ q1'[m.1] ∈ q2').Nonempty := by
      have hlen1' : 0 < q1'.length := List.length_pos_iff.2 hq1'_walk.1
      refine ⟨⟨q1'.length - 1, Nat.sub_lt hlen1' Nat.one_pos⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      change q1'[q1'.length - 1] ∈ q2'
      rw [getElem_last_of_getLast? hq1'_walk.1 hq1'_last,
        ← getElem_last_of_getLast? hq2'_walk.1 hq2'_last]
      exact List.getElem_mem _
    let m1 : Fin q1'.length := (Finset.univ.filter fun m : Fin q1'.length ↦ q1'[m.1] ∈ q2').min' hW_ne
    have hm1_mem : q1'[m1.1] ∈ q2' := (Finset.mem_filter.1 (Finset.min'_mem _ hW_ne)).2
    have hm1_min : ∀ m : Fin q1'.length, q1'[m.1] ∈ q2' → m1 ≤ m :=
      fun m hm ↦ Finset.min'_le _ m (Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩)
    obtain ⟨m2, hm2, hEqW⟩ := List.getElem_of_mem hm1_mem
    let r1 := pA.drop jA
    let r2 := q1'.take (m1.1 + 1)
    let r3 := q2'.take (m2 + 1)
    let r4 := pB.drop jB
    have hr2_len_eq : r2.length = m1.1 + 1 := List.length_take_of_le (Nat.succ_le_of_lt m1.2)
    have hr3_len_eq : r3.length = m2 + 1 := List.length_take_of_le (Nat.succ_le_of_lt hm2)
    have hr1 := G.isDirWalk_drop hpA hjA
    have hr2 := G.isDirWalk_take hq1'_walk m1.2
    have hr3 := G.isDirWalk_take hq2'_walk hm2
    have hr4 := G.isDirWalk_drop hpB hjB
    let u₁ := q1[i1.1]
    let u₂ := q2[i2.1]
    let w := q1'[m1.1]
    have hw_in_q1 : w ∈ q1 := List.mem_of_mem_drop (List.getElem_mem m1.2)
    have hw_in_q2 : w ∈ q2 := List.mem_of_mem_drop hm1_mem
    have hw1 : u₁ ≠ w := fun h ↦ hQ2A w hw_in_q2 (h ▸ hi1_mem)
    have hw2 : u₂ ≠ w := fun h ↦ hQ1B w hw_in_q1 (h ▸ hi2_mem)
    have hwC : ∃ c ∈ C, G.Reach w c := by
      refine ⟨cmin, hcminC, ?_⟩
      have hlen1' : 0 < q1'.length := List.length_pos_iff.2 hq1'_walk.1
      have hl1 := getElem_last_of_getLast? hq1'_walk.1 hq1'_last
      have hreach := G.reach_of_isDirWalk_get hq1'_walk (Nat.le_sub_one_of_lt m1.2)
        (Nat.sub_lt hlen1' Nat.one_pos)
      rwa [hl1] at hreach
    have h12 : ∀ x ∈ r1, x ∈ r2 → x = u₁ := by
      intro x hx1 hx2
      have hx_pA : x ∈ pA := List.mem_of_mem_drop hx1
      have hx_q1' : x ∈ q1' := List.mem_of_mem_take hx2
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx_q1'
      have hidx : i1.1 + t < q1.length := by omega
      have hEq1 : q1[i1.1 + t] = q1'[t] := by simp [q1']
      have hle : (⟨i1.1 + t, hidx⟩ : Fin q1.length) ≤ i1 := hi1_max _ (hEq1.symm ▸ hx_pA)
      have ht0 : t = 0 := by have : i1.1 + t ≤ i1.1 := hle; omega
      subst ht0; simpa [u₁] using hEq1.symm
    have h34 : ∀ x ∈ r3, x ∈ r4 → x = u₂ := by
      intro x hx3 hx4
      have hx_pB : x ∈ pB := List.mem_of_mem_drop hx4
      have hx_q2' : x ∈ q2' := List.mem_of_mem_take hx3
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx_q2'
      have hidx : i2.1 + t < q2.length := by omega
      have hEq2 : q2[i2.1 + t] = q2'[t] := by simp [q2']
      have hle : (⟨i2.1 + t, hidx⟩ : Fin q2.length) ≤ i2 := hi2_max _ (hEq2.symm ▸ hx_pB)
      have ht0 : t = 0 := by have : i2.1 + t ≤ i2.1 := hle; omega
      subst ht0; simpa [u₂] using hEq2.symm
    have h23 : ∀ x ∈ r2, x ∈ r3 → x = w := by
      intro x hx2 hx3
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx2
      have ht_le : t ≤ m1.1 := by omega
      have ht_lt : t < q1'.length := Nat.lt_of_le_of_lt ht_le m1.2
      have heq_t : r2[t] = q1'[t] := List.getElem_take
      have hge : m1 ≤ ⟨t, ht_lt⟩ := hm1_min ⟨t, ht_lt⟩ (heq_t ▸ List.mem_of_mem_take hx3)
      have hteq : t = m1.1 := le_antisymm ht_le hge
      rw [heq_t]; simp [w, hteq]
    have h2C : ∀ x ∈ r2, x ≠ w → x ∉ C := by
      intro x hx2 hne
      apply hq1_C x (List.mem_of_mem_drop (List.mem_of_mem_take hx2))
      intro hxc
      obtain ⟨t, ht, hxt⟩ := List.getElem_of_mem hx2
      have ht_le : t ≤ m1.1 := by omega
      have hqt : q1'[t]'(by omega) = cmin := by rw [← hxc, ← hxt]; exact List.getElem_take.symm
      have hrcw : G.Reach cmin w := by
        have h := G.reach_of_isDirWalk_get hq1'_walk ht_le m1.2
        rwa [hqt] at h
      have hlen1' : 0 < q1'.length := List.length_pos_iff.2 hq1'_walk.1
      have hl1 := getElem_last_of_getLast? hq1'_walk.1 hq1'_last
      have hrwc : G.Reach w cmin := by
        have h := G.reach_of_isDirWalk_get hq1'_walk (Nat.le_sub_one_of_lt m1.2)
          (Nat.sub_lt hlen1' Nat.one_pos)
        rwa [hl1] at h
      exact hne (hxc.trans (G.reach_antisymm hrcw hrwc))
    have h3C : ∀ x ∈ r3, x ≠ w → x ∉ C := by
      intro x hx3 hne
      apply hq2_C x (List.mem_of_mem_drop (List.mem_of_mem_take hx3))
      intro hxc
      obtain ⟨t, ht, hxt⟩ := List.getElem_of_mem hx3
      have ht_le : t ≤ m2 := by omega
      have hqt : q2'[t]'(by omega) = cmin := by rw [← hxc, ← hxt]; exact List.getElem_take.symm
      have hrcw : G.Reach cmin w := by
        have h := G.reach_of_isDirWalk_get hq2'_walk ht_le hm2
        rwa [hqt, hEqW] at h
      have hlen2' : 0 < q2'.length := List.length_pos_iff.2 hq2'_walk.1
      have hl2 := getElem_last_of_getLast? hq2'_walk.1 hq2'_last
      have hrwc : G.Reach w cmin := by
        have h := G.reach_of_isDirWalk_get hq2'_walk (Nat.le_sub_one_of_lt hm2)
          (Nat.sub_lt hlen2' Nat.one_pos)
        rwa [hEqW, hl2] at h
      exact hne (hxc.trans (G.reach_antisymm hrcw hrwc))
    obtain ⟨p, hph, hpl, hpstar⟩ := G.exists_oneCollider_starConnecting r1 r2 r3 r4
      hr1.1 hr2.1 hr3.1 hr4.1
      (hr1.2.1.trans (congrArg some hEqA)) (hr1.2.2.trans hAl)
      (hr2.2.1.trans hq1'.2.1) hr2.2.2
      (hr3.2.1.trans hq2'.2.1) (hr3.2.2.trans (congrArg some hEqW))
      (hr4.2.1.trans (congrArg some hEqB)) (hr4.2.2.trans hBl)
      hw1 hw2 h12 h34 h23
      (fun x hx1 hx4 ↦ hAB x (List.mem_of_mem_drop hx1) (List.mem_of_mem_drop hx4))
      (fun x hx1 hx3 ↦ hQ2A x (List.mem_of_mem_drop (List.mem_of_mem_take hx3)) (List.mem_of_mem_drop hx1))
      (fun x hx2 hx4 ↦ hQ1B x (List.mem_of_mem_drop (List.mem_of_mem_take hx2)) (List.mem_of_mem_drop hx4))
      (fun x hx1 ↦ hAC x (List.mem_of_mem_drop hx1))
      (fun x hx4 ↦ hBC x (List.mem_of_mem_drop hx4))
      h2C h3C hwC
    exact hstar p a ha b hb hph hpl hpstar

end DAG

/-! ### Recursive max-linear models and tropical Kleene star -/

/-- A **recursive max-linear model** on a finite DAG `G` with positive edge weights `weight i j`
for edges `j → i` (zero otherwise) and positive innovation scales `diag k`.
In tropical structural equations, `X i = max (diag i * Z i) (max_{j → i} weight i j * X j)`. -/
structure MaxLinearModel {V : Type*} (G : DAG V) where
  /-- Edge weight `c_{ij}` for directed edge `j → i`. -/
  weight : V → V → ℝ
  /-- Innovation scale `c_{kk} > 0` for the independent unit Fréchet shock `Z_k`. -/
  diag : V → ℝ
  weight_nonneg : ∀ i j, 0 ≤ weight i j
  weight_pos_iff : ∀ i j, 0 < weight i j ↔ G.edge j i
  diag_pos : ∀ k, 0 < diag k

namespace MaxLinearModel

variable {V : Type*} [Fintype V] [DecidableEq V] {G : DAG V} (M : MaxLinearModel G)

/-- Product of edge weights along a directed walk `p` (equals `1` for a length-1 walk `[k]`). -/
def walkWeight : List V → ℝ
  | [] => 0
  | [_] => 1
  | u :: v :: t => M.weight v u * walkWeight (v :: t)

omit [Fintype V] [DecidableEq V] in
lemma walkWeight_pos {p : List V} (hp : G.IsDirWalk p) : 0 < M.walkWeight p := by
  match p with
  | [] => exact (hp.1 rfl).elim
  | [_] => simp [walkWeight]
  | u :: v :: t =>
    have huv : G.edge u v := (List.isChain_cons_cons.1 hp.2).1
    have ht : G.IsDirWalk (v :: t) := ⟨List.cons_ne_nil _ _, (List.isChain_cons_cons.1 hp.2).2⟩
    exact mul_pos ((M.weight_pos_iff v u).2 huv) (walkWeight_pos ht)

omit [Fintype V] [DecidableEq V] in
lemma walkWeight_append_tail {p q : List V} {w : V}
    (hp : G.IsDirWalk p) (hq : G.IsDirWalk q)
    (hpl : p.getLast? = some w) (hqh : q.head? = some w) :
    M.walkWeight (p ++ q.tail) = M.walkWeight p * M.walkWeight q := by
  match p with
  | [] => exact (hp.1 rfl).elim
  | [x] =>
    simp only [List.getLast?_singleton, Option.some.injEq] at hpl
    subst hpl
    cases q with
    | nil => exact (hq.1 rfl).elim
    | cons y ys =>
      simp only [List.head?_cons, Option.some.injEq] at hqh
      subst hqh
      simp [walkWeight]
  | u :: v :: t =>
    have ht : G.IsDirWalk (v :: t) := ⟨List.cons_ne_nil _ _, (List.isChain_cons_cons.1 hp.2).2⟩
    have htl : (v :: t).getLast? = some w := by simpa using hpl
    have ih := walkWeight_append_tail ht hq htl hqh
    change M.weight v u * M.walkWeight ((v :: t) ++ q.tail) =
      (M.weight v u * M.walkWeight (v :: t)) * M.walkWeight q
    rw [ih, mul_assoc]

/-- Bounded-length tropical Kleene star: maximum walk weight over all directed walks `k →* i` of
at most `n` edges. -/
noncomputable def kleeneAux : ℕ → V → V → ℝ
  | 0, i, k => if i = k then 1 else 0
  | n + 1, i, k =>
    max (kleeneAux n i k)
      (if h : (Finset.univ : Finset V).Nonempty then
        Finset.univ.sup' h fun j ↦ M.weight i j * kleeneAux n j k
       else 0)

/-- The **tropical Kleene star** `P_{i, k}` of `M` (maximum weight over all directed paths
`k →* i`, with `P_{k, k} = 1` and `P_{i, k} = 0` when `¬ G.Reach k i`). -/
noncomputable def kleenePath (i k : V) : ℝ := M.kleeneAux (Fintype.card V) i k

/-- The **max-linear coefficient matrix** `B_{i, k} = P_{i, k} * diag k`. -/
noncomputable def coeff (i k : V) : ℝ := M.kleenePath i k * M.diag k

lemma kleeneAux_nonneg (n : ℕ) (i k : V) : 0 ≤ M.kleeneAux n i k := by
  induction n generalizing i with
  | zero => simp only [kleeneAux]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [kleeneAux]
    exact le_trans (ih i) (le_max_left _ _)

lemma kleeneAux_mono {m n : ℕ} (hmn : m ≤ n) (i k : V) :
    M.kleeneAux m i k ≤ M.kleeneAux n i k := by
  induction hmn with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (le_max_left _ _)

lemma kleeneAux_step_le (n : ℕ) (i j k : V) :
    M.weight i j * M.kleeneAux n j k ≤ M.kleeneAux (n + 1) i k := by
  have hne : (Finset.univ : Finset V).Nonempty := ⟨j, Finset.mem_univ j⟩
  have hdef : M.kleeneAux (n + 1) i k =
      max (M.kleeneAux n i k) (Finset.univ.sup' hne fun j' ↦ M.weight i j' * M.kleeneAux n j' k) := by
    simp [kleeneAux, hne]
  rw [hdef]
  exact le_trans (Finset.le_sup' (fun j' ↦ M.weight i j' * M.kleeneAux n j' k) (Finset.mem_univ j))
    (le_max_right _ _)

/-- Every directed walk `p : k →* i` of length `≤ n + 1` has `walkWeight p ≤ kleeneAux n i k`. -/
lemma walkWeight_le_kleeneAux {n : ℕ} {p : List V} {i k : V}
    (hp : G.IsDirWalk p) (hph : p.head? = some k) (hpl : p.getLast? = some i)
    (hlen : p.length ≤ n + 1) :
    M.walkWeight p ≤ M.kleeneAux n i k := by
  induction n generalizing p i with
  | zero =>
    match p with
    | [] => exact (hp.1 rfl).elim
    | [x] =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hph hpl
      subst hph; subst hpl; simp [walkWeight, kleeneAux]
    | _ :: _ :: _ => simp at hlen
  | succ n ih =>
    match p with
    | [] => exact (hp.1 rfl).elim
    | [x] =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hph hpl
      subst hph; subst hpl
      exact le_trans (by simp [walkWeight, kleeneAux]) (M.kleeneAux_mono (Nat.zero_le _) _ _)
    | u :: v :: t =>
      have hidx : (u :: v :: t).length - 2 < (u :: v :: t).length := by simp; omega
      have hpref := G.isDirWalk_take hp hidx
      let pref := (u :: v :: t).take ((u :: v :: t).length - 2 + 1)
      have hpref_len : pref.length = (u :: v :: t).length - 1 := by
        have hle : (u :: v :: t).length - 2 + 1 ≤ (u :: v :: t).length := by simp
        rw [List.length_take_of_le hle]; simp
      let j := (u :: v :: t)[(u :: v :: t).length - 2]
      have hji : G.edge j i := by
        have hstep := List.isChain_iff_getElem.1 hp.2 ((u :: v :: t).length - 2) (by simp)
        have hl := DAG.getElem_last_of_getLast? hp.1 hpl
        have hk : (u :: v :: t).length - 2 + 1 = (u :: v :: t).length - 1 := by simp
        have h1 : (u :: v :: t)[(u :: v :: t).length - 2 + 1]'(by simp) = i := by
          simpa [hk] using hl
        rwa [h1] at hstep
      have hcat_eq : pref ++ [j, i].tail = u :: v :: t := by
        simp only [List.tail_cons]
        have htake_eq : pref = (u :: v :: t).dropLast := by
          simp only [pref, List.dropLast_eq_take]; congr 1
        have hlast_eq : (u :: v :: t).getLast hp.1 = i := by
          rw [List.getLast?_eq_some_getLast hp.1] at hpl
          exact Option.some.inj hpl
        rw [htake_eq, ← hlast_eq]
        exact List.dropLast_append_getLast hp.1
      have hji_walk : G.IsDirWalk [j, i] :=
        G.isDirWalk_cons hji (G.isDirWalk_singleton i)
      have hw_split : M.walkWeight (u :: v :: t) = M.weight i j * M.walkWeight pref := by
        have h := M.walkWeight_append_tail hpref.1 hji_walk hpref.2.2 rfl
        rw [hcat_eq] at h
        rw [h]
        change M.walkWeight pref * (M.weight i j * 1) = M.weight i j * M.walkWeight pref
        ring
      rw [hw_split]
      have hih : M.walkWeight pref ≤ M.kleeneAux n j k :=
        ih hpref.1 (hpref.2.1.trans hph) hpref.2.2 (by omega)
      exact le_trans (mul_le_mul_of_nonneg_left hih (M.weight_nonneg i j)) (M.kleeneAux_step_le n i j k)

/-- If `kleeneAux n i k > 0`, then it is achieved by a directed walk `k →* i`. -/
lemma exists_dirWalk_of_kleeneAux_pos {n : ℕ} {i k : V} (hpos : 0 < M.kleeneAux n i k) :
    ∃ p : List V, G.IsDirWalk p ∧ p.head? = some k ∧ p.getLast? = some i ∧
      M.walkWeight p = M.kleeneAux n i k := by
  induction n generalizing i with
  | zero =>
    simp only [kleeneAux] at hpos ⊢
    split_ifs at hpos ⊢ with h
    · subst h; exact ⟨[i], G.isDirWalk_singleton i, rfl, rfl, rfl⟩
    · linarith
  | succ n ih =>
    have hne : (Finset.univ : Finset V).Nonempty := ⟨i, Finset.mem_univ i⟩
    have hdef : M.kleeneAux (n + 1) i k =
        max (M.kleeneAux n i k) (Finset.univ.sup' hne fun j ↦ M.weight i j * M.kleeneAux n j k) := by
      simp [kleeneAux, hne]
    rw [hdef] at hpos ⊢
    rcases le_total (M.kleeneAux n i k)
      (Finset.univ.sup' hne fun j ↦ M.weight i j * M.kleeneAux n j k) with hle | hle
    · rw [max_eq_right hle] at hpos ⊢
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne
        (fun j ↦ M.weight i j * M.kleeneAux n j k)
      rw [hj] at hpos ⊢
      have hwj : 0 < M.weight i j := by
        by_contra h
        have h0 : M.weight i j = 0 := le_antisymm (not_lt.1 h) (M.weight_nonneg i j)
        rw [h0, zero_mul] at hpos; linarith
      have hkj : 0 < M.kleeneAux n j k := by
        by_contra h
        have h0 : M.kleeneAux n j k = 0 := le_antisymm (not_lt.1 h) (M.kleeneAux_nonneg n j k)
        rw [h0, mul_zero] at hpos; linarith
      obtain ⟨p, hp, hph, hpl, hpw⟩ := ih hkj
      have hji : G.edge j i := (M.weight_pos_iff i j).1 hwj
      have hji_walk : G.IsDirWalk [j, i] := G.isDirWalk_cons hji (G.isDirWalk_singleton i)
      have hcat := G.isDirWalk_append_tail hp hji_walk hpl rfl
      refine ⟨p ++ [j, i].tail, hcat.1, hcat.2.1.trans hph, hcat.2.2, ?_⟩
      rw [M.walkWeight_append_tail hp hji_walk hpl rfl, hpw]
      change M.kleeneAux n j k * (M.weight i j * 1) = M.weight i j * M.kleeneAux n j k
      ring
    · rw [max_eq_left hle] at hpos ⊢
      exact ih hpos

lemma walkWeight_le_kleenePath {p : List V} {i k : V}
    (hp : G.IsDirWalk p) (hph : p.head? = some k) (hpl : p.getLast? = some i) :
    M.walkWeight p ≤ M.kleenePath i k := by
  have hlen : p.length ≤ Fintype.card V := (G.isDirWalk_nodup hp).length_le_card
  exact M.walkWeight_le_kleeneAux hp hph hpl (Nat.le_succ_of_le hlen)

lemma kleenePath_nonneg (i k : V) : 0 ≤ M.kleenePath i k :=
  M.kleeneAux_nonneg _ i k

lemma kleenePath_pos_iff (i k : V) : 0 < M.kleenePath i k ↔ G.Reach k i := by
  constructor
  · intro hpos
    obtain ⟨p, hp, hph, hpl, _⟩ := M.exists_dirWalk_of_kleeneAux_pos hpos
    exact G.reach_iff_exists_dirWalk.2 ⟨p, hp, hph, hpl⟩
  · intro hreach
    obtain ⟨p, hp, hph, hpl⟩ := G.reach_iff_exists_dirWalk.1 hreach
    exact lt_of_lt_of_le (M.walkWeight_pos hp) (M.walkWeight_le_kleenePath hp hph hpl)

lemma coeff_nonneg (i k : V) : 0 ≤ M.coeff i k :=
  mul_nonneg (M.kleenePath_nonneg i k) (M.diag_pos k).le

lemma coeff_pos_iff (i k : V) : 0 < M.coeff i k ↔ G.Reach k i := by
  rw [coeff, mul_pos_iff_of_pos_right (M.diag_pos k), M.kleenePath_pos_iff]

lemma kleenePath_mul_le (i c k : V) :
    M.kleenePath i c * M.kleenePath c k ≤ M.kleenePath i k := by
  by_cases h1 : 0 < M.kleenePath i c
  · by_cases h2 : 0 < M.kleenePath c k
    · obtain ⟨p2, hp2, h2h, h2l, hw2⟩ := M.exists_dirWalk_of_kleeneAux_pos h2
      obtain ⟨p1, hp1, h1h, h1l, hw1⟩ := M.exists_dirWalk_of_kleeneAux_pos h1
      have hcat := G.isDirWalk_append_tail hp2 hp1 h2l h1h
      have hle := M.walkWeight_le_kleenePath hcat.1 (hcat.2.1.trans h2h) (hcat.2.2.trans h1l)
      rw [M.walkWeight_append_tail hp2 hp1 h2l h1h, hw1, hw2, mul_comm] at hle
      exact hle
    · have h0 : M.kleenePath c k = 0 := le_antisymm (not_lt.1 h2) (M.kleenePath_nonneg c k)
      rw [h0, mul_zero]; exact M.kleenePath_nonneg i k
  · have h0 : M.kleenePath i c = 0 := le_antisymm (not_lt.1 h1) (M.kleenePath_nonneg i c)
    rw [h0, zero_mul]; exact M.kleenePath_nonneg i k

/-- **Tropical bottleneck factorization:** if `k` has no `C`-avoiding directed path to `a`, then
`P_{a, k} = max_{c ∈ S} (P_{a, c} * P_{c, k})` where `S = G.footprint C k`. -/
lemma kleenePath_eq_sup'_of_not_avoidReach {C : Set V} {a k : V}
    (hno : ¬ G.AvoidReach C k a)
    {Sf : Finset V} (hSf : ∀ c, c ∈ Sf ↔ c ∈ G.footprint C k) (hne : Sf.Nonempty) :
    M.kleenePath a k = Sf.sup' hne fun c ↦ M.kleenePath a c * M.kleenePath c k := by
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun c _ ↦ M.kleenePath_mul_le a c k)
  by_cases hpos : 0 < M.kleenePath a k
  · obtain ⟨p, hp, hph, hpl, hpw⟩ := M.exists_dirWalk_of_kleeneAux_pos hpos
    have hex : ∃ c ∈ p, c ∈ C := by
      by_contra h; push Not at h; exact hno ⟨p, hp, hph, hpl, h⟩
    obtain ⟨c, hcp, hcC⟩ := hex
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcp
    have ht := G.isDirWalk_take hp hm
    have hd := G.isDirWalk_drop hp hm
    have hreach_kc : G.Reach k p[m] :=
      G.reach_iff_exists_dirWalk.2 ⟨p.take (m + 1), ht.1, ht.2.1.trans hph, ht.2.2⟩
    have hcSf : p[m] ∈ Sf := (hSf _).2 ⟨hcC, hreach_kc⟩
    have hsplit : p.take (m + 1) ++ (p.drop m).tail = p := by
      have htake : p.take (m + 1) = p.take m ++ [p[m]] := List.take_succ_eq_append_getElem hm
      have hdrop : p.drop m = p[m] :: p.drop (m + 1) := List.drop_eq_getElem_cons hm
      rw [hdrop, List.tail_cons, htake, List.append_assoc, List.singleton_append, ← hdrop,
        List.take_append_drop]
    have hw_eq : M.walkWeight p = M.walkWeight (p.take (m + 1)) * M.walkWeight (p.drop m) := by
      have := M.walkWeight_append_tail ht.1 hd.1 ht.2.2 hd.2.1
      rwa [hsplit] at this
    have h1 : M.walkWeight (p.take (m + 1)) ≤ M.kleenePath p[m] k :=
      M.walkWeight_le_kleenePath ht.1 (ht.2.1.trans hph) ht.2.2
    have h2 : M.walkWeight (p.drop m) ≤ M.kleenePath a p[m] :=
      M.walkWeight_le_kleenePath hd.1 hd.2.1 (hd.2.2.trans hpl)
    calc M.kleenePath a k
        = M.walkWeight p := hpw.symm
      _ = M.walkWeight (p.drop m) * M.walkWeight (p.take (m + 1)) := by rw [hw_eq, mul_comm]
      _ ≤ M.kleenePath a p[m] * M.kleenePath p[m] k :=
          mul_le_mul h2 h1 (M.walkWeight_pos ht.1).le (M.kleenePath_nonneg a p[m])
      _ ≤ Sf.sup' hne fun c ↦ M.kleenePath a c * M.kleenePath c k :=
          Finset.le_sup' (fun c ↦ M.kleenePath a c * M.kleenePath c k) hcSf
  · have h0 : M.kleenePath a k = 0 := le_antisymm (not_lt.1 hpos) (M.kleenePath_nonneg a k)
    rw [h0]
    rcases hne with ⟨c, hc⟩
    exact le_trans (mul_nonneg (M.kleenePath_nonneg a c) (M.kleenePath_nonneg c k))
      (Finset.le_sup' (fun c ↦ M.kleenePath a c * M.kleenePath c k) hc)

end MaxLinearModel

/-! ### The exact ray criterion `RayCICondition` -/

/-- L1 norm of a ray vector `b` on a finite subset `C`. -/
def rayL1Norm {V : Type*} (b : V → ℝ) (C : Finset V) : ℝ :=
  ∑ c ∈ C, b c

/-- Normalized `C`-direction of a ray vector `b` (scaled by its L1 norm on `C`). -/
noncomputable def rayDir {V : Type*} (b : V → ℝ) (C : Finset V) (c : C) : ℝ :=
  b c / rayL1Norm b C

/-- Normalized `A`-coordinate vector of ray `k` scaled by its `C`-L1 norm. -/
noncomputable def rayScaled {V : Type*} (b : V → ℝ) (C A : Finset V) (a : A) : ℝ :=
  b a / rayL1Norm b C

/-- Total weight of rays with `C`-direction `v` matching predicate `P`. -/
noncomputable def rayDirMass {V κ : Type*} [Fintype κ]
    (b : κ → V → ℝ) (C : Finset V) (v : C → ℝ) (P : κ → Prop) : ℝ :=
  open Classical in
  ∑ k : κ, if 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ P k then rayL1Norm (b k) C else 0

lemma rayDirMass_congr {V κ : Type*} [Fintype κ]
    {b : κ → V → ℝ} {C : Finset V} {v : C → ℝ} {P Q : κ → Prop}
    (h : ∀ k : κ, 0 < rayL1Norm (b k) C → rayDir (b k) C = v → (P k ↔ Q k)) :
    rayDirMass b C v P = rayDirMass b C v Q := by
  unfold rayDirMass
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases h1 : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
  · by_cases hp : P k
    · have hq : Q k := (h k h1.1 h1.2).1 hp
      simp [h1.1, h1.2, hp, hq]
    · have hq : ¬ Q k := fun hq ↦ hp ((h k h1.1 h1.2).2 hq)
      simp [h1.1, h1.2, hp, hq]
  · have hP : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ P k) := fun ⟨a, b', _⟩ ↦ h1 ⟨a, b'⟩
    have hQ : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ Q k) := fun ⟨a, b', _⟩ ↦ h1 ⟨a, b'⟩
    simp [hP, hQ]

lemma rayDirMass_eq_zero {V κ : Type*} [Fintype κ]
    {b : κ → V → ℝ} {C : Finset V} {v : C → ℝ} {P : κ → Prop}
    (h : ∀ k : κ, 0 < rayL1Norm (b k) C → rayDir (b k) C = v → ¬ P k) :
    rayDirMass b C v P = 0 := by
  unfold rayDirMass
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hnot : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ P k) :=
    fun ⟨h1, h2, h3⟩ ↦ h k h1 h2 h3
  simp [hnot]

/-- **Exact algebraic ray criterion (`RayCICondition`):**
For a finite family of nonnegative ray vectors `b : κ → V → ℝ` and disjoint `A, B, C : Finset V`:
1. **(Condition I)** If `b k` vanishes on `C`, then `b k` vanishes on `A` or vanishes on `B`.
2. **(Condition II)** For every non-zero `C`-direction `v : C → ℝ`, the weighted discrete measure
   `ν_v = ∑_{k ∈ I_v} ‖b_k|_C‖₁ · δ_{(b_k|_A / ‖b_k|_C‖₁, b_k|_B / ‖b_k|_C‖₁)}`
   is a product measure on `(A → ℝ) × (B → ℝ)` (equivalently, its mass on every singleton `(x, y)`
   satisfies `ν_v{(x, y)} · ν_v(univ) = ν_v({x} × univ) · ν_v(univ × {y})`). -/
def RayCICondition {V κ : Type*} [Fintype κ]
    (b : κ → V → ℝ) (A B C : Finset V) : Prop :=
  (∀ k, (∀ c ∈ C, b k c = 0) → (∀ a ∈ A, b k a = 0) ∨ (∀ x ∈ B, b k x = 0)) ∧
  (∀ v : C → ℝ, ∀ x : A → ℝ, ∀ y : B → ℝ,
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y) *
      rayDirMass b C v (fun _ ↦ True) =
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x) *
      rayDirMass b C v (fun k ↦ rayScaled (b k) C B = y))

/-- Sufficiency helper for Condition (II): if `rayScaled (b k) C A` is constant across `Iv`,
then Condition (II) holds at `v`. -/
lemma rayCICondition_part2_of_const_left {V κ : Type*} [Fintype κ]
    {b : κ → V → ℝ} {A B C : Finset V} {v : C → ℝ} {x₀ : A → ℝ}
    (hconst : ∀ k : κ, 0 < rayL1Norm (b k) C → rayDir (b k) C = v → rayScaled (b k) C A = x₀)
    (x : A → ℝ) (y : B → ℝ) :
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y) *
      rayDirMass b C v (fun _ ↦ True) =
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x) *
      rayDirMass b C v (fun k ↦ rayScaled (b k) C B = y) := by
  by_cases hx : x₀ = x
  · subst hx
    rw [rayDirMass_congr (fun k h1 h2 ↦ ⟨fun _ ↦ trivial, fun _ ↦ hconst k h1 h2⟩),
      rayDirMass_congr (fun k h1 h2 ↦ ⟨fun ⟨_, hy⟩ ↦ hy, fun hy ↦ ⟨hconst k h1 h2, hy⟩⟩),
      mul_comm]
  · rw [rayDirMass_eq_zero (fun k h1 h2 h3 ↦ hx ((hconst k h1 h2).symm.trans h3)),
      rayDirMass_eq_zero (fun k h1 h2 ⟨h3, _⟩ ↦ hx ((hconst k h1 h2).symm.trans h3)),
      zero_mul, zero_mul]

lemma rayCICondition_part2_of_const_right {V κ : Type*} [Fintype κ]
    {b : κ → V → ℝ} {A B C : Finset V} {v : C → ℝ} {y₀ : B → ℝ}
    (hconst : ∀ k : κ, 0 < rayL1Norm (b k) C → rayDir (b k) C = v → rayScaled (b k) C B = y₀)
    (x : A → ℝ) (y : B → ℝ) :
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y) *
      rayDirMass b C v (fun _ ↦ True) =
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x) *
      rayDirMass b C v (fun k ↦ rayScaled (b k) C B = y) := by
  by_cases hy : y₀ = y
  · subst hy
    rw [rayDirMass_congr (fun k h1 h2 ↦ ⟨fun _ ↦ trivial, fun _ ↦ hconst k h1 h2⟩),
      rayDirMass_congr (fun k h1 h2 ↦ ⟨fun ⟨hx, _⟩ ↦ hx, fun hx ↦ ⟨hx, hconst k h1 h2⟩⟩)]
  · rw [rayDirMass_eq_zero (fun k h1 h2 h3 ↦ hy ((hconst k h1 h2).symm.trans h3)),
      rayDirMass_eq_zero (fun k h1 h2 ⟨_, h4⟩ ↦ hy ((hconst k h1 h2).symm.trans h4)),
      zero_mul, mul_zero]

/-- **Tropical bridge:** for every finite DAG `G` and every positive max-linear model `M` on `G`,
footprint separation implies `RayCICondition` for the ray columns `k ↦ (i ↦ M.coeff i k)`. -/
theorem MaxLinearModel.isFootprintSeparated_imp_rayCICondition
    {V : Type*} [Fintype V] [DecidableEq V] {G : DAG V} (M : MaxLinearModel G)
    {A B C : Finset V} (hfp : G.IsFootprintSeparated (A : Set V) (B : Set V) (C : Set V)) :
    RayCICondition (fun k i ↦ M.coeff i k) A B C := by
  classical
  constructor
  · -- Condition (I)
    intro k hkC
    have hfp0 : G.footprint (C : Set V) k = ∅ := by
      ext c; simp only [DAG.footprint, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hcC hreach
      have hpos := (M.coeff_pos_iff c k).2 hreach
      linarith [hkC c hcC]
    have hG1 := hfp.1 k hfp0
    by_contra h
    push Not at h
    rcases h with ⟨⟨a, haA, ha0⟩, ⟨b, hbB, hb0⟩⟩
    have ha_pos : 0 < M.coeff a k := lt_of_le_of_ne (M.coeff_nonneg a k) (Ne.symm ha0)
    have hb_pos : 0 < M.coeff b k := lt_of_le_of_ne (M.coeff_nonneg b k) (Ne.symm hb0)
    exact hG1 ⟨⟨a, haA, (M.coeff_pos_iff a k).1 ha_pos⟩, ⟨b, hbB, (M.coeff_pos_iff b k).1 hb_pos⟩⟩
  · -- Condition (II)
    intro v x y
    let Iv := Finset.univ.filter fun k : V ↦
      0 < rayL1Norm (fun i ↦ M.coeff i k) C ∧ rayDir (fun i ↦ M.coeff i k) C = v
    by_cases hcard : Iv.card ≤ 1
    · rcases Iv.eq_empty_or_nonempty with hEmpty | ⟨k₀, hk₀⟩
      · refine rayCICondition_part2_of_const_left (x₀ := 0) (fun k hpos hdir ↦ ?_) x y
        exfalso
        have : k ∈ Iv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos, hdir⟩
        rw [hEmpty] at this; exact Finset.notMem_empty k this
      · refine rayCICondition_part2_of_const_left (x₀ := rayScaled (fun i ↦ M.coeff i k₀) C A)
          (fun k hpos hdir ↦ ?_) x y
        have hk_in : k ∈ Iv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos, hdir⟩
        have hkeq : k = k₀ := Finset.card_le_one.1 hcard k hk_in k₀ hk₀
        subst hkeq; rfl
    · have h2 : 1 < Iv.card := Nat.lt_of_not_le hcard
      obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := Finset.one_lt_card.1 h2
      let Sf' : Finset V := (C.attach.filter fun c ↦ 0 < v c).map ⟨Subtype.val, Subtype.val_injective⟩
      have hfoot : ∀ k ∈ Iv, G.footprint (C : Set V) k = (Sf' : Set V) := by
        intro k hk
        obtain ⟨_, hpos, hdir⟩ := Finset.mem_filter.1 hk
        ext c
        simp only [DAG.footprint, mem_ofPred_eq, Finset.mem_coe, Sf', Finset.mem_map,
          Finset.mem_filter, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨hcC, hreach⟩
          refine ⟨⟨c, hcC⟩, ?_, rfl⟩
          have hcpos : 0 < M.coeff c k := (M.coeff_pos_iff c k).2 hreach
          have hdv : rayDir (fun i ↦ M.coeff i k) C ⟨c, hcC⟩ = v ⟨c, hcC⟩ := congrFun hdir ⟨c, hcC⟩
          rw [← hdv, rayDir]
          exact div_pos hcpos hpos
        · rintro ⟨⟨c', hc'C⟩, hvpos, rfl⟩
          refine ⟨hc'C, (M.coeff_pos_iff c' k).1 ?_⟩
          have hdv : rayDir (fun i ↦ M.coeff i k) C ⟨c', hc'C⟩ = v ⟨c', hc'C⟩ := congrFun hdir ⟨c', hc'C⟩
          rw [← hdv, rayDir] at hvpos
          exact (div_pos_iff_of_pos_right hpos).1 hvpos
      have hSf'_ne : Sf'.Nonempty := by
        obtain ⟨_, hpos, _⟩ := Finset.mem_filter.1 hk₁
        have hex : ∃ c ∈ C, 0 < M.coeff c k₁ := by
          by_contra h; push Not at h
          have hsum0 : rayL1Norm (fun i ↦ M.coeff i k₁) C = 0 :=
            Finset.sum_eq_zero fun c hc ↦ le_antisymm (h c hc) (M.coeff_nonneg c k₁)
          linarith
        rcases hex with ⟨c, hcC, hcpos⟩
        refine ⟨c, ?_⟩
        rw [← Finset.mem_coe, ← hfoot k₁ hk₁]
        exact ⟨hcC, (M.coeff_pos_iff c k₁).1 hcpos⟩
      have hG2 := hfp.2 (Sf' : Set V) hSf'_ne ⟨k₁, k₂, hne, hfoot k₁ hk₁, hfoot k₂ hk₂⟩
      rw [not_and_or] at hG2
      rcases hG2 with hnoA | hnoB
      · let x₀ : A → ℝ := fun a ↦ Sf'.sup' hSf'_ne fun c ↦
          if hc : c ∈ C then M.kleenePath a.1 c * v ⟨c, hc⟩ else 0
        refine rayCICondition_part2_of_const_left (x₀ := x₀) (fun k hpos hdir ↦ ?_) x y
        have hkIv : k ∈ Iv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos, hdir⟩
        funext a
        have hno : ¬ G.AvoidReach (C : Set V) k a.1 := fun hav ↦
          hnoA ⟨k, hfoot k hkIv, a.1, a.2, hav⟩
        have hkp := M.kleenePath_eq_sup'_of_not_avoidReach hno
          (fun c ↦ by rw [hfoot k hkIv]; rfl) hSf'_ne
        rw [rayScaled, MaxLinearModel.coeff, hkp, mul_div_assoc]
        have hscale_pos : 0 < M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C :=
          div_pos (M.diag_pos k) hpos
        have hmul_sup : (Sf'.sup' hSf'_ne fun c ↦ M.kleenePath a.1 c * M.kleenePath c k) *
            (M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C) =
            Sf'.sup' hSf'_ne fun c ↦ (M.kleenePath a.1 c * M.kleenePath c k) *
              (M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C) := by
          refine le_antisymm ?_ (Finset.sup'_le _ _ fun c hc ↦
            mul_le_mul_of_nonneg_right (Finset.le_sup' (fun c ↦ M.kleenePath a.1 c * M.kleenePath c k) hc)
              hscale_pos.le)
          obtain ⟨c₀, hc₀, heq⟩ := Finset.exists_mem_eq_sup' hSf'_ne
            (fun c ↦ M.kleenePath a.1 c * M.kleenePath c k)
          rw [heq]
          exact Finset.le_sup' (fun c ↦ (M.kleenePath a.1 c * M.kleenePath c k) *
            (M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C)) hc₀
        rw [hmul_sup]
        refine Finset.sup'_congr hSf'_ne rfl fun c hc ↦ ?_
        have hcC : c ∈ C := by
          have : c ∈ G.footprint (C : Set V) k := by rw [hfoot k hkIv]; exact hc
          exact this.1
        simp only [hcC, ↓reduceDIte]
        have hdv : M.coeff c k / rayL1Norm (fun i ↦ M.coeff i k) C = v ⟨c, hcC⟩ :=
          congrFun hdir ⟨c, hcC⟩
        rw [← hdv, MaxLinearModel.coeff]
        ring
      · let y₀ : B → ℝ := fun b ↦ Sf'.sup' hSf'_ne fun c ↦
          if hc : c ∈ C then M.kleenePath b.1 c * v ⟨c, hc⟩ else 0
        refine rayCICondition_part2_of_const_right (y₀ := y₀) (fun k hpos hdir ↦ ?_) x y
        have hkIv : k ∈ Iv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos, hdir⟩
        funext b
        have hno : ¬ G.AvoidReach (C : Set V) k b.1 := fun hav ↦
          hnoB ⟨k, hfoot k hkIv, b.1, b.2, hav⟩
        have hkp := M.kleenePath_eq_sup'_of_not_avoidReach hno
          (fun c ↦ by rw [hfoot k hkIv]; rfl) hSf'_ne
        rw [rayScaled, MaxLinearModel.coeff, hkp, mul_div_assoc]
        have hscale_pos : 0 < M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C :=
          div_pos (M.diag_pos k) hpos
        have hmul_sup : (Sf'.sup' hSf'_ne fun c ↦ M.kleenePath b.1 c * M.kleenePath c k) *
            (M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C) =
            Sf'.sup' hSf'_ne fun c ↦ (M.kleenePath b.1 c * M.kleenePath c k) *
              (M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C) := by
          refine le_antisymm ?_ (Finset.sup'_le _ _ fun c hc ↦
            mul_le_mul_of_nonneg_right (Finset.le_sup' (fun c ↦ M.kleenePath b.1 c * M.kleenePath c k) hc)
              hscale_pos.le)
          obtain ⟨c₀, hc₀, heq⟩ := Finset.exists_mem_eq_sup' hSf'_ne
            (fun c ↦ M.kleenePath b.1 c * M.kleenePath c k)
          rw [heq]
          exact Finset.le_sup' (fun c ↦ (M.kleenePath b.1 c * M.kleenePath c k) *
            (M.diag k / rayL1Norm (fun i ↦ M.coeff i k) C)) hc₀
        rw [hmul_sup]
        refine Finset.sup'_congr hSf'_ne rfl fun c hc ↦ ?_
        have hcC : c ∈ C := by
          have : c ∈ G.footprint (C : Set V) k := by rw [hfoot k hkIv]; exact hc
          exact this.1
        simp only [hcC, ↓reduceDIte]
        have hdv : M.coeff c k / rayL1Norm (fun i ↦ M.coeff i k) C = v ⟨c, hcC⟩ :=
          congrFun hdir ⟨c, hcC⟩
        rw [← hdv, MaxLinearModel.coeff]
        ring

end MaxLinearCI

end ExtremeValueTheory
