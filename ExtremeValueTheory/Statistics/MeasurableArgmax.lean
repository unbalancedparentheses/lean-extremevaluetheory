/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib

/-!
# Measurable selection of a maximizer over a compact set of parameters

Let `K ⊂ ℝ²` or `K ⊂ ℝ³` be compact and nonempty, and let `f : Θ → α → [-∞, ∞]` be continuous in the
parameter on `K` and measurable in the data. Then there is a **measurable** map `g : α → Θ` with
`g x ∈ K` a maximizer of `f(·, x)` over `K` for every `x`
(`exists_measurable_isMaxOn`, `exists_measurable_isMaxOn₃`). Mathlib has no general measurable
selection theorem; for a compact parameter set and a continuous criterion the classical argument of
Jennrich (1969) works: take the **lexicographically smallest maximizer**.

## Proof

* For a closed `C`, the set `{x | ∃ θ ∈ K ∩ C maximizing f(·, x) over K}` is measurable
  (`measurableSet_exists_isMaxOn_inter`): by continuity, a supremum over `K` or `K ∩ C` is a
  supremum over a countable dense subset, and the event is `sup_K f ≤ sup_{K ∩ C} f`.
* Let `A x ⊂ ℝ × E` be compact, nonempty, with measurable events `{x | ∃ θ ∈ A x, θ ∈ C}`, `C`
  closed (`lexStep`). The first coordinate `g₁(x) = min {θ₁ | θ ∈ A x}` is measurable, since
  `g₁ x ≤ a` is such an event, for `C = {θ₁ ≤ a}`. The section `A₂ x = {y | (g₁ x, y) ∈ A x}` has
  the same properties: `∃ y ∈ A₂ x, y ∈ C` iff some `θ ∈ A x` has `θ₁ ≤ g₁ x` and `θ₂ ∈ C`, which by
  compactness is the countable intersection over `m` of the unions over rationals
  `q < g₁ x + 1/(m+1)` of the events for `{θ₁ ≤ q, θ₂ ∈ C}`.
* The lexicographic minimizer is obtained by iterating this step.

## References

* R. I. Jennrich, *Asymptotic properties of non-linear least squares estimators*, Ann. Math.
  Statist. 40 (1969), Lemma 2.
-/

open Set Filter Topology MeasureTheory

namespace ExtremeValueTheory

section Argmax

variable {α : Type*} [MeasurableSpace α] {Θ : Type*} [TopologicalSpace Θ]
  [SecondCountableTopology Θ] {K : Set Θ} {f : Θ → α → EReal}

omit [MeasurableSpace α] [SecondCountableTopology Θ] in
/-- On a subset `D ⊆ K` dense in `θ ∈ K`, the supremum of a function continuous on `K` dominates
its value at `θ`. -/
lemma le_iSup_of_mem_closure {D : Set Θ} (hDK : D ⊆ K) {x : α}
    (hf : ContinuousOn (fun p => f p x) K) {θ : Θ} (hθK : θ ∈ K) (hθ : θ ∈ closure D) :
    f θ x ≤ ⨆ d : D, f d x := by
  have hne : (𝓝[D] θ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hθ
  have ht : Tendsto (fun p => f p x) (𝓝[D] θ) (𝓝 (f θ x)) :=
    ((hf θ hθK).mono hDK).tendsto
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun d hd =>
    le_iSup (fun d : D => f d x) ⟨d, hd⟩)

/-- **The event that a maximizer lies in a closed set is measurable.** -/
theorem measurableSet_exists_isMaxOn_inter (hK : IsCompact K)
    (hf : ∀ x, ContinuousOn (fun p => f p x) K) (hfm : ∀ θ, Measurable (f θ)) {C : Set Θ}
    (hC : IsClosed C) :
    MeasurableSet {x | ∃ θ ∈ K ∩ C, IsMaxOn (fun p => f p x) K θ} := by
  by_cases hne : (K ∩ C).Nonempty
  swap
  · convert MeasurableSet.empty
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
    exact fun θ hθ => absurd ⟨θ, hθ⟩ hne
  have hKC : IsCompact (K ∩ C) := hK.inter_right hC
  obtain ⟨D, hDc, hDK, hKD⟩ := TopologicalSpace.exists_countable_dense_subset K
  obtain ⟨E, hEc, hEK, hKE⟩ := TopologicalSpace.exists_countable_dense_subset (K ∩ C)
  have : Countable D := hDc.to_subtype
  have : Countable E := hEc.to_subtype
  have hset : {x | ∃ θ ∈ K ∩ C, IsMaxOn (fun p => f p x) K θ} =
      {x | (⨆ d : D, f d x) ≤ ⨆ e : E, f e x} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨θ, hθ, hmax⟩
      refine (iSup_le fun d => ?_).trans
        (le_iSup_of_mem_closure (hEK.trans inter_subset_left) (hf x) hθ.1 (hKE hθ))
      exact hmax (hDK d.2)
    · intro hle
      obtain ⟨θc, hθc, hmax⟩ := hKC.exists_isMaxOn hne ((hf x).mono inter_subset_left)
      refine ⟨θc, hθc, fun p hp => ?_⟩
      have h1 := le_iSup_of_mem_closure hDK (hf x) hp (hKD hp)
      have h2 : (⨆ e : E, f e x) ≤ f θc x := iSup_le fun e => hmax (hEK e.2)
      exact h1.trans (hle.trans h2)
  rw [hset]
  exact measurableSet_le (Measurable.iSup fun d => hfm d) (Measurable.iSup fun e => hfm e)

/-- The set of maximizers of `f(·, x)` over `K`. -/
def argmaxSet (K : Set Θ) (f : Θ → α → EReal) (x : α) : Set Θ :=
  {θ | θ ∈ K ∧ IsMaxOn (fun p => f p x) K θ}

omit [MeasurableSpace α] [SecondCountableTopology Θ] in
lemma argmaxSet_nonempty (hK : IsCompact K) (hf : ∀ x, ContinuousOn (fun p => f p x) K)
    (hKne : K.Nonempty) (x : α) : (argmaxSet K f x).Nonempty := by
  obtain ⟨θ, hθ, hmax⟩ := hK.exists_isMaxOn hKne (hf x)
  exact ⟨θ, hθ, hmax⟩

omit [MeasurableSpace α] [SecondCountableTopology Θ] in
lemma isCompact_argmaxSet [T2Space Θ] (hK : IsCompact K)
    (hf : ∀ x, ContinuousOn (fun p => f p x) K) (hKne : K.Nonempty) (x : α) :
    IsCompact (argmaxSet K f x) := by
  obtain ⟨θ, hθ, hmax⟩ := hK.exists_isMaxOn hKne (hf x)
  have he : argmaxSet K f x = K ∩ (fun p => f p x) ⁻¹' Ici (f θ x) := by
    ext p
    simp only [argmaxSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici]
    exact ⟨fun h => ⟨h.1, h.2 hθ⟩, fun h => ⟨h.1, fun q hq => (hmax hq).trans h.2⟩⟩
  rw [he]
  exact hK.of_isClosed_subset ((hf x).preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
    inter_subset_left

lemma measurableSet_exists_mem_argmaxSet (hK : IsCompact K)
    (hf : ∀ x, ContinuousOn (fun p => f p x) K) (hfm : ∀ θ, Measurable (f θ)) {C : Set Θ}
    (hC : IsClosed C) : MeasurableSet {x | ∃ θ ∈ argmaxSet K f x, θ ∈ C} := by
  convert measurableSet_exists_isMaxOn_inter hK hf hfm hC using 1
  ext x
  simp only [argmaxSet, mem_ofPred_eq, mem_inter_iff]
  exact ⟨fun ⟨θ, ⟨h1, h2⟩, h3⟩ => ⟨θ, ⟨h1, h3⟩, h2⟩, fun ⟨θ, ⟨h1, h3⟩, h2⟩ => ⟨θ, ⟨h1, h2⟩, h3⟩⟩

end Argmax

section Lex

variable {α : Type*} [MeasurableSpace α] {E : Type*} [TopologicalSpace E] [T2Space E]

/-- A family of compact nonempty sets `A x ⊂ E` with measurable events
`{x | ∃ θ ∈ A x, θ ∈ C}`, `C` closed. -/
structure IsMeasurableCompactFamily (A : α → Set E) : Prop where
  nonempty : ∀ x, (A x).Nonempty
  isCompact : ∀ x, IsCompact (A x)
  event : ∀ {C : Set E}, IsClosed C → MeasurableSet {x | ∃ θ ∈ A x, θ ∈ C}

omit [T2Space E] in
/-- The minimal first coordinate is measurable and attained. -/
lemma IsMeasurableCompactFamily.measurable_sInf_fst {A : α → Set (ℝ × E)}
    (hA : IsMeasurableCompactFamily A) :
    Measurable (fun x => sInf (Prod.fst '' A x)) ∧
      (∀ x, sInf (Prod.fst '' A x) ∈ Prod.fst '' A x) ∧
      ∀ x, ∀ θ ∈ A x, sInf (Prod.fst '' A x) ≤ θ.1 := by
  have hmem : ∀ x, sInf (Prod.fst '' A x) ∈ Prod.fst '' A x := fun x =>
    ((hA.isCompact x).image continuous_fst).sInf_mem ((hA.nonempty x).image _)
  have hle : ∀ x, ∀ θ ∈ A x, sInf (Prod.fst '' A x) ≤ θ.1 := fun x θ hθ =>
    csInf_le ((hA.isCompact x).image continuous_fst).bddBelow (mem_image_of_mem _ hθ)
  refine ⟨measurable_of_Iic fun a => ?_, hmem, hle⟩
  have : (fun x => sInf (Prod.fst '' A x)) ⁻¹' Iic a =
      {x | ∃ θ ∈ A x, θ ∈ {p : ℝ × E | p.1 ≤ a}} := by
    ext x
    constructor
    · intro h
      obtain ⟨θ, hθ, he⟩ := hmem x
      exact ⟨θ, hθ, by simp only [mem_ofPred_eq]; rw [he]; exact h⟩
    · rintro ⟨θ, hθ, h⟩
      exact (hle x θ hθ).trans h
  rw [this]
  exact hA.event (isClosed_le continuous_fst continuous_const)

/-- **One step of the lexicographic selection**: the section of `A x` at the minimal first
coordinate is again a measurable compact family. -/
theorem IsMeasurableCompactFamily.section_sInf_fst {A : α → Set (ℝ × E)}
    (hA : IsMeasurableCompactFamily A) :
    IsMeasurableCompactFamily fun x =>
      Prod.snd '' (A x ∩ {θ | θ.1 = sInf (Prod.fst '' A x)}) := by
  obtain ⟨hg₁m, hg₁mem, hg₁le⟩ := hA.measurable_sInf_fst
  set g₁ : α → ℝ := fun x => sInf (Prod.fst '' A x) with hg₁
  refine ⟨fun x => ?_, fun x => ?_, fun {C} hC => ?_⟩
  · obtain ⟨θ, hθ, he⟩ := hg₁mem x
    exact ⟨θ.2, θ, ⟨hθ, he⟩, rfl⟩
  · exact ((hA.isCompact x).inter_right
      (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  · have hiff : ∀ x, (∃ y ∈ Prod.snd '' (A x ∩ {θ | θ.1 = g₁ x}), y ∈ C) ↔
        ∃ θ ∈ A x, θ.1 ≤ g₁ x ∧ θ.2 ∈ C := fun x => by
      constructor
      · rintro ⟨y, ⟨θ, ⟨hθ, he₁⟩, rfl⟩, hy⟩
        exact ⟨θ, hθ, le_of_eq he₁, hy⟩
      · rintro ⟨θ, hθ, h1, h2⟩
        exact ⟨θ.2, ⟨θ, ⟨hθ, le_antisymm h1 (hg₁le x θ hθ)⟩, rfl⟩, h2⟩
    have hset : {x | ∃ y ∈ Prod.snd '' (A x ∩ {θ | θ.1 = g₁ x}), y ∈ C} =
        ⋂ m : ℕ, ⋃ q : ℚ, ({x | (q : ℝ) < g₁ x + 1 / ((m : ℝ) + 1)} ∩
          {x | ∃ θ ∈ A x, θ ∈ {p : ℝ × E | p.1 ≤ q ∧ p.2 ∈ C}}) := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
      rw [hiff]
      constructor
      · rintro ⟨θ, hθ, h1, h2⟩ m
        have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g₁ x) hm)
        exact ⟨q, hq2, θ, hθ, h1.trans hq1.le, h2⟩
      · intro h
        set t : ℕ → Set (ℝ × E) := fun m =>
          A x ∩ {p | p.1 ≤ g₁ x + 1 / ((m : ℝ) + 1) ∧ p.2 ∈ C} with ht
        have htcl : ∀ m, IsClosed (t m) := fun m =>
          (hA.isCompact x).isClosed.inter ((isClosed_le continuous_fst continuous_const).inter
            (hC.preimage continuous_snd))
        have htd : ∀ m, t (m + 1) ⊆ t m := fun m p hp => by
          refine ⟨hp.1, le_trans hp.2.1 ?_, hp.2.2⟩
          gcongr
          linarith
        have htn : ∀ m, (t m).Nonempty := fun m => by
          obtain ⟨q, hq, θ, hθ, h1, h2⟩ := h m
          exact ⟨θ, hθ, h1.trans hq.le, h2⟩
        obtain ⟨θ, hθ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
          htd htn ((hA.isCompact x).of_isClosed_subset (htcl 0) inter_subset_left) htcl
        rw [mem_iInter] at hθ
        refine ⟨θ, (hθ 0).1, ?_, (hθ 0).2.2⟩
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
        exact (hθ m).2.1.trans (by linarith)
    rw [hset]
    refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => ?_
    exact (measurableSet_lt measurable_const (hg₁m.add_const _)).inter
      (hA.event ((isClosed_le continuous_fst continuous_const).inter
        (hC.preimage continuous_snd)))

/-- The minimum of a measurable compact family of subsets of `ℝ` is a measurable selection. -/
lemma IsMeasurableCompactFamily.measurable_sInf {A : α → Set ℝ}
    (hA : IsMeasurableCompactFamily A) :
    Measurable (fun x => sInf (A x)) ∧ ∀ x, sInf (A x) ∈ A x := by
  have hmem : ∀ x, sInf (A x) ∈ A x := fun x => (hA.isCompact x).sInf_mem (hA.nonempty x)
  refine ⟨measurable_of_Iic fun a => ?_, hmem⟩
  have : (fun x => sInf (A x)) ⁻¹' Iic a = {x | ∃ θ ∈ A x, θ ∈ Iic a} := by
    ext x
    exact ⟨fun h => ⟨_, hmem x, h⟩,
      fun ⟨θ, hθ, h⟩ => (csInf_le (hA.isCompact x).bddBelow hθ).trans h⟩
  rw [this]
  exact hA.event isClosed_Iic

end Lex

section Selection

variable {α : Type*} [MeasurableSpace α]

/-- **Measurable selection of a maximizer** over a compact nonempty parameter set `K ⊂ ℝ²`, for
a criterion continuous on `K` in the parameter and measurable in the data: the lexicographically
smallest maximizer. -/
theorem exists_measurable_isMaxOn {K : Set (ℝ × ℝ)} {f : ℝ × ℝ → α → EReal} (hK : IsCompact K)
    (hf : ∀ x, ContinuousOn (fun p => f p x) K) (hfm : ∀ θ, Measurable (f θ))
    (hKne : K.Nonempty) :
    ∃ g : α → ℝ × ℝ, Measurable g ∧ ∀ x, g x ∈ K ∧ IsMaxOn (fun p => f p x) K (g x) := by
  have hA : IsMeasurableCompactFamily (argmaxSet K f) :=
    ⟨argmaxSet_nonempty hK hf hKne, isCompact_argmaxSet hK hf hKne,
      measurableSet_exists_mem_argmaxSet hK hf hfm⟩
  obtain ⟨hg₁m, -, -⟩ := hA.measurable_sInf_fst
  obtain ⟨hg₂m, hg₂mem⟩ := hA.section_sInf_fst.measurable_sInf
  refine ⟨_, hg₁m.prodMk hg₂m, fun x => ?_⟩
  obtain ⟨θ, ⟨hθ, he₁⟩, he₂⟩ := hg₂mem x
  have : θ = (sInf (Prod.fst '' argmaxSet K f x), sInf (Prod.snd '' (argmaxSet K f x ∩
      {θ | θ.1 = sInf (Prod.fst '' argmaxSet K f x)}))) := Prod.ext he₁ he₂
  rw [← this]
  exact hθ

/-- **Measurable selection of a maximizer** over a compact nonempty parameter set `K ⊂ ℝ³`, for
a criterion continuous on `K` in the parameter and measurable in the data: the lexicographically
smallest maximizer. -/
theorem exists_measurable_isMaxOn₃ {K : Set (ℝ × ℝ × ℝ)} {f : ℝ × ℝ × ℝ → α → EReal}
    (hK : IsCompact K) (hf : ∀ x, ContinuousOn (fun p => f p x) K) (hfm : ∀ θ, Measurable (f θ))
    (hKne : K.Nonempty) :
    ∃ g : α → ℝ × ℝ × ℝ, Measurable g ∧ ∀ x, g x ∈ K ∧ IsMaxOn (fun p => f p x) K (g x) := by
  have hA : IsMeasurableCompactFamily (argmaxSet K f) :=
    ⟨argmaxSet_nonempty hK hf hKne, isCompact_argmaxSet hK hf hKne,
      measurableSet_exists_mem_argmaxSet hK hf hfm⟩
  have hA₂ := hA.section_sInf_fst
  have hA₃ := hA₂.section_sInf_fst
  obtain ⟨hg₁m, -, -⟩ := hA.measurable_sInf_fst
  obtain ⟨hg₂m, -, -⟩ := hA₂.measurable_sInf_fst
  obtain ⟨hg₃m, hg₃mem⟩ := hA₃.measurable_sInf
  refine ⟨_, hg₁m.prodMk (hg₂m.prodMk hg₃m), fun x => ?_⟩
  obtain ⟨p, ⟨⟨θ, ⟨hθ, he₁⟩, hp⟩, he₂⟩, he₃⟩ := hg₃mem x
  subst hp
  have : θ = (_, _, _) := Prod.ext he₁ (Prod.ext he₂ he₃)
  rw [← this]
  exact hθ

end Selection

end ExtremeValueTheory
