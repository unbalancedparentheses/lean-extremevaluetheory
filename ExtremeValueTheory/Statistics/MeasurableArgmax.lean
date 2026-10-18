/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib

/-!
# Measurable selection of a maximizer over a compact set of parameters

Let `K ⊂ ℝ²` be compact and nonempty, and let `f : ℝ² → α → [-∞, ∞]` be continuous in the
parameter on `K` and measurable in the data. Then there is a **measurable** map `g : α → ℝ²` with
`g x ∈ K` a maximizer of `f(·, x)` over `K` for every `x`
(`exists_measurable_isMaxOn`). Mathlib has no general measurable selection theorem; for a compact
parameter set and a continuous criterion the classical argument of Jennrich (1969) works: take
the **lexicographically smallest maximizer**.

## Proof

* For a closed `C`, the set `{x | ∃ θ ∈ K ∩ C maximizing f(·, x) over K}` is measurable
  (`measurableSet_exists_isMaxOn_inter`): by continuity, a supremum over `K` or `K ∩ C` is a
  supremum over a countable dense subset, and the event is `sup_K f ≤ sup_{K ∩ C} f`.
* The first coordinate `g₁(x) = min {θ₁ | θ ∈ argmax}` is measurable, since `g₁ x ≤ a` is the
  event above for `C = {θ₁ ≤ a}`.
* The second coordinate `g₂(x) = min {θ₂ | θ ∈ argmax, θ₁ = g₁ x}` is measurable: `g₂ x ≤ b` iff
  some maximizer has `θ₁ ≤ g₁ x` and `θ₂ ≤ b`, which by compactness is the countable
  intersection over `m` of the unions over rationals `q < g₁ x + 1/(m+1)` of the events above
  for `C = {θ₁ ≤ q, θ₂ ≤ b}`.

## References

* R. I. Jennrich, *Asymptotic properties of non-linear least squares estimators*, Ann. Math.
  Statist. 40 (1969), Lemma 2.
-/

open Set Filter Topology MeasureTheory

namespace ExtremeValueTheory

section Argmax

variable {α : Type*} [MeasurableSpace α] {K : Set (ℝ × ℝ)} {f : ℝ × ℝ → α → EReal}

omit [MeasurableSpace α] in
/-- On a subset `D ⊆ K` dense in `θ ∈ K`, the supremum of a function continuous on `K` dominates
its value at `θ`. -/
lemma le_iSup_of_mem_closure {D : Set (ℝ × ℝ)} (hDK : D ⊆ K) {x : α}
    (hf : ContinuousOn (fun p => f p x) K) {θ : ℝ × ℝ} (hθK : θ ∈ K) (hθ : θ ∈ closure D) :
    f θ x ≤ ⨆ d : D, f d x := by
  have hne : (𝓝[D] θ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hθ
  have ht : Tendsto (fun p => f p x) (𝓝[D] θ) (𝓝 (f θ x)) :=
    ((hf θ hθK).mono hDK).tendsto
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun d hd =>
    le_iSup (fun d : D => f d x) ⟨d, hd⟩)

variable (hK : IsCompact K) (hf : ∀ x, ContinuousOn (fun p => f p x) K)
  (hfm : ∀ θ, Measurable (f θ))
include hK hf hfm

/-- **The event that a maximizer lies in a closed set is measurable.** -/
theorem measurableSet_exists_isMaxOn_inter {C : Set (ℝ × ℝ)} (hC : IsClosed C) :
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

/-- **Measurable selection of a maximizer** over a compact nonempty parameter set `K ⊂ ℝ²`, for
a criterion continuous on `K` in the parameter and measurable in the data: the lexicographically
smallest maximizer. -/
theorem exists_measurable_isMaxOn (hKne : K.Nonempty) :
    ∃ g : α → ℝ × ℝ, Measurable g ∧ ∀ x, g x ∈ K ∧ IsMaxOn (fun p => f p x) K (g x) := by
  -- the argmax sets
  set A : α → Set (ℝ × ℝ) := fun x => {θ | θ ∈ K ∧ IsMaxOn (fun p => f p x) K θ} with hA
  have hAne : ∀ x, (A x).Nonempty := fun x => by
    obtain ⟨θ, hθ, hmax⟩ := hK.exists_isMaxOn hKne (hf x)
    exact ⟨θ, hθ, hmax⟩
  have hAc : ∀ x, IsCompact (A x) := fun x => by
    obtain ⟨θ, hθ, hmax⟩ := hAne x
    have he : A x = K ∩ (fun p => f p x) ⁻¹' Ici (f θ x) := by
      ext p
      simp only [hA, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici]
      exact ⟨fun h => ⟨h.1, h.2 hθ⟩, fun h => ⟨h.1, fun q hq => (hmax hq).trans h.2⟩⟩
    rw [he]
    exact hK.of_isClosed_subset ((hf x).preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
      inter_subset_left
  have hevent : ∀ {C : Set (ℝ × ℝ)}, IsClosed C →
      MeasurableSet {x | ∃ θ ∈ A x, θ ∈ C} := fun {C} hC => by
    convert measurableSet_exists_isMaxOn_inter hK hf hfm hC using 1
    ext x
    simp only [hA, mem_ofPred_eq, mem_inter_iff]
    exact ⟨fun ⟨θ, ⟨h1, h2⟩, h3⟩ => ⟨θ, ⟨h1, h3⟩, h2⟩, fun ⟨θ, ⟨h1, h3⟩, h2⟩ => ⟨θ, ⟨h1, h2⟩, h3⟩⟩
  -- the first coordinate
  set g₁ : α → ℝ := fun x => sInf (Prod.fst '' A x) with hg₁
  have hg₁mem : ∀ x, g₁ x ∈ Prod.fst '' A x := fun x =>
    ((hAc x).image continuous_fst).sInf_mem ((hAne x).image _)
  have hg₁le : ∀ x, ∀ θ ∈ A x, g₁ x ≤ θ.1 := fun x θ hθ =>
    csInf_le ((hAc x).image continuous_fst).bddBelow (mem_image_of_mem _ hθ)
  have hg₁iff : ∀ x a, g₁ x ≤ a ↔ ∃ θ ∈ A x, θ ∈ {p : ℝ × ℝ | p.1 ≤ a} := fun x a => by
    constructor
    · intro h
      obtain ⟨θ, hθ, he⟩ := hg₁mem x
      exact ⟨θ, hθ, by simp only [mem_ofPred_eq]; rw [he]; exact h⟩
    · rintro ⟨θ, hθ, h⟩
      exact (hg₁le x θ hθ).trans h
  have hg₁m : Measurable g₁ := by
    refine measurable_of_Iic fun a => ?_
    have : g₁ ⁻¹' Iic a = {x | ∃ θ ∈ A x, θ ∈ {p : ℝ × ℝ | p.1 ≤ a}} := by
      ext x; exact hg₁iff x a
    rw [this]
    exact hevent (isClosed_le continuous_fst continuous_const)
  -- the second coordinate
  set A₂ : α → Set (ℝ × ℝ) := fun x => A x ∩ {θ | θ.1 = g₁ x} with hA₂
  have hA₂ne : ∀ x, (A₂ x).Nonempty := fun x => by
    obtain ⟨θ, hθ, he⟩ := hg₁mem x
    exact ⟨θ, hθ, he⟩
  have hA₂c : ∀ x, IsCompact (A₂ x) := fun x =>
    (hAc x).inter_right (isClosed_eq continuous_fst continuous_const)
  set g₂ : α → ℝ := fun x => sInf (Prod.snd '' A₂ x) with hg₂
  have hg₂mem : ∀ x, g₂ x ∈ Prod.snd '' A₂ x := fun x =>
    ((hA₂c x).image continuous_snd).sInf_mem ((hA₂ne x).image _)
  have hg₂iff : ∀ x b, g₂ x ≤ b ↔ ∃ θ ∈ A x, θ.1 ≤ g₁ x ∧ θ.2 ≤ b := fun x b => by
    constructor
    · intro h
      obtain ⟨θ, ⟨hθ, he₁⟩, he⟩ := hg₂mem x
      exact ⟨θ, hθ, he₁.le, by rw [he]; exact h⟩
    · rintro ⟨θ, hθ, h1, h2⟩
      have he : θ.1 = g₁ x := le_antisymm h1 (hg₁le x θ hθ)
      exact (csInf_le ((hA₂c x).image continuous_snd).bddBelow
        (mem_image_of_mem _ (⟨hθ, he⟩ : θ ∈ A₂ x))).trans h2
  have hg₂m : Measurable g₂ := by
    refine measurable_of_Iic fun b => ?_
    have : g₂ ⁻¹' Iic b = ⋂ m : ℕ, ⋃ q : ℚ, ({x | (q : ℝ) < g₁ x + 1 / ((m : ℝ) + 1)} ∩
        {x | ∃ θ ∈ A x, θ ∈ {p : ℝ × ℝ | p.1 ≤ q ∧ p.2 ≤ b}}) := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_iInter, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      rw [hg₂iff]
      constructor
      · rintro ⟨θ, hθ, h1, h2⟩ m
        have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g₁ x) hm)
        exact ⟨q, hq2, θ, hθ, h1.trans hq1.le, h2⟩
      · intro h
        set t : ℕ → Set (ℝ × ℝ) := fun m =>
          A x ∩ {p | p.1 ≤ g₁ x + 1 / ((m : ℝ) + 1) ∧ p.2 ≤ b} with ht
        have htcl : ∀ m, IsClosed (t m) := fun m =>
          (hAc x).isClosed.inter ((isClosed_le continuous_fst continuous_const).inter
            (isClosed_le continuous_snd continuous_const))
        have htd : ∀ m, t (m + 1) ⊆ t m := fun m p hp => by
          refine ⟨hp.1, le_trans hp.2.1 ?_, hp.2.2⟩
          gcongr
          linarith
        have htn : ∀ m, (t m).Nonempty := fun m => by
          obtain ⟨q, hq, θ, hθ, h1, h2⟩ := h m
          exact ⟨θ, hθ, h1.trans hq.le, h2⟩
        obtain ⟨θ, hθ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
          htd htn ((hAc x).of_isClosed_subset (htcl 0) inter_subset_left) htcl
        rw [mem_iInter] at hθ
        refine ⟨θ, (hθ 0).1, ?_, (hθ 0).2.2⟩
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
        exact (hθ m).2.1.trans (by linarith)
    rw [this]
    refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => ?_
    exact (measurableSet_lt measurable_const (hg₁m.add_const _)).inter
      (hevent ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le continuous_snd continuous_const)))
  -- the lexicographic minimizer
  refine ⟨fun x => (g₁ x, g₂ x), hg₁m.prodMk hg₂m, fun x => ?_⟩
  obtain ⟨θ, ⟨hθ, he₁⟩, he₂⟩ := hg₂mem x
  have : θ = (g₁ x, g₂ x) := Prod.ext he₁ he₂
  show (g₁ x, g₂ x) ∈ K ∧ IsMaxOn (fun p => f p x) K (g₁ x, g₂ x)
  rw [← this]
  exact hθ

end Argmax

end ExtremeValueTheory
