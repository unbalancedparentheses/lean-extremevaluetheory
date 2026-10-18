/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.BetaMixing
import ExtremeValueTheory.Dependence.EchoPowerLag
import ExtremeValueTheory.Minimality.DependenceMixing

/-!
# `β`-mixing of the echo process

TODO docstring
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section Partition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- For pairwise disjoint measurable `Cᵢ`, `∑ᵢ P(Cᵢ ∩ S) ≤ P(S)`. -/
theorem sum_measureReal_inter_le {k : ℕ} {C : Fin k → Set Ω} (hC : ∀ i, MeasurableSet (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) {S : Set Ω} (hS : MeasurableSet S) :
    ∑ i, P.real (C i ∩ S) ≤ P.real S := by
  rw [← measureReal_iUnion_fintype (μ := P)
    (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
    fun i => (hC i).inter hS]
  exact measureReal_mono (iUnion_subset fun i => inter_subset_right)

/-- For a finite measurable partition `(Cᵢ)` of `Ω`, `∑ᵢ P(Cᵢ ∩ S) = P(S)`. -/
theorem sum_measureReal_inter_eq {k : ℕ} {C : Fin k → Set Ω} (hC : ∀ i, MeasurableSet (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) (hu : (⋃ i, C i) = univ) {S : Set Ω}
    (hS : MeasurableSet S) : ∑ i, P.real (C i ∩ S) = P.real S := by
  rw [← measureReal_iUnion_fintype (μ := P)
    (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
    fun i => (hC i).inter hS, ← iUnion_inter, hu, univ_inter]

end Partition

section EchoBeta

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

theorem measurableSet_echoGood (hZ : ∀ t, Measurable (Z t)) (hLm : Measurable L) (s : ℤ)
    (h : ℕ) : MeasurableSet (echoGood L Z s h) := by
  have : echoGood L Z s h = ⋂ m : ℕ, (fun ω => L (Z (s - m) ω)) ⁻¹' Iio (h + m) := by
    ext ω; simp [echoGood]
  rw [this]
  exact MeasurableSet.iInter fun m => (hLm.comp (hZ _)) measurableSet_Iio

/-- **The `β`-mixing coefficients of the echo process**: for `h ≥ 1`,
`β(h) ≤ 2 ∑_{m ≥ 0} P(L(Z) ≥ h + m)`. Only measurability of `L`, independence and the common
Pareto law of the innovations, and summability of the tail of `L(Z)` are used. -/
theorem betaMixing_echoProcess_le (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hLm : Measurable L) {h : ℕ} (hh : 1 ≤ h)
    (hsum : Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ L z}) :
    (betaMixing (fun k : ℕ => echoProcess L Z k) P h).toReal ≤
      2 * ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z} := by
  set T := ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z}
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => measureReal_nonneg
  have hX : ∀ t : ℕ, Measurable (echoProcess L Z t) := fun t => measurable_echoProcess hZ hLm t
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (iSup_le fun s => ?_)
  have hI : Indep (innovationPast Z s) (innovationFuture Z s) P :=
    indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (Z i) inferInstance)
      (fun i => (hZ i).comap_le) hind.iIndep (by
        rw [Set.disjoint_left]
        intro i hi hi'
        simp only [mem_ofPred_eq] at hi hi'
        omega)
  have hpast : pastMeasurableSpace (fun k : ℕ => echoProcess L Z k) s ≤ innovationPast Z s := by
    refine iSup₂_le fun t ht => Measurable.comap_le ?_
    show Measurable[innovationPast Z s] (echoProcess L Z (t : ℤ))
    rw [← echoProcess_truncPast (L := L) (Z := Z) (s := (s : ℤ)) (t := (t : ℤ))
      (by exact_mod_cast ht)]
    exact measurable_echoProcess (mΩ := innovationPast Z s) (measurable_truncPast s) hLm t
  have hfut : innovationFuture Z s ≤ mΩ := iSup₂_le fun i _ => (hZ i).comap_le
  have hg := measureReal_compl_echoGood_le hZ hlaw hLm (s : ℤ) h hsum (P := P)
  set G := echoGood L Z s h
  have hG : MeasurableSet G := measurableSet_echoGood hZ hLm s h
  simp only [betaMixingCoeff, iSup_le_iff]
  intro k l A hA hdA huA B hB hdB huB
  refine ENNReal.ofReal_le_ofReal ?_
  have hAm : ∀ i, MeasurableSet (A i) := fun i => pastMeasurableSpace_le hX s _ (hA i)
  have hBm : ∀ j, MeasurableSet (B j) := fun j => futureMeasurableSpace_le hX _ _ (hB j)
  -- couple the future partition with a disjoint family of future-innovation events
  choose B' hB' e using fun j => exists_inter_echoGood_eq hLm hh (hB j)
  set B'' : Fin l → Set Ω := fun j => B' j \ ⋃ (i : Fin l) (_ : i < j), B' i
  have hB'' : ∀ j, MeasurableSet[innovationFuture Z s] (B'' j) := fun j =>
    (hB' j).diff (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hB' i)
  have hB''m : ∀ j, MeasurableSet (B'' j) := fun j => hfut _ (hB'' j)
  have hdB'' : Pairwise fun i j => Disjoint (B'' i) (B'' j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · refine Set.disjoint_left.2 fun ω h1 h2 => h2.2 ?_
      exact mem_iUnion₂.2 ⟨i, hlt, h1.1⟩
    · refine Set.disjoint_left.2 fun ω h1 h2 => h1.2 ?_
      exact mem_iUnion₂.2 ⟨j, hlt, h2.1⟩
  have e'' : ∀ j, B j ∩ G = B'' j ∩ G := by
    intro j
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : ω ∈ B' j ∩ G := e j ▸ ⟨h1, h2⟩
      refine ⟨⟨h3.1, fun hω => ?_⟩, h2⟩
      obtain ⟨i, hi, h4⟩ := mem_iUnion₂.1 hω
      have h5 : ω ∈ B i ∩ G := (e i).symm ▸ ⟨h4, h2⟩
      exact Set.disjoint_left.1 (hdB (ne_of_lt hi)) h5.1 h1
    · rintro ⟨h1, h2⟩
      have h3 : ω ∈ B j ∩ G := (e j).symm ▸ ⟨h1.1, h2⟩
      exact h3
  -- the pointwise bound
  have key : ∀ i j, |P.real (A i ∩ B j) - P.real (A i) * P.real (B j)| ≤
      P.real (A i ∩ (B j ∩ Gᶜ)) + P.real (A i ∩ (B'' j ∩ Gᶜ)) +
        P.real (A i) * (P.real (B j ∩ Gᶜ) + P.real (B'' j ∩ Gᶜ)) := by
    intro i j
    have hind' : P.real (A i ∩ B'' j) = P.real (A i) * P.real (B'' j) := by
      rw [measureReal_def, (Indep_iff _ _ P).1 hI _ _ (hpast _ (hA i)) (hB'' j),
        ENNReal.toReal_mul]
      rfl
    have split : ∀ S : Set Ω, MeasurableSet S → P.real S = P.real (S ∩ G) + P.real (S ∩ Gᶜ) :=
      fun S hS => (measureReal_inter_add_sdiff (s := S) hG).symm.trans (by rw [Set.sdiff_eq])
    have hAB := split _ ((hAm i).inter (hBm j))
    have hAB'' := split _ ((hAm i).inter (hB''m j))
    have hB1 := split _ (hBm j)
    have hB2 := split _ (hB''m j)
    have eG : A i ∩ B j ∩ G = A i ∩ B'' j ∩ G := by rw [inter_assoc, e'', ← inter_assoc]
    rw [eG] at hAB
    have r1 : A i ∩ B j ∩ Gᶜ = A i ∩ (B j ∩ Gᶜ) := inter_assoc _ _ _
    have r2 : A i ∩ B'' j ∩ Gᶜ = A i ∩ (B'' j ∩ Gᶜ) := inter_assoc _ _ _
    rw [r1] at hAB
    rw [r2] at hAB''
    have hBG : P.real (B j ∩ G) = P.real (B'' j ∩ G) := by rw [e'']
    have hA0 : 0 ≤ P.real (A i) := measureReal_nonneg
    have n1 : 0 ≤ P.real (A i ∩ (B j ∩ Gᶜ)) := measureReal_nonneg
    have n2 : 0 ≤ P.real (A i ∩ (B'' j ∩ Gᶜ)) := measureReal_nonneg
    have n3 : 0 ≤ P.real (B j ∩ Gᶜ) := measureReal_nonneg
    have n4 : 0 ≤ P.real (B'' j ∩ Gᶜ) := measureReal_nonneg
    have hD : P.real (A i ∩ B j) - P.real (A i) * P.real (B j) =
        (P.real (A i ∩ (B j ∩ Gᶜ)) - P.real (A i ∩ (B'' j ∩ Gᶜ))) -
          P.real (A i) * (P.real (B j ∩ Gᶜ) - P.real (B'' j ∩ Gᶜ)) := by
      rw [hAB, hB1, hBG]
      rw [hAB''] at hind'
      rw [hB2] at hind'
      linarith
    rw [hD, abs_le]
    constructor <;> nlinarith
  have hGc : MeasurableSet Gᶜ := hG.compl
  have s1 : ∑ i, ∑ j, P.real (A i ∩ (B j ∩ Gᶜ)) = P.real Gᶜ := by
    rw [Finset.sum_comm]
    simp_rw [sum_measureReal_inter_eq hAm hdA huA ((hBm _).inter hGc)]
    exact sum_measureReal_inter_eq hBm hdB huB hGc
  have s2 : ∑ i, ∑ j, P.real (A i ∩ (B'' j ∩ Gᶜ)) ≤ P.real Gᶜ := by
    rw [Finset.sum_comm]
    simp_rw [sum_measureReal_inter_eq hAm hdA huA ((hB''m _).inter hGc)]
    exact sum_measureReal_inter_le hB''m hdB'' hGc
  have s3 : ∑ i, P.real (A i) = 1 := by
    have := sum_measureReal_inter_eq (P := P) hAm hdA huA MeasurableSet.univ
    simpa using this
  have s4 : ∑ j, P.real (B j ∩ Gᶜ) = P.real Gᶜ := sum_measureReal_inter_eq hBm hdB huB hGc
  have s5 : ∑ j, P.real (B'' j ∩ Gᶜ) ≤ P.real Gᶜ := sum_measureReal_inter_le hB''m hdB'' hGc
  calc 2⁻¹ * ∑ i, ∑ j, |P.real (A i ∩ B j) - P.real (A i) * P.real (B j)|
      ≤ 2⁻¹ * ∑ i, ∑ j, (P.real (A i ∩ (B j ∩ Gᶜ)) + P.real (A i ∩ (B'' j ∩ Gᶜ)) +
          P.real (A i) * (P.real (B j ∩ Gᶜ) + P.real (B'' j ∩ Gᶜ))) := by
        gcongr with i _ j _
        exact key i j
    _ = 2⁻¹ * (∑ i, ∑ j, P.real (A i ∩ (B j ∩ Gᶜ)) + ∑ i, ∑ j, P.real (A i ∩ (B'' j ∩ Gᶜ)) +
          (∑ i, P.real (A i)) * (∑ j, P.real (B j ∩ Gᶜ) + ∑ j, P.real (B'' j ∩ Gᶜ))) := by
        simp only [Finset.sum_add_distrib, Finset.sum_mul]
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 2⁻¹ * (P.real Gᶜ + P.real Gᶜ + 1 * (P.real Gᶜ + P.real Gᶜ)) := by
        rw [s1, s3, s4]
        gcongr
    _ ≤ 2 * T := by linarith

end EchoBeta

end ExtremeValueTheory
