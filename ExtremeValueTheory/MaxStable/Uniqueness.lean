/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.Converse

/-!
# Uniqueness of the spectral measure

A simple max-stable law `μ` on `ℝ^ι` (`ι` finite) has a spectral measure `H` on the unit sphere
`{w ∈ [0, 1]^ι : max_i w i = 1}` of the sup norm (`IsSimpleMaxStable.exists_hasSpectralMeasure`).
This file shows that `H` is unique: a finite measure on the sphere is determined by the
integrals `∫ max_i w i / y i dH(w)`, `y ∈ (0, ∞)^ι` ([dHF, Theorem 6.1.9]; [Res87, Proposition
5.11]).

## The proof

We use the exponent-measure route. For a measure `H` on `[0, ∞]^ι` let

  `ν_H = image of r ^ (-2) dr ⊗ H under (r, w) ↦ r w`

(`spectralExponentMeasure H`). By the computation of `MaxStable/Spectral.lean`, the measure of the
complement of a lower orthant is the spectral integral:

  `ν_H {x | ∃ i, d i < x i} = ∫ max_i w i / d i dH(w)`

(`spectralExponentMeasure_exceedSet`), also for thresholds `d i = ∞` (the coordinate `i` is then
dropped; this case is reached by monotone limits, `lintegral_iSup_div_eq_of_forall`). Equality of
`ν_H` and `ν_H'` on these sets propagates, by inclusion–exclusion (an induction on the number of
constrained coordinates, `measure_upperSet_inter_exceedSet_eq`), to the sets
`{x | ∀ i ∈ K, c i < x i} ∩ {x | ∃ i, d i < x i}`. The open upper orthants
`{x | ∀ i, c i ≠ 0 → c i < x i}` form a π-system generating the Borel σ-algebra of `[0, ∞]^ι`
(`generateFrom_upperOrthant`), so `ν_H` and `ν_H'` agree on the region `{x | ∃ i, 1 < x i}`, where
they are finite. Finally `H` is the angular part of `ν_H`: when `H` lives on the sphere,

  `ν_H {x | 1 < max_i x i, x / max_i x i ∈ B} = H B`

(`spectralExponentMeasure_angularSet`), since `r ^ (-2) dr` gives mass `1` to `(1, ∞)`.

## Main results

* `spectralExponentMeasure H`: the exponent measure `r ^ (-2) dr ⊗ H` in polar coordinates.
* `eq_of_lintegral_iSup_div_eq`: two finite measures on the sup-norm sphere with the same
  integrals `∫ max_i w i / y i dH`, `y ∈ (0, ∞)^ι`, are equal.
* `HasSpectralMeasure.unique`: **the spectral measure on the sphere is unique**.
* `IsSimpleMaxStable.existsUnique_hasSpectralMeasure`: every simple max-stable law has exactly one
  finite spectral measure on the sphere.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 6.1.9 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Proposition 5.11 [Res87].
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ExtremeValueTheory

variable {ι : Type*}

/-! ### The exponent measure of a spectral measure -/

section Cone

/-- The cone map `(r, w) ↦ r w` from `ℝ × [0, ∞]^ι` to `[0, ∞]^ι`. -/
noncomputable def coneMap (p : ℝ × (ι → ℝ≥0∞)) : ι → ℝ≥0∞ := fun i ↦ ENNReal.ofReal p.1 * p.2 i

lemma measurable_coneMap : Measurable (coneMap (ι := ι)) :=
  Measurable.of_eval fun i ↦
    (ENNReal.measurable_ofReal.comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)

/-- The **exponent measure** of a spectral measure `H`: the image of `r ^ (-2) dr ⊗ H` under
`(r, w) ↦ r w`. -/
noncomputable def spectralExponentMeasure (H : Measure (ι → ℝ≥0∞)) : Measure (ι → ℝ≥0∞) :=
  ((radialMeasure 1).prod H).map coneMap

/-- The complement `{x | ∃ i, d i < x i}` of the lower orthant `[0, d]`. -/
def exceedSet (d : ι → ℝ≥0∞) : Set (ι → ℝ≥0∞) := {x | ∃ i, d i < x i}

/-- The open upper orthant `{x | ∀ i ∈ K, c i < x i}` in the coordinates `K`. -/
def upperSet (K : Finset ι) (c : ι → ℝ≥0∞) : Set (ι → ℝ≥0∞) := {x | ∀ i ∈ K, c i < x i}

/-- The open upper orthant `{x | ∀ i, c i ≠ 0 → c i < x i}`: the coordinates with `c i = 0` are
unconstrained. -/
def upperOrthant (c : ι → ℝ≥0∞) : Set (ι → ℝ≥0∞) := {x | ∀ i, c i ≠ 0 → c i < x i}

lemma measurableSet_exceedSet [Countable ι] (d : ι → ℝ≥0∞) : MeasurableSet (exceedSet d) := by
  simp only [exceedSet, ofPred_exists]
  exact MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const (measurable_pi_apply i)

lemma measurableSet_upperSet (K : Finset ι) (c : ι → ℝ≥0∞) : MeasurableSet (upperSet K c) := by
  have : upperSet K c = ⋂ i ∈ K, {x | c i < x i} := by ext; simp [upperSet]
  rw [this]
  exact Finset.measurableSet_biInter K fun i _ ↦ measurableSet_lt measurable_const
    (measurable_pi_apply i)

lemma upperOrthant_eq_upperSet [Fintype ι] (c : ι → ℝ≥0∞) [DecidablePred fun i ↦ c i ≠ 0] :
    upperOrthant c = upperSet (Finset.univ.filter fun i ↦ c i ≠ 0) c := by
  ext; simp [upperOrthant, upperSet]

lemma measurableSet_upperOrthant [Fintype ι] (c : ι → ℝ≥0∞) : MeasurableSet (upperOrthant c) := by
  classical
  rw [upperOrthant_eq_upperSet]
  exact measurableSet_upperSet _ _

/-- `∫ 1 {r a > c} r ^ (-2) dr = a / c`, also for `c = ∞`. -/
lemma radialMeasure_one_setOf_lt_mul' {c a : ℝ≥0∞} (hc0 : c ≠ 0) :
    radialMeasure 1 {r | c < ENNReal.ofReal r * a} = a / c := by
  rcases eq_or_ne c ∞ with rfl | hc
  · have : {r : ℝ | ∞ < ENNReal.ofReal r * a} = ∅ := by
      ext r
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact le_top
    rw [this, measure_empty, ENNReal.div_top]
  · exact radialMeasure_one_setOf_lt_mul hc0 hc

/-- `∫ 1 {∃ i, r a i > c i} r ^ (-2) dr = max_i a i / c i`, also for infinite thresholds. -/
lemma radialMeasure_one_setOf_exists_lt_mul' [Countable ι] {c a : ι → ℝ≥0∞}
    (hc0 : ∀ i, c i ≠ 0) :
    radialMeasure 1 {r | ∃ i, c i < ENNReal.ofReal r * a i} = ⨆ i, a i / c i := by
  have : {r : ℝ | ∃ i, c i < ENNReal.ofReal r * a i} =
      ⋃ i, {r | c i < ENNReal.ofReal r * a i} := by ext; simp
  rw [this, Directed.measure_iUnion]
  · simp_rw [radialMeasure_one_setOf_lt_mul' (hc0 _)]
  · intro i j
    have hup (k : ι) : IsUpperSet {r : ℝ | c k < ENNReal.ofReal r * a k} :=
      fun x y hxy (hx : c k < _) ↦ show c k < _ from lt_of_lt_of_le hx (by gcongr)
    rcases (hup i).total (hup j) with h | h
    · exact ⟨j, h, le_rfl⟩
    · exact ⟨i, le_rfl, h⟩

/-- **The exponent measure of the complement of a lower orthant** is the spectral integral:
`ν_H {x | ∃ i, d i < x i} = ∫ max_i w i / d i dH(w)`. -/
theorem spectralExponentMeasure_exceedSet [Countable ι] {H : Measure (ι → ℝ≥0∞)} [SFinite H]
    {d : ι → ℝ≥0∞} (hd : ∀ i, d i ≠ 0) :
    spectralExponentMeasure H (exceedSet d) = ∫⁻ w, ⨆ i, w i / d i ∂H := by
  rw [spectralExponentMeasure, Measure.map_apply measurable_coneMap (measurableSet_exceedSet d),
    Measure.prod_apply_symm (measurable_coneMap (measurableSet_exceedSet d))]
  refine lintegral_congr fun w ↦ ?_
  rw [← radialMeasure_one_setOf_exists_lt_mul' hd]
  rfl

lemma lintegral_apply_ne_top_of_le_one {H : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure H]
    (hH : ∀ᵐ w ∂H, ∀ i, w i ≤ 1) (i : ι) : ∫⁻ w, w i ∂H ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂H) ?_ (lintegral_mono_ae (hH.mono fun w hw ↦ hw i))
  rw [lintegral_one]
  exact measure_ne_top H univ

/-- The `H`-a.e. bound `w ≤ 1` on the sup-norm sphere. -/
lemma ae_le_one_of_ae_iSup_eq_one {H : Measure (ι → ℝ≥0∞)} (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    ∀ᵐ w ∂H, ∀ i, w i ≤ 1 :=
  hH.mono fun w hw i ↦ hw ▸ le_iSup (fun i ↦ w i) i

lemma ae_ne_top_of_ae_le_one {H : Measure (ι → ℝ≥0∞)} (hH : ∀ᵐ w ∂H, ∀ i, w i ≤ 1) :
    ∀ᵐ w ∂H, ∀ i, w i ≠ ∞ :=
  hH.mono fun _ hw i ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hw i)

/-- On `[0, 1]^ι`, the exponent measure of `{x | ∃ i, d i < x i}` is finite. -/
lemma spectralExponentMeasure_exceedSet_ne_top [Fintype ι] {H : Measure (ι → ℝ≥0∞)}
    [IsFiniteMeasure H] (hH : ∀ᵐ w ∂H, ∀ i, w i ≤ 1) {d : ι → ℝ≥0∞} (hd : ∀ i, d i ≠ 0) :
    spectralExponentMeasure H (exceedSet d) ≠ ∞ := by
  rw [spectralExponentMeasure_exceedSet hd]
  exact lintegral_iSup_div_ne_top (fun i ↦ measurable_pi_apply i)
    (lintegral_apply_ne_top_of_le_one hH) hd

/-- The angular region `{x | 1 < max_i x i, x / max_i x i ∈ B}`. -/
def angularSet (B : Set (ι → ℝ≥0∞)) : Set (ι → ℝ≥0∞) :=
  {x | 1 < ⨆ i, x i ∧ (fun i ↦ x i / ⨆ j, x j) ∈ B}

lemma measurableSet_angularSet [Countable ι] {B : Set (ι → ℝ≥0∞)} (hB : MeasurableSet B) :
    MeasurableSet (angularSet B) := by
  have hsup : Measurable fun x : ι → ℝ≥0∞ ↦ ⨆ i, x i :=
    Measurable.iSup fun i ↦ measurable_pi_apply i
  refine (measurableSet_lt measurable_const hsup).inter ?_
  exact hB.preimage (Measurable.of_eval fun i ↦ (measurable_pi_apply i).div hsup)

lemma angularSet_subset_exceedSet (B : Set (ι → ℝ≥0∞)) : angularSet B ⊆ exceedSet 1 :=
  fun _ hx ↦ lt_iSup_iff.1 hx.1

/-- **`H` is the angular part of its exponent measure**: for `H` on the sup-norm sphere,
`ν_H {x | 1 < max_i x i, x / max_i x i ∈ B} = H B`. -/
theorem spectralExponentMeasure_angularSet [Countable ι] {H : Measure (ι → ℝ≥0∞)} [SFinite H]
    (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) {B : Set (ι → ℝ≥0∞)} (hB : MeasurableSet B) :
    spectralExponentMeasure H (angularSet B) = H B := by
  rw [spectralExponentMeasure, Measure.map_apply measurable_coneMap (measurableSet_angularSet hB),
    Measure.prod_apply_symm (measurable_coneMap (measurableSet_angularSet hB)),
    ← lintegral_indicator_one hB]
  refine lintegral_congr_ae (hH.mono fun w hw ↦ ?_)
  have hset : (fun r : ℝ ↦ (r, w)) ⁻¹' (coneMap ⁻¹' angularSet B) = {r | 1 < r ∧ w ∈ B} := by
    ext r
    simp only [mem_preimage, angularSet, coneMap, mem_ofPred_eq]
    rw [← ENNReal.mul_iSup, hw, mul_one, ENNReal.one_lt_ofReal]
    refine and_congr_right fun hr ↦ ?_
    have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 (one_pos.trans hr)).ne'
    have : (fun i ↦ ENNReal.ofReal r * w i / ENNReal.ofReal r) = w := by
      ext i
      rw [mul_comm]; exact ENNReal.mul_div_cancel_right h0 ENNReal.ofReal_ne_top
    rw [this]
  dsimp only
  rw [hset]
  by_cases hwB : w ∈ B
  · simp only [hwB, and_true, indicator_of_mem hwB, Pi.one_apply]
    rw [show {r : ℝ | 1 < r} = Ioi 1 from rfl, radialMeasure_Ioi one_pos one_pos]
    simp
  · simp [hwB]

lemma upperSet_empty (c : ι → ℝ≥0∞) : upperSet ∅ c = univ := by ext; simp [upperSet]

lemma upperSet_insert [DecidableEq ι] (j : ι) (K : Finset ι) (c : ι → ℝ≥0∞) :
    upperSet (insert j K) c = upperSet K c ∩ {x | c j < x j} := by
  ext; simp [upperSet, and_comm]

lemma exceedSet_update_top [DecidableEq ι] (j : ι) (a : ℝ≥0∞) :
    exceedSet (Function.update (fun _ ↦ ∞) j a) = {x | a < x j} := by
  ext x
  simp only [exceedSet, mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hij : i = j
    · subst hij; simpa using hi
    · simp [Function.update_of_ne hij] at hi
  · intro h
    exact ⟨j, by simpa using h⟩

lemma exceedSet_union (d e : ι → ℝ≥0∞) : exceedSet d ∪ exceedSet e = exceedSet (d ⊓ e) := by
  ext; simp [exceedSet, exists_or]

lemma isPiSystem_upperOrthant : IsPiSystem (range (upperOrthant (ι := ι))) := by
  rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ -
  refine ⟨c ⊔ c', ?_⟩
  ext x
  simp only [upperOrthant, mem_inter_iff, mem_ofPred_eq]
  rw [← forall_and]
  refine forall_congr' fun i ↦ ?_
  by_cases h : c i = 0 <;> by_cases h' : c' i = 0 <;> simp [h, h']

lemma upperOrthant_update_zero [DecidableEq ι] (i : ι) {a : ℝ≥0∞} (ha : a ≠ 0) :
    upperOrthant (Function.update 0 i a) = {x | a < x i} := by
  ext x
  simp only [upperOrthant, mem_ofPred_eq]
  constructor
  · intro h
    simpa using h i (by simpa using ha)
  · intro h j hj
    by_cases hji : j = i
    · subst hji; simpa using h
    · simp [Function.update_of_ne hji] at hj

end Cone

/-! ### Uniqueness of the exponent measure from its values on lower orthants -/

section Ext

variable [Fintype ι]

/-- **Inclusion–exclusion for the exponent measure**: two measures that agree, and are finite, on
the complements of lower orthants `{x | ∃ i, d i < x i}` (`d i ∈ (0, ∞]`) agree on all the sets
`{x | ∀ i ∈ K, c i < x i} ∩ {x | ∃ i, d i < x i}`. -/
theorem measure_upperSet_inter_exceedSet_eq {ν ν' : Measure (ι → ℝ≥0∞)}
    (hfin : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) ≠ ∞)
    (heq : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) = ν' (exceedSet d))
    (K : Finset ι) (c : ι → ℝ≥0∞) (hc : ∀ i ∈ K, c i ≠ 0) (d : ι → ℝ≥0∞) (hd : ∀ i, d i ≠ 0) :
    ν (upperSet K c ∩ exceedSet d) = ν' (upperSet K c ∩ exceedSet d) := by
  classical
  induction K using Finset.induction_on generalizing d with
  | empty => simpa [upperSet_empty] using heq d hd
  | insert j K hj ih =>
    have hcK : ∀ i ∈ K, c i ≠ 0 := fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
    set e : ι → ℝ≥0∞ := Function.update (fun _ ↦ ∞) j (c j) with he_def
    have he : ∀ i, e i ≠ 0 := fun i ↦ by
      by_cases hij : i = j
      · subst hij; simpa [he_def] using hc i (Finset.mem_insert_self i K)
      · simp [he_def, Function.update_of_ne hij]
    have hde : ∀ i, (d ⊓ e) i ≠ 0 := fun i ↦
      (lt_inf_iff.2 ⟨pos_iff_ne_zero.2 (hd i), pos_iff_ne_zero.2 (he i)⟩).ne'
    set X := upperSet K c ∩ exceedSet d
    set Y := upperSet K c ∩ exceedSet e
    have hY : MeasurableSet Y := (measurableSet_upperSet K c).inter (measurableSet_exceedSet e)
    have hXY : X ∪ Y = upperSet K c ∩ exceedSet (d ⊓ e) := by
      rw [← exceedSet_union, inter_union_distrib_left]
    have hXY' : X ∩ Y = upperSet (insert j K) c ∩ exceedSet d := by
      rw [upperSet_insert, ← exceedSet_update_top j (c j), ← he_def]
      ext x; simp only [X, Y, mem_inter_iff]; tauto
    have h1 := measure_union_add_inter (μ := ν) X hY
    have h2 := measure_union_add_inter (μ := ν') X hY
    rw [hXY, hXY'] at h1 h2
    rw [ih hcK d hd, ih hcK e he, ← h2, ih hcK (d ⊓ e) hde] at h1
    have hne : ν' (upperSet K c ∩ exceedSet (d ⊓ e)) ≠ ∞ := by
      rw [← ih hcK (d ⊓ e) hde]
      exact ne_top_of_le_ne_top (hfin _ hde) (measure_mono inter_subset_right)
    exact (ENNReal.add_right_inj hne).1 h1

/-- The open upper orthants generate the Borel σ-algebra of `[0, ∞]^ι`. -/
theorem generateFrom_upperOrthant :
    (MeasurableSpace.pi : MeasurableSpace (ι → ℝ≥0∞)) =
      MeasurableSpace.generateFrom (range (upperOrthant (ι := ι))) := by
  classical
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · let m : MeasurableSpace (ι → ℝ≥0∞) := MeasurableSpace.generateFrom (range upperOrthant)
    have hcoord : ∀ i, Measurable[m] fun x : ι → ℝ≥0∞ ↦ x i := fun i ↦ by
      refine measurable_of_Ioi fun a ↦ ?_
      rcases eq_or_ne a 0 with rfl | ha
      · have : (fun x : ι → ℝ≥0∞ ↦ x i) ⁻¹' Ioi 0 =
            ⋃ n : ℕ, upperOrthant (Function.update 0 i ((n : ℝ≥0∞)⁻¹)) := by
          ext x
          simp only [mem_preimage, mem_Ioi, mem_iUnion,
            upperOrthant_update_zero i (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)),
            mem_ofPred_eq]
          exact ⟨fun h ↦ ENNReal.exists_inv_nat_lt h.ne', fun ⟨n, hn⟩ ↦ bot_le.trans_lt hn⟩
        rw [this]
        exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
      · have : (fun x : ι → ℝ≥0∞ ↦ x i) ⁻¹' Ioi a = upperOrthant (Function.update 0 i a) := by
          rw [upperOrthant_update_zero i ha]; rfl
        rw [this]
        exact MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
    have := measurable_pi_iff.2 hcoord
    exact fun s hs ↦ this hs
  · rintro _ ⟨c, rfl⟩
    exact measurableSet_upperOrthant c

/-- Two measures on `[0, ∞]^ι` that agree, and are finite, on all complements of lower orthants
`{x | ∃ i, d i < x i}` (`d i ∈ (0, ∞]`) agree on the region `{x | ∃ i, 1 < x i}`. -/
theorem restrict_exceedSet_one_eq {ν ν' : Measure (ι → ℝ≥0∞)}
    (hfin : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) ≠ ∞)
    (heq : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) = ν' (exceedSet d)) :
    ν.restrict (exceedSet 1) = ν'.restrict (exceedSet 1) := by
  classical
  have h1 : ∀ i, (1 : ι → ℝ≥0∞) i ≠ 0 := fun _ ↦ one_ne_zero
  have : IsFiniteMeasure (ν.restrict (exceedSet 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (hfin 1 h1).lt_top⟩
  refine ext_of_generate_finite _ generateFrom_upperOrthant isPiSystem_upperOrthant ?_ ?_
  · rintro _ ⟨c, rfl⟩
    rw [Measure.restrict_apply (measurableSet_upperOrthant c),
      Measure.restrict_apply (measurableSet_upperOrthant c), upperOrthant_eq_upperSet]
    exact measure_upperSet_inter_exceedSet_eq hfin heq _ c (fun i hi ↦ by simpa using hi) 1 h1
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    exact heq 1 h1

end Ext

/-! ### Uniqueness of the spectral measure -/

section Unique

variable [Fintype ι]

/-- `max_i w i / min (d i, n + 1)` decreases to `max_i w i / d i` for finite `w`. -/
lemma iInf_iSup_div_min_eq {w d : ι → ℝ≥0∞} (hw : ∀ i, w i ≠ ∞) :
    ⨅ n : ℕ, ⨆ i, w i / (d i ⊓ ((n : ℝ≥0∞) + 1)) = ⨆ i, w i / d i := by
  rw [iInf_iSup_of_antitone]
  · refine iSup_congr fun i ↦ ?_
    rcases eq_or_ne (d i) ∞ with hd | hd
    · simp only [hd, top_inf_eq, ENNReal.div_top]
      rcases eq_or_ne (w i) 0 with h0 | h0
      · simp [h0]
      simp_rw [div_eq_mul_inv]
      rw [← ENNReal.mul_iInf_of_ne h0 (hw i), ← ENNReal.inv_iSup, ← ENNReal.iSup_add,
        ENNReal.iSup_natCast]
      simp
    · refine le_antisymm ?_ (le_iInf fun n ↦ ENNReal.div_le_div_left inf_le_left _)
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hd
      refine iInf_le_of_le n (le_of_eq ?_)
      rw [inf_eq_left.2 (hn.le.trans le_self_add)]
  · intro i m n hmn
    refine ENNReal.div_le_div_left (inf_le_inf_left _ ?_) _
    gcongr

lemma inf_add_one_ne_zero {a : ℝ≥0∞} (ha : a ≠ 0) (n : ℕ) : a ⊓ ((n : ℝ≥0∞) + 1) ≠ 0 :=
  (lt_inf_iff.2 ⟨pos_iff_ne_zero.2 ha, by positivity⟩).ne'

lemma inf_add_one_ne_top (a : ℝ≥0∞) (n : ℕ) : a ⊓ ((n : ℝ≥0∞) + 1) ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) inf_le_right

omit [Fintype ι] in
lemma antitone_iSup_div_inf (d : ι → ℝ≥0∞) :
    Antitone fun n : ℕ ↦ fun w : ι → ℝ≥0∞ ↦ ⨆ i, w i / (d i ⊓ ((n : ℝ≥0∞) + 1)) :=
  fun m n hmn w ↦ iSup_mono fun i ↦ ENNReal.div_le_div_left
    (inf_le_inf_left _ (by gcongr)) _

/-- The spectral integral at thresholds in `(0, ∞]^ι` is the decreasing limit of the spectral
integrals at the finite thresholds `min (d i, n + 1)`. -/
theorem lintegral_iSup_div_eq_iInf {G : Measure (ι → ℝ≥0∞)} (hG : ∀ᵐ w ∂G, ∀ i, w i ≠ ∞)
    (hGfin : ∀ i, ∫⁻ w, w i ∂G ≠ ∞) {d : ι → ℝ≥0∞} (hd : ∀ i, d i ≠ 0) :
    ∫⁻ w, ⨆ i, w i / d i ∂G = ⨅ n : ℕ, ∫⁻ w, ⨆ i, w i / (d i ⊓ ((n : ℝ≥0∞) + 1)) ∂G := by
  rw [← lintegral_iInf (fun n ↦ Measurable.iSup fun i ↦ (measurable_pi_apply i).div_const _)
    (antitone_iSup_div_inf d) (lintegral_iSup_div_ne_top (fun i ↦ measurable_pi_apply i)
      hGfin fun i ↦ inf_add_one_ne_zero (hd i) 0)]
  exact lintegral_congr_ae (hG.mono fun w hw ↦ (iInf_iSup_div_min_eq hw).symm)

/-- Equality of the spectral integrals at finite thresholds `y ∈ (0, ∞)^ι` extends to thresholds
in `(0, ∞]^ι`. -/
theorem lintegral_iSup_div_eq_of_forall {H H' : Measure (ι → ℝ≥0∞)}
    (hH : ∀ᵐ w ∂H, ∀ i, w i ≠ ∞) (hH' : ∀ᵐ w ∂H', ∀ i, w i ≠ ∞)
    (hfin : ∀ i, ∫⁻ w, w i ∂H ≠ ∞) (hfin' : ∀ i, ∫⁻ w, w i ∂H' ≠ ∞)
    (heq : ∀ y : ι → ℝ, (∀ i, 0 < y i) →
      ∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H = ∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H')
    {d : ι → ℝ≥0∞} (hd : ∀ i, d i ≠ 0) :
    ∫⁻ w, ⨆ i, w i / d i ∂H = ∫⁻ w, ⨆ i, w i / d i ∂H' := by
  rw [lintegral_iSup_div_eq_iInf hH hfin hd, lintegral_iSup_div_eq_iInf hH' hfin' hd]
  refine iInf_congr fun n ↦ ?_
  have := heq (fun i ↦ (d i ⊓ ((n : ℝ≥0∞) + 1)).toReal) fun i ↦
    ENNReal.toReal_pos (inf_add_one_ne_zero (hd i) n) (inf_add_one_ne_top _ n)
  simpa only [ENNReal.ofReal_toReal (inf_add_one_ne_top _ n)] using this

/-- **Uniqueness of the spectral measure on the sup-norm sphere**: two finite measures `H`, `H'`
on `[0, ∞]^ι`, concentrated on `{w | max_i w i = 1}`, with
`∫ max_i w i / y i dH(w) = ∫ max_i w i / y i dH'(w)` for every `y ∈ (0, ∞)^ι`, are equal. -/
theorem eq_of_lintegral_iSup_div_eq {H H' : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure H]
    [IsFiniteMeasure H'] (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) (hH' : ∀ᵐ w ∂H', ⨆ i, w i = 1)
    (heq : ∀ y : ι → ℝ, (∀ i, 0 < y i) →
      ∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H = ∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H') :
    H = H' := by
  have hle := ae_le_one_of_ae_iSup_eq_one hH
  have hle' := ae_le_one_of_ae_iSup_eq_one hH'
  have hnt := ae_ne_top_of_ae_le_one hle
  have hnt' := ae_ne_top_of_ae_le_one hle'
  have hfin := lintegral_apply_ne_top_of_le_one hle
  have hfin' := lintegral_apply_ne_top_of_le_one hle'
  have hres : (spectralExponentMeasure H).restrict (exceedSet 1) =
      (spectralExponentMeasure H').restrict (exceedSet 1) := by
    refine restrict_exceedSet_one_eq (fun d hd ↦ spectralExponentMeasure_exceedSet_ne_top hle hd)
      fun d hd ↦ ?_
    rw [spectralExponentMeasure_exceedSet hd, spectralExponentMeasure_exceedSet hd]
    exact lintegral_iSup_div_eq_of_forall hnt hnt' hfin hfin' heq hd
  ext B hB
  rw [← spectralExponentMeasure_angularSet hH hB, ← spectralExponentMeasure_angularSet hH' hB,
    ← inter_eq_left.2 (angularSet_subset_exceedSet B),
    ← Measure.restrict_apply (measurableSet_angularSet hB),
    ← Measure.restrict_apply (measurableSet_angularSet hB), hres]

/-- On the sup-norm sphere, the spectral integral `∫ max_i w i / y i dH` is finite. -/
lemma lintegral_iSup_div_ofReal_ne_top {H : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure H]
    (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    ∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H ≠ ∞ :=
  lintegral_iSup_div_ne_top (fun i ↦ measurable_pi_apply i)
    (lintegral_apply_ne_top_of_le_one (ae_le_one_of_ae_iSup_eq_one hH))
    fun i ↦ (ENNReal.ofReal_pos.2 (hy i)).ne'

/-- **The spectral measure on the sphere is unique** ([dHF, Theorem 6.1.9]): two finite spectral
measures of the same law, both concentrated on the unit sphere `{w | max_i w i = 1}` of the sup
norm, are equal. -/
theorem HasSpectralMeasure.unique {ν : Measure (ι → ℝ)} {H H' : Measure (ι → ℝ≥0∞)}
    [IsFiniteMeasure H] [IsFiniteMeasure H'] (hνH : HasSpectralMeasure ν H)
    (hνH' : HasSpectralMeasure ν H') (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hH' : ∀ᵐ w ∂H', ⨆ i, w i = 1) : H = H' := by
  refine eq_of_lintegral_iSup_div_eq hH hH' fun y hy ↦ ?_
  have := (hνH.maxStableExponent_eq hy).symm.trans (hνH'.maxStableExponent_eq hy)
  exact (ENNReal.toReal_eq_toReal_iff' (lintegral_iSup_div_ofReal_ne_top hH hy)
    (lintegral_iSup_div_ofReal_ne_top hH' hy)).1 this

/-- Every simple max-stable law has **exactly one** finite spectral measure on the sup-norm
sphere; it is normalized by `∫ w i dH = 1`. -/
theorem IsSimpleMaxStable.existsUnique_hasSpectralMeasure {μ : Measure (ι → ℝ)}
    (h : IsSimpleMaxStable μ) :
    ∃! H : Measure (ι → ℝ≥0∞), IsFiniteMeasure H ∧ (∀ᵐ w ∂H, ⨆ i, w i = 1) ∧
      HasSpectralMeasure μ H := by
  obtain ⟨H, hfin, -, hsph, -, hS⟩ := h.exists_hasSpectralMeasure
  refine ⟨H, ⟨hfin, hsph, hS⟩, fun H' ⟨hfin', hsph', hS'⟩ ↦ ?_⟩
  exact (HasSpectralMeasure.unique hS hS' hsph hsph').symm

end Unique

end ExtremeValueTheory
