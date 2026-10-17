/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.Basic
import ExtremeValueTheory.ForMathlib.Probability.PoissonRandomMeasure
import ExtremeValueTheory.RegularVariation.Multivariate

/-!
# Spectral representation of max-stable vectors and processes

DOC
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section Void

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] {N : Ω → Measure E}
  {ν : Measure E} {P : Measure Ω}

/-- **Void probabilities** of a Poisson random measure: `P(N A = 0) = exp (-ν A)`. -/
lemma _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_apply_eq_zero (hN : IsPoissonRandomMeasure N ν P)
    {A : Set E} (hA : MeasurableSet A) (hνA : ν A ≠ ∞) :
    P {ω | N ω A = 0} = ENNReal.ofReal (Real.exp (-(ν A).toReal)) := by
  have h := (hN.hasLaw hA hνA).map_eq
  have hm : Measurable (Nat.cast : ℕ → ℝ≥0∞) := measurable_from_nat
  have hpre : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' {0} = {0} := by ext n; simp
  calc P {ω | N ω A = 0} = P.map (fun ω ↦ N ω A) {0} := by
        rw [Measure.map_apply (hN.measurable_apply hA) (measurableSet_singleton 0)]; rfl
    _ = _ := by
        rw [h, Measure.map_apply hm (measurableSet_singleton 0), hpre, poissonMeasure_singleton]
        simp [ENNReal.toReal]

/-- `essSup g m ≤ c` iff `m` gives no mass to `{g > c}`. -/
lemma essSup_le_iff_measure_eq_zero {g : E → ℝ≥0∞} {m : Measure E} {c : ℝ≥0∞} :
    essSup g m ≤ c ↔ m {x | c < g x} = 0 := by
  constructor
  · intro h
    have : ∀ᵐ x ∂m, g x ≤ c := (ENNReal.ae_le_essSup g).mono fun x hx ↦ hx.trans h
    simpa [not_le] using ae_iff.1 this
  · intro h
    exact essSup_le_of_ae_le c (ae_iff.2 (by simpa [not_le] using h))

/-- For a measurable random measure, `ω ↦ essSup g (N ω)` is measurable. -/
lemma measurable_essSup_comp (hN : Measurable N) {g : E → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun ω ↦ essSup g (N ω) := by
  refine measurable_of_Iic fun c ↦ ?_
  have : (fun ω ↦ essSup g (N ω)) ⁻¹' Iic c = (fun ω ↦ N ω {x | c < g x}) ⁻¹' {0} := by
    ext ω; simp [essSup_le_iff_measure_eq_zero]
  rw [this]
  exact (Measure.measurable_coe (measurableSet_lt measurable_const hg)).comp hN
    (measurableSet_singleton 0)

/-- **Joint law of the maxima of a Poisson random measure.** If `N` is a Poisson random measure
with intensity `ν`, the "maxima" `essSup (g i) N = max_{x ∈ N} g i x` satisfy
`P(∀ i, max_{x ∈ N} g i x ≤ c i) = exp (-ν (⋃ i, {g i > c i}))`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_forall_essSup_le {ι : Type*} [Countable ι]
    (hN : IsPoissonRandomMeasure N ν P) {g : ι → E → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (c : ι → ℝ≥0∞) (hfin : ν (⋃ i, {x | c i < g i x}) ≠ ∞) :
    P {ω | ∀ i, essSup (g i) (N ω) ≤ c i} =
      ENNReal.ofReal (Real.exp (-(ν (⋃ i, {x | c i < g i x})).toReal)) := by
  have hset : {ω | ∀ i, essSup (g i) (N ω) ≤ c i} = {ω | N ω (⋃ i, {x | c i < g i x}) = 0} := by
    ext ω
    simp only [mem_ofPred_eq, essSup_le_iff_measure_eq_zero, measure_iUnion_null_iff]
  rw [hset]
  exact hN.measure_apply_eq_zero
    (MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const (hg i)) hfin

end Void

/-! ### The radial measure `r ^ (-2) dr` -/

section Radial

lemma radialMeasure_one_Ioi_zero : radialMeasure 1 (Ioi 0) = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  have hu : (0 : ℝ) < ((r : ℝ) + 1)⁻¹ := by positivity
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal (((r : ℝ) + 1)⁻¹ ^ (-1 : ℝ)) := by
        rw [Real.rpow_neg_one, inv_inv, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = radialMeasure 1 (Ioi _) := (radialMeasure_Ioi one_pos hu).symm
    _ ≤ _ := measure_mono (Ioi_subset_Ioi hu.le)

/-- `∫ 1 {r a > c} r ^ (-2) dr = a / c`. -/
lemma radialMeasure_one_setOf_lt_mul {c a : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    radialMeasure 1 {r | c < ENNReal.ofReal r * a} = a / c := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  rcases eq_or_ne a ∞ with rfl | hatop
  · have : {r : ℝ | c < ENNReal.ofReal r * ∞} = Ioi 0 := by
      ext r
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      · intro h
        by_contra hr
        rw [ENNReal.ofReal_of_nonpos (not_lt.1 hr), zero_mul] at h
        exact not_lt_zero h
      · intro hr
        rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hr).ne']
        exact hc.lt_top
    rw [this, radialMeasure_one_Ioi_zero, ENNReal.top_div_of_ne_top hc]
  · have hne : c / a ≠ ∞ := ENNReal.div_ne_top hc ha0
    have hu : 0 < (c / a).toReal := ENNReal.toReal_pos (by simp [hc0, hatop]) hne
    have : {r : ℝ | c < ENNReal.ofReal r * a} = Ioi (c / a).toReal := by
      ext r
      rw [mem_ofPred_eq, mem_Ioi, ← ENNReal.div_lt_iff (Or.inl ha0) (Or.inl hatop),
        ENNReal.lt_ofReal_iff_toReal_lt hne]
    rw [this, radialMeasure_Ioi one_pos hu, Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos hu,
      ENNReal.ofReal_toReal hne, ENNReal.inv_div (Or.inl hatop) (Or.inl ha0)]

/-- `∫ 1 {∃ i, r a i > c i} r ^ (-2) dr = max_i a i / c i`. -/
lemma radialMeasure_one_setOf_exists_lt_mul {ι : Type*} [Countable ι] {c a : ι → ℝ≥0∞}
    (hc0 : ∀ i, c i ≠ 0) (hc : ∀ i, c i ≠ ∞) :
    radialMeasure 1 {r | ∃ i, c i < ENNReal.ofReal r * a i} = ⨆ i, a i / c i := by
  have : {r : ℝ | ∃ i, c i < ENNReal.ofReal r * a i} =
      ⋃ i, {r | c i < ENNReal.ofReal r * a i} := by ext; simp
  rw [this, Directed.measure_iUnion]
  · simp_rw [radialMeasure_one_setOf_lt_mul (hc0 _) (hc _)]
  · intro i j
    have hup (k : ι) : IsUpperSet {r : ℝ | c k < ENNReal.ofReal r * a k} :=
      fun x y hxy (hx : c k < _) ↦ show c k < _ from lt_of_lt_of_le hx (by gcongr)
    rcases (hup i).total (hup j) with h | h
    · exact ⟨j, h, le_rfl⟩
    · exact ⟨i, le_rfl, h⟩

end Radial

/-! ### The spectral construction -/

section Spectral

variable {S : Type*} [MeasurableSpace S] {ι : Type*}

lemma measurable_ofReal_fst_mul {g : S → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun p : ℝ × S ↦ ENNReal.ofReal p.1 * g p.2 :=
  (ENNReal.measurable_ofReal.comp measurable_fst).mul (hg.comp measurable_snd)

/-- **Exponent measure of the spectral construction.** For the measure `r ^ (-2) dr ⊗ μ`,
`ν (⋃ i, {(r, s) | r f i s > c i}) = ∫ max_i f i s / c i dμ(s)`. -/
theorem radialMeasure_prod_iUnion [Countable ι] (μ : Measure S) [SFinite μ]
    {f : ι → S → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) {c : ι → ℝ≥0∞} (hc0 : ∀ i, c i ≠ 0)
    (hc : ∀ i, c i ≠ ∞) :
    ((radialMeasure 1).prod μ) (⋃ i, {p : ℝ × S | c i < ENNReal.ofReal p.1 * f i p.2}) =
      ∫⁻ s, ⨆ i, f i s / c i ∂μ := by
  rw [Measure.prod_apply_symm (MeasurableSet.iUnion fun i ↦
    measurableSet_lt measurable_const (measurable_ofReal_fst_mul (hf i)))]
  refine lintegral_congr fun s ↦ ?_
  rw [← radialMeasure_one_setOf_exists_lt_mul hc0 hc]
  congr 1
  ext r
  simp

/-- The maxima of the spectral construction: for a counting measure `m = ∑ δ_{(r_k, s_k)}` on
`ℝ × S`, `spectralMax f m i = sup_k r_k f i (s_k)`. -/
noncomputable def spectralMax (f : ι → S → ℝ≥0∞) (m : Measure (ℝ × S)) (i : ι) : ℝ≥0∞ :=
  essSup (fun p : ℝ × S ↦ ENNReal.ofReal p.1 * f i p.2) m

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : Ω → Measure (ℝ × S)}
  {μ : Measure S}

lemma measurable_spectralMax (hN : Measurable N) {f : ι → S → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (i : ι) : Measurable fun ω ↦ spectralMax f (N ω) i :=
  measurable_essSup_comp hN (measurable_ofReal_fst_mul (hf i))

/-- **de Haan's spectral representation (constructive direction).** Let `N = ∑ δ_{(ζ_k, s_k)}` be
a Poisson random measure on `ℝ × S` with intensity `ζ ^ (-2) dζ ⊗ μ`, and `Y i = sup_k ζ_k f i s_k`.
Then `P(∀ i, Y i ≤ c i) = exp (-∫ max_i f i s / c i dμ(s))`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_forall_spectralMax_le [Countable ι] [SFinite μ]
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P) {f : ι → S → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) {c : ι → ℝ≥0∞} (hc0 : ∀ i, c i ≠ 0) (hc : ∀ i, c i ≠ ∞)
    (hfin : ∫⁻ s, ⨆ i, f i s / c i ∂μ ≠ ∞) :
    P {ω | ∀ i, spectralMax f (N ω) i ≤ c i} =
      ENNReal.ofReal (Real.exp (-(∫⁻ s, ⨆ i, f i s / c i ∂μ).toReal)) := by
  have h := hN.measure_forall_essSup_le (fun i ↦ measurable_ofReal_fst_mul (hf i)) c
    (by rwa [radialMeasure_prod_iUnion μ hf hc0 hc])
  rwa [radialMeasure_prod_iUnion μ hf hc0 hc] at h

/-- The integral `∫ max_i f i / c i dμ` is finite when every `∫ f i dμ` is. -/
lemma lintegral_iSup_div_ne_top [Fintype ι] {f : ι → S → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (hfi : ∀ i, ∫⁻ s, f i s ∂μ ≠ ∞) {c : ι → ℝ≥0∞} (hc0 : ∀ i, c i ≠ 0) :
    ∫⁻ s, ⨆ i, f i s / c i ∂μ ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ s, ∑ i, f i s / c i ∂μ) ?_
    (lintegral_mono fun s ↦ iSup_le fun i ↦
      Finset.single_le_sum (f := fun i ↦ f i s / c i) (fun _ _ ↦ zero_le) (Finset.mem_univ i))
  rw [lintegral_finsetSum _ fun i _ ↦ (hf i).div_const _]
  refine ENNReal.sum_ne_top.2 fun i _ ↦ ?_
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ (hf i)]
  exact ENNReal.mul_ne_top (hfi i) (ENNReal.inv_ne_top.2 (hc0 i))

end Spectral


end ExtremeValueTheory
