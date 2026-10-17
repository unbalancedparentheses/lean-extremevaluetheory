/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.Basic
import ExtremeValueTheory.ForMathlib.Probability.PoissonRandomMeasure
import ExtremeValueTheory.RegularVariation.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real

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

/-- Scaling: `∫ max_i f i / (c i / n) = n ∫ max_i f i / c i`. -/
lemma lintegral_iSup_div_inv_mul [Countable ι] {f : ι → S → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (c : ι → ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ s, ⨆ i, f i s / ((n : ℝ≥0∞)⁻¹ * c i) ∂μ = n * ∫⁻ s, ⨆ i, f i s / c i ∂μ := by
  have h (x c : ℝ≥0∞) : x / ((n : ℝ≥0∞)⁻¹ * c) = n * (x / c) := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (a := (n : ℝ≥0∞)⁻¹) (b := c)
      (Or.inl (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)))
      (Or.inl (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hn))), inv_inv, div_eq_mul_inv,
      mul_left_comm]
  simp_rw [h, ← ENNReal.mul_iSup]
  exact lintegral_const_mul _ (Measurable.iSup fun i ↦ (hf i).div_const _)

/-- **Unit Fréchet margins** (before normalization): `P(Y i ≤ c) = exp (-∫ f i dμ / c)`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_spectralMax_le [SFinite μ]
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P) {f : ι → S → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hfi : ∀ i, ∫⁻ s, f i s ∂μ ≠ ∞) (i : ι) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) :
    P {ω | spectralMax f (N ω) i ≤ c} =
      ENNReal.ofReal (Real.exp (-((∫⁻ s, f i s ∂μ) / c).toReal)) := by
  have hint : ∫⁻ s, f i s / c ∂μ = (∫⁻ s, f i s ∂μ) / c := by
    simp_rw [div_eq_mul_inv]; exact lintegral_mul_const _ (hf i)
  have h := hN.measure_forall_spectralMax_le (ι := Unit) (f := fun _ ↦ f i) (fun _ ↦ hf i)
    (c := fun _ ↦ c) (fun _ ↦ hc0) (fun _ ↦ hc)
    (by simpa [hint] using ENNReal.div_ne_top (hfi i) hc0)
  simpa [hint, spectralMax] using h

/-- The maxima of the spectral construction are a.s. finite when every `∫ f i dμ` is finite. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_spectralMax_eq_top [SFinite μ]
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P) {f : ι → S → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hfi : ∀ i, ∫⁻ s, f i s ∂μ ≠ ∞) (i : ι) :
    P {ω | spectralMax f (N ω) i = ∞} = 0 := by
  have := hN.isProbabilityMeasure
  have hmeas : MeasurableSet {ω | spectralMax f (N ω) i ≠ ∞} :=
    (measurableSet_singleton ∞).compl.preimage (measurable_spectralMax hN.measurable hf i)
  have htend : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal (Real.exp (-((∫⁻ s, f i s ∂μ) / n).toReal))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ ↦ (∫⁻ s, f i s ∂μ) / n) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr (hfi i))
    have := ((ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).tendsto
      0).comp ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0)
    have h1 : (ENNReal.ofReal ∘ Real.exp ∘ fun a : ℝ ↦ -a) 0 = 1 := by simp
    rw [h1] at this
    exact this
  have hle : 1 ≤ P {ω | spectralMax f (N ω) i ≠ ∞} := by
    refine le_of_tendsto htend ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    rw [← hN.measure_spectralMax_le hf hfi i (by exact_mod_cast (by omega : n ≠ 0))
      (ENNReal.natCast_ne_top n)]
    exact measure_mono fun ω hω ↦ ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hω
  have hc := prob_compl_eq_one_sub (μ := P) hmeas
  rw [show {ω | spectralMax f (N ω) i ≠ ∞}ᶜ = {ω | spectralMax f (N ω) i = ∞} by ext; simp] at hc
  rw [hc, tsub_eq_zero_of_le hle]

/-- The real random vector `Y = (Y i)_i` of the spectral construction. -/
noncomputable def spectralVector (f : ι → S → ℝ≥0∞) (m : Measure (ℝ × S)) : ι → ℝ :=
  fun i ↦ (spectralMax f m i).toReal

lemma measurable_spectralVector (hN : Measurable N) {f : ι → S → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable fun ω ↦ spectralVector f (N ω) :=
  Measurable.of_eval fun i ↦ (measurable_spectralMax hN hf i).ennreal_toReal

/-- **de Haan's spectral representation, constructive direction, joint law.** For the real vector
`Y i = sup_k ζ_k f i (s_k)` and `y` with positive coordinates,
`P(Y ≤ y) = exp (-∫ max_i f i s / y i dμ(s))`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_spectralVector_le [Fintype ι]
    [SFinite μ] (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P)
    {f : ι → S → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (hfi : ∀ i, ∫⁻ s, f i s ∂μ ≠ ∞)
    {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    P {ω | spectralVector f (N ω) ≤ y} =
      ENNReal.ofReal (Real.exp (-(∫⁻ s, ⨆ i, f i s / ENNReal.ofReal (y i) ∂μ).toReal)) := by
  have hc0 (i : ι) : ENNReal.ofReal (y i) ≠ 0 := (ENNReal.ofReal_pos.2 (hy i)).ne'
  rw [← hN.measure_forall_spectralMax_le hf hc0 (fun i ↦ ENNReal.ofReal_ne_top)
    (lintegral_iSup_div_ne_top hf hfi hc0)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  have hae : ∀ᵐ ω ∂P, ∀ i, spectralMax f (N ω) i ≠ ∞ := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    simpa using hN.measure_spectralMax_eq_top hf hfi i
  filter_upwards [hae] with ω hω
  simp only [Pi.le_def, spectralVector]
  exact forall_congr' fun i ↦ (ENNReal.le_ofReal_iff_toReal_le (hω i) (hy i).le).symm

/-- **Unit Fréchet margins.** If `∫ f i dμ = 1`, then `P(Y i ≤ y) = exp (-1 / y)`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_spectralVector_apply_le [SFinite μ]
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P) {f : ι → S → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hfi : ∀ i, ∫⁻ s, f i s ∂μ = 1) (i : ι) {y : ℝ} (hy : 0 < y) :
    P {ω | spectralVector f (N ω) i ≤ y} = ENNReal.ofReal (Real.exp (-y⁻¹)) := by
  have hfi' (i : ι) : ∫⁻ s, f i s ∂μ ≠ ∞ := by simp [hfi i]
  rw [← (by simpa [hfi, ENNReal.toReal_inv, ENNReal.toReal_ofReal hy.le] using
    hN.measure_spectralMax_le hf hfi' i (ENNReal.ofReal_pos.2 hy).ne' ENNReal.ofReal_ne_top :
      P {ω | spectralMax f (N ω) i ≤ ENNReal.ofReal y} = ENNReal.ofReal (Real.exp (-y⁻¹)))]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  have hae : ∀ᵐ ω ∂P, spectralMax f (N ω) i ≠ ∞ := by
    rw [ae_iff]
    simpa using hN.measure_spectralMax_eq_top hf hfi' i
  filter_upwards [hae] with ω hω
  exact (ENNReal.le_ofReal_iff_toReal_le hω hy.le).symm

/-- **The spectral construction is simple max-stable.** If `N` is a Poisson random measure with
intensity `ζ ^ (-2) dζ ⊗ μ` and `∫ f i dμ = 1` for every `i`, the law of
`Y = (sup_k ζ_k f i (s_k))_i` is simple max-stable. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.isSimpleMaxStable_map_spectralVector
    [Fintype ι] [SFinite μ] (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P)
    {f : ι → S → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (hfi : ∀ i, ∫⁻ s, f i s ∂μ = 1) :
    IsSimpleMaxStable (P.map fun ω ↦ spectralVector f (N ω)) := by
  have := hN.isProbabilityMeasure
  have hfi' (i : ι) : ∫⁻ s, f i s ∂μ ≠ ∞ := by simp [hfi i]
  have hY := measurable_spectralVector hN.measurable hf
  have hIic {y : ι → ℝ} (hy : ∀ i, 0 < y i) : (P.map fun ω ↦ spectralVector f (N ω)) (Iic y) =
      ENNReal.ofReal (Real.exp (-(∫⁻ s, ⨆ i, f i s / ENNReal.ofReal (y i) ∂μ).toReal)) := by
    rw [Measure.map_apply hY measurableSet_Iic]
    exact hN.measure_spectralVector_le hf hfi' hy
  refine ⟨inferInstance, fun i y hy ↦ ?_, fun n hn y hy ↦ ?_⟩
  · rw [Measure.map_apply hY (measurableSet_le (measurable_pi_apply i) measurable_const)]
    exact hN.measure_spectralVector_apply_le hf hfi i hy
  · have hy' (i : ι) : 0 < ((n : ℝ)⁻¹ • y) i := by
      simpa using mul_pos (inv_pos.2 (by exact_mod_cast hn)) (hy i)
    rw [hIic hy, hIic hy']
    have hscale (i : ι) : ENNReal.ofReal (((n : ℝ)⁻¹ • y) i) =
        (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (y i) := by
      rw [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.2 n.cast_nonneg),
        ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]
    simp_rw [hscale]
    rw [lintegral_iSup_div_inv_mul hf _ hn.ne', ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, mul_neg]

end Spectral



/-! ### Existence: every spectral measure gives a simple max-stable law -/

section Existence

universe u

variable {S : Type u} [MeasurableSpace S] {ι : Type*} [Fintype ι]

/-- **Every spectral representation gives a simple max-stable law** ([dHF, Theorem 6.1.9],
"⇐"; [Res87, Proposition 5.11]). If `μ` is an s-finite measure on `S` and `f i ≥ 0` satisfy
`∫ f i dμ = 1`, there is a simple max-stable law with distribution function
`F(y) = exp (-∫ max_i f i s / y i dμ(s))`, namely the law of `Y i = sup_k ζ_k f i (s_k)` for a
Poisson random measure `∑ δ_{(ζ_k, s_k)}` with intensity `ζ ^ (-2) dζ ⊗ μ`. -/
theorem exists_isSimpleMaxStable_of_spectral (μ : Measure S) [SFinite μ]
    {f : ι → S → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (hfi : ∀ i, ∫⁻ s, f i s ∂μ = 1) :
    ∃ ν : Measure (ι → ℝ), IsSimpleMaxStable ν ∧ ∀ y : ι → ℝ, (∀ i, 0 < y i) →
      ν (Iic y) =
        ENNReal.ofReal (Real.exp (-(∫⁻ s, ⨆ i, f i s / ENNReal.ofReal (y i) ∂μ).toReal)) := by
  obtain ⟨Ω, _, P, N, _, hN⟩ := exists_isPoissonRandomMeasure ((radialMeasure 1).prod μ)
  have hY := measurable_spectralVector hN.measurable hf
  refine ⟨P.map fun ω ↦ spectralVector f (N ω), hN.isSimpleMaxStable_map_spectralVector hf hfi,
    fun y hy ↦ ?_⟩
  rw [Measure.map_apply hY measurableSet_Iic]
  exact hN.measure_spectralVector_le hf (fun i ↦ by simp [hfi i]) hy

/-- **Spectral measures on `[0, ∞]^ι`** ([dHF, Theorem 6.1.9], "⇐"). For every s-finite measure
`H` on `ι → [0, ∞]` with `∫ w i dH(w) = 1` (for instance a measure on the unit simplex
normalized this way) there is a simple max-stable law with
`F(y) = exp (-∫ max_i w i / y i dH(w))`. -/
theorem exists_isSimpleMaxStable_of_spectralMeasure (H : Measure (ι → ℝ≥0∞)) [SFinite H]
    (hH : ∀ i, ∫⁻ w, w i ∂H = 1) :
    ∃ ν : Measure (ι → ℝ), IsSimpleMaxStable ν ∧ ∀ y : ι → ℝ, (∀ i, 0 < y i) →
      ν (Iic y) =
        ENNReal.ofReal (Real.exp (-(∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H).toReal)) :=
  exists_isSimpleMaxStable_of_spectral H (fun i ↦ measurable_pi_apply i) hH

end Existence

/-! ### Max-stable processes -/

section Process

variable {S T : Type*} [MeasurableSpace S] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {N : Ω → Measure (ℝ × S)} {μ : Measure S} {W : T → S → ℝ≥0∞}

/-- **de Haan's spectral representation of max-stable processes, constructive direction**
([dHF, Theorem 9.4.1]; [de Haan 1984]). Let `N = ∑ δ_{(ζ_k, s_k)}` be a Poisson random measure on
`ℝ × S` with intensity `ζ ^ (-2) dζ ⊗ μ` and `W t : S → [0, ∞]` with `∫ W t dμ = 1` for every
`t`. Then every finite-dimensional law of the process `Y t = sup_k ζ_k W t (s_k)`
(`spectralVector W (N ω) t`) is simple max-stable.

When `μ` is a probability measure, the `s_k` are i.i.d. with law `μ` given the `ζ_k`, so
`W_k = W · (s_k)` are i.i.d. nonnegative processes with `E W_k t = 1`; taking `S = T → [0, ∞]`
and `W t w = w t`, `μ` is the law of an arbitrary such process. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.isSimpleMaxStable_map_process
    [SFinite μ] (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P)
    (hW : ∀ t, Measurable (W t)) (hW1 : ∀ t, ∫⁻ s, W t s ∂μ = 1) {ι : Type*} [Fintype ι]
    (t : ι → T) :
    IsSimpleMaxStable (P.map fun ω i ↦ spectralVector W (N ω) (t i)) :=
  hN.isSimpleMaxStable_map_spectralVector (f := fun i ↦ W (t i)) (fun i ↦ hW (t i))
    (fun i ↦ hW1 (t i))

/-- **Finite-dimensional distributions of de Haan's process**:
`P(Y t₁ ≤ y₁, …, Y tₙ ≤ yₙ) = exp (-∫ max_i W tᵢ s / yᵢ dμ(s))`, i.e.
`exp (-E max_i W(tᵢ) / yᵢ)` when `μ` is the law of `W`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_process_le
    [SFinite μ] (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P)
    (hW : ∀ t, Measurable (W t)) (hW1 : ∀ t, ∫⁻ s, W t s ∂μ = 1) {ι : Type*} [Fintype ι]
    (t : ι → T) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    P {ω | ∀ i, spectralVector W (N ω) (t i) ≤ y i} =
      ENNReal.ofReal (Real.exp (-(∫⁻ s, ⨆ i, W (t i) s / ENNReal.ofReal (y i) ∂μ).toReal)) :=
  hN.measure_spectralVector_le (f := fun i ↦ W (t i)) (fun i ↦ hW (t i))
    (fun i ↦ by simp [hW1 (t i)]) hy

/-- **Unit Fréchet margins of de Haan's process**: `P(Y t ≤ y) = exp (-1 / y)`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_process_apply_le
    [SFinite μ] (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod μ) P)
    (hW : ∀ t, Measurable (W t)) (hW1 : ∀ t, ∫⁻ s, W t s ∂μ = 1) (t : T) {y : ℝ} (hy : 0 < y) :
    P {ω | spectralVector W (N ω) t ≤ y} = ENNReal.ofReal (Real.exp (-y⁻¹)) :=
  hN.measure_spectralVector_apply_le hW hW1 t hy

/-- The kernel of the **Smith (Gaussian extreme value) model** on `ℝ` ([Smith 1990]): the moving
maximum process `Y t = sup_k ζ_k φ(t - u_k)`, with `φ` the centered Gaussian density of variance
`v` and `∑ δ_{(ζ_k, u_k)}` a Poisson random measure with intensity `ζ ^ (-2) dζ ⊗ du`. -/
noncomputable def smithKernel (v : ℝ≥0) (t u : ℝ) : ℝ≥0∞ := gaussianPDF 0 v (t - u)

lemma lintegral_smithKernel {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    ∫⁻ u, smithKernel v t u = 1 := by
  change ∫⁻ u, gaussianPDF 0 v (t - u) = 1
  rw [lintegral_sub_left_eq_self (fun x ↦ gaussianPDF 0 v x) t,
    lintegral_gaussianPDF_eq_one 0 hv]

lemma measurable_smithKernel (v : ℝ≥0) (t : ℝ) : Measurable (smithKernel v t) :=
  (measurable_gaussianPDF 0 v).comp (measurable_const.sub measurable_id)

/-- The finite-dimensional laws of the Smith model are simple max-stable. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.isSimpleMaxStable_smith
    {N : Ω → Measure (ℝ × ℝ)} (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod volume) P)
    {v : ℝ≥0} (hv : v ≠ 0) {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    IsSimpleMaxStable (P.map fun ω i ↦ spectralVector (smithKernel v) (N ω) (t i)) :=
  hN.isSimpleMaxStable_map_process (measurable_smithKernel v) (lintegral_smithKernel hv) t

end Process

/-! ### Examples: independence and complete dependence -/

section Examples

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {N : Ω → Measure (ℝ × (ι → ℝ≥0∞))}

/-- The spectral measure of **independence**: unit masses at the vertices `e i` of the simplex. -/
noncomputable def independentSpectralMeasure : Measure (ι → ℝ≥0∞) :=
  ∑ i, Measure.dirac (Pi.single i 1)

/-- The spectral measure of **complete dependence**: a unit mass at `(1, …, 1)`. -/
noncomputable def comonotoneSpectralMeasure : Measure (ι → ℝ≥0∞) := Measure.dirac fun _ ↦ 1

instance : IsFiniteMeasure (independentSpectralMeasure (ι := ι)) := by
  unfold independentSpectralMeasure; infer_instance

instance : IsProbabilityMeasure (comonotoneSpectralMeasure (ι := ι)) := by
  unfold comonotoneSpectralMeasure; infer_instance

lemma lintegral_independentSpectralMeasure {g : (ι → ℝ≥0∞) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ w, g w ∂independentSpectralMeasure = ∑ i, g (Pi.single i 1) := by
  rw [independentSpectralMeasure, lintegral_finsetSum_measure]
  exact Finset.sum_congr rfl fun i _ ↦ lintegral_dirac' _ hg

lemma lintegral_apply_independentSpectralMeasure (i : ι) :
    ∫⁻ w, w i ∂independentSpectralMeasure = 1 := by
  rw [lintegral_independentSpectralMeasure (measurable_pi_apply i)]
  simp [Pi.single_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma lintegral_apply_comonotoneSpectralMeasure (i : ι) :
    ∫⁻ w, w i ∂(comonotoneSpectralMeasure (ι := ι)) = 1 := by
  rw [comonotoneSpectralMeasure, lintegral_dirac' _ (measurable_pi_apply i)]

omit [Fintype ι] in
lemma iSup_single_div (i : ι) (c : ι → ℝ≥0∞) :
    ⨆ j, (Pi.single i 1 : ι → ℝ≥0∞) j / c j = (c i)⁻¹ := by
  refine le_antisymm (iSup_le fun j ↦ ?_) (le_iSup_of_le i (by simp))
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- **Independence**: for the vertex spectral measure, `P(Y ≤ y) = ∏ i, exp (-1 / y i)`. -/
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_spectralVector_le_independent
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod independentSpectralMeasure) P)
    {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    P {ω | spectralVector (fun i w ↦ w i) (N ω) ≤ y} =
      ∏ i, ENNReal.ofReal (Real.exp (-(y i)⁻¹)) := by
  rw [hN.measure_spectralVector_le (fun i ↦ measurable_pi_apply i)
    (fun i ↦ by simp [lintegral_apply_independentSpectralMeasure]) hy,
    lintegral_independentSpectralMeasure
      (Measurable.iSup fun j ↦ (measurable_pi_apply j).div_const _)]
  simp_rw [iSup_single_div]
  rw [ENNReal.toReal_sum fun i _ ↦ ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hy i)).ne',
    ← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (hy _).le]

/-- **Complete dependence**: for the spectral measure `δ_(1, …, 1)`,
`P(Y ≤ y) = min_i exp (-1 / y i) = min_i P(Y i ≤ y i)`. -/
omit [DecidableEq ι] in
theorem _root_.ProbabilityTheory.IsPoissonRandomMeasure.measure_spectralVector_le_comonotone
    [Nonempty ι]
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod comonotoneSpectralMeasure) P)
    {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    P {ω | spectralVector (fun i w ↦ w i) (N ω) ≤ y} =
      ⨅ i, ENNReal.ofReal (Real.exp (-(y i)⁻¹)) := by
  rw [hN.measure_spectralVector_le (fun i ↦ measurable_pi_apply i)
    (fun i ↦ by simp [lintegral_apply_comonotoneSpectralMeasure]) hy, comonotoneSpectralMeasure,
    lintegral_dirac' _ (Measurable.iSup fun j ↦ (measurable_pi_apply j).div_const _)]
  obtain ⟨j₀, hj₀⟩ := Finite.exists_min y
  have hsup : ⨆ j, (1 : ℝ≥0∞) / ENNReal.ofReal (y j) = (ENNReal.ofReal (y j₀))⁻¹ := by
    refine le_antisymm (iSup_le fun j ↦ ?_) (le_iSup_of_le j₀ (by simp))
    rw [one_div]
    exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (hj₀ j))
  rw [hsup, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hy j₀).le]
  exact le_antisymm (le_iInf fun j ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    (neg_le_neg (inv_anti₀ (hy j₀) (hj₀ j))))) (iInf_le _ j₀)

end Examples

end ExtremeValueTheory
