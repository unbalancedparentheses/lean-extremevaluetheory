/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.EchoProcess

/-!
# A block-length phase transition for the echo process

DOCSTRING
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Sums of probabilities as integrals of counting functions -/

section Counting

variable {μ : Measure ℝ}

/-- A `0/1` series with finitely many nonzero terms sums to the number of them. -/
theorem tsum_indicator_one_eq_card {S : ℕ → Set ℝ} {z : ℝ} {F : Finset ℕ}
    (hF : ∀ k, z ∈ S k ↔ k ∈ F) :
    ∑' k, (S k).indicator (1 : ℝ → ℝ≥0∞) z = F.card := by
  rw [tsum_eq_sum (s := F) fun k hk => indicator_of_notMem (fun h => hk ((hF k).1 h)) _,
    Finset.sum_congr rfl fun k hk => indicator_of_mem ((hF k).2 hk) _]
  simp

/-- `∑ₖ μ(Sₖ) = ∫ #{k : z ∈ Sₖ} dμ(z)`. -/
theorem tsum_measure_eq_lintegral_count {S : ℕ → Set ℝ} (hS : ∀ k, MeasurableSet (S k))
    {f : ℝ → ℕ} (hcount : ∀ z, ∑' k, (S k).indicator (1 : ℝ → ℝ≥0∞) z = f z) :
    ∑' k, μ (S k) = ∫⁻ z, (f z : ℝ≥0∞) ∂μ := by
  simp_rw [← lintegral_indicator_one (μ := μ) (hS _)]
  rw [← lintegral_tsum fun k => (measurable_one.indicator (hS k)).aemeasurable]
  exact lintegral_congr fun z => hcount z

/-- **Sums of probabilities as integrals of counting functions**: if every `z` lies in exactly
`f z` of the sets `Sₖ` and `∫ f dμ < ∞`, then `∑ₖ μ(Sₖ) = ∫ f dμ` (and `f` is integrable). -/
theorem hasSum_measureReal_of_count {S : ℕ → Set ℝ} (hS : ∀ k, MeasurableSet (S k))
    {f : ℝ → ℕ} (hf : Measurable f)
    (hcount : ∀ z, ∑' k, (S k).indicator (1 : ℝ → ℝ≥0∞) z = f z)
    (hfin : ∫⁻ z, (f z : ℝ≥0∞) ∂μ ≠ ∞) :
    HasSum (fun k => μ.real (S k)) (∫ z, (f z : ℝ) ∂μ) ∧ Integrable (fun z => (f z : ℝ)) μ := by
  have h1 := tsum_measure_eq_lintegral_count (μ := μ) hS hcount
  have hfm : Measurable fun z => (f z : ℝ≥0∞) := measurable_from_nat.comp hf
  have hint : Integrable (fun z => (f z : ℝ)) μ := by
    simpa using integrable_toReal_of_lintegral_ne_top hfm.aemeasurable hfin
  refine ⟨?_, hint⟩
  have hfin' : ∑' k, μ (S k) ≠ ∞ := by rwa [h1]
  have hne : ∀ k, μ (S k) ≠ ∞ := fun k =>
    ne_top_of_le_ne_top hfin' (ENNReal.le_tsum (f := fun k => μ (S k)) k)
  have hsum : Summable fun k => μ.real (S k) := ENNReal.summable_toReal hfin'
  rw [hsum.hasSum_iff]
  simp only [measureReal_def]
  rw [← ENNReal.tsum_toReal_eq hne, h1,
    ← integral_toReal hfm.aemeasurable (ae_of_all _ fun _ => ENNReal.natCast_lt_top _)]
  simp

end Counting

/-! ### The probability of an exceedance in a block -/

section Block

/-- The source times of exceedances in the block `{0, …, r - 1}`, indexed by `i ∈ ℕ`, `i ↦` time
`s = r - 1 - i`: an innovation `z` at time `s` produces an exceedance in the block iff `s ≥ 0`
(`i < r`) or its echo `s + L(z)` falls in the block (`r - i ≤ L(z) + 1`, `L(z) ≤ i`). -/
def echoBlockIdx (L : ℝ → ℕ) (r i : ℕ) : Set ℝ := {z | i < r ∨ (i + 1 ≤ L z + r ∧ L z ≤ i)}

theorem measurableSet_echoBlockIdx {L : ℝ → ℕ} (hLm : Measurable L) (r i : ℕ) :
    MeasurableSet (echoBlockIdx L r i) :=
  (MeasurableSet.const _).union (hLm (Set.to_countable {k : ℕ | i + 1 ≤ k + r ∧ k ≤ i}).measurableSet)

/-- Each `z` is a source for `r + min (L z) r` of the indices. -/
theorem tsum_indicator_echoBlockIdx (L : ℝ → ℕ) (r : ℕ) (z : ℝ) :
    ∑' i, (echoBlockIdx L r i).indicator (1 : ℝ → ℝ≥0∞) z = ((r + min (L z) r : ℕ) : ℝ≥0∞) := by
  rcases le_total (L z) r with h | h
  · rw [tsum_indicator_one_eq_card (F := Finset.range (L z + r)), Finset.card_range]
    · congr 1; omega
    · intro i; simp only [echoBlockIdx, mem_ofPred_eq, Finset.mem_range]; omega
  · rw [tsum_indicator_one_eq_card (F := Finset.range r ∪ Finset.Ico (L z) (L z + r)),
      Finset.card_union_of_disjoint, Finset.card_range, Nat.card_Ico]
    · congr 1; omega
    · rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
      omega
    · intro i
      simp only [echoBlockIdx, mem_ofPred_eq, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega

/-- **The block mass of the echoes**: `E[min(L(Z), r); Z > u]` for `Z` Pareto(`α`), i.e. the
expected number of echoes, landing in a block of length `r`, of the exceedances of `u` preceding
the block. -/
noncomputable def echoBlockMass (α : ℝ) (L : ℝ → ℕ) (u : ℝ) (r : ℕ) : ℝ :=
  ∫ z in Ioi u, ((min (L z) r : ℕ) : ℝ) ∂(paretoMeasure 1 α)

theorem integrable_min_lag {α : ℝ} (hα : 0 < α) {L : ℝ → ℕ} (hLm : Measurable L) (u : ℝ)
    (r : ℕ) : Integrable (fun z => ((min (L z) r : ℕ) : ℝ)) ((paretoMeasure 1 α).restrict (Ioi u)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  refine (integrable_const (r : ℝ)).mono' ?_ (ae_of_all _ fun z => ?_)
  · exact (measurable_from_nat.comp (hLm.min measurable_const)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.2 (min_le_right _ _)

theorem echoBlockMass_nonneg (α : ℝ) (L : ℝ → ℕ) (u : ℝ) (r : ℕ) : 0 ≤ echoBlockMass α L u r :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => Nat.cast_nonneg _

theorem echoBlockMass_le {α : ℝ} (hα : 0 < α) {L : ℝ → ℕ} (hLm : Measurable L) {u : ℝ}
    (hu : 1 ≤ u) (r : ℕ) : echoBlockMass α L u r ≤ r * u ^ (-α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rw [← paretoMeasure_one_real_Ioi hα hu, echoBlockMass]
  calc _ ≤ ∫ _z in Ioi u, (r : ℝ) ∂(paretoMeasure 1 α) :=
        setIntegral_mono (integrable_min_lag hα hLm u r) (integrable_const _)
          fun z => Nat.cast_le.2 (min_le_right _ _)
    _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- The expected number of sources: `∑ᵢ P(Z ∈ Sᵢ, Z > u) = r u^(-α) + E[min(L(Z), r); Z > u]`. -/
theorem hasSum_echoBlockIdx {α : ℝ} (hα : 0 < α) {L : ℝ → ℕ} (hLm : Measurable L) {u : ℝ}
    (hu : 1 ≤ u) (r : ℕ) :
    HasSum (fun i => (paretoMeasure 1 α).real (echoBlockIdx L r i ∩ Ioi u))
      (r * u ^ (-α) + echoBlockMass α L u r) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set μ := (paretoMeasure 1 α).restrict (Ioi u)
  have hf : Measurable fun z => r + min (L z) r := measurable_const.add (hLm.min measurable_const)
  have hfin : ∫⁻ z, ((r + min (L z) r : ℕ) : ℝ≥0∞) ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _z, ((2 * r : ℕ) : ℝ≥0∞) ∂μ) ?_ (lintegral_mono fun z => ?_)
    · rw [lintegral_const]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)
    · exact Nat.cast_le.2 (show r + min (L z) r ≤ 2 * r by omega)
  have h := (hasSum_measureReal_of_count (μ := μ) (measurableSet_echoBlockIdx hLm r) hf
    (tsum_indicator_echoBlockIdx L r) hfin).1
  have e1 : ∀ i, μ.real (echoBlockIdx L r i) =
      (paretoMeasure 1 α).real (echoBlockIdx L r i ∩ Ioi u) := fun i =>
    measureReal_restrict_apply (measurableSet_echoBlockIdx hLm r i)
  simp_rw [e1] at h
  convert h using 1
  simp only [Nat.cast_add]
  rw [integral_add (integrable_const _) (integrable_min_lag hα hLm u r), integral_const,
    smul_eq_mul, measureReal_restrict_apply_univ, paretoMeasure_one_real_Ioi hα hu, mul_comm]
  rfl

end Block

section EchoBlock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

/-- The event that the innovation at time `r - 1 - i` is a source of an exceedance of `u` in the
block `{0, …, r - 1}`. -/
def echoBlockEvent (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (u : ℝ) (r i : ℕ) : Set Ω :=
  Z ((r : ℤ) - 1 - i) ⁻¹' (echoBlockIdx L r i ∩ Ioi u)

omit [IsProbabilityMeasure P] in
/-- Every exceedance in the block has a source. -/
theorem subset_iUnion_echoBlockEvent (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℝ} (hu : 0 ≤ u) (r : ℕ) :
    {ω | ∃ t ∈ Finset.Ico (0 : ℤ) r, u < |echoProcess L Z t ω|} ⊆
      ⋃ i, echoBlockEvent L Z u r i := by
  rintro ω ⟨t, ht, hlt⟩
  rw [Finset.mem_Ico] at ht
  rw [abs_of_nonneg (echoProcess_nonneg hpos t ω)] at hlt
  obtain ⟨j, h1, h2⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset hu t hlt)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (r : ℤ) - 1 - i = t - j := ⟨((r : ℤ) - 1 - (t - j)).toNat, by omega⟩
  refine mem_iUnion.2 ⟨i, ?_⟩
  show Z ((r : ℤ) - 1 - i) ω ∈ echoBlockIdx L r i ∩ Ioi u
  rw [hi]
  refine ⟨?_, h1⟩
  simp only [echoBlockIdx, mem_ofPred_eq]
  rcases h2 with rfl | h2
  · left; omega
  · rw [h2]; omega

omit [IsProbabilityMeasure P] in
/-- Every source produces an exceedance in the block (when the echoes are bounded, which holds
almost surely). -/
theorem mem_block_of_mem_echoBlockEvent {u : ℝ} {r i : ℕ} {ω : Ω}
    (hb : ∀ t, BddAbove (range fun j => echoTerm L Z t j ω)) (hω : ω ∈ echoBlockEvent L Z u r i) :
    ω ∈ {ω | ∃ t ∈ Finset.Ico (0 : ℤ) r, u < |echoProcess L Z t ω|} := by
  obtain ⟨hi1, hi2⟩ := hω
  rcases hi1 with hi | ⟨h1, h2⟩
  · refine ⟨(r : ℤ) - 1 - i, Finset.mem_Ico.2 ⟨by omega, by omega⟩, ?_⟩
    exact lt_of_lt_of_le hi2 ((le_echoProcess _ ω).trans (le_abs_self _))
  · refine ⟨(r : ℤ) - 1 - i + L (Z ((r : ℤ) - 1 - i) ω), Finset.mem_Ico.2 ⟨by omega, by omega⟩, ?_⟩
    have hmem : ω ∈ echoSource L Z ((r : ℤ) - 1 - i + L (Z ((r : ℤ) - 1 - i) ω)) u
        (L (Z ((r : ℤ) - 1 - i) ω)) := by
      simp only [echoSource, mem_ofPred_eq, add_sub_cancel_right]
      exact ⟨hi2, Or.inr trivial⟩
    exact (lt_echoProcess_of_mem_echoSource (hb _) hmem).trans_le (le_abs_self _)

variable (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L)

include hα hZ hlaw hLm in
omit [IsProbabilityMeasure P] in
theorem hasSum_measureReal_echoBlockEvent {u : ℝ} (hu : 1 ≤ u) (r : ℕ) :
    HasSum (fun i => P.real (echoBlockEvent L Z u r i)) (r * u ^ (-α) + echoBlockMass α L u r) := by
  refine (hasSum_echoBlockIdx hα hLm hu r).congr_fun fun i => ?_
  exact measureReal_preimage_eq hZ hlaw _
    ((measurableSet_echoBlockIdx hLm r i).inter measurableSet_Ioi)

include hα hZ hlaw hpos hLm in
/-- `P(max_{0 ≤ t < r} X_t > u) ≤ r u^(-α) + E[min(L(Z), r); Z > u]`. -/
theorem measureReal_block_echoProcess_le {u : ℝ} (hu : 1 ≤ u) (r : ℕ) :
    P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) r, u < |echoProcess L Z t ω|} ≤
      r * u ^ (-α) + echoBlockMass α L u r := by
  have hs := hasSum_measureReal_echoBlockEvent hα hZ hlaw hLm (P := P) hu r
  refine (measureReal_mono (subset_iUnion_echoBlockEvent hpos (by linarith) r)).trans ?_
  rw [← hs.tsum_eq]
  exact measureReal_iUnion_le_tsum hs.summable

include hα hZ hind hlaw hLm in
/-- `P(max_{0 ≤ t < r} X_t > u) ≥ S - S²` with `S = r u^(-α) + E[min(L(Z), r); Z > u]`
(Bonferroni over the independent sources). -/
theorem le_measureReal_block_echoProcess {u : ℝ} (hu : 1 ≤ u) (r : ℕ) :
    (r * u ^ (-α) + echoBlockMass α L u r) - (r * u ^ (-α) + echoBlockMass α L u r) ^ 2 ≤
      P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) r, u < |echoProcess L Z t ω|} := by
  have hs := hasSum_measureReal_echoBlockEvent hα hZ hlaw hLm (P := P) hu r
  have hA : ∀ i, MeasurableSet (echoBlockEvent L Z u r i) := fun i =>
    hZ _ ((measurableSet_echoBlockIdx hLm r i).inter measurableSet_Ioi)
  have hpair : ∀ i j, i ≠ j → P.real (echoBlockEvent L Z u r i ∩ echoBlockEvent L Z u r j) =
      P.real (echoBlockEvent L Z u r i) * P.real (echoBlockEvent L Z u r j) := by
    intro i j hij
    have hij' : (r : ℤ) - 1 - i ≠ (r : ℤ) - 1 - j := by omega
    rw [echoBlockEvent, echoBlockEvent, measureReal_def,
      (hind.indepFun hij').measure_inter_preimage_eq_mul _ _
        ((measurableSet_echoBlockIdx hLm r i).inter measurableSet_Ioi)
        ((measurableSet_echoBlockIdx hLm r j).inter measurableSet_Ioi), ENNReal.toReal_mul]
    rfl
  have key := le_measureReal_iUnion_of_pairwise hA hpair hs.summable
  rw [hs.tsum_eq] at key
  refine key.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
  filter_upwards [ae_bddAbove_echoTerm hα hZ hlaw hLm] with ω hω hmem
  obtain ⟨i, hi⟩ := mem_iUnion.1 hmem
  exact mem_block_of_mem_echoBlockEvent hω hi

include hα hZ hind hlaw hpos hLm in
/-- **The cluster ratio of the echo process at every block length.** For iid Pareto(`α`)
innovations and any measurable echo lag `L ≥ 1`, along `uₙ → ∞` and block lengths `rₙ ≥ 1` with
`rₙ uₙ^(-α) → 0`,
`clusterRatio - (1 + E[min(L(Z), rₙ); Z > uₙ] / (rₙ uₙ^(-α))) / 2 → 0`,
that is, the cluster ratio is asymptotically `(1 + E[min(L(Z) / rₙ, 1) | Z > uₙ]) / 2`.
Neither `L → ∞` nor `E[L(Z)] < ∞` is used. -/
theorem tendsto_clusterRatio_sub_echoProcess (hL1 : ∀ z, 1 ≤ L z) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0)) :
    Tendsto (fun n => clusterRatio P (echoProcess L Z) u r n -
      (1 + echoBlockMass α L (u n) (r n) / (r n * u n ^ (-α))) / 2) atTop (𝓝 0) := by
  set b : ℕ → ℝ := fun n => u n ^ (-α)
  set ρ : ℕ → ℝ := fun n => P.real {ω | u n < echoProcess L Z 0 ω} / b n
  have hρ : Tendsto ρ atTop (𝓝 2) :=
    (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw hLm hL1 0).comp hu
  set g : ℕ → ℝ := fun n => 4 * (r n * b n) / ρ n + 2 * |1 / ρ n - 1 / 2|
  have hg : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 4 * (r n * b n) / ρ n) atTop (𝓝 0) := by
      have := (hrb.const_mul 4).div hρ two_ne_zero
      rw [mul_zero, zero_div] at this
      exact this
    have h2 : Tendsto (fun n => 2 * |1 / ρ n - 1 / 2|) atTop (𝓝 0) := by
      have := ((((tendsto_const_nhds (x := (1 : ℝ))).div hρ two_ne_zero).sub_const
        (1 / 2)).abs).const_mul 2
      simpa using this
    have := h1.add h2
    rw [add_zero] at this
    exact this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hu.eventually_ge_atTop 1, hr] with n hn hrn
  have hb : 0 < b n := Real.rpow_pos_of_pos (by linarith) _
  have hR0 : (0 : ℝ) < r n := by exact_mod_cast hrn
  have hP0 : 0 < P.real {ω | u n < echoProcess L Z 0 ω} := by
    refine hb.trans_le ?_
    show u n ^ (-α) ≤ _
    rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hn]
    exact measureReal_mono fun ω hω => lt_of_lt_of_le hω (le_echoProcess 0 ω)
  have hρpos : 0 < ρ n := div_pos hP0 hb
  have hM0 := echoBlockMass_nonneg α L (u n) (r n)
  have hM1 : echoBlockMass α L (u n) (r n) ≤ r n * b n := echoBlockMass_le hα hLm hn (r n)
  have hup := measureReal_block_echoProcess_le hα hZ hlaw hpos hLm hn (r n) (P := P)
  have hlow := le_measureReal_block_echoProcess hα hZ hind hlaw hLm hn (r n) (P := P)
  set M := echoBlockMass α L (u n) (r n)
  set PB := P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |echoProcess L Z t ω|}
  have hcr : clusterRatio P (echoProcess L Z) u r n = PB / (r n * b n * ρ n) := by
    rw [clusterRatio]
    congr 1
    simp only [ρ, abs_of_nonneg (echoProcess_nonneg hpos _ _)]
    field_simp
  rw [Real.norm_eq_abs, hcr]
  set D := (r n : ℝ) * b n with hD
  set S := D + M with hS
  have hD0 : 0 < D := mul_pos hR0 hb
  have e : PB / (D * ρ n) - (1 + M / D) / 2 =
      (PB - S) / (D * ρ n) + S / D * (1 / ρ n - 1 / 2) := by
    field_simp
    ring
  rw [e]
  have hS0 : 0 ≤ S := by linarith
  have hS2 : S ≤ 2 * D := by linarith
  have hq : S / D ≤ 2 := by rw [div_le_iff₀ hD0]; linarith
  have hq0 : 0 ≤ S / D := div_nonneg hS0 hD0.le
  have h1 : |PB - S| ≤ S ^ 2 := abs_le.2 ⟨by linarith, by nlinarith⟩
  calc |(PB - S) / (D * ρ n) + S / D * (1 / ρ n - 1 / 2)|
      ≤ |(PB - S) / (D * ρ n)| + |S / D * (1 / ρ n - 1 / 2)| := abs_add_le _ _
    _ ≤ 4 * D / ρ n + 2 * |1 / ρ n - 1 / 2| := by
      gcongr ?_ + ?_
      · rw [abs_div, abs_of_pos (mul_pos hD0 hρpos), div_le_div_iff₀ (mul_pos hD0 hρpos) hρpos]
        calc |PB - S| * ρ n ≤ S ^ 2 * ρ n := mul_le_mul_of_nonneg_right h1 hρpos.le
          _ ≤ (2 * D) ^ 2 * ρ n := by gcongr
          _ = 4 * D * (D * ρ n) := by ring
      · rw [abs_mul, abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)

include hα hZ hind hlaw hpos hLm in
/-- If `E[min(L(Z), rₙ); Z > uₙ] / (rₙ uₙ^(-α)) → c`, the cluster ratio tends to `(1 + c) / 2`. -/
theorem tendsto_clusterRatio_echoProcess_of_tendsto (hL1 : ∀ z, 1 ≤ L z) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0)) {c : ℝ}
    (hc : Tendsto (fun n => echoBlockMass α L (u n) (r n) / (r n * u n ^ (-α))) atTop (𝓝 c)) :
    Tendsto (clusterRatio P (echoProcess L Z) u r) atTop (𝓝 ((1 + c) / 2)) := by
  have := (tendsto_clusterRatio_sub_echoProcess hα hZ hind hlaw hpos hLm hL1 hu hr hrb).add
    ((hc.const_add 1).div_const 2)
  rw [zero_add] at this
  exact this.congr fun n => by ring

omit [IsProbabilityMeasure P] in
include hα in
/-- For blocks shorter than the echo lag of every exceedance, `E[min(L(Z), r); Z > u] = r u^(-α)`. -/
theorem echoBlockMass_eq_of_le {u : ℝ} (hu : 1 ≤ u) {r : ℕ} (hle : ∀ z, u < z → r ≤ L z) :
    echoBlockMass α L u r = r * u ^ (-α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rw [echoBlockMass, setIntegral_congr_fun measurableSet_Ioi fun z hz => by
    rw [min_eq_right (hle z hz)], setIntegral_const, smul_eq_mul,
    paretoMeasure_one_real_Ioi hα hu, mul_comm]

include hα hZ hind hlaw hpos hLm in
/-- **Short blocks: the cluster ratio tends to `1 = ϑ`.** If eventually every exceedance of `uₙ`
has echo lag at least `rₙ` (`rₙ ≤ L(z)` for all `z > uₙ`), the two exceedances of a cluster are
never in the same block, and the cluster ratio tends to `1`. -/
theorem tendsto_clusterRatio_echoProcess_short (hL1 : ∀ z, 1 ≤ L z) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hshort : ∀ᶠ n in atTop, ∀ z, u n < z → r n ≤ L z) :
    Tendsto (clusterRatio P (echoProcess L Z) u r) atTop (𝓝 1) := by
  have h := tendsto_clusterRatio_echoProcess_of_tendsto hα hZ hind hlaw hpos hLm hL1 hu hr hrb
    (c := 1) ?_
  · norm_num at h
    exact h
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hshort, hu.eventually_ge_atTop 1, hr] with n hn hu1 hrn
  have hb : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have hR : (0 : ℝ) < r n := by exact_mod_cast hrn
  rw [echoBlockMass_eq_of_le hα hu1 hn, div_self (by positivity)]

include hα hZ hind hlaw hpos hLm in
/-- **Short blocks: no escape mass.** In the regime of `tendsto_clusterRatio_echoProcess_short`
(and `L → ∞`, `rₙ → ∞`), the escape mass is `0`: at block lengths below the echo lag the echo
process looks like an iid sequence, with cluster ratio `ϑ = 1`. -/
theorem hasEscapeMass_echoProcess_short (hL1 : ∀ z, 1 ≤ L z) (hLinf : Tendsto L atTop atTop)
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hshort : ∀ᶠ n in atTop, ∀ z, u n < z → r n ≤ L z) :
    HasEscapeMass P (echoProcess L Z) u r 0 := by
  have h := (hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf
    ).tendsto_clusterRatio_iff hα (measurable_echoProcess hZ hLm) measurable_unitSpectral
    (hasShiftInvariantWindows_echoProcess hZ hind hlaw hLm) hu hr 1
  rw [candidateExtremalIndex_unitSpectral hα] at h
  have := h.1 (tendsto_clusterRatio_echoProcess_short hα hZ hind hlaw hpos hLm hL1 hu
    (hr.eventually_gt_atTop 0) hrb hshort)
  convert this using 1
  norm_num

end EchoBlock

end ExtremeValueTheory
