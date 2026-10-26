/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.ThetaGap
import ExtremeValueTheory.Dependence.MDependentExamples
import ExtremeValueTheory.Dependence.EchoProcess.Tools

/-!
# The echo process: tail, tail process and extremal index

The echo process `X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})` driven by iid Pareto(`α`)
innovations: stationarity, the tail `P(X_0 > x) ~ 2 x^(-α)`, the spectral tail process
`Θ_t = 1{t = 0}` with candidate extremal index `ϑ = 1`, and the extremal index `θ = 1/2`.

## Main definitions

* `echoTerm`: The echo of the innovation at time `t - (j + 1)` into time `t`: it is `Z_{t - (j +
  1)}` if the echo lag `L(Z_{t - (j + 1)})` of that innovation is exactly `j + 1`, and `0`
  otherwise.
* `echoProcess`: **The echo process** `X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})`: every
  innovation `Z_s` appears at time `s` and once more, as an echo, at time `s + L(Z_s)`.
* `echoSource`: The *sources* of an exceedance of `x` at time `t`: `j = 0` is `Z_t > x` itself, `j ≥
  1` is the echo of `Z_{t - j} > x` (`L(Z_{t - j}) = j`).
* `echoSourceSet`: The set of values `z` giving a source with index `j` at level `x`.
* `echoIntoFuture`: The event that some innovation before time `0` exceeds `u` and echoes at or
  after time `0`.

## Main results

* `tendsto_measureReal_lt_echoProcess_div`: `P(X_t > x) / x^(-α) → 2`.
* `isRegularlyVarying_echoProcess`: The echo process is regularly varying with index `-α`.
* `hasSpectralTailProcess_echoProcess`: **The spectral tail process of the echo process is
  trivial**: `Θ_t = 1{t = 0}`.
* `candidateExtremalIndex_unitSpectral`: **The candidate extremal index of the echo process is `ϑ =
  1`.**
* `hasExtremalIndex_echoProcess`: **The extremal index of the echo process is `θ = 1/2`**, provided
  the echo lag of an innovation has finite mean, `E[L(Z)] = ∑ⱼ P(L(Z) ≥ j + 1) < ∞`, and grows to
  infinity with the innovation.
* `hasShiftInvariantWindows_echoProcess`: The echo process is stationary.
* `echoProcess_theta_lt_vartheta`: **The echo process has `θ = 1/2 < 1 = ϑ`.** For iid Pareto(`α`)
  innovations and an echo lag `L ≥ 1` with `L(z) → ∞` and `E[L(Z)] < ∞`, the echo process is
  stationary, its spectral tail process is `Θ_t = 1{t = 0}` (so `ϑ = 1`), and its extremal index is
  `1/2`.

This file is part of the proof in `ExtremeValueTheory.Dependence.EchoProcess`.

## References

* B. Basrak and J. Segers, *Regularly varying multivariate time series*, Stoch. Proc. Appl. 119
  (2009) [BS09].
* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020) [KS20].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### The echo process -/

section Echo

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

/-- The echo of the innovation at time `t - (j + 1)` into time `t`: it is `Z_{t - (j + 1)}` if the
echo lag `L(Z_{t - (j + 1)})` of that innovation is exactly `j + 1`, and `0` otherwise. -/
noncomputable def echoTerm (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (j : ℕ) (ω : Ω) : ℝ :=
  if L (Z (t - (j + 1)) ω) = j + 1 then Z (t - (j + 1)) ω else 0

/-- **The echo process** `X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})`: every innovation
`Z_s` appears at time `s` and once more, as an echo, at time `s + L(Z_s)`. The echo lag
`L(Z_s) ≥ 1` grows with the size of the innovation. -/
noncomputable def echoProcess (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  max (Z t ω) (⨆ j : ℕ, echoTerm L Z t j ω)

/-- The *sources* of an exceedance of `x` at time `t`: `j = 0` is `Z_t > x` itself, `j ≥ 1` is
the echo of `Z_{t - j} > x` (`L(Z_{t - j}) = j`). -/
def echoSource (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (x : ℝ) (j : ℕ) : Set Ω :=
  {ω | x < Z (t - j) ω ∧ (j = 0 ∨ L (Z (t - j) ω) = j)}

/-- The set of values `z` giving a source with index `j` at level `x`. -/
def echoSourceSet (L : ℝ → ℕ) (x : ℝ) (j : ℕ) : Set ℝ := {z | x < z ∧ (j = 0 ∨ L z = j)}

theorem echoSource_eq (t : ℤ) (x : ℝ) (j : ℕ) :
    echoSource L Z t x j = Z (t - j) ⁻¹' echoSourceSet L x j := rfl

theorem measurableSet_echoSourceSet (hLm : Measurable L) (x : ℝ) (j : ℕ) :
    MeasurableSet (echoSourceSet L x j) := by
  refine measurableSet_Ioi.inter ((MeasurableSet.const (j = 0)).union ?_)
  exact hLm (measurableSet_singleton j)

theorem measurable_echoTerm (hZ : ∀ t, Measurable (Z t)) (hLm : Measurable L) (t : ℤ) (j : ℕ) :
    Measurable (echoTerm L Z t j) :=
  Measurable.ite ((hLm.comp (hZ _)) (measurableSet_singleton _)) (hZ _) measurable_const

theorem measurable_echoProcess (hZ : ∀ t, Measurable (Z t)) (hLm : Measurable L) (t : ℤ) :
    Measurable (echoProcess L Z t) :=
  (hZ t).max (Measurable.iSup fun j => measurable_echoTerm hZ hLm t j)

theorem le_echoProcess (t : ℤ) (ω : Ω) : Z t ω ≤ echoProcess L Z t ω := le_max_left _ _

theorem echoProcess_nonneg (hpos : ∀ t ω, 0 ≤ Z t ω) (t : ℤ) (ω : Ω) :
    0 ≤ echoProcess L Z t ω := (hpos t ω).trans (le_echoProcess t ω)

/-- The echo process is a shift functional of the innovations. -/
theorem echoProcess_eq_shift : echoProcess L Z = fun t ω => (fun z : ℤ → ℝ =>
    max (z 0) (⨆ j : ℕ, if L (z (-(j + 1))) = j + 1 then z (-(j + 1)) else 0))
      (fun i => Z (t + i) ω) := by
  funext t ω
  simp only [echoProcess, echoTerm, add_zero, ← sub_eq_add_neg]

/-- **Upper inclusion**: an exceedance of `x ≥ 0` at time `t` has a source. -/
theorem setOf_lt_echoProcess_subset {x : ℝ} (hx : 0 ≤ x) (t : ℤ) :
    {ω | x < echoProcess L Z t ω} ⊆ ⋃ j, echoSource L Z t x j := by
  intro ω hω
  simp only [mem_ofPred_eq, echoProcess, lt_max_iff] at hω
  rcases hω with hω | hω
  · exact mem_iUnion.2 ⟨0, by simpa [echoSource] using hω⟩
  · by_cases hb : BddAbove (range fun j => echoTerm L Z t j ω)
    · obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup hω
      simp only [echoTerm] at hj
      split_ifs at hj with hL
      · refine mem_iUnion.2 ⟨j + 1, ?_⟩
        simp only [echoSource, mem_ofPred_eq, Nat.cast_add, Nat.cast_one]
        exact ⟨hj, Or.inr hL⟩
      · exact absurd hj (not_lt.2 hx)
    · rw [Real.iSup_of_not_bddAbove hb] at hω
      exact absurd hω (not_lt.2 hx)

/-- **Lower inclusion**, when the echoes into `t` are bounded (almost surely, see
`ae_bddAbove_echoTerm`). -/
theorem lt_echoProcess_of_mem_echoSource {t : ℤ} {x : ℝ} {j : ℕ} {ω : Ω}
    (hb : BddAbove (range fun j => echoTerm L Z t j ω)) (hω : ω ∈ echoSource L Z t x j) :
    x < echoProcess L Z t ω := by
  obtain ⟨h1, h2⟩ := hω
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h1' : x < Z t ω := by simpa using h1
    exact h1'.trans_le (le_echoProcess t ω)
  · replace h2 : L (Z (t - j) ω) = j := h2.resolve_left hj.ne'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hterm : echoTerm L Z t k ω = Z (t - (k + 1)) ω := by
      have h2' : L (Z (t - (k + 1)) ω) = k + 1 := by exact_mod_cast h2
      simp [echoTerm, h2']
    refine lt_max_of_lt_right (lt_of_lt_of_le ?_ (le_ciSup hb k))
    rw [hterm]
    exact_mod_cast h1

variable (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L)
  (hL1 : ∀ z, 1 ≤ L z)

include hZ hlaw in
omit [IsProbabilityMeasure P] in
theorem measureReal_preimage_eq (t : ℤ) {s : Set ℝ} (hs : MeasurableSet s) :
    P.real (Z t ⁻¹' s) = (paretoMeasure 1 α).real s := by
  rw [← map_measureReal_apply (hZ t) hs, hlaw]

include hZ hlaw in
omit [IsProbabilityMeasure P] in
theorem measure_preimage_eq (t : ℤ) {s : Set ℝ} (hs : MeasurableSet s) :
    P (Z t ⁻¹' s) = paretoMeasure 1 α s := by
  rw [← Measure.map_apply (hZ t) hs, hlaw]

include hα hZ hlaw hLm in
omit [IsProbabilityMeasure P] in
/-- **Almost surely, only finitely many innovations echo into a given time** (Borel–Cantelli:
`∑ⱼ P(L(Z_{t - j}) = j) = ∑ⱼ P(L(Z_0) = j) ≤ 1`). -/
theorem ae_bddAbove_echoTerm :
    ∀ᵐ ω ∂P, ∀ t, BddAbove (range fun j => echoTerm L Z t j ω) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rw [ae_all_iff]
  intro t
  set s : ℕ → Set Ω := fun j => {ω | L (Z (t - (j + 1)) ω) = j + 1}
  have hs : ∀ j, P (s j) = paretoMeasure 1 α (L ⁻¹' {j + 1}) := fun j =>
    measure_preimage_eq hZ hlaw _ (hLm (measurableSet_singleton _))
  have hsum : ∑' j, P (s j) ≠ ∞ := by
    rw [tsum_congr hs, ← measure_iUnion]
    · exact measure_ne_top _ _
    · intro i j hij
      exact Disjoint.preimage _ (Set.disjoint_singleton.2 (by omega))
    · exact fun j => hLm (measurableSet_singleton _)
  have hae : ∀ᵐ ω ∂P, ω ∉ limsup s atTop :=
    measure_eq_zero_iff_ae_notMem.1 (measure_limsup_atTop_eq_zero hsum)
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently] at hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨max (Finset.sup' (Finset.range (N + 1)) Finset.nonempty_range_add_one
    fun j => echoTerm L Z t j ω) 0, ?_⟩
  rintro _ ⟨j, rfl⟩
  by_cases hj : j ≤ N
  · exact le_max_of_le_left (Finset.le_sup' (fun j => echoTerm L Z t j ω)
      (Finset.mem_range.2 (by omega)))
  · have : echoTerm L Z t j ω = 0 := by
      rw [echoTerm, ite_eq_right_iff]
      exact fun h => absurd h (hN j (by omega))
    show echoTerm L Z t j ω ≤ _
    rw [this]
    exact le_max_right _ _

include hα hLm hL1 in
/-- The source probabilities at level `x ≥ 1` sum to `2 x^(-α)`: the innovation itself and its
echo. -/
theorem hasSum_measureReal_echoSourceSet {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun j => (paretoMeasure 1 α).real (echoSourceSet L x j)) (2 * x ^ (-α)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set ν := paretoMeasure 1 α
  set b : ℕ → ℝ := fun j => ν.real {z | x < z ∧ L z = j}
  have hb : HasSum b (x ^ (-α)) := by
    have hU : (⋃ j, {z : ℝ | x < z ∧ L z = j}) = Ioi x := by
      ext z
      simp
    rw [← paretoMeasure_one_real_Ioi hα hx, ← hU]
    refine hasSum_measureReal_iUnion (fun j => measurableSet_Ioi.inter
      (hLm (measurableSet_singleton j))) fun i j hij => ?_
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨-, hi⟩ ⟨-, hj⟩
    exact hij (hi.symm.trans hj)
  have hb0 : b 0 = 0 := by
    have : {z : ℝ | x < z ∧ L z = 0} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      have := hL1 z
      omega
    simp [b, this]
  have hsum := hb.add (hasSum_ite_eq 0 (x ^ (-α)))
  rw [show x ^ (-α) + x ^ (-α) = 2 * x ^ (-α) by ring] at hsum
  refine hsum.congr_fun fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [hb0, ↓reduceIte, zero_add, echoSourceSet, true_or, and_true]
    exact paretoMeasure_one_real_Ioi hα hx
  · simp only [b, echoSourceSet, hj.ne', false_or, ↓reduceIte, add_zero]

include hα hZ hlaw hLm hL1 in
omit [IsProbabilityMeasure P] in
theorem hasSum_measureReal_echoSource (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun j => P.real (echoSource L Z t x j)) (2 * x ^ (-α)) := by
  refine (hasSum_measureReal_echoSourceSet hα hLm hL1 hx).congr_fun fun j => ?_
  rw [echoSource_eq, measureReal_preimage_eq hZ hlaw _ (measurableSet_echoSourceSet hLm x j)]

include hα hZ hlaw hLm hL1 in
/-- `P(X_0 > x) ≤ 2 x^(-α)` for `x ≥ 1`. -/
theorem measureReal_lt_echoProcess_le (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    P.real {ω | x < echoProcess L Z t ω} ≤ 2 * x ^ (-α) := by
  have hs := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 t hx
  refine (measureReal_mono (setOf_lt_echoProcess_subset (by linarith) t)).trans ?_
  rw [← hs.tsum_eq]
  exact measureReal_iUnion_le_tsum hs.summable

include hα hZ hind hlaw hLm hL1 in
/-- `P(X_0 > x) ≥ 2 x^(-α) - 4 x^(-2α)` for `x ≥ 1` (Bonferroni over the independent sources). -/
theorem le_measureReal_lt_echoProcess (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    2 * x ^ (-α) - (2 * x ^ (-α)) ^ 2 ≤ P.real {ω | x < echoProcess L Z t ω} := by
  have hs := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 t hx
  have hA : ∀ j, MeasurableSet (echoSource L Z t x j) := fun j => by
    rw [echoSource_eq]
    exact hZ _ (measurableSet_echoSourceSet hLm x j)
  have hpair : ∀ i j, i ≠ j → P.real (echoSource L Z t x i ∩ echoSource L Z t x j) =
      P.real (echoSource L Z t x i) * P.real (echoSource L Z t x j) := by
    intro i j hij
    have hij' : t - (i : ℤ) ≠ t - j := by omega
    rw [echoSource_eq, echoSource_eq, measureReal_def,
      (hind.indepFun hij').measure_inter_preimage_eq_mul _ _ (measurableSet_echoSourceSet hLm x i)
        (measurableSet_echoSourceSet hLm x j), ENNReal.toReal_mul]
    rfl
  have key := le_measureReal_iUnion_of_pairwise hA hpair hs.summable
  rw [hs.tsum_eq] at key
  refine key.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
  filter_upwards [ae_bddAbove_echoTerm hα hZ hlaw hLm] with ω hω hmem
  obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
  exact lt_echoProcess_of_mem_echoSource (hω t) hj

include hα hZ hind hlaw hLm hL1 in
/-- `P(X_t > x) / x^(-α) → 2`. -/
theorem tendsto_measureReal_lt_echoProcess_div (t : ℤ) :
    Tendsto (fun x => P.real {ω | x < echoProcess L Z t ω} / x ^ (-α)) atTop (𝓝 2) := by
  have hy := tendsto_rpow_neg_atTop hα
  have hlow : Tendsto (fun x : ℝ => 2 - 4 * x ^ (-α)) atTop (𝓝 2) := by
    simpa using (hy.const_mul 4).const_sub 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    rw [le_div_iff₀ h0]
    nlinarith [le_measureReal_lt_echoProcess hα hZ hind hlaw hLm hL1 t hx]
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    rw [div_le_iff₀ h0]
    exact measureReal_lt_echoProcess_le hα hZ hlaw hLm hL1 t hx

include hα hZ hind hlaw hpos hLm hL1 in
/-- The echo process is regularly varying with index `-α`. -/
theorem isRegularlyVarying_echoProcess :
    IsRegularlyVarying (fun x => P.real {ω | x < |echoProcess L Z 0 ω|}) (-α) := by
  have h := (IsRegularlyVarying.rpow_id (-α)).of_tendsto_div
    (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw hLm hL1 0) two_pos
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [abs_of_nonneg (echoProcess_nonneg hpos _ _)]

include hind in
omit [IsProbabilityMeasure P] in
/-- Two sources of exceedances at times `0` and `t ≠ 0` are either distinct innovations
(independent) or the same innovation, which then has echo lag `|t|`; the latter is impossible
above a level `z₀` beyond which all echo lags exceed `|t|`. -/
theorem measure_echoSource_inter_le {t : ℤ} (ht : t ≠ 0) {z₀ : ℝ}
    (hz₀ : ∀ z, z₀ ≤ z → t.natAbs < L z) (hLm : Measurable L) {x y : ℝ} (hx : z₀ ≤ x)
    (j j' : ℕ) :
    P (echoSource L Z 0 x j ∩ echoSource L Z t y j') ≤
      P (echoSource L Z 0 x j) * P (echoSource L Z t y j') := by
  by_cases h : (0 : ℤ) - j = t - j'
  · have hempty : echoSource L Z 0 x j ∩ echoSource L Z t y j' = ∅ := by
      ext ω
      simp only [echoSource, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
        not_and]
      rintro ⟨h1, h2⟩ _ h4
      rw [← h] at h4
      have hL := hz₀ _ (hx.trans h1.le)
      rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4 <;> omega
    rw [hempty, measure_empty]
    exact zero_le
  · rw [echoSource_eq, echoSource_eq]
    exact le_of_eq ((hind.indepFun h).measure_inter_preimage_eq_mul _ _
      (measurableSet_echoSourceSet hLm x j) (measurableSet_echoSourceSet hLm y j'))

include hα hZ hind hlaw hLm hL1 in
/-- **Pair bound**: for `t ≠ 0`, `P(X_0 > x, X_t > y) ≤ 2 x^(-α) · 2 y^(-α)` for `x` large and
`y ≥ 1`. -/
theorem eventually_measureReal_lt_echoProcess_inter_le (hLinf : Tendsto L atTop atTop) {t : ℤ}
    (ht : t ≠ 0) : ∃ z₀ : ℝ, ∀ x y : ℝ, z₀ ≤ x → 1 ≤ y →
      P.real {ω | x < echoProcess L Z 0 ω ∧ y < echoProcess L Z t ω} ≤
        2 * x ^ (-α) * (2 * y ^ (-α)) := by
  obtain ⟨z₁, hz₁⟩ := eventually_atTop.1 (hLinf.eventually_gt_atTop t.natAbs)
  refine ⟨max z₁ 1, fun x y hx hy => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hsx := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 0 hx1
  have hsy := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 t hy
  have htsum : ∀ (s : ℤ) (w : ℝ) (c : ℝ),
      HasSum (fun j => P.real (echoSource L Z s w j)) c →
        ∑' j, P (echoSource L Z s w j) = ENNReal.ofReal c := by
    intro s w c hc
    rw [← hc.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hc.summable]
    exact tsum_congr fun j => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hsub : {ω | x < echoProcess L Z 0 ω ∧ y < echoProcess L Z t ω} ⊆
      ⋃ j, ⋃ j', echoSource L Z 0 x j ∩ echoSource L Z t y j' := by
    intro ω ⟨h1, h2⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (by linarith) 0 h1)
    obtain ⟨j', hj'⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (by linarith) t h2)
    exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨j', hj, hj'⟩⟩
  have hbound : P {ω | x < echoProcess L Z 0 ω ∧ y < echoProcess L Z t ω} ≤
      ENNReal.ofReal (2 * x ^ (-α)) * ENNReal.ofReal (2 * y ^ (-α)) := by
    calc _ ≤ P (⋃ j, ⋃ j', echoSource L Z 0 x j ∩ echoSource L Z t y j') := measure_mono hsub
      _ ≤ ∑' j, ∑' j', P (echoSource L Z 0 x j ∩ echoSource L Z t y j') :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => measure_iUnion_le _)
      _ ≤ ∑' j, ∑' j', P (echoSource L Z 0 x j) * P (echoSource L Z t y j') :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun j' =>
            measure_echoSource_inter_le hind ht (fun z hz => hz₁ z hz) hLm
              ((le_max_left _ _).trans hx) j j'
      _ = (∑' j, P (echoSource L Z 0 x j)) * ∑' j', P (echoSource L Z t y j') := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun j => ENNReal.tsum_mul_left
      _ = _ := by rw [htsum 0 x _ hsx, htsum t y _ hsy]
  have hpos1 : 0 ≤ 2 * x ^ (-α) := by positivity
  have hpos2 : 0 ≤ 2 * y ^ (-α) := by positivity
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rwa [ENNReal.ofReal_mul hpos1]

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The echo process is asymptotically independent at every fixed lag**: the echo of a large
innovation comes at lag `L(Z) → ∞`. -/
theorem tendsto_echoProcess_cond (hLinf : Tendsto L atTop atTop) {t : ℤ} (ht : t ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x => P.real {ω | x < |echoProcess L Z 0 ω| ∧ ε * x < |echoProcess L Z t ω|} /
      P.real {ω | x < |echoProcess L Z 0 ω|}) atTop (𝓝 0) := by
  obtain ⟨z₀, hz₀⟩ := eventually_measureReal_lt_echoProcess_inter_le hα hZ hind hlaw hLm hL1
    hLinf ht
  have hlim : Tendsto (fun x : ℝ => 4 * (ε * x) ^ (-α)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hα).comp
      (tendsto_id.const_mul_atTop hε)).const_mul 4
  refine squeeze_zero' (Eventually.of_forall fun x => div_nonneg measureReal_nonneg
    measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop z₀, eventually_ge_atTop 1,
    eventually_ge_atTop (1 / ε)] with x hxz hx1 hxε
  have hεx : 1 ≤ ε * x := by rwa [div_le_iff₀' hε] at hxε
  simp only [abs_of_nonneg (echoProcess_nonneg hpos _ _)]
  have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have hlow : x ^ (-α) ≤ P.real {ω | x < echoProcess L Z 0 ω} := by
    rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hx1]
    exact measureReal_mono fun ω hω => lt_of_lt_of_le hω (le_echoProcess 0 ω)
  rw [div_le_iff₀ (h0.trans_le hlow)]
  calc _ ≤ 2 * x ^ (-α) * (2 * (ε * x) ^ (-α)) := hz₀ x (ε * x) hxz hεx
    _ = 4 * (ε * x) ^ (-α) * x ^ (-α) := by ring
    _ ≤ _ := by gcongr

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The spectral tail process of the echo process is trivial**: `Θ_t = 1{t = 0}`. -/
theorem hasSpectralTailProcess_echoProcess (hLinf : Tendsto L atTop atTop) :
    HasSpectralTailProcess P (echoProcess L Z) α (Measure.dirac ()) unitSpectral :=
  hasSpectralTailProcess_of_asymptoticIndependence (measurable_echoProcess hZ hLm)
    (echoProcess_nonneg hpos 0) (isRegularlyVarying_echoProcess hα hZ hind hlaw hpos hLm hL1)
    fun _ ht _ hε => tendsto_echoProcess_cond hα hZ hind hlaw hpos hLm hL1 hLinf ht hε

/-- **The candidate extremal index of the echo process is `ϑ = 1`.** -/
theorem candidateExtremalIndex_unitSpectral (hα : 0 < α) :
    candidateExtremalIndex (Measure.dirac ()) unitSpectral α = 1 :=
  candidateExtremalIndex_eq_one hα (by simp [unitSpectral])
    fun k => by simp [unitSpectral]; omega

/-- The event that some innovation before time `0` exceeds `u` and echoes at or after time `0`. -/
def echoIntoFuture (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (u : ℝ) : Set Ω :=
  ⋃ j : ℕ, Z (-(j + 1)) ⁻¹' {z | u < z ∧ j + 1 ≤ L z}

include hα in
/-- The mass of the echoes into the future vanishes when `L(Z)` has a finite mean:
`∑ⱼ P(Z > u, L(Z) ≥ j + 1) = E[L(Z); Z > u] → 0`. -/
theorem tendsto_tsum_echoIntoFuture
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) :
    Tendsto (fun u => ∑' j : ℕ, (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z}) atTop
      (𝓝 0) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun _ : ℕ => (0 : ℝ))
    (f := fun u j => (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z}) hLsum ?_ ?_
  · simpa using h
  · intro j
    refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
      (tendsto_rpow_neg_atTop hα)
    filter_upwards [eventually_ge_atTop 1] with u hu
    rw [← paretoMeasure_one_real_Ioi hα hu]
    exact measureReal_mono fun z hz => hz.1
  · exact Eventually.of_forall fun u j => by
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact measureReal_mono fun z hz => hz.2

include hα hZ hlaw hLm in
theorem measureReal_echoIntoFuture_le
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) (u : ℝ) :
    P.real (echoIntoFuture L Z u) ≤
      ∑' j : ℕ, (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hm : ∀ j : ℕ, MeasurableSet {z : ℝ | u < z ∧ j + 1 ≤ L z} := fun j =>
    measurableSet_Ioi.inter (hLm measurableSet_Ici)
  have heq : ∀ j : ℕ, P.real (Z (-(j + 1)) ⁻¹' {z | u < z ∧ j + 1 ≤ L z}) =
      (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z} := fun j =>
    measureReal_preimage_eq hZ hlaw _ (hm j)
  have hs : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z} :=
    hLsum.of_nonneg_of_le (fun _ => measureReal_nonneg) fun j => measureReal_mono fun z hz => hz.2
  rw [echoIntoFuture]
  simp_rw [← heq] at hs ⊢
  exact measureReal_iUnion_le_tsum hs

omit [IsProbabilityMeasure P] in
/-- **No exceedance up to time `n`**: if no innovation at times `0, …, n - 1` exceeds `u ≥ 0` and
no earlier innovation above `u` echoes at or after time `0`, then `M n ≤ u`. -/
theorem partialMax_echoProcess_le {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) {ω : Ω}
    (h1 : ∀ k < n, Z k ω ≤ u) (h2 : ω ∉ echoIntoFuture L Z u) :
    partialMax (fun k : ℕ => echoProcess L Z k) n ω ≤ u := by
  rw [partialMax_le_iff hn]
  intro k hk
  refine max_le (h1 k hk) (ciSup_le fun j => ?_)
  simp only [echoTerm]
  split_ifs with hL
  · by_cases hkj : (j : ℤ) + 1 ≤ k
    · obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k : ℤ) - (j + 1) = k' := ⟨k - (j + 1), by omega⟩
      rw [hk']
      exact h1 k' (by omega)
    · obtain ⟨i, hi⟩ : ∃ i : ℕ, (k : ℤ) - (j + 1) = -(i + 1) := ⟨j - k, by omega⟩
      rw [hi]
      rw [hi] at hL
      by_contra hcon
      exact h2 (mem_iUnion.2 ⟨i, not_le.1 hcon, by omega⟩)
  · exact hu

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The extremal index of the echo process is `θ = 1/2`**, provided the echo lag of an
innovation has finite mean, `E[L(Z)] = ∑ⱼ P(L(Z) ≥ j + 1) < ∞`, and grows to infinity with the
innovation. Each exceedance cluster consists of two exceedances, an innovation and its echo,
`L(Z)` time units later; since `E[L(Z); Z > uₙ] → 0`, the echoes of innovations before time `0`
are negligible and `P(M n ≤ uₙ) ≈ P(Z ≤ uₙ)^n → exp (-τ / 2)`. -/
theorem hasExtremalIndex_echoProcess (hLinf : Tendsto L atTop atTop)
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) :
    HasExtremalIndex (fun k : ℕ => echoProcess L Z k) P (1 / 2) := by
  have hT := hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf
  refine ⟨⟨by norm_num, by norm_num⟩, fun τ hτ u hu => ?_⟩
  have hu' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess L Z 0 ω|}) atTop (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hu
  have hu0 : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess L Z 0 ω}) atTop (𝓝 τ) := by
    simpa using hu
  have hinf := hT.tendsto_atTop_of_tendsto_mul hu'
  -- `n uₙ^(-α) → τ / 2`
  set b : ℕ → ℝ := fun n => u n ^ (-α)
  have hratio := (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw hLm hL1 0).comp hinf
  have hnb : Tendsto (fun n : ℕ => (n : ℝ) * b n) atTop (𝓝 (τ / 2)) := by
    refine (hu0.div hratio two_ne_zero).congr' ?_
    filter_upwards [hinf.eventually_ge_atTop 1] with n hn
    have h0 : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    have hP : 0 < P.real {ω | u n < echoProcess L Z 0 ω} := by
      refine h0.trans_le ?_
      rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hn]
      exact measureReal_mono fun ω hω => lt_of_lt_of_le hω (le_echoProcess 0 ω)
    simp only [Pi.div_apply, Function.comp_apply, b]
    field_simp
  have hb : Tendsto b atTop (𝓝 0) := (tendsto_rpow_neg_atTop hα).comp hinf
  have hpow := tendsto_one_sub_pow_exp_of_tendsto_mul (k := fun n => n) hb hnb
  rw [show -(τ / 2) = -(1 / 2 * τ) by ring] at hpow
  -- the iid part
  have hidZ : ∀ k : ℕ, IdentDistrib (Z k) (Z ((0 : ℕ) : ℤ)) P P := fun k =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have hindN : iIndepFun (fun k : ℕ => Z k) P :=
    hind.precomp (g := fun k : ℕ => (k : ℤ)) Nat.cast_injective
  have hiid : ∀ n, 1 ≤ u n → P.real (maxLE (fun k : ℕ => Z k) (Finset.range n) (u n)) =
      (1 - b n) ^ n := by
    intro n hn
    rw [measureReal_maxLE_of_iIndepFun hindN hidZ, Finset.card_range]
    congr 1
    have hc : {ω | Z ((0 : ℕ) : ℤ) ω ≤ u n} = {ω | u n < Z 0 ω}ᶜ := by
      ext ω; simp
    rw [hc, probReal_compl_eq_one_sub (measurableSet_lt measurable_const (hZ 0)),
      measureReal_lt_of_map_eq hZ hlaw hα 0 hn]
  have hR := (tendsto_tsum_echoIntoFuture hα hLsum).comp hinf
  have hlow : Tendsto (fun n => (1 - b n) ^ n -
      ∑' j : ℕ, (paretoMeasure 1 α).real {z | u n < z ∧ j + 1 ≤ L z}) atTop
        (𝓝 (Real.exp (-(1 / 2 * τ)))) := by
    simpa using hpow.sub hR
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hpow ?_ ?_
  · filter_upwards [hinf.eventually_ge_atTop 1, eventually_gt_atTop 0] with n hn hn0
    rw [← hiid n hn]
    have hsub : maxLE (fun k : ℕ => Z k) (Finset.range n) (u n) \ echoIntoFuture L Z (u n) ⊆
        {ω | partialMax (fun k : ℕ => echoProcess L Z k) n ω ≤ u n} := by
      rintro ω ⟨h1, h2⟩
      exact partialMax_echoProcess_le hn0 (by linarith) (fun k hk => h1 k (Finset.mem_range.2 hk))
        h2
    have := measureReal_echoIntoFuture_le hα hZ hlaw hLm hLsum (P := P) (u n)
    have h3 : P.real (maxLE (fun k : ℕ => Z k) (Finset.range n) (u n)) ≤
        P.real (maxLE (fun k : ℕ => Z k) (Finset.range n) (u n) \ echoIntoFuture L Z (u n)) +
          P.real (echoIntoFuture L Z (u n)) := by
      refine (measureReal_mono (fun ω hω => ?_)).trans (measureReal_union_le _ _)
      by_cases h : ω ∈ echoIntoFuture L Z (u n)
      · exact Or.inr h
      · exact Or.inl ⟨hω, h⟩
    linarith [measureReal_mono (μ := P) hsub]
  · filter_upwards [hinf.eventually_ge_atTop 1, eventually_gt_atTop 0] with n hn hn0
    rw [← hiid n hn]
    refine measureReal_mono fun ω hω t ht => ?_
    have := (partialMax_le_iff hn0).1 hω t (Finset.mem_range.1 ht)
    exact (le_echoProcess (L := L) t ω).trans this

include hZ hind hlaw hLm in
/-- The echo process is stationary. -/
theorem hasShiftInvariantWindows_echoProcess : HasShiftInvariantWindows P (echoProcess L Z) := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have hG : Measurable fun z : ℤ → ℝ =>
      max (z 0) (⨆ j : ℕ, if L (z (-(j + 1))) = j + 1 then z (-(j + 1)) else 0) :=
    (measurable_pi_apply 0).max (Measurable.iSup fun j =>
      Measurable.ite ((hLm.comp (measurable_pi_apply _)) (measurableSet_singleton _))
        (measurable_pi_apply _) measurable_const)
  rw [echoProcess_eq_shift]
  exact hasShiftInvariantWindows_of_shift hZ hind hid hG

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The echo process has `θ = 1/2 < 1 = ϑ`.** For iid Pareto(`α`) innovations and an echo lag
`L ≥ 1` with `L(z) → ∞` and `E[L(Z)] < ∞`, the echo process is stationary, its spectral tail
process is `Θ_t = 1{t = 0}` (so `ϑ = 1`), and its extremal index is `1/2`. -/
theorem echoProcess_theta_lt_vartheta (hLinf : Tendsto L atTop atTop)
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) :
    HasShiftInvariantWindows P (echoProcess L Z) ∧
      HasSpectralTailProcess P (echoProcess L Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess L Z k) P (1 / 2) :=
  ⟨hasShiftInvariantWindows_echoProcess hZ hind hlaw hLm,
    hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf,
    by rw [candidateExtremalIndex_unitSpectral hα]; rfl,
    hasExtremalIndex_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf hLsum⟩

end Echo

end ExtremeValueTheory
