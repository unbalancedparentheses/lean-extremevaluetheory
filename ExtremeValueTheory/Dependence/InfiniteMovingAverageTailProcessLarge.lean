/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.InfiniteMovingAverageTailProcess
import ExtremeValueTheory.Dependence.InfiniteMovingAverageLarge

/-!
# The spectral tail process of an infinite moving average, all `α > 0`

This file removes the restriction `α < 1` of `Dependence/InfiniteMovingAverageTailProcess.lean`.
Let `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` with `ψ_j ≥ 0` (not all zero), iid nonnegative noise with
`P(Z_0 > x)` regularly varying with index `-α`, **any `α > 0`**, and `∑ ψ_j^δ < ∞` for some
`0 < δ < α` with `δ < 1`. Then

* `hasTailProcess_of_lt_one`: `X` has tail process `R Θ_t`, `R` Pareto(`α`) independent of `J`;
* `hasSpectralTailProcess_of_lt_one`: `X` has spectral tail process `Θ_t = ψ_{J+t} / ψ_J`,
  `P(J = j) = ψ_j^α / ∑_i ψ_i^α`;
* `hasSpectralTailProcess_and_hasExtremalIndex_of_lt_one`: `θ = ϑ = sup_j ψ_j^α / ∑_j ψ_j^α`.

The proofs are those of `InfiniteMovingAverageTailProcess.lean`, with the remainder bound and
the tail asymptotics replaced by their all-`α` versions
(`exists_measureReal_abs_sub_gt_le_of_lt_one`, `tendsto_measureReal_process_div_of_lt_one`).
The candidate extremal index computation `candidateExtremalIndex_spectral` needs no restriction
on `α` and is reused as is.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace InfiniteMovingAverage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z : ℤ → Ω → ℝ} {ψ : ℕ → ℝ}
  {α δ : ℝ}

section Approx

variable [IsProbabilityMeasure P]

/-- **Approximation of the windows**: for `ε, η > 0`, for large `m` and then large `x`, the
windows `(X_t / x)_{t ∈ S}` and `(X^{(m)}_t / x)_{t ∈ S}` are `ε`-close off an event `D` with
`P(B_x Δ B^m_x) + P(B_x ∩ D) ≤ η P(B_x)`, `B_x = {X_0 > x}`, `B^m_x = {X^{(m)}_0 > x}`. -/
theorem eventually_approx_of_lt_one (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) (S : Finset ℤ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ᶠ x in atTop, ∃ D : Set Ω, MeasurableSet D ∧
      (∀ ω ∉ D, dist (fun t : S => process ψ Z t ω / x)
        (fun t : S => MovingAverage.process m ψ Z t ω / x) ≤ ε) ∧
      P.real ({ω | x < |process ψ Z 0 ω|} \ {ω | x < |MovingAverage.process m ψ Z 0 ω|}) +
        P.real ({ω | x < |MovingAverage.process m ψ Z 0 ω|} \ {ω | x < |process ψ Z 0 ω|}) +
        P.real ({ω | x < |process ψ Z 0 ω|} ∩ D) ≤
        η * P.real {ω | x < |process ψ Z 0 ω|} := by
  have hα : 0 < α := hδ.trans hδα
  have hS := summable_rpow hψ0 hδ hδα.le hψ
  obtain ⟨k, hk⟩ := hpos
  set W := ∑' j, ψ j ^ α with hW_def
  have hW : 0 < W := (Real.rpow_pos_of_pos hk _).trans_le
    (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  set L : ℝ → ℝ := fun x => P.real {ω | x < Z 0 ω} with hL_def
  obtain ⟨K, x₀, m₀, hK, hx₀, hR⟩ :=
    exists_measureReal_abs_sub_gt_le_of_lt_one hZ hident hZ0 hδ hδα hδ1 hL hψ0 hψ
  set S' := insert (0 : ℤ) S with hS'
  set n : ℝ := (S'.card : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  -- the choice of `ε'`
  set c : ℝ → ℝ := fun e => (1 - e) ^ (-α) - (1 + e) ^ (-α) with hc_def
  have hc : ContinuousAt c 0 :=
    ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))).sub
      ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num)))
  have hc0 : c 0 = 0 := by simp [hc_def]
  obtain ⟨ε', hcε, hε'0, hε'1⟩ : ∃ e, c e < η / 4 ∧ e ∈ Set.Ioo 0 (min ε 1) :=
    (((hc.eventually (gt_mem_nhds (show c 0 < η / 4 by rw [hc0]; positivity))).filter_mono
      nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (lt_min hε one_pos))).exists
  have hε'ε : ε' ≤ ε := hε'1.le.trans (min_le_left _ _)
  have hε'1' : ε' < 1 := hε'1.trans_le (min_le_right _ _)
  -- the choice of `m`
  set T : ℕ → ℝ := fun m => ∑' j, ψ (j + (m + 1)) ^ δ with hT_def
  have hT : Tendsto T atTop (𝓝 0) :=
    (tendsto_sum_nat_add fun j => ψ j ^ δ).comp (tendsto_add_atTop_nat 1)
  have hTsmall : ∀ᶠ m in atTop, 3 * n * K * T m * ε' ^ (-α) < η * W / 8 := by
    have : Tendsto (fun m => 3 * n * K * T m * ε' ^ (-α)) atTop
        (𝓝 (3 * n * K * 0 * ε' ^ (-α))) := ((hT.const_mul _).mul_const _)
    rw [mul_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hTsmall, eventually_ge_atTop m₀] with m hm hmm₀
  set Wm := MovingAverage.weightSum m ψ α with hWm_def
  have hWm0 : 0 ≤ Wm := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hψ0 j) _
  have hWmW : Wm ≤ W := weightSum_le_tsum hψ0 hS m
  have hFm := MovingAverage.tendsto_measureReal_process_div (m := m) (ψ := ψ) hZ hind hident hZ0
    hα hL hψ0
  have hdiff := (LinearProcess.tendsto_comp_mul_div hL hFm (show (0 : ℝ) < 1 - ε' by linarith)).sub
    (LinearProcess.tendsto_comp_mul_div hL hFm (show (0 : ℝ) < 1 + ε' by linarith))
  rw [← mul_sub] at hdiff
  have hWmc : Wm * c ε' < η * W / 4 := by
    rcases le_or_gt (c ε') 0 with h | h
    · have : Wm * c ε' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hWm0 h
      have : 0 < η * W / 4 := by positivity
      linarith
    · calc Wm * c ε' ≤ W * c ε' := mul_le_mul_of_nonneg_right hWmW h.le
        _ < W * (η / 4) := mul_lt_mul_of_pos_left hcε hW
        _ = η * W / 4 := by ring
  have hX := tendsto_measureReal_process_div_of_lt_one hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ
  have hDlim : Tendsto (fun x => 3 * n * K * T m * (L (ε' * x) / L x)) atTop
      (𝓝 (3 * n * K * T m * ε' ^ (-α))) := tendsto_const_nhds.mul (hL.2 ε' hε'0)
  filter_upwards [hdiff.eventually (gt_mem_nhds (show Wm * c ε' < Wm * c ε' + η * W / 8 by
      have : 0 < η * W / 8 := by positivity
      linarith)),
    hDlim.eventually (gt_mem_nhds hm), hX.eventually (lt_mem_nhds (show W / 2 < W by linarith)),
    hL.1, (tendsto_id.const_mul_atTop hε'0).eventually (eventually_ge_atTop x₀),
    eventually_gt_atTop 0] with x h1 h2 h3 hLx hx0' hx
  set X := process ψ Z with hX_def
  set Xm := MovingAverage.process m ψ Z with hXm_def
  have hXm0 : ∀ ω, 0 ≤ Xm 0 ω := MovingAverage.process_nonneg hψ0 hZ0 0
  have hX0 : ∀ ω, 0 ≤ X 0 ω := process_nonneg hψ0 hZ0 0
  set D := ⋃ t ∈ S', {ω | ε' * x < |X t ω - Xm t ω|} with hD_def
  have hDm : MeasurableSet D := Finset.measurableSet_biUnion S' fun t _ =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp
      ((measurable_process hZ t).sub (MovingAverage.measurable_process hZ t)))
  have hnotD : ∀ ω ∉ D, ∀ t ∈ S', |X t ω - Xm t ω| ≤ ε' * x := by
    intro ω hω t ht
    by_contra h
    exact hω (mem_biUnion ht (not_le.1 h))
  refine ⟨D, hDm, fun ω hω => ?_, ?_⟩
  · refine (dist_pi_le_iff hε.le).2 fun t => ?_
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hx, div_le_iff₀ hx]
    exact (hnotD ω hω t (Finset.mem_insert_of_mem t.2)).trans
      (mul_le_mul_of_nonneg_right hε'ε hx.le)
  -- the bound
  have habsX : ∀ y, {ω | y < |X 0 ω|} = {ω | y < X 0 ω} := fun y => by
    ext ω; simp [abs_of_nonneg (hX0 ω)]
  have habsXm : ∀ y, {ω | y < |Xm 0 ω|} = {ω | y < Xm 0 ω} := fun y => by
    ext ω; simp [abs_of_nonneg (hXm0 ω)]
  rw [habsX, habsXm]
  have hmeasXm : ∀ y, MeasurableSet {ω | y < Xm 0 ω} := fun y =>
    measurableSet_lt measurable_const (MovingAverage.measurable_process hZ 0)
  have hPD : P.real D ≤ n * (K * T m * L (ε' * x)) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun t _ => hR m hmm₀ t _ hx0').trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact le_rfl
  have h0S' : (0 : ℤ) ∈ S' := Finset.mem_insert_self 0 S
  have hsub1 : {ω | x < X 0 ω} \ {ω | x < Xm 0 ω} ⊆
      D ∪ ({ω | (1 - ε') * x < Xm 0 ω} \ {ω | x < Xm 0 ω}) := by
    rintro ω ⟨h1, h2⟩
    by_cases hω : ω ∈ D
    · exact Or.inl hω
    · refine Or.inr ⟨?_, h2⟩
      have := (abs_le.1 (hnotD ω hω 0 h0S')).2
      simp only [mem_ofPred_eq] at h1 ⊢
      linarith
  have hsub2 : {ω | x < Xm 0 ω} \ {ω | x < X 0 ω} ⊆
      D ∪ ({ω | x < Xm 0 ω} \ {ω | (1 + ε') * x < Xm 0 ω}) := by
    rintro ω ⟨h1, h2⟩
    by_cases hω : ω ∈ D
    · exact Or.inl hω
    · refine Or.inr ⟨h1, ?_⟩
      have := (abs_le.1 (hnotD ω hω 0 h0S')).1
      simp only [mem_ofPred_eq, not_lt] at h2 ⊢
      linarith
  have hd1 : P.real ({ω | (1 - ε') * x < Xm 0 ω} \ {ω | x < Xm 0 ω}) =
      P.real {ω | (1 - ε') * x < Xm 0 ω} - P.real {ω | x < Xm 0 ω} :=
    measureReal_sdiff (fun ω (h : x < Xm 0 ω) => (show (1 - ε') * x < Xm 0 ω by nlinarith))
      (hmeasXm x)
  have hd2 : P.real ({ω | x < Xm 0 ω} \ {ω | (1 + ε') * x < Xm 0 ω}) =
      P.real {ω | x < Xm 0 ω} - P.real {ω | (1 + ε') * x < Xm 0 ω} :=
    measureReal_sdiff (fun ω (h : (1 + ε') * x < Xm 0 ω) => (show x < Xm 0 ω by nlinarith))
      (hmeasXm _)
  have hb1 := (measureReal_mono (μ := P) hsub1 (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)
  have hb2 := (measureReal_mono (μ := P) hsub2 (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)
  have hb3 : P.real ({ω | x < X 0 ω} ∩ D) ≤ P.real D :=
    measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
  rw [hd1] at hb1
  rw [hd2] at hb2
  -- the limits, in multiplied form
  rw [← sub_div, div_lt_iff₀ hLx] at h1
  rw [← mul_div_assoc, div_lt_iff₀ hLx] at h2
  rw [lt_div_iff₀ hLx] at h3
  have h4 := mul_lt_mul_of_pos_left h3 hη
  have h5 : n * (K * T m * L (ε' * x)) = 3 * n * K * T m * L (ε' * x) / 3 := by ring
  have hL0 : 0 < L x := hLx
  nlinarith

/-! ### The tail process and the spectral tail process -/

/-- **The tail process of an infinite moving average, all `α > 0`** ([DR85], [KS20, §15.3]):
under the hypotheses of `hasExtremalIndex_of_lt_one`, `X_t = ∑_j ψ_j Z_{t-j}` has tail process
`Y_t = R Θ_t`, with `R` Pareto(`α`) independent of `J`, `Θ_t = ψ_{J+t} / ψ_J`,
`P(J = j) = ψ_j^α / ∑_i ψ_i^α`. -/
theorem hasTailProcess_of_lt_one (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasTailProcess P (process ψ Z) α ((paretoMeasure 1 α).prod (indexLaw ψ α))
      (fun t p => p.1 * spectral ψ t p.2) := by
  have hα : 0 < α := hδ.trans hδα
  have hS := summable_rpow hψ0 hδ hδα.le hψ
  obtain ⟨k, hk⟩ := hpos
  have hkα : 0 < ψ k ^ α := Real.rpow_pos_of_pos hk _
  have hW : 0 < ∑' j, ψ j ^ α := hkα.trans_le (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  have hP := isProbabilityMeasure_paretoMeasure one_pos hα
  have hQ := indexLaw_isProbabilityMeasure hψ0 hS hW
  have hθ0 : ∀ j, 0 < ψ j → spectral ψ 0 j = 1 := fun j hj => by
    simp [spectral, hj.ne']
  constructor
  · have hae : ∀ᵐ p ∂((paretoMeasure 1 α).prod (indexLaw ψ α)), |p.1 * spectral ψ 0 p.2| = p.1 := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure,
        Measure.quasiMeasurePreserving_snd.ae (ae_indexLaw_pos hα hψ0)] with p h1 h2
      rw [hθ0 _ h2, mul_one, abs_of_pos (one_pos.trans h1)]
    rw [Measure.map_congr hae]
    simp
  intro S
  -- the finite tail processes
  have hfinTP : ∀ m ≥ k, HasTailProcess P (MovingAverage.process m ψ Z) α
      ((paretoMeasure 1 α).prod (MovingAverage.indexLaw m (trunc m ψ) α))
      (fun t p => p.1 * MovingAverage.spectral m (trunc m ψ) t p.2) := by
    intro m hm
    have hWm : 0 < MovingAverage.weightSum m (trunc m ψ) α := by
      rw [weightSum_trunc]
      exact hkα.trans_le (Finset.single_le_sum (f := fun j => ψ j ^ α)
        (fun j _ => Real.rpow_nonneg (hψ0 j) _) (Finset.mem_range.2 (by omega)))
    have := MovingAverage.indexLaw_isProbabilityMeasure (trunc_nonneg hψ0 m) hWm
    have h := (MovingAverage.hasSpectralTailProcess hZ hind hident hZ0 hα hL
      (trunc_nonneg hψ0 m) (fun j hj => trunc_of_lt hj) hWm).hasTailProcess hα
      (MovingAverage.measurable_process hZ) (fun t => measurable_from_top)
    rwa [process_trunc] at h
  -- positivity of `P(X_0 > x)`
  have hX := tendsto_measureReal_process_div_of_lt_one hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ
  have hBpos : ∀ᶠ x in atTop, 0 < P.real {ω | x < |process ψ Z 0 ω|} := by
    filter_upwards [hX.eventually (lt_mem_nhds hW), hL.1] with x hx hLx
    have : {ω | x < |process ψ Z 0 ω|} = {ω | x < process ψ Z 0 ω} := by
      ext ω; simp [abs_of_nonneg (process_nonneg hψ0 hZ0 0 ω)]
    rw [this]
    exact (div_pos_iff_of_pos_right hLx).1 hx
  refine tendstoLawCond_of_approx (Bm := fun m x => {ω | x < |MovingAverage.process m ψ Z 0 ω|})
    (Vm := fun m x ω (t : S) => MovingAverage.process m ψ Z t ω / x)
    (fun x => measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (measurable_process hZ 0)))
    (fun m x => measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (MovingAverage.measurable_process hZ 0)))
    (fun x => measurable_pi_iff.2 fun t => (measurable_process hZ t).div_const x)
    (fun m x => measurable_pi_iff.2 fun t => (MovingAverage.measurable_process hZ t).div_const x)
    hBpos ?_ (tendsto_integral_window hα hψ0 hS hk S) fun ε hε η hη =>
      eventually_approx_of_lt_one hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ ⟨k, hk⟩ S hε hη
  filter_upwards [eventually_ge_atTop k] with m hm
  exact (hfinTP m hm).2 S

/-- **The spectral tail process of an infinite moving average, all `α > 0`** ([DR85],
[KS20, §15.3], [Meinguet–Segers 2010]). Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative with
`P(Z_0 > x)` regularly varying with index `-α`, `α > 0`, let `0 < δ < α` with `δ < 1`, and let
`ψ_j ≥ 0`, not all zero, with `∑ ψ_j^δ < ∞`. Then `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` has spectral
tail process `Θ_t = ψ_{J+t} / ψ_J`, `P(J = j) = ψ_j^α / ∑_i ψ_i^α`, `J ∈ ℕ`. -/
theorem hasSpectralTailProcess_of_lt_one (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasSpectralTailProcess P (process ψ Z) α (indexLaw ψ α) (spectral ψ) := by
  have hα : 0 < α := hδ.trans hδα
  have hS := summable_rpow hψ0 hδ hδα.le hψ
  obtain ⟨k, hk⟩ := hpos
  have hW : 0 < ∑' j, ψ j ^ α := (Real.rpow_pos_of_pos hk _).trans_le
    (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  have hP := isProbabilityMeasure_paretoMeasure one_pos hα
  have hQ := indexLaw_isProbabilityMeasure hψ0 hS hW
  have h := (hasTailProcess_of_lt_one hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ
    ⟨k, hk⟩).hasSpectralTailProcess hα (measurable_process hZ) (fun t => measurable_fst.mul
      ((measurable_from_top (f := fun j : ℕ => spectral ψ t j)).comp measurable_snd))
  refine ⟨h.1, fun S => ?_⟩
  have hae : ∀ᵐ p ∂((paretoMeasure 1 α).prod (indexLaw ψ α)),
      (fun (t : S) => p.1 * spectral ψ t p.2 / |p.1 * spectral ψ 0 p.2|) =
        fun (t : S) => spectral ψ t p.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure,
      Measure.quasiMeasurePreserving_snd.ae (ae_indexLaw_pos hα hψ0)] with p h1 h2
    have h0 : spectral ψ 0 p.2 = 1 := by simp [spectral, h2.ne']
    funext t
    rw [h0, mul_one, abs_of_pos (one_pos.trans h1)]
    field_simp
  have e : ((paretoMeasure 1 α).prod (indexLaw ψ α)).map
      (fun p (t : S) => p.1 * spectral ψ t p.2 / |p.1 * spectral ψ 0 p.2|) =
      (indexLaw ψ α).map fun j (t : S) => spectral ψ t j := by
    rw [Measure.map_congr hae, show (fun p : ℝ × ℕ => fun t : S => spectral ψ t p.2) =
      (fun j (t : S) => spectral ψ t j) ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_from_top measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul]
  convert h.2 S using 1
  exact e.symm

end Approx

/-- **`θ = ϑ` for infinite moving averages, all `α > 0`** ([DR85], [KS20, Chapter 15]): under
the hypotheses of `hasExtremalIndex_of_lt_one`, `X` has spectral tail process
`Θ_t = ψ_{J+t} / ψ_J`, and its extremal index is the candidate extremal index `ϑ` of `Θ`, namely
`sup_j ψ_j^α / ∑_j ψ_j^α`. -/
theorem hasSpectralTailProcess_and_hasExtremalIndex_of_lt_one [IsProbabilityMeasure P]
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasSpectralTailProcess P (process ψ Z) α (indexLaw ψ α) (spectral ψ) ∧
      HasExtremalIndex (fun n : ℕ => process ψ Z n) P
        (candidateExtremalIndex (indexLaw ψ α) (spectral ψ) α).toReal := by
  refine ⟨hasSpectralTailProcess_of_lt_one hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ hpos, ?_⟩
  rw [candidateExtremalIndex_spectral hψ0 hδ hψ hδα.le hpos, ENNReal.toReal_ofReal]
  · exact hasExtremalIndex_of_lt_one hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ hpos
  · obtain ⟨k, hk⟩ := hpos
    exact div_nonneg (Real.rpow_nonneg ((hψ0 k).trans (le_ciSup (f := ψ)
      ⟨ψ (Classical.choose (exists_forall_le hψ0 hδ hψ ⟨k, hk⟩)), by
        rintro _ ⟨j, rfl⟩
        exact (Classical.choose_spec (exists_forall_le hψ0 hδ hψ ⟨k, hk⟩)).2 j⟩ k)) _)
      (tsum_nonneg fun j => Real.rpow_nonneg (hψ0 j) _)


end InfiniteMovingAverage

end ExtremeValueTheory
