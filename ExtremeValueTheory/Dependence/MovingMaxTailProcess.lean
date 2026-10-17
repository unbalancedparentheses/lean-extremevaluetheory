/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Examples
import ExtremeValueTheory.Dependence.TailProcess

/-!
# The tail process of the moving maximum

PLACEHOLDER
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### The spectral tail process -/

/-- The fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin :=
  ⟨by simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- The location `0` (for `b = true`) or `1` (for `b = false`) of the large innovation. -/
def movingMaxPeak (b : Bool) : ℤ := if b then 0 else 1

/-- The spectral tail process of the moving maximum `X_t = max(Z_t, Z_{t+1})`: with `b` a fair
coin, `Θ_t = 1` if `t` or `t + 1` is the peak location (`0` if `b`, `1` otherwise), and `Θ_t = 0`
otherwise. Thus `Θ = (…, 0, 1, 1, 0, …)` at times `(-1, 0)` or `(0, 1)` with probability `1/2`
each. -/
noncomputable def movingMaxSpectral (t : ℤ) (b : Bool) : ℝ :=
  if t = movingMaxPeak b ∨ t + 1 = movingMaxPeak b then 1 else 0

theorem measurable_movingMaxSpectral (t : ℤ) : Measurable (movingMaxSpectral t) :=
  measurable_from_top

/-- **The candidate extremal index of the moving maximum is `1/2`**: for `b = true` (peak at `0`)
the process vanishes at positive times, so the integrand is `1`; for `b = false` (peak at `1`),
`Θ_1 = 1` and the integrand is `0`. -/
theorem candidateExtremalIndex_movingMax {α : ℝ} (hα : 0 < α) :
    candidateExtremalIndex fairCoin movingMaxSpectral α = 2⁻¹ := by
  have hT0 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral k true|) = 1 := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0
      (by simp [movingMaxSpectral, movingMaxPeak]))
    unfold movingMaxSpectral; split_ifs <;> simp
  have hT1 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral (k + 1) true|) = 0 := by
    refine ENNReal.iSup_eq_zero.2 fun k => ?_
    simp only [movingMaxSpectral, movingMaxPeak, ↓reduceIte]
    split_ifs with h
    · omega
    · simp
  have hF0 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral k false|) = 1 := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0
      (by simp [movingMaxSpectral, movingMaxPeak]))
    unfold movingMaxSpectral; split_ifs <;> simp
  have hF1 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral (k + 1) false|) = 1 := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0 (by simp [movingMaxSpectral,
      movingMaxPeak]))
    unfold movingMaxSpectral; split_ifs <;> simp
  rw [candidateExtremalIndex, fairCoin, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac, lintegral_dirac, hT0, hT1, hF0, hF1, ENNReal.zero_rpow_of_pos hα]
  simp

/-! ### The moving maximum of iid Pareto variables -/

/-- The moving maximum `X_t = max(Z_t, Z_{t+1})` of a `ℤ`-indexed sequence. -/
def movingMax {Ω : Type*} (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ := max (Z t ω) (Z (t + 1) ω)

/-- The deterministic heart of the window convergence: if one coordinate `z i₀ > x` dominates and
all other coordinates in a window `T` are at most `c x`, then the normalized moving maximum
`max(z_t, z_{t+1}) / z_{i₀}` is within `c` of the indicator of `i₀ ∈ {t, t + 1}`. -/
theorem abs_movingMax_div_sub_le {z : ℤ → ℝ} (hz : ∀ j, 0 ≤ z j) {T : Finset ℤ} {i₀ : ℤ}
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (hc1 : c < 1) (hi₀ : x < z i₀)
    (hT : ∀ j ∈ T, j ≠ i₀ → z j ≤ c * x) {t : ℤ} (ht : t ∈ T) (ht1 : t + 1 ∈ T) :
    |max (z t) (z (t + 1)) / z i₀ - (if t = i₀ ∨ t + 1 = i₀ then 1 else 0)| ≤ c := by
  have hzi₀ : 0 < z i₀ := hx.trans hi₀
  have hcx : c * x < z i₀ := lt_trans (by nlinarith) hi₀
  split_ifs with h
  · have hmax : max (z t) (z (t + 1)) = z i₀ := by
      rcases h with rfl | h
      · exact max_eq_left ((hT _ ht1 (by omega)).trans hcx.le)
      · rw [h]; exact max_eq_right ((hT _ ht (by omega)).trans hcx.le)
    rw [hmax, div_self hzi₀.ne', sub_self, abs_zero]
    exact hc.le
  · push Not at h
    have h1 := hT _ ht h.1
    have h2 := hT _ ht1 h.2
    rw [sub_zero, abs_of_nonneg (div_nonneg (le_max_of_le_left (hz _)) hzi₀.le),
      div_le_iff₀ hzi₀]
    calc max (z t) (z (t + 1)) ≤ c * x := max_le h1 h2
      _ ≤ c * z i₀ := by nlinarith

section MovingMax

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
theorem measureReal_lt_of_map_eq (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hα : 0 < α) (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    P.real {ω | x < Z t ω} = x ^ (-α) := by
  have : {ω | x < Z t ω} = Z t ⁻¹' Ioi x := rfl
  rw [this, ← map_measureReal_apply (hZ t) measurableSet_Ioi, hlaw, paretoMeasure_one_real_Ioi hα hx]

omit [IsProbabilityMeasure P] in
theorem measureReal_lt_inter_lt_of_ne (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hα : 0 < α) {i j : ℤ} (hij : i ≠ j) {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    P.real ({ω | x < Z i ω} ∩ {ω | y < Z j ω}) = x ^ (-α) * y ^ (-α) := by
  have h := (hind.indepFun hij).measure_inter_preimage_eq_mul (Ioi x) (Ioi y) measurableSet_Ioi
    measurableSet_Ioi
  have e : {ω | x < Z i ω} ∩ {ω | y < Z j ω} = Z i ⁻¹' Ioi x ∩ Z j ⁻¹' Ioi y := rfl
  rw [e, measureReal_def, h, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]
  exact congrArg₂ (· * ·) (measureReal_lt_of_map_eq hZ hlaw hα i hx)
    (measureReal_lt_of_map_eq hZ hlaw hα j hy)

variable (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)
include hα hZ hind hlaw hpos

omit [IsProbabilityMeasure P] hα hZ hind hlaw hpos in
theorem setOf_lt_abs_movingMax {x : ℝ} :
    {ω | x < |movingMax Z 0 ω|} ⊇ {ω | x < Z 0 ω} := fun ω (hω : x < Z 0 ω) => by
  simp only [mem_ofPred_eq, movingMax, zero_add]
  exact hω.trans_le ((le_max_left _ _).trans (le_abs_self _))

/-- The tail of the moving maximum: `P(|X_0| > x) = 2 x^(-α) - x^(-2α)` for `x ≥ 1`. -/
theorem measureReal_lt_abs_movingMax {x : ℝ} (hx : 1 ≤ x) :
    P.real {ω | x < |movingMax Z 0 ω|} = 2 * x ^ (-α) - x ^ (-α) * x ^ (-α) := by
  have hset : {ω | x < |movingMax Z 0 ω|} = {ω | x < Z 0 ω} ∪ {ω | x < Z 1 ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, movingMax, zero_add,
      abs_of_nonneg (le_max_of_le_left (hpos 0 ω)), lt_max_iff]
  have hu := measureReal_union_add_inter (μ := P) (s := {ω | x < Z 0 ω})
    (measurableSet_lt measurable_const (hZ 1)) (t := {ω | x < Z 1 ω})
  rw [hset, measureReal_lt_inter_lt_of_ne hZ hind hlaw hα (by decide : (0 : ℤ) ≠ 1) hx hx,
    measureReal_lt_of_map_eq hZ hlaw hα 0 hx, measureReal_lt_of_map_eq hZ hlaw hα 1 hx] at *
  linarith

/-- The moving maximum of iid Pareto(`α`) variables is regularly varying with index `-α`. -/
theorem isRegularlyVarying_movingMax :
    IsRegularlyVarying (fun x => P.real {ω | x < |movingMax Z 0 ω|}) (-α) := by
  have hy := tendsto_rpow_neg_atTop hα
  refine ⟨?_, fun c hc => ?_⟩
  · filter_upwards [eventually_gt_atTop 1] with x hx
    rw [measureReal_lt_abs_movingMax hα hZ hind hlaw hpos hx.le]
    have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    have h1 : x ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by linarith)
    nlinarith
  · have key : Tendsto (fun x : ℝ => c ^ (-α) * ((2 - c ^ (-α) * x ^ (-α)) / (2 - x ^ (-α))))
        atTop (𝓝 (c ^ (-α))) := by
      have := (((tendsto_const_nhds (x := (2 : ℝ))).sub (hy.const_mul (c ^ (-α)))).div
        ((tendsto_const_nhds (x := (2 : ℝ))).sub hy) (by norm_num : (2 : ℝ) - 0 ≠ 0)).const_mul (c ^ (-α))
      simpa using this
    refine key.congr' ?_
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (1 / c)] with x hx hxc
    have hcx : 1 ≤ c * x := by rwa [div_le_iff₀' hc] at hxc
    rw [measureReal_lt_abs_movingMax hα hZ hind hlaw hpos hx,
      measureReal_lt_abs_movingMax hα hZ hind hlaw hpos hcx,
      Real.mul_rpow hc.le (by linarith)]
    have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    have h1 : x ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
    have h2 : 2 - x ^ (-α) ≠ 0 := by linarith
    field_simp

end MovingMax

end ExtremeValueTheory
