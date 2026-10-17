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

omit hpos in
/-- **Exchangeability**: given `|X_0| > x`, the larger of `Z_0, Z_1` is `Z_0` with probability
exactly `1/2` (ties have probability `0` because the Pareto law has no atoms). -/
theorem measureReal_peak_eq_half (x : ℝ) :
    P.real ({ω | x < |movingMax Z 0 ω|} ∩ {ω | Z 1 ω ≤ Z 0 ω}) =
      P.real {ω | x < |movingMax Z 0 ω|} / 2 := by
  set ν := paretoMeasure 1 α
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set φ : Ω → ℝ × ℝ := fun ω => (Z 0 ω, Z 1 ω)
  have hφ : Measurable φ := (hZ 0).prodMk (hZ 1)
  have hρ : P.map φ = ν.prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hZ 0).aemeasurable (hZ 1).aemeasurable).1
      (hind.indepFun (by decide : (0 : ℤ) ≠ 1)), hlaw, hlaw]
  have hswap : (ν.prod ν).map Prod.swap = ν.prod ν := Measure.prod_swap
  have hdiag : (ν.prod ν) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    refine (lintegral_congr fun a => ?_).trans lintegral_zero
    have : Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {a} := by ext b; simp [eq_comm]
    rw [this, paretoMeasure_singleton]
  set F : Set (ℝ × ℝ) := {p | x < |max p.1 p.2|}
  have hF : MeasurableSet F := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (measurable_fst.max measurable_snd))
  set E1 := F ∩ {p : ℝ × ℝ | p.2 ≤ p.1}
  set E2 := F ∩ {p : ℝ × ℝ | p.1 ≤ p.2}
  have hE1 : MeasurableSet E1 := hF.inter (measurableSet_le measurable_snd measurable_fst)
  have hE2 : MeasurableSet E2 := hF.inter (measurableSet_le measurable_fst measurable_snd)
  have h12 : (ν.prod ν).real E1 = (ν.prod ν).real E2 := by
    have : E2 = Prod.swap ⁻¹' E1 := by
      ext p; simp [E1, E2, F, max_comm]
    rw [this, ← map_measureReal_apply measurable_swap hE1, hswap]
  have hsum : (ν.prod ν).real E1 + (ν.prod ν).real E2 = (ν.prod ν).real F := by
    have hu := measureReal_union_add_inter (μ := ν.prod ν) (s := E1) hE2
    have hun : E1 ∪ E2 = F := by
      ext p
      simp only [E1, E2, mem_union, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        rcases le_total p.2 p.1 with h' | h'
        exacts [Or.inl ⟨h, h'⟩, Or.inr ⟨h, h'⟩]
    have hin : (ν.prod ν) (E1 ∩ E2) = 0 :=
      measure_mono_null (fun p hp => le_antisymm hp.2.2 hp.1.2) hdiag
    have hin' : (ν.prod ν).real (E1 ∩ E2) = 0 := by simp [measureReal_def, hin]
    rw [hun, hin', add_zero] at hu
    linarith
  have e1 : {ω | x < |movingMax Z 0 ω|} ∩ {ω | Z 1 ω ≤ Z 0 ω} = φ ⁻¹' E1 := by
    ext ω; simp [movingMax, φ, E1, F]
  have e0 : {ω | x < |movingMax Z 0 ω|} = φ ⁻¹' F := by
    ext ω; simp [movingMax, φ, F]
  rw [e1, e0, ← map_measureReal_apply hφ hE1, ← map_measureReal_apply hφ hF, hρ]
  linarith

/-- **Window convergence for the moving maximum**: for every finite window `S`, the law of
`(X_t / |X_0|)_{t ∈ S}` given `|X_0| > x` converges to the law of `(Θ_t)_{t ∈ S}`, where
`Θ = movingMaxSpectral b` with `b` a fair coin. Given `|X_0| > x`, outside an event of conditional
probability `O(x^(-α))` exactly one innovation `Z_i` near the window exceeds `c x`, namely the
peak `Z_0` or `Z_1`, and then the normalized window is within `c` of `Θ`. -/
theorem tendstoLawCond_movingMax (S : Finset ℤ) :
    TendstoLawCond P (fun x => {ω | x < |movingMax Z 0 ω|})
      (fun _ ω (t : S) => movingMax Z t ω / |movingMax Z 0 ω|) atTop
      (fairCoin.map fun b (t : S) => movingMaxSpectral t b) := by
  intro f
  set vT : S → ℝ := fun t => movingMaxSpectral t true
  set vF : S → ℝ := fun t => movingMaxSpectral t false
  have hvT : vT = fun t : S => if (t : ℤ) = 0 ∨ (t : ℤ) + 1 = 0 then 1 else 0 := by
    funext t; simp [vT, movingMaxSpectral, movingMaxPeak]
  have hvF : vF = fun t : S => if (t : ℤ) = 1 ∨ (t : ℤ) + 1 = 1 then 1 else 0 := by
    funext t; simp [vF, movingMaxSpectral, movingMaxPeak]
  have hL : ∫ y, f y ∂(fairCoin.map fun b (t : S) => movingMaxSpectral t b) =
      2⁻¹ * (f vT + f vF) := by
    rw [integral_map measurable_from_top.aemeasurable f.continuous.aestronglyMeasurable,
      fairCoin, integral_smul_measure, integral_add_measure Integrable.of_finite
      Integrable.of_finite, integral_dirac, integral_dirac]
    simp [vT, vF]
  rw [hL, Metric.tendsto_nhds]
  intro ε hε
  set M := ‖f‖
  have hM0 : 0 ≤ M := norm_nonneg _
  have hM : ∀ y, |f y| ≤ M := fun y => by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
  obtain ⟨δT, hδT, hTc⟩ := Metric.continuous_iff.1 f.continuous vT (ε / 2) (by positivity)
  obtain ⟨δF, hδF, hFc⟩ := Metric.continuous_iff.1 f.continuous vF (ε / 2) (by positivity)
  set c := min (min δT δF / 2) (1 / 2) with hcdef
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcT : c < δT := (min_le_left _ _).trans_lt (by have := min_le_left δT δF; linarith)
  have hcF : c < δF := (min_le_left _ _).trans_lt (by have := min_le_right δT δF; linarith)
  -- an index window containing `S`, `S + 1`, `0` and `1`
  set N : ℤ := 1 + ∑ t ∈ S, |t|
  set T : Finset ℤ := Finset.Icc (-N) (N + 1)
  have hN0 : 0 ≤ ∑ t ∈ S, |t| := Finset.sum_nonneg fun i _ => abs_nonneg i
  have hTS : ∀ t ∈ S, t ∈ T ∧ t + 1 ∈ T := fun t ht => by
    have h1 : |t| ≤ ∑ t ∈ S, |t| := Finset.single_le_sum (fun i _ => abs_nonneg i) ht
    have h2 := neg_abs_le t
    have h3 := le_abs_self t
    simp only [T, N, Finset.mem_Icc]
    constructor <;> constructor <;> linarith
  have h0T : (0 : ℤ) ∈ T := by simp only [T, N, Finset.mem_Icc]; constructor <;> linarith
  have h1T : (1 : ℤ) ∈ T := by simp only [T, N, Finset.mem_Icc]; constructor <;> linarith
  -- the bad event: two innovations in `T` exceed `c x`
  set B : ℝ → Set Ω := fun x =>
    ⋃ i ∈ T, ⋃ j ∈ T.erase i, ({ω | c * x < Z i ω} ∩ {ω | c * x < Z j ω})
  have hBm : ∀ x, MeasurableSet (B x) := fun x =>
    Finset.measurableSet_biUnion _ fun i _ => Finset.measurableSet_biUnion _ fun j _ =>
      (measurableSet_lt measurable_const (hZ i)).inter (measurableSet_lt measurable_const (hZ j))
  have hB : ∀ x, 1 ≤ c * x →
      P.real (B x) ≤ (T.card * T.card : ℝ) * ((c * x) ^ (-α) * (c * x) ^ (-α)) := by
    intro x hx
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ i ∈ T, P.real (⋃ j ∈ T.erase i, ({ω | c * x < Z i ω} ∩ {ω | c * x < Z j ω}))
        ≤ ∑ i ∈ T, ∑ j ∈ T.erase i, P.real ({ω | c * x < Z i ω} ∩ {ω | c * x < Z j ω}) :=
          Finset.sum_le_sum fun i _ => measureReal_biUnion_finset_le _ _
      _ = ∑ i ∈ T, ∑ j ∈ T.erase i, ((c * x) ^ (-α) * (c * x) ^ (-α)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
            measureReal_lt_inter_lt_of_ne hZ hind hlaw hα (Finset.ne_of_mem_erase hj).symm hx hx
      _ ≤ ∑ i ∈ T, ∑ j ∈ T, ((c * x) ^ (-α) * (c * x) ^ (-α)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hs_low : ∀ x, 1 ≤ x → x ^ (-α) ≤ P.real {ω | x < |movingMax Z 0 ω|} := fun x hx =>
    (measureReal_lt_of_map_eq hZ hlaw hα 0 hx).symm.le.trans
      (measureReal_mono setOf_lt_abs_movingMax)
  have hBlim : Tendsto (fun x => P.real (B x) / P.real {ω | x < |movingMax Z 0 ω|}) atTop
      (𝓝 0) := by
    have hy := (tendsto_rpow_neg_atTop hα).const_mul
      ((T.card * T.card : ℝ) * (c ^ (-α) * c ^ (-α)))
    rw [mul_zero] at hy
    refine squeeze_zero' (Eventually.of_forall fun x =>
      div_nonneg measureReal_nonneg measureReal_nonneg) ?_ hy
    filter_upwards [eventually_ge_atTop (1 / c)] with x hxc
    have hcx : 1 ≤ c * x := by rwa [div_le_iff₀' hc] at hxc
    have hx1 : 1 ≤ x := by nlinarith
    have hx0 : 0 < x := by linarith
    have hpos' : 0 < x ^ (-α) := Real.rpow_pos_of_pos hx0 _
    calc P.real (B x) / P.real {ω | x < |movingMax Z 0 ω|} ≤ P.real (B x) / x ^ (-α) :=
          div_le_div_of_nonneg_left measureReal_nonneg hpos' (hs_low x hx1)
      _ ≤ (T.card * T.card : ℝ) * ((c * x) ^ (-α) * (c * x) ^ (-α)) / x ^ (-α) := by
          gcongr; exact hB x hcx
      _ = (T.card * T.card : ℝ) * (c ^ (-α) * c ^ (-α)) * x ^ (-α) := by
          rw [Real.mul_rpow hc.le hx0.le]; field_simp
  -- the main estimate at a fixed level `x`
  have hXm : ∀ t, Measurable (movingMax Z t) := fun t => (hZ t).max (hZ (t + 1))
  have hmain : ∀ x, 1 ≤ c * x →
      |∫ ω, f (fun t : S => movingMax Z t ω / |movingMax Z 0 ω|)
          ∂P[|{ω | x < |movingMax Z 0 ω|}] - 2⁻¹ * (f vT + f vF)| ≤
        ε / 2 + 2 * M * (P.real (B x) / P.real {ω | x < |movingMax Z 0 ω|}) := by
    intro x hcx
    have hx1 : 1 ≤ x := by nlinarith
    have hx0 : 0 < x := by linarith
    set s := {ω | x < |movingMax Z 0 ω|} with hsdef
    have hs : MeasurableSet s :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hXm 0))
    have hPs : 0 < P.real s := (Real.rpow_pos_of_pos hx0 _).trans_le (hs_low x hx1)
    have hPs' : P s ≠ 0 := fun h0 => by simp [measureReal_def, h0] at hPs
    have := cond_isProbabilityMeasure (μ := P) hPs'
    have hcondreal : ∀ E, (P[|s]).real E = P.real (s ∩ E) / P.real s := fun E => by
      rw [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
      rfl
    set W : Ω → (S → ℝ) := fun ω t => movingMax Z t ω / |movingMax Z 0 ω|
    have hWm : Measurable W := measurable_pi_iff.2 fun t =>
      (hXm t).div (continuous_abs.measurable.comp (hXm 0))
    set A := {ω | Z 1 ω ≤ Z 0 ω}
    have hA : MeasurableSet A := measurableSet_le (hZ 1) (hZ 0)
    set V : Ω → (S → ℝ) := fun ω => if Z 1 ω ≤ Z 0 ω then vT else vF
    have hVm : Measurable V := Measurable.ite hA measurable_const measurable_const
    -- the coin is fair
    have hμA : (P[|s]).real A = 2⁻¹ := by
      rw [hcondreal, measureReal_peak_eq_half hα hZ hind hlaw x, ← hsdef]
      field_simp
    have hμAc : (P[|s]).real Aᶜ = 2⁻¹ := by
      rw [probReal_compl_eq_one_sub hA, hμA]; norm_num
    have hfV : ∫ ω, f (V ω) ∂P[|s] = 2⁻¹ * (f vT + f vF) := by
      have : (fun ω => f (V ω)) =
          fun ω => A.indicator (fun _ => f vT) ω + Aᶜ.indicator (fun _ => f vF) ω := by
        funext ω
        by_cases h : Z 1 ω ≤ Z 0 ω
        · simp [V, A, h, Set.indicator]
        · simp [V, A, h, Set.indicator]
      rw [this, integral_add ((integrable_const _).indicator hA)
        ((integrable_const _).indicator hA.compl), integral_indicator_const _ hA,
        integral_indicator_const _ hA.compl, hμA, hμAc, smul_eq_mul, smul_eq_mul]
      ring
    -- pointwise comparison of `f ∘ W` and `f ∘ V`
    have hpt : ∀ ω ∈ s, |f (W ω) - f (V ω)| ≤ ε / 2 + (B x).indicator (fun _ => 2 * M) ω := by
      intro ω hω
      by_cases hBω : ω ∈ B x
      · rw [indicator_of_mem hBω]
        have := hM (W ω)
        have := hM (V ω)
        have := abs_sub (f (W ω)) (f (V ω))
        linarith
      · rw [indicator_of_notMem hBω, add_zero]
        have hno : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ (c * x < Z i ω ∧ c * x < Z j ω) := by
          intro i hi j hj hij hcon
          exact hBω (mem_iUnion₂.2 ⟨i, hi, mem_iUnion₂.2 ⟨j,
            Finset.mem_erase.2 ⟨hij.symm, hj⟩, hcon⟩⟩)
        have hω' : x < |movingMax Z 0 ω| := hω
        have habs : |movingMax Z 0 ω| = max (Z 0 ω) (Z 1 ω) := by
          simp [movingMax, abs_of_nonneg (le_max_of_le_left (hpos 0 ω))]
        have hcx' : c * x < x := by nlinarith
        have hclose : ∀ i₀ : ℤ, i₀ ∈ T → x < Z i₀ ω → |movingMax Z 0 ω| = Z i₀ ω →
            dist (W ω) (fun t : S => if (t : ℤ) = i₀ ∨ (t : ℤ) + 1 = i₀ then 1 else 0) ≤ c := by
          intro i₀ hi₀T hxi hXi
          have hT' : ∀ j ∈ T, j ≠ i₀ → Z j ω ≤ c * x := fun j hj hji => by
            by_contra hcon
            exact hno i₀ hi₀T j hj (Ne.symm hji) ⟨hcx'.trans hxi, not_le.1 hcon⟩
          rw [dist_pi_le_iff hc.le]
          intro t
          rw [Real.dist_eq]
          show |max (Z t ω) (Z (t + 1) ω) / |movingMax Z 0 ω| - _| ≤ c
          rw [hXi]
          exact abs_movingMax_div_sub_le (z := fun j => Z j ω) (fun j => hpos j ω) hx0 hc hc1
            hxi hT' (hTS t t.2).1 (hTS t t.2).2
        by_cases hAω : Z 1 ω ≤ Z 0 ω
        · have hX : |movingMax Z 0 ω| = Z 0 ω := by rw [habs, max_eq_left hAω]
          have hd := hclose 0 h0T (by rw [← hX]; exact hω') hX
          rw [← hvT] at hd
          have := hTc (W ω) (hd.trans_lt hcT)
          rw [Real.dist_eq] at this
          simpa [V, hAω] using this.le
        · have hX : |movingMax Z 0 ω| = Z 1 ω := by rw [habs, max_eq_right (not_le.1 hAω).le]
          have hd := hclose 1 h1T (by rw [← hX]; exact hω') hX
          rw [← hvF] at hd
          have := hFc (W ω) (hd.trans_lt hcF)
          rw [Real.dist_eq] at this
          simpa [V, hAω] using this.le
    have hiW : Integrable (fun ω => f (W ω)) (P[|s]) :=
      integrable_of_abs_le (f.continuous.measurable.comp hWm) fun ω => hM _
    have hiV : Integrable (fun ω => f (V ω)) (P[|s]) :=
      integrable_of_abs_le (f.continuous.measurable.comp hVm) fun ω => hM _
    have hint : |∫ ω, f (W ω) ∂P[|s] - ∫ ω, f (V ω) ∂P[|s]| ≤
        ε / 2 + (P[|s]).real (B x) * (2 * M) := by
      rw [← integral_sub hiW hiV]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |f (W ω) - f (V ω)| ∂P[|s]
          ≤ ∫ ω, (ε / 2 + (B x).indicator (fun _ => 2 * M) ω) ∂P[|s] := by
            refine integral_mono_ae (hiW.sub hiV).abs
              ((integrable_const _).add ((integrable_const _).indicator (hBm x))) ?_
            filter_upwards [ae_cond_mem hs] with ω hω
            exact hpt ω hω
        _ = ε / 2 + (P[|s]).real (B x) * (2 * M) := by
            rw [integral_add (integrable_const _) ((integrable_const _).indicator (hBm x)),
              integral_const, integral_indicator_const _ (hBm x), probReal_univ, one_smul,
              smul_eq_mul]
    have hμB : (P[|s]).real (B x) ≤ P.real (B x) / P.real s := by
      rw [hcondreal]
      exact div_le_div_of_nonneg_right
        (measureReal_mono (μ := P) inter_subset_right (measure_ne_top _ _)) hPs.le
    rw [← hfV]
    calc _ ≤ ε / 2 + (P[|s]).real (B x) * (2 * M) := hint
      _ ≤ ε / 2 + P.real (B x) / P.real s * (2 * M) := by gcongr
      _ = _ := by ring
  -- conclusion
  have hK : 0 < ε / 2 / (2 * M + 1) := by positivity
  filter_upwards [hBlim.eventually (gt_mem_nhds hK), eventually_ge_atTop (1 / c)] with x h1 h2
  have hcx : 1 ≤ c * x := by rwa [div_le_iff₀' hc] at h2
  rw [Real.dist_eq]
  have hm := hmain x hcx
  set ρ := P.real (B x) / P.real {ω | x < |movingMax Z 0 ω|}
  have hρ0 : 0 ≤ ρ := div_nonneg measureReal_nonneg measureReal_nonneg
  have hρ : (2 * M + 1) * ρ < ε / 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * M + 1)] at h1
    linarith
  nlinarith

/-- **The spectral tail process of the moving maximum** of iid Pareto(`α`) innovations: `Θ` is
`movingMaxSpectral b` with `b` a fair coin, i.e. the extremal cluster is `Θ_{-1} = Θ_0 = 1` or
`Θ_0 = Θ_1 = 1`, with probability `1/2` each. -/
theorem hasSpectralTailProcess_movingMax :
    HasSpectralTailProcess P (movingMax Z) α fairCoin movingMaxSpectral :=
  ⟨isRegularlyVarying_movingMax hα hZ hind hlaw hpos,
    tendstoLawCond_movingMax hα hZ hind hlaw hpos⟩

omit hpos in
/-- **Consistency check: `θ = ϑ = 1/2` for the moving maximum.** The block extremal index of the
moving maximum, computed directly in `hasExtremalIndex_movingMax` (`θ = 1/2`), equals the
candidate extremal index `ϑ` of its spectral tail process (`candidateExtremalIndex_movingMax`).
-/
theorem hasExtremalIndex_movingMax_candidateExtremalIndex :
    HasExtremalIndex (fun n : ℕ => movingMax Z n) P
      (candidateExtremalIndex fairCoin movingMaxSpectral α).toReal := by
  rw [candidateExtremalIndex_movingMax hα]
  have hZ' : ∀ n : ℕ, Measurable (Z n) := fun n => hZ n
  have hind' : iIndepFun (fun n : ℕ => Z n) P := hind.precomp Nat.cast_injective
  have hid' : ∀ n : ℕ, IdentDistrib (Z n) (Z ((0 : ℕ) : ℤ)) P P := fun n =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have key := hasExtremalIndex_movingMax (Z := fun n : ℕ => Z n) hZ' hind' hid'
  have e : (fun t ω => max (Z ((t : ℕ) : ℤ) ω) (Z ((t + 1 : ℕ) : ℤ) ω)) =
      fun n : ℕ => movingMax Z n := by
    funext n ω; simp [movingMax]
  rw [e] at key
  simpa using key

end MovingMax

end ExtremeValueTheory
