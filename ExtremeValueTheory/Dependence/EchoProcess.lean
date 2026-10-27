/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.ThetaGap
import ExtremeValueTheory.Dependence.MDependentExamples
import ExtremeValueTheory.Dependence.EchoProcess.Basic

/-!
# The echo process: an explicit stationary sequence with `θ < ϑ`

Let `(Z_t)_{t ∈ ℤ}` be iid Pareto(`α`) and let `L : ℝ → ℕ` be an *echo lag* with `L ≥ 1`,
`L(z) → ∞` as `z → ∞` and `E[L(Z)] < ∞`. The **echo process** is
`X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})`:
every innovation appears at its own time and once more, `L(Z_s)` time units later. Large
innovations echo far away.

* The tail process only sees fixed lags. Given `X_0 > x`, the exceedance comes from an innovation
  at `0` (whose echo is at lag `L(Z_0) → ∞`) or from the echo of an innovation at lag
  `-L → -∞`; either way nothing else is large at any fixed lag. So the spectral tail process is
  `Θ_t = 1{t = 0}`, as for an iid sequence, and `ϑ = 1`.
* But every exceedance cluster consists of *two* exceedances (an innovation and its echo), and
  `P(X_0 > x) ~ 2 P(Z > x)`. The extremal index is `θ = 1/2`.
* The missing half of the cluster is exactly the late-return mass of `Dependence/ThetaGap.lean`: for
  blocks `rₙ` longer than the echo lag of an exceedance (`E[L(Z); Z > uₙ] = o(rₙ P(Z > uₙ))`) but
  with `rₙ P(Z > uₙ) → 0`, the cluster ratio tends to `1/2` and the late-return mass is
  `1/2 = ϑ - θ`. Forward anticlustering fails.

The model is much simpler than the stable-regenerative model of Bai–Wang (arXiv:2110.07499), and
everything is explicit. It is a stationary *factor* of an iid sequence (hence mixing in the
ergodic-theoretic sense; not formalized here). The extremal index is computed directly from
`P(M n ≤ uₙ)`; the block condition `A(uₙ)` is not used here. It is proved for long blocks in
`Dependence/EchoConditionA.lean`.

## Main definitions

* `echoTerm`, `echoProcess`: the model.
* `echoSource L Z t x j`: the sources of an exceedance of `x` at time `t` (`j = 0`: `Z_t > x`;
  `j ≥ 1`: `Z_{t - j} > x` with `L(Z_{t - j}) = j`).
* `unitSpectral`: the spectral tail process `Θ_t = 1{t = 0}` on the one-point space.
* `logLag z = ⌊log z⌋₊ + 1`: a concrete echo lag.

## Main results

General tools:
* `hasSpectralTailProcess_of_asymptoticIndependence`: if `X_0 ≥ 0` is regularly varying and
  `P(|X_t| > ε x | |X_0| > x) → 0` for all `t ≠ 0`, `ε > 0`, then `Θ_t = 1{t = 0}`.
* `hasShiftInvariantWindows_of_shift`: measurable shift functionals of iid noise are stationary.
* `le_measureReal_iUnion_of_pairwise`: `P(⋃ Aⱼ) ≥ S - S²` for pairwise independent events.

The echo process (hypotheses: `α > 0`, iid Pareto(`α`) innovations, `L` measurable, `L ≥ 1`,
plus `L → ∞` and `E[L(Z)] < ∞` where stated):
* `hasShiftInvariantWindows_echoProcess`: stationarity.
* `isRegularlyVarying_echoProcess`, `tendsto_measureReal_lt_echoProcess_div`:
  `P(X_0 > x) ~ 2 x^(-α)`.
* `hasSpectralTailProcess_echoProcess`, `candidateExtremalIndex_unitSpectral`: `Θ = e_0`,
  `ϑ = 1` (uses `L → ∞`, not `E[L(Z)] < ∞`).
* `hasExtremalIndex_echoProcess`: `θ = 1/2` (uses `E[L(Z)] < ∞`).
* `echoProcess_theta_lt_vartheta`: all of the above together.
* `tendsto_clusterRatio_echoProcess`, `hasLateReturnMass_echoProcess`,
  `not_forwardAntiClusteringAt_echoProcess`: the cluster ratio tends to `1/2`, the late-return mass is
  `1/2`, anticlustering fails.
* `logEchoProcess_theta_lt_vartheta`, `logEchoProcess_hasLateReturnMass`,
  `logEchoProcess_hasLateReturnMass_of_tendsto`: the same for `L(z) = ⌊log z⌋₊ + 1`, where the
  condition on the blocks is `log uₙ = o(rₙ)`; in the standard normalization
  `n P(X_0 > uₙ) → τ > 0` it suffices that `rₙ / n → 0` and `log n = o(rₙ)`.

## Remarks

* For blocks shorter than the echo lag of an exceedance the cluster ratio tends to `ϑ = 1`
  instead (both exceedances of a cluster are then seen as separate clusters). This mesoscopic
  phase transition at the scale of `L(uₙ)` is in `Dependence/EchoPhaseTransition.lean`.
* The innovations are assumed nonnegative pointwise (`hpos`), a harmless normalization.

## File layout

This file holds the final part of the development and imports the others:

* `ExtremeValueTheory.Dependence.EchoProcess.Tools`: asymptotic independence gives the trivial
  spectral tail process; stationarity of shift functionals of iid noise; a pairwise-independence
  lower bound.
* `ExtremeValueTheory.Dependence.EchoProcess.Basic`: the model, stationarity, `P(X_0 > x) ~ 2
  x^(-α)`, `Θ = e_0`, `ϑ = 1` and `θ = 1/2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section Echo

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}
variable (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L)
  (hL1 : ∀ z, 1 ≤ L z)

/-! #### The cluster ratio and the late-return mass -/

include hα hZ hind hlaw in
omit [IsProbabilityMeasure P] in
/-- `P(max_{0 ≤ k < r} Z_k > u) ≥ r u^(-α) - (r u^(-α))²` (Bonferroni). -/
theorem le_measureReal_exists_lt_innovation [IsProbabilityMeasure P] (r : ℕ) {u : ℝ}
    (hu : 1 ≤ u) :
    r * u ^ (-α) - (r * u ^ (-α)) ^ 2 ≤ P.real {ω | ∃ k < r, u < Z k ω} := by
  set A : ℕ → Set Ω := fun j => {ω | j < r ∧ u < Z j ω}
  have hA : ∀ j, MeasurableSet (A j) := fun j =>
    (MeasurableSet.const _).inter (measurableSet_lt measurable_const (hZ _))
  have hPA : ∀ j, P.real (A j) = if j < r then u ^ (-α) else 0 := by
    intro j
    split_ifs with hj
    · rw [← measureReal_lt_of_map_eq hZ hlaw hα j hu]
      congr 1
      ext ω
      simp [A, hj]
    · have : A j = ∅ := by ext ω; simp [A, hj]
      rw [this, measureReal_empty]
  have hsum : HasSum (fun j => P.real (A j)) (r * u ^ (-α)) := by
    have : HasSum (fun j => P.real (A j)) (∑ j ∈ Finset.range r, P.real (A j)) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        rw [hPA, ite_eq_right_iff]
        exact fun h => absurd (Finset.mem_range.2 h) hj
    convert this using 1
    rw [Finset.sum_congr rfl fun j hj => by
      rw [hPA, ite_eq_left_iff.2 fun h => absurd (Finset.mem_range.1 hj) h]]
    simp
  have hpair : ∀ i j, i ≠ j → P.real (A i ∩ A j) = P.real (A i) * P.real (A j) := by
    intro i j hij
    by_cases hi : i < r
    · by_cases hj : j < r
      · have e : A i ∩ A j = Z i ⁻¹' Ioi u ∩ Z j ⁻¹' Ioi u := by
          ext ω; simp [A, hi, hj]
        have ei : A i = Z i ⁻¹' Ioi u := by ext ω; simp [A, hi]
        have ej : A j = Z j ⁻¹' Ioi u := by ext ω; simp [A, hj]
        rw [e, ei, ej, measureReal_def, (hind.indepFun (by exact_mod_cast hij)
          ).measure_inter_preimage_eq_mul _ _ measurableSet_Ioi measurableSet_Ioi,
          ENNReal.toReal_mul]
        rfl
      · have : A j = ∅ := by ext ω; simp [A, hj]
        simp [this]
    · have : A i = ∅ := by ext ω; simp [A, hi]
      simp [this]
  have key := le_measureReal_iUnion_of_pairwise hA hpair hsum.summable
  rw [hsum.tsum_eq] at key
  refine key.trans (le_of_eq (congrArg P.real ?_))
  ext ω
  simp only [A, mem_iUnion, mem_ofPred_eq]

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The cluster ratio of the echo process tends to `1/2`** when the block length `rₙ` is
negligible against `1 / P(Z > uₙ)` but large against the typical echo lag of an exceedance:
`rₙ uₙ^(-α) → 0` and `E[L(Z); Z > uₙ] = o(rₙ uₙ^(-α))`. Each cluster contributes its innovation
and its echo, both inside the block, but the tail process only sees one of them. -/
theorem tendsto_clusterRatio_echoProcess {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z})
    (hR : Tendsto (fun n => (∑' j : ℕ, (paretoMeasure 1 α).real {z | u n < z ∧ j + 1 ≤ L z}) /
      (r n * u n ^ (-α))) atTop (𝓝 0)) :
    Tendsto (clusterRatio P (echoProcess L Z) u r) atTop (𝓝 (1 / 2)) := by
  set b : ℕ → ℝ := fun n => u n ^ (-α)
  set R : ℕ → ℝ := fun n => ∑' j : ℕ, (paretoMeasure 1 α).real {z | u n < z ∧ j + 1 ≤ L z}
  set ρ : ℕ → ℝ := fun n => P.real {ω | u n < echoProcess L Z 0 ω} / b n
  have hρ : Tendsto ρ atTop (𝓝 2) :=
    (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw hLm hL1 0).comp hu
  have hlow : Tendsto (fun n => (1 - r n * b n) / ρ n) atTop (𝓝 (1 / 2)) := by
    have := (hrb.const_sub 1).div hρ two_ne_zero
    rw [sub_zero] at this
    exact this
  have hup : Tendsto (fun n => (1 + R n / (r n * b n)) / ρ n) atTop (𝓝 (1 / 2)) := by
    have := (hR.const_add 1).div hρ two_ne_zero
    rw [add_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  all_goals
    filter_upwards [hu.eventually_ge_atTop 1, hr.eventually_gt_atTop 0] with n hn hrn
    have hb : 0 < b n := Real.rpow_pos_of_pos (by linarith) _
    have hR0 : (0 : ℝ) < r n := by exact_mod_cast hrn
    have hP0 : 0 < P.real {ω | u n < echoProcess L Z 0 ω} := by
      refine hb.trans_le ?_
      show u n ^ (-α) ≤ _
      rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hn]
      exact measureReal_mono fun ω hω => lt_of_lt_of_le hω (le_echoProcess 0 ω)
    have hρe : r n * P.real {ω | u n < |echoProcess L Z 0 ω|} = r n * b n * ρ n := by
      simp only [ρ, abs_of_nonneg (echoProcess_nonneg hpos _ _)]
      field_simp
    have hρpos : 0 < ρ n := div_pos hP0 hb
    rw [clusterRatio, hρe]
  · -- lower bound
    rw [div_le_div_iff₀ hρpos (by positivity)]
    have hB := le_measureReal_exists_lt_innovation hα hZ hind hlaw (P := P) (r n) hn
    have hsub : {ω | ∃ k < r n, u n < Z k ω} ⊆
        {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |echoProcess L Z t ω|} := by
      rintro ω ⟨k, hk, hlt⟩
      refine ⟨k, Finset.mem_Ico.2 ⟨by positivity, by exact_mod_cast hk⟩, ?_⟩
      exact hlt.trans_le ((le_echoProcess (L := L) k ω).trans (le_abs_self _))
    have h2 := measureReal_mono (μ := P) hsub
    have : (1 - r n * b n) * (r n * b n * ρ n) = (r n * b n - (r n * b n) ^ 2) * ρ n := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hρpos.le
  · -- upper bound
    rw [div_le_div_iff₀ (by positivity) hρpos]
    have hsub : {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |echoProcess L Z t ω|} ⊆
        (⋃ k ∈ Finset.range (r n), {ω | u n < Z k ω}) ∪ echoIntoFuture L Z (u n) := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
      obtain ⟨t, ht, hlt⟩ := hω
      rw [Finset.mem_Ico] at ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
      have hle := partialMax_echoProcess_le (L := L) hrn (by linarith : (0 : ℝ) ≤ u n)
        (fun k hk => not_lt.1 (hcon.1 k hk)) hcon.2
      rw [partialMax_le_iff hrn] at hle
      have := hle k (by exact_mod_cast ht.2)
      rw [abs_of_nonneg (echoProcess_nonneg hpos _ _)] at hlt
      linarith
    have h1 := measureReal_mono (μ := P) hsub
    have h2 := measureReal_union_le (μ := P) (⋃ k ∈ Finset.range (r n), {ω | u n < Z k ω})
      (echoIntoFuture L Z (u n))
    have h3 : P.real (⋃ k ∈ Finset.range (r n), {ω | u n < Z k ω}) ≤ r n * b n := by
      refine (measureReal_biUnion_finset_le _ _).trans (le_of_eq ?_)
      have hk : ∀ k ∈ Finset.range (r n), P.real {ω | u n < Z (k : ℤ) ω} = b n := fun k _ =>
        measureReal_lt_of_map_eq hZ hlaw hα _ hn
      rw [Finset.sum_congr rfl hk]
      simp
    have h4 := measureReal_echoIntoFuture_le hα hZ hlaw hLm hLsum (P := P) (u n)
    have e : (1 + R n / (r n * b n)) * (r n * b n * ρ n) = (r n * b n + R n) * ρ n := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) hρpos.le

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The late-return mass of the echo process is `1/2 = ϑ - θ`**, as predicted by the gap formula
`HasSpectralTailProcess.tendsto_clusterRatio_iff`: one of the two exceedances of each cluster
sits at lag `L(Z) → ∞`, invisible to the tail process. -/
theorem hasLateReturnMass_echoProcess (hLinf : Tendsto L atTop atTop) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z})
    (hR : Tendsto (fun n => (∑' j : ℕ, (paretoMeasure 1 α).real {z | u n < z ∧ j + 1 ≤ L z}) /
      (r n * u n ^ (-α))) atTop (𝓝 0)) :
    HasLateReturnMass P (echoProcess L Z) u r (1 / 2) := by
  have h := (hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf
    ).tendsto_clusterRatio_iff hα (measurable_echoProcess hZ hLm) measurable_unitSpectral
    (hasShiftInvariantWindows_echoProcess hZ hind hlaw hLm) hu hr (1 / 2)
  rw [candidateExtremalIndex_unitSpectral hα] at h
  have := h.1 (tendsto_clusterRatio_echoProcess hα hZ hind hlaw hpos hLm hL1 hu hr hrb hLsum hR)
  convert this using 1
  norm_num

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The echo process violates (forward) anticlustering** along every such pair `uₙ`, `rₙ`. -/
theorem not_forwardAntiClusteringAt_echoProcess (hLinf : Tendsto L atTop atTop) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z})
    (hR : Tendsto (fun n => (∑' j : ℕ, (paretoMeasure 1 α).real {z | u n < z ∧ j + 1 ≤ L z}) /
      (r n * u n ^ (-α))) atTop (𝓝 0)) :
    ¬ ForwardAntiClusteringAt P (echoProcess L Z) u r := fun hAC => by
  have h1 := hasLateReturnMass_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf hu hr hrb hLsum hR
  have := h1.unique (hAC.hasLateReturnMass_zero hr)
  norm_num at this

end Echo

/-! ### A concrete echo lag: `L(z) = ⌊log z⌋ + 1` -/

section LogLag

/-- The logarithmic echo lag `L(z) = ⌊log z⌋₊ + 1`. -/
noncomputable def logLag (z : ℝ) : ℕ := ⌊Real.log z⌋₊ + 1

theorem measurable_logLag : Measurable logLag := by
  show Measurable ((fun n : ℕ => n + 1) ∘ fun z => ⌊Real.log z⌋₊)
  exact measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_log)

theorem one_le_logLag (z : ℝ) : 1 ≤ logLag z := Nat.le_add_left 1 _

theorem tendsto_logLag : Tendsto logLag atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_succ _)
    (tendsto_nat_floor_atTop.comp Real.tendsto_log_atTop)

/-- The tail of the logarithmic lag: `P(L(Z) ≥ j + 1) ≤ 2^α e^(-α j)`. -/
theorem measureReal_logLag_le {α : ℝ} (hα : 0 < α) (j : ℕ) :
    (paretoMeasure 1 α).real {z | j + 1 ≤ logLag z} ≤ 2 ^ α * Real.exp (-α) ^ j := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero, mul_one]
    exact measureReal_le_one.trans (Real.one_le_rpow (by norm_num) hα.le)
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have he : 1 ≤ Real.exp j / 2 := by
      have := Real.add_one_le_exp (j : ℝ)
      linarith
    calc (paretoMeasure 1 α).real {z | j + 1 ≤ logLag z}
        ≤ (paretoMeasure 1 α).real (Ioi (Real.exp j / 2)) := by
          refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
          filter_upwards [ae_one_lt_paretoMeasure (α := α)] with z hz1 hz
          have hz' : j ≤ ⌊Real.log z⌋₊ := by simpa [logLag] using hz
          have hlog : (j : ℝ) ≤ Real.log z :=
            (Nat.cast_le.2 hz').trans (Nat.floor_le (Real.log_pos hz1).le)
          have := (Real.exp_le_exp.2 hlog).trans_eq (Real.exp_log (by linarith))
          show Real.exp j / 2 < z
          linarith [Real.exp_pos (j : ℝ)]
      _ = (Real.exp j / 2) ^ (-α) := paretoMeasure_one_real_Ioi hα he
      _ = Real.exp j ^ (-α) / 2 ^ (-α) := Real.div_rpow (Real.exp_pos _).le (by norm_num) _
      _ = Real.exp (j * -α) * 2 ^ α := by
          rw [← Real.exp_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      _ = 2 ^ α * Real.exp (-α) ^ j := by
          rw [← Real.exp_nat_mul]
          ring_nf

theorem summable_geometric_exp_neg {α : ℝ} (hα : 0 < α) :
    Summable fun j : ℕ => (2 : ℝ) ^ α * Real.exp (-α) ^ j :=
  (summable_geometric_of_lt_one (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (by linarith))).mul_left _

/-- `E[L(Z)] < ∞` for the logarithmic lag. -/
theorem summable_logLag {α : ℝ} (hα : 0 < α) :
    Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ logLag z} :=
  (summable_geometric_exp_neg hα).of_nonneg_of_le (fun _ => measureReal_nonneg)
    (measureReal_logLag_le hα)

/-- `E[L(Z); Z > u] ≤ (⌈log u⌉ + 2^α / (1 - e^(-α))) u^(-α)` for the logarithmic lag: the echo
lag of an exceedance of `u` is of order `log u`. -/
theorem tsum_logLag_le {α : ℝ} (hα : 0 < α) {u : ℝ} (hu : 1 ≤ u) :
    ∑' j : ℕ, (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ logLag z} ≤
      (⌈Real.log u⌉₊ + 2 ^ α / (1 - Real.exp (-α))) * u ^ (-α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set ν := paretoMeasure 1 α
  set f : ℕ → ℝ := fun j => ν.real {z | u < z ∧ j + 1 ≤ logLag z}
  set K := ⌈Real.log u⌉₊
  have hq0 : 0 ≤ Real.exp (-α) := (Real.exp_pos _).le
  have hq1 : Real.exp (-α) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hfs : Summable f := (summable_logLag hα).of_nonneg_of_le (fun _ => measureReal_nonneg)
    fun j => measureReal_mono fun z hz => hz.2
  have hfu : ∀ j, f j ≤ u ^ (-α) := fun j => by
    rw [← paretoMeasure_one_real_Ioi hα hu]
    exact measureReal_mono fun z hz => hz.1
  rw [← hfs.sum_add_tsum_nat_add K]
  have h1 : ∑ j ∈ Finset.range K, f j ≤ K * u ^ (-α) := by
    calc _ ≤ ∑ _j ∈ Finset.range K, u ^ (-α) := Finset.sum_le_sum fun j _ => hfu j
      _ = K * u ^ (-α) := by simp
  have hgK : Summable fun j : ℕ => (2 : ℝ) ^ α * Real.exp (-α) ^ (j + K) :=
    (summable_geometric_exp_neg hα).comp_injective (add_left_injective K)
  have h2 : ∑' j, f (j + K) ≤ 2 ^ α / (1 - Real.exp (-α)) * u ^ (-α) := by
    calc ∑' j, f (j + K) ≤ ∑' j : ℕ, (2 : ℝ) ^ α * Real.exp (-α) ^ (j + K) :=
          (hfs.comp_injective (add_left_injective K)).tsum_le_tsum
            (fun j => (measureReal_mono (by intro z hz; exact hz.2)).trans
              (measureReal_logLag_le hα _)) hgK
      _ = 2 ^ α / (1 - Real.exp (-α)) * Real.exp (-α) ^ K := by
          simp_rw [pow_add, ← mul_assoc]
          rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
          ring
      _ ≤ 2 ^ α / (1 - Real.exp (-α)) * u ^ (-α) := by
          have hpos : 0 ≤ 2 ^ α / (1 - Real.exp (-α)) :=
            div_nonneg (by positivity) (by linarith)
          refine mul_le_mul_of_nonneg_left ?_ hpos
          rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (by linarith)]
          refine Real.exp_le_exp.2 ?_
          have := Nat.le_ceil (Real.log u)
          nlinarith
  linarith

/-- The hypothesis `E[L(Z); Z > uₙ] = o(rₙ uₙ^(-α))` of `tendsto_clusterRatio_echoProcess` holds
for the logarithmic lag as soon as `log uₙ = o(rₙ)`. -/
theorem tendsto_tsum_logLag_div {α : ℝ} (hα : 0 < α) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hlog : Tendsto (fun n => Real.log (u n) / r n) atTop (𝓝 0)) :
    Tendsto (fun n => (∑' j : ℕ, (paretoMeasure 1 α).real {z | u n < z ∧ j + 1 ≤ logLag z}) /
      (r n * u n ^ (-α))) atTop (𝓝 0) := by
  set C := 2 ^ α / (1 - Real.exp (-α))
  have hrinv : Tendsto (fun n => (1 + C) / (r n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr)
  have hlim := hlog.add hrinv
  rw [add_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hu.eventually_ge_atTop 1] with n hn
    exact div_nonneg (tsum_nonneg fun _ => measureReal_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _))
  · filter_upwards [hu.eventually_ge_atTop 1, hr.eventually_gt_atTop 0] with n hn hrn
    have hb : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    have hR : (0 : ℝ) < r n := by exact_mod_cast hrn
    have hceil : (⌈Real.log (u n)⌉₊ : ℝ) ≤ Real.log (u n) + 1 :=
      (Nat.ceil_lt_add_one (Real.log_nonneg hn)).le
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ (⌈Real.log (u n)⌉₊ + C) * u n ^ (-α) := tsum_logLag_le hα hn
      _ ≤ (Real.log (u n) + 1 + C) * u n ^ (-α) := by gcongr
      _ = (Real.log (u n) / r n + (1 + C) / r n) * (r n * u n ^ (-α)) := by
          field_simp
          ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- **A fully explicit example of `θ < ϑ`**: with iid Pareto(`α`) innovations and the echo lag
`L(z) = ⌊log z⌋₊ + 1`, the echo process `X_t = max(Z_t, max {Z_s : s + L(Z_s) = t})` is
stationary with spectral tail process `Θ_t = 1{t = 0}`, so `ϑ = 1`, while its extremal index is
`θ = 1/2`. -/
theorem logEchoProcess_theta_lt_vartheta (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) :
    HasShiftInvariantWindows P (echoProcess logLag Z) ∧
      HasSpectralTailProcess P (echoProcess logLag Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess logLag Z k) P (1 / 2) :=
  echoProcess_theta_lt_vartheta hα hZ hind hlaw hpos measurable_logLag one_le_logLag
    tendsto_logLag (summable_logLag hα)

/-- **The gap is the late-return mass, explicitly**: for the logarithmic echo process, along any
`uₙ → ∞`, `rₙ → ∞` with `rₙ uₙ^(-α) → 0` and `log uₙ = o(rₙ)` (see
`logEchoProcess_hasLateReturnMass_of_tendsto` for the standard normalization), the cluster ratio
tends to `1/2 = θ`, the late-return mass is `1/2 = ϑ - θ`, and forward anticlustering fails. -/
theorem logEchoProcess_hasLateReturnMass (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hlog : Tendsto (fun n => Real.log (u n) / r n) atTop (𝓝 0)) :
    Tendsto (clusterRatio P (echoProcess logLag Z) u r) atTop (𝓝 (1 / 2)) ∧
      HasLateReturnMass P (echoProcess logLag Z) u r (1 / 2) ∧
      ¬ ForwardAntiClusteringAt P (echoProcess logLag Z) u r := by
  have hR := tendsto_tsum_logLag_div hα hu hr hlog
  exact ⟨tendsto_clusterRatio_echoProcess hα hZ hind hlaw hpos measurable_logLag one_le_logLag
      hu hr hrb (summable_logLag hα) hR,
    hasLateReturnMass_echoProcess hα hZ hind hlaw hpos measurable_logLag one_le_logLag tendsto_logLag
      hu hr hrb (summable_logLag hα) hR,
    not_forwardAntiClusteringAt_echoProcess hα hZ hind hlaw hpos measurable_logLag one_le_logLag
      tendsto_logLag hu hr hrb (summable_logLag hα) hR⟩

/-- **The same in the standard normalization**: along every level sequence with
`n P(X_0 > uₙ) → τ > 0` and every block length with `rₙ / n → 0` and `log n = o(rₙ)` (for
instance `rₙ = ⌊√n⌋`, not checked here), the logarithmic echo process has late-return mass
`1/2 = ϑ - θ` and violates forward anticlustering. -/
theorem logEchoProcess_hasLateReturnMass_of_tendsto (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    Tendsto (clusterRatio P (echoProcess logLag Z) u r) atTop (𝓝 (1 / 2)) ∧
      HasLateReturnMass P (echoProcess logLag Z) u r (1 / 2) ∧
      ¬ ForwardAntiClusteringAt P (echoProcess logLag Z) u r := by
  have hT := hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos measurable_logLag
    one_le_logLag tendsto_logLag
  have hτ' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess logLag Z 0 ω|}) atTop
      (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hτ
  have hu := hT.tendsto_atTop_of_tendsto_mul hτ'
  -- `n uₙ^(-α) → τ / 2`
  have hratio := (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw measurable_logLag
    one_le_logLag 0).comp hu
  have hnb : Tendsto (fun n : ℕ => (n : ℝ) * u n ^ (-α)) atTop (𝓝 (τ / 2)) := by
    refine (hτ.div hratio two_ne_zero).congr' ?_
    filter_upwards [hu.eventually_ge_atTop 1] with n hn
    have h0 : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    have hP : 0 < P.real {ω | u n < echoProcess logLag Z 0 ω} := by
      refine h0.trans_le ?_
      rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hn]
      exact measureReal_mono fun ω hω => lt_of_lt_of_le hω (le_echoProcess 0 ω)
    simp only [Pi.div_apply, Function.comp_apply]
    field_simp
  have hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0) := by
    have := hrn.mul hnb
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  -- `log uₙ ≤ (log (4 / τ) + log n) / α`, hence `log uₙ = o(rₙ)`
  have hlog : Tendsto (fun n => Real.log (u n) / r n) atTop (𝓝 0) := by
    have hc : Tendsto (fun n => (Real.log (4 / τ) / r n + Real.log n / r n) / α) atTop (𝓝 0) := by
      have := (((tendsto_const_nhds (x := Real.log (4 / τ))).div_atTop
        (tendsto_natCast_atTop_atTop.comp hr)).add hlogr).div_const α
      simpa using this
    refine squeeze_zero' ?_ ?_ hc
    · filter_upwards [hu.eventually_ge_atTop 1] with n hn
      exact div_nonneg (Real.log_nonneg hn) (Nat.cast_nonneg _)
    · filter_upwards [hu.eventually_ge_atTop 1, hr.eventually_gt_atTop 0,
        hnb.eventually (lt_mem_nhds (show τ / 4 < τ / 2 by linarith)),
        eventually_gt_atTop 0] with n hn hrn0 hnb' hn0
      have hR : (0 : ℝ) < r n := by exact_mod_cast hrn0
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      have hupos : 0 < u n := by linarith
      have hpow : u n ^ α ≤ 4 / τ * n := by
        have h0 : 0 < u n ^ α := Real.rpow_pos_of_pos hupos _
        rw [Real.rpow_neg hupos.le] at hnb'
        rw [← div_lt_iff₀' hn', lt_inv_comm₀ (by positivity) h0] at hnb'
        calc u n ^ α ≤ (τ / 4 / n)⁻¹ := hnb'.le
          _ = 4 / τ * n := by field_simp
      have hl : α * Real.log (u n) ≤ Real.log (4 / τ) + Real.log n := by
        rw [← Real.log_rpow hupos, ← Real.log_mul (by positivity) hn'.ne']
        exact Real.log_le_log (Real.rpow_pos_of_pos hupos _) hpow
      rw [div_le_div_iff₀ hR hα, ← add_div, div_mul_eq_mul_div, le_div_iff₀ hR]
      nlinarith
  exact logEchoProcess_hasLateReturnMass hα hZ hind hlaw hpos hu hr hrb hlog

end LogLag

end ExtremeValueTheory

/-! ### Deprecated names -/

namespace ExtremeValueTheory

@[deprecated (since := "2026-10-23")] alias hasEscapeMass_echoProcess := hasLateReturnMass_echoProcess
@[deprecated (since := "2026-10-23")] alias logEchoProcess_hasEscapeMass := logEchoProcess_hasLateReturnMass
@[deprecated (since := "2026-10-23")] alias logEchoProcess_hasEscapeMass_of_tendsto := logEchoProcess_hasLateReturnMass_of_tendsto

end ExtremeValueTheory
