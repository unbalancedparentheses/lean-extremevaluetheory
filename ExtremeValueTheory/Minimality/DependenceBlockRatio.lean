/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MixtureProcess

/-!
# Minimal hypotheses for the cluster ratio and for `Θ_t → 0`

We test each hypothesis of

* `HasSpectralTailProcess.tendsto_blockRatio`: stationarity, spectral tail process, `uₙ → ∞`,
  `rₙ → ∞` and forward anticlustering `ForwardAntiClusteringAt P X u r` give
  `P(max_{0 ≤ t < rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ)) → ϑ`;
* `HasSpectralTailProcess.tendsto_zero_of_forwardAntiClusteringAt`: spectral tail process,
  `uₙ → ∞`, `rₙ → ∞` and forward anticlustering at the one level sequence `uₙ` give
  `Θ_t → 0` a.s.

## Findings

* **Anticlustering cannot be dropped from `tendsto_blockRatio`** (`logEcho_blockRatio_ne`): the
  logarithmic echo process is stationary, has a spectral tail process with `ϑ = 1`, and for
  `n P(X_0 > uₙ) → τ > 0`, `rₙ / n → 0`, `log n = o(rₙ)` its cluster ratio tends to `1/2 ≠ ϑ`;
  forward anticlustering fails.
* **But anticlustering is not necessary** (`mixture_tendsto_blockRatio_of_not_antiClustering`):
  the constant/iid mixture has cluster ratio `→ ϑ` while forward anticlustering fails. The sharp
  condition is already known: the cluster ratio tends to `ϑ` *iff* the late-return mass vanishes,
  `η = 0` (`HasSpectralTailProcess.tendsto_clusterRatio_iff`, which needs no anticlustering).
* **`rₙ → ∞` cannot be dropped** (`movingMax_blockRatio_const_one`): for any process, bounded
  block lengths satisfy forward anticlustering vacuously (`forwardAntiClusteringAt_of_le`); for the
  moving maximum with `rₙ = 1` the cluster ratio is identically `1`, while `ϑ = 1/2`.
* **`Θ_t → 0` does not need anticlustering** (`logEcho_tendsto_zero_of_not_antiClustering`): the
  echo process has `Θ_t = 1{t = 0}` but violates forward anticlustering.
* **`rₙ → ∞` cannot be dropped from `tendsto_zero_of_forwardAntiClusteringAt`**
  (`mixture_not_tendsto_zero_of_const_one`): with `rₙ = 1` anticlustering is vacuous, and the
  mixture's spectral tail process is `Θ ≡ 1` with probability `p > 0`.
* One level sequence suffices for `Θ_t → 0` (this is how
  `tendsto_zero_of_forwardAntiClusteringAt` is stated; the proof transfers the level `1` of the tail
  process to every level through the Pareto radius). Whether `uₙ → ∞` can be weakened is left
  open; for a stationary process and a *constant* level `u` with `P(|X_0| > u) > 0`, Poincaré
  recurrence makes anticlustering with `rₙ → ∞` impossible (not formalized), so the hypothesis is
  only restrictive for non-stationary processes or levels oscillating without diverging.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory.Minimality

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℤ → Ω → ℝ}

/-- **Bounded block lengths satisfy forward anticlustering vacuously**: if `rₙ ≤ R` for all `n`,
the lags `R + 1 ≤ t ≤ rₙ` form an empty range. -/
theorem forwardAntiClusteringAt_of_le {u : ℕ → ℝ} {r : ℕ → ℕ} {R : ℕ} (hR : ∀ n, r n ≤ R) :
    ForwardAntiClusteringAt P X u r := by
  intro ε hε
  refine ⟨R + 1, Eventually.of_forall fun n => ?_⟩
  have : {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, ((R + 1 : ℕ) : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X t ω|} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
    intro _ t h1 h2
    have := hR n
    omega
  rw [this, measureReal_empty]
  exact mul_nonneg hε.le measureReal_nonneg

/-- With blocks of length `1` the cluster ratio is `1` (whenever `P(|X_0| > uₙ) > 0`). -/
theorem clusterRatio_const_one {u : ℕ → ℝ} {n : ℕ} (hp : 0 < P.real {ω | u n < |X 0 ω|}) :
    clusterRatio P X u (fun _ => 1) n = 1 := by
  have : {ω | ∃ t ∈ Finset.Ico (0 : ℤ) ((fun _ => 1 : ℕ → ℕ) n), u n < |X t ω|} =
      {ω | u n < |X 0 ω|} := by
    ext ω
    simp only [mem_ofPred_eq, Nat.cast_one]
    constructor
    · rintro ⟨t, ht, h⟩
      have : t = 0 := by rw [Finset.mem_Ico] at ht; omega
      rwa [this] at h
    · intro h
      exact ⟨0, by simp, h⟩
  rw [clusterRatio, this, Nat.cast_one, one_mul, div_self hp.ne']

end General

/-! ### `rₙ → ∞` is needed: the moving maximum with blocks of length one -/

section MovingMax

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- **`rₙ → ∞` cannot be dropped from `tendsto_blockRatio`.** For the moving maximum
`X_t = max(Z_t, Z_{t+1})` of iid Pareto(`α`) noise and the constant block length `rₙ = 1`: the
process is stationary, has a spectral tail process with `ϑ = 1/2`, and forward anticlustering holds
(vacuously) along every `uₙ`; yet the cluster ratio is identically `1`. -/
theorem movingMax_blockRatio_const_one (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) (u : ℕ → ℝ) :
    HasShiftInvariantWindows P (movingMax Z) ∧
      HasSpectralTailProcess P (movingMax Z) α fairCoin movingMaxSpectral ∧
      (candidateExtremalIndex fairCoin movingMaxSpectral α).toReal = 1 / 2 ∧
      ForwardAntiClusteringAt P (movingMax Z) u (fun _ => 1) ∧
      Tendsto (clusterRatio P (movingMax Z) u (fun _ => 1)) atTop (𝓝 1) ∧
      ¬ Tendsto (clusterRatio P (movingMax Z) u (fun _ => 1)) atTop
        (𝓝 (candidateExtremalIndex fairCoin movingMaxSpectral α).toReal) := by
  have hF : Measurable fun y : Fin 2 → ℝ => max (y 0) (y 1) :=
    (measurable_pi_apply 0).max (measurable_pi_apply 1)
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have hstat : HasShiftInvariantWindows P (movingMax Z) := by
    rw [movingMax_eq_slidingWindow]
    exact (hasShiftInvariantWindows_of_iIndepFun hZ hind hid).slidingWindow hZ _ hF
  have hT := hasSpectralTailProcess_movingMax hα hZ hind hlaw hpos
  have hϑ : (candidateExtremalIndex fairCoin movingMaxSpectral α).toReal = 1 / 2 := by
    rw [candidateExtremalIndex_movingMax hα]; norm_num
  have h1 : Tendsto (clusterRatio P (movingMax Z) u (fun _ => 1)) atTop (𝓝 1) :=
    tendsto_const_nhds.congr fun n => (clusterRatio_const_one (hT.measureReal_lt_abs_pos _)).symm
  refine ⟨hstat, hT, hϑ, forwardAntiClusteringAt_of_le (R := 1) fun _ => le_rfl, h1, fun h2 => ?_⟩
  have := tendsto_nhds_unique h1 h2
  rw [hϑ] at this
  norm_num at this

end MovingMax

/-! ### Anticlustering: not removable, not necessary -/

section Echo

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- **Anticlustering cannot be dropped from `tendsto_blockRatio`.** The logarithmic echo process
satisfies every other hypothesis (stationarity, spectral tail process with `ϑ = 1`, `uₙ → ∞`,
`rₙ → ∞`), but along `n P(X_0 > uₙ) → τ > 0` with `rₙ / n → 0` and `log n = o(rₙ)` its cluster
ratio tends to `1/2`, not to `ϑ`; forward anticlustering fails. -/
theorem logEcho_blockRatio_ne (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    HasShiftInvariantWindows P (echoProcess logLag Z) ∧
      HasSpectralTailProcess P (echoProcess logLag Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      Tendsto u atTop atTop ∧
      ¬ ForwardAntiClusteringAt P (echoProcess logLag Z) u r ∧
      ¬ Tendsto (clusterRatio P (echoProcess logLag Z) u r) atTop
        (𝓝 (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal) := by
  obtain ⟨hstat, hT, hϑ, -⟩ := logEchoProcess_theta_lt_vartheta hα hZ hind hlaw hpos
  obtain ⟨hratio, -, hAC⟩ :=
    logEchoProcess_hasLateReturnMass_of_tendsto hα hZ hind hlaw hpos hτ0 hτ hr hrn hlogr
  have hτ' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess logLag Z 0 ω|}) atTop
      (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hτ
  refine ⟨hstat, hT, hϑ, hT.tendsto_atTop_of_tendsto_mul hτ', hAC, fun h => ?_⟩
  have := tendsto_nhds_unique hratio h
  rw [hϑ] at this
  norm_num at this

/-- **`Θ_t → 0` does not need anticlustering.** The logarithmic echo process has spectral tail
process `Θ_t = 1{t = 0}`, so `Θ_t → 0`, but violates forward anticlustering along every
`n P(X_0 > uₙ) → τ > 0` with `rₙ / n → 0`, `log n = o(rₙ)`. So the converse of
`tendsto_zero_of_forwardAntiClusteringAt` fails. -/
theorem logEcho_tendsto_zero_of_not_antiClustering (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    HasSpectralTailProcess P (echoProcess logLag Z) α (Measure.dirac ()) unitSpectral ∧
      (∀ᵐ ω' ∂(Measure.dirac ()), Tendsto (fun k : ℕ => unitSpectral k ω') atTop (𝓝 0)) ∧
      ¬ ForwardAntiClusteringAt P (echoProcess logLag Z) u r := by
  obtain ⟨-, hT, -, -⟩ := logEchoProcess_theta_lt_vartheta hα hZ hind hlaw hpos
  obtain ⟨-, -, hAC⟩ :=
    logEchoProcess_hasLateReturnMass_of_tendsto hα hZ hind hlaw hpos hτ0 hτ hr hrn hlogr
  refine ⟨hT, Eventually.of_forall fun ω' => ?_, hAC⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  simp [unitSpectral]; omega

end Echo

section Mixture

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {E : Set Ω}

/-- **Anticlustering is not necessary for `tendsto_blockRatio`.** For the constant/iid mixture with
`P(E) > 0`, along `uₙ → ∞`, `rₙ → ∞`, `rₙ uₙ^(-α) → 0`, the cluster ratio tends to `ϑ = 1 - P(E)`
although forward anticlustering fails. The exact condition is `η = 0`
(`HasSpectralTailProcess.tendsto_clusterRatio_iff`). -/
theorem mixture_tendsto_blockRatio_of_not_antiClustering (hE : MeasurableSet E)
    (hEZ : Indep (MeasurableSpace.generateFrom {E}) (innovationSigma Z) P) (hα : 0 < α)
    (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)
    (hp0 : 0 < P.real E) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0)) :
    HasShiftInvariantWindows P (mixtureProcess E Z) ∧
      HasSpectralTailProcess P (mixtureProcess E Z) α (mixtureCoin (P.real E)) mixtureSpectral ∧
      ¬ ForwardAntiClusteringAt P (mixtureProcess E Z) u r ∧
      Tendsto (clusterRatio P (mixtureProcess E Z) u r) atTop
        (𝓝 (candidateExtremalIndex (mixtureCoin (P.real E)) mixtureSpectral α).toReal) := by
  refine ⟨hasShiftInvariantWindows_mixture hE hEZ hZ hind hlaw,
    hasSpectralTailProcess_mixture hE hEZ hα hZ hind hlaw hpos,
    not_forwardAntiClusteringAt_mixture hEZ hα hZ hlaw hpos hp0 hu hr, ?_⟩
  rw [candidateExtremalIndex_mixture hα, ENNReal.toReal_ofReal
    (by have := measureReal_le_one (μ := P) (s := E); linarith)]
  exact tendsto_clusterRatio_mixture hE hEZ hα hZ hind hlaw hpos hu hr hrb

/-- **`rₙ → ∞` cannot be dropped from `tendsto_zero_of_forwardAntiClusteringAt`.** With `rₙ = 1`
forward anticlustering holds vacuously (along every `uₙ`, in particular along `uₙ → ∞`), but the
mixture's spectral tail process is `Θ ≡ 1` on a set of probability `P(E) > 0`, so `Θ_t ↛ 0`. -/
theorem mixture_not_tendsto_zero_of_const_one (hE : MeasurableSet E)
    (hEZ : Indep (MeasurableSpace.generateFrom {E}) (innovationSigma Z) P) (hα : 0 < α)
    (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)
    (hp0 : 0 < P.real E) (u : ℕ → ℝ) :
    HasSpectralTailProcess P (mixtureProcess E Z) α (mixtureCoin (P.real E)) mixtureSpectral ∧
      ForwardAntiClusteringAt P (mixtureProcess E Z) u (fun _ => 1) ∧
      ¬ ∀ᵐ b ∂(mixtureCoin (P.real E)), Tendsto (fun k : ℕ => mixtureSpectral k b) atTop (𝓝 0) := by
  refine ⟨hasSpectralTailProcess_mixture hE hEZ hα hZ hind hlaw hpos,
    forwardAntiClusteringAt_of_le (R := 1) fun _ => le_rfl, fun h => ?_⟩
  have hnull := ae_iff.1 h
  have hsub : ({true} : Set Bool) ⊆
      {b | ¬ Tendsto (fun k : ℕ => mixtureSpectral k b) atTop (𝓝 0)} := by
    intro b hb
    rw [mem_singleton_iff] at hb
    subst hb
    simp only [mem_ofPred_eq]
    intro ht
    have h1 : Tendsto (fun k : ℕ => mixtureSpectral k true) atTop (𝓝 1) :=
      tendsto_const_nhds.congr fun k => by simp [mixtureSpectral]
    exact one_ne_zero (tendsto_nhds_unique h1 ht)
  have h0 := measure_mono_null hsub hnull
  simp [mixtureCoin] at h0
  rw [measureReal_def, h0] at hp0
  simp at hp0

end Mixture

end ExtremeValueTheory.Minimality

/-! ### Deprecated names -/

namespace ExtremeValueTheory

@[deprecated (since := "2026-10-23")] alias forwardAntiClusteringAt_of_le := Minimality.forwardAntiClusteringAt_of_le
@[deprecated (since := "2026-10-23")] alias clusterRatio_const_one := Minimality.clusterRatio_const_one
@[deprecated (since := "2026-10-23")] alias movingMax_blockRatio_const_one := Minimality.movingMax_blockRatio_const_one
@[deprecated (since := "2026-10-23")] alias logEcho_blockRatio_ne := Minimality.logEcho_blockRatio_ne
@[deprecated (since := "2026-10-23")] alias logEcho_tendsto_zero_of_not_antiClustering := Minimality.logEcho_tendsto_zero_of_not_antiClustering
@[deprecated (since := "2026-10-23")] alias mixture_tendsto_blockRatio_of_not_antiClustering := Minimality.mixture_tendsto_blockRatio_of_not_antiClustering
@[deprecated (since := "2026-10-23")] alias mixture_not_tendsto_zero_of_const_one := Minimality.mixture_not_tendsto_zero_of_const_one

end ExtremeValueTheory
