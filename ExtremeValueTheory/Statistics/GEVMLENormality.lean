/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLEPath
import ExtremeValueTheory.Statistics.GPDJointNormality
import ExtremeValueTheory.Statistics.ExtremeQuantileSecondOrder
import ExtremeValueTheory.Statistics.MeasurableArgmax

/-!
# Joint asymptotic normality of the three-parameter GEV maximum likelihood estimator

Let `X₀, X₁, …` be iid with the location-scale GEV law of parameter `θ₀ = (ξ₀, μ₀, σ₀)`,
`ξ₀ > -1/2`, `ξ₀ ≠ 0`, `σ₀ > 0` (the regular case of [Smith 1985]).

* `tendstoInDistribution_gevLocalMLE`: strongly consistent local maximizers of the likelihood, at
  which every observation is in the support, satisfy `√n (θ̂ₙ - θ₀) ⇒ N(0, V(θ₀))`.
* `tendstoInDistribution_gevMLE`: **maximizers over a compact parameter set**
  `K ⊂ {ξ > -1, σ > 0}` with `θ₀` in its interior are asymptotically normal: consistency is
  `ae_tendsto_gevMLE`, and such maximizers are eventually local maximizers.
* `tendstoInDistribution_gevMLE_muSigmaXi`: the same in the order `(μ, σ, ξ)` of `gevFisherInfo`.
* `exists_measurable_gevMLE`, `exists_gevMLE_tendstoInDistribution`: measurable maximizers exist,
  so the theorem is not vacuous.

Here `V(θ₀) = gevMLECov ξ₀ σ₀` is the inverse Fisher information `I(θ₀)⁻¹` of
`ExtremeValueTheory.gevFisherInfo` (positive definite by `posDef_gevFisherInfo`, equal to minus the
expected Hessian by `integral_gevHess_eq_neg_gevFisherInfo`), with rows and columns permuted to the
order `(ξ, μ, σ)` of the parameters.

## Proof

The classical expansion of the likelihood equations cannot be applied directly, because the
support of the density moves with the parameter, and `√n (θ̂ₙ - θ₀)` must be bounded before
anything is known about how close `θ̂ₙ` is to the observations near the endpoint.

* Work in the coordinates `η` of `ExtremeValueTheory.Statistics.GEVMLECoordinates`, in which the
  support function is affine: the segment from the truth to `η̂ₙ` lies in the support of every
  observation.
* **The rate** (`gevPath_estimates`): the second derivative of the log-density has a one-sided bound
  which holds for every observation in the support (`exists_gevEtaM_self_le`); with the mean value
  theorem, it gives `√n |η̂ₙ - η₀| ≤ C |Zₙ|`, `Zₙ` the normalized score.
* **Domination at the moving endpoint**: `max_{i<n} 1/v(Xᵢ) = o_P(√n)`
  (`tendstoInMeasure_runMax_gevU_div_sqrt`): this is where `ξ₀ > -1/2` enters, on top of the
  integrability of the envelope. So with probability tending to `1` every observation is good all
  along the segment (`v/2 ≤ u ≤ 2v`), and the second derivative is two-sidedly dominated.
* **The Slutsky step**: then `I(θ₀) √n (θ̂ₙ - θ₀) = Zₙ + o_P(1 + |Zₙ|)`; no inversion of a random
  matrix is needed. The score CLT `tendstoInDistribution_gevScoreLin` concludes.

## Not covered

* The Gumbel case `ξ₀ = 0`: the score and Hessian are written for `ξ ≠ 0` (they extend continuously
  to `ξ = 0`, but this extension and its information matrix are not formalized, and the coordinates
  `η` are singular there).
* The boundary `ξ₀ = -1/2` and the nonregular case `-1 < ξ₀ < -1/2` of [Smith 1985], where the rate
  differs from `√n`.
* The results are for maximizers over a compact parameter set, or for consistent local maximizers;
  the existence of a consistent sequence of local maximizers without a compact parameter set
  ([Bücher–Segers 2017, Theorem 2]) is not formalized.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* A. Bücher and J. Segers, *On the maximum likelihood estimator for the Generalized Extreme-Value
  distribution*, Extremes 20 (2017).
* D. Prescott and A. T. Walden, *Maximum likelihood estimation of the parameters of the
  generalized extreme-value distribution*, Biometrika 67 (1980).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace ExtremeValueTheory

/-! ### The error term has vanishing expectation -/

section Tail

variable {ξ₀ μ₀ σ₀ ε K : ℝ}

lemma measurable_gevEnvM (ξ₀ ε : ℝ) : Measurable (gevEnvM ξ₀ ε) :=
  measurable_gevEnv_comp measurable_id

lemma measurable_gevEtaTail (ξ₀ ε K c : ℝ) : Measurable (gevEtaTail ξ₀ ε K c) :=
  (measurable_const.mul (measurable_gevEnvM ξ₀ ε)).indicator measurableSet_Icc.compl

lemma measurable_gevEtaTail_gevU (ξ₀ ε K c μ₀ σ₀ : ℝ) :
    Measurable fun x => gevEtaTail ξ₀ ε K c (gevU ξ₀ μ₀ σ₀ x) :=
  (measurable_gevEtaTail ξ₀ ε K c).comp (measurable_gevU ξ₀ μ₀ σ₀)

lemma abs_gevEtaTail_le (hK : 0 ≤ K) {c v : ℝ} (hv : 0 < v) (hε : 0 < ε) :
    |gevEtaTail ξ₀ ε K c v| ≤ K * gevEnvM ξ₀ ε v := by
  rw [abs_of_nonneg (gevEtaTail_nonneg hK hv)]
  exact Set.indicator_le_self' (fun _ _ => mul_nonneg hK ((one_le_gevEnvM hε hv).trans' zero_le_one)) v

lemma integrable_gevEtaTail (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hε : 0 < ε) (hK : 0 ≤ K)
    (ha : -1 < (gevAw ξ₀ + 2 + 2 * ε) * ξ₀) (hb : (gevBw ξ₀ + 2 * ε) * ξ₀ < 1) (c : ℝ) :
    Integrable (fun x => gevEtaTail ξ₀ ε K c (gevU ξ₀ μ₀ σ₀ x))
      (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure := by
  refine ((integrable_gevEnvM hξ₀0 hσ₀ ha hb).const_mul K).mono'
    (measurable_gevEtaTail_gevU ξ₀ ε K c μ₀ σ₀).aestronglyMeasurable ?_
  filter_upwards [ae_gevU_pos hξ₀0 hσ₀] with x hx
  rw [Real.norm_eq_abs]
  exact abs_gevEtaTail_le hK hx hε

/-- **The expectation of the error term vanishes as `c → 0`**, by dominated convergence. -/
theorem tendsto_integral_gevEtaTail (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hε : 0 < ε) (hK : 0 ≤ K)
    (ha : -1 < (gevAw ξ₀ + 2 + 2 * ε) * ξ₀) (hb : (gevBw ξ₀ + 2 * ε) * ξ₀ < 1) :
    Tendsto (fun k : ℕ => ∫ x, gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (gevU ξ₀ μ₀ σ₀ x)
      ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure) atTop (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _x, (0 : ℝ) ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence
    (fun x => K * gevEnvM ξ₀ ε (gevU ξ₀ μ₀ σ₀ x))
    (fun k => (measurable_gevEtaTail_gevU ξ₀ ε K _ μ₀ σ₀).aestronglyMeasurable)
    ((integrable_gevEnvM hξ₀0 hσ₀ ha hb).const_mul K) (fun k => ?_) ?_
  · filter_upwards [ae_gevU_pos hξ₀0 hσ₀] with x hx
    rw [Real.norm_eq_abs]
    exact abs_gevEtaTail_le hK hx hε
  · filter_upwards [ae_gevU_pos hξ₀0 hσ₀] with x hx
    refine tendsto_const_nhds.congr' ?_
    have h1 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ gevU ξ₀ μ₀ σ₀ x := by
      have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact (this.eventually (gt_mem_nhds hx)).mono fun _ h => h.le
    have h2 : ∀ᶠ k : ℕ in atTop, gevU ξ₀ μ₀ σ₀ x ≤ (k : ℝ) + 1 := by
      obtain ⟨m, hm⟩ := exists_nat_ge (gevU ξ₀ μ₀ σ₀ x)
      filter_upwards [eventually_ge_atTop m] with k hk
      have : (m : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    filter_upwards [h1, h2] with k hk1 hk2
    have hmem : gevU ξ₀ μ₀ σ₀ x ∈ Icc (1 / ((k : ℝ) + 1)) (1 / (1 / ((k : ℝ) + 1))) :=
      ⟨hk1, by rwa [one_div_one_div]⟩
    exact (gevEtaTail_of_mem hmem).symm

end Tail

/-! ### The moving endpoint: `max_{i<n} 1/v(Xᵢ) = o_P(√n)` -/

section RunMax

variable {ξ₀ μ₀ σ₀ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- **The observation nearest to the moving endpoint**: `max_{i<n} 1/v(Xᵢ) / √n → 0` in
probability, for `ξ₀ > -1/2`, `ξ₀ ≠ 0`, with `v = 1 + ξ₀ (x - μ₀)/σ₀`. On the exponential scale
`1/v = t^{ξ₀}`, and `t^{p ξ₀}` is integrable for some `p > 2`, exactly because `ξ₀ > -1/2`. -/
theorem tendstoInMeasure_runMax_gevU_div_sqrt (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) :
    TendstoInMeasure P (fun n ω => runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (X i ω)) n / √(n : ℝ))
      atTop (fun _ => 0) := by
  obtain ⟨p, hp2, hp⟩ : ∃ p : ℝ, 2 < p ∧ -1 < p * ξ₀ := by
    rcases lt_or_gt_of_ne hξ₀0 with h | h
    · have h1 : 0 < -ξ₀ := by linarith
      have h2 : 2 < 1 / -ξ₀ := by rw [lt_div_iff₀ h1]; linarith
      refine ⟨(2 + 1 / -ξ₀) / 2, by linarith, ?_⟩
      have e : (2 + 1 / -ξ₀) / 2 * ξ₀ = ξ₀ - 1 / 2 := by
        have := h.ne
        field_simp
        ring
      rw [e]
      linarith
    · exact ⟨3, by norm_num, by nlinarith⟩
  have hI : Integrable (fun x => gevEnv p 0 (gevU ξ₀ μ₀ σ₀ x))
      (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure :=
    integrable_gevEnv hξ₀0 hσ₀ hp (by norm_num)
  set E := ∫ x, gevEnv p 0 (gevU ξ₀ μ₀ σ₀ x) ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure with hE
  have hE0 : 0 ≤ E := integral_nonneg_of_ae (by
    filter_upwards [ae_gevU_pos hξ₀0 hσ₀] with x hx
    exact gevEnv_nonneg hx.le)
  -- Markov's inequality
  have hmarkov : ∀ i, ∀ s : ℝ, 0 < s →
      P {ω | s ≤ 1 / gevU ξ₀ μ₀ σ₀ (X i ω)} ≤ ENNReal.ofReal (E / s ^ p) := fun i s hs => by
    have hm : MeasurableSet {x : ℝ | s ^ p ≤ gevEnv p 0 (gevU ξ₀ μ₀ σ₀ x)} :=
      measurableSet_le measurable_const (measurable_gevEnv_gevU p 0 ξ₀ μ₀ σ₀)
    have hsub : {ω | s ≤ 1 / gevU ξ₀ μ₀ σ₀ (X i ω)} ⊆
        X i ⁻¹' {x : ℝ | s ^ p ≤ gevEnv p 0 (gevU ξ₀ μ₀ σ₀ x)} := fun ω hω => by
      simp only [mem_ofPred_eq, mem_preimage] at hω ⊢
      set u := gevU ξ₀ μ₀ σ₀ (X i ω)
      have hu : 0 < u := one_div_pos.1 (hs.trans_le hω)
      have h1 : s ^ p ≤ (1 / u) ^ p := rpow_le_rpow hs.le hω (by linarith)
      have h2 : (1 / u) ^ p = u ^ (-p) := by
        rw [one_div, inv_rpow hu.le, rpow_neg hu.le]
      rw [h2] at h1
      have h3 := rpow_le_gevEnv (a := p) (b := 0) (r := -p) hu le_rfl (by linarith)
      linarith
    refine (measure_mono hsub).trans ?_
    rw [← Measure.map_apply_of_aemeasurable (hX i).aemeasurable hm, (hX i).map_eq]
    have h4 := mul_meas_ge_le_integral_of_nonneg (μ := (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure)
      (f := fun x => gevEnv p 0 (gevU ξ₀ μ₀ σ₀ x))
      (by filter_upwards [ae_gevU_pos hξ₀0 hσ₀] with x hx; exact gevEnv_nonneg hx.le) hI (s ^ p)
    have hsp : 0 < s ^ p := by positivity
    rw [measureReal_def] at h4
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hsp, mul_comm]
    exact h4
  rw [tendstoInMeasure_iff_dist]
  intro η hη
  have hl0 := (tendsto_natCast_mul_div_sqrt_rpow (C := 1 / η) (by positivity) hp2).const_mul E
  rw [mul_zero] at hl0
  have hlim := (ENNReal.continuous_ofReal.tendsto 0).comp hl0
  rw [ENNReal.ofReal_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsq : 0 < √(n : ℝ) := sqrt_pos.2 (by exact_mod_cast hn)
  set s := η * √(n : ℝ) with hs
  have hs0 : 0 < s := by positivity
  have hsub : {ω | η ≤ dist (runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (X i ω)) n / √(n : ℝ)) 0} ⊆
      ⋃ i ∈ Finset.range n, {ω | s ≤ 1 / gevU ξ₀ μ₀ σ₀ (X i ω)} := by
    intro ω hω
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
    rw [abs_of_nonneg (div_nonneg (runMax_nonneg _ _) hsq.le), le_div_iff₀ hsq] at hω
    obtain ⟨i, hi, hfi⟩ := exists_le_of_le_runMax _ hs0 hω
    exact mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hfi⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun i _ => hmarkov i s hs0).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Function.comp_apply]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have e1 : (1 / η / √(n : ℝ)) ^ p = 1 / s ^ p := by
    rw [div_div, hs, div_rpow zero_le_one (by positivity), one_rpow]
  rw [e1]
  ring

/-- `(1 + max_{i<n} 1/v(Xᵢ)) / √n → 0` in probability. -/
theorem tendstoInMeasure_one_add_runMax_gevU_div_sqrt (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0)
    (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) :
    TendstoInMeasure P (fun n ω => (1 + runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (X i ω)) n) / √(n : ℝ))
      atTop (fun _ => 0) := by
  have h1 : TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => 1 / √(n : ℝ)) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const) ?_
    refine ae_of_all _ fun _ => ?_
    exact tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have := tendstoInMeasure_add_zero h1 (tendstoInMeasure_runMax_gevU_div_sqrt hξ₀ hξ₀0 hσ₀ hX)
  refine this.congr_left (fun n => ae_of_all _ fun ω => ?_)
  simp only
  ring

end RunMax

/-! ### The score CLT for a linear image of the score -/

section ScoreLin

variable {ξ μ σ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- The linear image `B ∇ℓ` of the score, in `ℝ³`. -/
noncomputable def gevScoreLin (B : Matrix (Fin 3) (Fin 3) ℝ) (ξ μ σ x : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (B.mulVec (gevScore ξ μ σ x))

lemma measurable_gevScoreLin (B : Matrix (Fin 3) (Fin 3) ℝ) (ξ μ σ : ℝ) :
    Measurable (gevScoreLin B ξ μ σ) := by
  unfold gevScoreLin
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  have h : ∀ j, Measurable fun x => gevScore ξ μ σ x j := fun j => by
    fin_cases j
    · simpa [gevScore] using measurable_gevScoreMu ξ μ σ
    · simpa [gevScore] using measurable_gevScoreSigma ξ μ σ
    · simpa [gevScore] using measurable_gevScoreXi ξ μ σ
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ => (h j).const_mul _

/-- **The CLT for a linear image of the score**: `n^{-1/2} ∑_{i<n} B ∇ℓ(Xᵢ) ⇒ N(0, S)`, where
`S = B I Bᵀ`. -/
theorem tendstoInDistribution_gevScoreLin (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ μ hσ).measure P) (hind : iIndepFun X P)
    {B S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.PosSemidef)
    (hB : B * gevFisherInfo ξ σ * B.transpose = S) {W : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hW : HasLaw W (multivariateGaussian 0 S) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gevScoreLin B ξ μ σ (X i ω))
      atTop W (fun _ => P) P' := by
  refine TendstoInDistribution.of_inner hW.aemeasurable (fun n => ?_) fun v => ?_
  · have := measurable_gevScoreLin B ξ μ σ
    have := fun i => (hX i).aemeasurable
    fun_prop
  set t : Fin 3 → ℝ := fun i => v i with ht
  set u : Fin 3 → ℝ := B.transpose.mulVec t with hu
  set f : ℝ → ℝ := fun x => u ⬝ᵥ gevScore ξ μ σ x with hf_def
  have hf : Measurable f := measurable_dotProduct_gevScore u
  have hinner : ∀ x, ⟪gevScoreLin B ξ μ σ x, v⟫ = f x := fun x => by
    have : f x = t ⬝ᵥ B.mulVec (gevScore ξ μ σ x) := by
      simp only [hf_def, hu]
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    rw [this]
    simp [gevScoreLin, PiLp.inner_apply, dotProduct, ht, Fin.sum_univ_three, mul_comm]
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_dotProduct_gevScore hσ hξ0 hξ u
  have hint : ∀ g : ℝ → ℝ, Measurable g →
      P[g ∘ X 0] = ∫ x, g x ∂(gevLocScaleCDF ξ μ hσ).measure :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    exact integral_dotProduct_gevScore hσ hξ0 hξ u
  have hvar : Var[Y 0; P] = v ⬝ᵥ S *ᵥ v := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this
    simp only [Function.comp_def]
    have key : u ⬝ᵥ gevFisherInfo ξ σ *ᵥ u = t ⬝ᵥ S *ᵥ t := by
      rw [← hB]
      simp only [hu]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec t B,
        ← Matrix.mulVec_transpose]
    rw [this, integral_dotProduct_gevScore_sq hσ hξ0 hξ]
    exact key
  have hZt : HasLaw (fun ω => ⟪W ω, v⟫) (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by
    rw [hvar]
    exact hasLaw_inner_multivariateGaussian hS hW v
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp [Y, hinner]

end ScoreLin

/-! ### Convergence in probability of the linearization -/

section Linearization

variable {ξ₀ μ₀ σ₀ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

lemma measurable_gevEtaM_self (ξ₀ μ₀ σ₀ : ℝ) (d e : ℝ × ℝ × ℝ) :
    Measurable fun x => gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ x) d e := by
  have hU := measurable_gevU ξ₀ μ₀ σ₀
  simp only [gevEtaM, gevEtaDDY, gevEtaDY, gevEtaY, gevEtaU_self]
  fun_prop

lemma integrable_gevEtaM_self (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀)
    (d e : ℝ × ℝ × ℝ) :
    Integrable (fun x => gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ x) d e)
      (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure := by
  have hH := integrable_gevHess_entry (μ₀ := μ₀) hσ₀ hξ₀0 hξ₀
  have hI : Integrable (fun x => (∑ j, ∑ k, gevEtaJ ξ₀ σ₀ d j * gevEtaJ ξ₀ σ₀ e k *
      gevHess ξ₀ μ₀ σ₀ x j k) + gevEtaSecond ξ₀ σ₀ d e ⬝ᵥ gevScore ξ₀ μ₀ σ₀ x)
      (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure :=
    (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hH j k).const_mul _).add (integrable_dotProduct_gevScore hσ₀ hξ₀0 hξ₀ _)
  refine hI.congr ?_
  filter_upwards [ae_gevU_pos hξ₀0 hσ₀] with x hx
  exact (gevEtaM_self_eq hξ₀0 hσ₀.ne' hx d e).symm

/-- The Fisher information is invertible. -/
lemma mul_inv_gevFisherInfo (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀) :
    gevFisherInfo ξ₀ σ₀ * (gevFisherInfo ξ₀ σ₀)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.1
    (posDef_gevFisherInfo hσ₀ hξ₀0 hξ₀).isUnit)

/-- The sum of the linearization errors. -/
noncomputable def gevLinErr (ξ₀ μ₀ σ₀ : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℕ → ℝ)
    (θ : ℝ × ℝ × ℝ) (n : ℕ) : ℝ :=
  ∑ j, |√(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ θ j - (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n|

/-- The vector of normalized scores as a function of the sample. -/
lemma gevPathZ_eq_smul_sum (x : ℕ → ℝ) (n : ℕ) (k : Fin 3) :
    gevPathZ ξ₀ μ₀ σ₀ x n k =
      ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gevScoreVec3 ξ₀ μ₀ σ₀ (x i)) k := by
  simp [gevPathZ, gevScoreVec3, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [IsProbabilityMeasure P] in
lemma aemeasurable_gevPathZ (hX : ∀ i, AEMeasurable (X i) P) (n : ℕ) (k : Fin 3) :
    AEMeasurable (fun ω => gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n k) P := by
  have h : Measurable fun x => gevScore ξ₀ μ₀ σ₀ x k := by
    fin_cases k
    · simpa [gevScore] using measurable_gevScoreMu ξ₀ μ₀ σ₀
    · simpa [gevScore] using measurable_gevScoreSigma ξ₀ μ₀ σ₀
    · simpa [gevScore] using measurable_gevScoreXi ξ₀ μ₀ σ₀
  simp only [gevPathZ]
  exact (Finset.aemeasurable_fun_sum _ fun i _ =>
    h.comp_aemeasurable (hX i)).const_mul _

omit [IsProbabilityMeasure P] in
lemma aemeasurable_gevPathZNorm (hX : ∀ i, AEMeasurable (X i) P) (n : ℕ) :
    AEMeasurable (fun ω => gevPathZNorm ξ₀ μ₀ σ₀ (fun i => X i ω) n) P := by
  simp only [gevPathZNorm]
  exact Finset.aemeasurable_fun_sum _ fun k _ => (aemeasurable_gevPathZ hX n k).abs

/-- The normalized scores are bounded in probability, by the score CLT. -/
lemma isBoundedInProbability_gevPathZNorm (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P) :
    IsBoundedInProbability P (fun n ω => gevPathZNorm ξ₀ μ₀ σ₀ (fun i => X i ω) n) := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3))
      (gevFisherInfo ξ₀ σ₀)) (multivariateGaussian 0 (gevFisherInfo ξ₀ σ₀)) := HasLaw.id
  have hclt := tendstoInDistribution_gevScoreVec3 hξ₀ hξ₀0 hσ₀ hX hind hZ
  have hg : Continuous fun z : EuclideanSpace ℝ (Fin 3) => ∑ k, |z k| := by fun_prop
  have h := isBoundedInProbability_of_tendstoInDistribution (hclt.continuous_comp hg)
  convert h using 3 with n ω
  simp only [gevPathZNorm, Function.comp_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [gevPathZ_eq_smul_sum]

/-- **The linearization of the maximum likelihood estimator.** Let `X₀, X₁, …` be iid with the
GEV law of parameter `θ₀`, `ξ₀ > -1/2`, `ξ₀ ≠ 0`, let `A` be the inverse of the Fisher information
and `θ̂ₙ` be measurable, strongly consistent local maximizers of the likelihood at which every
observation is in the support. Then `√n (θ̂ₙ - θ₀) - A Zₙ → 0` in probability, where
`Zₙ = n^{-1/2} ∑_{i<n} ∇ℓ(θ₀, Xᵢ)`. -/
theorem tendstoInMeasure_gevLinErr (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω)) :
    TendstoInMeasure P (fun n ω => gevLinErr ξ₀ μ₀ σ₀ (gevFisherInfo ξ₀ σ₀)⁻¹ (fun i => X i ω)
      (θh n ω) n) atTop (fun _ => 0) := by
  set A := (gevFisherInfo ξ₀ σ₀)⁻¹ with hAdef
  have hA : gevFisherInfo ξ₀ σ₀ * A = 1 := mul_inv_gevFisherInfo hσ₀ hξ₀0 hξ₀
  obtain ⟨ε, hε, ha, hb⟩ := exists_gevEnvM_integrable hξ₀ hξ₀0
  obtain ⟨K, hK0, hdev⟩ := exists_gevEtaM_dev_le hξ₀ hξ₀0 hε
  obtain ⟨lam, hlam0, hlam⟩ := exists_gevEtaInfo_ge hσ₀ hξ₀0 hξ₀
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  -- the sample lies in the support, and the strong laws hold
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (X i ω) := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gevU_pos hξ₀0 hσ₀)
  have hM : ∀ᵐ ω ∂P, ∀ j k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ (X i ω)) (gevEtaBasis j) (gevEtaBasis k)) atTop
      (𝓝 (-gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))) := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
    have h := ae_tendsto_avg_comp hX hind (measurable_gevEtaM_self ξ₀ μ₀ σ₀ _ _)
      (integrable_gevEtaM_self hσ₀ hξ₀0 hξ₀ (gevEtaBasis j) (gevEtaBasis k))
    rwa [integral_gevEtaM_self hσ₀ hξ₀0 hξ₀] at h
  have hT : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (gevU ξ₀ μ₀ σ₀ (X i ω))) atTop
      (𝓝 (∫ x, gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (gevU ξ₀ μ₀ σ₀ x)
        ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure)) :=
    ae_all_iff.2 fun k => ae_tendsto_avg_comp hX hind (measurable_gevEtaTail_gevU ξ₀ ε K _ μ₀ σ₀)
      (integrable_gevEtaTail hξ₀0 hσ₀ hε hK0 ha hb _)
  have ht := tendsto_integral_gevEtaTail (μ₀ := μ₀) hξ₀0 hσ₀ hε hK0 ha hb
  -- the estimates along almost every path
  have hpath' : ∀ᵐ ω ∂P,
      (∀ᶠ n : ℕ in atTop, √(n : ℝ) * gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) ≤
        2 * gevJBound ξ₀ σ₀ / lam * gevPathZNorm ξ₀ μ₀ σ₀ (fun i => X i ω) n) ∧
      ∀ e' : ℝ, 0 < e' → ∀ᶠ n : ℕ in atTop,
        gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) *
          (1 + runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (X i ω)) n) < 1 / 2 →
        ∑ j, |√(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j -
            (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n| ≤
          e' * (1 + gevPathZNorm ξ₀ μ₀ σ₀ (fun i => X i ω) n) := by
    filter_upwards [hsupp, hcons, hloc, hadm, hM, hT] with ω h1 h2 h3 h4 h5 h6
    exact gevPath_estimates (μ₀ := μ₀) hξ₀0 hσ₀ hdev hlam0 hlam hA (x := fun i => X i ω)
      (θh := fun n => θh n ω) h1 h2 h3 h4 h5 h6 ht
  set C₂ := 2 * gevJBound ξ₀ σ₀ / lam with hC₂
  have hC₂0 : 0 ≤ C₂ := by unfold gevJBound at hC₂; rw [hC₂]; positivity
  set Z1 : ℕ → Ω → ℝ := fun n ω => gevPathZNorm ξ₀ μ₀ σ₀ (fun i => X i ω) n with hZ1
  have hZm := fun n => aemeasurable_gevPathZNorm (ξ₀ := ξ₀) (μ₀ := μ₀) (σ₀ := σ₀) hXm n
  have hZb := isBoundedInProbability_gevPathZNorm hξ₀ hξ₀0 hσ₀ hX hind
  have hZ0 : ∀ n ω, 0 ≤ Z1 n ω := fun n ω => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set M : ℕ → Ω → ℝ := fun n ω => runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (X i ω)) n with hMdef
  have hMm : ∀ n, AEMeasurable (M n) P := fun n =>
    aemeasurable_runMax (fun i => by
      have h : Measurable (gevU ξ₀ μ₀ σ₀) := measurable_gevU ξ₀ μ₀ σ₀
      exact (measurable_const.div h).comp_aemeasurable (hXm i)) n
  set N : ℕ → Ω → ℝ := fun n ω => gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) with hNdef
  have hNm : ∀ n, AEMeasurable (N n) P := fun n => by
    have h : Measurable fun θ : ℝ × ℝ × ℝ => gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ θ) := by
      simp only [gevEtaNorm, gevEtaIncr, gevEtaOf, Prod.fst_sub, Prod.snd_sub]
      fun_prop
    exact h.comp_aemeasurable (hθm n)
  set r : ℕ → Ω → ℝ := fun n ω => N n ω * (1 + M n ω) with hr_def
  have hrm : ∀ n, AEMeasurable (r n) P := fun n => (hNm n).mul (aemeasurable_const.add (hMm n))
  -- `rₙ → 0` in probability
  have hr : TendstoInMeasure P r atTop (fun _ => 0) := by
    have hY := tendstoInMeasure_one_add_runMax_gevU_div_sqrt (μ₀ := μ₀) hξ₀ hξ₀0 hσ₀ hX
    have hprod := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hZb hY
    have hg : TendstoInMeasure P (fun n ω => C₂ * ((1 + M n ω) / √(n : ℝ) * Z1 n ω)) atTop
        (fun _ => 0) := by
      have := tendstoInMeasure_comp hprod (φ := fun z => C₂ * z) (by fun_prop)
      simpa only [mul_zero] using this
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le
      (fun n => (hrm n).aestronglyMeasurable) (fun n => ?_) ?_ hg
    · exact (aemeasurable_const.mul ((aemeasurable_const.add (hMm n)).div_const _ |>.mul
        (hZm n))).aestronglyMeasurable
    · filter_upwards [hpath'] with ω hω
      filter_upwards [hω.1, eventually_gt_atTop 0] with n hn hn0
      have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      have hM0 : 0 ≤ M n ω := runMax_nonneg _ _
      have hN0 : 0 ≤ N n ω := gevEtaNorm_nonneg _
      rw [abs_of_nonneg (by simp only [hr_def]; positivity)]
      have e : r n ω = √(n : ℝ) * N n ω * ((1 + M n ω) / √(n : ℝ)) := by
        simp only [hr_def]
        field_simp
      rw [e]
      have : 0 ≤ (1 + M n ω) / √(n : ℝ) := by positivity
      calc √(n : ℝ) * N n ω * ((1 + M n ω) / √(n : ℝ))
          ≤ C₂ * Z1 n ω * ((1 + M n ω) / √(n : ℝ)) := mul_le_mul_of_nonneg_right hn this
        _ = _ := by ring
  -- the error divided by `1 + Zₙ`
  set G : ℕ → Ω → ℝ := fun n ω => gevLinErr ξ₀ μ₀ σ₀ A (fun i => X i ω) (θh n ω) n with hG
  have hGm : ∀ n, AEMeasurable (G n) P := fun n => by
    have hdiff : ∀ j, AEMeasurable (fun ω => gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j) P := fun j => by
      have h1 := hθm n
      fin_cases j
      · exact (measurable_snd.fst.comp_aemeasurable h1).sub_const _
      · exact (measurable_snd.snd.comp_aemeasurable h1).sub_const _
      · exact (measurable_fst.comp_aemeasurable h1).sub_const _
    have hd : ∀ j, AEMeasurable (fun ω => (fun k => A k j) ⬝ᵥ
        gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n) P := fun j => by
      simp only [dotProduct]
      exact Finset.aemeasurable_fun_sum _ fun k _ =>
        (aemeasurable_gevPathZ hXm n k).const_mul _
    simp only [hG, gevLinErr]
    exact Finset.aemeasurable_fun_sum _ fun j _ =>
      ((aemeasurable_const.mul (hdiff j)).sub (hd j)).abs
  set Q : ℕ → Ω → ℝ := fun n ω => G n ω / (1 + Z1 n ω) with hQ
  have hQm : ∀ n, AEMeasurable (Q n) P := fun n => (hGm n).div (aemeasurable_const.add (hZm n))
  have hQ1 : TendstoInMeasure P (fun n ω => Q n ω * cutoff (r n ω)) atTop (fun _ => 0) :=
    tendstoInMeasure_mul_cutoff Q hr
  have hQ2 : TendstoInMeasure P (fun n ω => Q n ω * (1 - cutoff (r n ω))) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · exact ((hQm n).mul (aemeasurable_const.sub
        (continuous_cutoff.measurable.comp_aemeasurable (hrm n)))).aestronglyMeasurable
    filter_upwards [hpath'] with ω hω
    refine Metric.tendsto_nhds.2 fun e he => ?_
    filter_upwards [hω.2 (e / 2) (by positivity)] with n hn
    rw [Real.dist_eq, sub_zero]
    have hdenom : 0 < 1 + Z1 n ω := by linarith [hZ0 n ω]
    have hG0 : 0 ≤ G n ω := Finset.sum_nonneg fun _ _ => abs_nonneg _
    by_cases hcut : cutoff (r n ω) = 1
    · rw [hcut, sub_self, mul_zero, abs_zero]
      exact he
    · have hr' : r n ω < 1 / 2 := by
        by_contra h
        exact hcut (cutoff_of_ge (not_lt.1 h))
      have hle := hn hr'
      have hc0 := cutoff_nonneg (r n ω)
      have hc1 : cutoff (r n ω) ≤ 1 := min_le_left _ _
      have hQle : Q n ω ≤ e / 2 := by
        rw [div_le_iff₀ hdenom]
        exact hle
      have hQ0 : 0 ≤ Q n ω := div_nonneg hG0 hdenom.le
      rw [abs_mul, abs_of_nonneg hQ0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - cutoff (r n ω))]
      calc Q n ω * (1 - cutoff (r n ω)) ≤ e / 2 * 1 :=
            mul_le_mul hQle (by linarith) (by linarith) (by positivity)
        _ < e := by linarith
  have hQ0 : TendstoInMeasure P Q atTop (fun _ => 0) := by
    have := tendstoInMeasure_add_zero hQ1 hQ2
    refine this.congr_left fun n => ae_of_all _ fun ω => ?_
    ring
  have hQZ := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hZb hQ0
  have hfinal := tendstoInMeasure_add_zero hQ0 hQZ
  refine hfinal.congr_left fun n => ae_of_all _ fun ω => ?_
  have hdenom : 1 + Z1 n ω ≠ 0 := by linarith [hZ0 n ω]
  simp only [hQ]
  field_simp
  rfl

end Linearization

/-! ### Joint asymptotic normality -/

section Normality

variable {ξ₀ μ₀ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- **The asymptotic covariance of the GEV maximum likelihood estimator in the order `(ξ, μ, σ)`
of the parameters**: the inverse of `gevFisherInfo`, which is in the order `(μ, σ, ξ)`, with its
rows and columns permuted. -/
noncomputable def gevMLECov (ξ σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((gevFisherInfo ξ σ)⁻¹).submatrix ![2, 0, 1] ![2, 0, 1]

lemma posDef_inv_gevFisherInfo (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀) :
    ((gevFisherInfo ξ₀ σ₀)⁻¹).PosDef :=
  (posDef_gevFisherInfo hσ₀ hξ₀0 hξ₀).inv

lemma posSemidef_gevMLECov (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀) :
    (gevMLECov ξ₀ σ₀).PosSemidef :=
  (posDef_inv_gevFisherInfo hσ₀ hξ₀0 hξ₀).posSemidef.submatrix _

/-- The norm on `ℝ³` is at most the `ℓ¹` norm. -/
lemma norm_euclidean_three_le (w : EuclideanSpace ℝ (Fin 3)) : ‖w‖ ≤ |w 0| + |w 1| + |w 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.sqrt_le_left (by positivity)]
  simp only [Real.norm_eq_abs]
  nlinarith [abs_nonneg (w 0), abs_nonneg (w 1), abs_nonneg (w 2),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1)),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 2)),
    mul_nonneg (abs_nonneg (w 1)) (abs_nonneg (w 2))]

/-- The transpose of the inverse information is itself. -/
lemma transpose_inv_gevFisherInfo (ξ σ : ℝ) :
    ((gevFisherInfo ξ σ)⁻¹).transpose = (gevFisherInfo ξ σ)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, gevFisherInfo_isSymm.eq]

/-- Normality in the order given by a selection `sel` of the coordinates. -/
private theorem tendstoInDistribution_gevMLE_aux (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0)
    (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω))
    (sel : Fin 3 → Fin 3) {W : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hW : HasLaw W (multivariateGaussian 0
      (((gevFisherInfo ξ₀ σ₀)⁻¹).submatrix sel sel)) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
        (WithLp.toLp 2 fun j => gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) (sel j) :
          EuclideanSpace ℝ (Fin 3)))
      atTop W (fun _ => P) P' := by
  set I := gevFisherInfo ξ₀ σ₀ with hI
  set A := I⁻¹ with hA
  have hIA : I * A = 1 := mul_inv_gevFisherInfo hσ₀ hξ₀0 hξ₀
  have hAt : A.transpose = A := transpose_inv_gevFisherInfo ξ₀ σ₀
  set B : Matrix (Fin 3) (Fin 3) ℝ := A.transpose.submatrix sel id with hB
  have hBS : B * I * B.transpose = A.submatrix sel sel := by
    have h1 : A.transpose * I * A = A := by rw [Matrix.mul_assoc, hIA, Matrix.mul_one, hAt]
    ext a b
    have h2 := congrFun (congrFun h1 (sel a)) (sel b)
    rw [Matrix.submatrix_apply, ← h2]
    rfl
  have hS : (A.submatrix sel sel).PosSemidef :=
    (posDef_inv_gevFisherInfo hσ₀ hξ₀0 hξ₀).posSemidef.submatrix _
  have hV := tendstoInDistribution_gevScoreLin hξ₀ hξ₀0 hσ₀ hX hind hS hBS hW
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω => √(n : ℝ) •
    (WithLp.toLp 2 fun j => gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) (sel j) : EuclideanSpace ℝ (Fin 3))
    with hT
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω => (√(n : ℝ))⁻¹ •
    ∑ i ∈ Finset.range n, gevScoreLin B ξ₀ μ₀ σ₀ (X i ω) with hVdef
  have hTm : ∀ n, AEMeasurable (T n) P := fun n => by
    have hm : Measurable fun θ : ℝ × ℝ × ℝ => (WithLp.toLp 2 fun j =>
        gevThetaDiff ξ₀ μ₀ σ₀ θ (sel j) : EuclideanSpace ℝ (Fin 3)) := by
      refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun j => ?_)
      generalize sel j = k
      fin_cases k
      · exact measurable_snd.fst.sub_const _
      · exact measurable_snd.snd.sub_const _
      · exact measurable_fst.sub_const _
    exact (hm.comp_aemeasurable (hθm n)).const_smul (√(n : ℝ))
  have hVm : ∀ n, AEMeasurable (V n) P := hV.forall_aemeasurable
  have hlin := tendstoInMeasure_gevLinErr hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm
  -- the coordinates of `T - V`
  have hcoord : ∀ n ω (j : Fin 3), (T n ω - V n ω) j = √(n : ℝ) *
      gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) (sel j) -
      (fun k => A k (sel j)) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n := fun n ω j => by
    have h1 : V n ω j = (fun k => A k (sel j)) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n := by
      rw [dotProduct_gevPathZ]
      simp only [hVdef, gevScoreLin, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
        Finset.sum_apply]
      congr 1
    simp only [PiLp.sub_apply, hT, PiLp.smul_apply, smul_eq_mul, h1]
  have hle : ∀ n ω (j : Fin 3), |(T n ω - V n ω) j| ≤
      gevLinErr ξ₀ μ₀ σ₀ A (fun i => X i ω) (θh n ω) n := fun n ω j => by
    rw [hcoord]
    exact Finset.single_le_sum (f := fun j => |√(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j -
      (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (sel j))
  have hdiff : TendstoInMeasure P (T - V) atTop 0 := by
    have hg : TendstoInMeasure P (fun n ω => 3 * gevLinErr ξ₀ μ₀ σ₀ A (fun i => X i ω)
        (θh n ω) n) atTop (fun _ => 0) := by
      have := tendstoInMeasure_comp hlin (φ := fun z => 3 * z) (by fun_prop)
      simpa only [mul_zero] using this
    have hr : TendstoInMeasure P (fun n ω => ‖T n ω - V n ω‖) atTop (fun _ => 0) := by
      refine tendstoInMeasure_zero_of_abs_le (fun n ω => ?_) hg
      rw [abs_norm]
      refine (norm_euclidean_three_le _).trans ?_
      have h0 := hle n ω 0
      have h1 := hle n ω 1
      have h2 := hle n ω 2
      linarith
    rw [tendstoInMeasure_iff_norm] at hr ⊢
    intro e he
    simpa using hr e he
  exact tendstoInDistribution_of_tendstoInMeasure_sub T W hV hdiff hTm

/-- **Joint asymptotic normality of consistent local maximizers of the GEV likelihood**
([Smith 1985]; [Bücher–Segers 2017]), regular case `ξ₀ > -1/2`, `ξ₀ ≠ 0`. Let `X₀, X₁, …` be iid
with the location-scale GEV law of parameter `θ₀ = (ξ₀, μ₀, σ₀)`, and let `θ̂ₙ` be (almost
everywhere) measurable and strongly consistent, such that almost surely, for all large `n`, `θ̂ₙ` is
a local maximizer of the log-likelihood at which every observation is in the support. Then

  `√n (ξ̂ₙ - ξ₀, μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, V)`,

where `V = gevMLECov ξ₀ σ₀` is the inverse of the Fisher information `gevFisherInfo ξ₀ σ₀`,
permuted to the order `(ξ, μ, σ)`. -/
theorem tendstoInDistribution_gevLocalMLE (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 3)} (hW : HasLaw W (multivariateGaussian 0 (gevMLECov ξ₀ σ₀)) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
        !₂[(θh n ω).1 - ξ₀, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀])
      atTop W (fun _ => P) P' := by
  have h := tendstoInDistribution_gevMLE_aux hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm ![2, 0, 1] hW
  refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
  simp only
  congr 1
  ext j
  fin_cases j <;> simp [gevThetaDiff]

/-- **The GEV likelihood is finite at the truth, so a maximizer admits every observation.** If `θ`
maximizes the extended real log-likelihood over `K ∋ θ₀`, the observations being in the support of
`θ₀`, then every observation is in the support of `θ`. -/
lemma gevU_pos_of_isMaxOn {K : Set (ℝ × ℝ × ℝ)} (hθ₀ : (ξ₀, μ₀, σ₀) ∈ K) (hξ₀0 : ξ₀ ≠ 0)
    (hσ₀ : 0 < σ₀) {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (x i)) {θ : ℝ × ℝ × ℝ}
    (hξ : θ.1 ≠ 0) (hmax : IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) K θ)
    (i : Fin n) : 0 < gevU θ.1 θ.2.1 θ.2.2 (x i) := by
  have h0 : gevLogLikE ξ₀ μ₀ σ₀ x ≠ ⊥ := by
    rw [gevLogLikE_eq_coe fun i => gevLocScaleDensity_pos hσ₀ hξ₀0 (hx i)]
    exact EReal.coe_ne_bot _
  have hle := hmax hθ₀
  simp only [mem_ofPred_eq] at hle
  have h1 : gevLogLikE θ.1 θ.2.1 θ.2.2 x ≠ ⊥ := ne_bot_of_le_ne_bot h0 hle
  have h2 : gevLogDensityE θ.1 θ.2.1 θ.2.2 (x i) ≠ ⊥ := by
    intro hi
    apply h1
    rw [gevLogLikE, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi, EReal.bot_add]
  exact gevU_pos_of_gevLocScaleDensity_pos hξ (gevLogDensityE_ne_bot_iff.1 h2)

omit [IsProbabilityMeasure P] in
/-- Consistency and the local maximum property of maximizers over a compact parameter set. -/
private lemma gevMLE_consistent_localMax {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K) (hξ₀0 : ξ₀ ≠ 0)
    (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) K (θh n ω)) :
    (∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀))) ∧
    (∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) (θh n ω)) ∧
    (∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω)) := by
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)) := by
    filter_upwards [ae_tendsto_gevMLE (θ₀ := (ξ₀, μ₀, σ₀)) hK hKS (interior_subset hθ₀) hσ₀ hX
      hind] with ω hω
    refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have := hmax n ω (interior_subset hθ₀)
    simp only [mem_ofPred_eq] at this
    simpa using this
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (X i ω) := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gevU_pos hξ₀0 hσ₀)
  refine ⟨hcons, ?_, ?_⟩
  · filter_upwards [hcons] with ω hc
    filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀)] with n hn
    exact (hmax n ω).isLocalMax (mem_of_superset (isOpen_interior.mem_nhds hn) interior_subset)
  · filter_upwards [hcons, hsupp] with ω hc hx
    have hne : ∀ᶠ n in atTop, (θh n ω).1 ≠ 0 := by
      have : Tendsto (fun n => (θh n ω).1) atTop (𝓝 ξ₀) :=
        (continuous_fst.tendsto (ξ₀, μ₀, σ₀)).comp hc
      exact this.eventually (isOpen_ne.mem_nhds hξ₀0)
    filter_upwards [hne] with n hn i hi
    exact gevU_pos_of_isMaxOn (x := fun i : Fin n => X i ω) (interior_subset hθ₀) hξ₀0 hσ₀
      (fun i => hx i) hn (hmax n ω) ⟨i, hi⟩

/-- **Joint asymptotic normality of the three-parameter GEV maximum likelihood estimator**
([Smith 1985]; [Bücher–Segers 2017]; the regular case `ξ₀ > -1/2`, `ξ₀ ≠ 0`). Let
`K ⊂ {ξ > -1, σ > 0}` be compact with the true parameter `θ₀ = (ξ₀, μ₀, σ₀)` in its interior, let
`X₀, X₁, …` be iid with the location-scale GEV law of parameter `θ₀`, and let `θ̂ₙ` be
(almost everywhere) measurable maximizers over `K` of the log-likelihood of `X₀, …, X_{n-1}`. Then

  `√n (ξ̂ₙ - ξ₀, μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, V)`,

where `V = gevMLECov ξ₀ σ₀` is the inverse of the Fisher information `gevFisherInfo ξ₀ σ₀`,
permuted to the order `(ξ, μ, σ)`. The Gumbel case `ξ₀ = 0` is not covered. -/
theorem tendstoInDistribution_gevMLE {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) K (θh n ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 3)} (hW : HasLaw W (multivariateGaussian 0 (gevMLECov ξ₀ σ₀)) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
        !₂[(θh n ω).1 - ξ₀, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀])
      atTop W (fun _ => P) P' := by
  obtain ⟨hcons, hloc, hadm⟩ := gevMLE_consistent_localMax hK hKS hθ₀ hξ₀0 hσ₀ hX hind hθK hmax
  exact tendstoInDistribution_gevLocalMLE hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm hW

/-- `tendstoInDistribution_gevMLE` in the order `(μ, σ, ξ)` of the Fisher information
`gevFisherInfo` and of the score `gevScore`: `√n (μ̂ₙ - μ₀, σ̂ₙ - σ₀, ξ̂ₙ - ξ₀) ⇒ N(0, I(θ₀)⁻¹)`
([Prescott–Walden 1980]; [Smith 1985]). -/
theorem tendstoInDistribution_gevMLE_muSigmaXi {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) K (θh n ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hW : HasLaw W (multivariateGaussian 0 (gevFisherInfo ξ₀ σ₀)⁻¹) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
        !₂[(θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀, (θh n ω).1 - ξ₀])
      atTop W (fun _ => P) P' := by
  obtain ⟨hcons, hloc, hadm⟩ := gevMLE_consistent_localMax hK hKS hθ₀ hξ₀0 hσ₀ hX hind hθK hmax
  have hW' : HasLaw W (multivariateGaussian 0 (((gevFisherInfo ξ₀ σ₀)⁻¹).submatrix id id)) P' := by
    simpa using hW
  have h := tendstoInDistribution_gevMLE_aux hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm id hW'
  refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
  simp only
  congr 1

/-- **Measurable maximum likelihood estimators exist** on a compact nonempty parameter set
`K ⊂ {ξ > -1, σ > 0}`: for every sample size there is a measurable map from the data to a
maximizer of the extended-real GEV log-likelihood over `K`. -/
theorem exists_measurable_gevMLE {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hne : K.Nonempty) (n : ℕ) :
    ∃ g : (Fin n → ℝ) → ℝ × ℝ × ℝ, Measurable g ∧
      ∀ x, g x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) K (g x) := by
  refine exists_measurable_isMaxOn₃ hK (f := fun p x => gevLogLikE p.1 p.2.1 p.2.2 x)
    (fun x => ?_) (fun θ => ?_) hne
  · refine (continuousOn_finsetSum_ereal Finset.univ
      (fun i _ => (continuousOn_gevLogDensityE (x i)).mono fun p hp => hKS p hp)
      (fun i _ p hp => ?_)).1
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
      (gevLogDensityE_le (hKS p hp).1 (hKS p hp).2 (x i))
  · exact Finset.measurable_sum _ fun i _ =>
      (measurable_gevLogDensityE _ _ _).comp (measurable_pi_apply i)

/-- **Asymptotic normality of the GEV maximum likelihood estimator, unconditional form.** Let
`K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, μ₀, σ₀)`, `ξ₀ > -1/2`, `ξ₀ ≠ 0`, in its interior,
and let `X₀, X₁, …` be iid with the GEV law of parameter `θ₀`. Then there is a maximum likelihood
estimator, a measurable function of the sample which maximizes the log-likelihood over `K` for every
`n` and every sample, and it satisfies `√n (θ̂ₙ - θ₀) ⇒ N(0, gevMLECov ξ₀ σ₀)`. -/
theorem exists_gevMLE_tendstoInDistribution {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {W : Ω' → EuclideanSpace ℝ (Fin 3)} (hW : HasLaw W (multivariateGaussian 0 (gevMLECov ξ₀ σ₀)) P') :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) K (g n x)) ∧
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
          !₂[(g n (fun i : Fin n => X i ω)).1 - ξ₀, (g n (fun i : Fin n => X i ω)).2.1 - μ₀,
            (g n (fun i : Fin n => X i ω)).2.2 - σ₀])
        atTop W (fun _ => P) P' := by
  choose g hgm hg using exists_measurable_gevMLE hK hKS ⟨_, interior_subset hθ₀⟩
  refine ⟨g, hgm, hg, ?_⟩
  exact tendstoInDistribution_gevMLE hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind
    (θh := fun n ω => g n (fun i : Fin n => X i ω))
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2) hW

end Normality

end ExtremeValueTheory
