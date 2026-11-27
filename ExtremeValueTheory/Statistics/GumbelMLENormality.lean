/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVGumbelLimit
import ExtremeValueTheory.Statistics.GPDJointNormality
import ExtremeValueTheory.Statistics.ConfidenceIntervals
import ExtremeValueTheory.Statistics.MeasurableArgmax

/-!
# Maximum likelihood normality and return-level intervals for the Gumbel model (`ξ = 0`)

For the two-parameter Gumbel family `GEV(0, μ, σ)` (`μ ∈ ℝ`, `σ > 0`), the support is all of `ℝ`
(no moving endpoints) and the log-density is `ℓ(μ, σ; x) = -log σ - z - e^{-z}`, `z = (x - μ)/σ`.
We establish:

1. **Strong consistency and measurable existence of the Gumbel MLE** (`ae_tendsto_gumbelMLE`,
   `exists_measurable_gumbelMLE`) on any compact `K ⊂ ℝ × (0, ∞)`, from `ae_tendsto_gevMLE`.
2. **Exact Hessian, information identity, and Lipschitz control** on a neighbourhood of `(μ₀, σ₀)`:
   `E[∇²ℓ(μ₀, σ₀; X)] = -gumbelFisherInfo σ₀`, with inverse
   `gumbelFisherInfoInv σ = σ² [[1 + 6(1 - γ)²/π², 6(1 - γ)/π²], [6(1 - γ)/π², 6/π²]]`.
3. **Joint asymptotic normality of the two-parameter Gumbel MLE** (`tendstoInDistribution_gumbelMLE`,
   `exists_gumbelMLE_tendstoInDistribution`): `√n (μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, gumbelFisherInfoInv σ₀)`.
4. **Unconditional Gumbel return-level normality and computable plug-in confidence interval**
   (`tendstoInDistribution_gumbelMLEReturnLevel`,
   `tendsto_measure_mem_gumbelMLEReturnLevelPlugInInterval`), removing the assumed-normality and
   standard-error caveats for the Gumbel model ([Coles 2001, §3.3.3]).
5. **Full `3 × 3` GEV Fisher information and trivariate score CLT at `ξ = 0`**
   (`gevFisherInfoZero`, `posDef_gevFisherInfoZero`, `tendstoInDistribution_gumbelScoreVec3`):
   progress on the three-parameter `ξ₀ = 0` case without requiring closed-form `ζ(3)` evaluation.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §3.3.
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72 (1985).
* A. Bücher and J. Segers, *On the maximum likelihood estimator for the Generalized Extreme-Value
  distribution*, Extremes 20 (2017).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace ExtremeValueTheory

/-! ### The inverse Gumbel Fisher information and Gumbel Hessian -/

section GumbelHessian

/-- The inverse of the `2 × 2` Gumbel Fisher information `gumbelFisherInfo σ`:
`σ² [[1 + 6(1 - γ)²/π², 6(1 - γ)/π²], [6(1 - γ)/π², 6/π²]]`. -/
noncomputable def gumbelFisherInfoInv (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ ^ 2 * (1 + 6 * (1 - eulerMascheroniConstant) ^ 2 / π ^ 2),
      σ ^ 2 * (6 * (1 - eulerMascheroniConstant) / π ^ 2);
     σ ^ 2 * (6 * (1 - eulerMascheroniConstant) / π ^ 2),
      σ ^ 2 * (6 / π ^ 2)]

lemma gumbelFisherInfoInv_mul_gumbelFisherInfo {σ : ℝ} (hσ : 0 < σ) :
    gumbelFisherInfoInv σ * gumbelFisherInfo σ = 1 := by
  have hpi : π ≠ 0 := pi_ne_zero
  have hσne : σ ≠ 0 := hσ.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gumbelFisherInfoInv, gumbelFisherInfo, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

lemma gumbelFisherInfo_inv_eq {σ : ℝ} (hσ : 0 < σ) :
    (gumbelFisherInfo σ)⁻¹ = gumbelFisherInfoInv σ := by
  have hmul := gumbelFisherInfoInv_mul_gumbelFisherInfo hσ
  have hdet : IsUnit (gumbelFisherInfo σ).det :=
    isUnit_iff_ne_zero.2 (posDef_gumbelFisherInfo hσ).det_pos.ne'
  calc (gumbelFisherInfo σ)⁻¹
      = 1 * (gumbelFisherInfo σ)⁻¹ := (Matrix.one_mul _).symm
    _ = (gumbelFisherInfoInv σ * gumbelFisherInfo σ) * (gumbelFisherInfo σ)⁻¹ := by rw [hmul]
    _ = gumbelFisherInfoInv σ * (gumbelFisherInfo σ * (gumbelFisherInfo σ)⁻¹) := Matrix.mul_assoc _ _ _
    _ = gumbelFisherInfoInv σ * 1 := by rw [Matrix.mul_nonsing_inv _ hdet]
    _ = gumbelFisherInfoInv σ := Matrix.mul_one _

theorem posDef_gumbelFisherInfoInv {σ : ℝ} (hσ : 0 < σ) :
    (gumbelFisherInfoInv σ).PosDef := by
  rw [← gumbelFisherInfo_inv_eq hσ]
  exact (posDef_gumbelFisherInfo hσ).inv

/-- The `(μ, μ)` entry of the Gumbel log-density Hessian: `-e^{-z}/σ²`. -/
noncomputable def gumbelHessMuMu (μ σ x : ℝ) : ℝ :=
  -exp (-((x - μ) / σ)) / σ ^ 2

/-- The `(μ, σ)` entry of the Gumbel log-density Hessian: `-(1 - e^{-z} + z e^{-z})/σ²`. -/
noncomputable def gumbelHessMuSigma (μ σ x : ℝ) : ℝ :=
  -(1 - exp (-((x - μ) / σ)) + (x - μ) / σ * exp (-((x - μ) / σ))) / σ ^ 2

/-- The `(σ, σ)` entry of the Gumbel log-density Hessian: `(1 - 2z + (2z - z²) e^{-z})/σ²`. -/
noncomputable def gumbelHessSigmaSigma (μ σ x : ℝ) : ℝ :=
  (1 - 2 * ((x - μ) / σ) + (2 * ((x - μ) / σ) - ((x - μ) / σ) ^ 2) * exp (-((x - μ) / σ))) / σ ^ 2

lemma hasDerivAt_gumbelScoreMu_mu {μ σ x : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun m => gumbelScoreMu m σ x) (gumbelHessMuMu μ σ x) μ := by
  have hz : HasDerivAt (fun m => -((x - m) / σ)) (1 / σ) μ := by
    have h1 : HasDerivAt (fun m => (x - m) / σ) (-1 / σ) μ := by
      simpa using ((hasDerivAt_id μ).const_sub x).div_const σ
    exact h1.neg.congr_deriv (by ring)
  have hd := ((hasDerivAt_const μ (1 : ℝ)).sub hz.exp).div_const σ
  refine hd.congr_deriv ?_
  rw [gumbelHessMuMu]; field_simp; ring

lemma hasDerivAt_gumbelScoreMu_sigma {μ σ x : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s => gumbelScoreMu μ s x) (gumbelHessMuSigma μ σ x) σ := by
  have hz : HasDerivAt (fun s => (x - μ) / s) (-(x - μ) / σ ^ 2) σ :=
    ((hasDerivAt_const σ (x - μ)).div (hasDerivAt_id σ) hσ.ne').congr_deriv (by simp)
  have hexp : HasDerivAt (fun s => exp (-((x - μ) / s)))
      (exp (-((x - μ) / σ)) * ((x - μ) / σ ^ 2)) σ :=
    hz.neg.exp.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hd := ((hasDerivAt_const σ (1 : ℝ)).sub hexp).div (hasDerivAt_id σ) hσ.ne'
  refine hd.congr_deriv ?_
  rw [gumbelHessMuSigma]; dsimp only [Pi.sub_apply, id_eq]; field_simp; ring

lemma hasDerivAt_gumbelScoreSigma_mu {μ σ x : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun m => gumbelScoreSigma m σ x) (gumbelHessMuSigma μ σ x) μ := by
  have hz : HasDerivAt (fun m => (x - m) / σ) (-1 / σ) μ := by
    simpa using ((hasDerivAt_id μ).const_sub x).div_const σ
  have hexp : HasDerivAt (fun m => exp (-((x - m) / σ))) (exp (-((x - μ) / σ)) * (1 / σ)) μ :=
    hz.neg.exp.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hd := ((hasDerivAt_const μ (-1 : ℝ)).add (hz.mul ((hasDerivAt_const μ (1 : ℝ)).sub hexp))).div_const σ
  refine hd.congr_deriv ?_
  rw [gumbelHessMuSigma]; dsimp only [Pi.sub_apply]; field_simp; ring

lemma hasDerivAt_gumbelScoreSigma_sigma {μ σ x : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s => gumbelScoreSigma μ s x) (gumbelHessSigmaSigma μ σ x) σ := by
  have hz : HasDerivAt (fun s => (x - μ) / s) (-(x - μ) / σ ^ 2) σ :=
    ((hasDerivAt_const σ (x - μ)).div (hasDerivAt_id σ) hσ.ne').congr_deriv (by simp)
  have hexp : HasDerivAt (fun s => exp (-((x - μ) / s)))
      (exp (-((x - μ) / σ)) * ((x - μ) / σ ^ 2)) σ :=
    hz.neg.exp.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hd := ((hasDerivAt_const σ (-1 : ℝ)).add
    (hz.mul ((hasDerivAt_const σ (1 : ℝ)).sub hexp))).div (hasDerivAt_id σ) hσ.ne'
  refine hd.congr_deriv ?_
  rw [gumbelHessSigmaSigma]; dsimp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
  field_simp; ring

/-- Expected Gumbel Hessian entries equal minus the Gumbel Fisher information. -/
theorem integral_gumbelHessMuMu {μ σ : ℝ} (hσ : 0 < σ) :
    ∫ x, gumbelHessMuMu μ σ x ∂(gevLocScaleCDF 0 μ hσ).measure = -(1 / σ ^ 2) := by
  have hm : Measurable (gumbelHessMuMu μ σ) := by unfold gumbelHessMuMu; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm
    (a₀ := 0) (b₀ := -1 / σ ^ 2) (c₀ := 0) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := 0) (e₀ := 0) (f₀ := 0)
    (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 0) (h₀ := 0) (k₀ := 0)
    fun t ht => by
      have hz : (μ + σ * gevTransform 0 t - μ) / σ = -log t := by
        simp [gevTransform]; field_simp
      rw [gumbelHessMuMu, hz, neg_neg, exp_log ht, gevLogPoly, gevPoly]
      ring]
  ring

theorem integral_gumbelHessMuSigma {μ σ : ℝ} (hσ : 0 < σ) :
    ∫ x, gumbelHessMuSigma μ σ x ∂(gevLocScaleCDF 0 μ hσ).measure =
      (1 - eulerMascheroniConstant) / σ ^ 2 := by
  have hm : Measurable (gumbelHessMuSigma μ σ) := by unfold gumbelHessMuSigma; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm
    (a₀ := -1 / σ ^ 2) (b₀ := 1 / σ ^ 2) (c₀ := 0) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := 0) (e₀ := 1 / σ ^ 2) (f₀ := 0)
    (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 0) (h₀ := 0) (k₀ := 0)
    fun t ht => by
      have hz : (μ + σ * gevTransform 0 t - μ) / σ = -log t := by
        simp [gevTransform]; field_simp
      rw [gumbelHessMuSigma, hz, neg_neg, exp_log ht, gevLogPoly, gevPoly]
      ring]
  ring

theorem integral_gumbelHessSigmaSigma {μ σ : ℝ} (hσ : 0 < σ) :
    ∫ x, gumbelHessSigmaSigma μ σ x ∂(gevLocScaleCDF 0 μ hσ).measure =
      -((π ^ 2 / 6 + (1 - eulerMascheroniConstant) ^ 2) / σ ^ 2) := by
  have hm : Measurable (gumbelHessSigmaSigma μ σ) := by unfold gumbelHessSigmaSigma; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm
    (a₀ := 1 / σ ^ 2) (b₀ := 0) (c₀ := 0) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := 2 / σ ^ 2) (e₀ := -2 / σ ^ 2) (f₀ := 0)
    (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 0) (h₀ := -1 / σ ^ 2) (k₀ := 0)
    fun t ht => by
      have hz : (μ + σ * gevTransform 0 t - μ) / σ = -log t := by
        simp [gevTransform]; field_simp
      rw [gumbelHessSigmaSigma, hz, neg_neg, exp_log ht, gevLogPoly, gevPoly]
      ring]
  ring

lemma integrable_gumbelHessMuMu {μ σ : ℝ} (hσ : 0 < σ) :
    Integrable (gumbelHessMuMu μ σ) (gevLocScaleCDF 0 μ hσ).measure := by
  have hm : Measurable (gumbelHessMuMu μ σ) := by unfold gumbelHessMuMu; fun_prop
  exact integrable_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm
    (a₀ := 0) (b₀ := -1 / σ ^ 2) (c₀ := 0) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := 0) (e₀ := 0) (f₀ := 0)
    (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 0) (h₀ := 0) (k₀ := 0)
    fun t ht => by
      have hz : (μ + σ * gevTransform 0 t - μ) / σ = -log t := by
        simp [gevTransform]; field_simp
      rw [gumbelHessMuMu, hz, neg_neg, exp_log ht, gevLogPoly, gevPoly]
      ring

lemma integrable_gumbelHessMuSigma {μ σ : ℝ} (hσ : 0 < σ) :
    Integrable (gumbelHessMuSigma μ σ) (gevLocScaleCDF 0 μ hσ).measure := by
  have hm : Measurable (gumbelHessMuSigma μ σ) := by unfold gumbelHessMuSigma; fun_prop
  exact integrable_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm
    (a₀ := -1 / σ ^ 2) (b₀ := 1 / σ ^ 2) (c₀ := 0) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := 0) (e₀ := 1 / σ ^ 2) (f₀ := 0)
    (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 0) (h₀ := 0) (k₀ := 0)
    fun t ht => by
      have hz : (μ + σ * gevTransform 0 t - μ) / σ = -log t := by
        simp [gevTransform]; field_simp
      rw [gumbelHessMuSigma, hz, neg_neg, exp_log ht, gevLogPoly, gevPoly]
      ring

lemma integrable_gumbelHessSigmaSigma {μ σ : ℝ} (hσ : 0 < σ) :
    Integrable (gumbelHessSigmaSigma μ σ) (gevLocScaleCDF 0 μ hσ).measure := by
  have hm : Measurable (gumbelHessSigmaSigma μ σ) := by unfold gumbelHessSigmaSigma; fun_prop
  exact integrable_gevLocScaleCDF_of_logPoly (by norm_num) hσ hm
    (a₀ := 1 / σ ^ 2) (b₀ := 0) (c₀ := 0) (a₁ := 0) (b₁ := 0) (c₁ := 0)
    (a₂ := 0) (b₂ := 0) (c₂ := 0) (d₀ := 2 / σ ^ 2) (e₀ := -2 / σ ^ 2) (f₀ := 0)
    (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 0) (h₀ := -1 / σ ^ 2) (k₀ := 0)
    fun t ht => by
      have hz : (μ + σ * gevTransform 0 t - μ) / σ = -log t := by
        simp [gevTransform]; field_simp
      rw [gumbelHessSigmaSigma, hz, neg_neg, exp_log ht, gevLogPoly, gevPoly]
      ring

end GumbelHessian

/-! ### Neighbourhood bounds and Lipschitz control of the Gumbel Hessian -/

section GumbelLipschitz

variable {μ₀ σ₀ : ℝ}

/-- The closed neighbourhood `|μ - μ₀| ≤ σ₀/8`, `|σ - σ₀| ≤ σ₀/8` of `(μ₀, σ₀)`. -/
def gumbelNbhd (μ₀ σ₀ : ℝ) : Set (ℝ × ℝ) :=
  Icc (μ₀ - σ₀ / 8) (μ₀ + σ₀ / 8) ×ˢ Icc (σ₀ - σ₀ / 8) (σ₀ + σ₀ / 8)

lemma convex_gumbelNbhd : Convex ℝ (gumbelNbhd μ₀ σ₀) := (convex_Icc _ _).prod (convex_Icc _ _)

lemma gumbelNbhd_mem_nhds (hσ₀ : 0 < σ₀) : gumbelNbhd μ₀ σ₀ ∈ 𝓝 (μ₀, σ₀) :=
  prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    (Icc_mem_nhds (by linarith) (by linarith))

lemma mem_gumbelNbhd_bounds {θ : ℝ × ℝ} (hθ : θ ∈ gumbelNbhd μ₀ σ₀) :
    |θ.1 - μ₀| ≤ σ₀ / 8 ∧ |θ.2 - σ₀| ≤ σ₀ / 8 ∧ 7 * σ₀ / 8 ≤ θ.2 ∧ θ.2 ≤ 9 * σ₀ / 8 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  exact ⟨abs_sub_le_iff.2 ⟨by linarith, by linarith⟩,
    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- An integrable dominating envelope for the Gumbel Hessian increments on `gumbelNbhd μ₀ σ₀`:
`(1 + |z₀|)³ · (1 + exp(-(8/7) z₀))`, where `z₀ = (x - μ₀)/σ₀`. -/
noncomputable def gumbelEnv (μ₀ σ₀ x : ℝ) : ℝ :=
  (1 + |(x - μ₀) / σ₀|) ^ 3 * (1 + exp (-(8 / 7 : ℝ) * ((x - μ₀) / σ₀)))

lemma gumbelEnv_nonneg (μ₀ σ₀ x : ℝ) : 0 ≤ gumbelEnv μ₀ σ₀ x := by
  unfold gumbelEnv; positivity

lemma measurable_gumbelEnv (μ₀ σ₀ : ℝ) : Measurable (gumbelEnv μ₀ σ₀) := by
  unfold gumbelEnv; fun_prop

/-- `|log t|^k` is bounded by a sum of powers `(t^ε + t^{-ε})^k / ε^k`, so `e^{-t} t^a |log t|^k`
is integrable on `(0, ∞)` for every `a > -1` and `k : ℕ`. -/
lemma integrableOn_exp_neg_mul_rpow_mul_abs_log_pow {a : ℝ} (ha : -1 < a) (k : ℕ) :
    IntegrableOn (fun t => exp (-t) * (t ^ a * |log t| ^ k)) (Ioi 0) := by
  set ε := (a + 1) / (2 * (k + 1 : ℝ)) with hε_def
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  -- Bound `|log t|^k ≤ (2/ε)^k * (t^{k ε} + t^{-k ε})`
  have hbd : ∀ t : ℝ, 0 < t → |log t| ^ k ≤ (2 / ε) ^ k * (t ^ ((k : ℝ) * ε) + t ^ (-((k : ℝ) * ε))) := by
    intro t ht
    have hl := abs_log_le_rpow_add_rpow hε ht
    have hmax : (t ^ ε + t ^ (-ε)) / ε ≤ (2 / ε) * max (t ^ ε) (t ^ (-ε)) := by
      have : t ^ ε + t ^ (-ε) ≤ 2 * max (t ^ ε) (t ^ (-ε)) := by
        linarith [le_max_left (t ^ ε) (t ^ (-ε)), le_max_right (t ^ ε) (t ^ (-ε))]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      calc (t ^ ε + t ^ (-ε)) * ε⁻¹ ≤ (2 * max (t ^ ε) (t ^ (-ε))) * ε⁻¹ :=
            mul_le_mul_of_nonneg_right this (inv_nonneg.2 hε.le)
        _ = 2 * (ε⁻¹ * max (t ^ ε) (t ^ (-ε))) := by ring
    have hpow : |log t| ^ k ≤ (2 / ε) ^ k * (max (t ^ ε) (t ^ (-ε))) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hl.trans hmax) k
    have hmk : (max (t ^ ε) (t ^ (-ε))) ^ k ≤ t ^ ((k : ℝ) * ε) + t ^ (-((k : ℝ) * ε)) := by
      rcases le_total (t ^ ε) (t ^ (-ε)) with hle | hle
      · rw [max_eq_right hle, ← rpow_natCast, ← rpow_mul ht.le, show -ε * (k : ℝ) = -((k : ℝ) * ε) by ring]
        linarith [rpow_pos_of_pos ht ((k : ℝ) * ε)]
      · rw [max_eq_left hle, ← rpow_natCast, ← rpow_mul ht.le, mul_comm]
        linarith [rpow_pos_of_pos ht (-((k : ℝ) * ε))]
    exact hpow.trans (mul_le_mul_of_nonneg_left hmk (by positivity))
  have h1 : -1 < a + (k : ℝ) * ε := by
    have : 0 ≤ (k : ℝ) * ε := by positivity
    linarith
  have h2 : -1 < a - (k : ℝ) * ε := by
    have hklt : (k : ℝ) < 2 * (k + 1 : ℝ) := by linarith
    have hke : (k : ℝ) * ε < (a + 1) / 2 := by
      rw [hε_def, show (k : ℝ) * ((a + 1) / (2 * (k + 1 : ℝ))) =
        ((k : ℝ) / (2 * (k + 1 : ℝ))) * (a + 1) by ring]
      have hdiv : (k : ℝ) / (2 * (k + 1 : ℝ)) < 1 / 2 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        linarith
      nlinarith
    linarith
  have hint_top : IntegrableOn (fun t => (2 / ε) ^ k *
      (exp (-t) * t ^ (a + (k : ℝ) * ε) + exp (-t) * t ^ (a + -((k : ℝ) * ε)))) (Ioi 0) :=
    ((integrableOn_exp_neg_mul_rpow h1).add
      (integrableOn_exp_neg_mul_rpow (a := a + -((k : ℝ) * ε)) (by linarith))).const_mul _
  refine hint_top.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
  have ht : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e1 : t ^ (a + (k : ℝ) * ε) = t ^ a * t ^ ((k : ℝ) * ε) := rpow_add ht a _
  have e2 : t ^ (a + -((k : ℝ) * ε)) = t ^ a * t ^ (-((k : ℝ) * ε)) := rpow_add ht a _
  rw [e1, e2]
  have hle := hbd t ht
  calc exp (-t) * (t ^ a * |log t| ^ k)
      ≤ exp (-t) * (t ^ a * ((2 / ε) ^ k * (t ^ ((k : ℝ) * ε) + t ^ (-((k : ℝ) * ε))))) := by gcongr
    _ = _ := by ring

/-- The Gumbel envelope is integrable against `GEV(0, μ₀, σ₀)`. -/
theorem integrable_gumbelEnv (hσ₀ : 0 < σ₀) :
    Integrable (gumbelEnv μ₀ σ₀) (gevLocScaleCDF 0 μ₀ hσ₀).measure := by
  rw [integrable_gevLocScaleCDF_iff hσ₀ (measurable_gumbelEnv μ₀ σ₀)]
  have hterm : ∀ (a : ℝ) (ha : -1 < a),
      IntegrableOn (fun t => exp (-t) * (t ^ a * (1 + |log t|) ^ 3)) (Ioi 0) := fun a ha => by
    have h0 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 0
    have h1 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 1
    have h2 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 2
    have h3 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 3
    have hsum := ((h0.add (h1.const_mul 3)).add (h2.const_mul 3)).add h3
    refine hsum.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, pow_zero, pow_one, mul_one]
    ring
  have hcomb := (hterm 0 (by norm_num)).add (hterm (8 / 7) (by norm_num))
  refine hcomb.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht : 0 < t := ht
  have hz : (μ₀ + σ₀ * gevTransform 0 t - μ₀) / σ₀ = -log t := by
    simp [gevTransform]; field_simp
  have hexp : exp (-(8 / 7 : ℝ) * -log t) = t ^ (8 / 7 : ℝ) := by
    rw [rpow_def_of_pos ht]; congr 1; ring
  simp only [Pi.add_apply, gumbelEnv, hz, abs_neg, hexp, rpow_zero, one_mul]
  ring

/-- Mean-value inequality for `exp`: `|e^a - e^b| ≤ max(e^a, e^b) |a - b|`. -/
private lemma abs_exp_sub_exp_le (a b : ℝ) : |exp a - exp b| ≤ max (exp a) (exp b) * |a - b| := by
  rcases le_total a b with hab | hab
  · rw [abs_of_nonpos (sub_nonpos.2 (exp_le_exp.2 hab)), neg_sub,
      abs_of_nonpos (sub_nonpos.2 hab), neg_sub, max_eq_right (exp_le_exp.2 hab)]
    have h := add_one_le_exp (a - b)
    have h1 : exp a = exp b * exp (a - b) := by rw [← exp_add]; congr 1; ring
    have h2 : exp b * (a - b + 1) ≤ exp b * exp (a - b) :=
      mul_le_mul_of_nonneg_left h (exp_pos b).le
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.2 (exp_le_exp.2 hab)),
      abs_of_nonneg (sub_nonneg.2 hab), max_eq_left (exp_le_exp.2 hab)]
    have h := add_one_le_exp (b - a)
    have h1 : exp b = exp a * exp (b - a) := by rw [← exp_add]; congr 1; ring
    have h2 : exp a * (b - a + 1) ≤ exp a * exp (b - a) :=
      mul_le_mul_of_nonneg_left h (exp_pos a).le
    nlinarith

/-- On `gumbelNbhd μ₀ σ₀`, `exp(-z) ≤ exp(1/7) * (1 + exp(-(8/7) z₀))`. -/
private lemma exp_neg_z_le_of_mem_gumbelNbhd (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ}
    (hθ : θ ∈ gumbelNbhd μ₀ σ₀) (x : ℝ) :
    exp (-((x - θ.1) / θ.2)) ≤ exp (1 / 7) * (1 + exp (-(8 / 7 : ℝ) * ((x - μ₀) / σ₀))) := by
  obtain ⟨hμ, _, hσlo, hσhi⟩ := mem_gumbelNbhd_bounds hθ
  have hσpos : 0 < θ.2 := by linarith
  set z₀ := (x - μ₀) / σ₀
  have hz : -((x - θ.1) / θ.2) = -(σ₀ / θ.2) * z₀ + (θ.1 - μ₀) / θ.2 := by
    simp only [z₀]; field_simp; ring
  have hshift : (θ.1 - μ₀) / θ.2 ≤ 1 / 7 := by
    rw [div_le_iff₀ hσpos]
    linarith [le_abs_self (θ.1 - μ₀)]
  have hrat_lo : 8 / 9 ≤ σ₀ / θ.2 := by rw [div_le_div_iff₀ (by norm_num) hσpos]; linarith
  have hrat_hi : σ₀ / θ.2 ≤ 8 / 7 := by rw [div_le_div_iff₀ hσpos (by norm_num)]; linarith
  rw [hz, exp_add]
  have h1 : exp (-(σ₀ / θ.2) * z₀) ≤ 1 + exp (-(8 / 7 : ℝ) * z₀) := by
    rcases le_total 0 z₀ with hz0 | hz0
    · have : -(σ₀ / θ.2) * z₀ ≤ 0 := by nlinarith
      linarith [exp_le_one_iff.2 this, exp_pos (-(8 / 7 : ℝ) * z₀)]
    · have : -(σ₀ / θ.2) * z₀ ≤ -(8 / 7 : ℝ) * z₀ := by nlinarith
      linarith [exp_le_exp.2 this]
  calc exp (-(σ₀ / θ.2) * z₀) * exp ((θ.1 - μ₀) / θ.2)
      ≤ (1 + exp (-(8 / 7 : ℝ) * z₀)) * exp (1 / 7) :=
        mul_le_mul h1 (exp_le_exp.2 hshift) (exp_pos _).le (by positivity)
    _ = exp (1 / 7) * (1 + exp (-(8 / 7 : ℝ) * z₀)) := mul_comm _ _

/-- Helper bound for the `(σ, σ)` Gumbel Hessian increment on `gumbelNbhd μ₀ σ₀`. -/
private lemma abs_gumbelHessSigmaSigma_sub_le (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} {x c : ℝ}
    (hc1 : 1 ≤ c)
    (hquot : ∀ f f₀ : ℝ,
      |f / θ.2 ^ 2 - f₀ / σ₀ ^ 2| ≤
        |f - f₀| * (2 / σ₀ ^ 2) + |f₀| * (4 / σ₀ ^ 3 * (|θ.1 - μ₀| + |θ.2 - σ₀|)))
    (hz_diff : |(x - θ.1) / θ.2 - (x - μ₀) / σ₀| ≤
      2 / σ₀ * (|θ.1 - μ₀| + |θ.2 - σ₀|) * (1 + |(x - μ₀) / σ₀|))
    (hz_abs : |(x - θ.1) / θ.2| ≤ 2 * (1 + |(x - μ₀) / σ₀|))
    (hexp_le : exp (-((x - θ.1) / θ.2)) ≤ c * (1 + exp (-(8 / 7 : ℝ) * ((x - μ₀) / σ₀))))
    (hexp0_le : exp (-((x - μ₀) / σ₀)) ≤ c * (1 + exp (-(8 / 7 : ℝ) * ((x - μ₀) / σ₀))))
    (hexp_diff : |exp (-((x - θ.1) / θ.2)) - exp (-((x - μ₀) / σ₀))| ≤
      2 * c / σ₀ * (|θ.1 - μ₀| + |θ.2 - σ₀|) * (1 + |(x - μ₀) / σ₀|) *
        (1 + exp (-(8 / 7 : ℝ) * ((x - μ₀) / σ₀)))) :
    |gumbelHessSigmaSigma θ.1 θ.2 x - gumbelHessSigmaSigma μ₀ σ₀ x| ≤
      1000 * c / σ₀ ^ 3 * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x := by
  set z₀ := (x - μ₀) / σ₀
  set z := (x - θ.1) / θ.2
  set d := |θ.1 - μ₀| + |θ.2 - σ₀|
  set Z := 1 + |z₀|
  set E := 1 + exp (-(8 / 7 : ℝ) * z₀)
  have hd0 : 0 ≤ d := by positivity
  have hZ1 : 1 ≤ Z := by linarith [abs_nonneg z₀]
  have hE1 : 1 ≤ E := by linarith [exp_pos (-(8 / 7 : ℝ) * z₀)]
  have hE0 : 0 ≤ E := zero_le_one.trans hE1
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have h1_le_cE : 1 ≤ c * E := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ c * E := mul_le_mul hc1 hE1 zero_le_one hc0
  have hZ_le_Z2 : Z ≤ Z ^ 2 := by
    calc Z = 1 * Z := (one_mul Z).symm
      _ ≤ Z * Z := mul_le_mul_of_nonneg_right hZ1 (by linarith)
      _ = Z ^ 2 := (sq Z).symm
  have hZ2_le_Z3 : Z ^ 2 ≤ Z ^ 3 := by
    calc Z ^ 2 = 1 * Z ^ 2 := (one_mul _).symm
      _ ≤ Z * Z ^ 2 := mul_le_mul_of_nonneg_right hZ1 (sq_nonneg Z)
      _ = Z ^ 3 := by ring
  have hZ_le_Z3 : Z ≤ Z ^ 3 := hZ_le_Z2.trans hZ2_le_Z3
  set A : ℝ := c / σ₀ ^ 3 * d * (Z ^ 3 * E)
  have hA0 : 0 ≤ A := by positivity
  unfold gumbelHessSigmaSigma
  set f := 1 - 2 * z + (2 * z - z ^ 2) * exp (-z)
  set f₀ := 1 - 2 * z₀ + (2 * z₀ - z₀ ^ 2) * exp (-z₀)
  have hq := hquot f f₀
  have hz2_diff : |z ^ 2 - z₀ ^ 2| ≤ 6 / σ₀ * d * Z ^ 2 := by
    have e : z ^ 2 - z₀ ^ 2 = (z - z₀) * (z + z₀) := by ring
    rw [e, abs_mul]
    have hsum : |z + z₀| ≤ 3 * Z := by
      calc |z + z₀| ≤ |z| + |z₀| := abs_add_le _ _
        _ ≤ 2 * Z + Z := by linarith
        _ = 3 * Z := by ring
    calc |z - z₀| * |z + z₀| ≤ (2 / σ₀ * d * Z) * (3 * Z) :=
          mul_le_mul hz_diff hsum (abs_nonneg _) (by positivity)
      _ = 6 / σ₀ * d * Z ^ 2 := by ring
  have hz2_le : |2 * z₀ - z₀ ^ 2| ≤ 3 * Z ^ 2 := by
    have hz0_le : |z₀| ≤ Z := by linarith
    have hz0_sq : |z₀| ^ 2 ≤ Z ^ 2 := by
      calc |z₀| ^ 2 = |z₀| * |z₀| := sq _
        _ ≤ Z * Z := mul_le_mul hz0_le hz0_le (abs_nonneg _) (by linarith)
        _ = Z ^ 2 := (sq _).symm
    calc |2 * z₀ - z₀ ^ 2| ≤ |2 * z₀| + |z₀ ^ 2| := abs_sub _ _
      _ = 2 * |z₀| + |z₀| ^ 2 := by rw [abs_mul, abs_of_pos two_pos, abs_pow]
      _ ≤ 2 * Z ^ 2 + Z ^ 2 := by linarith [hz0_le.trans hZ_le_Z2, hz0_sq]
      _ = 3 * Z ^ 2 := by ring
  have hterm_diff : |(2 * z - z ^ 2) * exp (-z) - (2 * z₀ - z₀ ^ 2) * exp (-z₀)| ≤
      16 * c / σ₀ * d * Z ^ 3 * E := by
    have e : (2 * z - z ^ 2) * exp (-z) - (2 * z₀ - z₀ ^ 2) * exp (-z₀) =
        (2 * (z - z₀) - (z ^ 2 - z₀ ^ 2)) * exp (-z) +
        (2 * z₀ - z₀ ^ 2) * (exp (-z) - exp (-z₀)) := by ring
    rw [e]
    have h1 : |2 * (z - z₀) - (z ^ 2 - z₀ ^ 2)| ≤ 10 / σ₀ * d * Z ^ 2 := by
      calc |2 * (z - z₀) - (z ^ 2 - z₀ ^ 2)|
          ≤ |2 * (z - z₀)| + |z ^ 2 - z₀ ^ 2| := abs_sub _ _
        _ = 2 * |z - z₀| + |z ^ 2 - z₀ ^ 2| := by rw [abs_mul, abs_of_pos two_pos]
        _ ≤ 2 * (2 / σ₀ * d * Z) + 6 / σ₀ * d * Z ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hz_diff (by norm_num)) hz2_diff
        _ ≤ 4 / σ₀ * d * Z ^ 2 + 6 / σ₀ * d * Z ^ 2 := by
            have h4 : 0 ≤ 4 / σ₀ * d := by positivity
            have hle : 4 / σ₀ * d * Z ≤ 4 / σ₀ * d * Z ^ 2 := mul_le_mul_of_nonneg_left hZ_le_Z2 h4
            have h2 : 2 * (2 / σ₀ * d * Z) = 4 / σ₀ * d * Z := by ring
            linarith
        _ = 10 / σ₀ * d * Z ^ 2 := by ring
    calc |(2 * (z - z₀) - (z ^ 2 - z₀ ^ 2)) * exp (-z) +
            (2 * z₀ - z₀ ^ 2) * (exp (-z) - exp (-z₀))|
        ≤ |(2 * (z - z₀) - (z ^ 2 - z₀ ^ 2)) * exp (-z)| +
          |(2 * z₀ - z₀ ^ 2) * (exp (-z) - exp (-z₀))| := abs_add_le _ _
      _ = |2 * (z - z₀) - (z ^ 2 - z₀ ^ 2)| * exp (-z) +
          |2 * z₀ - z₀ ^ 2| * |exp (-z) - exp (-z₀)| := by
          rw [abs_mul, abs_mul, abs_of_pos (exp_pos _)]
      _ ≤ (10 / σ₀ * d * Z ^ 2) * (c * E) + (3 * Z ^ 2) * (2 * c / σ₀ * d * Z * E) :=
          add_le_add (mul_le_mul h1 hexp_le (exp_pos _).le (by positivity))
            (mul_le_mul hz2_le hexp_diff (abs_nonneg _) (by positivity))
      _ = 10 * (c / σ₀ * d * E * Z ^ 2) + 6 * (c / σ₀ * d * E * Z ^ 3) := by ring
      _ ≤ 10 * (c / σ₀ * d * E * Z ^ 3) + 6 * (c / σ₀ * d * E * Z ^ 3) := by
          have hle : c / σ₀ * d * E * Z ^ 2 ≤ c / σ₀ * d * E * Z ^ 3 :=
            mul_le_mul_of_nonneg_left hZ2_le_Z3 (by positivity)
          linarith
      _ = 16 * c / σ₀ * d * Z ^ 3 * E := by ring
  have hf : |f - f₀| ≤ 20 * c / σ₀ * d * Z ^ 3 * E := by
    have e : f - f₀ = -2 * (z - z₀) + ((2 * z - z ^ 2) * exp (-z) - (2 * z₀ - z₀ ^ 2) * exp (-z₀)) := by
      simp only [f, f₀]; ring
    rw [e]
    calc |-2 * (z - z₀) + ((2 * z - z ^ 2) * exp (-z) - (2 * z₀ - z₀ ^ 2) * exp (-z₀))|
        ≤ |-2 * (z - z₀)| + |(2 * z - z ^ 2) * exp (-z) - (2 * z₀ - z₀ ^ 2) * exp (-z₀)| :=
          abs_add_le _ _
      _ = 2 * |z - z₀| + |(2 * z - z ^ 2) * exp (-z) - (2 * z₀ - z₀ ^ 2) * exp (-z₀)| := by
          rw [abs_mul, abs_neg, abs_of_pos two_pos]
      _ ≤ 2 * (2 / σ₀ * d * Z) + 16 * c / σ₀ * d * Z ^ 3 * E :=
          add_le_add (mul_le_mul_of_nonneg_left hz_diff (by norm_num)) hterm_diff
      _ ≤ 4 * c / σ₀ * d * Z ^ 3 * E + 16 * c / σ₀ * d * Z ^ 3 * E := by
          have h1 : Z ≤ Z ^ 3 * (c * E) := hZ_le_Z3.trans (by
            simpa using mul_le_mul_of_nonneg_left h1_le_cE (by positivity : 0 ≤ Z ^ 3))
          have h2 : 4 / σ₀ * d * Z ≤ 4 / σ₀ * d * (Z ^ 3 * (c * E)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          have h3 : 2 * (2 / σ₀ * d * Z) = 4 / σ₀ * d * Z := by ring
          have h4 : 4 / σ₀ * d * (Z ^ 3 * (c * E)) = 4 * c / σ₀ * d * Z ^ 3 * E := by ring
          linarith
      _ = 20 * c / σ₀ * d * Z ^ 3 * E := by ring
  have hf0 : |f₀| ≤ 6 * c * Z ^ 2 * E := by
    have hz0_le : |z₀| ≤ Z := by linarith
    have h12 : 1 + 2 * |z₀| ≤ 3 * Z ^ 2 := by
      have h1Z2 : 1 ≤ Z ^ 2 := hZ1.trans hZ_le_Z2
      linarith [hz0_le.trans hZ_le_Z2]
    have h3Z2 : 3 * Z ^ 2 ≤ 3 * Z ^ 2 * (c * E) := by
      simpa using mul_le_mul_of_nonneg_left h1_le_cE (by positivity : 0 ≤ 3 * Z ^ 2)
    calc |1 - 2 * z₀ + (2 * z₀ - z₀ ^ 2) * exp (-z₀)|
        ≤ |1 - 2 * z₀| + |(2 * z₀ - z₀ ^ 2) * exp (-z₀)| := abs_add_le _ _
      _ ≤ (1 + 2 * |z₀|) + |2 * z₀ - z₀ ^ 2| * exp (-z₀) :=
          add_le_add (by
            calc |1 - 2 * z₀| ≤ |1| + |2 * z₀| := abs_sub _ _
              _ = 1 + 2 * |z₀| := by rw [abs_one, abs_mul, abs_of_pos two_pos])
            (le_of_eq (by rw [abs_mul, abs_of_pos (exp_pos _)]))
      _ ≤ 3 * Z ^ 2 + (3 * Z ^ 2) * (c * E) :=
          add_le_add h12 (mul_le_mul hz2_le hexp0_le (exp_pos _).le (by positivity))
      _ ≤ 3 * Z ^ 2 * (c * E) + 3 * Z ^ 2 * (c * E) := add_le_add h3Z2 le_rfl
      _ = 6 * c * Z ^ 2 * E := by ring
  have h2s2 : 0 ≤ 2 / σ₀ ^ 2 := div_nonneg zero_le_two (sq_nonneg σ₀)
  have h4s3d : 0 ≤ 4 / σ₀ ^ 3 * d := mul_nonneg (div_nonneg (by norm_num) (pow_nonneg hσ₀.le 3)) hd0
  have hcs3d : 0 ≤ c / σ₀ ^ 3 * d := mul_nonneg (div_nonneg hc0 (pow_nonneg hσ₀.le 3)) hd0
  show |f / θ.2 ^ 2 - f₀ / σ₀ ^ 2| ≤ 1000 * c / σ₀ ^ 3 * d * (Z ^ 3 * E)
  calc |f / θ.2 ^ 2 - f₀ / σ₀ ^ 2|
      ≤ |f - f₀| * (2 / σ₀ ^ 2) + |f₀| * (4 / σ₀ ^ 3 * d) := hq
    _ ≤ (20 * c / σ₀ * d * Z ^ 3 * E) * (2 / σ₀ ^ 2) + (6 * c * Z ^ 2 * E) * (4 / σ₀ ^ 3 * d) :=
        add_le_add (mul_le_mul_of_nonneg_right hf h2s2) (mul_le_mul_of_nonneg_right hf0 h4s3d)
    _ = 40 * A + 24 * (c / σ₀ ^ 3 * d * (Z ^ 2 * E)) := by simp only [A]; ring
    _ ≤ 40 * A + 24 * A :=
        add_le_add_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZ2_le_Z3 hE0) hcs3d) (by norm_num)) _
    _ ≤ 1000 * A := by linarith
    _ = 1000 * c / σ₀ ^ 3 * d * (Z ^ 3 * E) := by simp only [A]; ring

/-- **Uniform Lipschitz control of the Gumbel Hessian** on `gumbelNbhd μ₀ σ₀`: there is `K ≥ 0`
such that for every `θ ∈ gumbelNbhd μ₀ σ₀` and every `x ∈ ℝ`, each of the three Hessian entries
differs from its value at `θ₀` by at most `K (|μ - μ₀| + |σ - σ₀|) gumbelEnv μ₀ σ₀ x`. -/
theorem exists_gumbelHess_lipschitz (hσ₀ : 0 < σ₀) :
    ∃ K ≥ (0 : ℝ), ∀ θ ∈ gumbelNbhd μ₀ σ₀, ∀ x : ℝ,
      |gumbelHessMuMu θ.1 θ.2 x - gumbelHessMuMu μ₀ σ₀ x| ≤
          K * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x ∧
      |gumbelHessMuSigma θ.1 θ.2 x - gumbelHessMuSigma μ₀ σ₀ x| ≤
          K * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x ∧
      |gumbelHessSigmaSigma θ.1 θ.2 x - gumbelHessSigmaSigma μ₀ σ₀ x| ≤
          K * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x := by
  -- Use explicit elementary bounds in terms of `d = |μ - μ₀| + |σ - σ₀|`, `Z = 1 + |z₀|`, `E = 1 + exp(-(8/7) z₀)`
  set c := max (exp (1 / 7)) 1 with hc_def
  have hc1 : 1 ≤ c := le_max_right _ _
  have hce : exp (1 / 7) ≤ c := le_max_left _ _
  -- A generous constant `K` works cleanly for all three entries
  refine ⟨1000 * c / σ₀ ^ 3, by positivity, fun θ hθ x => ?_⟩
  obtain ⟨hμ, hσd, hσlo, hσhi⟩ := mem_gumbelNbhd_bounds hθ
  have hσpos : 0 < θ.2 := by linarith
  set z₀ := (x - μ₀) / σ₀
  set z := (x - θ.1) / θ.2
  set d := |θ.1 - μ₀| + |θ.2 - σ₀|
  set Z := 1 + |z₀|
  set E := 1 + exp (-(8 / 7 : ℝ) * z₀)
  have hd0 : 0 ≤ d := by positivity
  have hZ1 : 1 ≤ Z := by linarith [abs_nonneg z₀]
  have hE1 : 1 ≤ E := by linarith [exp_pos (-(8 / 7 : ℝ) * z₀)]
  have hEnv : gumbelEnv μ₀ σ₀ x = Z ^ 3 * E := rfl
  -- Basic inequalities for `1/σ²`, `z`, `exp(-z)`
  have hinv_le : 1 / θ.2 ≤ 8 / (7 * σ₀) := by rw [div_le_div_iff₀ hσpos (by positivity)]; linarith
  have hinv2_le : 1 / θ.2 ^ 2 ≤ 2 / σ₀ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hinv2_diff : |1 / θ.2 ^ 2 - 1 / σ₀ ^ 2| ≤ 4 / σ₀ ^ 3 * d := by
    have e : 1 / θ.2 ^ 2 - 1 / σ₀ ^ 2 = (σ₀ - θ.2) * (σ₀ + θ.2) / (θ.2 ^ 2 * σ₀ ^ 2) := by
      field_simp; ring
    rw [e, abs_div, abs_mul, abs_of_pos (by positivity : 0 < θ.2 ^ 2 * σ₀ ^ 2),
      abs_of_pos (by linarith : 0 < σ₀ + θ.2), abs_sub_comm]
    have hnum : |θ.2 - σ₀| * (σ₀ + θ.2) ≤ d * (3 * σ₀) :=
      mul_le_mul (by linarith [abs_nonneg (θ.1 - μ₀)]) (by linarith) (by linarith) hd0
    have hden : (3 / 4 : ℝ) * σ₀ ^ 4 ≤ θ.2 ^ 2 * σ₀ ^ 2 := by
      have hsq : (3 / 4 : ℝ) * σ₀ ^ 2 ≤ θ.2 ^ 2 := by nlinarith
      calc (3 / 4 : ℝ) * σ₀ ^ 4 = ((3 / 4 : ℝ) * σ₀ ^ 2) * σ₀ ^ 2 := by ring
        _ ≤ θ.2 ^ 2 * σ₀ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg σ₀)
    rw [div_le_iff₀ (by positivity)]
    calc |θ.2 - σ₀| * (σ₀ + θ.2) ≤ d * (3 * σ₀) := hnum
      _ = 4 / σ₀ ^ 3 * d * ((3 / 4 : ℝ) * σ₀ ^ 4) := by field_simp
      _ ≤ 4 / σ₀ ^ 3 * d * (θ.2 ^ 2 * σ₀ ^ 2) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  have hz_diff : |z - z₀| ≤ 2 / σ₀ * d * Z := by
    have e : z - z₀ = (-(θ.1 - μ₀) - (θ.2 - σ₀) * z₀) / θ.2 := by
      simp only [z, z₀]; field_simp; ring
    rw [e, abs_div, abs_of_pos hσpos]
    have htri : |-(θ.1 - μ₀) - (θ.2 - σ₀) * z₀| ≤ |θ.1 - μ₀| + |θ.2 - σ₀| * |z₀| := by
      calc |-(θ.1 - μ₀) - (θ.2 - σ₀) * z₀|
          = |-(θ.1 - μ₀) + -((θ.2 - σ₀) * z₀)| := by ring_nf
        _ ≤ |-(θ.1 - μ₀)| + |-((θ.2 - σ₀) * z₀)| := abs_add_le _ _
        _ = |θ.1 - μ₀| + |θ.2 - σ₀| * |z₀| := by rw [abs_neg, abs_neg, abs_mul]
    have hle1 : |θ.1 - μ₀| + |θ.2 - σ₀| * |z₀| ≤ d * Z := by
      simp only [d, Z]; nlinarith [abs_nonneg (θ.1 - μ₀), abs_nonneg (θ.2 - σ₀), abs_nonneg z₀]
    rw [div_le_iff₀ hσpos]
    calc |-(θ.1 - μ₀) - (θ.2 - σ₀) * z₀| ≤ d * Z := htri.trans hle1
      _ ≤ (2 / σ₀ * d * Z) * (7 * σ₀ / 8) := by
          have : 0 ≤ d * Z := by positivity
          have : (2 / σ₀ * d * Z) * (7 * σ₀ / 8) = (7 / 4) * (d * Z) := by field_simp; ring
          linarith
      _ ≤ (2 / σ₀ * d * Z) * θ.2 := mul_le_mul_of_nonneg_left hσlo (by positivity)
  have hz_abs : |z| ≤ 2 * Z := by
    have hsub : |z| ≤ |z₀| + |z - z₀| := by
      calc |z| = |z₀ + (z - z₀)| := by ring_nf
        _ ≤ |z₀| + |z - z₀| := abs_add_le _ _
    have hd_le : d ≤ σ₀ / 4 := by linarith
    have hz_d : 2 / σ₀ * d * Z ≤ Z := by
      have : 2 / σ₀ * d ≤ 1 / 2 := by rw [div_mul_eq_mul_div, div_le_iff₀ hσ₀]; linarith
      nlinarith
    linarith [show |z₀| ≤ Z by linarith]
  have hexp_le : exp (-z) ≤ c * E :=
    (exp_neg_z_le_of_mem_gumbelNbhd hσ₀ hθ x).trans
      (mul_le_mul_of_nonneg_right hce (by positivity))
  have hexp0_le : exp (-z₀) ≤ c * E := by
    have h0mem : (μ₀, σ₀) ∈ gumbelNbhd μ₀ σ₀ := by
      simp only [gumbelNbhd, mem_prod, mem_Icc]; constructor <;> constructor <;> linarith
    exact (exp_neg_z_le_of_mem_gumbelNbhd hσ₀ h0mem x).trans
      (mul_le_mul_of_nonneg_right hce (by positivity))
  have hexp_diff : |exp (-z) - exp (-z₀)| ≤ 2 * c / σ₀ * d * Z * E := by
    have h1 := abs_exp_sub_exp_le (-z) (-z₀)
    have h2 : max (exp (-z)) (exp (-z₀)) ≤ c * E := max_le hexp_le hexp0_le
    have h3 : |-z - -z₀| = |z - z₀| := by rw [show -z - -z₀ = -(z - z₀) by ring, abs_neg]
    rw [h3] at h1
    calc |exp (-z) - exp (-z₀)|
        ≤ max (exp (-z)) (exp (-z₀)) * |z - z₀| := h1
      _ ≤ (c * E) * (2 / σ₀ * d * Z) :=
          mul_le_mul h2 hz_diff (abs_nonneg _) (by positivity)
      _ = 2 * c / σ₀ * d * Z * E := by ring
  -- Helper: `|f/σ² - f₀/σ₀²| ≤ |f - f₀| * (2/σ₀²) + |f₀| * (4/σ₀³ * d)`
  have hquot : ∀ f f₀ : ℝ,
      |f / θ.2 ^ 2 - f₀ / σ₀ ^ 2| ≤ |f - f₀| * (2 / σ₀ ^ 2) + |f₀| * (4 / σ₀ ^ 3 * d) := by
    intro f f₀
    have e : f / θ.2 ^ 2 - f₀ / σ₀ ^ 2 = (f - f₀) * (1 / θ.2 ^ 2) + f₀ * (1 / θ.2 ^ 2 - 1 / σ₀ ^ 2) := by
      ring
    rw [e]
    calc |(f - f₀) * (1 / θ.2 ^ 2) + f₀ * (1 / θ.2 ^ 2 - 1 / σ₀ ^ 2)|
        ≤ |(f - f₀) * (1 / θ.2 ^ 2)| + |f₀ * (1 / θ.2 ^ 2 - 1 / σ₀ ^ 2)| := abs_add_le _ _
      _ = |f - f₀| * (1 / θ.2 ^ 2) + |f₀| * |1 / θ.2 ^ 2 - 1 / σ₀ ^ 2| := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / θ.2 ^ 2)]
      _ ≤ |f - f₀| * (2 / σ₀ ^ 2) + |f₀| * (4 / σ₀ ^ 3 * d) := by gcongr
  have hZ_le_Z2 : Z ≤ Z ^ 2 := by
    calc Z = 1 * Z := (one_mul Z).symm
      _ ≤ Z * Z := mul_le_mul_of_nonneg_right hZ1 (by linarith)
      _ = Z ^ 2 := (sq Z).symm
  have hZ2_le_Z3 : Z ^ 2 ≤ Z ^ 3 := by
    calc Z ^ 2 = 1 * Z ^ 2 := (one_mul _).symm
      _ ≤ Z * Z ^ 2 := mul_le_mul_of_nonneg_right hZ1 (sq_nonneg Z)
      _ = Z ^ 3 := by ring
  have hZ_le_Z3 : Z ≤ Z ^ 3 := hZ_le_Z2.trans hZ2_le_Z3
  have h1_le_Z3 : 1 ≤ Z ^ 3 := hZ1.trans hZ_le_Z3
  have h1_le_E : 1 ≤ E := hE1
  have h1_le_cE : 1 ≤ c * E := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ c * E := mul_le_mul hc1 hE1 zero_le_one (by linarith)
  set A : ℝ := c / σ₀ ^ 3 * d * (Z ^ 3 * E)
  have hA0 : 0 ≤ A := by positivity
  -- Now bound each of the three Hessian entries
  refine ⟨?_, ?_, ?_⟩
  · -- `(μ, μ)`
    unfold gumbelHessMuMu
    have hq := hquot (-exp (-z)) (-exp (-z₀))
    have hf : |-exp (-z) - -exp (-z₀)| ≤ 2 * c / σ₀ * d * Z * E := by
      rw [show -exp (-z) - -exp (-z₀) = -(exp (-z) - exp (-z₀)) by ring, abs_neg]; exact hexp_diff
    have hf0 : |-exp (-z₀)| ≤ c * E := by
      rw [abs_neg, abs_of_pos (exp_pos _)]; exact hexp0_le
    rw [hEnv]
    calc |-exp (-z) / θ.2 ^ 2 - -exp (-z₀) / σ₀ ^ 2|
        ≤ |-exp (-z) - -exp (-z₀)| * (2 / σ₀ ^ 2) + |-exp (-z₀)| * (4 / σ₀ ^ 3 * d) := hq
      _ ≤ (2 * c / σ₀ * d * Z * E) * (2 / σ₀ ^ 2) + (c * E) * (4 / σ₀ ^ 3 * d) := by gcongr
      _ = 4 * (c / σ₀ ^ 3 * d * (Z * E)) + 4 * (c / σ₀ ^ 3 * d * (1 * E)) := by ring
      _ ≤ 4 * A + 4 * A := by
          have h1 : Z * E ≤ Z ^ 3 * E := mul_le_mul_of_nonneg_right hZ_le_Z3 (by positivity)
          have h2 : 1 * E ≤ Z ^ 3 * E := mul_le_mul_of_nonneg_right h1_le_Z3 (by positivity)
          have h3 : 0 ≤ c / σ₀ ^ 3 * d := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) (by norm_num))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 h3) (by norm_num))
      _ ≤ 1000 * A := by linarith
      _ = 1000 * c / σ₀ ^ 3 * d * (Z ^ 3 * E) := by simp only [A]; ring
  · -- `(μ, σ)`
    unfold gumbelHessMuSigma
    set f := -(1 - exp (-z) + z * exp (-z))
    set f₀ := -(1 - exp (-z₀) + z₀ * exp (-z₀))
    have hq := hquot f f₀
    have hze : |z * exp (-z) - z₀ * exp (-z₀)| ≤ 6 * c / σ₀ * d * Z ^ 2 * E := by
      have e : z * exp (-z) - z₀ * exp (-z₀) = (z - z₀) * exp (-z) + z₀ * (exp (-z) - exp (-z₀)) := by
        ring
      rw [e]
      have hB0 : 0 ≤ c / σ₀ * d * Z ^ 2 * E := by positivity
      calc |(z - z₀) * exp (-z) + z₀ * (exp (-z) - exp (-z₀))|
          ≤ |(z - z₀) * exp (-z)| + |z₀ * (exp (-z) - exp (-z₀))| := abs_add_le _ _
        _ = |z - z₀| * exp (-z) + |z₀| * |exp (-z) - exp (-z₀)| := by
            rw [abs_mul, abs_mul, abs_of_pos (exp_pos _)]
        _ ≤ (2 / σ₀ * d * Z) * (c * E) + Z * (2 * c / σ₀ * d * Z * E) :=
            add_le_add (mul_le_mul hz_diff hexp_le (exp_pos _).le (by positivity))
              (mul_le_mul (by linarith) hexp_diff (abs_nonneg _) (by positivity))
        _ = 2 * (c / σ₀ * d * E * Z) + 2 * (c / σ₀ * d * E * Z ^ 2) := by ring
        _ ≤ 2 * (c / σ₀ * d * E * Z ^ 2) + 2 * (c / σ₀ * d * E * Z ^ 2) := by
            have h1 : c / σ₀ * d * E * Z ≤ c / σ₀ * d * E * Z ^ 2 :=
              mul_le_mul_of_nonneg_left hZ_le_Z2 (by positivity)
            linarith
        _ = 4 * (c / σ₀ * d * Z ^ 2 * E) := by ring
        _ ≤ 6 * (c / σ₀ * d * Z ^ 2 * E) := by linarith
        _ = 6 * c / σ₀ * d * Z ^ 2 * E := by ring
    have hf : |f - f₀| ≤ 8 * c / σ₀ * d * Z ^ 2 * E := by
      have e : f - f₀ = (exp (-z) - exp (-z₀)) - (z * exp (-z) - z₀ * exp (-z₀)) := by
        simp only [f, f₀]; ring
      rw [e]
      calc |(exp (-z) - exp (-z₀)) - (z * exp (-z) - z₀ * exp (-z₀))|
          ≤ |exp (-z) - exp (-z₀)| + |z * exp (-z) - z₀ * exp (-z₀)| := abs_sub _ _
        _ ≤ 2 * c / σ₀ * d * Z * E + 6 * c / σ₀ * d * Z ^ 2 * E := add_le_add hexp_diff hze
        _ = 2 * (c / σ₀ * d * E * Z) + 6 * (c / σ₀ * d * E * Z ^ 2) := by ring
        _ ≤ 2 * (c / σ₀ * d * E * Z ^ 2) + 6 * (c / σ₀ * d * E * Z ^ 2) := by
            have h1 : c / σ₀ * d * E * Z ≤ c / σ₀ * d * E * Z ^ 2 :=
              mul_le_mul_of_nonneg_left hZ_le_Z2 (by positivity)
            linarith
        _ = 8 * c / σ₀ * d * Z ^ 2 * E := by ring
    have hf0 : |f₀| ≤ 3 * c * Z * E := by
      have e : |f₀| = |1 - exp (-z₀) + z₀ * exp (-z₀)| := by simp only [f₀, abs_neg]
      rw [e]
      have hcEZ : c * E ≤ Z * (c * E) := by
        simpa using mul_le_mul_of_nonneg_right hZ1 (by positivity : 0 ≤ c * E)
      calc |1 - exp (-z₀) + z₀ * exp (-z₀)|
          ≤ |1 - exp (-z₀)| + |z₀ * exp (-z₀)| := abs_add_le _ _
        _ ≤ (|1| + |exp (-z₀)|) + |z₀| * |exp (-z₀)| :=
            add_le_add (abs_sub _ _) (le_of_eq (abs_mul _ _))
        _ = 1 + exp (-z₀) + |z₀| * exp (-z₀) := by
            rw [abs_one, abs_of_pos (exp_pos _)]
        _ ≤ c * E + c * E + Z * (c * E) :=
            add_le_add (add_le_add h1_le_cE hexp0_le)
              (mul_le_mul (by linarith) hexp0_le (exp_pos _).le (by positivity))
        _ ≤ Z * (c * E) + Z * (c * E) + Z * (c * E) :=
            add_le_add (add_le_add hcEZ hcEZ) le_rfl
        _ = 3 * c * Z * E := by ring
    rw [hEnv]
    calc |f / θ.2 ^ 2 - f₀ / σ₀ ^ 2|
        ≤ |f - f₀| * (2 / σ₀ ^ 2) + |f₀| * (4 / σ₀ ^ 3 * d) := hq
      _ ≤ (8 * c / σ₀ * d * Z ^ 2 * E) * (2 / σ₀ ^ 2) + (3 * c * Z * E) * (4 / σ₀ ^ 3 * d) :=
          add_le_add (mul_le_mul_of_nonneg_right hf (by positivity))
            (mul_le_mul_of_nonneg_right hf0 (by positivity))
      _ = 16 * (c / σ₀ ^ 3 * d * (Z ^ 2 * E)) + 12 * (c / σ₀ ^ 3 * d * (Z * E)) := by ring
      _ ≤ 16 * A + 12 * A := by
          have h1 : Z ^ 2 * E ≤ Z ^ 3 * E := mul_le_mul_of_nonneg_right hZ2_le_Z3 (by positivity)
          have h2 : Z * E ≤ Z ^ 3 * E := mul_le_mul_of_nonneg_right hZ_le_Z3 (by positivity)
          have h3 : 0 ≤ c / σ₀ ^ 3 * d := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) (by norm_num))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 h3) (by norm_num))
      _ ≤ 1000 * A := by linarith
      _ = 1000 * c / σ₀ ^ 3 * d * (Z ^ 3 * E) := by simp only [A]; ring
  · -- `(σ, σ)`
    exact abs_gumbelHessSigmaSigma_sub_le hσ₀ hc1 hquot hz_diff hz_abs hexp_le hexp0_le hexp_diff

end GumbelLipschitz

/-! ### Exact axis-by-axis expansion of the Gumbel score -/

section GumbelAxisHess

variable {μ₀ σ₀ : ℝ}

/-- Average of `H(·, σ, x)` along the horizontal segment from `μ₀` to `μ`. -/
noncomputable def gumbelHorizH (H : ℝ → ℝ → ℝ → ℝ) (μ₀ : ℝ) (θ : ℝ × ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, H (μ₀ + t * (θ.1 - μ₀)) θ.2 x

/-- Average of `H(μ₀, ·, x)` along the vertical segment from `σ₀` to `σ`. -/
noncomputable def gumbelVertH (H : ℝ → ℝ → ℝ → ℝ) (μ₀ σ₀ : ℝ) (θ : ℝ × ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, H μ₀ (σ₀ + t * (θ.2 - σ₀)) x

/-- 1D fundamental theorem of calculus on `[0, 1]` along an affine path `t ↦ a + t (b - a)`. -/
private lemma sub_eq_mul_integral_affine {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt f (f' (a + t * (b - a))) (a + t * (b - a)))
    (hc : ContinuousOn (fun t : ℝ => f' (a + t * (b - a))) (uIcc 0 1)) :
    f b - f a = (b - a) * ∫ t in (0 : ℝ)..1, f' (a + t * (b - a)) := by
  have hpath : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => f (a + u * (b - a)))
        ((b - a) * f' (a + t * (b - a))) t := by
    intro t ht
    have hl : HasDerivAt (fun u : ℝ => a + u * (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id t).mul_const (b - a)).const_add a
    simpa [Function.comp_def, mul_comm] using (hd t ht).comp t hl
  have hi : IntervalIntegrable (fun t : ℝ => (b - a) * f' (a + t * (b - a))) volume 0 1 :=
    (continuousOn_const.mul hc).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath hi
  rw [intervalIntegral.integral_const_mul] at hftc
  simpa using hftc.symm

/-- Exact axis-by-axis expansion of the Gumbel score difference on `gumbelNbhd μ₀ σ₀`. -/
theorem gumbelScore_sub_eq_axisH (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gumbelNbhd μ₀ σ₀) (x : ℝ) :
    gumbelScoreMu θ.1 θ.2 x - gumbelScoreMu μ₀ σ₀ x =
        (θ.1 - μ₀) * gumbelHorizH gumbelHessMuMu μ₀ θ x +
          (θ.2 - σ₀) * gumbelVertH gumbelHessMuSigma μ₀ σ₀ θ x ∧
      gumbelScoreSigma θ.1 θ.2 x - gumbelScoreSigma μ₀ σ₀ x =
        (θ.1 - μ₀) * gumbelHorizH gumbelHessMuSigma μ₀ θ x +
          (θ.2 - σ₀) * gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ θ x := by
  obtain ⟨_, _, hσlo, _⟩ := mem_gumbelNbhd_bounds hθ
  have hσpos : 0 < θ.2 := by linarith
  have hσt : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < σ₀ + t * (θ.2 - σ₀) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have : σ₀ + t * (θ.2 - σ₀) = (1 - t) * σ₀ + t * θ.2 := by ring
    rw [this]; nlinarith [ht.1, ht.2]
  constructor
  · have h1 := sub_eq_mul_integral_affine (f := fun m => gumbelScoreMu m θ.2 x)
      (f' := fun m => gumbelHessMuMu m θ.2 x) (a := μ₀) (b := θ.1)
      (fun t _ => hasDerivAt_gumbelScoreMu_mu hσpos)
      (by unfold gumbelHessMuMu; fun_prop)
    have h2 := sub_eq_mul_integral_affine (f := fun s => gumbelScoreMu μ₀ s x)
      (f' := fun s => gumbelHessMuSigma μ₀ s x) (a := σ₀) (b := θ.2)
      (fun t ht => hasDerivAt_gumbelScoreMu_sigma (hσt t ht))
      (by
        unfold gumbelHessMuSigma
        intro t ht
        have hsne : σ₀ + t * (θ.2 - σ₀) ≠ 0 := (hσt t ht).ne'
        have hc : ContinuousAt (fun u : ℝ => -(1 - exp (-((x - μ₀) / (σ₀ + u * (θ.2 - σ₀)))) +
            (x - μ₀) / (σ₀ + u * (θ.2 - σ₀)) * exp (-((x - μ₀) / (σ₀ + u * (θ.2 - σ₀))))) /
            (σ₀ + u * (θ.2 - σ₀)) ^ 2) t := by
          fun_prop (disch := first | exact hsne | exact pow_ne_zero 2 hsne)
        exact hc.continuousWithinAt)
    unfold gumbelHorizH gumbelVertH
    linarith
  · have h1 := sub_eq_mul_integral_affine (f := fun m => gumbelScoreSigma m θ.2 x)
      (f' := fun m => gumbelHessMuSigma m θ.2 x) (a := μ₀) (b := θ.1)
      (fun t _ => hasDerivAt_gumbelScoreSigma_mu hσpos)
      (by unfold gumbelHessMuSigma; fun_prop)
    have h2 := sub_eq_mul_integral_affine (f := fun s => gumbelScoreSigma μ₀ s x)
      (f' := fun s => gumbelHessSigmaSigma μ₀ s x) (a := σ₀) (b := θ.2)
      (fun t ht => hasDerivAt_gumbelScoreSigma_sigma (hσt t ht))
      (by
        unfold gumbelHessSigmaSigma
        intro t ht
        have hsne : σ₀ + t * (θ.2 - σ₀) ≠ 0 := (hσt t ht).ne'
        have hc : ContinuousAt (fun u : ℝ => (1 - 2 * ((x - μ₀) / (σ₀ + u * (θ.2 - σ₀))) +
            (2 * ((x - μ₀) / (σ₀ + u * (θ.2 - σ₀))) - ((x - μ₀) / (σ₀ + u * (θ.2 - σ₀))) ^ 2) *
              exp (-((x - μ₀) / (σ₀ + u * (θ.2 - σ₀))))) /
            (σ₀ + u * (θ.2 - σ₀)) ^ 2) t := by
          fun_prop (disch := first | exact hsne | exact pow_ne_zero 2 hsne)
        exact hc.continuousWithinAt)
    unfold gumbelHorizH gumbelVertH
    linarith

/-- Perturbation bound on the horizontal and vertical averaged Hessians from `exists_gumbelHess_lipschitz`. -/
private lemma abs_gumbelHorizH_sub_le {H : ℝ → ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    {θ : ℝ × ℝ} (hθ : θ ∈ gumbelNbhd μ₀ σ₀) (x : ℝ)
    (hH : ∀ p ∈ gumbelNbhd μ₀ σ₀, |H p.1 p.2 x - H μ₀ σ₀ x| ≤
      K * (|p.1 - μ₀| + |p.2 - σ₀|) * gumbelEnv μ₀ σ₀ x)
    (hcont : ContinuousOn (fun t : ℝ => H (μ₀ + t * (θ.1 - μ₀)) θ.2 x) (uIcc 0 1)) :
    |gumbelHorizH H μ₀ θ x - H μ₀ σ₀ x| ≤
      K * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x := by
  have h1 : gumbelHorizH H μ₀ θ x - H μ₀ σ₀ x =
      ∫ t in (0 : ℝ)..1, (H (μ₀ + t * (θ.1 - μ₀)) θ.2 x - H μ₀ σ₀ x) := by
    unfold gumbelHorizH
    rw [intervalIntegral.integral_sub hcont.intervalIntegrable intervalIntegrable_const]
    simp
  rw [h1]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t => H (μ₀ + t * (θ.1 - μ₀)) θ.2 x - H μ₀ σ₀ x)
    (C := K * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have hmem : (μ₀ + t * (θ.1 - μ₀), θ.2) ∈ gumbelNbhd μ₀ σ₀ := by
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
        refine ⟨⟨?_, ?_⟩, h3, h4⟩
        · nlinarith [ht.1, ht.2]
        · nlinarith [ht.1, ht.2]
      rw [Real.norm_eq_abs]
      refine (hH _ hmem).trans ?_
      have hdist : |μ₀ + t * (θ.1 - μ₀) - μ₀| ≤ |θ.1 - μ₀| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_pos ht.1]
        exact mul_le_of_le_one_left (abs_nonneg _) ht.2
      have hEnv0 : 0 ≤ gumbelEnv μ₀ σ₀ x := gumbelEnv_nonneg μ₀ σ₀ x
      gcongr
  simpa [Real.norm_eq_abs] using hbd

private lemma abs_gumbelVertH_sub_le {H : ℝ → ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    {θ : ℝ × ℝ} (hθ : θ ∈ gumbelNbhd μ₀ σ₀) (x : ℝ)
    (hH : ∀ p ∈ gumbelNbhd μ₀ σ₀, |H p.1 p.2 x - H μ₀ σ₀ x| ≤
      K * (|p.1 - μ₀| + |p.2 - σ₀|) * gumbelEnv μ₀ σ₀ x)
    (hcont : ContinuousOn (fun t : ℝ => H μ₀ (σ₀ + t * (θ.2 - σ₀)) x) (uIcc 0 1)) :
    |gumbelVertH H μ₀ σ₀ θ x - H μ₀ σ₀ x| ≤
      K * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x := by
  have h1 : gumbelVertH H μ₀ σ₀ θ x - H μ₀ σ₀ x =
      ∫ t in (0 : ℝ)..1, (H μ₀ (σ₀ + t * (θ.2 - σ₀)) x - H μ₀ σ₀ x) := by
    unfold gumbelVertH
    rw [intervalIntegral.integral_sub hcont.intervalIntegrable intervalIntegrable_const]
    simp
  rw [h1]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t => H μ₀ (σ₀ + t * (θ.2 - σ₀)) x - H μ₀ σ₀ x)
    (C := K * (|θ.1 - μ₀| + |θ.2 - σ₀|) * gumbelEnv μ₀ σ₀ x) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have hmem : (μ₀, σ₀ + t * (θ.2 - σ₀)) ∈ gumbelNbhd μ₀ σ₀ := by
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
        refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
        · nlinarith [ht.1, ht.2]
        · nlinarith [ht.1, ht.2]
      rw [Real.norm_eq_abs]
      refine (hH _ hmem).trans ?_
      have hdist : |σ₀ + t * (θ.2 - σ₀) - σ₀| ≤ |θ.2 - σ₀| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_pos ht.1]
        exact mul_le_of_le_one_left (abs_nonneg _) ht.2
      have hEnv0 : 0 ≤ gumbelEnv μ₀ σ₀ x := gumbelEnv_nonneg μ₀ σ₀ x
      simp only [sub_self, abs_zero, zero_add]
      have : |θ.2 - σ₀| ≤ |θ.1 - μ₀| + |θ.2 - σ₀| := le_add_of_nonneg_left (abs_nonneg _)
      gcongr
      exact hdist.trans this
  simpa [Real.norm_eq_abs] using hbd

/-- Solving a general (not necessarily symmetric) `2 × 2` linear system `S = -B T`. -/
private lemma solve_two_by_two_gen {B₁₁ B₁₂ B₂₁ B₂₂ S₁ S₂ T₁ T₂ j₁₁ j₁₂ j₂₂ : ℝ}
    (hS₁ : S₁ = -(B₁₁ * T₁ + B₁₂ * T₂)) (hS₂ : S₂ = -(B₂₁ * T₁ + B₂₂ * T₂))
    (hD : B₁₁ * B₂₂ - B₁₂ * B₂₁ ≠ 0) :
    T₁ - (j₁₁ * S₁ + j₁₂ * S₂) = (-B₂₂ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₁₁) * S₁ +
        (B₁₂ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₁₂) * S₂ ∧
      T₂ - (j₁₂ * S₁ + j₂₂ * S₂) = (B₂₁ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₁₂) * S₁ +
        (-B₁₁ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₂₂) * S₂ := by
  have e₁ : -B₂₂ * S₁ + B₁₂ * S₂ = (B₁₁ * B₂₂ - B₁₂ * B₂₁) * T₁ := by rw [hS₁, hS₂]; ring
  have e₂ : B₂₁ * S₁ + -B₁₁ * S₂ = (B₁₁ * B₂₂ - B₁₂ * B₂₁) * T₂ := by rw [hS₁, hS₂]; ring
  constructor
  · rw [show (-B₂₂ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₁₁) * S₁ +
        (B₁₂ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₁₂) * S₂ =
        (-B₂₂ * S₁ + B₁₂ * S₂) / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - (j₁₁ * S₁ + j₁₂ * S₂) by ring,
      e₁, mul_div_cancel_left₀ _ hD]
  · rw [show (B₂₁ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₁₂) * S₁ +
        (-B₁₁ / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - j₂₂) * S₂ =
        (B₂₁ * S₁ + -B₁₁ * S₂) / (B₁₁ * B₂₂ - B₁₂ * B₂₁) - (j₁₂ * S₁ + j₂₂ * S₂) by ring,
      e₂, mul_div_cancel_left₀ _ hD]

/-- Algebraic perturbation bound for solving a `2 × 2` system `S = -B T` when `B` is close to
`-I` (symmetric) and `det B > det I / 2`. -/
private lemma two_by_two_perturbation_bound
    {B₁₁ B₁₂ B₂₁ B₂₂ i₁₁ i₁₂ i₂₂ j₁₁ j₁₂ j₂₂ S₁ S₂ T₁ T₂ δ : ℝ}
    (hS₁ : S₁ = -(B₁₁ * T₁ + B₁₂ * T₂)) (hS₂ : S₂ = -(B₂₁ * T₁ + B₂₂ * T₂))
    (hdet₀ : 0 < i₁₁ * i₂₂ - i₁₂ ^ 2)
    (hj₁₁ : j₁₁ = i₂₂ / (i₁₁ * i₂₂ - i₁₂ ^ 2))
    (hj₁₂ : j₁₂ = -i₁₂ / (i₁₁ * i₂₂ - i₁₂ ^ 2))
    (hj₂₂ : j₂₂ = i₁₁ / (i₁₁ * i₂₂ - i₁₂ ^ 2))
    (hB11 : |B₁₁ - (-i₁₁)| ≤ δ) (hB12 : |B₁₂ - (-i₁₂)| ≤ δ)
    (hB21 : |B₂₁ - (-i₁₂)| ≤ δ) (hB22 : |B₂₂ - (-i₂₂)| ≤ δ)
    (hδ1 : δ < 1) (hDn : (i₁₁ * i₂₂ - i₁₂ ^ 2) / 2 < B₁₁ * B₂₂ - B₁₂ * B₂₁) :
    |T₁ - (j₁₁ * S₁ + j₁₂ * S₂)| + |T₂ - (j₁₂ * S₁ + j₂₂ * S₂)| ≤
      (24 * (1 + |i₁₁| + |i₁₂| + |i₂₂| + |j₁₁| + |j₁₂| + |j₂₂|) ^ 2 / (i₁₁ * i₂₂ - i₁₂ ^ 2)) *
        δ * (|S₁| + |S₂|) := by
  set det₀ := i₁₁ * i₂₂ - i₁₂ ^ 2
  set Dn := B₁₁ * B₂₂ - B₁₂ * B₂₁
  set R := 1 + |i₁₁| + |i₁₂| + |i₂₂| + |j₁₁| + |j₁₂| + |j₂₂|
  set C_mat := 24 * R ^ 2 / det₀
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hB11
  have hR1 : 1 ≤ R := by
    linarith [abs_nonneg i₁₁, abs_nonneg i₁₂, abs_nonneg i₂₂, abs_nonneg j₁₁, abs_nonneg j₁₂, abs_nonneg j₂₂]
  have hi11_R : |i₁₁| + 1 ≤ R := by
    linarith [abs_nonneg i₁₂, abs_nonneg i₂₂, abs_nonneg j₁₁, abs_nonneg j₁₂, abs_nonneg j₂₂]
  have hi12_R : |i₁₂| + 1 ≤ R := by
    linarith [abs_nonneg i₁₁, abs_nonneg i₂₂, abs_nonneg j₁₁, abs_nonneg j₁₂, abs_nonneg j₂₂]
  have hi22_R : |i₂₂| + 1 ≤ R := by
    linarith [abs_nonneg i₁₁, abs_nonneg i₁₂, abs_nonneg j₁₁, abs_nonneg j₁₂, abs_nonneg j₂₂]
  have hj11_R : |j₁₁| ≤ R := by
    linarith [abs_nonneg i₁₁, abs_nonneg i₁₂, abs_nonneg i₂₂, abs_nonneg j₁₂, abs_nonneg j₂₂]
  have hj12_R : |j₁₂| ≤ R := by
    linarith [abs_nonneg i₁₁, abs_nonneg i₁₂, abs_nonneg i₂₂, abs_nonneg j₁₁, abs_nonneg j₂₂]
  have hj22_R : |j₂₂| ≤ R := by
    linarith [abs_nonneg i₁₁, abs_nonneg i₁₂, abs_nonneg i₂₂, abs_nonneg j₁₁, abs_nonneg j₁₂]
  have hB22_abs : |B₂₂| ≤ R := by
    have := abs_sub_abs_le_abs_sub B₂₂ (-i₂₂); rw [abs_neg] at this; linarith
  have hB21_abs : |B₂₁| ≤ R := by
    have := abs_sub_abs_le_abs_sub B₂₁ (-i₁₂); rw [abs_neg] at this; linarith
  have hdet_diff : |Dn - det₀| ≤ 4 * R * δ := by
    have e : Dn - det₀ = (B₁₁ - (-i₁₁)) * B₂₂ + (-i₁₁) * (B₂₂ - (-i₂₂)) -
        ((B₁₂ - (-i₁₂)) * B₂₁ + (-i₁₂) * (B₂₁ - (-i₁₂))) := by simp only [Dn, det₀]; ring
    rw [e]
    calc |(B₁₁ - -i₁₁) * B₂₂ + -i₁₁ * (B₂₂ - -i₂₂) - ((B₁₂ - -i₁₂) * B₂₁ + -i₁₂ * (B₂₁ - -i₁₂))|
        ≤ |(B₁₁ - -i₁₁) * B₂₂ + -i₁₁ * (B₂₂ - -i₂₂)| +
            |(B₁₂ - -i₁₂) * B₂₁ + -i₁₂ * (B₂₁ - -i₁₂)| := abs_sub _ _
      _ ≤ (|B₁₁ - -i₁₁| * |B₂₂| + |i₁₁| * |B₂₂ - -i₂₂|) +
            (|B₁₂ - -i₁₂| * |B₂₁| + |i₁₂| * |B₂₁ - -i₁₂|) := by
          gcongr
          · calc _ ≤ |(B₁₁ - -i₁₁) * B₂₂| + |-i₁₁ * (B₂₂ - -i₂₂)| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul, abs_neg]
          · calc _ ≤ |(B₁₂ - -i₁₂) * B₂₁| + |-i₁₂ * (B₂₁ - -i₁₂)| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul, abs_neg]
      _ ≤ (δ * R + R * δ) + (δ * R + R * δ) := by
          have hi1 : |i₁₁| ≤ R := by linarith
          have hi2 : |i₁₂| ≤ R := by linarith
          gcongr
      _ = 4 * R * δ := by ring
  have hcoeff : ∀ (x y z : ℝ), |x - y| ≤ δ → z = y / det₀ → |z| ≤ R →
      |x / Dn - z| ≤ (C_mat / 2) * δ := by
    intro x y z hxy hzy hzR
    have hDn0 : 0 < Dn := by linarith
    have e : x / Dn - z = ((x - y) - z * (Dn - det₀)) / Dn := by
      rw [hzy]; field_simp [hdet₀.ne', hDn0.ne']; ring
    rw [e, abs_div, abs_of_pos hDn0, div_le_iff₀ hDn0]
    have hnum : |(x - y) - z * (Dn - det₀)| ≤ (1 + 4 * R ^ 2) * δ := by
      calc |(x - y) - z * (Dn - det₀)| ≤ |x - y| + |z * (Dn - det₀)| := abs_sub _ _
        _ = |x - y| + |z| * |Dn - det₀| := by rw [abs_mul]
        _ ≤ δ + R * (4 * R * δ) :=
            add_le_add hxy (mul_le_mul hzR hdet_diff (abs_nonneg _) (by positivity))
        _ = (1 + 4 * R ^ 2) * δ := by ring
    have hC_eq : C_mat / 2 * (det₀ / 2) = 6 * R ^ 2 := by
      simp only [C_mat]; field_simp [hdet₀.ne']; ring
    have hR2 : 1 + 4 * R ^ 2 ≤ 6 * R ^ 2 := by
      have : 1 ≤ R ^ 2 := by nlinarith
      linarith
    have hC_ge : (1 + 4 * R ^ 2) * δ ≤ (C_mat / 2) * δ * (det₀ / 2) := by
      have : (C_mat / 2) * δ * (det₀ / 2) = (6 * R ^ 2) * δ := by
        calc (C_mat / 2) * δ * (det₀ / 2) = (C_mat / 2 * (det₀ / 2)) * δ := by ring
          _ = 6 * R ^ 2 * δ := by rw [hC_eq]
      rw [this]
      exact mul_le_mul_of_nonneg_right hR2 hδ0
    exact hnum.trans (hC_ge.trans (mul_le_mul_of_nonneg_left hDn.le (by positivity)))
  have hc11 : |-B₂₂ / Dn - j₁₁| ≤ (C_mat / 2) * δ :=
    hcoeff (-B₂₂) i₂₂ j₁₁ (by rw [show -B₂₂ - i₂₂ = -(B₂₂ - (-i₂₂)) by ring, abs_neg]; exact hB22)
      hj₁₁ hj11_R
  have hc12 : |B₁₂ / Dn - j₁₂| ≤ (C_mat / 2) * δ := hcoeff B₁₂ (-i₁₂) j₁₂ hB12 hj₁₂ hj12_R
  have hc21 : |B₂₁ / Dn - j₁₂| ≤ (C_mat / 2) * δ := hcoeff B₂₁ (-i₁₂) j₁₂ hB21 hj₁₂ hj12_R
  have hc22 : |-B₁₁ / Dn - j₂₂| ≤ (C_mat / 2) * δ :=
    hcoeff (-B₁₁) i₁₁ j₂₂ (by rw [show -B₁₁ - i₁₁ = -(B₁₁ - (-i₁₁)) by ring, abs_neg]; exact hB11)
      hj₂₂ hj22_R
  obtain ⟨h1, h2⟩ := solve_two_by_two_gen (j₁₁ := j₁₁) (j₁₂ := j₁₂) (j₂₂ := j₂₂) hS₁ hS₂
    (by linarith : Dn ≠ 0)
  rw [h1, h2]
  have ha1 : |(-B₂₂ / Dn - j₁₁) * S₁ + (B₁₂ / Dn - j₁₂) * S₂| ≤ (C_mat / 2) * δ * (|S₁| + |S₂|) := by
    calc _ ≤ |(-B₂₂ / Dn - j₁₁) * S₁| + |(B₁₂ / Dn - j₁₂) * S₂| := abs_add_le _ _
      _ = |-B₂₂ / Dn - j₁₁| * |S₁| + |B₁₂ / Dn - j₁₂| * |S₂| := by rw [abs_mul, abs_mul]
      _ ≤ (C_mat / 2) * δ * |S₁| + (C_mat / 2) * δ * |S₂| :=
          add_le_add (mul_le_mul_of_nonneg_right hc11 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hc12 (abs_nonneg _))
      _ = _ := by ring
  have ha2 : |(B₂₁ / Dn - j₁₂) * S₁ + (-B₁₁ / Dn - j₂₂) * S₂| ≤ (C_mat / 2) * δ * (|S₁| + |S₂|) := by
    calc _ ≤ |(B₂₁ / Dn - j₁₂) * S₁| + |(-B₁₁ / Dn - j₂₂) * S₂| := abs_add_le _ _
      _ = |B₂₁ / Dn - j₁₂| * |S₁| + |-B₁₁ / Dn - j₂₂| * |S₂| := by rw [abs_mul, abs_mul]
      _ ≤ (C_mat / 2) * δ * |S₁| + (C_mat / 2) * δ * |S₂| :=
          add_le_add (mul_le_mul_of_nonneg_right hc21 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hc22 (abs_nonneg _))
      _ = _ := by ring
  calc _ ≤ (C_mat / 2) * δ * (|S₁| + |S₂|) + (C_mat / 2) * δ * (|S₁| + |S₂|) := add_le_add ha1 ha2
    _ = C_mat * δ * (|S₁| + |S₂|) := by ring

end GumbelAxisHess

/-! ### Joint asymptotic normality of the two-parameter Gumbel MLE and return-level intervals -/

section GumbelMLENormality

variable {μ₀ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- The Gumbel log-density for `σ > 0` is finite at every real observation. -/
lemma gevLogLikE_zero_eq_coe {μ σ : ℝ} (hσ : 0 < σ) {n : ℕ} (x : Fin n → ℝ) :
    gevLogLikE 0 μ σ x = ((∑ i, log (gevLocScaleDensity 0 μ σ (x i)) : ℝ) : EReal) := by
  rw [gevLogLikE, ereal_coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : 0 < gevLocScaleDensity 0 μ σ (x i) := by
    unfold gevLocScaleDensity gevDensity
    simp only [↓reduceIte]
    positivity
  unfold gevLogDensityE
  rw [ENNReal.log_ofReal_of_pos hd]

omit [IsProbabilityMeasure P] in
/-- **Strong consistency of the two-parameter Gumbel MLE** on a compact parameter set
`K ⊂ ℝ × (0, ∞)` (direct corollary of `ae_tendsto_gevMLE` on `{0} ×ˢ K`). -/
theorem ae_tendsto_gumbelMLE {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ K) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, ∀ (θhat : ℕ → ℝ × ℝ) (ε : ℕ → ℝ), (∀ n, θhat n ∈ K) →
      Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, gevLogLikE 0 μ₀ σ₀ (fun i : Fin n => X i ω) ≤
        gevLogLikE 0 (θhat n).1 (θhat n).2 (fun i : Fin n => X i ω) + ((n * ε n : ℝ) : EReal)) →
      Tendsto θhat atTop (𝓝 (μ₀, σ₀)) := by
  set K₃ : Set (ℝ × ℝ × ℝ) := ({(0 : ℝ)} : Set ℝ) ×ˢ K
  have hK₃ : IsCompact K₃ := isCompact_singleton.prod hK
  have hKS₃ : ∀ p ∈ K₃, -1 < p.1 ∧ 0 < p.2.2 := by
    rintro ⟨a, b, c⟩ ⟨ha, hbc⟩
    rw [mem_singleton_iff] at ha
    exact ⟨by linarith, hKS (b, c) hbc⟩
  have hθ₃ : ((0 : ℝ), μ₀, σ₀) ∈ K₃ := ⟨mem_singleton 0, hθ₀⟩
  filter_upwards [ae_tendsto_gevMLE hK₃ hKS₃ hθ₃ hσ₀ hX hind] with ω hω θhat ε hθK hε hle
  have h3 := hω (fun n => (0, θhat n)) ε (fun n => ⟨mem_singleton 0, hθK n⟩) hε hle
  exact (continuous_snd.tendsto ((0 : ℝ), μ₀, σ₀)).comp h3

/-- **Measurable Gumbel MLEs exist** on any compact nonempty `K ⊂ ℝ × (0, ∞)`. -/
theorem exists_measurable_gumbelMLE {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, 0 < p.2) (hne : K.Nonempty) (n : ℕ) :
    ∃ g : (Fin n → ℝ) → ℝ × ℝ, Measurable g ∧
      ∀ x, g x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2 x) K (g x) := by
  refine exists_measurable_isMaxOn hK (f := fun p x => gevLogLikE 0 p.1 p.2 x)
    (fun x => ?_) (fun θ => ?_) hne
  · refine (continuousOn_finsetSum_ereal Finset.univ
      (fun i _ => ?_) (fun i _ p hp => ?_)).1
    · have hc := (continuousOn_gevLogDensityE (x i)).comp
        (f := fun p : ℝ × ℝ => ((0 : ℝ), p.1, p.2))
        (by fun_prop : Continuous fun p : ℝ × ℝ => ((0 : ℝ), p.1, p.2)).continuousOn
        (fun p hp => ⟨by norm_num, hKS p hp⟩)
      exact hc
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
        (gevLogDensityE_le (by norm_num) (hKS p hp) (x i))
  · exact Finset.measurable_sum _ fun i _ =>
      (measurable_gevLogDensityE 0 _ _).comp (measurable_pi_apply i)

/-- **The likelihood equations at an interior maximizer** of the Gumbel log-likelihood. -/
theorem gumbelScore_eq_zero_of_isMaxOn {K : Set (ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ}
    {θ : ℝ × ℝ} (hθK : θ ∈ interior K) (hσ : 0 < θ.2)
    (hmax : IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2 x) K θ) :
    ∑ i, gumbelScoreMu θ.1 θ.2 (x i) = 0 ∧ ∑ i, gumbelScoreSigma θ.1 θ.2 (x i) = 0 := by
  have hint := isOpen_interior.mem_nhds hθK
  have hle : ∀ p ∈ interior K, 0 < p.2 →
      ∑ i, log (gevLocScaleDensity 0 p.1 p.2 (x i)) ≤
        ∑ i, log (gevLocScaleDensity 0 θ.1 θ.2 (x i)) := by
    intro p hp hp2
    have := hmax (interior_subset hp)
    simp only [mem_ofPred_eq] at this
    rw [gevLogLikE_zero_eq_coe hp2, gevLogLikE_zero_eq_coe hσ] at this
    exact EReal.coe_le_coe_iff.1 this
  constructor
  · have hd : HasDerivAt (fun m => ∑ i, log (gevLocScaleDensity 0 m θ.2 (x i)))
        (∑ i, gumbelScoreMu θ.1 θ.2 (x i)) θ.1 := by
      have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
        hasDerivAt_log_gevLocScaleDensity_zero_mu hσ (μ := θ.1) (x := x i)
      convert this using 1; funext m; simp
    have hloc : IsLocalMax (fun m => ∑ i, log (gevLocScaleDensity 0 m θ.2 (x i))) θ.1 := by
      have h1 : ∀ᶠ m in 𝓝 θ.1, (m, θ.2) ∈ interior K :=
        (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
          (by simpa using hint)
      filter_upwards [h1] with m hm
      exact hle (m, θ.2) hm hσ
    exact hloc.hasDerivAt_eq_zero hd
  · have hd : HasDerivAt (fun s => ∑ i, log (gevLocScaleDensity 0 θ.1 s (x i)))
        (∑ i, gumbelScoreSigma θ.1 θ.2 (x i)) θ.2 := by
      have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
        hasDerivAt_log_gevLocScaleDensity_zero_sigma hσ (μ := θ.1) (x := x i)
      convert this using 1; funext s; simp
    have hloc : IsLocalMax (fun s => ∑ i, log (gevLocScaleDensity 0 θ.1 s (x i))) θ.2 := by
      have h1 : ∀ᶠ s in 𝓝 θ.2, (θ.1, s) ∈ interior K :=
        (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
          (by simpa using hint)
      filter_upwards [h1, lt_mem_nhds hσ] with s hs hs0
      exact hle (θ.1, s) hs hs0
    exact hloc.hasDerivAt_eq_zero hd

/-- The linearized Gumbel score `I(σ₀)⁻¹ ∇ℓ(μ₀, σ₀; x)`. -/
noncomputable def gumbelScoreLin (μ₀ σ₀ x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  let j₁₁ := gumbelFisherInfoInv σ₀ 0 0
  let j₁₂ := gumbelFisherInfoInv σ₀ 0 1
  let j₂₂ := gumbelFisherInfoInv σ₀ 1 1
  !₂[j₁₁ * gumbelScoreMu μ₀ σ₀ x + j₁₂ * gumbelScoreSigma μ₀ σ₀ x,
     j₁₂ * gumbelScoreMu μ₀ σ₀ x + j₂₂ * gumbelScoreSigma μ₀ σ₀ x]

/-- **CLT for the linearized Gumbel score**: `n^{-1/2} ∑ I(σ₀)⁻¹ ∇ℓ(μ₀, σ₀; Xᵢ) ⇒ N(0, I(σ₀)⁻¹)`. -/
theorem tendstoInDistribution_gumbelScoreLin (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gumbelScoreLin μ₀ σ₀ (X i ω))
      atTop W (fun _ => P) P' := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gumbelFisherInfo σ₀))
      (multivariateGaussian 0 (gumbelFisherInfo σ₀)) := HasLaw.id
  have hclt := tendstoInDistribution_gumbelScoreVec hσ₀ hX hind hZ
  -- Apply the continuous linear map `v ↦ gumbelFisherInfoInv σ₀ *ᵥ v`
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((Matrix.toLin' (gumbelFisherInfoInv σ₀)).toContinuousLinearMap.comp
        (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearEquiv.toContinuousLinearMap)
  have hL_apply : ∀ v : EuclideanSpace ℝ (Fin 2),
      L v = !₂[gumbelFisherInfoInv σ₀ 0 0 * v 0 + gumbelFisherInfoInv σ₀ 0 1 * v 1,
               gumbelFisherInfoInv σ₀ 1 0 * v 0 + gumbelFisherInfoInv σ₀ 1 1 * v 1] := by
    intro v; ext i; fin_cases i <;>
      simp [L, Matrix.toLin'_apply]
  have hL_score : ∀ x, L (gumbelScoreVec μ₀ σ₀ x) = gumbelScoreLin μ₀ σ₀ x := by
    intro x
    rw [hL_apply]
    ext i; fin_cases i <;> simp [gumbelScoreLin, gumbelScoreVec, gumbelFisherInfoInv]
  have hmap := hclt.continuous_comp L.continuous
  -- Identify the limit law `L (N(0, I)) = N(0, I⁻¹)` via inner products
  have hW' : HasLaw (fun ω => L ω) (multivariateGaussian 0 (gumbelFisherInfoInv σ₀))
      (multivariateGaussian 0 (gumbelFisherInfo σ₀)) := by
    have hsym : (gumbelFisherInfoInv σ₀).IsSymm := by
      refine Matrix.IsSymm.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [gumbelFisherInfoInv]
    have hinner : ∀ t : EuclideanSpace ℝ (Fin 2),
        HasLaw (fun ω => ⟪L ω, t⟫)
          (gaussianReal 0 (t ⬝ᵥ gumbelFisherInfoInv σ₀ *ᵥ t).toNNReal)
          (multivariateGaussian 0 (gumbelFisherInfo σ₀)) := by
      intro t
      set u : EuclideanSpace ℝ (Fin 2) := L t
      have hLu : ∀ ω, ⟪L ω, t⟫ = ⟪ω, u⟫ := by
        intro ω
        simp [u, hL_apply, PiLp.inner_apply, Fin.sum_univ_two, gumbelFisherInfoInv]
        ring
      have hvar : u ⬝ᵥ gumbelFisherInfo σ₀ *ᵥ u = t ⬝ᵥ gumbelFisherInfoInv σ₀ *ᵥ t := by
        have h1 : u.ofLp = gumbelFisherInfoInv σ₀ *ᵥ t.ofLp := by
          ext i; fin_cases i <;>
            simp [u, hL_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, gumbelFisherInfoInv]
        rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hsym.eq,
          gumbelFisherInfoInv_mul_gumbelFisherInfo hσ₀, Matrix.vecMul_one]
      have hl := hasLaw_inner_multivariateGaussian (posDef_gumbelFisherInfo hσ₀).posSemidef hZ u
      rw [hvar] at hl
      exact ⟨L.measurable.inner measurable_const |>.aemeasurable, by
        have : (fun ω => ⟪L ω, t⟫) = (fun ω => ⟪ω, u⟫) := funext hLu
        rw [this]; exact hl.map_eq⟩
    refine ⟨L.measurable.aemeasurable, ?_⟩
    exact Measure.ext_of_charFun (funext fun t => by
      have ht1 : charFun (Measure.map (fun ω => ⟪L ω, t⟫)
          (multivariateGaussian 0 (gumbelFisherInfo σ₀))) 1 =
          charFun (gaussianReal 0 (t ⬝ᵥ gumbelFisherInfoInv σ₀ *ᵥ t).toNNReal) 1 := by
        rw [(hinner t).map_eq]
      have ht2 : charFun (Measure.map (fun ω => ⟪ω, t⟫)
          (multivariateGaussian 0 (gumbelFisherInfoInv σ₀))) 1 =
          charFun (gaussianReal 0 (t ⬝ᵥ gumbelFisherInfoInv σ₀ *ᵥ t).toNNReal) 1 := by
        have h2 := hasLaw_inner_multivariateGaussian (posDef_gumbelFisherInfoInv hσ₀).posSemidef
          (HasLaw.id (μ := multivariateGaussian 0 (gumbelFisherInfoInv σ₀))) t
        simpa using congr_arg (fun μ => charFun μ 1) h2.map_eq
      have heq1 : charFun (Measure.map L (multivariateGaussian 0 (gumbelFisherInfo σ₀))) t =
          charFun (Measure.map (fun ω => ⟪L ω, t⟫) (multivariateGaussian 0 (gumbelFisherInfo σ₀))) 1 := by
        rw [charFun_apply, charFun_apply_real,
          integral_map L.measurable.aemeasurable (by fun_prop),
          integral_map (L.measurable.inner measurable_const).aemeasurable (by fun_prop)]
        simp [real_inner_comm]
      have heq2 : charFun (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) t =
          charFun (Measure.map (fun ω => ⟪ω, t⟫) (multivariateGaussian 0 (gumbelFisherInfoInv σ₀))) 1 := by
        rw [charFun_apply, charFun_apply_real,
          integral_map (show Measurable (fun ω : EuclideanSpace ℝ (Fin 2) => ⟪ω, t⟫) by fun_prop).aemeasurable
            (by fun_prop)]
        simp [real_inner_comm]
      rw [heq1, heq2, ht1, ht2])
  have hfinal : TendstoInDistribution
      (fun (n : ℕ) => ⇑L ∘ fun ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gumbelScoreVec μ₀ σ₀ (X i ω))
      atTop W (fun _ => P) P' :=
    ⟨hmap.forall_aemeasurable, hW.aemeasurable, by
      have hmap_eq : Measure.map (L ∘ id) (multivariateGaussian 0 (gumbelFisherInfo σ₀)) =
          Measure.map W P' := by
        simpa [Function.comp_def] using hW'.map_eq.trans hW.map_eq.symm
      have hpm1 : IsProbabilityMeasure (Measure.map (L ∘ id) (multivariateGaussian 0 (gumbelFisherInfo σ₀))) := by
        have : Measure.map (L ∘ id) (multivariateGaussian 0 (gumbelFisherInfo σ₀)) =
            multivariateGaussian 0 (gumbelFisherInfoInv σ₀) := by
          simpa [Function.comp_def] using hW'.map_eq
        rw [this]; infer_instance
      have hpm2 : IsProbabilityMeasure (Measure.map W P') := by
        rw [hW.map_eq]; infer_instance
      have hpm : (⟨Measure.map (L ∘ id) (multivariateGaussian 0 (gumbelFisherInfo σ₀)), hpm1⟩ :
          ProbabilityMeasure _) = ⟨Measure.map W P', hpm2⟩ :=
        ProbabilityMeasure.toMeasure_injective hmap_eq
      simpa only [← hpm] using hmap.tendsto⟩
  refine hfinal.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
  simp only [Function.comp_apply, map_smul, map_sum, hL_score]

/-- **Joint asymptotic normality of consistent roots of the Gumbel likelihood equations.** -/
theorem tendstoInDistribution_gumbelJointMLE (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (μ₀, σ₀)))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ∑ i ∈ Finset.range n, gumbelScoreMu (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gumbelScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  obtain ⟨K, hK0, hLip⟩ := exists_gumbelHess_lipschitz (μ₀ := μ₀) hσ₀
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hidX : ∀ i, IdentDistrib (X i) (X 0) P P := fun i => (hX i).identDistrib (hX 0)
  -- Strong law for the 3 true Hessian entries and the envelope
  have hslln : ∀ (g : ℝ → ℝ), Measurable g → Integrable g (gevLocScaleCDF 0 μ₀ hσ₀).measure →
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω))
        atTop (𝓝 (∫ x, g x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure)) := by
    intro g hg hgi
    have hE : ∫ ω, g (X 0 ω) ∂P = ∫ x, g x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure :=
      (hX 0).integral_comp hg.aestronglyMeasurable
    rw [← hE]
    have hae := strong_law_ae (fun i ω => g (X i ω))
      ((hX 0).integrable_comp hgi)
      (fun i j hij => (hind.indepFun hij).comp hg hg)
      (fun i => (hidX i).comp hg)
    filter_upwards [hae] with ω hω
    simpa [smul_eq_mul] using hω
  have hH11 := hslln (gumbelHessMuMu μ₀ σ₀) (by unfold gumbelHessMuMu; fun_prop)
    (integrable_gumbelHessMuMu hσ₀)
  have hH12 := hslln (gumbelHessMuSigma μ₀ σ₀) (by unfold gumbelHessMuSigma; fun_prop)
    (integrable_gumbelHessMuSigma hσ₀)
  have hH22 := hslln (gumbelHessSigmaSigma μ₀ σ₀) (by unfold gumbelHessSigmaSigma; fun_prop)
    (integrable_gumbelHessSigmaSigma hσ₀)
  have hEnv := hslln (gumbelEnv μ₀ σ₀) (measurable_gumbelEnv μ₀ σ₀) (integrable_gumbelEnv hσ₀)
  -- Define the observed averaged Hessian entries
  set B₁₁ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    gumbelHorizH gumbelHessMuMu μ₀ (θh n ω) (X i ω)
  set B₁₂ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    gumbelVertH gumbelHessMuSigma μ₀ σ₀ (θh n ω) (X i ω)
  set B₂₁ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    gumbelHorizH gumbelHessMuSigma μ₀ (θh n ω) (X i ω)
  set B₂₂ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ (θh n ω) (X i ω)
  set i₁₁ := gumbelFisherInfo σ₀ 0 0
  set i₁₂ := gumbelFisherInfo σ₀ 0 1
  set i₂₂ := gumbelFisherInfo σ₀ 1 1
  have hi₁₁ : ∫ x, gumbelHessMuMu μ₀ σ₀ x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure = -i₁₁ := by
    rw [integral_gumbelHessMuMu hσ₀]; simp [i₁₁, gumbelFisherInfo]
  have hi₁₂ : ∫ x, gumbelHessMuSigma μ₀ σ₀ x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure = -i₁₂ := by
    rw [integral_gumbelHessMuSigma hσ₀]; simp [i₁₂, gumbelFisherInfo]; ring
  have hi₂₂ : ∫ x, gumbelHessSigmaSigma μ₀ σ₀ x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure = -i₂₂ := by
    rw [integral_gumbelHessSigmaSigma hσ₀]; simp [i₂₂, gumbelFisherInfo]
  -- Almost-sure convergence of `B₁₁, B₁₂, B₂₁, B₂₂` to `-i₁₁, -i₁₂, -i₁₂, -i₂₂`
  have hBconv : ∀ᵐ ω ∂P, Tendsto (fun n => B₁₁ n ω) atTop (𝓝 (-i₁₁)) ∧
      Tendsto (fun n => B₁₂ n ω) atTop (𝓝 (-i₁₂)) ∧
      Tendsto (fun n => B₂₁ n ω) atTop (𝓝 (-i₁₂)) ∧
      Tendsto (fun n => B₂₂ n ω) atTop (𝓝 (-i₂₂)) := by
    filter_upwards [hcons, hH11, hH12, hH22, hEnv] with ω hω h11 h12 h22 henv
    rw [hi₁₁] at h11; rw [hi₁₂] at h12; rw [hi₂₂] at h22
    have hdist0 : Tendsto (fun n => |((θh n ω).1 - μ₀)| + |((θh n ω).2 - σ₀)|) atTop (𝓝 0) := by
      have h1 := ((continuous_fst.tendsto (μ₀, σ₀)).comp hω).sub_const μ₀ |>.abs
      have h2 := ((continuous_snd.tendsto (μ₀, σ₀)).comp hω).sub_const σ₀ |>.abs
      simpa using h1.add h2
    have herr : Tendsto (fun n : ℕ => K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω))) atTop (𝓝 0) := by
      simpa using (hdist0.const_mul K).mul henv
    have hnbhd : ∀ᶠ n in atTop, θh n ω ∈ gumbelNbhd μ₀ σ₀ :=
      hω.eventually (gumbelNbhd_mem_nhds hσ₀)
    have hstep : ∀ (f : ℕ → ℝ) (g : ℕ → ℝ) (L : ℝ),
        Tendsto g atTop (𝓝 L) →
        (∀ᶠ n in atTop, |f n - g n| ≤ K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω))) →
        Tendsto f atTop (𝓝 L) := by
      intro f g L hg hle
      have hdiff : Tendsto (fun n => f n - g n) atTop (𝓝 0) :=
        squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hle) herr
      simpa using hdiff.add hg
    have hσt_pos : ∀ θ ∈ gumbelNbhd μ₀ σ₀, ∀ t ∈ uIcc (0 : ℝ) 1, 0 < σ₀ + t * (θ.2 - σ₀) := by
      intro θ hθ t ht
      obtain ⟨_, _, hσlo, _⟩ := mem_gumbelNbhd_bounds hθ
      rw [uIcc_of_le zero_le_one] at ht
      have : σ₀ + t * (θ.2 - σ₀) = (1 - t) * σ₀ + t * θ.2 := by ring
      rw [this]; nlinarith [ht.1, ht.2]
    refine ⟨hstep _ _ _ h11 ?_, hstep _ _ _ h12 ?_, hstep _ _ _ h12 ?_, hstep _ _ _ h22 ?_⟩
    · filter_upwards [hnbhd] with n hn
      have havg : B₁₁ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuMu μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelHorizH gumbelHessMuMu μ₀ (θh n ω) (X i ω) - gumbelHessMuMu μ₀ σ₀ (X i ω)) := by
        simp only [B₁₁, ← mul_sub, ← Finset.sum_sub_distrib]
      rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
      have hsum : ∑ i ∈ Finset.range n,
          |gumbelHorizH gumbelHessMuMu μ₀ (θh n ω) (X i ω) - gumbelHessMuMu μ₀ σ₀ (X i ω)| ≤
          ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
        Finset.sum_le_sum fun i _ => abs_gumbelHorizH_sub_le hK0 hn (X i ω)
          (fun p hp => (hLip p hp (X i ω)).1) (by unfold gumbelHessMuMu; fun_prop)
      rw [← Finset.mul_sum] at hsum
      calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
        _ = _ := by ring
    · filter_upwards [hnbhd] with n hn
      have havg : B₁₂ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelVertH gumbelHessMuSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)) := by
        simp only [B₁₂, ← mul_sub, ← Finset.sum_sub_distrib]
      rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
      have hsum : ∑ i ∈ Finset.range n,
          |gumbelVertH gumbelHessMuSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)| ≤
          ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
        Finset.sum_le_sum fun i _ => abs_gumbelVertH_sub_le hK0 hn (X i ω)
          (fun p hp => (hLip p hp (X i ω)).2.1) (by
            unfold gumbelHessMuSigma
            intro t ht
            have hsne : σ₀ + t * ((θh n ω).2 - σ₀) ≠ 0 := (hσt_pos _ hn t ht).ne'
            have hc : ContinuousAt (fun u : ℝ => -(1 - exp (-((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀)))) +
                (X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀)) *
                  exp (-((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))))) /
                (σ₀ + u * ((θh n ω).2 - σ₀)) ^ 2) t := by
              fun_prop (disch := first | exact hsne | exact pow_ne_zero 2 hsne)
            exact hc.continuousWithinAt)
      rw [← Finset.mul_sum] at hsum
      calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
        _ = _ := by ring
    · filter_upwards [hnbhd] with n hn
      have havg : B₂₁ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelHorizH gumbelHessMuSigma μ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)) := by
        simp only [B₂₁, ← mul_sub, ← Finset.sum_sub_distrib]
      rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
      have hsum : ∑ i ∈ Finset.range n,
          |gumbelHorizH gumbelHessMuSigma μ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)| ≤
          ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
        Finset.sum_le_sum fun i _ => abs_gumbelHorizH_sub_le hK0 hn (X i ω)
          (fun p hp => (hLip p hp (X i ω)).2.1) (by unfold gumbelHessMuSigma; fun_prop)
      rw [← Finset.mul_sum] at hsum
      calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
        _ = _ := by ring
    · filter_upwards [hnbhd] with n hn
      have havg : B₂₂ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessSigmaSigma μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessSigmaSigma μ₀ σ₀ (X i ω)) := by
        simp only [B₂₂, ← mul_sub, ← Finset.sum_sub_distrib]
      rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
      have hsum : ∑ i ∈ Finset.range n,
          |gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessSigmaSigma μ₀ σ₀ (X i ω)| ≤
          ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
        Finset.sum_le_sum fun i _ => abs_gumbelVertH_sub_le hK0 hn (X i ω)
          (fun p hp => (hLip p hp (X i ω)).2.2) (by
            unfold gumbelHessSigmaSigma
            intro t ht
            have hsne : σ₀ + t * ((θh n ω).2 - σ₀) ≠ 0 := (hσt_pos _ hn t ht).ne'
            have hc : ContinuousAt (fun u : ℝ => (1 - 2 * ((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))) +
                (2 * ((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))) -
                  ((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))) ^ 2) *
                  exp (-((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))))) /
                (σ₀ + u * ((θh n ω).2 - σ₀)) ^ 2) t := by
              fun_prop (disch := first | exact hsne | exact pow_ne_zero 2 hsne)
            exact hc.continuousWithinAt)
      rw [← Finset.mul_sum] at hsum
      calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
        _ = _ := by ring
  -- Now solve the 2×2 linearized equations and apply Slutsky
  set j₁₁ := gumbelFisherInfoInv σ₀ 0 0
  set j₁₂ := gumbelFisherInfoInv σ₀ 0 1
  set j₂₂ := gumbelFisherInfoInv σ₀ 1 1
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin 2) := fun n ω =>
    √(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2 - σ₀]
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin 2) := fun n ω =>
    (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gumbelScoreLin μ₀ σ₀ (X i ω)
  set S₁ : ℕ → Ω → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gumbelScoreMu μ₀ σ₀ (X i ω)
  set S₂ : ℕ → Ω → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gumbelScoreSigma μ₀ σ₀ (X i ω)
  have hV := tendstoInDistribution_gumbelScoreLin hσ₀ hX hind hW
  have hTm : ∀ n, AEMeasurable (T n) P := fun n => by
    have hm_pair : Measurable (fun p : ℝ × ℝ => (!₂[p.1 - μ₀, p.2 - σ₀] : EuclideanSpace ℝ (Fin 2))) := by
      refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp (measurable_pi_iff.2 fun i => ?_)
      fin_cases i
      · exact measurable_fst.sub_const μ₀
      · exact measurable_snd.sub_const σ₀
    exact (hm_pair.comp_aemeasurable (hθm n)).const_smul (√(n : ℝ))
  have hVm : ∀ n, AEMeasurable (V n) P := fun n => hV.forall_aemeasurable n
  -- Boundedness in probability of `S₁` and `S₂` from the bivariate score CLT
  have hS1_bd : IsBoundedInProbability P S₁ := by
    have hZ0 : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gumbelFisherInfo σ₀))
        (multivariateGaussian 0 (gumbelFisherInfo σ₀)) := HasLaw.id
    have hclt := (tendstoInDistribution_gumbelScoreVec hσ₀ hX hind hZ0).continuous_comp
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous
    refine isBoundedInProbability_of_tendstoInDistribution (hclt.congr (fun n => Eventually.of_forall fun ω => ?_)
      (ae_of_all _ fun _ => rfl))
    simp [S₁, gumbelScoreVec]
  have hS2_bd : IsBoundedInProbability P S₂ := by
    have hZ0 : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gumbelFisherInfo σ₀))
        (multivariateGaussian 0 (gumbelFisherInfo σ₀)) := HasLaw.id
    have hclt := (tendstoInDistribution_gumbelScoreVec hσ₀ hX hind hZ0).continuous_comp
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
    refine isBoundedInProbability_of_tendstoInDistribution (hclt.congr (fun n => Eventually.of_forall fun ω => ?_)
      (ae_of_all _ fun _ => rfl))
    simp [S₂, gumbelScoreVec]
  -- Define an explicit a.e.-vanishing upper bound `M n ω` on the matrix error
  -- (avoiding measurability of `gumbelHorizH`/`gumbelVertH` by bounding `|B_ij - (-i_ij)|` directly
  -- by the measurable strong-law error `|H_avg - (-i_ij)| + K * dist(θh, θ₀) * env_avg`!)
  set E₁₁ : ℕ → Ω → ℝ := fun n ω =>
    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuMu μ₀ σ₀ (X i ω) - (-i₁₁)| +
      K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω))
  set E₁₂ : ℕ → Ω → ℝ := fun n ω =>
    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω) - (-i₁₂)| +
      K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω))
  set E₂₂ : ℕ → Ω → ℝ := fun n ω =>
    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessSigmaSigma μ₀ σ₀ (X i ω) - (-i₂₂)| +
      K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω))
  set δ : ℕ → Ω → ℝ := fun n ω => E₁₁ n ω + E₁₂ n ω + E₂₂ n ω
  have hδm : ∀ n, AEMeasurable (δ n) P := fun n => by
    have h1 := hθm n
    have hm1 : Measurable (gumbelHessMuMu μ₀ σ₀) := by unfold gumbelHessMuMu; fun_prop
    have hm2 : Measurable (gumbelHessMuSigma μ₀ σ₀) := by unfold gumbelHessMuSigma; fun_prop
    have hm3 : Measurable (gumbelHessSigmaSigma μ₀ σ₀) := by unfold gumbelHessSigmaSigma; fun_prop
    have hmE : Measurable (gumbelEnv μ₀ σ₀) := measurable_gumbelEnv μ₀ σ₀
    have hS1m : AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuMu μ₀ σ₀ (X i ω)) P :=
      (Finset.aemeasurable_fun_sum _ fun i _ => hm1.comp_aemeasurable (hXm i)).const_mul _
    have hS2m : AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω)) P :=
      (Finset.aemeasurable_fun_sum _ fun i _ => hm2.comp_aemeasurable (hXm i)).const_mul _
    have hS3m : AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessSigmaSigma μ₀ σ₀ (X i ω)) P :=
      (Finset.aemeasurable_fun_sum _ fun i _ => hm3.comp_aemeasurable (hXm i)).const_mul _
    have hSEm : AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) P :=
      (Finset.aemeasurable_fun_sum _ fun i _ => hmE.comp_aemeasurable (hXm i)).const_mul _
    have hdm : AEMeasurable (fun ω => |(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) P :=
      ((measurable_fst.comp_aemeasurable h1).sub_const μ₀).abs.add
        ((measurable_snd.comp_aemeasurable h1).sub_const σ₀).abs
    exact (((hS1m.sub_const _).abs.add ((hdm.const_mul K).mul hSEm)).add
      ((hS2m.sub_const _).abs.add ((hdm.const_mul K).mul hSEm))).add
      ((hS3m.sub_const _).abs.add ((hdm.const_mul K).mul hSEm))
  have hδ0 : TendstoInMeasure P δ atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (hδm n).aestronglyMeasurable) ?_
    filter_upwards [hcons, hH11, hH12, hH22, hEnv] with ω hω h11 h12 h22 henv
    rw [hi₁₁] at h11; rw [hi₁₂] at h12; rw [hi₂₂] at h22
    have hdist0 : Tendsto (fun n => |(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) atTop (𝓝 0) := by
      have h1 := ((continuous_fst.tendsto (μ₀, σ₀)).comp hω).sub_const μ₀ |>.abs
      have h2 := ((continuous_snd.tendsto (μ₀, σ₀)).comp hω).sub_const σ₀ |>.abs
      simpa using h1.add h2
    have herr : Tendsto (fun n : ℕ => K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω))) atTop (𝓝 0) := by
      simpa using (hdist0.const_mul K).mul henv
    have he1 : Tendsto (fun n => E₁₁ n ω) atTop (𝓝 0) := by
      simpa [E₁₁] using (h11.sub_const (-i₁₁)).abs.add herr
    have he2 : Tendsto (fun n => E₁₂ n ω) atTop (𝓝 0) := by
      simpa [E₁₂] using (h12.sub_const (-i₁₂)).abs.add herr
    have he3 : Tendsto (fun n => E₂₂ n ω) atTop (𝓝 0) := by
      simpa [E₂₂] using (h22.sub_const (-i₂₂)).abs.add herr
    simpa [δ] using (he1.add he2).add he3
  -- Continuous matrix-error factor `C * δ n ω * (|S₁ n ω| + |S₂ n ω|)`
  set det₀ := i₁₁ * i₂₂ - i₁₂ ^ 2
  have hdet_eq : det₀ = π ^ 2 / (6 * σ₀ ^ 4) := by
    simp [det₀, i₁₁, i₁₂, i₂₂, gumbelFisherInfo]
    field_simp; ring
  have hdet₀ : 0 < det₀ := by
    have hpi : 0 < π := pi_pos
    rw [hdet_eq]; positivity
  -- Actually, even simpler: `|(T n ω) - (V n ω)| ≤ C_mat * (|B - (-I)|) * (|S₁| + |S₂|)` whenever
  -- `|B - (-I)|` is small enough that `det(B) ≥ det₀ / 2`!
  -- Here `δ n ω → 0` a.e. and dominates all four `|B_ab - (-i_ab)|`, so for a single constant `C_mat`,
  -- eventually `‖T n ω - V n ω‖ ≤ C_mat * δ n ω * (|S₁ n ω| + |S₂ n ω|)`!
  set C_mat : ℝ := 24 * (1 + |i₁₁| + |i₁₂| + |i₂₂| + |j₁₁| + |j₁₂| + |j₂₂|) ^ 2 / det₀
  set G : ℕ → Ω → ℝ := fun n ω => C_mat * δ n ω * (|S₁ n ω| + |S₂ n ω|)
  have hG0 : TendstoInMeasure P G atTop (fun _ => 0) := by
    have hSbd : IsBoundedInProbability P (fun n ω => |S₁ n ω| + |S₂ n ω|) := by
      intro ε hε
      obtain ⟨M₁, hM₁⟩ := hS1_bd (ε / 2) (ENNReal.half_pos hε.ne')
      obtain ⟨M₂, hM₂⟩ := hS2_bd (ε / 2) (ENNReal.half_pos hε.ne')
      refine ⟨max M₁ 0 + max M₂ 0, ?_⟩
      filter_upwards [hM₁, hM₂] with n h1 h2
      have hsub : {ω | max M₁ 0 + max M₂ 0 < |(|S₁ n ω| + |S₂ n ω|)|} ⊆
          {ω | M₁ < |S₁ n ω|} ∪ {ω | M₂ < |S₂ n ω|} := by
        intro ω hω
        simp only [mem_ofPred_eq, mem_union] at hω ⊢
        rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at hω
        by_contra h
        push Not at h
        linarith [le_max_left M₁ 0, le_max_left M₂ 0]
      calc P {ω | max M₁ 0 + max M₂ 0 < |(|S₁ n ω| + |S₂ n ω|)|}
          ≤ P ({ω | M₁ < |S₁ n ω|} ∪ {ω | M₂ < |S₂ n ω|}) := measure_mono hsub
        _ ≤ P {ω | M₁ < |S₁ n ω|} + P {ω | M₂ < |S₂ n ω|} := measure_union_le _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
        _ = ε := ENNReal.add_halves ε
    have hCδ : TendstoInMeasure P (fun n ω => C_mat * δ n ω) atTop (fun _ => 0) := by
      have := tendstoInMeasure_comp hδ0 (φ := fun r => C_mat * r)
        (continuous_const.mul continuous_id).continuousAt
      simpa using this
    have hmul := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hSbd hCδ
    refine hmul.congr_left fun n => ae_of_all _ fun ω => by simp [G]
  have hdom : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |‖T n ω - V n ω‖| ≤ G n ω := by
    -- Exact algebraic identities for `j₁₁, j₁₂, j₂₂` in terms of `i₁₁, i₁₂, i₂₂, det₀`
    have hj₁₁ : j₁₁ = i₂₂ / det₀ := by
      rw [hdet_eq]; simp [j₁₁, i₂₂, gumbelFisherInfoInv, gumbelFisherInfo]
      field_simp [pi_ne_zero, hσ₀.ne']
    have hj₁₂ : j₁₂ = -i₁₂ / det₀ := by
      rw [hdet_eq]; simp [j₁₂, i₁₂, gumbelFisherInfoInv, gumbelFisherInfo]
      field_simp [pi_ne_zero, hσ₀.ne']; ring
    have hj₂₂ : j₂₂ = i₁₁ / det₀ := by
      rw [hdet_eq]; simp [j₂₂, i₁₁, gumbelFisherInfoInv, gumbelFisherInfo]
      field_simp [pi_ne_zero, hσ₀.ne']
    filter_upwards [hcons, hroot, hBconv, hH11, hH12, hH22, hEnv] with ω hω hrt hBc h11 h12 h22 henv
    rw [hi₁₁] at h11; rw [hi₁₂] at h12; rw [hi₂₂] at h22
    have hnbhd : ∀ᶠ n in atTop, θh n ω ∈ gumbelNbhd μ₀ σ₀ :=
      hω.eventually (gumbelNbhd_mem_nhds hσ₀)
    have hdetB : Tendsto (fun n => B₁₁ n ω * B₂₂ n ω - B₁₂ n ω * B₂₁ n ω) atTop (𝓝 det₀) := by
      have := (hBc.1.mul hBc.2.2.2).sub (hBc.2.1.mul hBc.2.2.1)
      convert this using 2; simp only [det₀]; ring
    have hδ_tend : Tendsto (fun n => δ n ω) atTop (𝓝 0) := by
      have hdist0 : Tendsto (fun n => |(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) atTop (𝓝 0) := by
        have h1 := ((continuous_fst.tendsto (μ₀, σ₀)).comp hω).sub_const μ₀ |>.abs
        have h2 := ((continuous_snd.tendsto (μ₀, σ₀)).comp hω).sub_const σ₀ |>.abs
        simpa using h1.add h2
      have herr : Tendsto (fun n : ℕ => K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω))) atTop (𝓝 0) := by
        simpa using (hdist0.const_mul K).mul henv
      have he1 : Tendsto (fun n => E₁₁ n ω) atTop (𝓝 0) := by
        simpa [E₁₁] using (h11.sub_const (-i₁₁)).abs.add herr
      have he2 : Tendsto (fun n => E₁₂ n ω) atTop (𝓝 0) := by
        simpa [E₁₂] using (h12.sub_const (-i₁₂)).abs.add herr
      have he3 : Tendsto (fun n => E₂₂ n ω) atTop (𝓝 0) := by
        simpa [E₂₂] using (h22.sub_const (-i₂₂)).abs.add herr
      simpa [δ] using (he1.add he2).add he3
    filter_upwards [eventually_gt_atTop 0, hnbhd, hrt, hdetB.eventually (lt_mem_nhds (half_lt_self hdet₀)),
      hδ_tend.eventually (gt_mem_nhds one_pos)] with n hn0 hnb ⟨hr1, hr2⟩ hDn hδ1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsq : (√(n : ℝ))⁻¹ * n = √(n : ℝ) := by
      have hsp : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnR
      rw [inv_mul_eq_div, div_eq_iff hsp.ne', mul_self_sqrt hnR.le]
    -- Linearized equations from `gumbelScore_sub_eq_axisH` and `hr1, hr2`
    set a := (θh n ω).1 - μ₀
    set b := (θh n ω).2 - σ₀
    have eμ : ∑ i ∈ Finset.range n, gumbelScoreMu μ₀ σ₀ (X i ω) =
        -(a * (n * B₁₁ n ω) + b * (n * B₁₂ n ω)) := by
      have hsum : ∑ i ∈ Finset.range n, (gumbelScoreMu (θh n ω).1 (θh n ω).2 (X i ω) -
          gumbelScoreMu μ₀ σ₀ (X i ω)) =
          a * ∑ i ∈ Finset.range n, gumbelHorizH gumbelHessMuMu μ₀ (θh n ω) (X i ω) +
          b * ∑ i ∈ Finset.range n, gumbelVertH gumbelHessMuSigma μ₀ σ₀ (θh n ω) (X i ω) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (gumbelScore_sub_eq_axisH hσ₀ hnb (X i ω)).1
      rw [Finset.sum_sub_distrib, hr1, zero_sub] at hsum
      have h1 : (n : ℝ) * B₁₁ n ω = ∑ i ∈ Finset.range n, gumbelHorizH gumbelHessMuMu μ₀ (θh n ω) (X i ω) := by
        simp only [B₁₁]; field_simp
      have h2 : (n : ℝ) * B₁₂ n ω = ∑ i ∈ Finset.range n, gumbelVertH gumbelHessMuSigma μ₀ σ₀ (θh n ω) (X i ω) := by
        simp only [B₁₂]; field_simp
      rw [h1, h2]; linarith
    have eσ : ∑ i ∈ Finset.range n, gumbelScoreSigma μ₀ σ₀ (X i ω) =
        -(a * (n * B₂₁ n ω) + b * (n * B₂₂ n ω)) := by
      have hsum : ∑ i ∈ Finset.range n, (gumbelScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) -
          gumbelScoreSigma μ₀ σ₀ (X i ω)) =
          a * ∑ i ∈ Finset.range n, gumbelHorizH gumbelHessMuSigma μ₀ (θh n ω) (X i ω) +
          b * ∑ i ∈ Finset.range n, gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ (θh n ω) (X i ω) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (gumbelScore_sub_eq_axisH hσ₀ hnb (X i ω)).2
      rw [Finset.sum_sub_distrib, hr2, zero_sub] at hsum
      have h1 : (n : ℝ) * B₂₁ n ω = ∑ i ∈ Finset.range n, gumbelHorizH gumbelHessMuSigma μ₀ (θh n ω) (X i ω) := by
        simp only [B₂₁]; field_simp
      have h2 : (n : ℝ) * B₂₂ n ω = ∑ i ∈ Finset.range n, gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ (θh n ω) (X i ω) := by
        simp only [B₂₂]; field_simp
      rw [h1, h2]; linarith
    have hS₁e : S₁ n ω = -(B₁₁ n ω * (√(n : ℝ) * a) + B₁₂ n ω * (√(n : ℝ) * b)) := by
      simp only [S₁]; rw [eμ]
      have : (√(n : ℝ))⁻¹ * -(a * (n * B₁₁ n ω) + b * (n * B₁₂ n ω)) =
          -(((√(n : ℝ))⁻¹ * n) * a * B₁₁ n ω + ((√(n : ℝ))⁻¹ * n) * b * B₁₂ n ω) := by ring
      rw [this, hsq]; ring
    have hS₂e : S₂ n ω = -(B₂₁ n ω * (√(n : ℝ) * a) + B₂₂ n ω * (√(n : ℝ) * b)) := by
      simp only [S₂]; rw [eσ]
      have : (√(n : ℝ))⁻¹ * -(a * (n * B₂₁ n ω) + b * (n * B₂₂ n ω)) =
          -(((√(n : ℝ))⁻¹ * n) * a * B₂₁ n ω + ((√(n : ℝ))⁻¹ * n) * b * B₂₂ n ω) := by ring
      rw [this, hsq]; ring
    set Dn := B₁₁ n ω * B₂₂ n ω - B₁₂ n ω * B₂₁ n ω
    -- Bound each of `|B_ab - (-i_ab)|` by `δ n ω`
    have hσt_pos : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < σ₀ + t * ((θh n ω).2 - σ₀) := by
      intro t ht
      obtain ⟨_, _, hσlo, _⟩ := mem_gumbelNbhd_bounds hnb
      rw [uIcc_of_le zero_le_one] at ht
      have h78 : 0 < 7 * σ₀ / 8 := by positivity
      have hle : 7 * σ₀ / 8 ≤ (1 - t) * σ₀ + t * (θh n ω).2 := by
        calc 7 * σ₀ / 8 = (1 - t) * (7 * σ₀ / 8) + t * (7 * σ₀ / 8) := by ring
          _ ≤ (1 - t) * σ₀ + t * (θh n ω).2 :=
              add_le_add (mul_le_mul_of_nonneg_left (by linarith) (by linarith [ht.2]))
                (mul_le_mul_of_nonneg_left hσlo ht.1)
      have heq : σ₀ + t * ((θh n ω).2 - σ₀) = (1 - t) * σ₀ + t * (θh n ω).2 := by ring
      linarith
    have hB11_le : |B₁₁ n ω - (-i₁₁)| ≤ δ n ω := by
      have htri := abs_sub_le (B₁₁ n ω)
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuMu μ₀ σ₀ (X i ω)) (-i₁₁)
      have havg : B₁₁ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuMu μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelHorizH gumbelHessMuMu μ₀ (θh n ω) (X i ω) - gumbelHessMuMu μ₀ σ₀ (X i ω)) := by
        simp only [B₁₁, ← mul_sub, ← Finset.sum_sub_distrib]
      have hpart : |B₁₁ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuMu μ₀ σ₀ (X i ω)| ≤
          K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by
        rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
        refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
        have hsum : ∑ i ∈ Finset.range n,
            |gumbelHorizH gumbelHessMuMu μ₀ (θh n ω) (X i ω) - gumbelHessMuMu μ₀ σ₀ (X i ω)| ≤
            ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
          Finset.sum_le_sum fun i _ => abs_gumbelHorizH_sub_le hK0 hnb (X i ω)
            (fun p hp => (hLip p hp (X i ω)).1) (by unfold gumbelHessMuMu; fun_prop)
        rw [← Finset.mul_sum] at hsum
        calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
              ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
          _ = _ := by ring
      have hE12_0 : 0 ≤ E₁₂ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      have hE22_0 : 0 ≤ E₂₂ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      linarith
    have hB12_le : |B₁₂ n ω - (-i₁₂)| ≤ δ n ω := by
      have htri := abs_sub_le (B₁₂ n ω)
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω)) (-i₁₂)
      have havg : B₁₂ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelVertH gumbelHessMuSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)) := by
        simp only [B₁₂, ← mul_sub, ← Finset.sum_sub_distrib]
      have hpart : |B₁₂ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω)| ≤
          K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by
        rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
        refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
        have hsum : ∑ i ∈ Finset.range n,
            |gumbelVertH gumbelHessMuSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)| ≤
            ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
          Finset.sum_le_sum fun i _ => abs_gumbelVertH_sub_le hK0 hnb (X i ω)
            (fun p hp => (hLip p hp (X i ω)).2.1) (by
              unfold gumbelHessMuSigma; intro t ht
              have hsne : σ₀ + t * ((θh n ω).2 - σ₀) ≠ 0 := (hσt_pos t ht).ne'
              have hc : ContinuousAt (fun u : ℝ => -(1 - exp (-((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀)))) +
                  (X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀)) *
                    exp (-((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))))) /
                  (σ₀ + u * ((θh n ω).2 - σ₀)) ^ 2) t := by
                fun_prop (disch := first | exact hsne | exact pow_ne_zero 2 hsne)
              exact hc.continuousWithinAt)
        rw [← Finset.mul_sum] at hsum
        calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
              ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
          _ = _ := by ring
      have hE11_0 : 0 ≤ E₁₁ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      have hE22_0 : 0 ≤ E₂₂ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      linarith
    have hB21_le : |B₂₁ n ω - (-i₁₂)| ≤ δ n ω := by
      have htri := abs_sub_le (B₂₁ n ω)
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω)) (-i₁₂)
      have havg : B₂₁ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelHorizH gumbelHessMuSigma μ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)) := by
        simp only [B₂₁, ← mul_sub, ← Finset.sum_sub_distrib]
      have hpart : |B₂₁ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessMuSigma μ₀ σ₀ (X i ω)| ≤
          K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by
        rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
        refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
        have hsum : ∑ i ∈ Finset.range n,
            |gumbelHorizH gumbelHessMuSigma μ₀ (θh n ω) (X i ω) - gumbelHessMuSigma μ₀ σ₀ (X i ω)| ≤
            ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
          Finset.sum_le_sum fun i _ => abs_gumbelHorizH_sub_le hK0 hnb (X i ω)
            (fun p hp => (hLip p hp (X i ω)).2.1) (by unfold gumbelHessMuSigma; fun_prop)
        rw [← Finset.mul_sum] at hsum
        calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
              ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
          _ = _ := by ring
      have hE11_0 : 0 ≤ E₁₁ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      have hE22_0 : 0 ≤ E₂₂ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      linarith
    have hB22_le : |B₂₂ n ω - (-i₂₂)| ≤ δ n ω := by
      have htri := abs_sub_le (B₂₂ n ω)
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessSigmaSigma μ₀ σ₀ (X i ω)) (-i₂₂)
      have havg : B₂₂ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessSigmaSigma μ₀ σ₀ (X i ω) =
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessSigmaSigma μ₀ σ₀ (X i ω)) := by
        simp only [B₂₂, ← mul_sub, ← Finset.sum_sub_distrib]
      have hpart : |B₂₂ n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelHessSigmaSigma μ₀ σ₀ (X i ω)| ≤
          K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by
        rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.2 n.cast_nonneg)]
        refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
        have hsum : ∑ i ∈ Finset.range n,
            |gumbelVertH gumbelHessSigmaSigma μ₀ σ₀ (θh n ω) (X i ω) - gumbelHessSigmaSigma μ₀ σ₀ (X i ω)| ≤
            ∑ i ∈ Finset.range n, K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) * gumbelEnv μ₀ σ₀ (X i ω) :=
          Finset.sum_le_sum fun i _ => abs_gumbelVertH_sub_le hK0 hnb (X i ω)
            (fun p hp => (hLip p hp (X i ω)).2.2) (by
              unfold gumbelHessSigmaSigma; intro t ht
              have hsne : σ₀ + t * ((θh n ω).2 - σ₀) ≠ 0 := (hσt_pos t ht).ne'
              have hc : ContinuousAt (fun u : ℝ => (1 - 2 * ((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))) +
                  (2 * ((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))) -
                    ((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))) ^ 2) *
                    exp (-((X i ω - μ₀) / (σ₀ + u * ((θh n ω).2 - σ₀))))) /
                  (σ₀ + u * ((θh n ω).2 - σ₀)) ^ 2) t := by
                fun_prop (disch := first | exact hsne | exact pow_ne_zero 2 hsne)
              exact hc.continuousWithinAt)
        rw [← Finset.mul_sum] at hsum
        calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * (K * (|(θh n ω).1 - μ₀| + |(θh n ω).2 - σ₀|) *
              ∑ i ∈ Finset.range n, gumbelEnv μ₀ σ₀ (X i ω)) := by gcongr
          _ = _ := by ring
      have hE11_0 : 0 ≤ E₁₁ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      have hE12_0 : 0 ≤ E₁₂ n ω := add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => gumbelEnv_nonneg _ _ _)))
      linarith
    -- Apply the algebraic 2×2 perturbation bound
    have hV0 : V n ω 0 = j₁₁ * S₁ n ω + j₁₂ * S₂ n ω := by
      simp only [V, S₁, S₂, gumbelScoreLin, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        smul_eq_mul, Matrix.cons_val_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hV1 : V n ω 1 = j₁₂ * S₁ n ω + j₂₂ * S₂ n ω := by
      simp only [V, S₁, S₂, gumbelScoreLin, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring
    have hT0 : T n ω 0 = √(n : ℝ) * a := by simp [T, a]
    have hT1 : T n ω 1 = √(n : ℝ) * b := by simp [T, b]
    rw [abs_norm]
    refine (norm_euclidean_two_le _).trans ?_
    simp only [PiLp.sub_apply, hT0, hT1, hV0, hV1]
    exact two_by_two_perturbation_bound hS₁e hS₂e hdet₀ hj₁₁ hj₁₂ hj₂₂
      hB11_le hB12_le hB21_le hB22_le hδ1 hDn
  have hS1m : ∀ n, AEMeasurable (S₁ n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ =>
      (measurable_gumbelScoreMu μ₀ σ₀).comp_aemeasurable (hXm i)).const_mul _
  have hS2m : ∀ n, AEMeasurable (S₂ n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ =>
      (measurable_gumbelScoreSigma μ₀ σ₀).comp_aemeasurable (hXm i)).const_mul _
  have hGm : ∀ n, AEMeasurable (G n) P := fun n =>
    ((hδm n).const_mul C_mat).mul ((hS1m n).abs.add (hS2m n).abs)
  have hdiff : TendstoInMeasure P (T - V) atTop 0 := by
    have hr := tendstoInMeasure_zero_of_ae_eventually_abs_le
      (f := fun n ω => ‖T n ω - V n ω‖)
      (fun n => ((hTm n).sub (hVm n)).norm.aestronglyMeasurable)
      (fun n => (hGm n).aestronglyMeasurable) hdom hG0
    rw [tendstoInMeasure_iff_norm] at hr ⊢
    intro ε hε
    simpa using hr ε hε
  exact tendstoInDistribution_of_tendstoInMeasure_sub T W hV hdiff hTm

/-- **Joint asymptotic normality of the two-parameter Gumbel MLE** on a compact parameter set
`K ⊂ ℝ × (0, ∞)` with `(μ₀, σ₀) ∈ interior K`:
`√n (μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, gumbelFisherInfoInv σ₀)`. -/
theorem tendstoInDistribution_gumbelMLE {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ interior K) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2
      (fun i : Fin n => X i ω)) K (θh n ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (μ₀, σ₀)) := by
    filter_upwards [ae_tendsto_gumbelMLE hK hKS (interior_subset hθ₀) hσ₀ hX hind] with ω hω
    refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have hle := hmax n ω (interior_subset hθ₀)
    simp only [mem_ofPred_eq] at hle
    simpa using hle
  have hroot : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ∑ i ∈ Finset.range n, gumbelScoreMu (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gumbelScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0 := by
    filter_upwards [hcons] with ω hω
    filter_upwards [hω.eventually (isOpen_interior.mem_nhds hθ₀)] with n hn
    have hσn : 0 < (θh n ω).2 := hKS (θh n ω) (interior_subset hn)
    have hfin := gumbelScore_eq_zero_of_isMaxOn hn hσn (hmax n ω)
    rw [Fin.sum_univ_eq_sum_range (fun i => gumbelScoreMu (θh n ω).1 (θh n ω).2 (X i ω))] at hfin
    rw [Fin.sum_univ_eq_sum_range (fun i => gumbelScoreSigma (θh n ω).1 (θh n ω).2 (X i ω))] at hfin
    exact hfin
  exact tendstoInDistribution_gumbelJointMLE hσ₀ hX hind hθm hcons hroot hW

/-- **Existence and joint asymptotic normality of a measurable two-parameter Gumbel MLE.** -/
theorem exists_gumbelMLE_tendstoInDistribution {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ interior K) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) P') :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2 x) K (g n x)) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) •
          !₂[(g n (fun i : Fin n => X i ω)).1 - μ₀, (g n (fun i : Fin n => X i ω)).2 - σ₀])
        atTop W (fun _ => P) P' := by
  choose g hgm hg using exists_measurable_gumbelMLE hK hKS ⟨_, interior_subset hθ₀⟩
  refine ⟨g, hgm, hg, ?_⟩
  exact tendstoInDistribution_gumbelMLE hK hKS hθ₀ hσ₀ hX hind
    (θh := fun n ω => g n (fun i : Fin n => X i ω))
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2) hW

end GumbelMLENormality

/-! ### Unconditional Gumbel return-level normality and computable plug-in confidence intervals -/

section GumbelReturnLevel

variable {μ₀ σ₀ m : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- The asymptotic variance `∇z_mᵀ I(σ)⁻¹ ∇z_m` of the Gumbel MLE `m`-block return level,
where `∇z_m = (1, -log (-log (1 - 1/m)))`. -/
noncomputable def gumbelReturnLevelVar (σ m : ℝ) : ℝ :=
  (!₂[1, -log (-log (1 - 1 / m))] : EuclideanSpace ℝ (Fin 2)) ⬝ᵥ
    gumbelFisherInfoInv σ *ᵥ (!₂[1, -log (-log (1 - 1 / m))] : EuclideanSpace ℝ (Fin 2))

/-- Closed-form formula: `gumbelReturnLevelVar σ m = σ² (1 + 6 (1 - γ - log y_m)² / π²)`. -/
theorem gumbelReturnLevelVar_eq (σ m : ℝ) :
    gumbelReturnLevelVar σ m =
      σ ^ 2 * (1 + 6 * (1 - eulerMascheroniConstant - log (-log (1 - 1 / m))) ^ 2 / π ^ 2) := by
  simp [gumbelReturnLevelVar, gumbelFisherInfoInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `gumbelReturnLevelVar σ m > 0` for every `σ > 0` and every `m`. -/
theorem gumbelReturnLevelVar_pos {σ : ℝ} (hσ : 0 < σ) (m : ℝ) :
    0 < gumbelReturnLevelVar σ m := by
  rw [gumbelReturnLevelVar_eq]
  have h2 : 0 ≤ 6 * (1 - eulerMascheroniConstant - log (-log (1 - 1 / m))) ^ 2 / π ^ 2 := by
    positivity
  exact mul_pos (sq_pos_of_pos hσ) (by linarith)

lemma continuous_gumbelReturnLevelVar (m : ℝ) : Continuous fun σ : ℝ => gumbelReturnLevelVar σ m := by
  have : (fun σ : ℝ => gumbelReturnLevelVar σ m) =
      fun σ => σ ^ 2 * (1 + 6 * (1 - eulerMascheroniConstant - log (-log (1 - 1 / m))) ^ 2 / π ^ 2) :=
    funext fun σ => gumbelReturnLevelVar_eq σ m
  rw [this]; fun_prop

/-- **Unconditional asymptotic normality of the Gumbel maximum likelihood return level**
([Coles 2001, §3.3.3]): for iid `Gumbel(μ₀, σ₀)` observations and measurable maximizers over
a compact `K ⊂ ℝ × (0, ∞)` containing `(μ₀, σ₀)` in its interior,
`√n (ẑ_m - z_m) ⇒ N(0, gumbelReturnLevelVar σ₀ m)`. -/
theorem tendstoInDistribution_gumbelMLEReturnLevel {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ interior K) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2
      (fun i : Fin n => X i ω)) K (θh n ω))
    {W : Ω' → ℝ} (hW : HasLaw W (gaussianReal 0 (gumbelReturnLevelVar σ₀ m).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel 0 (θh n ω).1 (θh n ω).2 m - gevReturnLevel 0 μ₀ σ₀ m))
      atTop W (fun _ => P) P' := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gumbelFisherInfoInv σ₀))
      (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) := HasLaw.id
  have hθN := tendstoInDistribution_gumbelMLE hK hKS hθ₀ hσ₀ hX hind hθm hθK hmax hZ
  exact tendstoInDistribution_gumbelReturnLevel hθm (posDef_gumbelFisherInfoInv hσ₀).posSemidef
    hθN hZ hW

/-- **Computable asymptotic confidence interval for the Gumbel MLE return level**
([Coles 2001, §3.3.3]): with the plug-in standard error `ŝₙ = √(gumbelReturnLevelVar σ̂ₙ m)`
computed from the MLE alone, `[ẑ_m - z ŝₙ/√n, ẑ_m + z ŝₙ/√n]` has asymptotic coverage
`N(0, 1)([-z, z])`. No parameter-normality or standard-error hypothesis is assumed. -/
theorem tendsto_measure_mem_gumbelMLEReturnLevelPlugInInterval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ interior K) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2
      (fun i : Fin n => X i ω)) K (θh n ω)) (z : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gevReturnLevel 0 μ₀ σ₀ m ∈ Icc
      (gevReturnLevel 0 (θh n ω).1 (θh n ω).2 m -
        z * √(gumbelReturnLevelVar (θh n ω).2 m) / √(n : ℝ))
      (gevReturnLevel 0 (θh n ω).1 (θh n ω).2 m +
        z * √(gumbelReturnLevelVar (θh n ω).2 m) / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hvpos : 0 < gumbelReturnLevelVar σ₀ m := gumbelReturnLevelVar_pos hσ₀ m
  have hW : HasLaw id (gaussianReal 0 (gumbelReturnLevelVar σ₀ m).toNNReal)
      (gaussianReal 0 (gumbelReturnLevelVar σ₀ m).toNNReal) := HasLaw.id
  have hN := tendstoInDistribution_gumbelMLEReturnLevel (m := m) hK hKS hθ₀ hσ₀ hX hind hθm hθK hmax hW
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gumbelFisherInfoInv σ₀))
      (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) := HasLaw.id
  have hθN := tendstoInDistribution_gumbelMLE hK hKS hθ₀ hσ₀ hX hind hθm hθK hmax hZ
  have hθ0 : TendstoInMeasure P (fun (n : ℕ) ω =>
      (!₂[(θh n ω).1 - μ₀, (θh n ω).2 - σ₀] : EuclideanSpace ℝ (Fin 2)))
      atTop (fun _ => 0) :=
    TendstoInDistribution.tendstoInMeasure_of_smul (r := fun n : ℕ => √(n : ℝ)) hθN
      tendsto_sqrt_natCast_atTop
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun v => √(gumbelReturnLevelVar (σ₀ + v 1) m)
  have hG : ContinuousAt G 0 := by
    have hc : Continuous G := ((continuous_gumbelReturnLevelVar m).comp
      (continuous_const.add (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).sqrt
    exact hc.continuousAt
  have hS := hθ0.comp_continuousAt hG
  simp only [G, PiLp.zero_apply, add_zero] at hS
  have hS' : TendstoInMeasure P (fun (n : ℕ) ω => √(gumbelReturnLevelVar (θh n ω).2 m))
      atTop (fun _ => √(gumbelReturnLevelVar σ₀ m)) := by
    simpa using hS
  have hSm : ∀ n : ℕ, AEMeasurable (fun ω => √(gumbelReturnLevelVar (θh n ω).2 m)) P := fun n =>
    (((continuous_gumbelReturnLevelVar m).measurable.comp measurable_snd).comp_aemeasurable
      (hθm n)).sqrt
  have hW' : HasLaw id (gaussianReal 0 ((√(gumbelReturnLevelVar σ₀ m)) ^ 2).toNNReal)
      (gaussianReal 0 (gumbelReturnLevelVar σ₀ m).toNNReal) := by
    rwa [Real.sq_sqrt hvpos.le]
  exact hN.tendsto_measure_mem_waldInterval_gaussian (Real.sqrt_pos.2 hvpos) z hW'
    (tendsto_sqrt_natCast_atTop.eventually_gt_atTop 0) hS' hSm

/-- **Computable asymptotic confidence interval for the Gumbel MLE return level, with existence of
the measurable MLE.** -/
theorem exists_gumbelMLE_returnLevelPlugInInterval_tendsto {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ interior K) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P) :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2 x) K (g n x)) ∧
      ∀ z : ℝ, Tendsto (fun n : ℕ => P {ω | gevReturnLevel 0 μ₀ σ₀ m ∈ Icc
        (gevReturnLevel 0 (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2 m -
          z * √(gumbelReturnLevelVar (g n (fun i : Fin n => X i ω)).2 m) / √(n : ℝ))
        (gevReturnLevel 0 (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2 m +
          z * √(gumbelReturnLevelVar (g n (fun i : Fin n => X i ω)).2 m) / √(n : ℝ))})
        atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  choose g hgm hg using exists_measurable_gumbelMLE hK hKS ⟨_, interior_subset hθ₀⟩
  refine ⟨g, hgm, hg, fun z => ?_⟩
  exact tendsto_measure_mem_gumbelMLEReturnLevelPlugInInterval (m := m) hK hKS hθ₀ hσ₀ hX hind
    (θh := fun n ω => g n (fun i : Fin n => X i ω))
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2) z

end GumbelReturnLevel

/-! ### Full `3 × 3` GEV Fisher information and trivariate score CLT at `ξ = 0` -/

section GEVZeroScore3

variable {μ σ : ℝ}

/-- The standardized three-component GEV score at `ξ = 0`, in the order `(μ, σ, ξ)`:
`s₀(z) = 1 - e^{-z}`, `s₁(z) = -1 + z (1 - e^{-z})`, `s₂(z) = -z + z² (1 - e^{-z})/2`. -/
noncomputable def stdGumbelScore3 (i : Fin 3) (z : ℝ) : ℝ :=
  match i with
  | ⟨0, _⟩ => 1 - exp (-z)
  | ⟨1, _⟩ => -1 + z * (1 - exp (-z))
  | ⟨2, _⟩ => -z + z ^ 2 * (1 - exp (-z)) / 2

/-- The full three-component GEV score vector at `ξ = 0`, in the order `(μ, σ, ξ)`. -/
noncomputable def gumbelScoreVec3 (μ σ x : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[gumbelScoreMu μ σ x, gumbelScoreSigma μ σ x, gumbelScoreXi μ σ x]

lemma measurable_gumbelScoreVec3 (μ σ : ℝ) : Measurable (gumbelScoreVec3 μ σ) := by
  unfold gumbelScoreVec3
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · simpa using measurable_gumbelScoreMu μ σ
  · simpa using measurable_gumbelScoreSigma μ σ
  · simpa using measurable_gumbelScoreXi μ σ

lemma gumbelScoreVec3_eq_std (μ σ x : ℝ) (i : Fin 3) :
    gumbelScoreVec3 μ σ x i = (![σ⁻¹, σ⁻¹, 1] i) * stdGumbelScore3 i ((x - μ) / σ) := by
  fin_cases i <;> simp [gumbelScoreVec3, stdGumbelScore3, gumbelScoreMu, gumbelScoreSigma,
    gumbelScoreXi, div_eq_inv_mul]

/-- The full `3 × 3` GEV Fisher information matrix at `ξ = 0`, in the order `(μ, σ, ξ)`:
`I_0(σ)_{ij} = E_{GEV(0, 0, σ)}[∂_i ℓ · ∂_j ℓ]`. Defined via the standard Gumbel measure so
no closed-form evaluation of `ζ(3)` is required. -/
noncomputable def gevFisherInfoZero (σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    (![σ⁻¹, σ⁻¹, 1] i) * (![σ⁻¹, σ⁻¹, 1] j) *
      ∫ z, stdGumbelScore3 i z * stdGumbelScore3 j z ∂(gevLocScaleCDF 0 0 one_pos).measure

private lemma integrable_stdGumbelScore3_mul (i j : Fin 3) :
    Integrable (fun z => stdGumbelScore3 i z * stdGumbelScore3 j z)
      (gevLocScaleCDF 0 0 one_pos).measure := by
  have hm : Measurable (fun z => stdGumbelScore3 i z * stdGumbelScore3 j z) := by
    fin_cases i <;> fin_cases j <;> simp only [stdGumbelScore3] <;> fun_prop
  -- Under `t = e^{-z}` (`z = -log t`), every `stdGumbelScore3 i (-log t)` is bounded by
  -- `2 * (1 + |log t|)^2 * (1 + t)`, so the product is bounded by
  -- `4 * (1 + |log t|)^4 * (1 + t)^2`, which is integrable against `e^{-t} dt` on `(0, ∞)`!
  rw [integrable_gevLocScaleCDF_iff one_pos hm]
  have hdom : IntegrableOn (fun t : ℝ =>
      4 * (1 + |log t| ^ 4) * 8 * (1 + t ^ 2) * exp (-t)) (Ioi 0) volume := by
    have h00 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 0) (by norm_num) 0
    have h04 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 0) (by norm_num) 4
    have h20 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 2) (by norm_num) 0
    have h24 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 2) (by norm_num) 4
    have hsum : IntegrableOn (fun t => 32 * ((exp (-t) * (t ^ (0 : ℝ) * |log t| ^ 0) +
        exp (-t) * (t ^ (0 : ℝ) * |log t| ^ 4)) + (exp (-t) * (t ^ (2 : ℝ) * |log t| ^ 0) +
        exp (-t) * (t ^ (2 : ℝ) * |log t| ^ 4)))) (Ioi 0) volume :=
      ((h00.add h04).add (h20.add h24)).const_mul 32
    refine hsum.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only [rpow_zero, rpow_two, pow_zero, mul_one]
    ring
  refine hdom.mono' (by
    have h1 : Measurable (fun t : ℝ => exp (-t) * (stdGumbelScore3 i (0 + 1 * gevTransform 0 t) *
        stdGumbelScore3 j (0 + 1 * gevTransform 0 t))) := by
      fin_cases i <;> fin_cases j <;> simp only [stdGumbelScore3, gevTransform, ↓reduceIte] <;> fun_prop
    exact h1.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have harg : (0 : ℝ) + 1 * gevTransform 0 t = -log t := by simp [gevTransform]
  rw [harg]
  have h1 : ∀ k : Fin 3, |stdGumbelScore3 k (-log t)| ≤
      2 * (1 + |log t| ^ 2) * (1 + t) := by
    intro k
    have he : exp (-(-log t)) = t := by rw [neg_neg, exp_log ht0]
    have h1t : |1 - t| ≤ 1 + t := by
      calc |1 - t| ≤ |(1 : ℝ)| + |t| := abs_sub _ _
        _ = 1 + t := by rw [abs_one, abs_of_pos ht0]
    have hl1 : |log t| ≤ 1 + |log t| ^ 2 := by nlinarith [sq_nonneg (|log t| - 1)]
    have hl2 : |log t| ^ 2 ≤ 1 + |log t| ^ 2 := by linarith
    fin_cases k
    · simp only [stdGumbelScore3, he]
      calc |1 - t| ≤ 1 + t := h1t
        _ ≤ 2 * (1 + |log t| ^ 2) * (1 + t) := by nlinarith [sq_nonneg |log t|, ht0]
    · simp only [stdGumbelScore3, he]
      have hmul := mul_le_mul hl1 h1t (abs_nonneg _) (by positivity)
      calc |-1 + -log t * (1 - t)| ≤ |-1| + |-log t * (1 - t)| := abs_add_le _ _
        _ = 1 + |log t| * |1 - t| := by rw [abs_neg, abs_one, abs_mul, abs_neg]
        _ ≤ 1 + (1 + |log t| ^ 2) * (1 + t) := by linarith
        _ ≤ 2 * (1 + |log t| ^ 2) * (1 + t) := by nlinarith [sq_nonneg |log t|, ht0]
    · simp only [stdGumbelScore3, neg_neg, even_two, Even.neg_pow, exp_log ht0]
      calc |log t + (log t) ^ 2 * (1 - t) / 2|
          ≤ |log t| + |(log t) ^ 2 * (1 - t) / 2| := abs_add_le _ _
        _ = |log t| + |log t| ^ 2 * |1 - t| / 2 := by rw [abs_div, abs_mul, abs_pow, abs_two]
        _ ≤ (1 + |log t| ^ 2) + (1 + |log t| ^ 2) * (1 + t) / 2 := by
            have := mul_le_mul hl2 h1t (abs_nonneg _) (by positivity)
            linarith
        _ ≤ 2 * (1 + |log t| ^ 2) * (1 + t) := by nlinarith [sq_nonneg |log t|, ht0]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _)]
  have hprod := mul_le_mul (h1 i) (h1 j) (abs_nonneg _) (by positivity)
  have hsq1 : (1 + |log t| ^ 2) ^ 2 ≤ 2 * (1 + |log t| ^ 4) := by
    have : (1 - |log t| ^ 2) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  have hsq2 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    have : (1 - t) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  have hcomb : (2 * (1 + |log t| ^ 2) * (1 + t)) * (2 * (1 + |log t| ^ 2) * (1 + t)) ≤
      4 * (1 + |log t| ^ 4) * 8 * (1 + t ^ 2) := by
    have h4 : (1 + |log t| ^ 2) ^ 2 * (1 + t) ^ 2 ≤ (2 * (1 + |log t| ^ 4)) * (2 * (1 + t ^ 2)) :=
      mul_le_mul hsq1 hsq2 (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg |log t|, ht0]
  rw [mul_comm (exp (-t))]
  exact mul_le_mul_of_nonneg_right (hprod.trans hcomb) (exp_pos _).le

lemma memLp_lin_gumbelScore3 (hσ : 0 < σ) (a b c : ℝ) :
    MemLp (fun x => a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x + c * gumbelScoreXi μ σ x)
      2 (gevLocScaleCDF 0 μ hσ).measure := by
  have hm : Measurable (fun x => a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x +
      c * gumbelScoreXi μ σ x) := by
    have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreSigma μ σ
    have := measurable_gumbelScoreXi μ σ; fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  set v : Fin 3 → ℝ := ![a, b, c]
  have hsq : (fun x => (a * gumbelScoreMu μ σ x + b * gumbelScoreSigma μ σ x +
      c * gumbelScoreXi μ σ x) ^ 2) = fun x =>
      ∑ i : Fin 3, ∑ j : Fin 3, (v i * v j * (![σ⁻¹, σ⁻¹, 1] i) * (![σ⁻¹, σ⁻¹, 1] j)) *
        (stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ)) := by
    funext x
    simp [Fin.sum_univ_three, v, stdGumbelScore3, gumbelScoreMu, gumbelScoreSigma,
      gumbelScoreXi, div_eq_inv_mul]
    ring
  rw [hsq]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  refine Integrable.const_mul ?_ _
  have h1 := integrable_stdGumbelScore3_mul i j
  have hmi : Measurable (fun z => stdGumbelScore3 i z * stdGumbelScore3 j z) := by
    fin_cases i <;> fin_cases j <;> simp only [stdGumbelScore3] <;> fun_prop
  have hmi' : Measurable (fun x => stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ)) :=
    hmi.comp (by fun_prop)
  rw [integrable_gevLocScaleCDF_iff one_pos hmi] at h1
  rw [integrable_gevLocScaleCDF_iff hσ hmi']
  refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioi
  have : (μ + σ * gevTransform 0 t - μ) / σ = 0 + 1 * gevTransform 0 t := by
    simp [gevTransform]; field_simp [hσ.ne']
  rw [this]

/-- Quadratic-form identity for `gevFisherInfoZero`:
`E[(∑ vᵢ sᵢ(X))²] = vᵀ I_0(σ) v`. -/
theorem integral_lin_gumbelScore3_sq (hσ : 0 < σ) (v : Fin 3 → ℝ) :
    ∫ x, (v 0 * gumbelScoreMu μ σ x + v 1 * gumbelScoreSigma μ σ x + v 2 * gumbelScoreXi μ σ x) ^ 2
      ∂(gevLocScaleCDF 0 μ hσ).measure = v ⬝ᵥ gevFisherInfoZero σ *ᵥ v := by
  have hterm : ∀ i j : Fin 3,
      ∫ x, stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ)
        ∂(gevLocScaleCDF 0 μ hσ).measure =
      ∫ z, stdGumbelScore3 i z * stdGumbelScore3 j z ∂(gevLocScaleCDF 0 0 one_pos).measure := by
    intro i j
    have hmi : Measurable (fun z => stdGumbelScore3 i z * stdGumbelScore3 j z) := by
      fin_cases i <;> fin_cases j <;> simp only [stdGumbelScore3] <;> fun_prop
    have hmi' : Measurable (fun x => stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ)) :=
      hmi.comp (by fun_prop)
    rw [integral_gevLocScaleCDF hσ hmi', integral_gevLocScaleCDF one_pos hmi]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have : (μ + σ * gevTransform 0 t - μ) / σ = 0 + 1 * gevTransform 0 t := by
      simp [gevTransform]; field_simp [hσ.ne']
    rw [this]
  have hint : ∀ i j : Fin 3,
      Integrable (fun x => stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ))
        (gevLocScaleCDF 0 μ hσ).measure := by
    intro i j
    have hmi : Measurable (fun z => stdGumbelScore3 i z * stdGumbelScore3 j z) := by
      fin_cases i <;> fin_cases j <;> simp only [stdGumbelScore3] <;> fun_prop
    have hmi' : Measurable (fun x => stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ)) :=
      hmi.comp (by fun_prop)
    have h1 := integrable_stdGumbelScore3_mul i j
    rw [integrable_gevLocScaleCDF_iff one_pos hmi] at h1
    rw [integrable_gevLocScaleCDF_iff hσ hmi']
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioi
    have : (μ + σ * gevTransform 0 t - μ) / σ = 0 + 1 * gevTransform 0 t := by
      simp [gevTransform]; field_simp [hσ.ne']
    rw [this]
  have hsq : (fun x => (v 0 * gumbelScoreMu μ σ x + v 1 * gumbelScoreSigma μ σ x +
      v 2 * gumbelScoreXi μ σ x) ^ 2) = fun x =>
      ∑ i : Fin 3, ∑ j : Fin 3, (v i * v j * (![σ⁻¹, σ⁻¹, 1] i) * (![σ⁻¹, σ⁻¹, 1] j)) *
        (stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ)) := by
    funext x
    simp [Fin.sum_univ_three, stdGumbelScore3, gumbelScoreMu, gumbelScoreSigma,
      gumbelScoreXi, div_eq_inv_mul]
    ring
  rw [hsq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  have hinner : ∀ i : Fin 3,
      ∫ x, ∑ j : Fin 3, (v i * v j * (![σ⁻¹, σ⁻¹, 1] i) * (![σ⁻¹, σ⁻¹, 1] j)) *
        (stdGumbelScore3 i ((x - μ) / σ) * stdGumbelScore3 j ((x - μ) / σ))
        ∂(gevLocScaleCDF 0 μ hσ).measure =
      ∑ j : Fin 3, (v i * v j * (![σ⁻¹, σ⁻¹, 1] i) * (![σ⁻¹, σ⁻¹, 1] j)) *
        ∫ z, stdGumbelScore3 i z * stdGumbelScore3 j z ∂(gevLocScaleCDF 0 0 one_pos).measure := by
    intro i
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hterm i j]
  simp_rw [hinner]
  simp only [gevFisherInfoZero, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The full `3 × 3` GEV Fisher information matrix at `ξ = 0` is positive definite** for `σ > 0`.
Proved by checking linear independence of `(1 - e^{-z}, -1 + z(1 - e^{-z}), -z + z²(1 - e^{-z})/2)`
via derivatives at `z = 0`, without evaluating `ζ(3)`. -/
theorem posDef_gevFisherInfoZero (hσ : 0 < σ) : (gevFisherInfoZero σ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [gevFisherInfoZero, star_trivial, Matrix.of_apply]
    have : (fun z => stdGumbelScore3 j z * stdGumbelScore3 i z) =
        fun z => stdGumbelScore3 i z * stdGumbelScore3 j z := funext fun z => mul_comm _ _
    rw [this]; ring
  · rw [star_trivial, ← integral_lin_gumbelScore3_sq (μ := 0) hσ v]
    set f : ℝ → ℝ := fun z =>
      (v 0 / σ) * (1 - exp (-z)) + (v 1 / σ) * (-1 + z * (1 - exp (-z))) +
        v 2 * (-z + z ^ 2 * (1 - exp (-z)) / 2)
    have hf_eq : ∀ x, v 0 * gumbelScoreMu 0 σ x + v 1 * gumbelScoreSigma 0 σ x +
        v 2 * gumbelScoreXi 0 σ x = f (x / σ) := by
      intro x; simp only [f, gumbelScoreMu, gumbelScoreSigma, gumbelScoreXi, sub_zero]; ring
    have hf_cont : Continuous f := by unfold f; fun_prop
    have hint_sq : Integrable (fun x => (f (x / σ)) ^ 2) (gevLocScaleCDF 0 0 hσ).measure := by
      have := (memLp_lin_gumbelScore3 (μ := 0) hσ (v 0) (v 1) (v 2)).integrable_sq
      simpa only [Real.norm_eq_abs, sq_abs, hf_eq] using this
    have hnn : 0 ≤ ∫ x, (f (x / σ)) ^ 2 ∂(gevLocScaleCDF 0 0 hσ).measure :=
      integral_nonneg fun x => sq_nonneg _
    simp only [hf_eq]
    refine lt_of_le_of_ne hnn (Ne.symm fun h0 => hv ?_)
    -- `∫ e^{-t} (f (-log t))² dt = 0` on `(0, ∞)` implies `f (-log t) = 0` for all `t > 0`,
    -- hence `f z = 0` for all `z ∈ ℝ`.
    have hint_t : ∫ t in Ioi (0 : ℝ), exp (-t) * (f (-log t)) ^ 2 = 0 := by
      have h1 := integral_gevLocScaleCDF (ξ := 0) (μ := 0) hσ (h := fun x => (f (x / σ)) ^ 2)
        ((hf_cont.comp (continuous_id.div_const σ)).pow 2).measurable
      rw [h0] at h1
      have hcongr : ∀ t : ℝ, exp (-t) * (f ((0 + σ * gevTransform 0 t) / σ)) ^ 2 =
          exp (-t) * (f (-log t)) ^ 2 := by
        intro t; congr 3; simp [gevTransform]; field_simp [hσ.ne']
      simpa only [hcongr] using h1.symm
    have hint_t_int : IntegrableOn (fun t : ℝ => exp (-t) * (f (-log t)) ^ 2) (Ioi 0) volume := by
      have hm_sq : Measurable (fun x : ℝ => (f (x / σ)) ^ 2) :=
        (hf_cont.comp (continuous_id.div_const σ)).measurable.pow_const 2
      rw [integrable_gevLocScaleCDF_iff (ξ := 0) (μ := 0) hσ hm_sq] at hint_sq
      refine hint_sq.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp [gevTransform]; field_simp [hσ.ne']
    have hae_zero : (fun t : ℝ => exp (-t) * (f (-log t)) ^ 2) =ᵐ[volume.restrict (Ioi 0)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun t => by positivity) hint_t_int).1 hint_t
    have hcont_t : ContinuousOn (fun t : ℝ => exp (-t) * (f (-log t)) ^ 2) (Ioi 0) := by
      intro t ht
      have hc : ContinuousAt (fun u : ℝ => exp (-u) * (f (-log u)) ^ 2) t :=
        (continuous_exp.comp continuous_neg).continuousAt.mul
          ((hf_cont.continuousAt.comp (continuousAt_log (ne_of_gt ht)).neg).pow 2)
      exact hc.continuousWithinAt
    have hf_zero : ∀ z : ℝ, f z = 0 := by
      intro z
      have htz : exp (-z) ∈ Ioi (0 : ℝ) := exp_pos _
      have heq_t : exp (-(exp (-z))) * (f (-log (exp (-z)))) ^ 2 = 0 := by
        have hopen : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
        have hdense : ∀ U, IsOpen U → (U ∩ Ioi (0 : ℝ)).Nonempty →
            ∃ u ∈ U ∩ Ioi (0 : ℝ), exp (-u) * (f (-log u)) ^ 2 = 0 := by
          intro U hU hne
          have hpos : 0 < volume.restrict (Ioi (0 : ℝ)) U := by
            rw [Measure.restrict_apply hU.measurableSet]
            exact (hU.inter hopen).measure_pos volume hne
          by_contra hnone
          push Not at hnone
          have hsub : U ∩ Ioi (0 : ℝ) ⊆ {u | exp (-u) * (f (-log u)) ^ 2 ≠ 0} :=
            fun u hu => hnone u hu
          have hm0 : volume.restrict (Ioi (0 : ℝ)) {u | exp (-u) * (f (-log u)) ^ 2 ≠ 0} = 0 :=
            MeasureTheory.ae_iff.1 hae_zero
          have hle : volume.restrict (Ioi (0 : ℝ)) U ≤
              volume.restrict (Ioi (0 : ℝ)) {u | exp (-u) * (f (-log u)) ^ 2 ≠ 0} := by
            rw [Measure.restrict_apply hU.measurableSet, Measure.restrict_apply' measurableSet_Ioi]
            exact measure_mono fun u hu => ⟨hsub hu, hu.2⟩
          exact hpos.ne' (le_antisymm (hle.trans hm0.le) bot_le)
        by_contra hne0
        have hpos0 : 0 < exp (-(exp (-z))) * (f (-log (exp (-z)))) ^ 2 :=
          lt_of_le_of_ne (by positivity) (Ne.symm hne0)
        have hnhds := (hcont_t (exp (-z)) htz).eventually (lt_mem_nhds hpos0)
        rw [eventually_nhdsWithin_iff] at hnhds
        obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.1 hnhds
        obtain ⟨u, ⟨huU, huI⟩, hu0⟩ := hdense U hUopen ⟨exp (-z), hUmem, htz⟩
        exact (hUsub huU huI).ne' hu0
      have hsq0 : (f (-log (exp (-z)))) ^ 2 = 0 :=
        (mul_eq_zero.1 heq_t).resolve_left (exp_pos _).ne'
      simpa [log_exp] using sq_eq_zero_iff.1 hsq0
    -- Now extract `v 1 = 0`, `v 0 = 0`, `v 2 = 0` from `f(0) = 0`, `f'(0) = 0`, `f(-1) = 0`!
    have h0' := hf_zero 0
    simp only [f, neg_zero, exp_zero, sub_self, mul_zero, add_zero, zero_pow two_ne_zero, zero_div] at h0'
    have hv1 : v 1 = 0 := by
      have : v 1 / σ = 0 := by linarith
      exact (div_eq_zero_iff.1 this).resolve_right hσ.ne'
    have hf1 : ∀ z, f z = (v 0 / σ) * (1 - exp (-z)) + v 2 * (-z + z ^ 2 * (1 - exp (-z)) / 2) := by
      intro z; simp [f, hv1]
    have hd1 : HasDerivAt f (v 0 / σ - v 2) 0 := by
      have he : HasDerivAt (fun z : ℝ => 1 - exp (-z)) 1 0 := by
        have h := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).neg.exp)
        exact h.congr_deriv (by simp)
      have hq : HasDerivAt (fun z : ℝ => z ^ 2 * (1 - exp (-z)) / 2) 0 0 := by
        have hsq : HasDerivAt (fun z : ℝ => z ^ 2) 0 0 := by
          simpa using (hasDerivAt_pow 2 (0 : ℝ))
        have h := (hsq.mul he).div_const 2
        exact h.congr_deriv (by simp)
      have h3 := (he.const_mul (v 0 / σ)).add (((hasDerivAt_id (0 : ℝ)).neg.add hq).const_mul (v 2))
      refine (h3.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv (by ring)
      exact hf1 z
    have hderiv0 : v 0 / σ - v 2 = 0 := by
      have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const 0 0
      exact hd1.unique (hconst.congr_of_eventuallyEq (Eventually.of_forall fun z => hf_zero z))
    have hv2_eq : v 2 = v 0 / σ := by linarith
    -- Now `f(z) = (v 0 / σ) * (1 - exp (-z) - z + z² (1 - exp (-z)) / 2) = 0` for all `z`.
    -- Evaluate at `z = 1`: `1 - e^{-1} - 1 + (1 - e^{-1})/2 = (1 - 3 e^{-1})/2 ≠ 0` since `e > 2` (in fact `e < 3`? Wait: `e ≈ 2.718 < 3`, so `1 - 3 e^{-1} = (e - 3)/e < 0`!).
    -- Even better: evaluate at `z = -1`! At `z = -1`:
    -- `1 - e - (-1) + (1 - e)/2 = 2 - e + (1 - e)/2 = (5 - 3 e)/2 < 0` since `e > 2` (`add_one_lt_exp`)!
    have hm1 := hf_zero (-1)
    rw [hf1 (-1), hv2_eq] at hm1
    have hne : (1 - exp (-(-1 : ℝ))) + (-(-1 : ℝ) + (-1 : ℝ) ^ 2 * (1 - exp (-(-1 : ℝ))) / 2) ≠ 0 := by
      have he2 : (2 : ℝ) < exp 1 := by linarith [add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
      simp only [neg_neg, even_two, Even.neg_pow, one_pow, one_mul]
      linarith
    have hfac : (v 0 / σ) * ((1 - exp (-(-1 : ℝ))) +
        (-(-1 : ℝ) + (-1 : ℝ) ^ 2 * (1 - exp (-(-1 : ℝ))) / 2)) = 0 := by linarith
    have hv0 : v 0 = 0 := by
      have := (mul_eq_zero.1 hfac).resolve_right hne
      exact (div_eq_zero_iff.1 this).resolve_right hσ.ne'
    have hv2 : v 2 = 0 := by rw [hv2_eq, hv0, zero_div]
    ext i; fin_cases i <;> simp [hv0, hv1, hv2]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- **The full trivariate GEV score CLT at `ξ = 0`**: for iid `GEV(0, μ, σ)` observations,
`n^{-1/2} ∑_{i<n} (∂_μ ℓ, ∂_σ ℓ, ∂_ξ ℓ)(Xᵢ) ⇒ N(0, gevFisherInfoZero σ)`. -/
theorem tendstoInDistribution_gumbelScoreVec3 (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ hσ).measure P) (hind : iIndepFun X P)
    {Z : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hZ : HasLaw Z (multivariateGaussian 0 (gevFisherInfoZero σ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gumbelScoreVec3 μ σ (X i ω))
      atTop Z (fun _ => P) P' := by
  refine TendstoInDistribution.of_inner hZ.aemeasurable (fun n => ?_) fun v => ?_
  · have := measurable_gumbelScoreVec3 μ σ
    have := fun i => (hX i).aemeasurable
    fun_prop
  set f : ℝ → ℝ := fun x => v 0 * gumbelScoreMu μ σ x + v 1 * gumbelScoreSigma μ σ x +
    v 2 * gumbelScoreXi μ σ x
  have hf : Measurable f := by
    have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreSigma μ σ
    have := measurable_gumbelScoreXi μ σ
    simp only [f]; fun_prop
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_lin_gumbelScore3 hσ _ _ _
  have hint : ∀ g : ℝ → ℝ, Measurable g →
      P[g ∘ X 0] = ∫ x, g x ∂(gevLocScaleCDF 0 μ hσ).measure :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    exact integral_lin_gumbelScore (μ := μ) hσ (v 0) (v 1) (v 2)
  have hvar : Var[Y 0; P] = v ⬝ᵥ gevFisherInfoZero σ *ᵥ v := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this ⊢
    rw [this, integral_lin_gumbelScore3_sq hσ]
  have hZt : HasLaw (fun ω => ⟪Z ω, v⟫) (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by
    rw [hvar]
    exact hasLaw_inner_multivariateGaussian (posDef_gevFisherInfoZero hσ).posSemidef hZ v
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp [Y, f, gumbelScoreVec3, PiLp.inner_apply, Fin.sum_univ_three]

end GEVZeroScore3

end ExtremeValueTheory
