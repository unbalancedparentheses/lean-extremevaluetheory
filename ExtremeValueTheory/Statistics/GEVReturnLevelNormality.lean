/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLENormality
import ExtremeValueTheory.Statistics.ConfidenceIntervals

/-!
# The maximum likelihood GEV return level is asymptotically normal

`ExtremeValueTheory.tendstoInDistribution_gevReturnLevel` is the delta method: it assumes that the
parameter estimators are asymptotically normal. For the maximum likelihood estimator this is now a
theorem (`tendstoInDistribution_gevMLE`), so the hypothesis disappears.

## Main results

Let `K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, μ₀, σ₀)`, `ξ₀ > -1/2`, `ξ₀ ≠ 0`, in its
interior, let `X₀, X₁, …` be iid with the GEV law of parameter `θ₀`, and let `θ̂ₙ` be measurable
maximizers of the log-likelihood over `K`, `m > 1`.

* `tendstoInDistribution_gevMLEReturnLevel`: **the plug-in `m`-block return level** satisfies
  `√n (ẑ_m - z_m) ⇒ N(0, ∇zᵀ V ∇z)`, with `V = gevMLECov ξ₀ σ₀` the inverse Fisher information, and
  `∇z = gevReturnLevelGrad ξ₀ σ₀ m` ([Coles, §3.3.3]).
* `gevReturnLevelVar`, `gevReturnLevelVar_pos`: the asymptotic variance, which is positive.
* `exists_gevMLE_returnLevel_tendstoInDistribution`: the same for a maximum likelihood estimator
  which exists by `exists_measurable_gevMLE`, so that the theorem is not vacuous.
* `tendstoInDistribution_gevLocalMLEReturnLevel`: the same for consistent local maximizers.
* `tendsto_measure_mem_gevMLEReturnLevelInterval`: **the coverage of the delta-method confidence
  interval** `ẑ_m ± z ŝₙ/√n` tends to `N(0, 1)([-z, z])`, for any consistent standard error `ŝₙ`.
* `continuousAt_gevFisherInfo`, `continuousAt_gevMLECov`, `continuousAt_gevReturnLevelVar`:
  continuity of the Fisher information, asymptotic covariance and return-level variance on
  `ξ > -1/2`, `ξ ≠ 0`, `σ > 0` (`m > 1`).
* `tendsto_measure_mem_gevMLEReturnLevelPlugInInterval`: **the computable delta-method confidence
  interval** with plug-in standard error `ŝₙ = √(gevReturnLevelVar ξ̂ₙ σ̂ₙ m)` has asymptotic
  coverage `N(0, 1)([-z, z])`, with no standard-error hypothesis.
* `exists_gevMLE_returnLevelPlugInInterval_tendsto`: the same together with the existence of a
  measurable maximum likelihood estimator.

## Not covered

* `ξ₀ = 0`: see `ExtremeValueTheory.Statistics.GEVMLENormality`.
* Coles' profile likelihood intervals.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §3.3.3.
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ExtremeValueTheory

variable {ξ₀ μ₀ σ₀ m : ℝ} {Ω Ω'' : Type*} {mΩ : MeasurableSpace Ω} {mΩ'' : MeasurableSpace Ω''}
  {P : Measure Ω} [IsProbabilityMeasure P] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
  {X : ℕ → Ω → ℝ}

/-- The asymptotic variance `∇zᵀ V ∇z` of the maximum likelihood `m`-block return level, with
`V = gevMLECov ξ σ` the inverse Fisher information and `∇z = gevReturnLevelGrad ξ σ m`. -/
noncomputable def gevReturnLevelVar (ξ σ m : ℝ) : ℝ :=
  gevReturnLevelGrad ξ σ m ⬝ᵥ gevMLECov ξ σ *ᵥ gevReturnLevelGrad ξ σ m

/-- The asymptotic covariance of the GEV maximum likelihood estimator is positive definite. -/
theorem posDef_gevMLECov (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀) :
    (gevMLECov ξ₀ σ₀).PosDef :=
  (posDef_inv_gevFisherInfo hσ₀ hξ₀0 hξ₀).submatrix (by decide)

/-- **The asymptotic variance of the maximum likelihood return level is positive**: the
`μ` component of the gradient is `1`, and the covariance is positive definite. -/
theorem gevReturnLevelVar_pos (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀) (m : ℝ) :
    0 < gevReturnLevelVar ξ₀ σ₀ m := by
  have hne : (fun i => gevReturnLevelGrad ξ₀ σ₀ m i) ≠ 0 := fun h => by
    have := congrFun h 1
    simp [gevReturnLevelGrad] at this
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 (posDef_gevMLECov hσ₀ hξ₀0 hξ₀)).2 hne
  simpa [gevReturnLevelVar] using this

/-- **Asymptotic normality of the maximum likelihood GEV return level for consistent local
maximizers** ([Coles, §3.3.3]; [Smith 1985]), `ξ₀ > -1/2`, `ξ₀ ≠ 0`, `m > 1`. -/
theorem tendstoInDistribution_gevLocalMLEReturnLevel (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0)
    (hσ₀ : 0 < σ₀) (hm : 1 < m) (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω))
    {W : Ω'' → ℝ} (hW : HasLaw W (gaussianReal 0 (gevReturnLevelVar ξ₀ σ₀ m).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m - gevReturnLevel ξ₀ μ₀ σ₀ m))
      atTop W (fun _ => P) P'' := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevMLECov ξ₀ σ₀))
      (multivariateGaussian 0 (gevMLECov ξ₀ σ₀)) := HasLaw.id
  exact tendstoInDistribution_gevReturnLevel hξ₀0 hm hθm (posSemidef_gevMLECov hσ₀ hξ₀0 hξ₀)
    (tendstoInDistribution_gevLocalMLE hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm hZ) hZ hW

/-- **Asymptotic normality of the maximum likelihood GEV return level** ([Coles, §3.3.3];
[Smith 1985]), unconditional form of `tendstoInDistribution_gevReturnLevel`. Let
`K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, μ₀, σ₀)`, `ξ₀ > -1/2`, `ξ₀ ≠ 0`, in its interior,
let `X₀, X₁, …` be iid with the GEV law of parameter `θ₀`, let `θ̂ₙ` be (almost everywhere)
measurable maximizers of the log-likelihood over `K`, and `m > 1`. Then

  `√n (ẑ_m - z_m) ⇒ N(0, ∇z_mᵀ V ∇z_m)`,

where `ẑ_m = gevReturnLevel ξ̂ₙ μ̂ₙ σ̂ₙ m`, `V = gevMLECov ξ₀ σ₀` is the inverse Fisher information
and `∇z_m = gevReturnLevelGrad ξ₀ σ₀ m`. -/
theorem tendstoInDistribution_gevMLEReturnLevel {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hm : 1 < m)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) K (θh n ω))
    {W : Ω'' → ℝ} (hW : HasLaw W (gaussianReal 0 (gevReturnLevelVar ξ₀ σ₀ m).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m - gevReturnLevel ξ₀ μ₀ σ₀ m))
      atTop W (fun _ => P) P'' := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevMLECov ξ₀ σ₀))
      (multivariateGaussian 0 (gevMLECov ξ₀ σ₀)) := HasLaw.id
  exact tendstoInDistribution_gevReturnLevel hξ₀0 hm hθm (posSemidef_gevMLECov hσ₀ hξ₀0 hξ₀)
    (tendstoInDistribution_gevMLE hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind hθm hθK hmax hZ) hZ hW

/-- **The maximum likelihood GEV return level, with the existence of the estimator**: there is a
measurable maximum likelihood estimator over `K`, and its plug-in return level satisfies
`√n (ẑ_m - z_m) ⇒ N(0, ∇z_mᵀ V ∇z_m)`. -/
theorem exists_gevMLE_returnLevel_tendstoInDistribution {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hm : 1 < m)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {W : Ω'' → ℝ} (hW : HasLaw W (gaussianReal 0 (gevReturnLevelVar ξ₀ σ₀ m).toNNReal) P'') :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) K (g n x)) ∧
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
        (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
          (g n (fun i : Fin n => X i ω)).2.2 m - gevReturnLevel ξ₀ μ₀ σ₀ m))
        atTop W (fun _ => P) P'' := by
  choose g hgm hg using exists_measurable_gevMLE hK hKS ⟨_, interior_subset hθ₀⟩
  refine ⟨g, hgm, hg, ?_⟩
  exact tendstoInDistribution_gevMLEReturnLevel hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hm hX hind
    (θh := fun n ω => g n (fun i : Fin n => X i ω))
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2) hW

/-- **Coverage of the delta-method confidence interval for the maximum likelihood GEV return
level** ([Coles, §3.3.3]), for `ξ₀ > -1/2`, `ξ₀ ≠ 0`: if `θ̂ₙ` are measurable maximizers over `K`
and `ŝₙ → s = √(∇zᵀ V ∇z)` in probability, then the coverage probability of
`[ẑ_m - z ŝₙ/√n, ẑ_m + z ŝₙ/√n]` converges to `N(0, 1)([-z, z])`. The consistency of the standard
error `ŝₙ` is a hypothesis. -/
theorem tendsto_measure_mem_gevMLEReturnLevelInterval {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hm : 1 < m)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) K (θh n ω))
    {S : ℕ → Ω → ℝ} (hS : TendstoInMeasure P S atTop (fun _ => √(gevReturnLevelVar ξ₀ σ₀ m)))
    (hSm : ∀ n, AEMeasurable (S n) P) (z : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gevReturnLevel ξ₀ μ₀ σ₀ m ∈ Icc
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m - z * S n ω / √(n : ℝ))
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m + z * S n ω / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevMLECov ξ₀ σ₀))
      (multivariateGaussian 0 (gevMLECov ξ₀ σ₀)) := HasLaw.id
  have hpos := gevReturnLevelVar_pos hσ₀ hξ₀0 hξ₀ m
  exact tendsto_measure_mem_gevReturnLevelInterval hξ₀0 hm hθm
    (posSemidef_gevMLECov hσ₀ hξ₀0 hξ₀)
    (tendstoInDistribution_gevMLE hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind hθm hθK hmax hZ) hZ
    (sqrt_pos.2 hpos) (sq_sqrt hpos.le) hS hSm z

/-! ### Continuity of the Fisher information and computable plug-in confidence intervals -/

section PlugInInterval

/-- On `(0, ∞)`, the real derivative of `Real.Gamma` agrees with the real part of the complex
derivative of `Complex.Gamma`. -/
lemma deriv_realGamma_eq_re_deriv_complexGamma {s : ℝ} (hs : 0 < s) :
    deriv Real.Gamma s = (deriv Complex.Gamma (s : ℂ)).re := by
  have hre : (0 : ℝ) < (s : ℂ).re := by simpa using hs
  have hC : HasDerivAt (fun x : ℝ => Complex.Gamma (x : ℂ)) (deriv Complex.Gamma (s : ℂ)) s := by
    have hG : HasDerivAt Complex.Gamma (deriv Complex.Gamma (s : ℂ)) (s : ℂ) :=
      (Complex.analyticAt_Gamma_of_re_pos hre).differentiableAt.hasDerivAt
    simpa using hG.comp_ofReal
  have hR : HasDerivAt (fun x : ℝ => ((Real.Gamma x : ℝ) : ℂ))
      (((deriv Real.Gamma s : ℝ) : ℂ)) s :=
    (Real.hasDerivAt_Gamma_of_pos hs).differentiableAt.hasDerivAt.ofReal_comp
  have hR' : HasDerivAt (fun x : ℝ => Complex.Gamma (x : ℂ))
      (((deriv Real.Gamma s : ℝ) : ℂ)) s := by
    refine hR.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    exact Complex.Gamma_ofReal x
  have heq : (((deriv Real.Gamma s : ℝ) : ℂ)) = deriv Complex.Gamma (s : ℂ) := hR'.unique hC
  simpa using congrArg Complex.re heq

/-- `deriv Real.Gamma` is continuous on `(0, ∞)`. -/
lemma continuousAt_deriv_realGamma {s : ℝ} (hs : 0 < s) : ContinuousAt (deriv Real.Gamma) s := by
  have hre : (0 : ℝ) < (s : ℂ).re := by simpa using hs
  have hc : ContinuousAt (fun x : ℝ => (deriv Complex.Gamma (x : ℂ)).re) s :=
    Complex.continuous_re.continuousAt.comp
      ((Complex.analyticAt_Gamma_of_re_pos hre).deriv.continuousAt.comp
        Complex.continuous_ofReal.continuousAt)
  refine hc.congr ?_
  filter_upwards [lt_mem_nhds hs] with x hx
  exact (deriv_realGamma_eq_re_deriv_complexGamma hx).symm

/-- `realDigamma` is continuous on `(0, ∞)`. -/
theorem continuousAt_realDigamma {s : ℝ} (hs : 0 < s) : ContinuousAt realDigamma s :=
  (continuousAt_deriv_realGamma hs).div (Real.hasDerivAt_Gamma_of_pos hs).continuousAt
    (Gamma_pos_of_pos hs).ne'

/-- `gevInfoP` is continuous on `(-1/2, ∞)`. -/
theorem continuousAt_gevInfoP {ξ : ℝ} (hξ : -1 / 2 < ξ) : ContinuousAt gevInfoP ξ := by
  unfold gevInfoP
  have hG : ContinuousAt (fun t : ℝ => Gamma (1 + 2 * t)) ξ :=
    (Real.hasDerivAt_Gamma_of_pos (by linarith)).continuousAt.comp (by fun_prop)
  exact ((continuousAt_const.add continuousAt_id).pow 2).mul hG

/-- `gevInfoQ` is continuous on `(-1/2, ∞) \ {0}`. -/
theorem continuousAt_gevInfoQ {ξ : ℝ} (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) :
    ContinuousAt gevInfoQ ξ := by
  unfold gevInfoQ
  have hG : ContinuousAt (fun t : ℝ => Gamma (2 + t)) ξ :=
    (Real.hasDerivAt_Gamma_of_pos (by linarith)).continuousAt.comp (by fun_prop)
  have hD : ContinuousAt (fun t : ℝ => realDigamma (1 + t)) ξ :=
    (continuousAt_realDigamma (by linarith)).comp (by fun_prop)
  exact hG.mul (hD.add ((continuousAt_const.add continuousAt_id).div continuousAt_id hξ0))

/-- **Continuity of the GEV Fisher information** on `ξ > -1/2`, `ξ ≠ 0`, `σ > 0`. -/
theorem continuousAt_gevFisherInfo {ξ σ : ℝ} (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ) :
    ContinuousAt (fun p : ℝ × ℝ => gevFisherInfo p.1 p.2) (ξ, σ) := by
  change ContinuousAt (fun p : ℝ × ℝ => fun i j : Fin 3 => gevFisherInfo p.1 p.2 i j) (ξ, σ)
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  have hP : ContinuousAt (fun p : ℝ × ℝ => gevInfoP p.1) (ξ, σ) :=
    ContinuousAt.comp (g := gevInfoP) (continuousAt_gevInfoP hξ) continuousAt_fst
  have hQ : ContinuousAt (fun p : ℝ × ℝ => gevInfoQ p.1) (ξ, σ) :=
    ContinuousAt.comp (g := gevInfoQ) (continuousAt_gevInfoQ hξ hξ0) continuousAt_fst
  have hG : ContinuousAt (fun p : ℝ × ℝ => Gamma (2 + p.1)) (ξ, σ) :=
    ContinuousAt.comp (g := Gamma) (Real.hasDerivAt_Gamma_of_pos (by linarith)).continuousAt
      (continuousAt_const.add continuousAt_fst)
  have h1 : ContinuousAt (fun p : ℝ × ℝ => p.1) (ξ, σ) := continuousAt_fst
  have h2 : ContinuousAt (fun p : ℝ × ℝ => p.2) (ξ, σ) := continuousAt_snd
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  have hξ2 : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ0
  fin_cases i <;> fin_cases j <;> simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one]
  · exact hP.div (h2.pow 2) hσ2
  · exact (hG.sub hP).div (h1.mul (h2.pow 2)) (mul_ne_zero hξ0 hσ2)
  · exact ((hQ.sub (hP.div h1 hξ0)).neg).div (h2.mul h1) (mul_ne_zero hσ.ne' hξ0)
  · exact (hG.sub hP).div (h1.mul (h2.pow 2)) (mul_ne_zero hξ0 hσ2)
  · exact (((continuousAt_const.sub (continuousAt_const.mul hG)).add hP)).div
      ((h1.pow 2).mul (h2.pow 2)) (mul_ne_zero hξ2 hσ2)
  · exact (((((continuousAt_const.sub continuousAt_const).add
      ((continuousAt_const.sub hG).div h1 hξ0)).sub hQ).add (hP.div h1 hξ0)).neg).div
      (h2.mul (h1.pow 2)) (mul_ne_zero hσ.ne' hξ2)
  · exact ((hQ.sub (hP.div h1 hξ0)).neg).div (h2.mul h1) (mul_ne_zero hσ.ne' hξ0)
  · exact (((((continuousAt_const.sub continuousAt_const).add
      ((continuousAt_const.sub hG).div h1 hξ0)).sub hQ).add (hP.div h1 hξ0)).neg).div
      (h2.mul (h1.pow 2)) (mul_ne_zero hσ.ne' hξ2)
  · exact (((continuousAt_const.add (((continuousAt_const.sub continuousAt_const).add
      (continuousAt_const.div h1 hξ0)).pow 2)).sub
      ((continuousAt_const.mul hQ).div h1 hξ0)).add
      (hP.div (h1.pow 2) hξ2)).div (h1.pow 2) hξ2

/-- Matrix inversion on `Matrix (Fin 3) (Fin 3) ℝ` is continuous at every invertible matrix. -/
private lemma continuousAt_matrix_inv {A : Matrix (Fin 3) (Fin 3) ℝ} (hdet : A.det ≠ 0) :
    ContinuousAt (fun M : Matrix (Fin 3) (Fin 3) ℝ => M⁻¹) A := by
  have heq : (fun M : Matrix (Fin 3) (Fin 3) ℝ => M⁻¹) =
      fun M => (M.det)⁻¹ • M.adjugate := by
    funext M
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [heq]
  exact ((continuous_id.matrix_det.continuousAt).inv₀ hdet).smul
    continuous_id.matrix_adjugate.continuousAt

/-- **Continuity of the GEV asymptotic covariance** `gevMLECov` on `ξ > -1/2`, `ξ ≠ 0`, `σ > 0`. -/
theorem continuousAt_gevMLECov {ξ σ : ℝ} (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ) :
    ContinuousAt (fun p : ℝ × ℝ => gevMLECov p.1 p.2) (ξ, σ) := by
  have hdet : (gevFisherInfo ξ σ).det ≠ 0 := (posDef_gevFisherInfo hσ hξ0 hξ).det_pos.ne'
  have hinv : ContinuousAt (fun p : ℝ × ℝ => (gevFisherInfo p.1 p.2)⁻¹) (ξ, σ) :=
    ContinuousAt.comp (g := fun M : Matrix (Fin 3) (Fin 3) ℝ => M⁻¹)
      (continuousAt_matrix_inv hdet) (continuousAt_gevFisherInfo hξ hξ0 hσ)
  unfold gevMLECov
  change ContinuousAt
    (fun p : ℝ × ℝ => fun i j : Fin 3 => (gevFisherInfo p.1 p.2)⁻¹ (![2, 0, 1] i) (![2, 0, 1] j))
    (ξ, σ)
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  exact ContinuousAt.comp (g := fun M : Matrix (Fin 3) (Fin 3) ℝ => M (![2, 0, 1] i) (![2, 0, 1] j))
    ((continuous_apply (![2, 0, 1] j)).comp (continuous_apply (![2, 0, 1] i))).continuousAt hinv

/-- **Continuity of the GEV return-level asymptotic variance** `gevReturnLevelVar` on
`ξ > -1/2`, `ξ ≠ 0`, `σ > 0`, `m > 1`. -/
theorem continuousAt_gevReturnLevelVar {ξ σ m : ℝ} (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hm : 1 < m) : ContinuousAt (fun p : ℝ × ℝ => gevReturnLevelVar p.1 p.2 m) (ξ, σ) := by
  have hx : 0 < (-log (1 - 1 / m))⁻¹ := inv_pos.2 (neg_log_one_sub_inv_pos hm)
  have hcov := continuousAt_gevMLECov hξ hξ0 hσ
  have hg : ∀ i : Fin 3, ContinuousAt (fun p : ℝ × ℝ => gevReturnLevelGrad p.1 p.2 m i) (ξ, σ) := by
    intro i
    fin_cases i
    · simp only [gevReturnLevelGrad]
      exact continuousAt_snd.mul (ContinuousAt.comp
        (g := fun ρ => boxCoxShapeDeriv ρ (-log (1 - 1 / m))⁻¹)
        (continuousAt_boxCoxShapeDeriv hξ0 hx) continuousAt_fst)
    · simp only [gevReturnLevelGrad]
      exact continuousAt_const
    · have hret : (fun p : ℝ × ℝ => gevReturnLevelGrad p.1 p.2 m ⟨2, by decide⟩) =
          fun p => boxCox p.1 (-log (1 - 1 / m))⁻¹ := by
        funext p
        simp [gevReturnLevelGrad, returnLevel_eq_boxCox _ hm]
      change ContinuousAt (fun p : ℝ × ℝ => gevReturnLevelGrad p.1 p.2 m ⟨2, by decide⟩) (ξ, σ)
      rw [hret]
      exact ((continuous_boxCox_shape hx).comp continuous_fst).continuousAt
  have hmat : ∀ i j : Fin 3, ContinuousAt (fun p : ℝ × ℝ => gevMLECov p.1 p.2 i j) (ξ, σ) :=
    fun i j => ContinuousAt.comp (g := fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j)
      ((continuous_apply j).comp (continuous_apply i)).continuousAt hcov
  have hrow : ∀ i : Fin 3,
      ContinuousAt (fun p : ℝ × ℝ => ∑ j : Fin 3, gevMLECov p.1 p.2 i j *
        gevReturnLevelGrad p.1 p.2 m j) (ξ, σ) := fun i => by
    simp only [Fin.sum_univ_three]
    exact (((hmat i 0).mul (hg 0)).add ((hmat i 1).mul (hg 1))).add ((hmat i 2).mul (hg 2))
  have hsum := (((hg 0).mul (hrow 0)).add ((hg 1).mul (hrow 1))).add ((hg 2).mul (hrow 2))
  convert hsum using 1
  funext p
  simp [gevReturnLevelVar, dotProduct, Matrix.mulVec, Fin.sum_univ_three]

private lemma measurable_realGamma : Measurable Real.Gamma := by
  set S : Set ℝ := (Set.range fun m : ℕ => -(m : ℝ))ᶜ with hS_def
  have hSm : MeasurableSet S := (Set.countable_range _).measurableSet.compl
  have hcont : ContinuousOn Real.Gamma S := fun x hx =>
    (Real.differentiableAt_Gamma fun m hm => hx ⟨m, hm.symm⟩).continuousAt.continuousWithinAt
  have hind : S.indicator Real.Gamma = Real.Gamma := by
    funext x
    by_cases hx : x ∈ S
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx]
      simp only [hS_def, Set.mem_compl_iff, not_not, Set.mem_range] at hx
      obtain ⟨m, rfl⟩ := hx
      exact (Real.Gamma_neg_nat_eq_zero m).symm
  rw [← hind]
  exact (measurable_of_restrict_of_restrict_compl hSm
    (by
      have : S.domRestrict (S.indicator Real.Gamma) = S.domRestrict Real.Gamma := by
        funext ⟨x, hx⟩; exact Set.indicator_of_mem hx _
      rw [this]
      exact (continuousOn_iff_continuous_domRestrict.1 hcont).measurable)
    (by
      have : Sᶜ.domRestrict (S.indicator Real.Gamma) = fun _ => (0 : ℝ) := by
        funext ⟨x, hx⟩; exact Set.indicator_of_notMem hx _
      rw [this]
      exact measurable_const))

lemma measurable_realDigamma : Measurable realDigamma :=
  (measurable_deriv Real.Gamma).div measurable_realGamma

lemma measurable_gevInfoP : Measurable gevInfoP := by
  unfold gevInfoP
  exact ((measurable_const.add measurable_id).pow_const 2).mul
    (measurable_realGamma.comp (measurable_const.add (measurable_const.mul measurable_id)))

lemma measurable_gevInfoQ : Measurable gevInfoQ := by
  unfold gevInfoQ
  exact (measurable_realGamma.comp (measurable_const.add measurable_id)).mul
    ((measurable_realDigamma.comp (measurable_const.add measurable_id)).add
      ((measurable_const.add measurable_id).div measurable_id))

lemma measurable_gevFisherInfo : Measurable fun p : ℝ × ℝ => gevFisherInfo p.1 p.2 := by
  change Measurable (fun p : ℝ × ℝ => fun i j : Fin 3 => gevFisherInfo p.1 p.2 i j)
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  have hP : Measurable fun p : ℝ × ℝ => gevInfoP p.1 := measurable_gevInfoP.comp measurable_fst
  have hQ : Measurable fun p : ℝ × ℝ => gevInfoQ p.1 := measurable_gevInfoQ.comp measurable_fst
  have hG : Measurable fun p : ℝ × ℝ => Gamma (2 + p.1) :=
    measurable_realGamma.comp (measurable_const.add measurable_fst)
  fin_cases i <;> fin_cases j <;> simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one] <;> fun_prop

lemma measurable_gevMLECov : Measurable fun p : ℝ × ℝ => gevMLECov p.1 p.2 := by
  have hinv : Measurable fun M : Matrix (Fin 3) (Fin 3) ℝ => M⁻¹ := by
    have heq : (fun M : Matrix (Fin 3) (Fin 3) ℝ => M⁻¹) =
        fun M => (M.det)⁻¹ • M.adjugate := by
      funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [heq]
    exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable
  change Measurable (fun p : ℝ × ℝ => fun i j : Fin 3 => gevMLECov p.1 p.2 i j)
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  exact (measurable_pi_apply (![2, 0, 1] j)).comp
    ((measurable_pi_apply (![2, 0, 1] i)).comp (hinv.comp measurable_gevFisherInfo))

lemma measurable_gevReturnLevelVar (m : ℝ) :
    Measurable fun p : ℝ × ℝ => gevReturnLevelVar p.1 p.2 m := by
  have hg : ∀ i : Fin 3, Measurable fun p : ℝ × ℝ => gevReturnLevelGrad p.1 p.2 m i := by
    intro i
    fin_cases i
    · simp only [gevReturnLevelGrad]
      exact measurable_snd.mul ((measurable_boxCoxShapeDeriv _).comp measurable_fst)
    · simp only [gevReturnLevelGrad]
      exact measurable_const
    · simp only [gevReturnLevelGrad, returnLevel, gevTransform]
      exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
        (((measurable_const.pow measurable_fst.neg).sub_const 1).div measurable_fst)
  have hmat : ∀ i j : Fin 3, Measurable fun p : ℝ × ℝ => gevMLECov p.1 p.2 i j :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_gevMLECov)
  unfold gevReturnLevelVar
  simp only [dotProduct, Matrix.mulVec]
  exact Finset.measurable_sum Finset.univ fun i _ =>
    (hg i).mul (Finset.measurable_sum Finset.univ fun j _ => (hmat i j).mul (hg j))

/-- **Computable asymptotic confidence interval for the maximum likelihood GEV return level**
([Coles, §3.3.3]), for `ξ₀ > -1/2`, `ξ₀ ≠ 0`, `σ₀ > 0`, `m > 1`: with the plug-in standard error
`ŝₙ = √(∇z(θ̂ₙ)ᵀ V(θ̂ₙ) ∇z(θ̂ₙ))` computed from the MLE alone, the coverage probability of
`[ẑ_m - z ŝₙ/√n, ẑ_m + z ŝₙ/√n]` converges to `N(0, 1)([-z, z])`. No standard-error consistency
hypothesis is assumed. -/
theorem tendsto_measure_mem_gevMLEReturnLevelPlugInInterval {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hm : 1 < m)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) K (θh n ω)) (z : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gevReturnLevel ξ₀ μ₀ σ₀ m ∈ Icc
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m -
        z * √(gevReturnLevelVar (θh n ω).1 (θh n ω).2.2 m) / √(n : ℝ))
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m +
        z * √(gevReturnLevelVar (θh n ω).1 (θh n ω).2.2 m) / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevMLECov ξ₀ σ₀))
      (multivariateGaussian 0 (gevMLECov ξ₀ σ₀)) := HasLaw.id
  have hθN := tendstoInDistribution_gevMLE hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind hθm hθK hmax hZ
  have hθ0 : TendstoInMeasure P (fun (n : ℕ) ω =>
      (!₂[(θh n ω).1 - ξ₀, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀] : EuclideanSpace ℝ (Fin 3)))
      atTop (fun _ => 0) :=
    TendstoInDistribution.tendstoInMeasure_of_smul (r := fun n : ℕ => √(n : ℝ)) hθN
      tendsto_sqrt_natCast_atTop
  set G : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => √(gevReturnLevelVar (ξ₀ + v 0) (σ₀ + v 2) m)
  have hG : ContinuousAt G 0 := by
    have haff : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) => (ξ₀ + v 0, σ₀ + v 2)) 0 := by
      fun_prop
    exact ((continuousAt_gevReturnLevelVar hξ₀ hξ₀0 hσ₀ hm).comp_of_eq haff (by simp)).sqrt
  have hS := hθ0.comp_continuousAt hG
  simp only [G, PiLp.zero_apply, add_zero] at hS
  have hS' : TendstoInMeasure P (fun (n : ℕ) ω => √(gevReturnLevelVar (θh n ω).1 (θh n ω).2.2 m))
      atTop (fun _ => √(gevReturnLevelVar ξ₀ σ₀ m)) := by
    simpa using hS
  have hSm : ∀ n : ℕ, AEMeasurable
      (fun ω => √(gevReturnLevelVar (θh n ω).1 (θh n ω).2.2 m)) P := fun n =>
    ((measurable_gevReturnLevelVar m).comp_aemeasurable
      ((measurable_fst.prodMk measurable_snd.snd).comp_aemeasurable (hθm n))).sqrt
  exact tendsto_measure_mem_gevMLEReturnLevelInterval hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hm hX hind hθm hθK
    hmax hS' hSm z

/-- **Computable asymptotic confidence interval for the GEV return level, with existence of the
measurable MLE.** -/
theorem exists_gevMLE_returnLevelPlugInInterval_tendsto {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hm : 1 < m)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P) :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) K (g n x)) ∧
      ∀ z : ℝ, Tendsto (fun n : ℕ => P {ω | gevReturnLevel ξ₀ μ₀ σ₀ m ∈ Icc
        (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
            (g n (fun i : Fin n => X i ω)).2.2 m -
          z * √(gevReturnLevelVar (g n (fun i : Fin n => X i ω)).1
            (g n (fun i : Fin n => X i ω)).2.2 m) / √(n : ℝ))
        (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
            (g n (fun i : Fin n => X i ω)).2.2 m +
          z * √(gevReturnLevelVar (g n (fun i : Fin n => X i ω)).1
            (g n (fun i : Fin n => X i ω)).2.2 m) / √(n : ℝ))})
        atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  choose g hgm hg using exists_measurable_gevMLE hK hKS ⟨_, interior_subset hθ₀⟩
  refine ⟨g, hgm, hg, fun z => ?_⟩
  exact tendsto_measure_mem_gevMLEReturnLevelPlugInInterval hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hm hX hind
    (θh := fun n ω => g n (fun i : Fin n => X i ω))
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2) z

end PlugInInterval

end ExtremeValueTheory
