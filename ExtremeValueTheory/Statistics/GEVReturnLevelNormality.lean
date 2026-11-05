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

## Not covered

* `ξ₀ = 0`: see `ExtremeValueTheory.Statistics.GEVMLENormality`.
* In the confidence interval the consistency of the standard error is a hypothesis; the consistency
  of the plug-in `ŝₙ² = ∇z(θ̂ₙ)ᵀ V(θ̂ₙ) ∇z(θ̂ₙ)`, which needs the continuity of `gevFisherInfo` in the
  parameters, is not formalized.
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

end ExtremeValueTheory
