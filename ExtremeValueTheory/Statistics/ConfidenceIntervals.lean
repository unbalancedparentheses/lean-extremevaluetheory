/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ReturnLevelNormality
import ExtremeValueTheory.Statistics.HillNormality
import ExtremeValueTheory.ForMathlib.Probability.WaldInterval

/-!
# Asymptotic confidence intervals for the tail index and for return levels

The Wald interval `θ̂ ± z ŝ / rₙ` built from an asymptotically normal estimator and a consistent
estimator `ŝ` of its asymptotic standard deviation has asymptotic coverage `N(0, 1)([-z, z])`,
which is `1 - α` for the two-sided standard normal quantile `z = z_{α/2}`
(`MeasureTheory.TendstoInDistribution.tendsto_measure_mem_waldInterval_gaussian`,
`ProbabilityTheory.exists_gaussianReal_Icc_eq`). We instantiate it for

* **the Hill estimator** (`tendsto_measure_mem_hillInterval`): `γ̂ ± z γ̂ / √k`, under the
  second-order conditions of `tendstoInDistribution_hill_of_tendsto_zero` (no asymptotic bias,
  `√k A(n/k) → 0`); the standard error `γ̂` is consistent because `√k (γ̂ - γ)` is tight;
* **the maximum likelihood POT return level** (`tendsto_measure_mem_gpdReturnLevelInterval`):
  `x̂_N ± z ŝ / √n` with the plug-in standard error `ŝ² = ∇x_Nᵀ I⁻¹ ∇x_N` evaluated at the
  MLE ([Coles, §4.3.3]);
* **the GEV return level** (`tendsto_measure_mem_gevReturnLevelInterval`), given asymptotic
  normality of the GEV parameter estimators and a consistent standard error (hypotheses, as the
  library does not yet prove GEV MLE normality).

The intervals are the symmetric delta-method intervals; Coles' profile likelihood intervals are
not covered.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §2.6.4, §3.3.3, §4.3.3.
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006), §3.2.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ExtremeValueTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-! ### The Hill estimator -/

/-- **Asymptotic confidence interval for the tail index** ([dHF, §3.2]). Under the hypotheses
of `tendstoInDistribution_hill_of_tendsto_zero` (iid, second-order regular variation of the tail
quantile function with index `γ > 0`, `k → ∞`, `k/n → 0`, `√k A(n/k) → 0`), the coverage
probability of the Wald interval `[γ̂ - z γ̂/√k, γ̂ + z γ̂/√k]`, `γ̂ = H_{k,n}`, converges to
`N(0, 1)([-z, z])`; for `z = z_{α/2}` the limit is `1 - α`. -/
theorem tendsto_measure_mem_hillInterval {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hA : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 0)) (z : ℝ) :
    Tendsto (fun n => P {ω | γ ∈ Icc
      (hill (fun i : Fin n => X i ω) (k n) - z * hill (fun i : Fin n => X i ω) (k n) / √(k n : ℝ))
      (hill (fun i : Fin n => X i ω) (k n) + z * hill (fun i : Fin n => X i ω) (k n) / √(k n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  set H : ℕ → Ω → ℝ := fun n ω => hill (fun i : Fin n => X i ω) (k n)
  have hZ : HasLaw id (gaussianReal 0 (γ ^ 2).toNNReal) (gaussianReal 0 (γ ^ 2).toNNReal) :=
    HasLaw.id
  have hN := tendstoInDistribution_hill_of_tendsto_zero hX hindep hident hγ h2 hk hkn hA hZ
  have hr : Tendsto (fun n => √(k n : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hk)
  -- consistency of `γ̂` from the rate `√k → ∞`
  have hcons0 : TendstoInMeasure P (fun n ω => H n ω - γ) atTop (fun _ => 0) :=
    TendstoInDistribution.tendstoInMeasure_of_smul (r := fun n => √(k n : ℝ)) hN hr
  have hcons : TendstoInMeasure P H atTop (fun _ => γ) := by
    have := hcons0.comp_continuousAt (g := fun x : ℝ => x + γ) (continuous_id.add continuous_const).continuousAt
    simpa using this
  have hHm : ∀ n, AEMeasurable (H n) P := fun n =>
    ((measurable_hill_pi n (k n)).comp (measurable_pi_iff.2 fun i => hX i)).aemeasurable
  exact hN.tendsto_measure_mem_waldInterval_gaussian hγ z hZ
    (hr.eventually_gt_atTop 0) hcons hHm

/-! ### The POT return level -/

lemma measurable_boxCoxShapeDeriv (x : ℝ) : Measurable fun ξ : ℝ => boxCoxShapeDeriv ξ x := by
  unfold boxCoxShapeDeriv
  fun_prop

lemma measurable_gpdReturnLevelVar (ζ N : ℝ) :
    Measurable fun p : ℝ × ℝ => gpdReturnLevelVar p.1 p.2 ζ N := by
  have hD : Measurable fun p : ℝ × ℝ => boxCoxShapeDeriv p.1 (N * ζ) :=
    (measurable_boxCoxShapeDeriv _).comp measurable_fst
  have hB : Measurable fun p : ℝ × ℝ => boxCox p.1 (N * ζ) :=
    measurable_boxCox.comp (measurable_fst.prodMk measurable_const)
  unfold gpdReturnLevelVar
  fun_prop

lemma continuousAt_gpdReturnLevelVar {ξ σ ζ N : ℝ} (hξ : ξ ≠ 0) (hNζ : 0 < N * ζ) :
    ContinuousAt (fun p : ℝ × ℝ => gpdReturnLevelVar p.1 p.2 ζ N) (ξ, σ) := by
  have hD : ContinuousAt (fun p : ℝ × ℝ => boxCoxShapeDeriv p.1 (N * ζ)) (ξ, σ) :=
    ContinuousAt.comp (g := fun ρ => boxCoxShapeDeriv ρ (N * ζ))
      (continuousAt_boxCoxShapeDeriv hξ hNζ) continuousAt_fst
  have hB : ContinuousAt (fun p : ℝ × ℝ => boxCox p.1 (N * ζ)) (ξ, σ) :=
    ((continuous_boxCox_shape hNζ).comp continuous_fst).continuousAt
  have h1 : ContinuousAt (fun p : ℝ × ℝ => p.1) (ξ, σ) := continuousAt_fst
  have h2 : ContinuousAt (fun p : ℝ × ℝ => p.2) (ξ, σ) := continuousAt_snd
  unfold gpdReturnLevelVar
  exact (continuousAt_const.add h1).mul
    ((((continuousAt_const.add h1).mul ((h2.mul hD).pow 2)).sub
      (((continuousAt_const.mul h2).mul (h2.mul hD)).mul hB)).add
      ((continuousAt_const.mul (h2.pow 2)).mul (hB.pow 2)))

/-- **Asymptotic confidence interval for the POT return level** ([Coles, §4.3.3]). Under the
hypotheses of `tendstoInDistribution_gpdReturnLevel` (maximum likelihood over a compact set,
`ξ₀ > -1/2`, `ξ₀ ≠ 0`, known exceedance probability `ζ`) and `N ζ > 1`, let
`ŝₙ = (∇x_Nᵀ I⁻¹ ∇x_N)^{1/2}` be the plug-in standard error at the MLE. The coverage probability
of `[x̂_N - z ŝₙ/√n, x̂_N + z ŝₙ/√n]` converges to `N(0, 1)([-z, z])`. -/
theorem tendsto_measure_mem_gpdReturnLevelInterval {ξ₀ σ₀ u ζ N : ℝ} {X : ℕ → Ω → ℝ}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω)) (hNζ : 1 < N * ζ) (z : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gpdReturnLevel u ξ₀ σ₀ ζ N ∈ Icc
      (gpdReturnLevel u (θh n ω).1 (θh n ω).2 ζ N -
        z * √(gpdReturnLevelVar (θh n ω).1 (θh n ω).2 ζ N) / √(n : ℝ))
      (gpdReturnLevel u (θh n ω).1 (θh n ω).2 ζ N +
        z * √(gpdReturnLevelVar (θh n ω).1 (θh n ω).2 ζ N) / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hNζ0 : 0 < N * ζ := one_pos.trans hNζ
  set v₀ := gpdReturnLevelVar ξ₀ σ₀ ζ N
  have hv₀ : 0 < v₀ := gpdReturnLevelVar_pos hξ₀ hσ₀ hNζ
  have hs : 0 < √v₀ := sqrt_pos.2 hv₀
  have hsq : √v₀ ^ 2 = v₀ := sq_sqrt hv₀.le
  have hW : HasLaw id (gaussianReal 0 (√v₀ ^ 2).toNNReal) (gaussianReal 0 (√v₀ ^ 2).toNNReal) :=
    HasLaw.id
  have hN := tendstoInDistribution_gpdReturnLevel (u := u) hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind hθm
    hθK hmax hNζ0 (show HasLaw id (gaussianReal 0 v₀.toNNReal)
      (gaussianReal 0 (√v₀ ^ 2).toNNReal) from ⟨aemeasurable_id, by rw [Measure.map_id, hsq]⟩)
  -- consistency of the parameter estimators, from their asymptotic normality
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
      (gpdFisherInfoInv ξ₀ σ₀)) (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) := HasLaw.id
  have hθN := tendstoInDistribution_gpdMLE_all hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind hθm hθK hmax hZ
  have hθ0 : TendstoInMeasure P (fun (n : ℕ) ω =>
      (!₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀] : EuclideanSpace ℝ (Fin 2))) atTop (fun _ => 0) :=
    TendstoInDistribution.tendstoInMeasure_of_smul (r := fun n : ℕ => √(n : ℝ)) hθN
      tendsto_sqrt_natCast_atTop
  -- consistency of the standard error
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun v => √(gpdReturnLevelVar (ξ₀ + v 0) (σ₀ + v 1) ζ N)
  have hG : ContinuousAt G 0 := by
    have haff : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 2) => (ξ₀ + v 0, σ₀ + v 1)) 0 := by
      fun_prop
    have hc := (continuousAt_gpdReturnLevelVar (σ := σ₀) hξ₀0 hNζ0).comp_of_eq haff (by simp)
    exact hc.sqrt
  have hS := hθ0.comp_continuousAt hG
  simp only [G, PiLp.zero_apply, add_zero] at hS
  have hS' : TendstoInMeasure P (fun (n : ℕ) ω => √(gpdReturnLevelVar (θh n ω).1 (θh n ω).2 ζ N))
      atTop (fun _ => √v₀) := by
    simpa using hS
  have hSm : ∀ n : ℕ, AEMeasurable
      (fun ω => √(gpdReturnLevelVar (θh n ω).1 (θh n ω).2 ζ N)) P := fun n =>
    ((measurable_gpdReturnLevelVar ζ N).comp_aemeasurable (hθm n)).sqrt
  have hr : ∀ᶠ n : ℕ in atTop, 0 < √(n : ℝ) :=
    tendsto_sqrt_natCast_atTop.eventually_gt_atTop 0
  exact hN.tendsto_measure_mem_waldInterval_gaussian hs z hW hr hS' hSm

/-! ### The GEV return level -/

/-- **Asymptotic confidence interval for the GEV return level** ([Coles, §3.3.3]). If GEV
parameter estimators satisfy `√n (θ̂ₙ - θ₀) ⇒ N(0, V)`, `ξ₀ ≠ 0`, the delta-method variance
`s² = ∇z_mᵀ V ∇z_m` is positive and `ŝₙ → s` in probability, then the coverage probability of
`[ẑ_m - z ŝₙ/√n, ẑ_m + z ŝₙ/√n]` converges to `N(0, 1)([-z, z])`. -/
theorem tendsto_measure_mem_gevReturnLevelInterval {ξ₀ μ₀ σ₀ m : ℝ} (hξ₀ : ξ₀ ≠ 0)
    (hm : 1 < m) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : V.PosSemidef) {Z : Ω' → EuclideanSpace ℝ (Fin 3)}
    (h : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      !₂[(θh n ω).1 - ξ₀, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]) atTop Z (fun _ => P) P')
    (hZ : HasLaw Z (multivariateGaussian 0 V) P') {s : ℝ} (hs : 0 < s)
    (hsV : s ^ 2 = gevReturnLevelGrad ξ₀ σ₀ m ⬝ᵥ V *ᵥ gevReturnLevelGrad ξ₀ σ₀ m)
    {S : ℕ → Ω → ℝ} (hS : TendstoInMeasure P S atTop (fun _ => s))
    (hSm : ∀ n, AEMeasurable (S n) P) (z : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gevReturnLevel ξ₀ μ₀ σ₀ m ∈ Icc
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m - z * S n ω / √(n : ℝ))
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m + z * S n ω / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hW : HasLaw id (gaussianReal 0 (s ^ 2).toNNReal) (gaussianReal 0 (s ^ 2).toNNReal) :=
    HasLaw.id
  have hN := tendstoInDistribution_gevReturnLevel hξ₀ hm hθm hV h hZ (show HasLaw id
    (gaussianReal 0 (gevReturnLevelGrad ξ₀ σ₀ m ⬝ᵥ V *ᵥ gevReturnLevelGrad ξ₀ σ₀ m).toNNReal)
    (gaussianReal 0 (s ^ 2).toNNReal) from ⟨aemeasurable_id, by rw [Measure.map_id, hsV]⟩)
  exact hN.tendsto_measure_mem_waldInterval_gaussian hs z hW
    (tendsto_sqrt_natCast_atTop.eventually_gt_atTop 0) hS hSm

end ExtremeValueTheory
