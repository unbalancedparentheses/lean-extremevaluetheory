/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDMLENormality
import ExtremeValueTheory.Statistics.ExtremeQuantile
import ExtremeValueTheory.RegularVariation.SecondOrder
import ExtremeValueTheory.ForMathlib.Probability.DeltaMethod

/-!
# Return levels and their asymptotic normality (delta method)

The return levels of the two classical extreme value models are smooth functions of the
parameters, so the delta method (`MeasureTheory.TendstoInDistribution.delta_method_gaussian`)
turns asymptotic normality of the parameter estimators into asymptotic normality of the
estimated return levels, with variance `∇zᵀ V ∇z` ([Coles 2001, §3.3.3, §4.3.3]).

Both return levels are written with the Box–Cox function `h_ξ(x) = (x^ξ - 1)/ξ`, `h_0 = log`
(`boxCox`):

* **GEV, block maxima.** The `m`-block return level of `GEV(ξ, μ, σ)` is
  `z_m = μ + σ h_ξ(1/y_m) = μ - σ/ξ (1 - y_m^{-ξ})`, `y_m = -log(1 - 1/m)` (`gevReturnLevel`,
  `gevReturnLevel_eq_of_ne`), with the Gumbel return level `z_m = μ - σ log y_m` at `ξ = 0`
  (`gevReturnLevel_zero`), which is also the limit as `ξ → 0` (`tendsto_gevReturnLevel_gumbel`).
* **GPD, peaks over threshold.** With threshold `u`, exceedance probability `ζ_u` and excess law
  `GPD(ξ, σ)`, the level exceeded on average once every `N` observations is
  `x_N = u + σ h_ξ(N ζ_u) = u + σ/ξ ((N ζ_u)^ξ - 1)` (`gpdReturnLevel`,
  `gpdReturnLevel_of_ne`).

## Main results

* `hasDerivAt_boxCox_shape`, `continuousAt_boxCox_shape_zero`: the Box–Cox function is
  differentiable in its index `ξ ≠ 0`, with derivative `boxCoxShapeDeriv`, and continuous at
  `ξ = 0`.
* `hasGradientAt_gevReturnLevelVec`: the gradient of `z_m` in `(ξ, μ, σ)` is
  `(σ ∂_ξ h, 1, h)`; `gevReturnLevelGrad_zero_eq` writes `σ ∂_ξ h` in Coles' form
  `σ ξ⁻² (1 - y^{-ξ}) - σ ξ⁻¹ y^{-ξ} log y`.
* `tendstoInDistribution_gevReturnLevel`: if `√n (θ̂ₙ - θ₀) ⇒ N(0, V)` for GEV parameter
  estimators, `ξ₀ ≠ 0`, then `√n (ẑ_m - z_m) ⇒ N(0, ∇zᵀ V ∇z)`.
  `tendstoInDistribution_gumbelReturnLevel`: the same for the Gumbel model, `∇z = (1, -log y_m)`.
* `tendstoInDistribution_gpdReturnLevel`: **the maximum likelihood return level of the GPD is
  asymptotically normal**, `√n (x̂_N - x_N) ⇒ N(0, ∇xᵀ I(θ₀)⁻¹ ∇x)`, from the joint normality
  of the GPD MLE (`tendstoInDistribution_gpdMLE_all`), for `ξ₀ > -1/2`, `ξ₀ ≠ 0`, `ζ_u` known.
  `dotProduct_gpdReturnLevelGrad` evaluates the variance.
* `tendstoInDistribution_gpdReturnLevel₃`: with `ζ_u` estimated too: if
  `√n (ζ̂ - ζ, ξ̂ - ξ, σ̂ - σ) ⇒ N(0, V)`, then `√n (x̂_N - x_N) ⇒ N(0, ∇xᵀ V ∇x)` with
  `∇x = (σ N^ξ ζ^{ξ-1}, σ ∂_ξ h, h)`.

## Deviations from the textbook

* The library proves joint asymptotic normality for the GPD maximum likelihood estimator only
  (`tendstoInDistribution_gpdMLE_all`). For the GEV and Gumbel models, and for the triple
  `(ζ̂_u, ξ̂, σ̂)`, joint normality of the parameter estimators is a hypothesis (any covariance
  `V`); Coles takes `V` block diagonal with `Var ζ̂_u = ζ_u (1 - ζ_u)/n`.
* Parameters are ordered `(ξ, μ, σ)` and `(ξ, σ)`, as in the rest of the library, rather than
  Coles' `(μ, σ, ξ)` and `(σ, ξ)`; the gradients are permuted accordingly.
* In the GPD statement the excesses form an iid sample of size `n` with `ζ_u` known; the random
  number of exceedances of a fixed threshold in a sample from the parent law is not modelled.
* The delta method at `ξ₀ = 0` in the three-parameter GEV model is not covered (the gradient
  formula has `ξ` in denominators; the function is smooth there, but this is not formalized).

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §3.3.3 and §4.3.3.
* A. W. van der Vaart, *Asymptotic Statistics*, Theorem 3.1.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace ExtremeValueTheory

/-! ### The Box–Cox function as a function of its index -/

section BoxCox

/-- The derivative of `ξ ↦ h_ξ(x) = (x^ξ - 1)/ξ` at `ξ ≠ 0`:
`∂_ξ h_ξ(x) = x^ξ log x / ξ - (x^ξ - 1)/ξ²`. -/
noncomputable def boxCoxShapeDeriv (ξ x : ℝ) : ℝ := x ^ ξ * log x / ξ - (x ^ ξ - 1) / ξ ^ 2

lemma boxCox_eventuallyEq {ξ : ℝ} (hξ : ξ ≠ 0) (x : ℝ) :
    (fun ρ => boxCox ρ x) =ᶠ[𝓝 ξ] fun ρ => (x ^ ρ - 1) / ρ := by
  filter_upwards [isOpen_ne.mem_nhds hξ] with ρ hρ
  exact boxCox_of_ne hρ x

/-- The Box–Cox function is differentiable in its index `ξ ≠ 0`. -/
theorem hasDerivAt_boxCox_shape {ξ x : ℝ} (hξ : ξ ≠ 0) (hx : 0 < x) :
    HasDerivAt (fun ρ => boxCox ρ x) (boxCoxShapeDeriv ξ x) ξ := by
  have h1 : HasDerivAt (fun ρ => x ^ ρ) (x ^ ξ * log x) ξ :=
    (hasStrictDerivAt_const_rpow hx ξ).hasDerivAt
  have h2 := (h1.sub_const 1).div (hasDerivAt_id ξ) hξ
  refine (h2.congr_of_eventuallyEq (boxCox_eventuallyEq hξ x)).congr_deriv ?_
  simp only [boxCoxShapeDeriv, id]
  field_simp

/-- The Box–Cox function is continuous in its index at `ξ = 0`: `(x^ξ - 1)/ξ → log x`. -/
theorem continuousAt_boxCox_shape_zero {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun ρ => boxCox ρ x) 0 := by
  have h := (hasStrictDerivAt_const_rpow hx 0).hasDerivAt.tendsto_slope
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, boxCox_zero]
  simp only [rpow_zero, one_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  rw [slope_def_field, boxCox_of_ne hρ, rpow_zero, sub_zero]

/-- The Box–Cox function is continuous in its index everywhere, for `x > 0`. -/
theorem continuous_boxCox_shape {x : ℝ} (hx : 0 < x) : Continuous fun ρ => boxCox ρ x := by
  refine continuous_iff_continuousAt.2 fun ξ => ?_
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact continuousAt_boxCox_shape_zero hx
  · exact (hasDerivAt_boxCox_shape hξ hx).continuousAt

lemma continuousAt_boxCoxShapeDeriv {ξ x : ℝ} (hξ : ξ ≠ 0) (hx : 0 < x) :
    ContinuousAt (fun ρ => boxCoxShapeDeriv ρ x) ξ := by
  unfold boxCoxShapeDeriv
  have hc : Continuous fun ρ : ℝ => x ^ ρ := continuous_const.rpow continuous_id fun _ => Or.inl hx.ne'
  exact ((hc.continuousAt.mul continuousAt_const).div continuousAt_id hξ).sub
    ((hc.continuousAt.sub continuousAt_const).div (continuousAt_id.pow 2) (pow_ne_zero 2 hξ))

lemma measurable_boxCox : Measurable fun p : ℝ × ℝ => boxCox p.1 p.2 := by
  unfold boxCox
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (measurable_snd.log) ?_
  exact ((measurable_snd.pow measurable_fst).sub_const 1).div measurable_fst

end BoxCox

/-! ### GEV return levels -/

section GEV

/-- `y_m = -log(1 - 1/m)`, the quantity entering the `m`-block return level. -/
lemma neg_log_one_sub_inv_pos {m : ℝ} (hm : 1 < m) : 0 < -log (1 - 1 / m) := by
  have hm0 : 0 < m := one_pos.trans hm
  have h1 : 0 < 1 - 1 / m := by
    have : 1 / m < 1 := (div_lt_one hm0).2 hm
    linarith
  have h2 : 1 - 1 / m < 1 := by
    have : 0 < 1 / m := by positivity
    linarith
  exact neg_pos.2 (log_neg h1 h2)

/-- The standardized return level is a Box–Cox transform: `z_m = h_ξ(1/y_m)`. -/
theorem returnLevel_eq_boxCox (ξ : ℝ) {m : ℝ} (hm : 1 < m) :
    returnLevel ξ m = boxCox ξ (-log (1 - 1 / m))⁻¹ := by
  have hy := neg_log_one_sub_inv_pos hm
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [returnLevel, boxCox_zero, log_inv]
  · rw [boxCox_of_ne hξ, inv_rpow hy.le, ← rpow_neg hy.le]
    simp only [returnLevel, hξ, ↓reduceIte]

/-- The **`m`-block return level** of `GEV(ξ, μ, σ)`: `z_m = μ + σ z_m^{std}`, the
`(1 - 1/m)` quantile of the block maximum (`gevLocScaleCDF_returnLevel`). -/
noncomputable def gevReturnLevel (ξ μ σ m : ℝ) : ℝ := μ + σ * returnLevel ξ m

/-- Coles' form of the GEV return level, `ξ ≠ 0`:
`z_m = μ - σ/ξ (1 - y_m^{-ξ})`, `y_m = -log(1 - 1/m)` ([Coles, (3.4)]). -/
theorem gevReturnLevel_eq_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) (μ σ m : ℝ) :
    gevReturnLevel ξ μ σ m = μ - σ / ξ * (1 - (-log (1 - 1 / m)) ^ (-ξ)) := by
  simp only [gevReturnLevel, returnLevel, hξ, ↓reduceIte]
  field_simp
  ring

/-- The **Gumbel return level**: `z_m = μ - σ log y_m` ([Coles, (3.4)], `ξ = 0`). -/
theorem gevReturnLevel_zero (μ σ m : ℝ) :
    gevReturnLevel 0 μ σ m = μ - σ * log (-log (1 - 1 / m)) := by
  simp [gevReturnLevel, returnLevel, sub_eq_add_neg]

/-- **Gumbel limit of the GEV return level**: `z_m(ξ) → μ - σ log y_m` as `ξ → 0`. -/
theorem tendsto_gevReturnLevel_gumbel (μ σ : ℝ) {m : ℝ} (hm : 1 < m) :
    Tendsto (fun ξ => gevReturnLevel ξ μ σ m) (𝓝 0) (𝓝 (gevReturnLevel 0 μ σ m)) := by
  have h := continuousAt_boxCox_shape_zero (inv_pos.2 (neg_log_one_sub_inv_pos hm))
  have : (fun ξ => gevReturnLevel ξ μ σ m) =
      fun ξ => μ + σ * boxCox ξ (-log (1 - 1 / m))⁻¹ := by
    funext ξ; rw [gevReturnLevel, returnLevel_eq_boxCox ξ hm]
  have hc : ContinuousAt (fun ξ => gevReturnLevel ξ μ σ m) 0 := by
    rw [this]
    exact continuousAt_const.add (continuousAt_const.mul h)
  exact hc.tendsto

lemma measurable_gevReturnLevel (m : ℝ) :
    Measurable fun p : ℝ × ℝ × ℝ => gevReturnLevel p.1 p.2.1 p.2.2 m := by
  unfold gevReturnLevel returnLevel
  refine measurable_snd.fst.add (measurable_snd.snd.mul ?_)
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
    (((measurable_const.pow measurable_fst.neg).sub_const 1).div measurable_fst)

/-- The return level as a function of the parameter vector `(ξ, μ, σ) ∈ ℝ³`. -/
noncomputable def gevReturnLevelVec (m : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  gevReturnLevel (v 0) (v 1) (v 2) m

/-- The gradient of the GEV return level in `(ξ, μ, σ)`:
`∇z_m = (σ ∂_ξ h_ξ(1/y_m), 1, h_ξ(1/y_m))`. -/
noncomputable def gevReturnLevelGrad (ξ σ m : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[σ * boxCoxShapeDeriv ξ (-log (1 - 1 / m))⁻¹, 1, returnLevel ξ m]

lemma returnLevel_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) (m : ℝ) :
    returnLevel ξ m = ((-log (1 - 1 / m)) ^ (-ξ) - 1) / ξ := by
  simp only [returnLevel, hξ, ↓reduceIte]

lemma boxCoxShapeDeriv_inv {ξ y : ℝ} (hξ : ξ ≠ 0) (hy : 0 < y) (σ : ℝ) :
    σ * boxCoxShapeDeriv ξ y⁻¹ = σ / ξ ^ 2 * (1 - y ^ (-ξ)) - σ / ξ * y ^ (-ξ) * log y := by
  rw [boxCoxShapeDeriv, inv_rpow hy.le, ← rpow_neg hy.le, log_inv]
  field_simp
  ring

/-- Coles' form of the shape component of the gradient ([Coles, §3.3.3]):
`∂z_m/∂ξ = σ ξ⁻² (1 - y_m^{-ξ}) - σ ξ⁻¹ y_m^{-ξ} log y_m`; the other components are
`∂z_m/∂μ = 1` and `∂z_m/∂σ = -ξ⁻¹ (1 - y_m^{-ξ})`. -/
theorem gevReturnLevelGrad_eq {ξ : ℝ} (hξ : ξ ≠ 0) (σ : ℝ) {m : ℝ} (hm : 1 < m) :
    gevReturnLevelGrad ξ σ m =
      !₂[σ / ξ ^ 2 * (1 - (-log (1 - 1 / m)) ^ (-ξ)) -
          σ / ξ * (-log (1 - 1 / m)) ^ (-ξ) * log (-log (1 - 1 / m)), 1,
        -(1 - (-log (1 - 1 / m)) ^ (-ξ)) / ξ] := by
  have hy := neg_log_one_sub_inv_pos hm
  rw [gevReturnLevelGrad, boxCoxShapeDeriv_inv hξ hy, returnLevel_of_ne hξ, neg_sub]

/-- Gradients on `ℝ^k` from Fréchet derivatives with explicit coordinates. -/
lemma hasGradientAt_of_hasFDerivAt {k : ℕ} {g : EuclideanSpace ℝ (Fin k) → ℝ}
    {L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ} {a θ : EuclideanSpace ℝ (Fin k)}
    (hg : HasFDerivAt g L θ) (hL : ∀ v, L v = ∑ i, a i * v i) : HasGradientAt g a θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hg using 1
  ext v
  simp [hL, PiLp.inner_apply, mul_comm]

/-- **The gradient of the GEV return level**, `ξ ≠ 0`. -/
theorem hasGradientAt_gevReturnLevelVec {ξ μ σ m : ℝ} (hξ : ξ ≠ 0) (hm : 1 < m) :
    HasGradientAt (gevReturnLevelVec m) (gevReturnLevelGrad ξ σ m) !₂[ξ, μ, σ] := by
  have hx := inv_pos.2 (neg_log_one_sub_inv_pos hm)
  set x := (-log (1 - 1 / m))⁻¹
  have hfun : gevReturnLevelVec m =
      fun v : EuclideanSpace ℝ (Fin 3) => v 1 + v 2 * boxCox (v 0) x := by
    funext v; rw [gevReturnLevelVec, gevReturnLevel, returnLevel_eq_boxCox _ hm]
  rw [hfun]
  have p0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt (x := !₂[ξ, μ, σ])
  have p1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt (x := !₂[ξ, μ, σ])
  have p2 := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := !₂[ξ, μ, σ])
  have hb : HasDerivAt (fun ρ => boxCox ρ x) (boxCoxShapeDeriv ξ x)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) !₂[ξ, μ, σ]) := by
    simpa using hasDerivAt_boxCox_shape hξ hx
  have hd := p1.add (p2.mul (hb.comp_hasFDerivAt !₂[ξ, μ, σ] p0))
  refine hasGradientAt_of_hasFDerivAt
    (hd.congr_of_eventuallyEq (Eventually.of_forall fun v => by simp)) fun v => ?_
  simp [Fin.sum_univ_three, gevReturnLevelGrad, returnLevel_eq_boxCox _ hm, x]
  ring

end GEV

end ExtremeValueTheory
