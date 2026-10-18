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

/-! ### Gumbel and GPD return levels as functions of the parameters -/

section Gradients

/-- The Gumbel return level as a function of `(μ, σ) ∈ ℝ²`. -/
noncomputable def gumbelReturnLevelVec (m : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  gevReturnLevel 0 (v 0) (v 1) m

/-- The gradient of the Gumbel return level in `(μ, σ)`: `(1, -log y_m)` ([Coles, §3.3.3]). -/
theorem hasGradientAt_gumbelReturnLevelVec (μ σ m : ℝ) :
    HasGradientAt (gumbelReturnLevelVec m) !₂[1, -log (-log (1 - 1 / m))] !₂[μ, σ] := by
  have p0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := !₂[μ, σ])
  have p1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := !₂[μ, σ])
  have hd := p0.add (p1.mul_const (-log (-log (1 - 1 / m))))
  refine hasGradientAt_of_hasFDerivAt
    (hd.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)) fun v => ?_
  · simp [gumbelReturnLevelVec, gevReturnLevel_zero, sub_eq_add_neg]
  · simp [Fin.sum_univ_two]

/-- The **`N`-observation return level of the peaks-over-threshold model** ([Coles, (4.12)]):
with threshold `u`, exceedance probability `ζ = P(X > u)` and excess law `GPD(ξ, σ)`, the level
exceeded on average once every `N` observations is `x_N = u + σ h_ξ(N ζ)`. -/
noncomputable def gpdReturnLevel (u ξ σ ζ N : ℝ) : ℝ := u + σ * boxCox ξ (N * ζ)

/-- Coles' form, `ξ ≠ 0`: `x_N = u + σ/ξ ((N ζ)^ξ - 1)`. -/
theorem gpdReturnLevel_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) (u σ ζ N : ℝ) :
    gpdReturnLevel u ξ σ ζ N = u + σ / ξ * ((N * ζ) ^ ξ - 1) := by
  rw [gpdReturnLevel, boxCox_of_ne hξ]
  ring

/-- The exponential case: `x_N = u + σ log(N ζ)`. -/
theorem gpdReturnLevel_zero (u σ ζ N : ℝ) :
    gpdReturnLevel u 0 σ ζ N = u + σ * log (N * ζ) := by
  rw [gpdReturnLevel, boxCox_zero]

/-- The GPD return level is continuous in the shape at `ξ = 0`. -/
theorem tendsto_gpdReturnLevel_zero (u σ : ℝ) {ζ N : ℝ} (hNζ : 0 < N * ζ) :
    Tendsto (fun ξ => gpdReturnLevel u ξ σ ζ N) (𝓝 0) (𝓝 (gpdReturnLevel u 0 σ ζ N)) :=
  (continuousAt_const.add (continuousAt_const.mul (continuousAt_boxCox_shape_zero hNζ))).tendsto

/-- The GPD return level as a function of `(ξ, σ) ∈ ℝ²`, with `u`, `ζ` and `N` fixed. -/
noncomputable def gpdReturnLevelVec (u ζ N : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  gpdReturnLevel u (v 0) (v 1) ζ N

/-- The gradient of the GPD return level in `(ξ, σ)`: `(σ ∂_ξ h_ξ(Nζ), h_ξ(Nζ))`. -/
noncomputable def gpdReturnLevelGrad (ξ σ ζ N : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[σ * boxCoxShapeDeriv ξ (N * ζ), boxCox ξ (N * ζ)]

/-- Coles' form of the gradient ([Coles, §4.3.3]):
`∂x_N/∂ξ = -σ ξ⁻² ((Nζ)^ξ - 1) + σ ξ⁻¹ (Nζ)^ξ log(Nζ)`, `∂x_N/∂σ = ξ⁻¹ ((Nζ)^ξ - 1)`. -/
theorem gpdReturnLevelGrad_eq {ξ : ℝ} (hξ : ξ ≠ 0) (σ ζ N : ℝ) :
    gpdReturnLevelGrad ξ σ ζ N =
      !₂[-σ / ξ ^ 2 * ((N * ζ) ^ ξ - 1) + σ / ξ * (N * ζ) ^ ξ * log (N * ζ),
        ((N * ζ) ^ ξ - 1) / ξ] := by
  rw [gpdReturnLevelGrad, boxCoxShapeDeriv, boxCox_of_ne hξ]
  congr 2
  ring

/-- **The gradient of the GPD return level**, `ξ ≠ 0`, `N ζ > 0`. -/
theorem hasGradientAt_gpdReturnLevelVec {ξ σ u ζ N : ℝ} (hξ : ξ ≠ 0) (hNζ : 0 < N * ζ) :
    HasGradientAt (gpdReturnLevelVec u ζ N) (gpdReturnLevelGrad ξ σ ζ N) !₂[ξ, σ] := by
  have p0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := !₂[ξ, σ])
  have p1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := !₂[ξ, σ])
  have hb : HasDerivAt (fun ρ => boxCox ρ (N * ζ)) (boxCoxShapeDeriv ξ (N * ζ))
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) !₂[ξ, σ]) := by
    simpa using hasDerivAt_boxCox_shape hξ hNζ
  have hd := (p1.mul (hb.comp_hasFDerivAt !₂[ξ, σ] p0)).const_add u
  refine hasGradientAt_of_hasFDerivAt
    (hd.congr_of_eventuallyEq (Eventually.of_forall fun v => by
      simp [gpdReturnLevelVec, gpdReturnLevel])) fun v => ?_
  simp [Fin.sum_univ_two, gpdReturnLevelGrad]
  ring

/-- The asymptotic variance `∇x_Nᵀ I(ξ, σ)⁻¹ ∇x_N` of the GPD maximum likelihood return level,
with `∇x_N = (a, b)`: `(1 + ξ) ((1 + ξ) a² - 2σ a b + 2σ² b²)`. -/
noncomputable def gpdReturnLevelVar (ξ σ ζ N : ℝ) : ℝ :=
  (1 + ξ) * ((1 + ξ) * (σ * boxCoxShapeDeriv ξ (N * ζ)) ^ 2 -
    2 * σ * (σ * boxCoxShapeDeriv ξ (N * ζ)) * boxCox ξ (N * ζ) +
    2 * σ ^ 2 * boxCox ξ (N * ζ) ^ 2)

theorem dotProduct_gpdReturnLevelGrad (ξ σ ζ N : ℝ) :
    gpdReturnLevelGrad ξ σ ζ N ⬝ᵥ gpdFisherInfoInv ξ σ *ᵥ gpdReturnLevelGrad ξ σ ζ N =
      gpdReturnLevelVar ξ σ ζ N := by
  simp [gpdReturnLevelGrad, gpdReturnLevelVar, gpdFisherInfoInv, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The return level variance is positive when the return period exceeds the mean waiting
time between exceedances, `N ζ > 1`, and `ξ > -1/2`, `σ > 0`. -/
theorem gpdReturnLevelVar_pos {ξ σ ζ N : ℝ} (hξ : -1 / 2 < ξ) (hσ : 0 < σ)
    (hNζ : 1 < N * ζ) : 0 < gpdReturnLevelVar ξ σ ζ N := by
  have hb := boxCox_pos_of_one_lt (ρ := ξ) hNζ
  set a := σ * boxCoxShapeDeriv ξ (N * ζ)
  set b := boxCox ξ (N * ζ)
  have h1 : 0 < 1 + ξ := by linarith
  have hq : 0 < (1 + ξ) * a ^ 2 - 2 * σ * a * b + 2 * σ ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg ((1 + ξ) * a - σ * b), mul_pos hσ hb, mul_pos (mul_pos hσ hb) h1,
      mul_pos (mul_pos hσ hb) (mul_pos hσ hb)]
  exact mul_pos h1 hq

/-- The POT return level as a function of `(ζ, ξ, σ) ∈ ℝ³`, with `u` and `N` fixed. -/
noncomputable def gpdReturnLevelVec₃ (u N : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  gpdReturnLevel u (v 1) (v 2) (v 0) N

/-- The gradient of the POT return level in `(ζ, ξ, σ)`:
`(σ N (Nζ)^{ξ-1}, σ ∂_ξ h_ξ(Nζ), h_ξ(Nζ))`. -/
noncomputable def gpdReturnLevelGrad₃ (ζ ξ σ N : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[σ * N * (N * ζ) ^ (ξ - 1), σ * boxCoxShapeDeriv ξ (N * ζ), boxCox ξ (N * ζ)]

/-- The `ζ` component in Coles' form, `∂x_N/∂ζ = σ N^ξ ζ^{ξ-1}` ([Coles, §4.3.3]). -/
theorem gpdReturnLevelGrad₃_zero {ζ N : ℝ} (hζ : 0 < ζ) (hN : 0 < N) (ξ σ : ℝ) :
    gpdReturnLevelGrad₃ ζ ξ σ N 0 = σ * N ^ ξ * ζ ^ (ξ - 1) := by
  simp only [gpdReturnLevelGrad₃]
  simp only [Matrix.cons_val_zero]
  rw [mul_rpow hN.le hζ.le, rpow_sub_one hN.ne']
  field_simp

/-- **The gradient of the POT return level in `(ζ, ξ, σ)`**, `ξ ≠ 0`, `N ζ > 0`. -/
theorem hasGradientAt_gpdReturnLevelVec₃ {ζ ξ σ u N : ℝ} (hξ : ξ ≠ 0) (hNζ : 0 < N * ζ) :
    HasGradientAt (gpdReturnLevelVec₃ u N) (gpdReturnLevelGrad₃ ζ ξ σ N) !₂[ζ, ξ, σ] := by
  set θ : EuclideanSpace ℝ (Fin 3) := !₂[ζ, ξ, σ]
  have p0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt (x := θ)
  have p1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt (x := θ)
  have p2 := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := θ)
  have hθ0 : EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) θ = ζ := by simp [θ]
  have hθ1 : EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) θ = ξ := by simp [θ]
  have hθ2 : EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) θ = σ := by simp [θ]
  have hpow := (p0.const_mul N).rpow p1 (by rw [hθ0]; exact hNζ)
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(ξ ^ 2)⁻¹)
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) θ) := by
    rw [hθ1]; exact hasDerivAt_inv hξ
  have hd := (p2.mul ((hpow.sub_const 1).mul (hinv.comp_hasFDerivAt θ p1))).const_add u
  have hev : (gpdReturnLevelVec₃ u N) =ᶠ[𝓝 θ] fun v => u + v 2 * ((N * v 0) ^ v 1 - 1) * (v 1)⁻¹ := by
    have hopen : {v : EuclideanSpace ℝ (Fin 3) | v 1 ≠ 0} ∈ 𝓝 θ :=
      (isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous
        continuous_const).mem_nhds (by simp [θ, hξ])
    filter_upwards [hopen] with v hv
    simp only [gpdReturnLevelVec₃, gpdReturnLevel, boxCox_of_ne hv, div_eq_mul_inv, mul_assoc]
  refine hasGradientAt_of_hasFDerivAt (hd.congr_of_eventuallyEq (hev.trans
    (Eventually.of_forall fun v => by simp [mul_assoc]))) fun v => ?_
  simp only [hθ0, hθ1, hθ2]
  simp [θ, Fin.sum_univ_three, gpdReturnLevelGrad₃, boxCoxShapeDeriv, boxCox_of_ne hξ]
  field_simp
  ring

end Gradients

/-! ### Asymptotic normality of estimated return levels -/

section Normality

variable {Ω Ω' Ω'' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mΩ'' : MeasurableSpace Ω''} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {P'' : Measure Ω''} [IsProbabilityMeasure P'']

lemma tendsto_sqrt_natCast_atTop : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
  tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- **Asymptotic normality of the GEV return level** ([Coles, §3.3.3]). If estimators
`θ̂ₙ = (ξ̂ₙ, μ̂ₙ, σ̂ₙ)` of the GEV parameters satisfy `√n (θ̂ₙ - θ₀) ⇒ N(0, V)` and `ξ₀ ≠ 0`, then
the plug-in `m`-block return level satisfies `√n (ẑ_m - z_m) ⇒ N(0, ∇z_mᵀ V ∇z_m)`, with the
gradient `gevReturnLevelGrad` (`gevReturnLevelGrad_eq`). -/
theorem tendstoInDistribution_gevReturnLevel {ξ₀ μ₀ σ₀ m : ℝ} (hξ₀ : ξ₀ ≠ 0) (hm : 1 < m)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : V.PosSemidef) {Z : Ω' → EuclideanSpace ℝ (Fin 3)}
    (h : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      !₂[(θh n ω).1 - ξ₀, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]) atTop Z (fun _ => P) P')
    (hZ : HasLaw Z (multivariateGaussian 0 V) P') {W : Ω'' → ℝ}
    (hW : HasLaw W (gaussianReal 0
      (gevReturnLevelGrad ξ₀ σ₀ m ⬝ᵥ V *ᵥ gevReturnLevelGrad ξ₀ σ₀ m).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m - gevReturnLevel ξ₀ μ₀ σ₀ m))
      atTop W (fun _ => P) P'' := by
  have h' : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      ((!₂[(θh n ω).1, (θh n ω).2.1, (θh n ω).2.2] : EuclideanSpace ℝ (Fin 3)) -
        !₂[ξ₀, μ₀, σ₀])) atTop Z (fun _ => P) P' := by
    refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
    simp only
    congr 1
    ext i; fin_cases i <;> simp
  have hd := h'.delta_method_gaussian hV hZ tendsto_sqrt_natCast_atTop
    (hasGradientAt_gevReturnLevelVec (μ := μ₀) hξ₀ hm)
    (fun n => ((measurable_gevReturnLevel m).comp_aemeasurable (hθm n)).congr
      (Eventually.of_forall fun ω => by simp [gevReturnLevelVec])) hW
  simpa [gevReturnLevelVec] using hd

/-- **Asymptotic normality of the Gumbel return level** ([Coles, §3.3.3]): if
`√n (μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, V)`, then `√n (ẑ_m - z_m) ⇒ N(0, ∇zᵀ V ∇z)`,
`∇z = (1, -log y_m)`, `y_m = -log(1 - 1/m)`. -/
theorem tendstoInDistribution_gumbelReturnLevel {μ₀ σ₀ m : ℝ}
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    {V : Matrix (Fin 2) (Fin 2) ℝ} (hV : V.PosSemidef) {Z : Ω' → EuclideanSpace ℝ (Fin 2)}
    (h : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      !₂[(θh n ω).1 - μ₀, (θh n ω).2 - σ₀]) atTop Z (fun _ => P) P')
    (hZ : HasLaw Z (multivariateGaussian 0 V) P') {W : Ω'' → ℝ}
    (hW : HasLaw W (gaussianReal 0 ((!₂[1, -log (-log (1 - 1 / m))] : EuclideanSpace ℝ (Fin 2)) ⬝ᵥ
      V *ᵥ (!₂[1, -log (-log (1 - 1 / m))] : EuclideanSpace ℝ (Fin 2))).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel 0 (θh n ω).1 (θh n ω).2 m - gevReturnLevel 0 μ₀ σ₀ m))
      atTop W (fun _ => P) P'' := by
  have h' : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      ((!₂[(θh n ω).1, (θh n ω).2] : EuclideanSpace ℝ (Fin 2)) - !₂[μ₀, σ₀]))
      atTop Z (fun _ => P) P' := by
    refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
    simp only
    congr 1
    ext i; fin_cases i <;> simp
  have hmeas : Measurable fun p : ℝ × ℝ => gevReturnLevel 0 p.1 p.2 m := by
    simp only [gevReturnLevel_zero]; fun_prop
  have hd := h'.delta_method_gaussian hV hZ tendsto_sqrt_natCast_atTop
    (hasGradientAt_gumbelReturnLevelVec μ₀ σ₀ m)
    (fun n => (hmeas.comp_aemeasurable (hθm n)).congr
      (Eventually.of_forall fun ω => by simp [gumbelReturnLevelVec])) hW
  simpa [gumbelReturnLevelVec] using hd

lemma measurable_gpdReturnLevel (u ζ N : ℝ) :
    Measurable fun p : ℝ × ℝ => gpdReturnLevel u p.1 p.2 ζ N := by
  unfold gpdReturnLevel
  exact measurable_const.add (measurable_snd.mul
    (measurable_boxCox.comp (measurable_fst.prodMk measurable_const)))

/-- **Asymptotic normality of a POT return level from asymptotically normal GPD parameter
estimators**, `ζ_u` known: if `√n (ξ̂ₙ - ξ₀, σ̂ₙ - σ₀) ⇒ N(0, V)`, `ξ₀ ≠ 0`, `N ζ > 0`, then
`√n (x̂_N - x_N) ⇒ N(0, ∇x_Nᵀ V ∇x_N)`. -/
theorem tendstoInDistribution_gpdReturnLevel_of_tendstoInDistribution {ξ₀ σ₀ u ζ N : ℝ}
    (hξ₀ : ξ₀ ≠ 0) (hNζ : 0 < N * ζ)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    {V : Matrix (Fin 2) (Fin 2) ℝ} (hV : V.PosSemidef) {Z : Ω' → EuclideanSpace ℝ (Fin 2)}
    (h : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      !₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀]) atTop Z (fun _ => P) P')
    (hZ : HasLaw Z (multivariateGaussian 0 V) P') {W : Ω'' → ℝ}
    (hW : HasLaw W (gaussianReal 0 (gpdReturnLevelGrad ξ₀ σ₀ ζ N ⬝ᵥ
      V *ᵥ gpdReturnLevelGrad ξ₀ σ₀ ζ N).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gpdReturnLevel u (θh n ω).1 (θh n ω).2 ζ N - gpdReturnLevel u ξ₀ σ₀ ζ N))
      atTop W (fun _ => P) P'' := by
  have h' : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      ((!₂[(θh n ω).1, (θh n ω).2] : EuclideanSpace ℝ (Fin 2)) - !₂[ξ₀, σ₀]))
      atTop Z (fun _ => P) P' := by
    refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
    simp only
    congr 1
    ext i; fin_cases i <;> simp
  have hd := h'.delta_method_gaussian hV hZ tendsto_sqrt_natCast_atTop
    (hasGradientAt_gpdReturnLevelVec (σ := σ₀) (u := u) hξ₀ hNζ)
    (fun n => ((measurable_gpdReturnLevel u ζ N).comp_aemeasurable (hθm n)).congr
      (Eventually.of_forall fun ω => by simp [gpdReturnLevelVec])) hW
  simpa [gpdReturnLevelVec] using hd

/-- **Asymptotic normality of the maximum likelihood POT return level** ([Coles, §4.3.3];
[Smith 1985]). Let `K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, σ₀)`, `ξ₀ > -1/2`,
`ξ₀ ≠ 0`, in its interior, let the excesses `X₀, X₁, …` be iid `GPD(θ₀)`, and let `θ̂ₙ` be
measurable maximizers of the GPD log-likelihood over `K`. For a known exceedance probability
`ζ` and `N ζ > 0`, the return level `x̂_N = u + σ̂ₙ h_{ξ̂ₙ}(N ζ)` satisfies

  `√n (x̂_N - x_N) ⇒ N(0, ∇x_Nᵀ I(θ₀)⁻¹ ∇x_N)`,

the variance being `gpdReturnLevelVar ξ₀ σ₀ ζ N` (`dotProduct_gpdReturnLevelGrad`). -/
theorem tendstoInDistribution_gpdReturnLevel {ξ₀ σ₀ u ζ N : ℝ} {X : ℕ → Ω → ℝ}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω)) (hNζ : 0 < N * ζ) {W : Ω'' → ℝ}
    (hW : HasLaw W (gaussianReal 0 (gpdReturnLevelVar ξ₀ σ₀ ζ N).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gpdReturnLevel u (θh n ω).1 (θh n ω).2 ζ N - gpdReturnLevel u ξ₀ σ₀ ζ N))
      atTop W (fun _ => P) P'' := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
      (gpdFisherInfoInv ξ₀ σ₀)) (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) := HasLaw.id
  have h := tendstoInDistribution_gpdMLE_all hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind hθm hθK hmax hZ
  exact tendstoInDistribution_gpdReturnLevel_of_tendstoInDistribution hξ₀0 hNζ hθm
    (posDef_gpdFisherInfoInv hξ₀ hσ₀).posSemidef h hZ
    (by rwa [dotProduct_gpdReturnLevelGrad])

lemma measurable_gpdReturnLevel₃ (u N : ℝ) :
    Measurable fun p : ℝ × ℝ × ℝ => gpdReturnLevel u p.2.1 p.2.2 p.1 N := by
  unfold gpdReturnLevel
  exact measurable_const.add (measurable_snd.snd.mul
    (measurable_boxCox.comp (measurable_snd.fst.prodMk (measurable_const.mul measurable_fst))))

/-- **Asymptotic normality of the POT return level with estimated exceedance rate**
([Coles, §4.3.3]). If `√n (ζ̂ₙ - ζ₀, ξ̂ₙ - ξ₀, σ̂ₙ - σ₀) ⇒ N(0, V)`, `ξ₀ ≠ 0`, `N ζ₀ > 0`, then
`√n (x̂_N - x_N) ⇒ N(0, ∇x_Nᵀ V ∇x_N)` with `∇x_N = (σ N^ξ ζ^{ξ-1}, σ ∂_ξ h, h)`
(`gpdReturnLevelGrad₃`, `gpdReturnLevelGrad₃_zero`). Coles takes `V` block diagonal, with
`ζ̂` the exceedance frequency (`Var = ζ(1 - ζ)`) and the GPD inverse information. -/
theorem tendstoInDistribution_gpdReturnLevel₃ {ζ₀ ξ₀ σ₀ u N : ℝ} (hξ₀ : ξ₀ ≠ 0)
    (hNζ : 0 < N * ζ₀) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : V.PosSemidef) {Z : Ω' → EuclideanSpace ℝ (Fin 3)}
    (h : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      !₂[(θh n ω).1 - ζ₀, (θh n ω).2.1 - ξ₀, (θh n ω).2.2 - σ₀]) atTop Z (fun _ => P) P')
    (hZ : HasLaw Z (multivariateGaussian 0 V) P') {W : Ω'' → ℝ}
    (hW : HasLaw W (gaussianReal 0 (gpdReturnLevelGrad₃ ζ₀ ξ₀ σ₀ N ⬝ᵥ
      V *ᵥ gpdReturnLevelGrad₃ ζ₀ ξ₀ σ₀ N).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gpdReturnLevel u (θh n ω).2.1 (θh n ω).2.2 (θh n ω).1 N - gpdReturnLevel u ξ₀ σ₀ ζ₀ N))
      atTop W (fun _ => P) P'' := by
  have h' : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      ((!₂[(θh n ω).1, (θh n ω).2.1, (θh n ω).2.2] : EuclideanSpace ℝ (Fin 3)) -
        !₂[ζ₀, ξ₀, σ₀])) atTop Z (fun _ => P) P' := by
    refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
    simp only
    congr 1
    ext i; fin_cases i <;> simp
  have hd := h'.delta_method_gaussian hV hZ tendsto_sqrt_natCast_atTop
    (hasGradientAt_gpdReturnLevelVec₃ (σ := σ₀) (u := u) hξ₀ hNζ)
    (fun n => ((measurable_gpdReturnLevel₃ u N).comp_aemeasurable (hθm n)).congr
      (Eventually.of_forall fun ω => by simp [gpdReturnLevelVec₃])) hW
  simpa [gpdReturnLevelVec₃] using hd

end Normality

end ExtremeValueTheory
