/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLEEnvelope

/-!
# Coordinates in which the support of the GEV family is linear

Fix the true parameter `θ₀ = (ξ₀, μ₀, σ₀)`, `ξ₀ ≠ 0`, and write `v = 1 + ξ₀ (x - μ₀)/σ₀` for the
position of an observation under the truth. For a parameter `θ = (ξ, μ, σ)`, the support function
`u = 1 + ξ (x - μ)/σ` is an **affine function of `v`**,

  `u = κ₀ + κ₁ v`, `κ₁ = ξ σ₀ / (ξ₀ σ)`, `κ₀ = 1 - κ₁ + (ξ/σ) (μ₀ - μ)`.

In the coordinates `η = (ξ, κ₀, κ₁)` (`ExtremeValueTheory.gevEtaOf`, with inverse
`ExtremeValueTheory.gevThetaOf`; the truth is
`(ξ₀, 0, 1)`) the set `{η : u(η, v) > 0}` of parameters admitting an observation is **convex**,
which it is not in the coordinates `(ξ, μ, σ)`: the segment from the truth to the maximum likelihood
estimator stays in the support of every observation. This is what replaces, for the three-parameter
family, the linearity of `σ + ξ x` used for the generalized Pareto family.

With `y = -log u / ξ` and `w = e^y = u^{-1/ξ}`, the log-density is
`gevEtaLog = log κ₁ - log (ξ/ξ₀) - log σ₀ + (1 + ξ) y - w`.

## Main results

* `hasDerivAt_gevEtaLog`, `hasDerivAt_gevEtaD`: `gevEtaD` and `gevEtaM` are the first and second
  derivatives of the log-density along curves in the coordinates `η`.
* `gevEtaD_eq_sum`, `gevEtaM_eq_sum`: they are linear and bilinear in the directions.

The link with the parameters `θ`, the score and the Fisher information is in
`ExtremeValueTheory.Statistics.GEVMLEInformation`.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### The log-density and its derivatives -/

section Defs

/-- The support function `u = κ₀ + κ₁ v` in the coordinates `η = (ξ, κ₀, κ₁)`. -/
noncomputable def gevEtaU (η : ℝ × ℝ × ℝ) (v : ℝ) : ℝ := η.2.1 + η.2.2 * v

/-- `y = -log u / ξ`, so that `e^y = u^{-1/ξ}`. -/
noncomputable def gevEtaY (η : ℝ × ℝ × ℝ) (v : ℝ) : ℝ := -log (gevEtaU η v) / η.1

/-- The GEV log-density in the coordinates `η`. -/
noncomputable def gevEtaLog (ξ₀ σ₀ : ℝ) (η : ℝ × ℝ × ℝ) (v : ℝ) : ℝ :=
  log η.2.2 - log (η.1 / ξ₀) - log σ₀ + (1 + η.1) * gevEtaY η v - exp (gevEtaY η v)

/-- The derivative of `y` in the direction `d`. -/
noncomputable def gevEtaDY (η : ℝ × ℝ × ℝ) (v : ℝ) (d : ℝ × ℝ × ℝ) : ℝ :=
  d.1 * log (gevEtaU η v) / η.1 ^ 2 - (d.2.1 + d.2.2 * v) / (η.1 * gevEtaU η v)

/-- The derivative of the log-density in the direction `d`. -/
noncomputable def gevEtaD (η : ℝ × ℝ × ℝ) (v : ℝ) (d : ℝ × ℝ × ℝ) : ℝ :=
  d.2.2 / η.2.2 - d.1 / η.1 + d.1 * gevEtaY η v + (1 + η.1 - exp (gevEtaY η v)) * gevEtaDY η v d

/-- The second derivative of `y` in the directions `d`, `e`. -/
noncomputable def gevEtaDDY (η : ℝ × ℝ × ℝ) (v : ℝ) (d e : ℝ × ℝ × ℝ) : ℝ :=
  η.1 * gevEtaDY η v d * gevEtaDY η v e +
    (d.1 * gevEtaDY η v e + e.1 * gevEtaDY η v d) * (gevEtaY η v - 1 / η.1) +
    1 / η.1 * d.1 * e.1 * gevEtaY η v ^ 2

/-- The second derivative of the log-density in the directions `d`, `e`. -/
noncomputable def gevEtaM (η : ℝ × ℝ × ℝ) (v : ℝ) (d e : ℝ × ℝ × ℝ) : ℝ :=
  -(d.2.2 * e.2.2) / η.2.2 ^ 2 + d.1 * e.1 / η.1 ^ 2 + d.1 * gevEtaDY η v e + e.1 * gevEtaDY η v d -
    exp (gevEtaY η v) * gevEtaDY η v d * gevEtaDY η v e +
    (1 + η.1 - exp (gevEtaY η v)) * gevEtaDDY η v d e

/-- The coordinates of a direction. -/
def gevEtaCoord (d : ℝ × ℝ × ℝ) : Fin 3 → ℝ := ![d.1, d.2.1, d.2.2]

/-- The coordinate directions. -/
def gevEtaBasis : Fin 3 → ℝ × ℝ × ℝ := ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]

/-- The `ℓ¹` norm of a direction. -/
noncomputable def gevEtaNorm (d : ℝ × ℝ × ℝ) : ℝ := |d.1| + |d.2.1| + |d.2.2|

lemma gevEtaNorm_nonneg (d : ℝ × ℝ × ℝ) : 0 ≤ gevEtaNorm d := by unfold gevEtaNorm; positivity

lemma abs_fst_le_gevEtaNorm (d : ℝ × ℝ × ℝ) : |d.1| ≤ gevEtaNorm d := by
  unfold gevEtaNorm; linarith [abs_nonneg d.2.1, abs_nonneg d.2.2]

lemma abs_snd_fst_le_gevEtaNorm (d : ℝ × ℝ × ℝ) : |d.2.1| ≤ gevEtaNorm d := by
  unfold gevEtaNorm; linarith [abs_nonneg d.1, abs_nonneg d.2.2]

lemma abs_snd_snd_le_gevEtaNorm (d : ℝ × ℝ × ℝ) : |d.2.2| ≤ gevEtaNorm d := by
  unfold gevEtaNorm; linarith [abs_nonneg d.1, abs_nonneg d.2.1]

lemma gevEtaNorm_eq_sum (d : ℝ × ℝ × ℝ) : gevEtaNorm d = ∑ j, |gevEtaCoord d j| := by
  simp [gevEtaNorm, gevEtaCoord, Fin.sum_univ_three]

lemma gevEtaNorm_smul (r : ℝ) (d : ℝ × ℝ × ℝ) : gevEtaNorm (r • d) = |r| * gevEtaNorm d := by
  simp only [gevEtaNorm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
  ring

/-- The derivative is linear in the direction. -/
lemma gevEtaD_eq_sum (η : ℝ × ℝ × ℝ) (v : ℝ) (d : ℝ × ℝ × ℝ) :
    gevEtaD η v d = ∑ j, gevEtaCoord d j * gevEtaD η v (gevEtaBasis j) := by
  simp only [Fin.sum_univ_three, gevEtaCoord, gevEtaBasis, gevEtaD, gevEtaDY]
  simp
  ring

/-- The second derivative is bilinear in the directions. -/
lemma gevEtaM_eq_sum (η : ℝ × ℝ × ℝ) (v : ℝ) (d e : ℝ × ℝ × ℝ) :
    gevEtaM η v d e = ∑ j, ∑ k, gevEtaCoord d j * gevEtaCoord e k *
      gevEtaM η v (gevEtaBasis j) (gevEtaBasis k) := by
  simp only [Fin.sum_univ_three, gevEtaCoord, gevEtaBasis, gevEtaM, gevEtaDDY, gevEtaDY]
  simp
  ring

end Defs

/-! ### Derivatives along curves -/

section Derivatives

variable {X K₀ K₁ : ℝ → ℝ} {τ b c s : ℝ} {v : ℝ}

/-- The curve in the coordinates `η` with components `X, K₀, K₁`. -/
private lemma hasDerivAt_u (hK₀ : HasDerivAt K₀ b s) (hK₁ : HasDerivAt K₁ c s) :
    HasDerivAt (fun r => gevEtaU (X r, K₀ r, K₁ r) v) (b + c * v) s :=
  hK₀.add (hK₁.mul_const v)

private lemma hasDerivAt_y (hX : HasDerivAt X τ s) (hK₀ : HasDerivAt K₀ b s)
    (hK₁ : HasDerivAt K₁ c s) (hξ : X s ≠ 0) (hu : gevEtaU (X s, K₀ s, K₁ s) v ≠ 0) :
    HasDerivAt (fun r => gevEtaY (X r, K₀ r, K₁ r) v)
      (gevEtaDY (X s, K₀ s, K₁ s) v (τ, b, c)) s := by
  have hU := hasDerivAt_u (X := X) (v := v) hK₀ hK₁
  have hd := (hU.log hu).neg.div hX hξ
  refine hd.congr_deriv ?_
  simp only [gevEtaDY, Pi.neg_apply]
  generalize log (gevEtaU (X s, K₀ s, K₁ s) v) = L
  generalize gevEtaU (X s, K₀ s, K₁ s) v = u at hu
  field_simp
  ring

/-- **The first derivative** of the log-density along a curve in the coordinates `η`. -/
theorem hasDerivAt_gevEtaLog {ξ₀ σ₀ : ℝ} (hξ₀ : ξ₀ ≠ 0) (hX : HasDerivAt X τ s)
    (hK₀ : HasDerivAt K₀ b s) (hK₁ : HasDerivAt K₁ c s) (hξ : X s ≠ 0) (hκ : K₁ s ≠ 0)
    (hu : gevEtaU (X s, K₀ s, K₁ s) v ≠ 0) :
    HasDerivAt (fun r => gevEtaLog ξ₀ σ₀ (X r, K₀ r, K₁ r) v)
      (gevEtaD (X s, K₀ s, K₁ s) v (τ, b, c)) s := by
  have hY := hasDerivAt_y hX hK₀ hK₁ hξ hu
  have hR : HasDerivAt (fun r => X r / ξ₀) (τ / ξ₀) s := hX.div_const ξ₀
  have hd := (((hK₁.log hκ).sub (hR.log (div_ne_zero hξ hξ₀))).sub_const (log σ₀)).add
    ((hX.const_add 1).mul hY) |>.sub hY.exp
  refine hd.congr_deriv ?_
  simp only [gevEtaD]
  generalize gevEtaDY (X s, K₀ s, K₁ s) v (τ, b, c) = Y
  generalize exp (gevEtaY (X s, K₀ s, K₁ s) v) = w
  generalize gevEtaY (X s, K₀ s, K₁ s) v = y
  field_simp
  ring

private lemma hasDerivAt_dy (e : ℝ × ℝ × ℝ) (hX : HasDerivAt X τ s) (hK₀ : HasDerivAt K₀ b s)
    (hK₁ : HasDerivAt K₁ c s) (hξ : X s ≠ 0) (hu : gevEtaU (X s, K₀ s, K₁ s) v ≠ 0) :
    HasDerivAt (fun r => gevEtaDY (X r, K₀ r, K₁ r) v e)
      (gevEtaDDY (X s, K₀ s, K₁ s) v (τ, b, c) e) s := by
  have hU := hasDerivAt_u (X := X) (v := v) hK₀ hK₁
  have hL := hU.log hu
  have hS : HasDerivAt (fun r => X r ^ 2) (2 * X s * τ) s := by simpa using hX.fun_pow 2
  have hd := ((hL.const_mul e.1).div hS (pow_ne_zero 2 hξ)).sub
    ((hasDerivAt_const s (e.2.1 + e.2.2 * v)).div (hX.mul hU) (mul_ne_zero hξ hu))
  refine hd.congr_deriv ?_
  simp only [gevEtaDDY, gevEtaDY, gevEtaY, Pi.mul_apply]
  generalize log (gevEtaU (X s, K₀ s, K₁ s) v) = L
  generalize gevEtaU (X s, K₀ s, K₁ s) v = u at hu
  field_simp
  ring

/-- **The second derivative** of the log-density along a curve in the coordinates `η`: the
derivative of `gevEtaD · v e` in the direction `(τ, b, c)` is `gevEtaM · v (τ, b, c) e`. -/
theorem hasDerivAt_gevEtaD (e : ℝ × ℝ × ℝ) (hX : HasDerivAt X τ s)
    (hK₀ : HasDerivAt K₀ b s) (hK₁ : HasDerivAt K₁ c s) (hξ : X s ≠ 0) (hκ : K₁ s ≠ 0)
    (hu : gevEtaU (X s, K₀ s, K₁ s) v ≠ 0) :
    HasDerivAt (fun r => gevEtaD (X r, K₀ r, K₁ r) v e)
      (gevEtaM (X s, K₀ s, K₁ s) v (τ, b, c) e) s := by
  have hY := hasDerivAt_y hX hK₀ hK₁ hξ hu
  have hDY := hasDerivAt_dy (v := v) e hX hK₀ hK₁ hξ hu
  have hd := (((hasDerivAt_const s e.2.2).div hK₁ hκ).sub
    ((hasDerivAt_const s e.1).div hX hξ)).add (hY.const_mul e.1) |>.add
    (((hX.const_add 1).sub hY.exp).mul hDY)
  refine hd.congr_deriv ?_
  simp only [gevEtaM, Pi.sub_apply]
  generalize gevEtaDDY (X s, K₀ s, K₁ s) v (τ, b, c) e = Z
  generalize gevEtaDY (X s, K₀ s, K₁ s) v e = Ye
  generalize gevEtaDY (X s, K₀ s, K₁ s) v (τ, b, c) = Yd
  generalize exp (gevEtaY (X s, K₀ s, K₁ s) v) = w
  generalize gevEtaY (X s, K₀ s, K₁ s) v = y
  field_simp
  ring

end Derivatives

end ExtremeValueTheory
