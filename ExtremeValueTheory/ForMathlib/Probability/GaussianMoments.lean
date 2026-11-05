/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Second and fourth moments of a centered real Gaussian

Mathlib gives the moment-generating function of `gaussianReal` and the identity between iterated
derivatives of the moment-generating function at `0` and moments. Differentiating
`t ↦ exp (v t² / 2)` four times gives the moments below.

## Main results

* `ProbabilityTheory.integrable_sq_gaussianReal`, `ProbabilityTheory.integrable_pow_four_gaussianReal`.
* `ProbabilityTheory.integral_sq_gaussianReal`: `∫ x², N(0, v) = v`.
* `ProbabilityTheory.integral_pow_four_gaussianReal`: `∫ x⁴, N(0, v) = 3 v²`.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ProbabilityTheory

/-- The moment-generating function of `N(0, v)`. -/
private noncomputable def gaussExp (v : ℝ) (t : ℝ) : ℝ := Real.exp (v * t ^ 2 / 2)

private lemma hasDerivAt_gaussExp (v t : ℝ) : HasDerivAt (gaussExp v) (v * t * gaussExp v t) t := by
  have h : HasDerivAt (fun t : ℝ => v * t ^ 2 / 2) (v * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul v).div_const 2
    convert this using 1
    simp
    ring
  refine HasDerivAt.congr_deriv (f := gaussExp v) h.exp ?_
  simp only [gaussExp]
  ring

/-- Differentiating `p · gaussExp v`, for `p` with derivative `p'`. -/
private lemma deriv_mul_gaussExp {v : ℝ} {p p' q : ℝ → ℝ} (hp : ∀ t, HasDerivAt p (p' t) t)
    (hq : ∀ t, q t = p' t + p t * (v * t)) :
    deriv (fun t => p t * gaussExp v t) = fun t => q t * gaussExp v t := by
  funext t
  have h : deriv (fun t => p t * gaussExp v t) t = _ :=
    HasDerivAt.deriv (f := fun t => p t * gaussExp v t) ((hp t).mul (hasDerivAt_gaussExp v t))
  rw [h, hq]
  ring

private lemma deriv_gaussExp₁ (v : ℝ) :
    deriv (gaussExp v) = fun t => (v * t) * gaussExp v t :=
  funext fun t => (hasDerivAt_gaussExp v t).deriv

private lemma deriv_gaussExp₂ (v : ℝ) :
    deriv (fun t => (v * t) * gaussExp v t) = fun t => (v + v ^ 2 * t ^ 2) * gaussExp v t :=
  deriv_mul_gaussExp (p' := fun _ => v)
    (fun t => by simpa using (hasDerivAt_id t).const_mul v) (fun t => by ring)

private lemma deriv_gaussExp₃ (v : ℝ) :
    deriv (fun t => (v + v ^ 2 * t ^ 2) * gaussExp v t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gaussExp v t :=
  deriv_mul_gaussExp (p' := fun t => 2 * v ^ 2 * t)
    (fun t => by
      convert ((hasDerivAt_pow 2 t).const_mul (v ^ 2)).const_add v using 1
      simp
      ring)
    (fun t => by ring)

private lemma deriv_gaussExp₄ (v : ℝ) :
    deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gaussExp v t) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * gaussExp v t :=
  deriv_mul_gaussExp (p' := fun t => 3 * v ^ 2 + 3 * v ^ 3 * t ^ 2)
    (fun t => HasDerivAt.congr_deriv (f := fun t => 3 * v ^ 2 * t + v ^ 3 * t ^ 3)
      (((hasDerivAt_id t).const_mul (3 * v ^ 2)).add ((hasDerivAt_pow 3 t).const_mul (v ^ 3)))
      (by simp; ring))
    (fun t => by ring)

variable {v : ℝ≥0}

private lemma iteratedDeriv_gaussExp (n : ℕ) :
    iteratedDeriv n (gaussExp v) 0 = ∫ x, x ^ n ∂gaussianReal 0 v := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) n
  have e : mgf id (gaussianReal 0 v) = gaussExp v := by
    funext t
    rw [mgf_id_gaussianReal]
    simp [gaussExp]
  rw [e] at h
  simpa using h

/-- `x²` is integrable under `N(0, v)`. -/
theorem integrable_sq_gaussianReal : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  ((memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_norm_pow (p := 2) (by norm_num)).congr
    (ae_of_all _ fun x => by simp [Real.norm_eq_abs])

/-- `x⁴` is integrable under `N(0, v)`. -/
theorem integrable_pow_four_gaussianReal : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) :=
  ((memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow (p := 4) (by norm_num)).congr
    (ae_of_all _ fun x => by simp [Real.norm_eq_abs, Even.pow_abs (show Even 4 by decide)])

/-- The second moment of `N(0, v)` is `v`. -/
theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  rw [← iteratedDeriv_gaussExp 2, show (2 : ℕ) = 0 + 1 + 1 from rfl, iteratedDeriv_succ',
    iteratedDeriv_succ', iteratedDeriv_zero, deriv_gaussExp₁, deriv_gaussExp₂]
  simp [gaussExp]

/-- The fourth moment of `N(0, v)` is `3 v²`. -/
theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  rw [← iteratedDeriv_gaussExp 4, show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, iteratedDeriv_succ',
    iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero,
    deriv_gaussExp₁, deriv_gaussExp₂, deriv_gaussExp₃, deriv_gaussExp₄]
  simp [gaussExp]

end ProbabilityTheory
