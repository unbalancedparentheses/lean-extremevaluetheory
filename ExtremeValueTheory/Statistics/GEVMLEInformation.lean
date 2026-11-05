/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLEDomination

/-!
# The coordinates `η` and the parameters `θ`: scores and the information identity

This file links the coordinates `η = (ξ, κ₀, κ₁)` of
`ExtremeValueTheory.Statistics.GEVMLECoordinates` to the parameters `θ = (ξ, μ, σ)`.

* `gevEtaOf`, `gevThetaOf`: the change of coordinates and its inverse;
  `gevU_gevThetaOf`: `u(θ(η), x) = κ₀ + κ₁ v(x)`;
  `log_gevLocScaleDensity_gevThetaOf`: the log-density is `gevEtaLog`.
* `gevEtaJ`, `gevEtaJInv`: the Jacobian of `gevThetaOf` at the truth `(ξ₀, 0, 1)`, in the order
  `(μ, σ, ξ)` of `gevScore` and `gevFisherInfo`, and its inverse;
  `exists_abs_gevThetaOf_sub_sub_le`: the remainder of the first-order expansion is quadratic.
* `gevEtaD_self_eq`: at the truth, the derivative in the direction `d` is
  `(J d) ⬝ᵥ gevScore`.
* `gevEtaM_self_eq`: at the truth, the second derivative in the directions `d, e` is
  `(J d)ᵀ H (J e) + (gevEtaSecond d e) ⬝ᵥ gevScore`, with `H = gevHess` and `gevEtaSecond` the
  second derivative of `gevThetaOf` at the truth.
* `integral_gevEtaM_self`:
  `E[M(η₀, v)[d, e]] = -(J d)ᵀ I(θ₀) (J e)`, for `ξ₀ > -1/2`, `ξ₀ ≠ 0`.
* `exists_gevEtaInfo_ge`: the form `(J d)ᵀ I(θ₀) (J d)` is uniformly positive definite.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ExtremeValueTheory

/-! ### The change of coordinates -/

section Change

variable {ξ₀ μ₀ σ₀ : ℝ}

/-- The parameters `θ = (ξ, μ, σ)` from the coordinates `η = (ξ, κ₀, κ₁)`:
`σ = ξ σ₀ / (ξ₀ κ₁)`, `μ = μ₀ + (1 - κ₁ - κ₀) σ₀ / (ξ₀ κ₁)`. -/
noncomputable def gevThetaOf (ξ₀ μ₀ σ₀ : ℝ) (η : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (η.1, μ₀ + (1 - η.2.2 - η.2.1) * σ₀ / (ξ₀ * η.2.2), η.1 * σ₀ / (ξ₀ * η.2.2))

/-- The coordinates `η = (ξ, κ₀, κ₁)` from the parameters `θ = (ξ, μ, σ)`:
`κ₁ = ξ σ₀ / (ξ₀ σ)`, `κ₀ = 1 - κ₁ + (ξ/σ) (μ₀ - μ)`. -/
noncomputable def gevEtaOf (ξ₀ μ₀ σ₀ : ℝ) (θ : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (θ.1, 1 - θ.1 * σ₀ / (ξ₀ * θ.2.2) + θ.1 / θ.2.2 * (μ₀ - θ.2.1), θ.1 * σ₀ / (ξ₀ * θ.2.2))

lemma gevEtaOf_self (hξ₀ : ξ₀ ≠ 0) (hσ₀ : σ₀ ≠ 0) : gevEtaOf ξ₀ μ₀ σ₀ (ξ₀, μ₀, σ₀) = (ξ₀, 0, 1) := by
  simp only [gevEtaOf, sub_self, mul_zero, add_zero]
  have : ξ₀ * σ₀ / (ξ₀ * σ₀) = 1 := div_self (mul_ne_zero hξ₀ hσ₀)
  rw [this]
  simp

lemma gevThetaOf_gevEtaOf (hξ₀ : ξ₀ ≠ 0) (hσ₀ : σ₀ ≠ 0) {θ : ℝ × ℝ × ℝ} (h1 : θ.1 ≠ 0)
    (h2 : θ.2.2 ≠ 0) : gevThetaOf ξ₀ μ₀ σ₀ (gevEtaOf ξ₀ μ₀ σ₀ θ) = θ := by
  obtain ⟨ξ, μ, σ⟩ := θ
  simp only at h1 h2
  simp only [gevThetaOf, gevEtaOf, Prod.mk.injEq, true_and]
  constructor
  · field_simp
    ring
  · field_simp

/-- **The support function is affine in `v`**: `u(θ(η), x) = κ₀ + κ₁ v(x)`. -/
theorem gevU_gevThetaOf (hξ₀ : ξ₀ ≠ 0) (hσ₀ : σ₀ ≠ 0) {η : ℝ × ℝ × ℝ} (h1 : η.1 ≠ 0)
    (h2 : η.2.2 ≠ 0) (x : ℝ) :
    gevU (gevThetaOf ξ₀ μ₀ σ₀ η).1 (gevThetaOf ξ₀ μ₀ σ₀ η).2.1 (gevThetaOf ξ₀ μ₀ σ₀ η).2.2 x =
      gevEtaU η (gevU ξ₀ μ₀ σ₀ x) := by
  simp only [gevThetaOf, gevU, gevEtaU]
  field_simp
  ring

/-- The scale `σ` of `θ(η)` is positive in the box. -/
lemma gevThetaOf_scale_pos (hσ₀ : 0 < σ₀) {η : ℝ × ℝ × ℝ} (h1 : 0 < η.1 / ξ₀) (h2 : 0 < η.2.2) :
    0 < (gevThetaOf ξ₀ μ₀ σ₀ η).2.2 := by
  have e : (gevThetaOf ξ₀ μ₀ σ₀ η).2.2 = η.1 / ξ₀ * (σ₀ / η.2.2) := by
    simp only [gevThetaOf]
    rw [div_mul_div_comm]
  rw [e]
  positivity

/-- **The log-density in the coordinates `η`.** -/
theorem log_gevLocScaleDensity_gevThetaOf (hξ₀ : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) {η : ℝ × ℝ × ℝ}
    (h1 : 0 < η.1 / ξ₀) (h2 : 0 < η.2.2) {x : ℝ} (hu : 0 < gevEtaU η (gevU ξ₀ μ₀ σ₀ x)) :
    log (gevLocScaleDensity (gevThetaOf ξ₀ μ₀ σ₀ η).1 (gevThetaOf ξ₀ μ₀ σ₀ η).2.1
      (gevThetaOf ξ₀ μ₀ σ₀ η).2.2 x) = gevEtaLog ξ₀ σ₀ η (gevU ξ₀ μ₀ σ₀ x) := by
  have hξ : η.1 ≠ 0 := fun h => by simp [h] at h1
  have hU := gevU_gevThetaOf (μ₀ := μ₀) hξ₀ hσ₀.ne' hξ h2.ne' x
  have hσ := gevThetaOf_scale_pos (μ₀ := μ₀) hσ₀ h1 h2
  have hu' : 0 < 1 + (gevThetaOf ξ₀ μ₀ σ₀ η).1 *
      ((x - (gevThetaOf ξ₀ μ₀ σ₀ η).2.1) / (gevThetaOf ξ₀ μ₀ σ₀ η).2.2) := by
    have := hU ▸ hu
    exact this
  have hne : (gevThetaOf ξ₀ μ₀ σ₀ η).1 ≠ 0 := hξ
  rw [log_gevLocScaleDensity hσ hne hu']
  have hU' : 1 + (gevThetaOf ξ₀ μ₀ σ₀ η).1 *
      ((x - (gevThetaOf ξ₀ μ₀ σ₀ η).2.1) / (gevThetaOf ξ₀ μ₀ σ₀ η).2.2) =
      gevEtaU η (gevU ξ₀ μ₀ σ₀ x) := hU
  rw [hU', rpow_def_of_pos hu]
  have hlogσ : log (gevThetaOf ξ₀ μ₀ σ₀ η).2.2 = log (η.1 / ξ₀) + log σ₀ - log η.2.2 := by
    have e : (gevThetaOf ξ₀ μ₀ σ₀ η).2.2 = η.1 / ξ₀ * σ₀ / η.2.2 := by
      simp only [gevThetaOf]
      field_simp
    rw [e, log_div (by positivity) h2.ne', log_mul h1.ne' hσ₀.ne']
  rw [hlogσ]
  have hfst : (gevThetaOf ξ₀ μ₀ σ₀ η).1 = η.1 := rfl
  rw [hfst]
  simp only [gevEtaLog, gevEtaY]
  rw [show log (gevEtaU η (gevU ξ₀ μ₀ σ₀ x)) * (-1 / η.1) =
    -log (gevEtaU η (gevU ξ₀ μ₀ σ₀ x)) / η.1 by ring]
  field_simp
  ring

/-- The Jacobian of `gevThetaOf` at the truth, in the order `(μ, σ, ξ)`. -/
noncomputable def gevEtaJ (ξ₀ σ₀ : ℝ) (d : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  ![σ₀ / ξ₀ * (-d.2.2 - d.2.1), σ₀ / ξ₀ * (d.1 - ξ₀ * d.2.2), d.1]

/-- The inverse of the Jacobian `gevEtaJ`. -/
noncomputable def gevEtaJInv (ξ₀ σ₀ : ℝ) (f : Fin 3 → ℝ) : ℝ × ℝ × ℝ :=
  (f 2, -(f 2 / ξ₀ - f 1 / σ₀) - ξ₀ * f 0 / σ₀, f 2 / ξ₀ - f 1 / σ₀)

lemma gevEtaJ_gevEtaJInv (hξ₀ : ξ₀ ≠ 0) (hσ₀ : σ₀ ≠ 0) (f : Fin 3 → ℝ) :
    gevEtaJ ξ₀ σ₀ (gevEtaJInv ξ₀ σ₀ f) = f := by
  funext j
  fin_cases j <;> simp [gevEtaJ, gevEtaJInv] <;> field_simp <;> ring

lemma gevEtaJInv_gevEtaJ (hξ₀ : ξ₀ ≠ 0) (hσ₀ : σ₀ ≠ 0) (d : ℝ × ℝ × ℝ) :
    gevEtaJInv ξ₀ σ₀ (gevEtaJ ξ₀ σ₀ d) = d := by
  obtain ⟨τ, b, c⟩ := d
  simp [gevEtaJ, gevEtaJInv, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- The second derivative of `gevThetaOf` at the truth, in the order `(μ, σ, ξ)`. -/
noncomputable def gevEtaSecond (ξ₀ σ₀ : ℝ) (d e : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  ![σ₀ / ξ₀ * (2 * d.2.2 * e.2.2 + d.2.1 * e.2.2 + e.2.1 * d.2.2),
    σ₀ / ξ₀ * (2 * ξ₀ * d.2.2 * e.2.2 - d.1 * e.2.2 - e.1 * d.2.2), 0]

/-- **The first-order expansion of `gevThetaOf` at the truth has a quadratic remainder**: for `d`
with `|d| ≤ 1/4`, in the `ℓ¹` norm, each coordinate of `θ(η₀ + d) - θ₀ - J d` is at most
`C |d|²` in absolute value. -/
theorem exists_abs_gevThetaOf_sub_sub_le (hξ₀ : ξ₀ ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ × ℝ × ℝ, gevEtaNorm d ≤ 1 / 4 →
      |(gevThetaOf ξ₀ μ₀ σ₀ ((ξ₀, 0, 1) + d)).2.1 - μ₀ - gevEtaJ ξ₀ σ₀ d 0| ≤
          C * gevEtaNorm d ^ 2 ∧
      |(gevThetaOf ξ₀ μ₀ σ₀ ((ξ₀, 0, 1) + d)).2.2 - σ₀ - gevEtaJ ξ₀ σ₀ d 1| ≤
          C * gevEtaNorm d ^ 2 ∧
      (gevThetaOf ξ₀ μ₀ σ₀ ((ξ₀, 0, 1) + d)).1 - ξ₀ - gevEtaJ ξ₀ σ₀ d 2 = 0 := by
  set A := |σ₀ / ξ₀| with hA
  refine ⟨2 * A * (1 + |ξ₀|), by positivity, fun d hd => ?_⟩
  obtain ⟨τ, b, c⟩ := d
  have hτ := abs_fst_le_gevEtaNorm (τ, b, c)
  have hb := abs_snd_fst_le_gevEtaNorm (τ, b, c)
  have hc := abs_snd_snd_le_gevEtaNorm (τ, b, c)
  simp only at hτ hb hc
  set N := gevEtaNorm (τ, b, c) with hN
  have hN0 : 0 ≤ N := gevEtaNorm_nonneg _
  have hc4 : |c| ≤ 1 / 4 := hc.trans hd
  have h1c : 3 / 4 ≤ 1 + c := by have := (abs_le.1 hc4).1; linarith
  have h1c0 : 1 + c ≠ 0 := by intro h; linarith
  have hinv : |1 / (1 + c)| ≤ 2 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ (by linarith)]
    linarith
  have hA0 : 0 ≤ A := abs_nonneg _
  have hcc : |c| * |c| ≤ N ^ 2 := by nlinarith [abs_nonneg c]
  have hcb : |c + b| * |c| ≤ N ^ 2 := by
    have : |c + b| ≤ N := by
      refine (abs_add_le _ _).trans ?_
      simp only [hN, gevEtaNorm]
      linarith [abs_nonneg τ]
    exact (mul_le_mul this hc (abs_nonneg _) hN0).trans (by nlinarith)
  have hcτ : |ξ₀ * c ^ 2 - τ * c| ≤ (1 + |ξ₀|) * N ^ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow]
    have a1 : |c| ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (abs_nonneg c) hc 2
    have a2 : |τ| * |c| ≤ N ^ 2 := by
      exact (mul_le_mul hτ hc (abs_nonneg _) hN0).trans (by nlinarith)
    nlinarith [abs_nonneg ξ₀]
  refine ⟨?_, ?_, ?_⟩
  · have e : (gevThetaOf ξ₀ μ₀ σ₀ ((ξ₀, 0, 1) + (τ, b, c))).2.1 - μ₀ -
        gevEtaJ ξ₀ σ₀ (τ, b, c) 0 = σ₀ / ξ₀ * ((c + b) * c) * (1 / (1 + c)) := by
      simp only [gevThetaOf, gevEtaJ, Prod.mk_add_mk, Matrix.cons_val_zero]
      field_simp
      ring
    rw [e, abs_mul, abs_mul, abs_mul]
    have : |c + b| * |c| * |1 / (1 + c)| ≤ N ^ 2 * 2 :=
      mul_le_mul hcb hinv (abs_nonneg _) (sq_nonneg _)
    calc A * (|c + b| * |c|) * |1 / (1 + c)| = A * (|c + b| * |c| * |1 / (1 + c)|) := by ring
      _ ≤ A * (N ^ 2 * 2) := mul_le_mul_of_nonneg_left this hA0
      _ ≤ _ := by
        have := mul_nonneg hA0 (sq_nonneg N)
        have h5 := abs_nonneg ξ₀
        nlinarith
  · have e : (gevThetaOf ξ₀ μ₀ σ₀ ((ξ₀, 0, 1) + (τ, b, c))).2.2 - σ₀ -
        gevEtaJ ξ₀ σ₀ (τ, b, c) 1 = σ₀ / ξ₀ * (ξ₀ * c ^ 2 - τ * c) * (1 / (1 + c)) := by
      simp only [gevThetaOf, gevEtaJ, Prod.mk_add_mk, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
      ring
    rw [e, abs_mul, abs_mul]
    have : |ξ₀ * c ^ 2 - τ * c| * |1 / (1 + c)| ≤ (1 + |ξ₀|) * N ^ 2 * 2 :=
      mul_le_mul hcτ hinv (abs_nonneg _) (by positivity)
    calc A * |ξ₀ * c ^ 2 - τ * c| * |1 / (1 + c)| = A * (|ξ₀ * c ^ 2 - τ * c| * |1 / (1 + c)|) := by
          ring
      _ ≤ A * ((1 + |ξ₀|) * N ^ 2 * 2) := mul_le_mul_of_nonneg_left this hA0
      _ = _ := by ring
  · simp [gevThetaOf, gevEtaJ]

end Change

/-! ### The derivatives at the truth -/

section Truth

variable {ξ₀ μ₀ σ₀ x : ℝ}

/-- At the truth, `u = v`. -/
@[simp] lemma gevEtaU_self (ξ₀ v : ℝ) : gevEtaU (ξ₀, 0, 1) v = v := by simp [gevEtaU]

private lemma exp_gevEtaY_self {v : ℝ} (hv : 0 < v) :
    exp (gevEtaY (ξ₀, 0, 1) v) = v ^ (-1 / ξ₀) := by
  rw [rpow_def_of_pos hv]
  simp only [gevEtaY, gevEtaU_self]
  congr 1
  ring

/-- **At the truth, the derivative in the direction `d` is the score in the direction `J d`.** -/
theorem gevEtaD_self_eq (hξ₀ : ξ₀ ≠ 0) (hσ₀ : σ₀ ≠ 0) (hv : 0 < gevU ξ₀ μ₀ σ₀ x)
    (d : ℝ × ℝ × ℝ) :
    gevEtaD (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ x) d = gevEtaJ ξ₀ σ₀ d ⬝ᵥ gevScore ξ₀ μ₀ σ₀ x := by
  rw [dotProduct_gevScore]
  simp only [gevEtaD, gevEtaDY, exp_gevEtaY_self hv]
  simp only [gevEtaY, gevEtaU_self, gevEtaJ, gevScoreMu, gevScoreSigma, gevScoreXi,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  unfold gevU at hv ⊢
  generalize (1 + ξ₀ * ((x - μ₀) / σ₀)) ^ (-1 / ξ₀) = w
  generalize log (1 + ξ₀ * ((x - μ₀) / σ₀)) = L
  generalize hz : (x - μ₀) / σ₀ = z at hv ⊢
  have hv' : 1 + ξ₀ * z ≠ 0 := hv.ne'
  have hv'' : 1 + z * ξ₀ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- **At the truth, the second derivative in terms of the Hessian and the score**: the
derivative of `θ(η)` enters through the Jacobian `J`, its second derivative through
`gevEtaSecond`. -/
theorem gevEtaM_self_eq (hξ₀ : ξ₀ ≠ 0) (hσ₀ : σ₀ ≠ 0) (hv : 0 < gevU ξ₀ μ₀ σ₀ x)
    (d e : ℝ × ℝ × ℝ) :
    gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ x) d e =
      (∑ j, ∑ k, gevEtaJ ξ₀ σ₀ d j * gevEtaJ ξ₀ σ₀ e k * gevHess ξ₀ μ₀ σ₀ x j k) +
        gevEtaSecond ξ₀ σ₀ d e ⬝ᵥ gevScore ξ₀ μ₀ σ₀ x := by
  rw [dotProduct_gevScore]
  simp only [Fin.sum_univ_three, gevEtaM, gevEtaDDY, gevEtaDY, exp_gevEtaY_self hv]
  simp only [gevEtaY, gevEtaU_self, gevEtaJ, gevEtaSecond, gevScoreMu, gevScoreSigma, gevScoreXi,
    gevHess, gevHessMuMu, gevHessMuSigma, gevHessMuXi, gevHessSigmaSigma, gevHessSigmaXi,
    gevHessXiXi, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.empty_val']
  have hzz : (x - μ₀) / σ₀ = (gevU ξ₀ μ₀ σ₀ x - 1) / ξ₀ := by
    unfold gevU
    field_simp
    ring
  have h1z : 1 + ξ₀ * ((x - μ₀) / σ₀) = gevU ξ₀ μ₀ σ₀ x := rfl
  rw [h1z, hzz]
  generalize gevU ξ₀ μ₀ σ₀ x ^ (-1 / ξ₀) = w
  generalize log (gevU ξ₀ μ₀ σ₀ x) = L
  generalize gevU ξ₀ μ₀ σ₀ x = u at hv
  have hu : u ≠ 0 := hv.ne'
  field_simp
  ring

end Truth

/-! ### The information identity in the coordinates `η` -/

section Information

variable {ξ₀ μ₀ σ₀ : ℝ}

lemma integrable_gevHess_entry (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀) (j k : Fin 3) :
    Integrable (fun x => gevHess ξ₀ μ₀ σ₀ x j k) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure := by
  fin_cases j <;> fin_cases k <;>
    simp only [gevHess, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
  · exact integrable_gevHessMuMu hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessMuSigma hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessMuXi hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessMuSigma hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessSigmaSigma hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessSigmaXi hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessMuXi hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessSigmaXi hσ₀ hξ₀0 hξ₀
  · exact integrable_gevHessXiXi hσ₀ hξ₀0 hξ₀

lemma integrable_dotProduct_gevScore (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀)
    (f : Fin 3 → ℝ) :
    Integrable (fun x => f ⬝ᵥ gevScore ξ₀ μ₀ σ₀ x) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure :=
  (memLp_dotProduct_gevScore hσ₀ hξ₀0 hξ₀ f).integrable one_le_two

/-- The quadratic form `(J d)ᵀ I(θ₀) (J e)`. -/
noncomputable def gevEtaInfo (ξ₀ σ₀ : ℝ) (d e : ℝ × ℝ × ℝ) : ℝ :=
  gevEtaJ ξ₀ σ₀ d ⬝ᵥ (gevFisherInfo ξ₀ σ₀).mulVec (gevEtaJ ξ₀ σ₀ e)

/-- **The information identity in the coordinates `η`**:
`E[M(η₀, v)[d, e]] = -(J d)ᵀ I(θ₀) (J e)`. -/
theorem integral_gevEtaM_self (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀)
    (d e : ℝ × ℝ × ℝ) :
    ∫ x, gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ x) d e ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure =
      -gevEtaInfo ξ₀ σ₀ d e := by
  have hae : (fun x => gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ x) d e) =ᵐ[(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure]
      fun x => (∑ j, ∑ k, gevEtaJ ξ₀ σ₀ d j * gevEtaJ ξ₀ σ₀ e k * gevHess ξ₀ μ₀ σ₀ x j k) +
        gevEtaSecond ξ₀ σ₀ d e ⬝ᵥ gevScore ξ₀ μ₀ σ₀ x := by
    filter_upwards [ae_gevU_pos hξ₀0 hσ₀] with x hx
    exact gevEtaM_self_eq hξ₀0 hσ₀.ne' hx d e
  have hH := integrable_gevHess_entry (μ₀ := μ₀) hσ₀ hξ₀0 hξ₀
  have hI : Integrable (fun x => ∑ j, ∑ k, gevEtaJ ξ₀ σ₀ d j * gevEtaJ ξ₀ σ₀ e k *
      gevHess ξ₀ μ₀ σ₀ x j k) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hH j k).const_mul _
  rw [integral_congr_ae hae, integral_add hI (integrable_dotProduct_gevScore hσ₀ hξ₀0 hξ₀ _),
    integral_dotProduct_gevScore hσ₀ hξ₀0 hξ₀, add_zero,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hH j k).const_mul _]
  have hin : ∀ j, ∫ x, ∑ k, gevEtaJ ξ₀ σ₀ d j * gevEtaJ ξ₀ σ₀ e k * gevHess ξ₀ μ₀ σ₀ x j k
      ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure =
      ∑ k, gevEtaJ ξ₀ σ₀ d j * gevEtaJ ξ₀ σ₀ e k * -gevFisherInfo ξ₀ σ₀ j k := fun j => by
    rw [integral_finsetSum _ fun k _ => (hH j k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_gevHess_eq_neg_gevFisherInfo hσ₀ hξ₀0 hξ₀]
  have hE : gevEtaInfo ξ₀ σ₀ d e = ∑ j, ∑ k, gevEtaJ ξ₀ σ₀ d j * gevEtaJ ξ₀ σ₀ e k *
      gevFisherInfo ξ₀ σ₀ j k := by
    simp only [gevEtaInfo, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hin, hE, mul_neg, Finset.sum_neg_distrib]

/-- A positive definite matrix is uniformly positive, in the `ℓ¹` norm. -/
lemma exists_le_dotProduct_mulVec {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : Fin 3 → ℝ, c * (∑ j, |f j|) ^ 2 ≤ f ⬝ᵥ A.mulVec f := by
  set S : Set (Fin 3 → ℝ) := {f | ∑ j, |f j| = 1} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq (by fun_prop) continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin 3 → ℝ)) (r := 1)).subset fun f hf => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [Real.norm_eq_abs]
    calc |f j| ≤ ∑ j, |f j| :=
          Finset.single_le_sum (f := fun j => |f j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ = 1 := hf
  have hSne : S.Nonempty := ⟨![1, 0, 0], by simp [hS, Fin.sum_univ_three]⟩
  have hc : Continuous fun f : Fin 3 → ℝ => f ⬝ᵥ A.mulVec f := by fun_prop
  obtain ⟨f₀, hf₀, hmin⟩ := hSc.exists_isMinOn hSne hc.continuousOn
  have hne : f₀ ≠ 0 := fun h => by
    have : ∑ j, |f₀ j| = 1 := hf₀
    simp [h] at this
  have hpos : 0 < f₀ ⬝ᵥ A.mulVec f₀ := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hA).2 hne
    simpa using this
  refine ⟨_, hpos, fun f => ?_⟩
  set N := ∑ j, |f j| with hN
  rcases (show 0 ≤ N by positivity).eq_or_lt with h | h
  · rw [← h]
    have hf : f = 0 := by
      funext j
      have : |f j| ≤ N := Finset.single_le_sum (f := fun j => |f j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
      rw [← h] at this
      simpa using this
    simp [hf]
  · have hg : N⁻¹ • f ∈ S := by
      simp only [hS, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 h),
        ← Finset.mul_sum, ← hN, inv_mul_cancel₀ h.ne']
    have h1 := hmin hg
    simp only [mem_ofPred_eq, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h1
    have h2 : N ^ 2 * (N⁻¹ * (N⁻¹ * (f ⬝ᵥ A.mulVec f))) = f ⬝ᵥ A.mulVec f := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg N)
    rw [h2] at h3
    linarith

/-- **The information form is uniformly negative definite in the coordinates `η`**: there is
`λ > 0` with `-(J d)ᵀ I(θ₀) (J d) ≤ -λ |d|²` for all `d`, for `ξ₀ > -1/2`, `ξ₀ ≠ 0`. -/
theorem exists_gevEtaInfo_ge (hσ₀ : 0 < σ₀) (hξ₀0 : ξ₀ ≠ 0) (hξ₀ : -1 / 2 < ξ₀) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ d : ℝ × ℝ × ℝ, lam * gevEtaNorm d ^ 2 ≤ gevEtaInfo ξ₀ σ₀ d d := by
  obtain ⟨c, hc, hle⟩ := exists_le_dotProduct_mulVec (posDef_gevFisherInfo hσ₀ hξ₀0 hξ₀)
  -- `|d| ≤ C |J d|`
  set C := 1 + 1 / |ξ₀| + 1 / σ₀ + |ξ₀| / σ₀ with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ 1 / |ξ₀| := by positivity
    have : 0 ≤ 1 / σ₀ := by positivity
    have : 0 ≤ |ξ₀| / σ₀ := by positivity
    rw [hC]
    linarith
  refine ⟨c / (2 * C) ^ 2, by positivity, fun d => ?_⟩
  set f := gevEtaJ ξ₀ σ₀ d with hf
  have hd : d = gevEtaJInv ξ₀ σ₀ f := (gevEtaJInv_gevEtaJ hξ₀0 hσ₀.ne' d).symm
  have hF := hle f
  have hF0 : 0 ≤ ∑ j, |f j| := by positivity
  have hsum : ∑ j, |f j| = |f 0| + |f 1| + |f 2| := Fin.sum_univ_three _
  have hnorm : gevEtaNorm d ≤ 2 * C * ∑ j, |f j| := by
    rw [hd, hsum]
    simp only [gevEtaNorm, gevEtaJInv]
    have ha : 0 < |ξ₀| := abs_pos.2 hξ₀0
    have h0 := abs_nonneg (f 0)
    have h1 := abs_nonneg (f 1)
    have h2 := abs_nonneg (f 2)
    have hc1 : |f 2 / ξ₀ - f 1 / σ₀| ≤ |f 2| / |ξ₀| + |f 1| / σ₀ := by
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_div, abs_of_pos hσ₀]
    have hc2 : |ξ₀ * f 0 / σ₀| = |ξ₀| / σ₀ * |f 0| := by
      rw [abs_div, abs_mul, abs_of_pos hσ₀]
      ring
    have hc3 : |-(f 2 / ξ₀ - f 1 / σ₀) - ξ₀ * f 0 / σ₀| ≤
        |f 2| / |ξ₀| + |f 1| / σ₀ + |ξ₀| / σ₀ * |f 0| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_neg, hc2]
      linarith
    have p1 : 0 ≤ 1 / |ξ₀| := by positivity
    have p2 : 0 ≤ 1 / σ₀ := by positivity
    have p3 : 0 ≤ |ξ₀| / σ₀ := by positivity
    have e1 : |f 2| / |ξ₀| = 1 / |ξ₀| * |f 2| := by ring
    have e2 : |f 1| / σ₀ = 1 / σ₀ * |f 1| := by ring
    rw [e1, e2] at hc1 hc3
    have b : 2 * C * (|f 0| + |f 1| + |f 2|) =
        2 * (|f 0| + |f 1| + |f 2|) + 2 * (1 / |ξ₀|) * (|f 0| + |f 1| + |f 2|) +
          2 * (1 / σ₀) * (|f 0| + |f 1| + |f 2|) +
          2 * (|ξ₀| / σ₀) * (|f 0| + |f 1| + |f 2|) := by
      rw [hC]
      ring
    rw [b]
    nlinarith [mul_nonneg p1 h0, mul_nonneg p1 h1, mul_nonneg p1 h2, mul_nonneg p2 h0,
      mul_nonneg p2 h1, mul_nonneg p2 h2, mul_nonneg p3 h0, mul_nonneg p3 h1, mul_nonneg p3 h2]
  have h2 : gevEtaNorm d ^ 2 ≤ (2 * C) ^ 2 * (∑ j, |f j|) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (gevEtaNorm_nonneg d) hnorm 2
  simp only [gevEtaInfo, ← hf]
  refine le_trans ?_ hF
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : c * gevEtaNorm d ^ 2 ≤ c * ((2 * C) ^ 2 * (∑ j, |f j|) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hc.le
  linarith

end Information

end ExtremeValueTheory
