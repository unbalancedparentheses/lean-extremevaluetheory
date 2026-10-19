/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVFisherInformation

/-!
# The Hessian of the GEV log-density and the information identity

For `ξ ≠ 0` and a point of the support, write `z = (x - μ)/σ`, `u = 1 + ξ z > 0`,
`w = u^{-1/ξ}` and `L = log u`. The second derivatives of the GEV log-density
`ℓ(μ, σ, ξ; x) = -log σ - (1/ξ + 1) L - w` are rational functions of `(ξ, σ, u, w, L)`:

* `∂²_μ ℓ = (-w + ξ(1 + ξ - w))/(σ² u²)`,
* `∂_μ ∂_σ ℓ = (w(1 + ξ - u) - ξ(1 + ξ))/(ξ σ² u²)`,
* `∂_μ ∂_ξ ℓ = (ξ² u - w(L u - u + 1) - ξ(u - 1)(1 + ξ - w))/(σ ξ² u²)`,
* `∂²_σ ℓ`, `∂_σ ∂_ξ ℓ`, `∂²_ξ ℓ` (`gevHessSigmaSigma`, `gevHessSigmaXi`, `gevHessXiXi`).

We prove that these are the derivatives of the scores (in both orders for the mixed entries,
`hasDerivAt_gevScoreMu_sigma`, `hasDerivAt_gevScoreSigma_mu`, …), compute them on the exponential
scale, and prove the **information identity** (the second Bartlett identity): for `ξ > -1/2`,
`ξ ≠ 0`, every entry of the Hessian is integrable under the true law and its expectation is minus
the corresponding entry of the Fisher information `gevFisherInfo ξ σ`
(`integral_gevHess_eq_neg_gevFisherInfo`).

## References

* D. Prescott and A. T. Walden, *Maximum likelihood estimation of the parameters of the
  generalized extreme-value distribution*, Biometrika 67 (1980).
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### The Hessian -/

section Hessian

variable {ξ μ σ x : ℝ}

/-- `u = 1 + ξ (x - μ)/σ`. -/
noncomputable def gevU (ξ μ σ x : ℝ) : ℝ := 1 + ξ * ((x - μ) / σ)

/-- `∂²_μ ℓ`. -/
noncomputable def gevHessMuMu (ξ μ σ x : ℝ) : ℝ :=
  (-gevU ξ μ σ x ^ (-1 / ξ) + ξ * (-gevU ξ μ σ x ^ (-1 / ξ) + ξ + 1)) /
    (σ ^ 2 * gevU ξ μ σ x ^ 2)

/-- `∂_μ ∂_σ ℓ = ∂_σ ∂_μ ℓ`. -/
noncomputable def gevHessMuSigma (ξ μ σ x : ℝ) : ℝ :=
  (-gevU ξ μ σ x * gevU ξ μ σ x ^ (-1 / ξ) + gevU ξ μ σ x ^ (-1 / ξ) * ξ +
      gevU ξ μ σ x ^ (-1 / ξ) - ξ ^ 2 - ξ) / (σ ^ 2 * gevU ξ μ σ x ^ 2 * ξ)

/-- `∂_μ ∂_ξ ℓ = ∂_ξ ∂_μ ℓ`. -/
noncomputable def gevHessMuXi (ξ μ σ x : ℝ) : ℝ :=
  (gevU ξ μ σ x * ξ ^ 2 - gevU ξ μ σ x ^ (-1 / ξ) *
      (log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) -
      ξ * (gevU ξ μ σ x - 1) * (-gevU ξ μ σ x ^ (-1 / ξ) + ξ + 1)) /
    (σ * gevU ξ μ σ x ^ 2 * ξ ^ 2)

/-- `∂²_σ ℓ`. -/
noncomputable def gevHessSigmaSigma (ξ μ σ x : ℝ) : ℝ :=
  (gevU ξ μ σ x ^ 2 * gevU ξ μ σ x ^ (-1 / ξ) * ξ - gevU ξ μ σ x ^ 2 * gevU ξ μ σ x ^ (-1 / ξ) -
      gevU ξ μ σ x ^ 2 * ξ + 2 * gevU ξ μ σ x * gevU ξ μ σ x ^ (-1 / ξ) -
      gevU ξ μ σ x ^ (-1 / ξ) * ξ - gevU ξ μ σ x ^ (-1 / ξ) + ξ ^ 2 + ξ) /
    (σ ^ 2 * gevU ξ μ σ x ^ 2 * ξ ^ 2)

/-- `∂_σ ∂_ξ ℓ = ∂_ξ ∂_σ ℓ`. -/
noncomputable def gevHessSigmaXi (ξ μ σ x : ℝ) : ℝ :=
  (gevU ξ μ σ x - 1) * (gevU ξ μ σ x * ξ ^ 2 - gevU ξ μ σ x ^ (-1 / ξ) *
      (log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) +
      ξ * (gevU ξ μ σ x - 1) * (gevU ξ μ σ x ^ (-1 / ξ) - ξ - 1)) /
    (σ * gevU ξ μ σ x ^ 2 * ξ ^ 3)

/-- `∂²_ξ ℓ`. -/
noncomputable def gevHessXiXi (ξ μ σ x : ℝ) : ℝ :=
  (-2 * log (gevU ξ μ σ x) * gevU ξ μ σ x ^ 2 * ξ +
      gevU ξ μ σ x * gevU ξ μ σ x ^ (-1 / ξ) * ξ *
        (2 * log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) +
      gevU ξ μ σ x * ξ * (gevU ξ μ σ x - (gevU ξ μ σ x - 1) * (gevU ξ μ σ x ^ (-1 / ξ) - 1) - 1) -
      gevU ξ μ σ x ^ (-1 / ξ) * (log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) ^ 2 -
      ξ * (gevU ξ μ σ x - 1) ^ 2 * (gevU ξ μ σ x ^ (-1 / ξ) - ξ - 1)) /
    (gevU ξ μ σ x ^ 2 * ξ ^ 4)

lemma measurable_gevU (ξ μ σ : ℝ) : Measurable (gevU ξ μ σ) := by unfold gevU; fun_prop

lemma measurable_gevHessMuMu (ξ μ σ : ℝ) : Measurable (gevHessMuMu ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessMuMu; fun_prop

lemma measurable_gevHessMuSigma (ξ μ σ : ℝ) : Measurable (gevHessMuSigma ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessMuSigma; fun_prop

lemma measurable_gevHessMuXi (ξ μ σ : ℝ) : Measurable (gevHessMuXi ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessMuXi; fun_prop

lemma measurable_gevHessSigmaSigma (ξ μ σ : ℝ) : Measurable (gevHessSigmaSigma ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessSigmaSigma; fun_prop

lemma measurable_gevHessSigmaXi (ξ μ σ : ℝ) : Measurable (gevHessSigmaXi ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessSigmaXi; fun_prop

lemma measurable_gevHessXiXi (ξ μ σ : ℝ) : Measurable (gevHessXiXi ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessXiXi; fun_prop

end Hessian

/-! ### The Hessian is the derivative of the score -/

section Derivatives

variable {ξ μ σ x : ℝ}

/-- Derivatives of `u` and `w = u^{-1/ξ}` in the location. -/
private lemma hasDerivAt_uw_mu (hξ : ξ ≠ 0) (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    HasDerivAt (fun m => 1 + ξ * ((x - m) / σ)) (-ξ / σ) μ ∧
    HasDerivAt (fun m => (1 + ξ * ((x - m) / σ)) ^ (-1 / ξ))
      (-ξ / σ * (-1 / ξ) * (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ - 1)) μ ∧
    HasDerivAt (fun m => (x - m) / σ) (-1 / σ) μ := by
  have hz : HasDerivAt (fun m => (x - m) / σ) (-1 / σ) μ := by
    simpa [neg_div] using ((hasDerivAt_id μ).const_sub x).div_const σ
  have hU : HasDerivAt (fun m => 1 + ξ * ((x - m) / σ)) (-ξ / σ) μ := by
    have := (hz.const_mul ξ).const_add 1
    convert this using 1; ring
  exact ⟨hU, hU.rpow_const (Or.inl hu.ne'), hz⟩

/-- Derivatives of `z`, `u` and `w = u^{-1/ξ}` in the scale. -/
private lemma hasDerivAt_uw_sigma (hσ : 0 < σ) (hξ : ξ ≠ 0) (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    HasDerivAt (fun s => 1 + ξ * ((x - μ) / s)) (ξ * (-((x - μ) / σ) / σ)) σ ∧
    HasDerivAt (fun s => (1 + ξ * ((x - μ) / s)) ^ (-1 / ξ))
      (ξ * (-((x - μ) / σ) / σ) * (-1 / ξ) * (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ - 1)) σ ∧
    HasDerivAt (fun s => (x - μ) / s) (-((x - μ) / σ) / σ) σ := by
  have hz : HasDerivAt (fun s => (x - μ) / s) (-((x - μ) / σ) / σ) σ := by
    have := (hasDerivAt_inv hσ.ne').const_mul (x - μ)
    convert this using 1
    · funext s; rw [div_eq_mul_inv]
    · field_simp
  have hU := (hz.const_mul ξ).const_add 1
  exact ⟨hU, hU.rpow_const (Or.inl hu.ne'), hz⟩

/-- Derivatives of `u`, `w = u^{-1/ξ}` and the coefficients in the shape. -/
private lemma hasDerivAt_uw_xi (hξ : ξ ≠ 0) (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    HasDerivAt (fun k => 1 + k * ((x - μ) / σ)) ((x - μ) / σ) ξ ∧
    HasDerivAt (fun k => (1 + k * ((x - μ) / σ)) ^ (-1 / k))
      ((x - μ) / σ * (-1 / ξ) * (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ - 1) +
        1 / ξ ^ 2 * (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) * log (1 + ξ * ((x - μ) / σ))) ξ ∧
    HasDerivAt (fun k => 1 / k) (-(1 / ξ ^ 2)) ξ := by
  have hU : HasDerivAt (fun k => 1 + k * ((x - μ) / σ)) ((x - μ) / σ) ξ := by
    simpa using ((hasDerivAt_id ξ).mul_const ((x - μ) / σ)).const_add 1
  have hE : HasDerivAt (fun k => -1 / k) (1 / ξ ^ 2) ξ := by
    have := (hasDerivAt_inv hξ).neg
    convert this using 1
    · funext k; simp [div_eq_mul_inv]
    · field_simp
  have hI : HasDerivAt (fun k => 1 / k) (-(1 / ξ ^ 2)) ξ := by
    simpa [one_div] using hasDerivAt_inv hξ
  exact ⟨hU, hU.rpow hE hu, hI⟩

variable (hσ : 0 < σ) (hξ : ξ ≠ 0) (hu : 0 < 1 + ξ * ((x - μ) / σ))
include hσ hξ hu

theorem hasDerivAt_gevScoreMu_mu :
    HasDerivAt (fun m => gevScoreMu ξ m σ x) (gevHessMuMu ξ μ σ x) μ := by
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_mu (μ := μ) (σ := σ) hξ hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const μ (1 + ξ)).sub hW).div (hU.const_mul σ) (mul_ne_zero hσ.ne' hu.ne')
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessMuMu, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreMu_sigma :
    HasDerivAt (fun s => gevScoreMu ξ μ s x) (gevHessMuSigma ξ μ σ x) σ := by
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_sigma (μ := μ) (x := x) hσ hξ hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const σ (1 + ξ)).sub hW).div ((hasDerivAt_id σ).mul hU) (mul_ne_zero hσ.ne' hu.ne')
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessMuSigma, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreMu_xi :
    HasDerivAt (fun k => gevScoreMu k μ σ x) (gevHessMuXi ξ μ σ x) ξ := by
  obtain ⟨hU, hW, hI⟩ := hasDerivAt_uw_xi (μ := μ) (σ := σ) (x := x) hξ hu
  have hL := hU.log hu.ne'
  have hS : HasDerivAt (fun k : ℝ => k ^ 2) (2 * ξ) ξ := by simpa using hasDerivAt_pow 2 ξ
  have hz := hasDerivAt_const ξ ((x - μ) / σ)
  have hd := (((hasDerivAt_id ξ).const_add 1).sub hW).div (hU.const_mul σ) (mul_ne_zero hσ.ne' hu.ne')
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessMuXi, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreSigma_mu :
    HasDerivAt (fun m => gevScoreSigma ξ m σ x) (gevHessMuSigma ξ μ σ x) μ := by
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_mu (μ := μ) (σ := σ) hξ hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const μ 1).add ((hz.mul ((hW.sub_const 1).sub_const ξ)).div hU hu.ne')).neg.div_const σ
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessMuSigma, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreSigma_sigma :
    HasDerivAt (fun s => gevScoreSigma ξ μ s x) (gevHessSigmaSigma ξ μ σ x) σ := by
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_sigma (μ := μ) (x := x) hσ hξ hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const σ 1).add ((hz.mul ((hW.sub_const 1).sub_const ξ)).div hU hu.ne')).neg.div (hasDerivAt_id σ) hσ.ne'
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessSigmaSigma, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreSigma_xi :
    HasDerivAt (fun k => gevScoreSigma k μ σ x) (gevHessSigmaXi ξ μ σ x) ξ := by
  obtain ⟨hU, hW, hI⟩ := hasDerivAt_uw_xi (μ := μ) (σ := σ) (x := x) hξ hu
  have hL := hU.log hu.ne'
  have hS : HasDerivAt (fun k : ℝ => k ^ 2) (2 * ξ) ξ := by simpa using hasDerivAt_pow 2 ξ
  have hz := hasDerivAt_const ξ ((x - μ) / σ)
  have hd := ((hasDerivAt_const ξ 1).add ((hz.mul ((hW.sub_const 1).sub (hasDerivAt_id ξ))).div hU hu.ne')).neg.div_const σ
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessSigmaXi, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreXi_mu :
    HasDerivAt (fun m => gevScoreXi ξ m σ x) (gevHessMuXi ξ μ σ x) μ := by
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_mu (μ := μ) (σ := σ) hξ hu
  have hL := hU.log hu.ne'
  have hd := (((hL.div_const (ξ ^ 2)).sub ((hz.div hU hu.ne').const_mul (1 / ξ + 1))).sub (hW.mul ((hL.div_const (ξ ^ 2)).sub (hz.div (hU.const_mul ξ) (mul_ne_zero hξ hu.ne')))))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessMuXi, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreXi_sigma :
    HasDerivAt (fun s => gevScoreXi ξ μ s x) (gevHessSigmaXi ξ μ σ x) σ := by
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_sigma (μ := μ) (x := x) hσ hξ hu
  have hL := hU.log hu.ne'
  have hd := (((hL.div_const (ξ ^ 2)).sub ((hz.div hU hu.ne').const_mul (1 / ξ + 1))).sub (hW.mul ((hL.div_const (ξ ^ 2)).sub (hz.div (hU.const_mul ξ) (mul_ne_zero hξ hu.ne')))))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessSigmaXi, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem hasDerivAt_gevScoreXi_xi :
    HasDerivAt (fun k => gevScoreXi k μ σ x) (gevHessXiXi ξ μ σ x) ξ := by
  obtain ⟨hU, hW, hI⟩ := hasDerivAt_uw_xi (μ := μ) (σ := σ) (x := x) hξ hu
  have hL := hU.log hu.ne'
  have hS : HasDerivAt (fun k : ℝ => k ^ 2) (2 * ξ) ξ := by simpa using hasDerivAt_pow 2 ξ
  have hz := hasDerivAt_const ξ ((x - μ) / σ)
  have hd := (((hL.div hS (pow_ne_zero 2 hξ)).sub ((hI.add_const 1).mul (hz.div hU hu.ne'))).sub (hW.mul ((hL.div hS (pow_ne_zero 2 hξ)).sub (hz.div ((hasDerivAt_id ξ).mul hU) (mul_ne_zero hξ hu.ne')))))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
  rw [gevHessXiXi, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

end Derivatives

end ExtremeValueTheory
