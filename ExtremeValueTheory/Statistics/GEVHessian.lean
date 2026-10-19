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
private lemma hasDerivAt_uw_mu (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
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
private lemma hasDerivAt_uw_sigma (hσ : 0 < σ) (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
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
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_mu (μ := μ) (σ := σ) hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const μ (1 + ξ)).sub hW).div (hU.const_mul σ) (mul_ne_zero hσ.ne' hu.ne')
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply]
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
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_sigma (μ := μ) (x := x) hσ hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const σ (1 + ξ)).sub hW).div ((hasDerivAt_id σ).mul hU) (mul_ne_zero hσ.ne' hu.ne')
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, id]
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
  simp only [Pi.sub_apply, id]
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
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_mu (μ := μ) (σ := σ) hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const μ 1).add ((hz.mul ((hW.sub_const 1).sub_const ξ)).div hU hu.ne')).neg.div_const σ
  refine hd.congr_deriv ?_
  simp only [Pi.mul_apply]
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
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_sigma (μ := μ) (x := x) hσ hu
  have hL := hU.log hu.ne'
  have hd := ((hasDerivAt_const σ 1).add ((hz.mul ((hW.sub_const 1).sub_const ξ)).div hU hu.ne')).neg.div (hasDerivAt_id σ) hσ.ne'
  refine hd.congr_deriv ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id]
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
  simp only [Pi.sub_apply, Pi.mul_apply, id]
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
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_mu (μ := μ) (σ := σ) hu
  have hL := hU.log hu.ne'
  have hd := (((hL.div_const (ξ ^ 2)).sub ((hz.div hU hu.ne').const_mul (1 / ξ + 1))).sub (hW.mul ((hL.div_const (ξ ^ 2)).sub (hz.div (hU.const_mul ξ) (mul_ne_zero hξ hu.ne')))))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.div_apply]
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
  obtain ⟨hU, hW, hz⟩ := hasDerivAt_uw_sigma (μ := μ) (x := x) hσ hu
  have hL := hU.log hu.ne'
  have hd := (((hL.div_const (ξ ^ 2)).sub ((hz.div hU hu.ne').const_mul (1 / ξ + 1))).sub (hW.mul ((hL.div_const (ξ ^ 2)).sub (hz.div (hU.const_mul ξ) (mul_ne_zero hξ hu.ne')))))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.div_apply]
  rw [gevHessSigmaXi, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

omit hσ in
theorem hasDerivAt_gevScoreXi_xi :
    HasDerivAt (fun k => gevScoreXi k μ σ x) (gevHessXiXi ξ μ σ x) ξ := by
  obtain ⟨hU, hW, hI⟩ := hasDerivAt_uw_xi (μ := μ) (σ := σ) (x := x) hξ hu
  have hL := hU.log hu.ne'
  have hS : HasDerivAt (fun k : ℝ => k ^ 2) (2 * ξ) ξ := by simpa using hasDerivAt_pow 2 ξ
  have hz := hasDerivAt_const ξ ((x - μ) / σ)
  have hd := (((hL.div hS (pow_ne_zero 2 hξ)).sub ((hI.add_const 1).mul (hz.div hU hu.ne'))).sub (hW.mul ((hL.div hS (pow_ne_zero 2 hξ)).sub (hz.div ((hasDerivAt_id ξ).mul hU) (mul_ne_zero hξ hu.ne')))))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id]
  rw [gevHessXiXi, gevU, rpow_sub_one hu.ne']
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w
  generalize log (1 + ξ * ((x - μ) / σ)) = L
  generalize (x - μ) / σ = z at hu ⊢
  have hu0 : 1 + ξ * z ≠ 0 := hu.ne'
  have hu2 : 1 + z * ξ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

end Derivatives

/-! ### The information identity -/

section InformationIdentity

variable {ξ μ σ : ℝ}

lemma gevU_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevU ξ μ σ (μ + σ * gevTransform ξ t) = t ^ (-ξ) := by
  have hz : (μ + σ * gevTransform ξ t - μ) / σ = gevTransform ξ t := by
    field_simp; ring
  rw [gevU, hz, one_add_mul_gevTransform hξ ht]

lemma gevHessMuMu_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevHessMuMu ξ μ σ (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ 0 0 0 0 0 0 (ξ * (ξ + 1) / σ ^ 2) ((-ξ - 1) / σ ^ 2) 0 0 0 0 0 0 0 0 0 0 t := by
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevHessMuMu, gevU_transform hσ hξ ht, rpow_neg_rpow_neg_one_div hξ ht]
  simp only [rpow_neg ht.le, gevLogPoly, gevPoly]
  field_simp
  ring

/-- The expected Hessian entry `E[∂²ℓ]` is minus the Fisher information entry. -/
theorem integral_gevHessMuMu (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    ∫ x, gevHessMuMu ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure =
      -gevFisherInfo ξ σ 0 0 := by
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessMuMu ξ μ σ)
    (fun _ ht => gevHessMuMu_transform hσ hξ0 ht)]
  have h1ξ : 0 < 1 + ξ := by linarith
  have hG : Gamma (1 + ξ) ≠ 0 := (Gamma_pos_of_pos h1ξ).ne'
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one h1ξ.ne']
  simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val, Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one]
  try simp only [gevInfoP]
  try simp only [show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  field_simp
  ring

lemma integrable_gevHessMuMu (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    Integrable (gevHessMuMu ξ μ σ) (gevLocScaleCDF ξ μ hσ).measure :=
  integrable_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessMuMu ξ μ σ)
    (fun _ ht => gevHessMuMu_transform hσ hξ0 ht)

lemma gevHessMuSigma_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevHessMuSigma ξ μ σ (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ 0 0 0 0 (-1 / (σ ^ 2 * ξ)) 0 ((-ξ - 1) / σ ^ 2) ((ξ + 1) / (σ ^ 2 * ξ)) 0 0 0 0 0 0 0 0 0 0 t := by
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevHessMuSigma, gevU_transform hσ hξ ht, rpow_neg_rpow_neg_one_div hξ ht]
  simp only [rpow_neg ht.le, gevLogPoly, gevPoly]
  field_simp
  ring

/-- The expected Hessian entry `E[∂²ℓ]` is minus the Fisher information entry. -/
theorem integral_gevHessMuSigma (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    ∫ x, gevHessMuSigma ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure =
      -gevFisherInfo ξ σ 0 1 := by
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessMuSigma ξ μ σ)
    (fun _ ht => gevHessMuSigma_transform hσ hξ0 ht)]
  have h1ξ : 0 < 1 + ξ := by linarith
  have hG : Gamma (1 + ξ) ≠ 0 := (Gamma_pos_of_pos h1ξ).ne'
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one h1ξ.ne']
  simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val, Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one]
  try simp only [gevInfoP, g2]
  try simp only [show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  field_simp
  ring

lemma integrable_gevHessMuSigma (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    Integrable (gevHessMuSigma ξ μ σ) (gevLocScaleCDF ξ μ hσ).measure :=
  integrable_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessMuSigma ξ μ σ)
    (fun _ ht => gevHessMuSigma_transform hσ hξ0 ht)

lemma gevHessMuXi_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevHessMuXi ξ μ σ (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ 0 0 0 (-1 / (σ * ξ)) ((ξ + 1) / (σ * ξ ^ 2)) 0 ((ξ + 1) / (σ * ξ)) ((-ξ - 1) / (σ * ξ ^ 2)) 0 0 0 0 0 (1 / (σ * ξ)) 0 0 0 0 t := by
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevHessMuXi, gevU_transform hσ hξ ht, rpow_neg_rpow_neg_one_div hξ ht]
  try rw [log_rpow ht]
  simp only [rpow_neg ht.le, gevLogPoly, gevPoly]
  field_simp
  ring

/-- The expected Hessian entry `E[∂²ℓ]` is minus the Fisher information entry. -/
theorem integral_gevHessMuXi (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    ∫ x, gevHessMuXi ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure =
      -gevFisherInfo ξ σ 0 2 := by
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessMuXi ξ μ σ)
    (fun _ ht => gevHessMuXi_transform hσ hξ0 ht)]
  have h1ξ : 0 < 1 + ξ := by linarith
  have hG : Gamma (1 + ξ) ≠ 0 := (Gamma_pos_of_pos h1ξ).ne'
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one h1ξ.ne']
  simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val, Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one]
  try simp only [gevInfoQ, gevInfoP, realDigamma, g2]
  try simp only [show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  field_simp
  ring

lemma integrable_gevHessMuXi (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    Integrable (gevHessMuXi ξ μ σ) (gevLocScaleCDF ξ μ hσ).measure :=
  integrable_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessMuXi ξ μ σ)
    (fun _ ht => gevHessMuXi_transform hσ hξ0 ht)

lemma gevHessSigmaSigma_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevHessSigmaSigma ξ μ σ (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ (-1 / (σ ^ 2 * ξ)) ((ξ - 1) / (σ ^ 2 * ξ ^ 2)) 0 0 (2 / (σ ^ 2 * ξ ^ 2)) 0 ((ξ + 1) / (σ ^ 2 * ξ)) ((-ξ - 1) / (σ ^ 2 * ξ ^ 2)) 0 0 0 0 0 0 0 0 0 0 t := by
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevHessSigmaSigma, gevU_transform hσ hξ ht, rpow_neg_rpow_neg_one_div hξ ht]
  simp only [rpow_neg ht.le, gevLogPoly, gevPoly]
  field_simp
  ring

/-- The expected Hessian entry `E[∂²ℓ]` is minus the Fisher information entry. -/
theorem integral_gevHessSigmaSigma (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    ∫ x, gevHessSigmaSigma ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure =
      -gevFisherInfo ξ σ 1 1 := by
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessSigmaSigma ξ μ σ)
    (fun _ ht => gevHessSigmaSigma_transform hσ hξ0 ht)]
  have h1ξ : 0 < 1 + ξ := by linarith
  have hG : Gamma (1 + ξ) ≠ 0 := (Gamma_pos_of_pos h1ξ).ne'
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one h1ξ.ne']
  simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val, Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one]
  try simp only [gevInfoP, g2]
  try simp only [show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  field_simp
  ring

lemma integrable_gevHessSigmaSigma (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    Integrable (gevHessSigmaSigma ξ μ σ) (gevLocScaleCDF ξ μ hσ).measure :=
  integrable_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessSigmaSigma ξ μ σ)
    (fun _ ht => gevHessSigmaSigma_transform hσ hξ0 ht)

lemma gevHessSigmaXi_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevHessSigmaXi ξ μ σ (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ (-1 / (σ * ξ ^ 2)) ((ξ + 1) / (σ * ξ ^ 3)) 0 ((ξ + 2) / (σ * ξ ^ 2)) (2 * (-ξ - 1) / (σ * ξ ^ 3)) 0 ((-ξ - 1) / (σ * ξ ^ 2)) ((ξ + 1) / (σ * ξ ^ 3)) 0 0 (1 / (σ * ξ ^ 2)) 0 0 (-1 / (σ * ξ ^ 2)) 0 0 0 0 t := by
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevHessSigmaXi, gevU_transform hσ hξ ht, rpow_neg_rpow_neg_one_div hξ ht]
  try rw [log_rpow ht]
  simp only [rpow_neg ht.le, gevLogPoly, gevPoly]
  field_simp
  ring

/-- The expected Hessian entry `E[∂²ℓ]` is minus the Fisher information entry. -/
theorem integral_gevHessSigmaXi (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    ∫ x, gevHessSigmaXi ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure =
      -gevFisherInfo ξ σ 1 2 := by
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessSigmaXi ξ μ σ)
    (fun _ ht => gevHessSigmaXi_transform hσ hξ0 ht)]
  have h1ξ : 0 < 1 + ξ := by linarith
  have hG : Gamma (1 + ξ) ≠ 0 := (Gamma_pos_of_pos h1ξ).ne'
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one h1ξ.ne']
  simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val, Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one]
  try simp only [gevInfoQ, gevInfoP, realDigamma, g2]
  try simp only [show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  field_simp
  ring

lemma integrable_gevHessSigmaXi (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    Integrable (gevHessSigmaXi ξ μ σ) (gevLocScaleCDF ξ μ hσ).measure :=
  integrable_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessSigmaXi ξ μ σ)
    (fun _ ht => gevHessSigmaXi_transform hσ hξ0 ht)

lemma gevHessXiXi_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevHessXiXi ξ μ σ (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ ((ξ + 3) / ξ ^ 3) ((-3 * ξ - 1) / ξ ^ 4) 0 (2 * (-ξ - 2) / ξ ^ 3) (2 * (2 * ξ + 1) / ξ ^ 4) 0 ((ξ + 1) / ξ ^ 3) ((-ξ - 1) / ξ ^ 4) 0 (2 / ξ ^ 2) (2 * (-ξ - 1) / ξ ^ 3) 0 0 (2 / ξ ^ 3) 0 0 (-1 / ξ ^ 2) 0 t := by
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevHessXiXi, gevU_transform hσ hξ ht, rpow_neg_rpow_neg_one_div hξ ht]
  try rw [log_rpow ht]
  simp only [rpow_neg ht.le, gevLogPoly, gevPoly]
  field_simp
  ring

/-- The expected Hessian entry `E[∂²ℓ]` is minus the Fisher information entry. -/
theorem integral_gevHessXiXi (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    ∫ x, gevHessXiXi ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure =
      -gevFisherInfo ξ σ 2 2 := by
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessXiXi ξ μ σ)
    (fun _ ht => gevHessXiXi_transform hσ hξ0 ht)]
  have h1ξ : 0 < 1 + ξ := by linarith
  have hG : Gamma (1 + ξ) ≠ 0 := (Gamma_pos_of_pos h1ξ).ne'
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one h1ξ.ne']
  simp only [gevFisherInfo, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val, Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one]
  try simp only [gevInfoQ, gevInfoP, realDigamma, g2]
  try simp only [show ξ + 1 = 1 + ξ by ring, show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  field_simp
  ring

lemma integrable_gevHessXiXi (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    Integrable (gevHessXiXi ξ μ σ) (gevLocScaleCDF ξ μ hσ).measure :=
  integrable_gevLocScaleCDF_of_logPoly hξ hσ (measurable_gevHessXiXi ξ μ σ)
    (fun _ ht => gevHessXiXi_transform hσ hξ0 ht)

/-- The Hessian matrix of the GEV log-density in `(μ, σ, ξ)`. -/
noncomputable def gevHess (ξ μ σ x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![gevHessMuMu ξ μ σ x, gevHessMuSigma ξ μ σ x, gevHessMuXi ξ μ σ x;
    gevHessMuSigma ξ μ σ x, gevHessSigmaSigma ξ μ σ x, gevHessSigmaXi ξ μ σ x;
    gevHessMuXi ξ μ σ x, gevHessSigmaXi ξ μ σ x, gevHessXiXi ξ μ σ x]

/-- **The information identity** (second Bartlett identity) for the GEV family, `ξ > -1/2`,
`ξ ≠ 0`: the expected Hessian of the log-density is minus the Fisher information. -/
theorem integral_gevHess_eq_neg_gevFisherInfo (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ)
    (i j : Fin 3) :
    ∫ x, gevHess ξ μ σ x i j ∂(gevLocScaleCDF ξ μ hσ).measure = -gevFisherInfo ξ σ i j := by
  have h01 := integral_gevHessMuSigma (μ := μ) hσ hξ0 hξ
  have h02 := integral_gevHessMuXi (μ := μ) hσ hξ0 hξ
  have h12 := integral_gevHessSigmaXi (μ := μ) hσ hξ0 hξ
  have s01 : gevFisherInfo ξ σ 1 0 = gevFisherInfo ξ σ 0 1 := by simp [gevFisherInfo]
  have s02 : gevFisherInfo ξ σ 2 0 = gevFisherInfo ξ σ 0 2 := by simp [gevFisherInfo]
  have s12 : gevFisherInfo ξ σ 2 1 = gevFisherInfo ξ σ 1 2 := by simp [gevFisherInfo]
  fin_cases i <;> fin_cases j <;> simp only [gevHess, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.empty_val',
    Matrix.cons_val_fin_one, Fin.isValue]
  · exact integral_gevHessMuMu hσ hξ0 hξ
  · exact h01
  · exact h02
  · rw [h01, s01]
  · exact integral_gevHessSigmaSigma hσ hξ0 hξ
  · exact h12
  · rw [h02, s02]
  · rw [h12, s12]
  · exact integral_gevHessXiXi hσ hξ0 hξ

end InformationIdentity

end ExtremeValueTheory
