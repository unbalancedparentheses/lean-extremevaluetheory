/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLEEnvelope

/-!
# The GEV log-density, score and Hessian in a common basis

For a shape `ξ ≠ 0` and a point of the support, with `u = 1 + ξ (x - μ)/σ`, `a = 1/u`,
`w = u^{-1/ξ}` and `L = log u`, the GEV log-density, its score and its Hessian are linear
combinations, with coefficients depending only on `(ξ, σ)`, of a few monomials in `(a, w, L)`:

* the log-density: `1, L, w` (`gevLogDensT_eq`);
* the score: `1, a, w, w a, L, w L` (`gevScoreT_eq`);
* the Hessian: `1, a, a², w, w a, w a², L, w L, w L a, w L²` (`gevHessT_eq`).

We index the parameter as `θ = (ξ, μ, σ)` (`gevScoreT`, `gevHessT`; index `0` is the shape).
The representation gives at once

* **bounds** `|ℓ| ≤ C (1 + w)(1 + |L|)`, `|∇ℓ| ≤ C (1 + a)(1 + w)(1 + |L|)`,
  `|∇²ℓ| ≤ C (1 + a)²(1 + w)(1 + |L|)²` with `C` continuous in `(ξ, σ)`; for good observations
  (`ExtremeValueTheory.gevU_comparable`) these weights are bounded by envelopes
  `gevEnv a b u₀` integrable under the true law (`exists_abs_gevHessT_le`,
  `exists_abs_gevScoreT_le`, `exists_abs_gevLogDensT_le`): this is the **domination of the
  Hessian near the moving endpoint**;
* **continuity** of the Hessian as a function of `(ξ, σ, u)` (`continuousOn_gevHessHat`), hence
  its uniform continuity on compact sets of observations inside the support
  (`exists_delta_abs_gevHessT_sub_le`).

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

/-! ### The parameter-ordered score and Hessian -/

section Defs

/-- The score in the parameter order `θ = (ξ, μ, σ)`: `(∂_ξ ℓ, ∂_μ ℓ, ∂_σ ℓ)`. -/
noncomputable def gevScoreT (j : Fin 3) (ξ μ σ x : ℝ) : ℝ :=
  ![gevScoreXi ξ μ σ x, gevScoreMu ξ μ σ x, gevScoreSigma ξ μ σ x] j

/-- The Hessian of the log-density in the parameter order `θ = (ξ, μ, σ)`. -/
noncomputable def gevHessT (j k : Fin 3) (ξ μ σ x : ℝ) : ℝ :=
  !![gevHessXiXi ξ μ σ x, gevHessMuXi ξ μ σ x, gevHessSigmaXi ξ μ σ x;
    gevHessMuXi ξ μ σ x, gevHessMuMu ξ μ σ x, gevHessMuSigma ξ μ σ x;
    gevHessSigmaXi ξ μ σ x, gevHessMuSigma ξ μ σ x, gevHessSigmaSigma ξ μ σ x] j k

/-- The log-density `log(σ⁻¹ h_ξ((x - μ)/σ))`. -/
noncomputable def gevLogDensT (ξ μ σ x : ℝ) : ℝ := log (gevLocScaleDensity ξ μ σ x)

lemma gevHessT_symm (j k : Fin 3) (ξ μ σ x : ℝ) : gevHessT j k ξ μ σ x = gevHessT k j ξ μ σ x := by
  fin_cases j <;> fin_cases k <;> rfl

lemma measurable_gevScoreT (j : Fin 3) (ξ μ σ : ℝ) : Measurable (gevScoreT j ξ μ σ) := by
  fin_cases j
  · exact measurable_gevScoreXi ξ μ σ
  · exact measurable_gevScoreMu ξ μ σ
  · exact measurable_gevScoreSigma ξ μ σ

lemma measurable_gevHessT (j k : Fin 3) (ξ μ σ : ℝ) : Measurable (gevHessT j k ξ μ σ) := by
  fin_cases j <;> fin_cases k
  · exact measurable_gevHessXiXi ξ μ σ
  · exact measurable_gevHessMuXi ξ μ σ
  · exact measurable_gevHessSigmaXi ξ μ σ
  · exact measurable_gevHessMuXi ξ μ σ
  · exact measurable_gevHessMuMu ξ μ σ
  · exact measurable_gevHessMuSigma ξ μ σ
  · exact measurable_gevHessSigmaXi ξ μ σ
  · exact measurable_gevHessMuSigma ξ μ σ
  · exact measurable_gevHessSigmaSigma ξ μ σ

lemma measurable_gevLogDensT (ξ μ σ : ℝ) : Measurable (gevLogDensT ξ μ σ) :=
  (measurable_gevLocScaleDensity ξ μ σ).log

end Defs

/-! ### The bases and the coefficients -/

section Basis

/-- The monomials `1, L, w` of the log-density. -/
noncomputable def gevBasisL (w L : ℝ) : Fin 3 → ℝ := ![1, L, w]

/-- The monomials `1, a, w, w a, L, w L` of the score. -/
noncomputable def gevBasisS (a w L : ℝ) : Fin 6 → ℝ := ![1, a, w, w * a, L, w * L]

/-- The monomials `1, a, a², w, w a, w a², L, w L, w L a, w L²` of the Hessian. -/
noncomputable def gevBasisH (a w L : ℝ) : Fin 10 → ℝ :=
  ![1, a, a ^ 2, w, w * a, w * a ^ 2, L, w * L, w * L * a, w * L ^ 2]

/-- The coefficients of the log-density: `ℓ = -log σ - (1/ξ + 1) L - w`. -/
noncomputable def gevCoefL (ξ σ : ℝ) : Fin 3 → ℝ := ![-log σ, -(1 / ξ + 1), -1]

/-- The coefficients of the score in the basis `gevBasisS`. -/
noncomputable def gevCoefS (j : Fin 3) (ξ σ : ℝ) : Fin 6 → ℝ :=
  ![![-(1 + ξ) / ξ ^ 2, (1 + ξ) / ξ ^ 2, 1 / ξ ^ 2, -1 / ξ ^ 2, 1 / ξ ^ 2, -1 / ξ ^ 2],
    ![0, (1 + ξ) / σ, 0, -1 / σ, 0, 0],
    ![1 / (σ * ξ), -(1 + ξ) / (σ * ξ), -1 / (σ * ξ), 1 / (σ * ξ), 0, 0]] j

/-- The coefficients of the Hessian in the basis `gevBasisH`. -/
noncomputable def gevCoefH (j k : Fin 3) (ξ σ : ℝ) : Fin 10 → ℝ :=
  ![![fun m => ![ξ ^ 2 + 3 * ξ, -2 * ξ ^ 2 - 4 * ξ, ξ * (ξ + 1), -3 * ξ - 1, 4 * ξ + 2, -1 - ξ,
        -2 * ξ, 2 * ξ + 2, -2, -1] m / ξ ^ 4,
      fun m => ![0, -ξ, ξ * (1 + ξ), 0, 1 + ξ, -1 - ξ, 0, 0, -1, 0] m / (σ * ξ ^ 2),
      fun m => ![-ξ, ξ * (2 + ξ), -ξ * (1 + ξ), 1 + ξ, -2 * (1 + ξ), 1 + ξ, 0, -1, 1, 0] m /
        (σ * ξ ^ 3)],
    ![fun m => ![0, -ξ, ξ * (1 + ξ), 0, 1 + ξ, -1 - ξ, 0, 0, -1, 0] m / (σ * ξ ^ 2),
      fun m => ![0, 0, ξ * (ξ + 1), 0, 0, -(1 + ξ), 0, 0, 0, 0] m / σ ^ 2,
      fun m => ![0, 0, -(ξ ^ 2 + ξ), 0, -1, ξ + 1, 0, 0, 0, 0] m / (σ ^ 2 * ξ)],
    ![fun m => ![-ξ, ξ * (2 + ξ), -ξ * (1 + ξ), 1 + ξ, -2 * (1 + ξ), 1 + ξ, 0, -1, 1, 0] m /
        (σ * ξ ^ 3),
      fun m => ![0, 0, -(ξ ^ 2 + ξ), 0, -1, ξ + 1, 0, 0, 0, 0] m / (σ ^ 2 * ξ),
      fun m => ![-ξ, 0, ξ ^ 2 + ξ, ξ - 1, 2, -ξ - 1, 0, 0, 0, 0] m / (σ ^ 2 * ξ ^ 2)]] j k

variable {ξ μ σ x : ℝ}

/-- **The log-density in the basis** `1, L, w`. -/
theorem gevLogDensT_eq (hσ : 0 < σ) (hξ : ξ ≠ 0) (hu : 0 < gevU ξ μ σ x) :
    gevLogDensT ξ μ σ x = ∑ m, gevCoefL ξ σ m *
      gevBasisL (gevU ξ μ σ x ^ (-1 / ξ)) (log (gevU ξ μ σ x)) m := by
  rw [gevLogDensT, log_gevLocScaleDensity hσ hξ hu]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, gevCoefL, gevBasisL, gevU]
  simp
  ring

/-- **The score in the basis** `1, a, w, w a, L, w L`. -/
theorem gevScoreT_eq (hσ : σ ≠ 0) (hξ : ξ ≠ 0) (hu : gevU ξ μ σ x ≠ 0) (j : Fin 3) :
    gevScoreT j ξ μ σ x = ∑ m, gevCoefS j ξ σ m *
      gevBasisS (gevU ξ μ σ x)⁻¹ (gevU ξ μ σ x ^ (-1 / ξ)) (log (gevU ξ μ σ x)) m := by
  unfold gevU at hu ⊢
  fin_cases j <;>
  simp only [gevScoreT, gevScoreXi, gevScoreMu, gevScoreSigma, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;>
  generalize (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) = w <;>
  generalize log (1 + ξ * ((x - μ) / σ)) = L <;>
  generalize hz : (x - μ) / σ = z at hu ⊢ <;>
  simp [Fin.sum_univ_succ, gevCoefS, gevBasisS] <;>
  field_simp <;>
  first | ring1 | linear_combination (1 + ξ - w) * inv_mul_cancel₀ hu

/-- **The Hessian in the basis** `1, a, a², w, w a, w a², L, w L, w L a, w L²`. -/
theorem gevHessT_eq (hσ : σ ≠ 0) (hξ : ξ ≠ 0) (hu : gevU ξ μ σ x ≠ 0) (j k : Fin 3) :
    gevHessT j k ξ μ σ x = ∑ m, gevCoefH j k ξ σ m *
      gevBasisH (gevU ξ μ σ x)⁻¹ (gevU ξ μ σ x ^ (-1 / ξ)) (log (gevU ξ μ σ x)) m := by
  fin_cases j <;> fin_cases k <;>
  simp only [gevHessT, gevHessXiXi, gevHessMuXi, gevHessSigmaXi, gevHessMuMu, gevHessMuSigma,
    gevHessSigmaSigma, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
  generalize gevU ξ μ σ x ^ (-1 / ξ) = w <;>
  generalize log (gevU ξ μ σ x) = L <;>
  generalize gevU ξ μ σ x = u at hu ⊢ <;>
  simp [Fin.sum_univ_succ, gevCoefH, gevBasisH] <;>
  field_simp <;>
  ring

end Basis

/-! ### Bounds in the basis -/

section BasisBounds

lemma abs_sum_mul_le {n : ℕ} (c g : Fin n → ℝ) {B : ℝ} (hg : ∀ m, |g m| ≤ B) :
    |∑ m, c m * g m| ≤ (∑ m, |c m|) * B := by
  calc |∑ m, c m * g m| ≤ ∑ m, |c m * g m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m, |c m| * B := Finset.sum_le_sum fun m _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hg m) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

variable {a w L : ℝ}

lemma abs_gevBasisL_le (hw : 0 ≤ w) (m : Fin 3) :
    |gevBasisL w L m| ≤ (1 + w) * (1 + |L|) := by
  have h1 : 0 ≤ |L| := abs_nonneg L
  fin_cases m <;> simp [gevBasisL, abs_of_nonneg hw] <;> nlinarith [mul_nonneg hw h1]

lemma abs_gevBasisS_le (ha : 0 ≤ a) (hw : 0 ≤ w) (m : Fin 6) :
    |gevBasisS a w L m| ≤ (1 + a) * (1 + w) * (1 + |L|) := by
  have h1 : 0 ≤ |L| := abs_nonneg L
  have h2 := mul_nonneg ha hw
  have h3 := mul_nonneg ha h1
  have h4 := mul_nonneg hw h1
  have h5 := mul_nonneg h2 h1
  fin_cases m <;> simp [gevBasisS, abs_of_nonneg hw, abs_of_nonneg ha, abs_mul] <;> nlinarith

lemma abs_gevBasisH_le (ha : 0 ≤ a) (hw : 0 ≤ w) (m : Fin 10) :
    |gevBasisH a w L m| ≤ (1 + a) ^ 2 * (1 + w) * (1 + |L|) ^ 2 := by
  have hl : 0 ≤ |L| := abs_nonneg L
  have hA : 1 ≤ 1 + a := by linarith
  have hW : 1 ≤ 1 + w := by linarith
  have hΛ : 1 ≤ 1 + |L| := by linarith
  have hA2 : 1 ≤ (1 + a) ^ 2 := one_le_pow₀ hA
  have hΛ2 : 1 ≤ (1 + |L|) ^ 2 := one_le_pow₀ hΛ
  have ea : a ≤ (1 + a) ^ 2 := by nlinarith
  have ea2 : a ^ 2 ≤ (1 + a) ^ 2 := by nlinarith
  have el : |L| ≤ (1 + |L|) ^ 2 := by nlinarith
  have el2 : |L| ^ 2 ≤ (1 + |L|) ^ 2 := by nlinarith
  have ew : w ≤ 1 + w := by linarith
  have P : ∀ {p q r : ℝ}, 0 ≤ p → 0 ≤ q → 0 ≤ r → p ≤ (1 + a) ^ 2 → q ≤ 1 + w →
      r ≤ (1 + |L|) ^ 2 → p * q * r ≤ (1 + a) ^ 2 * (1 + w) * (1 + |L|) ^ 2 := by
    intro p q r hp hq hr h1 h2 h3
    have := mul_le_mul h1 h2 hq (by positivity)
    exact mul_le_mul this h3 hr (by positivity)
  fin_cases m <;> simp only [gevBasisH, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, abs_mul, abs_pow,
    abs_one, abs_of_nonneg ha, abs_of_nonneg hw]
  · simpa using P zero_le_one zero_le_one zero_le_one hA2 hW hΛ2
  · simpa using P ha zero_le_one zero_le_one ea hW hΛ2
  · simpa using P (sq_nonneg a) zero_le_one zero_le_one ea2 hW hΛ2
  · simpa using P zero_le_one hw zero_le_one hA2 ew hΛ2
  · simpa [mul_comm] using P ha hw zero_le_one ea ew hΛ2
  · simpa [mul_comm] using P (sq_nonneg a) hw zero_le_one ea2 ew hΛ2
  · simpa using P zero_le_one zero_le_one hl hA2 hW el
  · simpa [mul_comm] using P zero_le_one hw hl hA2 ew el
  · have := P ha hw hl ea ew el
    calc w * |L| * a = a * w * |L| := by ring
      _ ≤ _ := this
  · simpa [mul_comm] using P zero_le_one hw (sq_nonneg |L|) hA2 ew el2

end BasisBounds

end ExtremeValueTheory
