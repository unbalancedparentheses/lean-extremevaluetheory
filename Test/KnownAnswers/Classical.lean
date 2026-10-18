import ExtremeValueTheory

/-!
# Known answers: the classical extreme value distributions

Checks of the standard Gumbel, Fréchet and Weibull c.d.f.s, the GEV family `H_ξ`, the affine
action `A • F`, max-stability and the GEV moments against textbook values.

References: [EKM] Embrechts, Klüppelberg, Mikosch, *Modelling Extremal Events* (1997);
[dHF] de Haan, Ferreira, *Extreme Value Theory* (2006); [Coles] Coles, *An Introduction to
Statistical Modeling of Extreme Values* (2001).
-/

open Real CumulativeDistributionFunction ExtremeValueTheory MeasureTheory ProbabilityTheory

namespace Test.KnownAnswers.Classical

/-! ### The three standard laws -/

/-- [EKM, Def. 3.2.6]: `Λ(0) = exp(-e⁰) = e⁻¹`. -/
theorem test_gumbel_zero : standardGumbelCDF 0 = exp (-1) := by
  simp [standardGumbelCDF_apply_eq]

/-- The median of the standard Gumbel law is `-log log 2` ([EKM, Table 3.4.2]):
`Λ(-log log 2) = 1/2`. Fails if the inner exponent had the wrong sign. -/
theorem test_gumbel_median : standardGumbelCDF (-log (log 2)) = 1 / 2 := by
  have h2 : 0 < log 2 := log_pos (by norm_num)
  rw [standardGumbelCDF_apply_eq, neg_neg, exp_log h2, exp_neg, exp_log (by norm_num)]
  norm_num

/-- [EKM, Def. 3.2.6]: `Φ_α(1) = e⁻¹` for every `α`. -/
theorem test_frechet_one {α : ℝ} (hα : 0 < α) : standardFrechetCDF hα 1 = exp (-1) := by
  rw [standardFrechetCDF_apply_pos_eq hα one_pos]
  simp

/-- `Φ_2(2) = exp(-2⁻²) = exp(-1/4)`: fails if the exponent were `+α` instead of `-α`. -/
theorem test_frechet_two_at_two : standardFrechetCDF (two_pos : (0 : ℝ) < 2) 2 = exp (-(1 / 4)) := by
  rw [standardFrechetCDF_apply_pos_eq _ two_pos]
  congr 2
  rw [Real.rpow_eq_pow, Real.rpow_neg (by norm_num)]
  norm_num

/-- The Fréchet law lives on `(0, ∞)`: `Φ_α(x) = 0` for `x ≤ 0` ([EKM, Def. 3.2.6]). -/
theorem test_frechet_left_support {α : ℝ} (hα : 0 < α) : standardFrechetCDF hα (-1) = 0 ∧
    standardFrechetCDF hα 0 = 0 :=
  ⟨standardFrechetCDF_apply_nonpos_eq hα (by norm_num), standardFrechetCDF_apply_nonpos_eq hα le_rfl⟩

/-- [EKM, Def. 3.2.6]: `Ψ_α(-1) = e⁻¹` for every `α`. -/
theorem test_weibull_neg_one {α : ℝ} (hα : 0 < α) : standardWeibullCDF hα (-1) = exp (-1) := by
  rw [standardWeibullCDF_apply_neg_eq hα (by norm_num)]
  simp

/-- `Ψ_2(-2) = exp(-(2²)) = exp(-4)`: fails if the exponent were `-α`. -/
theorem test_weibull_two_at_neg_two :
    standardWeibullCDF (two_pos : (0 : ℝ) < 2) (-2) = exp (-4) := by
  rw [standardWeibullCDF_apply_neg_eq _ (by norm_num)]
  norm_num [Real.rpow_two]

/-- The (max-)Weibull law has right endpoint `0`: `Ψ_α(x) = 1` for `x ≥ 0` ([EKM, Def. 3.2.6]). -/
theorem test_weibull_right_support {α : ℝ} (hα : 0 < α) : standardWeibullCDF hα 0 = 1 ∧
    standardWeibullCDF hα 1 = 1 :=
  ⟨standardWeibullCDF_apply_nonneg_eq hα le_rfl, standardWeibullCDF_apply_nonneg_eq hα zero_le_one⟩

/-- The Gumbel law has full support: `0 < Λ(x) < 1` everywhere (no endpoint). -/
theorem test_gumbel_full_support (x : ℝ) : 0 < standardGumbelCDF x ∧ standardGumbelCDF x < 1 := by
  rw [standardGumbelCDF_apply_eq]
  exact ⟨exp_pos _, exp_lt_one_iff.2 (by linarith [exp_pos (-x)])⟩

/-- The three standard laws are extreme value distributions ([EKM, Theorem 3.2.3]) and are
nondegenerate. -/
theorem test_three_types_are_evd {α : ℝ} (hα : 0 < α) :
    standardGumbelCDF.IsExtremeValueDistr ∧ (standardFrechetCDF hα).IsExtremeValueDistr ∧
      (standardWeibullCDF hα).IsExtremeValueDistr :=
  ⟨isExtremeValueDistr_standardGumbelCDF, isExtremeValueDistr_standardFrechetCDF hα,
    isExtremeValueDistr_standardWeibullCDF hα⟩

/-! ### The GEV family `H_ξ` -/

/-- [EKM, Def. 3.4.1]: `H_ξ(0) = exp(-1)` for every shape `ξ` (`1 + ξ·0 = 1`). -/
theorem test_gev_at_zero (ξ : ℝ) : gevCDF ξ 0 = exp (-1) := by
  rw [gevCDF_apply]
  unfold gevFun
  split_ifs <;> simp_all

/-- `H_0 = Λ` ([EKM, Def. 3.4.1]): `H_0(x) = exp(-e^{-x})`. -/
theorem test_gev_zero_eq_gumbel (x : ℝ) : gevCDF 0 x = exp (-exp (-x)) := by
  rw [gevCDF_zero, standardGumbelCDF_apply_eq]

/-- `H_1(1) = exp(-(1 + 1)^{-1}) = exp(-1/2)` ([EKM, Def. 3.4.1]). -/
theorem test_gev_one_at_one : gevCDF 1 1 = exp (-(1 / 2)) := by
  rw [gevCDF_apply]
  norm_num [gevFun, Real.rpow_neg_one]

/-- For `ξ > 0` the support of `H_ξ` is `(-1/ξ, ∞)`: `H_1(x) = 0` for `x ≤ -1`
([EKM, Def. 3.4.1]). This is the Fréchet side: fails if the `ξ > 0` and `ξ < 0` cases were
swapped. -/
theorem test_gev_pos_left_endpoint : gevCDF 1 (-1) = 0 ∧ gevCDF 1 (-2) = 0 := by
  simp only [gevCDF_apply, gevFun]
  norm_num

/-- For `ξ < 0` the support of `H_ξ` is `(-∞, -1/ξ)`: `H_{-1}(x) = 1` for `x ≥ 1`
([EKM, Def. 3.4.1]). -/
theorem test_gev_neg_right_endpoint : gevCDF (-1) 1 = 1 ∧ gevCDF (-1) 2 = 1 := by
  simp only [gevCDF_apply, gevFun]
  norm_num

/-- `H_{-1}(1/2) = exp(-(1 - 1/2)^1) = exp(-1/2)`. -/
theorem test_gev_neg_one_at_half : gevCDF (-1) (1 / 2) = exp (-(1 / 2)) := by
  rw [gevCDF_apply]
  simp only [gevFun]
  norm_num

/-- [EKM, p. 152]: for `ξ > 0`, `H_ξ(x) = Φ_{1/ξ}(1 + ξ x)`. With `ξ = 1/2`, `x = 2`:
`H_{1/2}(2) = Φ_2(2) = exp(-1/4)`. Fails if the Fréchet index were `ξ` instead of `1/ξ`. -/
theorem test_gev_half_eq_frechet_two :
    gevCDF (1 / 2) 2 = standardFrechetCDF (two_pos : (0 : ℝ) < 2) 2 := by
  rw [test_frechet_two_at_two, gevCDF_apply]
  norm_num [gevFun, Real.rpow_neg, Real.rpow_two]

/-- The library's affine identity for `ξ > 0` ([EKM, p. 152]): `(x ↦ ξ x + 1) • H_ξ = Φ_{1/ξ}`.
Evaluated at a point: `H_ξ(x) = Φ_{1/ξ}(1 + ξ x)`. -/
theorem test_gev_pos_affine {ξ : ℝ} (hξ : 0 < ξ) (x : ℝ) :
    gevCDF ξ x = standardFrechetCDF (one_div_pos.2 hξ) (1 + ξ * x) := by
  rw [← mkOfCoefs_smul_gevCDF_of_pos hξ, mulAction_apply_eq]
  congr 1
  simp [AffineIncrEquiv.apply_eq]
  field_simp
  ring

/-- [EKM, p. 152]: for `ξ < 0`, `H_ξ(x) = Ψ_{-1/ξ}(-(1 + ξ x))`. With `ξ = -1/2`, `x = -2`:
`H_{-1/2}(-2) = Ψ_2(-2) = exp(-4)`. Fails if the Weibull index were `-ξ` instead of `-1/ξ`. -/
theorem test_gev_neg_half_eq_weibull_two :
    gevCDF (-1 / 2) (-2) = standardWeibullCDF (two_pos : (0 : ℝ) < 2) (-2) := by
  rw [test_weibull_two_at_neg_two, gevCDF_apply]
  norm_num [gevFun, Real.rpow_two]

/-- The library's affine identity for `ξ < 0`: `H_ξ(x) = Ψ_{-1/ξ}(-(1 + ξ x))`. -/
theorem test_gev_neg_affine {ξ : ℝ} (hξ : ξ < 0) (x : ℝ) :
    gevCDF ξ x = standardWeibullCDF (div_pos_of_neg_of_neg (by norm_num : (-1 : ℝ) < 0) hξ)
      (-(1 + ξ * x)) := by
  have := hξ.ne
  rw [← mkOfCoefs_smul_gevCDF_of_neg hξ, mulAction_apply_eq]
  congr 1
  simp [AffineIncrEquiv.apply_eq]
  field_simp
  ring

/-- Continuity of the family at `ξ = 0` ([EKM, p. 152]): `H_ξ(1) → Λ(1)` as `ξ → 0`. -/
theorem test_gev_tendsto_gumbel :
    Filter.Tendsto (fun ξ ↦ gevCDF ξ 1) (nhds 0) (nhds (exp (-exp (-1)))) := by
  simpa [standardGumbelCDF_apply_eq] using tendsto_gevCDF_nhds_zero 1

/-! ### The affine action and location-scale families -/

/-- `A • F` is the law of `A X` for `X ∼ F`: `(x ↦ a x + b) • F` at `x` is `F((x - b)/a)`.
With `a = 2`, `b = 3`: `(A • Λ)(3) = Λ(0) = e⁻¹`. Fails if the action were `F(A x)`. -/
theorem test_smul_apply :
    (AffineIncrEquiv.mkOfCoefs (two_pos : (0 : ℝ) < 2) 3 • standardGumbelCDF) 3 = exp (-1) := by
  set A := AffineIncrEquiv.mkOfCoefs (two_pos : (0 : ℝ) < 2) 3 with hA
  have h : A 0 = 3 := by simp [hA, AffineIncrEquiv.apply_eq]
  rw [← h, mulAction_apply_eq_self_apply, test_gumbel_zero]

/-- [Coles, §3.1.3]: the location-scale GEV `H_{ξ,μ,σ}(x) = H_ξ((x - μ)/σ)`. At the location
parameter its value is `e⁻¹` for every `ξ`, `σ`. -/
theorem test_gevLocScale_at_location (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    gevLocScaleCDF ξ μ hσ μ = exp (-1) := by
  rw [gevLocScaleCDF_apply, sub_self, zero_div, ← gevCDF_apply, test_gev_at_zero]

/-- [Coles, §3.1.3]: `H_{0,2,3}(5) = Λ((5 - 2)/3) = Λ(1) = exp(-e⁻¹)`. -/
theorem test_gevLocScale_gumbel_value :
    gevLocScaleCDF 0 2 (by norm_num : (0 : ℝ) < 3) 5 = exp (-exp (-1)) := by
  rw [gevLocScaleCDF_apply]
  norm_num [gevFun]

/-! ### Max-stability ([EKM, §3.2]) -/

/-- `Λ(x + log 2)^2 = Λ(x)`: Gumbel max-stability with `a_n = 1`, `b_n = log n`
([EKM, Example 3.2.7]). -/
theorem test_gumbel_maxStable_two (x : ℝ) :
    standardGumbelCDF (x + log 2) ^ 2 = standardGumbelCDF x := by
  simp only [standardGumbelCDF_apply_eq, ← exp_nat_mul]
  congr 1
  rw [neg_add, exp_add, exp_neg (log 2), exp_log (by norm_num)]
  push_cast
  ring

/-- `Φ_1(2x)^2 = Φ_1(x)`: Fréchet max-stability with `a_n = n^{1/α}`, `b_n = 0`
([EKM, Example 3.2.7]). -/
theorem test_frechet_maxStable_two (x : ℝ) :
    standardFrechetCDF one_pos (2 * x) ^ 2 = standardFrechetCDF one_pos x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [standardFrechetCDF_apply_nonpos_eq _ hx,
      standardFrechetCDF_apply_nonpos_eq _ (by linarith)]
    norm_num
  · rw [standardFrechetCDF_apply_pos_eq _ hx, standardFrechetCDF_apply_pos_eq _ (by linarith),
      ← exp_nat_mul]
    congr 1
    simp only [Real.rpow_eq_pow, Real.rpow_neg_one]
    field_simp
    norm_num

/-- `Ψ_1(x/2)^2 = Ψ_1(x)`: Weibull max-stability with `a_n = n^{-1/α}`, `b_n = 0`
([EKM, Example 3.2.7]). -/
theorem test_weibull_maxStable_two (x : ℝ) :
    standardWeibullCDF one_pos (x / 2) ^ 2 = standardWeibullCDF one_pos x := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [standardWeibullCDF_apply_neg_eq _ hx, standardWeibullCDF_apply_neg_eq _ (by linarith),
      ← exp_nat_mul]
    congr 1
    simp only [Real.rpow_eq_pow, Real.rpow_one]
    push_cast
    ring
  · rw [standardWeibullCDF_apply_nonneg_eq _ hx,
      standardWeibullCDF_apply_nonneg_eq _ (by linarith)]
    norm_num

/-- The library's GEV max-stability relation with the textbook constants
`a_n = n^ξ`, `b_n = (n^ξ - 1)/ξ` ([EKM, §3.4]): `H_1(2x + 1)^2 = H_1(x)`. -/
theorem test_gev_maxStable_two (x : ℝ) : gevCDF 1 (2 * x + 1) ^ 2 = gevCDF 1 x := by
  have h := gevFun_pow_apply (ξ := 1) one_ne_zero (n := 2) (by norm_num) x
  simp only [Real.rpow_one] at h
  rw [gevCDF_apply, gevCDF_apply, ← h]
  norm_num

/-- Every `H_ξ` is max-stable in the sense of [EKM, Def. 3.2.1]. -/
theorem test_gumbel_isMaxStable : standardGumbelCDF.IsMaxStable := by
  simpa using isMaxStable_gevCDF 0

/-! ### GEV moments ([EKM, §3.4]; [Coles, §3.1]) -/

/-- The mean of the standard Gumbel law is the Euler–Mascheroni constant `γ ≈ 0.5772`
([EKM, Table 3.4.2]). -/
theorem test_gumbel_mean :
    ∫ x, x ∂standardGumbelCDF.measure = eulerMascheroniConstant :=
  integral_id_standardGumbelCDF

/-- The variance of the standard Gumbel law is `π²/6` ([EKM, Table 3.4.2]). -/
theorem test_gumbel_variance : variance (fun x ↦ x) standardGumbelCDF.measure = π ^ 2 / 6 :=
  variance_id_standardGumbelCDF

/-- The location-scale Gumbel law has mean `μ + σ γ` ([Coles, §3.1]). With `μ = 1`, `σ = 2`:
`1 + 2γ`. -/
theorem test_gumbel_locScale_mean :
    ∫ x, x ∂(gevLocScaleCDF 0 1 two_pos).measure = 1 + 2 * eulerMascheroniConstant :=
  integral_id_gevLocScaleCDF_zero 1 two_pos

/-- The mean of `Φ_2` is `Γ(1/2) = √π` ([EKM, Table 3.4.2]: mean `Γ(1 - 1/α)`). -/
theorem test_frechet_two_mean :
    ∫ x, x ∂(standardFrechetCDF (two_pos : (0 : ℝ) < 2)).measure = √π := by
  rw [integral_id_standardFrechetCDF (by norm_num : (1 : ℝ) < 2)]
  norm_num [Real.Gamma_one_half_eq]

/-- The mean of `Ψ_1` is `-Γ(2) = -1`: `Ψ_1` is the law of `-E` with `E ∼ Exp(1)`
([EKM, Table 3.4.2]: mean `-Γ(1 + 1/α)`). -/
theorem test_weibull_one_mean : ∫ x, x ∂(standardWeibullCDF one_pos).measure = -1 := by
  rw [integral_id_standardWeibullCDF one_pos]
  norm_num

/-- `H_{-1}(x) = exp(-(1 - x))` for `x < 1` is the law of `1 - E`, `E ∼ Exp(1)`: mean `0` and
variance `1`. Checks the GEV mean `(Γ(1 - ξ) - 1)/ξ` and variance
`(Γ(1 - 2ξ) - Γ(1 - ξ)²)/ξ²` ([Coles, §3.1]) at `ξ = -1`. -/
theorem test_gev_neg_one_mean_variance :
    ∫ x, x ∂(gevCDF (-1)).measure = 0 ∧ variance (fun x ↦ x) (gevCDF (-1)).measure = 1 := by
  constructor
  · rw [integral_id_gevCDF (by norm_num) (by norm_num)]
    norm_num
  · rw [variance_id_gevCDF (by norm_num) (by norm_num)]
    norm_num [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one]

/-- The mean of `H_{1/2}` is `(Γ(1/2) - 1)/(1/2) = 2(√π - 1)`. -/
theorem test_gev_half_mean : ∫ x, x ∂(gevCDF (1 / 2)).measure = 2 * (√π - 1) := by
  rw [integral_id_gevCDF (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_one_half_eq]
  ring

end Test.KnownAnswers.Classical
