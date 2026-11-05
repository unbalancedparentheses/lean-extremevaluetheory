import ExtremeValueTheory

/-!
# Known answers: return levels and Wald intervals

Exact values of the return-level formulas, the defining property of a return level, the delta-method
variance at a point computed by hand, and two worked examples of [Col] Coles, *An Introduction to
Statistical Modeling of Extreme Values* (2001):

* §3.4.1, Port Pirie annual maximum sea levels: `(μ̂, σ̂, ξ̂) = (3.87, 0.198, -0.050)`, with the
  100-year return level `4.69` and its variance `0.0251`;
* §4.4.1, daily rainfall: `u = 30`, `(σ̂, ξ̂) = (7.44, 0.184)`, `ζ̂ = 152/17531`, with the 100-year return
  level (`N = 36500`) `106.3` and its variance `431.3`.

The figures of [Col], including the covariance matrices, were recalled from memory, not read from the
book for these tests; the formulas reproduce them to within the rounding of the published estimates.
That agreement is itself the check: a wrong sign, a wrong coordinate order or a wrong gradient breaks
it. Each numerical test is an interval around the published value, wide enough for that rounding.
-/

open ExtremeValueTheory Real MeasureTheory ProbabilityTheory Set
open scoped Matrix

namespace Test.KnownAnswers.ReturnLevels

/-! ### Exact values -/

/-- The Gumbel median ([Col, (3.4)]): `z_2 = μ - σ log log 2`. -/
theorem test_gevReturnLevel_gumbel_median (μ σ : ℝ) :
    gevReturnLevel 0 μ σ 2 = μ - σ * log (log 2) := by
  rw [gevReturnLevel_zero]
  norm_num
  rw [one_div, log_inv]
  exact Or.inl (log_neg_eq_log _)

/-- The Fréchet case `ξ = 1`: `z_2 = (log 2)⁻¹ - 1`. -/
theorem test_gevReturnLevel_frechet : gevReturnLevel 1 0 1 2 = (log 2)⁻¹ - 1 := by
  rw [gevReturnLevel_eq_of_ne one_ne_zero]
  norm_num [rpow_neg_one]
  rw [one_div, log_inv, inv_neg, neg_neg]
  ring

/-- The Weibull case `ξ = -1`: `z_2 = 1 - log 2`. -/
theorem test_gevReturnLevel_weibull : gevReturnLevel (-1) 0 1 2 = 1 - log 2 := by
  rw [gevReturnLevel_eq_of_ne (by norm_num)]
  norm_num
  rw [one_div, log_inv]
  ring

/-- The defining property of the GEV return level ([Col, §3.1.3]): it is the `1 - 1/m` quantile. -/
theorem test_gevLocScaleCDF_gevReturnLevel (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) {m : ℝ} (hm : 1 < m) :
    gevLocScaleCDF ξ μ hσ (gevReturnLevel ξ μ σ m) = 1 - 1 / m :=
  gevLocScaleCDF_returnLevel ξ μ hσ hm

/-- The exponential excess case `ξ = 0`: `x_N = u + σ log (N ζ)` ([Col, (4.13)]). -/
theorem test_gpdReturnLevel_exp : gpdReturnLevel 30 0 2 (1 / 10) 100 = 30 + 2 * log 10 := by
  rw [gpdReturnLevel_zero]
  norm_num

/-- `ξ = 1`: `x_N = u + σ (N ζ - 1)`. -/
theorem test_gpdReturnLevel_pareto : gpdReturnLevel 0 1 1 (1 / 2) 10 = 4 := by
  rw [gpdReturnLevel_of_ne one_ne_zero]
  norm_num

/-- `ξ = -1` (uniform excesses): `x_N = u + σ (1 - 1 / (N ζ))`. -/
theorem test_gpdReturnLevel_uniform : gpdReturnLevel 0 (-1) 1 (1 / 2) 4 = 1 / 2 := by
  rw [gpdReturnLevel_of_ne (by norm_num)]
  norm_num [rpow_neg_one]

/-- **The defining property of the POT return level** ([Col, §4.3.3]): the level `x_N` is exceeded
with probability `1 / N` in the model `P(X > x) = ζ Ḡ(x - u)`, for every shape. -/
theorem test_mul_gpdMeasure_Ioi_gpdReturnLevel {ξ σ u ζ N : ℝ} (hσ : 0 < σ) (hζ : 0 < ζ)
    (hNζ : 1 < N * ζ) :
    ζ * (gpdMeasure ξ σ).real (Ioi (gpdReturnLevel u ξ σ ζ N - u)) = 1 / N := by
  have hN : N ≠ 0 := by
    rintro rfl
    simp at hNζ
    linarith
  rw [measureReal_gpdMeasure_Ioi_gpdReturnLevel_sub hσ hNζ]
  field_simp

/-- The delta-method variance at `ξ = 1`, `σ = 1`, `N ζ = e`, computed by hand from [Col, §4.3.3]:
`∇x = (∂_ξ, ∂_σ) = (1, e - 1)`, `I⁻¹ = 2 [[2, -1], [-1, 2]]`, so
`∇xᵀ I⁻¹ ∇x = 2 (2 - 2 (e - 1) + 2 (e - 1)²)`. -/
theorem test_gpdReturnLevelVar : gpdReturnLevelVar 1 1 1 (exp 1) =
    2 * (2 - 2 * (exp 1 - 1) + 2 * (exp 1 - 1) ^ 2) := by
  simp [gpdReturnLevelVar, boxCoxShapeDeriv, boxCox_of_ne]
  ring

/-- Coles' gradient at the same point: `∂x_N/∂ξ = 1` and `∂x_N/∂σ = e - 1`. -/
theorem test_gpdReturnLevelGrad :
    gpdReturnLevelGrad 1 1 1 (exp 1) = !₂[1, exp 1 - 1] := by
  rw [gpdReturnLevelGrad_eq one_ne_zero]
  norm_num

/-! ### Two numerical bounds, used below -/

/-- Test-specific: `2.3024 < log 10 < 2.3027`, from `3 log 10 = 10 log 2 - log 1.024`. -/
private theorem log_ten_bounds : 2.3024 < log 10 ∧ log 10 < 2.3027 := by
  have h : 3 * log 10 = 10 * log 2 - log 1.024 := by
    have e1 : log ((10 : ℝ) ^ 3) = 3 * log 10 := by rw [log_pow]; norm_num
    have e2 : log ((2 : ℝ) ^ 10) = 10 * log 2 := by rw [log_pow]; norm_num
    have e3 : ((2 : ℝ) ^ 10) = 10 ^ 3 * 1.024 := by norm_num
    rw [← e1, ← e2, e3, log_mul (by norm_num) (by norm_num)]
    ring
  have h1 : log 1.024 ≤ 0.024 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1.024 by norm_num)
    linarith
  have h2 : (0.0234 : ℝ) ≤ log 1.024 := by
    have := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.024 by norm_num)
    norm_num at this ⊢
    linarith
  have h3 := log_two_gt_d9
  have h4 := log_two_lt_d9
  constructor <;> linarith

/-- Test-specific: `a ≤ y^(1/n)` from `a^n ≤ y`. -/
private theorem le_rpow_inv {a y : ℝ} {n : ℕ} (hn : n ≠ 0) (ha : 0 ≤ a) (h : a ^ n ≤ y) :
    a ≤ y ^ ((n : ℝ)⁻¹) := by
  calc a = (a ^ n) ^ ((n : ℝ)⁻¹) := (pow_rpow_inv_natCast ha hn).symm
    _ ≤ _ := rpow_le_rpow (by positivity) h (by positivity)

/-- Test-specific: `y^(1/n) ≤ a` from `y ≤ a^n`. -/
private theorem rpow_inv_le {a y : ℝ} {n : ℕ} (hn : n ≠ 0) (ha : 0 ≤ a) (hy : 0 ≤ y)
    (h : y ≤ a ^ n) : y ^ ((n : ℝ)⁻¹) ≤ a := by
  calc y ^ ((n : ℝ)⁻¹) ≤ (a ^ n) ^ ((n : ℝ)⁻¹) := rpow_le_rpow hy h (by positivity)
    _ = a := pow_rpow_inv_natCast ha hn

/-! ### Coles §3.4.1: Port Pirie -/

/-- Test-specific: `y = -log(1 - 1/100)` lies in `[1/100, 1/99]`. -/
private theorem y100_bounds : (1 / 100 : ℝ) ≤ -log (1 - 1 / 100) ∧ -log (1 - 1 / 100) ≤ 1 / 99 := by
  have h1 := log_le_sub_one_of_pos (show (0 : ℝ) < 1 - 1 / 100 by norm_num)
  have h2 := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - 1 / 100 by norm_num)
  norm_num at h1 h2 ⊢
  constructor <;> linarith

/-- Test-specific: `w = y^(1/20)` lies in `[0.794, 0.795]`. -/
private theorem w100_bounds :
    (0.794 : ℝ) ≤ (-log (1 - 1 / 100)) ^ (1 / 20 : ℝ) ∧
      (-log (1 - 1 / 100)) ^ (1 / 20 : ℝ) ≤ 0.795 := by
  obtain ⟨h1, h2⟩ := y100_bounds
  have e : (1 / 20 : ℝ) = (((20 : ℕ) : ℝ))⁻¹ := by norm_num
  rw [e]
  exact ⟨le_rpow_inv (by norm_num) (by norm_num) (le_trans (by norm_num) h1),
    rpow_inv_le (by norm_num) (by norm_num) (by linarith) (le_trans h2 (by norm_num))⟩

/-- **The 100-year return level of Port Pirie** ([Col, §3.4.1], `ẑ = 4.69`): with the rounded
estimates `(μ, σ, ξ) = (3.87, 0.198, -0.05)` the formula gives a value in `(4.68, 4.69)`. -/
theorem test_gevReturnLevel_portPirie :
    4.68 < gevReturnLevel (-1 / 20) 3.87 0.198 100 ∧
      gevReturnLevel (-1 / 20) 3.87 0.198 100 < 4.69 := by
  obtain ⟨h1, h2⟩ := w100_bounds
  rw [gevReturnLevel_eq_of_ne (by norm_num), show -(-1 / 20 : ℝ) = 1 / 20 by norm_num]
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- Coles' covariance matrix for Port Pirie, reordered from his `(μ, σ, ξ)` to the library's
`(ξ, μ, σ)`. -/
private noncomputable def portPirieV : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0.00965, -0.00107, -0.000778; -0.00107, 0.000780, 0.000197; -0.000778, 0.000197, 0.000410]

/-- **The delta-method variance of the Port Pirie return level** ([Col, §3.4.1], `Var ẑ = 0.0251`): the
quadratic form `∇zᵀ V ∇z`, with the library's gradient and coordinate order, lies in
`[0.023, 0.028]`. With `∂_ξ` of the wrong sign the same form would be about `0.056`. -/
theorem test_gevReturnLevelVariance_portPirie :
    0.023 ≤ gevReturnLevelGrad (-1 / 20) 0.198 100 ⬝ᵥ
        portPirieV *ᵥ gevReturnLevelGrad (-1 / 20) 0.198 100 ∧
      gevReturnLevelGrad (-1 / 20) 0.198 100 ⬝ᵥ
        portPirieV *ᵥ gevReturnLevelGrad (-1 / 20) 0.198 100 ≤ 0.028 := by
  obtain ⟨hw1, hw2⟩ := w100_bounds
  obtain ⟨hy1, hy2⟩ := y100_bounds
  obtain ⟨hl1, hl2⟩ := log_ten_bounds
  set y := -log (1 - 1 / 100 : ℝ) with hy
  set w := y ^ (1 / 20 : ℝ) with hw
  have hy0 : 0 < y := by linarith
  -- `log y ∈ [-2 log 10, -2 log 10 + 1/99]`
  have hL100 : log (1 / 100 : ℝ) = -(2 * log 10) := by
    rw [show (1 / 100 : ℝ) = (10 ^ 2)⁻¹ by norm_num, log_inv, log_pow]
    norm_num
  have hL1 : -(2 * log 10) ≤ log y := by
    rw [← hL100]
    exact log_le_log (by norm_num) hy1
  have hL2 : log y ≤ -(2 * log 10) + 1 / 99 := by
    have := log_le_sub_one_of_pos (show 0 < y * 100 by positivity)
    rw [log_mul hy0.ne' (by norm_num), show (100 : ℝ) = 10 ^ 2 by norm_num, log_pow] at this
    norm_num at this
    linarith
  rw [gevReturnLevelGrad_eq (by norm_num) _ (by norm_num), show -(-1 / 20 : ℝ) = 1 / 20 by norm_num,
    ← hy, ← hw]
  set L := log y
  set a : ℝ := 0.198 / (-1 / 20) ^ 2 * (1 - w) - 0.198 / (-1 / 20) * w * L with ha
  set c : ℝ := -(1 - w) / (-1 / 20) with hc
  have hc1 : 4.1 ≤ c := by rw [hc]; norm_num at hw1 hw2 ⊢; linarith
  have hc2 : c ≤ 4.12 := by rw [hc]; norm_num at hw1 hw2 ⊢; linarith
  have hwL1 : -3.6613 ≤ w * L := by nlinarith
  have hwL2 : w * L ≤ -3.648 := by nlinarith
  have ha1 : 1.73 ≤ a := by rw [ha]; norm_num at hw1 hw2 hwL1 hwL2 ⊢; linarith
  have ha2 : a ≤ 1.87 := by rw [ha]; norm_num at hw1 hw2 hwL1 hwL2 ⊢; linarith
  have hform : (!₂[a, 1, c] : EuclideanSpace ℝ (Fin 3)) ⬝ᵥ portPirieV *ᵥ !₂[a, 1, c] =
      0.00965 * a ^ 2 - 2 * 0.00107 * a - 2 * 0.000778 * a * c + 0.000780 +
        2 * 0.000197 * c + 0.000410 * c ^ 2 := by
    simp [portPirieV, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  rw [hform]
  constructor <;> nlinarith

/-! ### Coles §4.4.1: daily rainfall -/

/-- Test-specific: `N ζ = 36500 · 152 / 17531`, the mean number of exceedances in 100 years. -/
private noncomputable def x₀ : ℝ := 36500 * (152 / 17531)

/-- Test-specific: `w = (N ζ)^ξ` lies in `[2.88, 2.89]`, from `2.88^125 ≤ 316^23` and
`317^23 ≤ 2.89^125`. -/
private theorem w_rain_bounds : (2.88 : ℝ) ≤ x₀ ^ (23 / 125 : ℝ) ∧ x₀ ^ (23 / 125 : ℝ) ≤ 2.89 := by
  have e : x₀ ^ (23 / 125 : ℝ) = (x₀ ^ (23 : ℕ)) ^ (((125 : ℕ) : ℝ))⁻¹ := by
    rw [← rpow_natCast, ← rpow_mul (by norm_num [x₀])]
    norm_num
  have hx1 : (316 : ℝ) ≤ x₀ := by norm_num [x₀]
  have hx2 : x₀ ≤ 317 := by norm_num [x₀]
  have hp1 : (316 : ℝ) ^ 23 ≤ x₀ ^ (23 : ℕ) := pow_le_pow_left₀ (by norm_num) hx1 _
  have hp2 : x₀ ^ (23 : ℕ) ≤ (317 : ℝ) ^ 23 := pow_le_pow_left₀ (by linarith) hx2 _
  rw [e]
  exact ⟨le_rpow_inv (by norm_num) (by norm_num) (le_trans (by norm_num) hp1),
    rpow_inv_le (by norm_num) (by norm_num) (by have : 0 < x₀ := by norm_num [x₀]
                                                positivity) (le_trans hp2 (by norm_num))⟩

/-- **The 100-year return level of the rainfall data** ([Col, §4.4.1], `x̂ = 106.3`): `u = 30`,
`σ = 7.44`, `ξ = 0.184`, `ζ = 152/17531`, `N = 36500` gives a value in `(106, 106.5)`. -/
theorem test_gpdReturnLevel_rainfall :
    106 < gpdReturnLevel 30 (23 / 125) (186 / 25) (152 / 17531) 36500 ∧
      gpdReturnLevel 30 (23 / 125) (186 / 25) (152 / 17531) 36500 < 106.5 := by
  obtain ⟨h1, h2⟩ := w_rain_bounds
  rw [gpdReturnLevel_of_ne (by norm_num), show (36500 : ℝ) * (152 / 17531) = x₀ from rfl]
  generalize x₀ ^ (23 / 125 : ℝ) = w at h1 h2 ⊢
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- Coles' covariance matrix for the rainfall data, reordered from `(ζ, σ, ξ)` to the library's
`(ζ, ξ, σ)`. The first entry is `ζ (1 - ζ) / n ≈ 4.9 · 10⁻⁷`. -/
private noncomputable def rainV : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0.00000049, 0, 0; 0, 0.0102, -0.0655; 0, -0.0655, 0.9188]

/-- **The delta-method variance of the rainfall return level** ([Col, §4.4.1], `Var x̂ = 431.3`): the
quadratic form `∇xᵀ V ∇x`, with the library's three-parameter gradient and coordinate order, lies in
`[410, 450]`. -/
theorem test_gpdReturnLevelVariance_rainfall :
    410 ≤ gpdReturnLevelGrad₃ (152 / 17531) (23 / 125) (186 / 25) 36500 ⬝ᵥ
        rainV *ᵥ gpdReturnLevelGrad₃ (152 / 17531) (23 / 125) (186 / 25) 36500 ∧
      gpdReturnLevelGrad₃ (152 / 17531) (23 / 125) (186 / 25) 36500 ⬝ᵥ
        rainV *ᵥ gpdReturnLevelGrad₃ (152 / 17531) (23 / 125) (186 / 25) 36500 ≤ 450 := by
  obtain ⟨hw1, hw2⟩ := w_rain_bounds
  obtain ⟨hl1, hl2⟩ := log_ten_bounds
  have hx0 : 0 < x₀ := by norm_num [x₀]
  set w := x₀ ^ (23 / 125 : ℝ) with hw
  -- `log (N ζ) ∈ [5.756, 5.762]`, from `10⁵ ≤ (N ζ)² ≤ 1.01 · 10⁵`
  have hL : log (x₀ ^ 2) = 2 * log x₀ := by rw [log_pow]; norm_num
  have h105 : log ((10 : ℝ) ^ 5) = 5 * log 10 := by rw [log_pow]; norm_num
  have hL1 : 5.756 ≤ log x₀ := by
    have := log_le_log (by norm_num) (show (10 : ℝ) ^ 5 ≤ x₀ ^ 2 by norm_num [x₀])
    rw [hL, h105] at this
    linarith
  have hL2 : log x₀ ≤ 5.762 := by
    have h := log_le_log (by positivity) (show x₀ ^ 2 ≤ (10 : ℝ) ^ 5 * 1.01 by norm_num [x₀])
    rw [hL, log_mul (by norm_num) (by norm_num), h105] at h
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1.01 by norm_num)
    norm_num at this
    linarith
  set L := log x₀
  -- the `ζ` coordinate is `σ N w / x₀`
  have hrpow : x₀ ^ ((23 / 125 : ℝ) - 1) = w / x₀ := rpow_sub_one hx0.ne' _
  set A : ℝ := 186 / 25 * 36500 * (w / x₀) with hA
  set B : ℝ := 186 / 25 * (w * L / (23 / 125) - (w - 1) / (23 / 125) ^ 2) with hB
  set C : ℝ := (w - 1) / (23 / 125) with hC
  have hgrad : gpdReturnLevelGrad₃ (152 / 17531) (23 / 125) (186 / 25) 36500 = !₂[A, B, C] := by
    simp only [gpdReturnLevelGrad₃, boxCoxShapeDeriv, boxCox_of_ne (show (23 / 125 : ℝ) ≠ 0 by norm_num)]
    rw [show (36500 : ℝ) * (152 / 17531) = x₀ from rfl, hrpow]
  have hAe : A = 186 / 25 * 36500 * (w / (36500 * (152 / 17531))) := rfl
  have hA1 : 2470 ≤ A := by rw [hAe]; norm_num at hw1 ⊢; linarith
  have hA2 : A ≤ 2482 := by rw [hAe]; norm_num at hw2 ⊢; linarith
  have hC1 : 10.21 ≤ C := by rw [hC]; norm_num at hw1 ⊢; linarith
  have hC2 : C ≤ 10.28 := by rw [hC]; norm_num at hw2 ⊢; linarith
  have hwL1 : 16.57 ≤ w * L := by nlinarith
  have hwL2 : w * L ≤ 16.66 := by nlinarith
  have hB1 : 254 ≤ B := by rw [hB]; norm_num at hw1 hw2 hwL1 hwL2 ⊢; linarith
  have hB2 : B ≤ 261 := by rw [hB]; norm_num at hw1 hw2 hwL1 hwL2 ⊢; linarith
  have hform : (!₂[A, B, C] : EuclideanSpace ℝ (Fin 3)) ⬝ᵥ rainV *ᵥ !₂[A, B, C] =
      0.00000049 * A ^ 2 + 0.0102 * B ^ 2 - 2 * 0.0655 * B * C + 0.9188 * C ^ 2 := by
    simp [rainV, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  rw [hgrad, hform]
  constructor <;> nlinarith

/-! ### Wald coverage -/

/-- The limit of the coverage at `z = 0` is `0`: the interval degenerates to a point, and
`N(0, 1)` has no atoms. -/
theorem test_coverage_zero : gaussianReal 0 1 (Icc (-(0 : ℝ)) 0) = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  simp

/-- The limit of the coverage for `z < 0` is `0`: the interval is empty. -/
theorem test_coverage_neg {z : ℝ} (hz : z < 0) : gaussianReal 0 1 (Icc (-z) z) = 0 := by
  rw [Icc_eq_empty (by linarith)]
  simp

/-- The 95% level exists ([Col, §2.6.4]): there is `z > 0` with `N(0, 1)[-z, z] = 0.95`, the textbook
quantile `z_{0.025} ≈ 1.96`. The value `1.96` itself is not verified here. -/
theorem test_coverage_ninetyFive : ∃ z : ℝ, 0 < z ∧ (gaussianReal 0 1).real (Icc (-z) z) = 0.95 := by
  have := exists_gaussianReal_Icc_eq (α := 0.05) (by norm_num) (by norm_num)
  norm_num at this ⊢
  exact this

end Test.KnownAnswers.ReturnLevels
