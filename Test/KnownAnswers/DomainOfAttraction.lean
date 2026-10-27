import ExtremeValueTheory

/-!
# Known answers: maximum domains of attraction, tail quantiles, extended regular variation

Checks that the textbook examples land in the right domain of attraction, with the textbook
normalizing constants, and that the tail quantile function `U` and the limit `D_γ` of extended
regular variation have the textbook values.

References: [EKM] Embrechts, Klüppelberg, Mikosch, *Modelling Extremal Events* (1997), §3.3;
[dHF] de Haan, Ferreira, *Extreme Value Theory* (2006), §1.1–1.2 and Appendix B.2;
[Resnick] Resnick, *Extreme Values, Regular Variation and Point Processes* (1987), §1.1.
-/

open Real Filter Topology Set CumulativeDistributionFunction ExtremeValueTheory

namespace Test.KnownAnswers.DomainOfAttraction

/-! ### Explicit normalizations -/

/-- **Pareto ∈ MDA(Φ_α) with `a_n = n^{1/α}`, `b_n = 0`** ([EKM, Example 3.3.10];
[Resnick, §1.1]): `F(n^{1/α} x)^n → Φ_α(x)` for every `x`. Fails if the normalization or the
Fréchet index were off (e.g. `a_n = n^α`). -/
theorem test_pareto_frechet_normalization {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ paretoCDF hα ((n : ℝ) ^ (1 / α) * x) ^ n) atTop
      (𝓝 (standardFrechetCDF hα x)) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [standardFrechetCDF_apply_nonpos_eq hα hx]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 : paretoCDF hα ((n : ℝ) ^ (1 / α) * x) = 0 :=
      paretoCDF_apply_of_le_one hα (by nlinarith [rpow_nonneg (Nat.cast_nonneg n) (1 / α)])
    rw [h0, zero_pow (by omega)]
  · rw [standardFrechetCDF_apply_pos_eq hα hx]
    refine (tendsto_one_add_div_pow_exp (-x ^ (-α))).congr' ?_
    have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) ^ (1 / α) * x := by
      have : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / α) * x) atTop atTop :=
        ((tendsto_rpow_atTop (one_div_pos.2 hα)).comp tendsto_natCast_atTop_atTop).atTop_mul_const
          hx
      exact this.eventually_ge_atTop 1
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [paretoCDF_apply_of_one_le hα hn, mul_rpow (rpow_nonneg hn0.le _) hx.le,
      ← rpow_mul hn0.le, show 1 / α * -α = -1 by field_simp, rpow_neg_one]
    congr 1
    ring

/-- **Exponential ∈ MDA(Λ) with `a_n = 1`, `b_n = log n`** ([EKM, Example 3.3.21]):
`F(x + log n)^n → Λ(x)`. -/
theorem test_exponential_gumbel_normalization (x : ℝ) :
    Tendsto (fun n : ℕ ↦ standardExponentialCDF (x + log n) ^ n) atTop
      (𝓝 (standardGumbelCDF x)) := by
  rw [standardGumbelCDF_apply_eq]
  refine (tendsto_one_add_div_pow_exp (-exp (-x))).congr' ?_
  have hev : ∀ᶠ n : ℕ in atTop, 0 ≤ x + log n :=
    (tendsto_atTop_add_const_left _ x
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 0
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [standardExponentialCDF_apply_of_nonneg hn, neg_add, exp_add, exp_neg (log _), exp_log hn0]
  congr 1
  ring

/-- The same statement through the library's affine action: with `A_n⁻¹ x = x + log n`,
`((A_n • F) x)^n → Λ(x)`, so the exponential law is in `MDA(Λ)` in the library's sense. -/
theorem test_exponential_isInMDAGumbel_explicit : standardExponentialCDF.IsInMDAGumbel :=
  ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs one_pos (log n))⁻¹, fun x ↦ by
    simpa [AffineIncrEquiv.apply_eq] using test_exponential_gumbel_normalization x⟩

/-- The bundled domain of attraction `ExtremeValueDistr.domainOfAtraction` contains the
exponential law for the Gumbel EVD (the definition has `F` the attracted law and `G` the limit,
not the other way round). -/
theorem test_exponential_mem_domainOfAtraction_gumbel :
    standardExponentialCDF ∈
      (⟨standardGumbelCDF, isExtremeValueDistr_standardGumbelCDF⟩ : ExtremeValueDistr).domainOfAtraction :=
  ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs one_pos (log n))⁻¹, fun x _ ↦ by
    simpa [AffineIncrEquiv.apply_eq] using test_exponential_gumbel_normalization x⟩

/-- Extreme value distributions are nondegenerate: `Λ` takes values other than `0` and `1`. -/
theorem test_gumbel_not_degenerate : ¬ standardGumbelCDF.IsDegenerate :=
  isExtremeValueDistr_standardGumbelCDF.nondegenerate

/-- **Uniform ∈ MDA(Ψ_1) with `a_n = 1/n`, `b_n = 1`** ([EKM, Example 3.3.15]):
`F(1 + x/n)^n → Ψ_1(x)` for the uniform law on `[0, 1]`. -/
theorem test_uniform_weibull_normalization (x : ℝ) :
    Tendsto (fun n : ℕ ↦ powerCDF one_pos (1 + x / n) ^ n) atTop
      (𝓝 (standardWeibullCDF one_pos x)) := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [standardWeibullCDF_apply_neg_eq one_pos hx]
    refine (tendsto_one_add_div_pow_exp x).congr' ?_ |>.trans (by simp)
    have hev : ∀ᶠ n : ℕ in atTop, -x ≤ n :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (-x)
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 : 0 ≤ 1 + x / n := by
      have : -1 ≤ x / n := by rw [le_div_iff₀ hn0]; linarith
      linarith
    have h2 : 1 + x / n ≤ 1 := by
      have : x / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx.le hn0.le
      linarith
    rw [powerCDF_apply_of_mem_Icc one_pos ⟨h1, h2⟩, rpow_one]
    ring_nf
  · rw [standardWeibullCDF_apply_nonneg_eq one_pos hx]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n ↦ ?_)
    have h : powerCDF one_pos (1 + x / n) = 1 :=
      powerCDF_apply_of_one_le one_pos (by have := div_nonneg hx (Nat.cast_nonneg n); linarith)
    simp [h]

/-! ### The unified `IsInMDAGEV ξ` and its sign convention ([dHF, Theorem 1.1.3]) -/

/-- Pareto(α) ∈ MDA(H_ξ) with `ξ = 1/α > 0` ([EKM, Table 3.4.2]). Fails if the Fréchet side
were assigned to `ξ < 0` or the index were `ξ` instead of `1/ξ`. -/
theorem test_pareto_isInMDAGEV {α : ℝ} (hα : 0 < α) : (paretoCDF hα).IsInMDAGEV (1 / α) :=
  isInMDAGEV_paretoCDF hα

/-- Uniform ∈ MDA(H_ξ) with `ξ = -1`, and more generally `1 - (1 - x)^α` ∈ MDA(H_{-1/α})
([EKM, Table 3.4.3]). -/
theorem test_power_isInMDAGEV {α : ℝ} (hα : 0 < α) : (powerCDF hα).IsInMDAGEV (-1 / α) :=
  isInMDAGEV_powerCDF hα

/-- Exponential ∈ MDA(H_0) ([EKM, Table 3.4.4]). -/
theorem test_exponential_isInMDAGEV : standardExponentialCDF.IsInMDAGEV 0 :=
  isInMDAGEV_standardExponentialCDF

/-- The sign convention of `IsInMDAGEV`: `ξ > 0` is the Fréchet side with index `1/ξ`, `ξ < 0` the
Weibull side with index `-1/ξ`, `ξ = 0` the Gumbel domain. -/
theorem test_isInMDAGEV_sign_convention (F : CumulativeDistributionFunction) :
    (F.IsInMDAGEV (1 / 2) ↔ F.IsInMDAFrechet two_pos) ∧
      (F.IsInMDAGEV (-1 / 2) ↔ F.IsInMDAWeibull two_pos) ∧
      (F.IsInMDAGEV 0 ↔ F.IsInMDAGumbel) := by
  refine ⟨?_, ?_, isInMDAGEV_zero_iff⟩
  · rw [isInMDAGEV_iff_of_pos (by norm_num)]
    norm_num
  · rw [isInMDAGEV_iff_of_neg (by norm_num)]
    norm_num

/-! ### Negative checks: the wrong domain is rejected -/

/-- Pareto(α) is **not** in `MDA(Φ_β)` for `β ≠ α`: the Fréchet index is the tail index
([EKM, Theorem 3.3.7]). -/
theorem test_pareto_not_isInMDAFrechet_of_ne {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hne : β ≠ α) :
    ¬ (paretoCDF hα).IsInMDAFrechet hβ := by
  intro h
  have h1 := isRegularlyVarying_of_isInMDAFrechet _ hβ h
  have h2 := isRegularlyVarying_of_isInMDAFrechet _ hα (isInMDAFrechet_paretoCDF hα)
  exact hne (neg_inj.1 (IsRegularlyVarying.index_eq h1 h2))

/-- The exponential law is **not** in any Fréchet domain: its tail `e^{-x}` is not regularly
varying ([EKM, Theorem 3.3.7]). -/
theorem test_exponential_not_isInMDAFrechet {α : ℝ} (hα : 0 < α) :
    ¬ standardExponentialCDF.IsInMDAFrechet hα := by
  intro h
  have hRV := (isRegularlyVarying_of_isInMDAFrechet _ hα h).tendsto two_pos
  have h0 : Tendsto (fun x ↦ (1 - standardExponentialCDF (2 * x)) /
      (1 - standardExponentialCDF x)) atTop (𝓝 0) := by
    refine (tendsto_exp_neg_atTop_nhds_zero).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [standardExponentialCDF_apply_of_nonneg (by linarith),
      standardExponentialCDF_apply_of_nonneg hx, sub_sub_cancel, sub_sub_cancel,
      show -(2 * x) = -x + -x by ring, exp_add, mul_div_cancel_right₀ _ (exp_pos _).ne']
  exact (rpow_pos_of_pos two_pos (-α)).ne' (tendsto_nhds_unique hRV h0)

/-- The uniform law (finite right endpoint) is **not** in any Fréchet domain. -/
theorem test_uniform_not_isInMDAFrechet {α : ℝ} (hα : 0 < α) :
    ¬ (powerCDF one_pos).IsInMDAFrechet hα := by
  intro h
  obtain ⟨x, hpos, hx1⟩ :=
    ((isRegularlyVarying_of_isInMDAFrechet _ hα h).eventually_pos.and
      (eventually_ge_atTop 1)).exists
  have : powerCDF one_pos x = 1 := powerCDF_apply_of_one_le one_pos hx1
  linarith

/-! ### The tail quantile function `U(t) = F^←(1 - 1/t)` ([dHF, §1.1]) -/

/-- `U(t) = log t` for the standard exponential law ([dHF, Example 1.1.7]). -/
theorem test_tailQuantile_exponential {t : ℝ} (ht : 1 < t) :
    standardExponentialCDF.tailQuantile t = log t := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < log t := log_pos ht
  have hS : {y | 1 - standardExponentialCDF y ≤ 1 / t} = Ici (log t) := by
    ext y
    simp only [mem_ofPred_eq, mem_Ici]
    rcases lt_or_ge y 0 with hy | hy
    · rw [standardExponentialCDF_apply_of_nonpos hy.le, sub_zero]
      constructor
      · intro h; exact absurd h (not_le.2 ((div_lt_one ht0).2 ht))
      · intro h; linarith
    · rw [standardExponentialCDF_apply_of_nonneg hy, sub_sub_cancel, one_div,
        show t⁻¹ = exp (-log t) by rw [exp_neg, exp_log ht0], exp_le_exp]
      constructor <;> intro h <;> linarith
  unfold CumulativeDistributionFunction.tailQuantile
  rw [hS, csInf_Ici]

/-- `U(t) = t^{1/α}` for the Pareto(α) law ([dHF, §1.1]; [EKM, Table 3.4.2]). -/
theorem test_tailQuantile_pareto {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 1 < t) :
    (paretoCDF hα).tailQuantile t = t ^ (1 / α) := by
  have ht0 : 0 < t := by linarith
  have hc : 1 < t ^ (1 / α) := one_lt_rpow ht (one_div_pos.2 hα)
  have hS : {y | 1 - paretoCDF hα y ≤ 1 / t} = Ici (t ^ (1 / α)) := by
    ext y
    simp only [mem_ofPred_eq, mem_Ici]
    rcases lt_or_ge y 1 with hy | hy
    · rw [paretoCDF_apply_of_le_one hα hy.le, sub_zero]
      constructor
      · intro h; exact absurd h (not_le.2 ((div_lt_one ht0).2 ht))
      · intro h; linarith
    · have hy0 : 0 < y := by linarith
      rw [paretoCDF_apply_of_one_le hα hy, sub_sub_cancel, rpow_neg hy0.le, one_div,
        inv_le_inv₀ (rpow_pos_of_pos hy0 _) ht0]
      rw [← rpow_le_rpow_iff (rpow_nonneg ht0.le _) hy0.le hα, ← rpow_mul ht0.le,
        one_div_mul_cancel hα.ne', rpow_one]
  unfold CumulativeDistributionFunction.tailQuantile
  rw [hS, csInf_Ici]

/-- `U(t) = 1 - 1/t` for the uniform law on `[0, 1]` ([dHF, §1.1]). -/
theorem test_tailQuantile_uniform {t : ℝ} (ht : 1 < t) :
    (powerCDF one_pos).tailQuantile t = 1 - 1 / t := by
  have ht0 : 0 < t := by linarith
  have hinv : 0 < 1 / t ∧ 1 / t < 1 := ⟨one_div_pos.2 ht0, (div_lt_one ht0).2 ht⟩
  have hS : {y | 1 - powerCDF one_pos y ≤ 1 / t} = Ici (1 - 1 / t) := by
    ext y
    simp only [mem_ofPred_eq, mem_Ici]
    rcases lt_or_ge y 0 with hy | hy
    · rw [powerCDF_apply_of_nonpos one_pos hy.le]
      constructor <;> intro h <;> linarith
    rcases le_or_gt y 1 with hy1 | hy1
    · rw [powerCDF_apply_of_mem_Icc one_pos ⟨hy, hy1⟩, rpow_one]
      constructor <;> intro h <;> linarith
    · rw [powerCDF_apply_of_one_le one_pos hy1.le]
      constructor <;> intro h <;> linarith
  unfold CumulativeDistributionFunction.tailQuantile
  rw [hS, csInf_Ici]

/-- For Pareto(α), `U` is regularly varying with index `γ = 1/α` ([dHF, Theorem 1.2.1]). -/
theorem test_tailQuantile_pareto_rv {α : ℝ} (hα : 0 < α) :
    IsRegularlyVarying (paretoCDF hα).tailQuantile (1 / α) :=
  (IsRegularlyVarying.rpow_id (1 / α)).congr (by
    filter_upwards [eventually_gt_atTop 1] with t ht using (test_tailQuantile_pareto hα ht).symm)

/-! ### Extended regular variation ([dHF, Appendix B.2]) -/

/-- `D_γ(x) = (x^γ - 1)/γ`: `D_1(x) = x - 1`, `D_{-1}(x) = 1 - 1/x`, `D_0(e) = 1`. -/
theorem test_extRVLimit_values (x : ℝ) :
    extRVLimit 1 x = x - 1 ∧ extRVLimit (-1) x = 1 - x⁻¹ ∧ extRVLimit 0 (exp 1) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [extRVLimit]
  · rw [extRVLimit_of_ne (by norm_num), rpow_neg_one]; ring
  · simp [extRVLimit]

/-- `U(t) = log t` (exponential law) is extended regularly varying with `γ = 0` and auxiliary
function `a ≡ 1` ([dHF, Example 1.1.7]). -/
theorem test_log_isExtendedRV : IsExtendedRegularlyVarying log 0 (fun _ ↦ 1) := by
  refine ⟨Eventually.of_forall fun _ ↦ one_pos, fun x hx ↦ ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [log_mul hx.ne' ht.ne', extRVLimit_zero_left]
  ring

/-- `U(t) = t^γ` with `γ > 0` is extended regularly varying with index `γ` and auxiliary function
`a(t) = γ t^γ` ([dHF, Theorem B.2.2]). Fails if `D_γ` lacked the division by `γ`. -/
theorem test_rpow_isExtendedRV {γ : ℝ} (hγ : 0 < γ) :
    IsExtendedRegularlyVarying (fun t ↦ t ^ γ) γ (fun t ↦ γ * t ^ γ) := by
  refine ⟨?_, fun x hx ↦ ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with t ht using mul_pos hγ (rpow_pos_of_pos ht _)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have := (rpow_pos_of_pos ht γ).ne'
  rw [mul_rpow hx.le ht.le, extRVLimit_of_ne hγ.ne']
  field_simp

/-- For the uniform law, `U(t) = 1 - 1/t` is extended regularly varying with `γ = -1` and
`a(t) = 1/t` ([dHF, §1.1]): `γ = -1` for the uniform law, matching its `MDA(H_{-1})`. -/
theorem test_uniform_tailQuantile_isExtendedRV :
    IsExtendedRegularlyVarying (powerCDF one_pos).tailQuantile (-1) (fun t ↦ 1 / t) := by
  refine ⟨?_, fun x hx ↦ ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with t ht using one_div_pos.2 ht
  refine tendsto_const_nhds.congr' ?_
  have hxt : Tendsto (fun t ↦ x * t) atTop atTop := tendsto_id.const_mul_atTop hx
  filter_upwards [eventually_gt_atTop 1, hxt.eventually_gt_atTop 1] with t ht hxt1
  rw [test_tailQuantile_uniform ht, test_tailQuantile_uniform hxt1, extRVLimit_of_ne (by norm_num),
    rpow_neg_one]
  have : t ≠ 0 := by linarith
  field_simp
  ring

end Test.KnownAnswers.DomainOfAttraction
