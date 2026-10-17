/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.GEV.MaxStable
import ExtremeValueTheory.Statistics.ExtremeQuantile

/-!
# The generalized extreme value family

The **generalized extreme value (GEV) distribution** in the von Mises–Jenkinson
parametrization ([EKM, Definition 3.4.1]; [dHF, Theorem 1.1.3]; [Coles, §3.1.3]) is

  `H_ξ(x) = exp(-(1 + ξ x) ^ (-1/ξ))` for `1 + ξ x > 0`,  `H_0(x) = exp(-e^{-x})`,

extended by `0` (left of the support, `ξ > 0`) or `1` (right of the support, `ξ < 0`). Its
values are `ExtremeValueTheory.gevFun ξ x` (from `Statistics/ExtremeQuantile.lean`). The family
unifies the three standard extreme value laws by explicit affine maps ([EKM, p. 152]):

* `ξ > 0`: `H_ξ(x) = Φ_α(1 + ξ x)` with `α = 1/ξ` (Fréchet);
* `ξ = 0`: `H_0 = Λ` (Gumbel);
* `ξ < 0`: `H_ξ(x) = Ψ_α(-(1 + ξ x))` with `α = -1/ξ` (Weibull).

## Main definitions and results

* `ExtremeValueTheory.gevCDF ξ`: `H_ξ` as a `CumulativeDistributionFunction`, with
  `gevCDF_apply : gevCDF ξ x = gevFun ξ x`.
* `gevCDF_of_pos`, `gevCDF_zero`, `gevCDF_of_neg` and `mkOfCoefs_smul_gevCDF_of_pos`,
  `mkOfCoefs_smul_gevCDF_of_neg`: the explicit affine relations with the three standard types.
* `isExtremeValueDistr_gevCDF`, `isMaxStable_gevCDF`; the explicit max-stability relation
  `gevFun_pow_apply`: `H_ξ(n^ξ x + (n^ξ - 1)/ξ) ^ n = H_ξ(x)` for `ξ ≠ 0`.
* `CumulativeDistributionFunction.IsExtremeValueDistr.exists_smul_eq_gevCDF`: the
  Fisher–Tippett–Gnedenko theorem in the Jenkinson–von Mises form: every extreme value
  distribution is of the type of some `H_ξ`.
* `gevLocScaleCDF ξ μ σ`: the location-scale family `H_ξ((x - μ)/σ)`.
* `tendsto_gevFun_nhds_zero`: continuity in the shape parameter at `ξ = 0`,
  `H_ξ(x) → H_0(x)` as `ξ → 0`, for every `x`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §3.4 [EKM].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  §1.1 [dHF].
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §3.1 [Coles].
-/

open Filter Topology Real CumulativeDistributionFunction

namespace ExtremeValueTheory

/-- The standard **generalized extreme value distribution** `H_ξ` as a c.d.f.: the Fréchet law
`Φ_{1/ξ}` read at `1 + ξ x` for `ξ > 0`, the Weibull law `Ψ_{-1/ξ}` read at `-(1 + ξ x)` for
`ξ < 0`, and the Gumbel law for `ξ = 0`. See `gevCDF_apply` for the closed form. -/
noncomputable def gevCDF (ξ : ℝ) : CumulativeDistributionFunction :=
  if hξ : 0 < ξ then
    (AffineIncrEquiv.mkOfCoefs hξ 1)⁻¹ • standardFrechetCDF (one_div_pos.2 hξ)
  else if hξ' : ξ < 0 then
    (AffineIncrEquiv.mkOfCoefs (neg_pos.2 hξ') (-1))⁻¹ •
      standardWeibullCDF (show 0 < -1 / ξ from div_pos_of_neg_of_neg (by norm_num) hξ')
  else standardGumbelCDF

lemma gevCDF_of_pos {ξ : ℝ} (hξ : 0 < ξ) :
    gevCDF ξ = (AffineIncrEquiv.mkOfCoefs hξ 1)⁻¹ • standardFrechetCDF (one_div_pos.2 hξ) := by
  simp [gevCDF, hξ]

lemma gevCDF_of_neg {ξ : ℝ} (hξ : ξ < 0) :
    gevCDF ξ = (AffineIncrEquiv.mkOfCoefs (neg_pos.2 hξ) (-1))⁻¹ •
      standardWeibullCDF (show 0 < -1 / ξ from div_pos_of_neg_of_neg (by norm_num) hξ) := by
  simp [gevCDF, hξ, not_lt.2 hξ.le]

@[simp] lemma gevCDF_zero : gevCDF 0 = standardGumbelCDF := by
  simp [gevCDF]

/-- For `ξ > 0`, `H_ξ` is the Fréchet law `Φ_{1/ξ}` up to the affine map `x ↦ ξ x + 1`. -/
lemma mkOfCoefs_smul_gevCDF_of_pos {ξ : ℝ} (hξ : 0 < ξ) :
    AffineIncrEquiv.mkOfCoefs hξ 1 • gevCDF ξ = standardFrechetCDF (one_div_pos.2 hξ) := by
  rw [gevCDF_of_pos hξ, smul_inv_smul]

/-- For `ξ < 0`, `H_ξ` is the Weibull law `Ψ_{-1/ξ}` up to the affine map `x ↦ -ξ x - 1`. -/
lemma mkOfCoefs_smul_gevCDF_of_neg {ξ : ℝ} (hξ : ξ < 0) :
    AffineIncrEquiv.mkOfCoefs (neg_pos.2 hξ) (-1) • gevCDF ξ =
      standardWeibullCDF (show 0 < -1 / ξ from div_pos_of_neg_of_neg (by norm_num) hξ) := by
  rw [gevCDF_of_neg hξ, smul_inv_smul]

/-- The c.d.f. `gevCDF ξ` has the closed form `gevFun ξ`. -/
theorem gevCDF_apply (ξ x : ℝ) : gevCDF ξ x = gevFun ξ x := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · have hξ0 : ξ ≠ 0 := hξ.ne
    rw [gevCDF_of_neg hξ, mulAction_apply_eq, inv_inv]
    have hA : AffineIncrEquiv.mkOfCoefs (neg_pos.2 hξ) (-1) x = -(1 + ξ * x) := by
      simp only [AffineIncrEquiv.apply_eq, AffineIncrEquiv.coefs_fst_mkOfCoefs,
        AffineIncrEquiv.coefs_snd_mkOfCoefs]
      ring
    rw [hA]
    by_cases h : 0 < 1 + ξ * x
    · rw [standardWeibullCDF_apply_neg_eq _ (by linarith)]
      simp only [gevFun, hξ0, h, ↓reduceIte, neg_neg]
      rfl
    · rw [standardWeibullCDF_apply_nonneg_eq _ (by linarith)]
      simp [gevFun, hξ0, h, not_lt.2 hξ.le]
  · simp [gevFun, standardGumbelCDF_apply_eq]
  · have hξ0 : ξ ≠ 0 := hξ.ne'
    rw [gevCDF_of_pos hξ, mulAction_apply_eq, inv_inv]
    have hA : AffineIncrEquiv.mkOfCoefs hξ 1 x = 1 + ξ * x := by
      simp only [AffineIncrEquiv.apply_eq, AffineIncrEquiv.coefs_fst_mkOfCoefs,
        AffineIncrEquiv.coefs_snd_mkOfCoefs]
      ring
    rw [hA]
    by_cases h : 0 < 1 + ξ * x
    · rw [standardFrechetCDF_apply_pos_eq _ h]
      simp only [gevFun, hξ0, h, ↓reduceIte]
      rw [neg_div, one_div]
      rfl
    · rw [standardFrechetCDF_apply_nonpos_eq _ (not_lt.1 h)]
      simp [gevFun, hξ0, h, hξ]

lemma coe_gevCDF (ξ : ℝ) : ⇑(gevCDF ξ) = gevFun ξ := funext (gevCDF_apply ξ)

lemma gevFun_nonneg (ξ x : ℝ) : 0 ≤ gevFun ξ x := gevCDF_apply ξ x ▸ (gevCDF ξ).apply_nonneg x

lemma gevFun_le_one (ξ x : ℝ) : gevFun ξ x ≤ 1 := gevCDF_apply ξ x ▸ (gevCDF ξ).apply_le_one x

lemma monotone_gevFun (ξ : ℝ) : Monotone (gevFun ξ) := coe_gevCDF ξ ▸ (gevCDF ξ).mono

/-- Each `H_ξ` is an extreme value distribution. -/
theorem isExtremeValueDistr_gevCDF (ξ : ℝ) : (gevCDF ξ).IsExtremeValueDistr := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · rw [gevCDF_of_neg hξ]
    exact IsExtremeValueDistr.affineTransform _ (isExtremeValueDistr_standardWeibullCDF _) _
  · rw [gevCDF_zero]; exact isExtremeValueDistr_standardGumbelCDF
  · rw [gevCDF_of_pos hξ]
    exact IsExtremeValueDistr.affineTransform _ (isExtremeValueDistr_standardFrechetCDF _) _

/-- Each `H_ξ` is max-stable. -/
theorem isMaxStable_gevCDF (ξ : ℝ) : (gevCDF ξ).IsMaxStable :=
  (isExtremeValueDistr_gevCDF ξ).isMaxStable

/-- Explicit max-stability of the GEV law ([EKM, §3.4]): for `ξ ≠ 0` and `n ≥ 1`,
`H_ξ(n^ξ x + (n^ξ - 1)/ξ) ^ n = H_ξ(x)`. -/
theorem gevFun_pow_apply {ξ : ℝ} (hξ : ξ ≠ 0) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    gevFun ξ ((n : ℝ) ^ ξ * x + ((n : ℝ) ^ ξ - 1) / ξ) ^ n = gevFun ξ x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < (n : ℝ) ^ ξ := rpow_pos_of_pos hn' _
  have key : 1 + ξ * ((n : ℝ) ^ ξ * x + ((n : ℝ) ^ ξ - 1) / ξ) = (n : ℝ) ^ ξ * (1 + ξ * x) := by
    field_simp; ring
  have hiff : 0 < 1 + ξ * ((n : ℝ) ^ ξ * x + ((n : ℝ) ^ ξ - 1) / ξ) ↔ 0 < 1 + ξ * x := by
    rw [key]; exact ⟨fun h ↦ pos_of_mul_pos_right h hc.le, fun h ↦ mul_pos hc h⟩
  by_cases h : 0 < 1 + ξ * x
  · simp only [gevFun, hξ, h, hiff.2 h, ↓reduceIte]
    rw [← exp_nat_mul, key, mul_rpow hc.le h.le, ← rpow_mul hn'.le,
      show ξ * (-1 / ξ) = -1 by field_simp, rpow_neg_one]
    congr 1
    field_simp
  · have h' := mt hiff.1 h
    by_cases hξp : 0 < ξ
    · simp [gevFun, hξ, h, h', hξp, zero_pow (by omega : n ≠ 0)]
    · simp [gevFun, hξ, h, h', hξp]

private lemma standardFrechetCDF_congr {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h : α = β) :
    standardFrechetCDF hα = standardFrechetCDF hβ := by
  subst h; rfl

private lemma standardWeibullCDF_congr {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h : α = β) :
    standardWeibullCDF hα = standardWeibullCDF hβ := by
  subst h; rfl

/-- **Fisher–Tippett–Gnedenko theorem, Jenkinson–von Mises form** ([EKM, Theorem 3.4.5];
[dHF, Theorem 1.1.3]): every extreme value distribution is of the type of a GEV law `H_ξ`. -/
theorem _root_.CumulativeDistributionFunction.IsExtremeValueDistr.exists_smul_eq_gevCDF
    {G : CumulativeDistributionFunction} (hG : G.IsExtremeValueDistr) :
    ∃ (A : AffineIncrEquiv) (ξ : ℝ), A • G = gevCDF ξ := by
  rcases hG.classification with ⟨A, hA⟩ | ⟨A, α, hα, hA⟩ | ⟨A, α, hα, hA⟩
  · exact ⟨A, 0, by rw [hA, gevCDF_zero]⟩
  · have hξ : 0 < 1 / α := one_div_pos.2 hα
    refine ⟨(AffineIncrEquiv.mkOfCoefs hξ 1)⁻¹ * A, 1 / α, ?_⟩
    rw [mul_smul, hA, gevCDF_of_pos hξ,
      standardFrechetCDF_congr (one_div_pos.2 hξ) hα (one_div_one_div α)]
  · have hξ : -(1 / α) < 0 := neg_neg_of_pos (one_div_pos.2 hα)
    refine ⟨(AffineIncrEquiv.mkOfCoefs (neg_pos.2 hξ) (-1))⁻¹ * A, -(1 / α), ?_⟩
    rw [mul_smul, hA, gevCDF_of_neg hξ]
    congr 1
    exact standardWeibullCDF_congr _ _ (by field_simp)

/-- The location-scale GEV law `H_{ξ,μ,σ}(x) = H_ξ((x - μ)/σ)` ([Coles, §3.1.3]). -/
noncomputable def gevLocScaleCDF (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    CumulativeDistributionFunction :=
  AffineIncrEquiv.mkOfCoefs hσ μ • gevCDF ξ

lemma gevLocScaleCDF_apply (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    gevLocScaleCDF ξ μ hσ x = gevFun ξ ((x - μ) / σ) := by
  rw [gevLocScaleCDF, mulAction_apply_eq, gevCDF_apply]
  congr 1
  simp
  field_simp
  ring

lemma isExtremeValueDistr_gevLocScaleCDF (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (gevLocScaleCDF ξ μ hσ).IsExtremeValueDistr :=
  IsExtremeValueDistr.affineTransform _ (isExtremeValueDistr_gevCDF ξ) _

/-- The `m`-block return level of the location-scale law `H_{ξ,μ,σ}` is `μ + σ z_m`. -/
lemma gevLocScaleCDF_returnLevel (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) {m : ℝ} (hm : 1 < m) :
    gevLocScaleCDF ξ μ hσ (μ + σ * returnLevel ξ m) = 1 - 1 / m := by
  rw [gevLocScaleCDF_apply, add_sub_cancel_left, mul_div_cancel_left₀ _ hσ.ne',
    gevFun_returnLevel ξ hm]

/-! ### Continuity in the shape parameter -/

/-- `ξ⁻¹ log(1 + ξ x) → x` as `ξ → 0`, `ξ ≠ 0`. -/
lemma tendsto_inv_mul_log_one_add_mul (x : ℝ) :
    Tendsto (fun ξ : ℝ ↦ ξ⁻¹ * log (1 + ξ * x)) (𝓝[≠] 0) (𝓝 x) := by
  have hf : HasDerivAt (fun ξ : ℝ ↦ 1 + ξ * x) x 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x).const_add 1
  have hlog := hf.log (by simp)
  rw [hasDerivAt_iff_tendsto_slope_zero] at hlog
  simpa using hlog

/-- **Continuity of the GEV family in the shape parameter at `ξ = 0`**: for every `x`,
`H_ξ(x) → H_0(x) = exp(-e^{-x})` as `ξ → 0` ([EKM, p. 152]; [Coles, §3.1.3]). -/
theorem tendsto_gevFun_nhds_zero (x : ℝ) :
    Tendsto (fun ξ ↦ gevFun ξ x) (𝓝 0) (𝓝 (gevFun 0 x)) := by
  refine (continuousWithinAt_compl_self.1 ?_).tendsto
  rw [ContinuousWithinAt]
  have hpos : ∀ᶠ ξ in 𝓝[≠] (0 : ℝ), 0 < 1 + ξ * x := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have : Tendsto (fun ξ : ℝ ↦ 1 + ξ * x) (𝓝 0) (𝓝 1) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const x).const_add (1 : ℝ)
    exact this.eventually (lt_mem_nhds one_pos)
  have hlim : Tendsto (fun ξ : ℝ ↦ exp (-exp (-(ξ⁻¹ * log (1 + ξ * x))))) (𝓝[≠] 0)
      (𝓝 (exp (-exp (-x)))) :=
    ((continuous_exp.comp (continuous_exp.comp continuous_neg).neg).tendsto x).comp
      (tendsto_inv_mul_log_one_add_mul x)
  simp only [gevFun, ↓reduceIte]
  refine hlim.congr' ?_
  filter_upwards [hpos, self_mem_nhdsWithin] with ξ hξ hξ0
  have hξ0 : ξ ≠ 0 := hξ0
  simp only [hξ0, hξ, ↓reduceIte, rpow_def_of_pos hξ]
  congr 3
  field_simp

/-- The GEV c.d.f.s converge to the Gumbel c.d.f. at every point as `ξ → 0`. -/
theorem tendsto_gevCDF_nhds_zero (x : ℝ) :
    Tendsto (fun ξ ↦ gevCDF ξ x) (𝓝 0) (𝓝 (standardGumbelCDF x)) := by
  have h := tendsto_gevFun_nhds_zero x
  simp only [← gevCDF_apply, gevCDF_zero] at h
  exact h

end ExtremeValueTheory
