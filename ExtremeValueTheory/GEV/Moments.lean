/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.GEV.Family
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Probability.Moments.Variance

/-!
# Moments of the generalized extreme value distributions

If `T` is a standard exponential random variable then

  `(T ^ (-ξ) - 1) / ξ` (`-log T` for `ξ = 0`)

has the GEV law `H_ξ`, since `P(T ≥ (1 + ξ x) ^ (-1/ξ)) = exp(-(1 + ξ x) ^ (-1/ξ))`. This
representation turns every moment of `H_ξ` into an Euler integral, and gives ([EKM, §3.4],
[Coles, §3.1], [dHF, Exercise 1.16]):

* the mean of the Gumbel law is the Euler–Mascheroni constant `γ`;
* for `ξ < 1`, `ξ ≠ 0`, the mean of `H_ξ` is `(Γ(1 - ξ) - 1) / ξ`;
* for `ξ < 1/2`, `ξ ≠ 0`, the second moment is `(Γ(1 - 2ξ) - 2 Γ(1 - ξ) + 1) / ξ²` and the
  variance is `(Γ(1 - 2ξ) - Γ(1 - ξ)²) / ξ²`;
* the mean of the Fréchet law `Φ_α`, `α > 1`, is `Γ(1 - 1/α)`, and the mean of the Weibull law
  `Ψ_α` is `-Γ(1 + 1/α)`;
* the mean of the location-scale law `H_{ξ,μ,σ}` is `μ + σ (Γ(1 - ξ) - 1) / ξ`.

## Main definitions and results

* `ExtremeValueTheory.stdExpMeasure`: the standard exponential law on `(0, ∞)`.
* `ExtremeValueTheory.gevTransform ξ t`: the map `t ↦ (t ^ (-ξ) - 1) / ξ` (`-log t` at `ξ = 0`).
* `measure_gevCDF_eq_map`: `H_ξ` is the image of the standard exponential law under
  `gevTransform ξ`.
* `CumulativeDistributionFunction.measure_smul_eq_map`: the law of `A • F` is the image of the
  law of `F` under `A`.
* `integral_id_gevCDF_zero`: `∫ x dΛ(x) = γ`.
* `integrable_id_gevCDF`, `integral_id_gevCDF`: `∫ x dH_ξ(x) = (Γ(1 - ξ) - 1) / ξ`.
* `integral_sq_gevCDF`, `variance_id_gevCDF`: second moment and variance for `ξ < 1/2`.
* `integral_id_standardFrechetCDF`, `integral_id_standardWeibullCDF`,
  `integral_id_gevLocScaleCDF`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §3.4 [EKM].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 1 [dHF].
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §3.1 [Coles].
-/

open Filter Topology Real MeasureTheory Set ExtremeValueTheory.CumulativeDistributionFunction ProbabilityTheory

namespace ExtremeValueTheory.CumulativeDistributionFunction

/-- The law of `A • F` is the image of the law of `F` under the affine map
`x ↦ a x + b`, `(a, b) = A.coefs`. -/
theorem measure_smul_eq_map (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    (A • F).measure = F.measure.map (fun x ↦ A.coefs.1 * x + A.coefs.2) := by
  have ha := A.coefs_fst_pos
  have hm : Measurable (fun x : ℝ ↦ A.coefs.1 * x + A.coefs.2) := by fun_prop
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply hm measurableSet_Iic,
    StieltjesFunction.measure_Iic _ (A • F).tendsto_atBot]
  have hpre : (fun x : ℝ ↦ A.coefs.1 * x + A.coefs.2) ⁻¹' Iic x =
      Iic (A.coefs.1⁻¹ * x + -A.coefs.1⁻¹ * A.coefs.2) := by
    ext y
    simp only [mem_preimage, mem_Iic]
    rw [show A.coefs.1⁻¹ * x + -A.coefs.1⁻¹ * A.coefs.2 = (x - A.coefs.2) / A.coefs.1 by
      field_simp; ring, le_div_iff₀ ha]
    constructor <;> intro h <;> linarith
  rw [hpre, StieltjesFunction.measure_Iic _ F.tendsto_atBot, sub_zero, sub_zero]
  congr 1
  change F (A⁻¹ x) = _
  simp

/-- First moment of an affine transform: `∫ x d(A • F) = a ∫ x dF + b`. -/
theorem integral_id_smul (F : CumulativeDistributionFunction) (A : AffineIncrEquiv)
    (hF : Integrable (fun x ↦ x) F.measure) :
    ∫ x, x ∂(A • F).measure = A.coefs.1 * ∫ x, x ∂F.measure + A.coefs.2 := by
  rw [measure_smul_eq_map, integral_map (f := fun x : ℝ ↦ x) (by fun_prop) (by fun_prop),
    integral_add (hF.const_mul _) (integrable_const _), integral_const_mul]
  simp

lemma integrable_id_smul (F : CumulativeDistributionFunction) (A : AffineIncrEquiv)
    (hF : Integrable (fun x ↦ x) F.measure) :
    Integrable (fun x ↦ x) (A • F).measure := by
  rw [measure_smul_eq_map, integrable_map_measure (g := fun x : ℝ ↦ x) (by fun_prop)
    (by fun_prop)]
  exact (hF.const_mul _).add (integrable_const _)

end ExtremeValueTheory.CumulativeDistributionFunction

namespace ExtremeValueTheory

/-- The standard exponential law, as the measure `e^{-t} dt` on `(0, ∞)`. -/
noncomputable def stdExpMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t ↦ ENNReal.ofReal (exp (-t))

/-- The transformation `t ↦ (t ^ (-ξ) - 1) / ξ` (`-log t` for `ξ = 0`) carrying the standard
exponential law to `H_ξ`. -/
noncomputable def gevTransform (ξ t : ℝ) : ℝ :=
  if ξ = 0 then -log t else (t ^ (-ξ) - 1) / ξ

lemma measurable_gevTransform (ξ : ℝ) : Measurable (gevTransform ξ) := by
  by_cases h : ξ = 0
  · have : gevTransform ξ = fun t ↦ -log t := funext fun t ↦ by simp [gevTransform, h]
    rw [this]; fun_prop
  · have : gevTransform ξ = fun t ↦ (t ^ (-ξ) - 1) / ξ :=
      funext fun t ↦ by simp [gevTransform, h]
    rw [this]; fun_prop

private lemma measurable_expDensity :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (exp (-t)) := by fun_prop

private lemma setLIntegral_exp_neg_Ioi (c : ℝ) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (exp (-t)) = ENNReal.ofReal (exp (-c)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi c)
    (ae_of_all _ fun t ↦ (exp_pos (-t)).le), integral_exp_neg_Ioi]

private lemma setLIntegral_exp_neg_Ici (c : ℝ) :
    ∫⁻ t in Ici c, ENNReal.ofReal (exp (-t)) = ENNReal.ofReal (exp (-c)) := by
  rw [← setLIntegral_exp_neg_Ioi c]
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

/-- The threshold computation for `ξ ≠ 0` inside the support. -/
private lemma gevTransform_le_iff {ξ x t : ℝ} (hξ : ξ ≠ 0) (hc : 0 < 1 + ξ * x) (ht : 0 < t) :
    gevTransform ξ t ≤ x ↔ (1 + ξ * x) ^ (-1 / ξ) ≤ t := by
  have hcc : ((1 + ξ * x) ^ (-1 / ξ)) ^ (-ξ) = 1 + ξ * x := by
    rw [← rpow_mul hc.le, show -1 / ξ * -ξ = 1 by field_simp, rpow_one]
  have hcpos : 0 < (1 + ξ * x) ^ (-1 / ξ) := rpow_pos_of_pos hc _
  simp only [gevTransform, hξ, ↓reduceIte]
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · rw [div_le_iff_of_neg hneg]
    calc x * ξ ≤ t ^ (-ξ) - 1 ↔ ((1 + ξ * x) ^ (-1 / ξ)) ^ (-ξ) ≤ t ^ (-ξ) := by
          rw [hcc]; constructor <;> intro h <;> linarith
      _ ↔ _ := rpow_le_rpow_iff hcpos.le ht.le (by linarith)
  · rw [div_le_iff₀ hpos]
    calc t ^ (-ξ) - 1 ≤ x * ξ ↔ t ^ (-ξ) ≤ ((1 + ξ * x) ^ (-1 / ξ)) ^ (-ξ) := by
          rw [hcc]; constructor <;> intro h <;> linarith
      _ ↔ _ := rpow_le_rpow_iff_of_neg ht hcpos (by linarith)

/-- **Exponential representation of the GEV law**: `H_ξ` is the law of `(T ^ (-ξ) - 1) / ξ`
(of `-log T` for `ξ = 0`) for a standard exponential `T`. -/
theorem measure_gevCDF_eq_map (ξ : ℝ) :
    (gevCDF ξ).measure = stdExpMeasure.map (gevTransform ξ) := by
  have hm := measurable_gevTransform ξ
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  have hS : MeasurableSet (gevTransform ξ ⁻¹' Iic x) := hm measurableSet_Iic
  rw [StieltjesFunction.measure_Iic _ (gevCDF ξ).tendsto_atBot, sub_zero,
    Measure.map_apply hm measurableSet_Iic, stdExpMeasure, withDensity_apply _ hS,
    Measure.restrict_restrict hS]
  change ENNReal.ofReal (gevCDF ξ x) = _
  rw [gevCDF_apply]
  by_cases hξ : ξ = 0
  · subst hξ
    have hset : gevTransform 0 ⁻¹' Iic x ∩ Ioi 0 = Ici (exp (-x)) := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_Ici, gevTransform,
        ↓reduceIte]
      constructor
      · rintro ⟨h, ht⟩
        exact (le_log_iff_exp_le ht).1 (by linarith)
      · intro h
        have ht : 0 < t := (exp_pos _).trans_le h
        exact ⟨by linarith [(le_log_iff_exp_le ht).2 h], ht⟩
    rw [hset, setLIntegral_exp_neg_Ici]
    simp [gevFun]
  by_cases hc : 0 < 1 + ξ * x
  · have hcpos : 0 < (1 + ξ * x) ^ (-1 / ξ) := rpow_pos_of_pos hc _
    have hset : gevTransform ξ ⁻¹' Iic x ∩ Ioi 0 = Ici ((1 + ξ * x) ^ (-1 / ξ)) := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_Ici]
      constructor
      · rintro ⟨h, ht⟩
        exact (gevTransform_le_iff hξ hc ht).1 h
      · intro h
        have ht : 0 < t := hcpos.trans_le h
        exact ⟨(gevTransform_le_iff hξ hc ht).2 h, ht⟩
    rw [hset, setLIntegral_exp_neg_Ici]
    simp [gevFun, hξ, hc]
  · rcases lt_or_gt_of_ne hξ with hneg | hpos
    · have hset : gevTransform ξ ⁻¹' Iic x ∩ Ioi 0 = Ioi 0 := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, gevTransform, hξ,
          ↓reduceIte, and_iff_right_iff_imp]
        intro ht
        rw [div_le_iff_of_neg hneg]
        have := rpow_pos_of_pos ht (-ξ)
        linarith
      rw [hset, setLIntegral_exp_neg_Ioi]
      simp [gevFun, hξ, hc, not_lt.2 hneg.le]
    · have hset : gevTransform ξ ⁻¹' Iic x ∩ Ioi 0 = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, gevTransform, hξ,
          ↓reduceIte, mem_empty_iff_false, iff_false, not_and]
        intro h ht
        rw [div_le_iff₀ hpos] at h
        have := rpow_pos_of_pos ht (-ξ)
        linarith
      rw [hset]
      simp [gevFun, hξ, hc, hpos]

/-- Integrals against `H_ξ` as Euler-type integrals. -/
theorem integral_gevCDF (ξ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂(gevCDF ξ).measure = ∫ t in Ioi 0, exp (-t) * f (gevTransform ξ t) := by
  rw [measure_gevCDF_eq_map, integral_map (measurable_gevTransform ξ).aemeasurable
    hf.aestronglyMeasurable, stdExpMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_expDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  congr 1
  funext t
  rw [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]

/-- Integrability against `H_ξ` in terms of the exponential representation. -/
theorem integrable_gevCDF_iff (ξ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (gevCDF ξ).measure ↔
      IntegrableOn (fun t ↦ exp (-t) * f (gevTransform ξ t)) (Ioi 0) := by
  rw [measure_gevCDF_eq_map, integrable_map_measure hf.aestronglyMeasurable
    (measurable_gevTransform ξ).aemeasurable, stdExpMeasure, integrable_withDensity_iff
    measurable_expDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top), IntegrableOn]
  refine integrable_congr (ae_of_all _ fun t ↦ ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (exp_pos _).le, mul_comm]

/-- `t ↦ log t · e^{-t}` is integrable on `(0, ∞)`. -/
lemma integrableOn_log_mul_exp_neg : IntegrableOn (fun t ↦ log t * exp (-t)) (Ioi 0) := by
  have h1 := (GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
  have h2 := GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)
  refine Integrable.mono' (h1.add h2) (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  show ‖log t * exp (-t)‖ ≤
    2 * (exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) + exp (-t) * t ^ ((2 : ℝ) - 1)
  have hlo := neg_rpow_div_le_log ht.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hhi := log_le_self ht.le
  have hr : 0 < t ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos ht _
  have he := exp_pos (-t)
  rw [norm_mul, norm_of_nonneg he.le, Real.norm_eq_abs,
    show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, show (2 : ℝ) - 1 = 1 by norm_num, rpow_one]
  have habs : |log t| ≤ 2 * t ^ (-(1 / 2 : ℝ)) + t := by
    rw [abs_le]; constructor <;> nlinarith
  calc |log t| * exp (-t) ≤ (2 * t ^ (-(1 / 2 : ℝ)) + t) * exp (-t) :=
        mul_le_mul_of_nonneg_right habs he.le
    _ = 2 * (exp (-t) * t ^ (-(1 / 2 : ℝ))) + exp (-t) * t := by ring

/-- The Gumbel law has a finite mean. -/
theorem integrable_id_gevCDF_zero : Integrable (fun x ↦ x) (gevCDF 0).measure := by
  rw [integrable_gevCDF_iff 0 measurable_id']
  refine (integrableOn_log_mul_exp_neg.neg).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp [gevTransform]; ring

/-- **The mean of the standard Gumbel law is the Euler–Mascheroni constant**
([EKM, §3.4]; [Coles, §3.1]). -/
theorem integral_id_gevCDF_zero :
    ∫ x, x ∂(gevCDF 0).measure = eulerMascheroniConstant := by
  rw [integral_gevCDF 0 measurable_id', eulerMascheroniConstant_eq_neg_integral_log,
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ ?_)
  simp [gevTransform]; ring

/-- The mean of the standard Gumbel law `Λ` is `γ`. -/
theorem integral_id_standardGumbelCDF :
    ∫ x, x ∂standardGumbelCDF.measure = eulerMascheroniConstant := by
  rw [← gevCDF_zero, integral_id_gevCDF_zero]

private lemma gevTransform_eq {ξ : ℝ} (hξ : ξ ≠ 0) (t : ℝ) :
    exp (-t) * gevTransform ξ t =
      ξ⁻¹ * (exp (-t) * t ^ ((1 - ξ) - 1)) - ξ⁻¹ * (exp (-t) * t ^ ((1 : ℝ) - 1)) := by
  simp only [gevTransform, hξ, ↓reduceIte, sub_self, rpow_zero, sub_sub_cancel_left]
  ring

private lemma integrableOn_gamma (c : ℝ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t ↦ c * (exp (-t) * t ^ (s - 1))) (Ioi 0) :=
  (GammaIntegral_convergent hs).const_mul c

private lemma integral_gamma (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioi 0, c * (exp (-t) * t ^ (s - 1)) = c * Gamma s := by
  rw [integral_const_mul, Gamma_eq_integral hs]

/-- For `ξ < 1` the GEV law `H_ξ` has a finite mean. -/
theorem integrable_id_gevCDF {ξ : ℝ} (hξ : ξ < 1) : Integrable (fun x ↦ x) (gevCDF ξ).measure := by
  by_cases h0 : ξ = 0
  · subst h0; exact integrable_id_gevCDF_zero
  rw [integrable_gevCDF_iff ξ measurable_id']
  have h : IntegrableOn (fun t ↦ ξ⁻¹ * (exp (-t) * t ^ ((1 - ξ) - 1)) -
      ξ⁻¹ * (exp (-t) * t ^ ((1 : ℝ) - 1))) (Ioi 0) :=
    (integrableOn_gamma _ (by linarith : 0 < 1 - ξ)).sub (integrableOn_gamma _ one_pos)
  exact h.congr_fun (fun t _ ↦ (gevTransform_eq h0 t).symm) measurableSet_Ioi

/-- **Mean of the GEV law** ([EKM, §3.4]; [Coles, §3.1]): for `ξ < 1`, `ξ ≠ 0`,
`∫ x dH_ξ(x) = (Γ(1 - ξ) - 1) / ξ`. -/
theorem integral_id_gevCDF {ξ : ℝ} (hξ : ξ < 1) (h0 : ξ ≠ 0) :
    ∫ x, x ∂(gevCDF ξ).measure = (Gamma (1 - ξ) - 1) / ξ := by
  rw [integral_gevCDF ξ measurable_id', setIntegral_congr_fun measurableSet_Ioi
    (fun t _ ↦ gevTransform_eq h0 t), integral_sub
    (integrableOn_gamma _ (by linarith : 0 < 1 - ξ)) (integrableOn_gamma _ one_pos),
    integral_gamma _ (by linarith), integral_gamma _ one_pos, Gamma_one]
  field_simp

private lemma gevTransform_sq_eq {ξ : ℝ} (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    exp (-t) * gevTransform ξ t ^ 2 =
      (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - 2 * ξ) - 1)) -
        2 * (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - ξ) - 1)) +
        (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 : ℝ) - 1)) := by
  have h2 : t ^ ((1 - 2 * ξ) - 1) = (t ^ (-ξ)) ^ 2 := by
    rw [← rpow_natCast, ← rpow_mul ht.le]; congr 1; push_cast; ring
  rw [h2, sub_sub_cancel_left, sub_self, rpow_zero]
  simp only [gevTransform, hξ, ↓reduceIte]
  field_simp
  ring

private lemma integrableOn_gevTransform_sq {ξ : ℝ} (hξ : ξ < 1 / 2) :
    IntegrableOn (fun t ↦ (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - 2 * ξ) - 1)) -
        2 * (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - ξ) - 1))) (Ioi 0) ∧
      IntegrableOn (fun t ↦ (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - 2 * ξ) - 1)) -
        2 * (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - ξ) - 1)) +
        (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 : ℝ) - 1))) (Ioi 0) := by
  have h12 : IntegrableOn (fun t ↦ (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - 2 * ξ) - 1)) -
      2 * (ξ ^ 2)⁻¹ * (exp (-t) * t ^ ((1 - ξ) - 1))) (Ioi 0) :=
    (integrableOn_gamma _ (by linarith : 0 < 1 - 2 * ξ)).sub
      (integrableOn_gamma _ (by linarith : 0 < 1 - ξ))
  exact ⟨h12, h12.add (integrableOn_gamma _ one_pos)⟩

/-- For `ξ < 1/2` the GEV law `H_ξ` has a finite second moment. -/
theorem integrable_sq_gevCDF {ξ : ℝ} (hξ : ξ < 1 / 2) (h0 : ξ ≠ 0) :
    Integrable (fun x ↦ x ^ 2) (gevCDF ξ).measure := by
  rw [integrable_gevCDF_iff ξ (by fun_prop)]
  exact (integrableOn_gevTransform_sq hξ).2.congr_fun
    (fun t ht ↦ (gevTransform_sq_eq h0 ht).symm) measurableSet_Ioi

/-- **Second moment of the GEV law**: for `ξ < 1/2`, `ξ ≠ 0`,
`∫ x² dH_ξ(x) = (Γ(1 - 2ξ) - 2 Γ(1 - ξ) + 1) / ξ²`. -/
theorem integral_sq_gevCDF {ξ : ℝ} (hξ : ξ < 1 / 2) (h0 : ξ ≠ 0) :
    ∫ x, x ^ 2 ∂(gevCDF ξ).measure = (Gamma (1 - 2 * ξ) - 2 * Gamma (1 - ξ) + 1) / ξ ^ 2 := by
  rw [integral_gevCDF ξ (by fun_prop), setIntegral_congr_fun measurableSet_Ioi
    (fun t ht ↦ gevTransform_sq_eq h0 ht),
    integral_add (integrableOn_gevTransform_sq hξ).1 (integrableOn_gamma _ one_pos),
    integral_sub (integrableOn_gamma _ (by linarith : 0 < 1 - 2 * ξ))
      (integrableOn_gamma _ (by linarith : 0 < 1 - ξ)),
    integral_gamma _ (by linarith), integral_gamma _ (by linarith), integral_gamma _ one_pos,
    Gamma_one]
  field_simp

/-- **Variance of the GEV law** ([Coles, §3.1]; [EKM, §3.4]): for `ξ < 1/2`, `ξ ≠ 0`,
`Var H_ξ = (Γ(1 - 2ξ) - Γ(1 - ξ)²) / ξ²`. -/
theorem variance_id_gevCDF {ξ : ℝ} (hξ : ξ < 1 / 2) (h0 : ξ ≠ 0) :
    variance (fun x ↦ x) (gevCDF ξ).measure = (Gamma (1 - 2 * ξ) - Gamma (1 - ξ) ^ 2) / ξ ^ 2 := by
  have hL2 : MemLp (fun x : ℝ ↦ x) 2 (gevCDF ξ).measure :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_sq_gevCDF hξ h0)
  rw [variance_eq_sub hL2]
  change ∫ x, x ^ 2 ∂(gevCDF ξ).measure - (∫ x, x ∂(gevCDF ξ).measure) ^ 2 = _
  rw [integral_sq_gevCDF hξ h0, integral_id_gevCDF (by linarith) h0]
  field_simp
  ring

/-- **Mean of the Fréchet law**: for `α > 1`, `∫ x dΦ_α(x) = Γ(1 - 1/α)`. -/
theorem integral_id_standardFrechetCDF {α : ℝ} (hα : 1 < α) :
    ∫ x, x ∂(standardFrechetCDF (zero_lt_one.trans hα)).measure = Gamma (1 - 1 / α) := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hξ : 0 < 1 / α := one_div_pos.2 hα0
  have hξ1 : 1 / α < 1 := (div_lt_one hα0).2 hα
  have hF : standardFrechetCDF hα0 = AffineIncrEquiv.mkOfCoefs hξ 1 • gevCDF (1 / α) := by
    rw [mkOfCoefs_smul_gevCDF_of_pos hξ]
    congr 1
    exact (one_div_one_div α).symm
  rw [hF, integral_id_smul _ _ (integrable_id_gevCDF hξ1),
    integral_id_gevCDF hξ1 hξ.ne', AffineIncrEquiv.coefs_fst_mkOfCoefs,
    AffineIncrEquiv.coefs_snd_mkOfCoefs]
  field_simp
  ring

/-- **Mean of the Weibull law**: for `α > 0`, `∫ x dΨ_α(x) = -Γ(1 + 1/α)`. -/
theorem integral_id_standardWeibullCDF {α : ℝ} (hα : 0 < α) :
    ∫ x, x ∂(standardWeibullCDF hα).measure = -Gamma (1 + 1 / α) := by
  have hξ : -(1 / α) < 0 := neg_neg_of_pos (one_div_pos.2 hα)
  have hξ1 : -(1 / α) < 1 := hξ.trans one_pos
  have hF : standardWeibullCDF hα =
      AffineIncrEquiv.mkOfCoefs (neg_pos.2 hξ) (-1) • gevCDF (-(1 / α)) := by
    rw [mkOfCoefs_smul_gevCDF_of_neg hξ]
    congr 1
    field_simp
  rw [hF, integral_id_smul _ _ (integrable_id_gevCDF hξ1),
    integral_id_gevCDF hξ1 hξ.ne, AffineIncrEquiv.coefs_fst_mkOfCoefs,
    AffineIncrEquiv.coefs_snd_mkOfCoefs, sub_neg_eq_add]
  field_simp
  ring

/-- **Mean of the location-scale GEV law**: for `ξ < 1`, `ξ ≠ 0`,
`∫ x dH_{ξ,μ,σ}(x) = μ + σ (Γ(1 - ξ) - 1) / ξ`. -/
theorem integral_id_gevLocScaleCDF {ξ : ℝ} (hξ : ξ < 1) (h0 : ξ ≠ 0) (μ : ℝ) {σ : ℝ}
    (hσ : 0 < σ) :
    ∫ x, x ∂(gevLocScaleCDF ξ μ hσ).measure = μ + σ * (Gamma (1 - ξ) - 1) / ξ := by
  rw [gevLocScaleCDF, integral_id_smul _ _ (integrable_id_gevCDF hξ), integral_id_gevCDF hξ h0,
    AffineIncrEquiv.coefs_fst_mkOfCoefs, AffineIncrEquiv.coefs_snd_mkOfCoefs]
  ring

/-- The location-scale Gumbel law `Λ((x - μ)/σ)` has mean `μ + σ γ`. -/
theorem integral_id_gevLocScaleCDF_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x, x ∂(gevLocScaleCDF 0 μ hσ).measure = μ + σ * eulerMascheroniConstant := by
  rw [gevLocScaleCDF, integral_id_smul _ _ integrable_id_gevCDF_zero, integral_id_gevCDF_zero,
    AffineIncrEquiv.coefs_fst_mkOfCoefs, AffineIncrEquiv.coefs_snd_mkOfCoefs]
  ring

/-! ### Probability-weighted moments -/

/-- On the exponential scale the GEV distribution function is explicit:
`H_ξ((t ^ (-ξ) - 1) / ξ) = e^{-t}` for `t > 0`. -/
lemma gevFun_gevTransform (ξ : ℝ) {t : ℝ} (ht : 0 < t) :
    gevFun ξ (gevTransform ξ t) = exp (-t) := by
  by_cases h0 : ξ = 0
  · simp [gevFun, gevTransform, h0, exp_log ht]
  · have hk : 1 + ξ * gevTransform ξ t = t ^ (-ξ) := by
      simp only [gevTransform, h0, ↓reduceIte]; field_simp; ring
    have hpos : 0 < 1 + ξ * gevTransform ξ t := hk ▸ rpow_pos_of_pos ht _
    simp only [gevFun, h0, ↓reduceIte, hpos]
    rw [hk, ← rpow_mul ht.le, show -ξ * (-1 / ξ) = 1 by field_simp, rpow_one]

private lemma integrableOn_rpow_mul_exp_neg_mul {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t ↦ t ^ (a - 1) * exp (-(r * t))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := a - 1) (p := 1) (b := r) (by linarith)
    one_pos hr).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp [rpow_one, neg_mul]

/-- **Probability-weighted moments of the GEV law** (Hosking, Wallis and Wood, *Estimation of
the generalized extreme-value distribution by the method of probability-weighted moments*,
Technometrics 27 (1985)): for `ξ < 1`, `ξ ≠ 0` and `r ∈ ℕ`,
`β_r = E[X H_ξ(X) ^ r] = ((r + 1) ^ ξ Γ(1 - ξ) - 1) / (ξ (r + 1))`. -/
theorem integral_mul_gevFun_pow_gevCDF {ξ : ℝ} (hξ : ξ < 1) (h0 : ξ ≠ 0) (r : ℕ) :
    ∫ x, x * gevFun ξ x ^ r ∂(gevCDF ξ).measure =
      (((r : ℝ) + 1) ^ ξ * Gamma (1 - ξ) - 1) / (ξ * ((r : ℝ) + 1)) := by
  have hr : (0 : ℝ) < r + 1 := by positivity
  have hmeas : Measurable fun x ↦ x * gevFun ξ x ^ r :=
    measurable_id.mul ((monotone_gevFun ξ).measurable.pow_const r)
  have key : ∀ t ∈ Ioi (0 : ℝ), exp (-t) * (gevTransform ξ t * gevFun ξ (gevTransform ξ t) ^ r) =
      ξ⁻¹ * (t ^ ((1 - ξ) - 1) * exp (-((r + 1) * t))) -
        ξ⁻¹ * (t ^ ((1 : ℝ) - 1) * exp (-((r + 1) * t))) := by
    intro t ht
    rw [gevFun_gevTransform ξ ht, ← exp_nat_mul, sub_sub_cancel_left, sub_self, rpow_zero,
      show -(((r : ℝ) + 1) * t) = -t + r * -t by ring, exp_add]
    simp only [gevTransform, h0, ↓reduceIte]
    field_simp
  rw [integral_gevCDF ξ hmeas, setIntegral_congr_fun measurableSet_Ioi key,
    integral_sub ((integrableOn_rpow_mul_exp_neg_mul (by linarith) hr).const_mul _)
      ((integrableOn_rpow_mul_exp_neg_mul one_pos hr).const_mul _),
    integral_const_mul, integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hr,
    integral_rpow_mul_exp_neg_mul_Ioi one_pos hr, Gamma_one, rpow_one,
    div_rpow zero_le_one hr.le, one_rpow, rpow_sub hr, rpow_one]
  field_simp

end ExtremeValueTheory
