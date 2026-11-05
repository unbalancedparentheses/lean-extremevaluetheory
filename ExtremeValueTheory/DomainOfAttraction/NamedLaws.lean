/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.GEVDomain
import ExtremeValueTheory.DomainOfAttraction.OfMeasure
import ExtremeValueTheory.GEV.Family
import ExtremeValueTheory.GEV.MaxStable
import ExtremeValueTheory.RegularVariation.KaramataConverse
import ExtremeValueTheory.Statistics.GPDLikelihood
import Mathlib.Probability.Distributions.Cauchy

/-!
# Domains of attraction of further named laws, and explicit norming constants

`DomainOfAttraction/VonMises.lean`, `Gumbel.lean` and `GEVDomain.lean` place the Pareto, power and
exponential laws in their domains. This file adds other standard laws, and the explicit norming
constants of the first three ([EKM, Tables 3.4.2–3.4.4]).

## Main definitions

* `ExtremeValueTheory.studentTMeasure ν`: Student's t law with `ν > 0` degrees of freedom. Its
  density is `c (1 + x² / ν) ^ (-(ν + 1) / 2)`, with `c` *defined* as the normalizing constant;
  the classical formula for `c` in terms of `Γ` is not proved here.

## Main results

* `IsRegularlyVarying.integral_Ioi`: if `f` is measurable and regularly varying with index
  `-(α + 1)`, `α > 0`, then its tail integral is regularly varying with index `-α`.
* `isRegularlyVarying_measureReal_Ioi_withDensity`: the same for the tail of a law with a density.
* Norming constants: `tendsto_paretoCDF_pow`, `tendsto_powerCDF_pow`,
  `tendsto_standardExponentialCDF_pow`.
* `isInMDAGEV_ofMeasure_gpdMeasure`: `GPD(ξ, σ)` is in `MDA(H_ξ)` for every `ξ`.
* `isInMDAGEV_gevCDF`, `isInMDAGEV_gevLocScaleCDF`: a GEV law is in its own domain.
* `isInMDAFrechet_ofMeasure_cauchyMeasure`: the Cauchy law is in `MDA(Φ_1)`.
* `isInMDAFrechet_ofMeasure_studentTMeasure`: Student's t law with `ν` degrees of freedom is in
  `MDA(Φ_ν)`; `studentTMeasure_one` identifies `ν = 1` with Mathlib's Cauchy law.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events for Insurance and
  Finance*, Springer (1997), Tables 3.4.2–3.4.4 [EKM].
* N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge University Press
  (1987), Proposition 1.5.10 [BGT].
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExtremeValueTheory

/-! ### Tails of laws with a regularly varying density -/

/-- **The tail integral of a regularly varying function** ([BGT, Proposition 1.5.10]): if `f` is
measurable and regularly varying with index `-(α + 1)`, `α > 0`, then `x ↦ ∫ₓ^∞ f` is regularly
varying with index `-α`. -/
theorem IsRegularlyVarying.integral_Ioi {f : ℝ → ℝ} {α : ℝ} (hm : Measurable f)
    (hRV : IsRegularlyVarying f (-(α + 1))) (hα : 0 < α) :
    IsRegularlyVarying (fun x => ∫ t in Ioi x, f t) (-α) := by
  have hK : Tendsto (fun x => (∫ t in Ioi x, f t) / (x * f x)) atTop (𝓝 (1 / α)) := by
    have := IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurable hm hRV (by linarith)
    simpa using this
  have hL : (0 : ℝ) < 1 / α := one_div_pos.2 hα
  have hx0 : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  refine ⟨?_, fun c hc => ?_⟩
  · filter_upwards [(tendsto_order.1 hK).1 0 hL, hRV.1, hx0] with x h1 h2 h3
    exact (div_pos_iff_of_pos_right (mul_pos h3 h2)).1 h1
  · have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
    have h := (((hK.comp hcx).div hK hL.ne').mul (hRV.2 c hc)).const_mul c
    have hlim : c * (1 / α / (1 / α) * c ^ (-(α + 1))) = c ^ (-α) := by
      rw [div_self hL.ne', one_mul, Real.rpow_neg hc.le, Real.rpow_neg hc.le,
        Real.rpow_add hc, Real.rpow_one]
      have := (Real.rpow_pos_of_pos hc α).ne'
      field_simp
    rw [hlim] at h
    refine h.congr' ?_
    filter_upwards [(tendsto_order.1 hK).1 0 hL, hRV.1, hx0, hcx.eventually hRV.1,
      hcx.eventually hx0] with x h1 h2 h3 h4 h5
    have hT : 0 < ∫ t in Ioi x, f t := (div_pos_iff_of_pos_right (mul_pos h3 h2)).1 h1
    simp only [Function.comp_apply, Pi.div_apply]
    field_simp

/-- The tail of a law with density `f`, as an integral of `f`. -/
theorem measureReal_withDensity_Ioi {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hi : Integrable f)
    (x : ℝ) :
    (volume.withDensity fun y => ENNReal.ofReal (f y)).real (Ioi x) = ∫ t in Ioi x, f t := by
  rw [measureReal_def, withDensity_apply _ measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal hi.restrict (Eventually.of_forall fun y => hf0 y),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun y _ => hf0 y)]

/-- **A law with a regularly varying density has a regularly varying tail**: if the density `f`
is regularly varying with index `-(α + 1)`, `α > 0`, the tail is regularly varying with index
`-α` (`IsRegularlyVarying.integral_Ioi`). -/
theorem isRegularlyVarying_measureReal_Ioi_withDensity {f : ℝ → ℝ} {α : ℝ} (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hi : Integrable f) (hRV : IsRegularlyVarying f (-(α + 1)))
    (hα : 0 < α) :
    IsRegularlyVarying
      (fun x => (volume.withDensity fun y => ENNReal.ofReal (f y)).real (Ioi x)) (-α) := by
  simpa only [measureReal_withDensity_Ioi hf0 hi] using IsRegularlyVarying.integral_Ioi hm hRV hα

/-! ### Student's t law -/

/-- The unnormalized density of Student's t law with `ν` degrees of freedom:
`(1 + x² / ν) ^ (-(ν + 1) / 2)`. -/
noncomputable def studentTKernel (ν x : ℝ) : ℝ := (1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)

/-- The density of **Student's t law**: `studentTKernel` divided by its integral. The classical
formula `Γ((ν + 1) / 2) / (√(ν π) Γ(ν / 2))` for the constant is not proved in this library. -/
noncomputable def studentTPDFReal (ν x : ℝ) : ℝ :=
  (∫ y, studentTKernel ν y)⁻¹ * studentTKernel ν x

/-- **Student's t law** with `ν` degrees of freedom, as the law with density `studentTPDFReal ν`.
Its representation as `Z / √(χ²_ν / ν)` is not proved in this library. -/
noncomputable def studentTMeasure (ν : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (studentTPDFReal ν x)

variable {ν : ℝ}

/-- The kernel of Student's t law is positive. -/
lemma studentTKernel_pos (hν : 0 < ν) (x : ℝ) : 0 < studentTKernel ν x :=
  rpow_pos_of_pos (by positivity) _

/-- The kernel of Student's t law is measurable. -/
lemma measurable_studentTKernel (ν : ℝ) : Measurable (studentTKernel ν) := by
  unfold studentTKernel
  fun_prop

/-- The kernel of Student's t law is integrable. -/
theorem integrable_studentTKernel (hν : 0 < ν) : Integrable (studentTKernel ν) := by
  have h : Integrable fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(ν + 1) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := ν + 1) (by simpa using hν)
  have hs : √ν ≠ 0 := (sqrt_pos.2 hν).ne'
  refine (h.comp_div hs).congr (Eventually.of_forall fun x => ?_)
  simp only [studentTKernel, Real.norm_eq_abs, sq_abs, div_pow, sq_sqrt hν.le]

/-- The integral of the kernel, which is the inverse of the normalizing constant, is positive. -/
theorem integral_studentTKernel_pos (hν : 0 < ν) : 0 < ∫ y, studentTKernel ν y := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (studentTKernel_pos hν x).le)
    (integrable_studentTKernel hν)]
  have : Function.support (studentTKernel ν) = univ :=
    Function.support_eq_univ fun x => (studentTKernel_pos hν x).ne'
  simp [this]

/-- The density of Student's t law is nonnegative. -/
lemma studentTPDFReal_nonneg (hν : 0 < ν) (x : ℝ) : 0 ≤ studentTPDFReal ν x :=
  mul_nonneg (inv_nonneg.2 (integral_studentTKernel_pos hν).le) (studentTKernel_pos hν x).le

/-- The density of Student's t law is measurable. -/
lemma measurable_studentTPDFReal (ν : ℝ) : Measurable (studentTPDFReal ν) :=
  (measurable_studentTKernel ν).const_mul _

/-- The density of Student's t law is integrable. -/
theorem integrable_studentTPDFReal (hν : 0 < ν) : Integrable (studentTPDFReal ν) :=
  (integrable_studentTKernel hν).const_mul _

/-- The density of Student's t law integrates to `1`. -/
theorem integral_studentTPDFReal (hν : 0 < ν) : ∫ x, studentTPDFReal ν x = 1 := by
  simp only [studentTPDFReal]
  rw [integral_const_mul, inv_mul_cancel₀ (integral_studentTKernel_pos hν).ne']

/-- Student's t law is a probability measure. -/
theorem isProbabilityMeasure_studentTMeasure (hν : 0 < ν) :
    IsProbabilityMeasure (studentTMeasure ν) := by
  refine ⟨?_⟩
  rw [studentTMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_studentTPDFReal hν)
      (Eventually.of_forall (studentTPDFReal_nonneg hν)), integral_studentTPDFReal hν,
    ENNReal.ofReal_one]

/-- The kernel of Student's t law is regularly varying with index `-(ν + 1)`. -/
theorem isRegularlyVarying_studentTKernel (hν : 0 < ν) :
    IsRegularlyVarying (studentTKernel ν) (-(ν + 1)) := by
  have hb : IsRegularlyVarying (fun x : ℝ => 1 + x ^ 2 / ν) 2 := by
    refine (IsRegularlyVarying.rpow_id 2).of_tendsto_div (L := 1 / ν) ?_ (one_div_pos.2 hν)
    have h : Tendsto (fun x : ℝ => (x ^ 2)⁻¹ + 1 / ν) atTop (𝓝 (0 + 1 / ν)) :=
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).add_const _
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_two]
    field_simp
  have := hb.rpow (-(ν + 1) / 2)
  rwa [show (2 : ℝ) * (-(ν + 1) / 2) = -(ν + 1) by ring] at this

/-- The tail of Student's t law is regularly varying with index `-ν`. -/
theorem isRegularlyVarying_measureReal_Ioi_studentTMeasure (hν : 0 < ν) :
    IsRegularlyVarying (fun x => (studentTMeasure ν).real (Ioi x)) (-ν) :=
  isRegularlyVarying_measureReal_Ioi_withDensity (measurable_studentTPDFReal ν)
    (studentTPDFReal_nonneg hν) (integrable_studentTPDFReal hν)
    ((isRegularlyVarying_studentTKernel hν).const_mul
      (inv_pos.2 (integral_studentTKernel_pos hν))) hν

/-- Student's t law with `ν = 1` is the standard Cauchy law. -/
theorem studentTMeasure_one : studentTMeasure 1 = cauchyMeasure 0 1 := by
  rw [cauchyMeasure_of_scale_ne_zero 0 one_ne_zero, studentTMeasure]
  congr 1
  funext x
  have hk : ∀ y : ℝ, studentTKernel 1 y = (1 + y ^ 2)⁻¹ := fun y => by
    simp only [studentTKernel]
    rw [show (-(1 + 1) / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one, div_one]
  simp only [cauchyPDF, studentTPDFReal, hk, integral_univ_inv_one_add_sq, cauchyPDFReal_def']
  simp

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

/-! ### Explicit norming constants -/

/-- **Norming constants of the Pareto law** ([EKM, Table 3.4.2]): `F^n(n^{1/α} x) → Φ_α(x)`. -/
theorem tendsto_paretoCDF_pow {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Tendsto (fun n : ℕ => paretoCDF hα ((n : ℝ) ^ (1 / α) * x) ^ n) atTop
      (𝓝 (standardFrechetCDF hα x)) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [standardFrechetCDF_apply_nonpos_eq hα hx]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 : (n : ℝ) ^ (1 / α) * x ≤ 1 :=
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx).trans zero_le_one
    rw [paretoCDF_apply_of_le_one hα h0, zero_pow (by omega)]
  · rw [standardFrechetCDF_apply_pos_eq hα hx]
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / α) * x) atTop atTop :=
      ((tendsto_rpow_atTop (one_div_pos.2 hα)).comp tendsto_natCast_atTop_atTop).atTop_mul_const hx
    refine (Real.tendsto_one_add_div_pow_exp (-(x ^ (-α)))).congr' ?_
    filter_upwards [ht.eventually_ge_atTop 1, eventually_ge_atTop 1] with n h1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [paretoCDF_apply_of_one_le hα h1, mul_rpow (by positivity) hx.le, ← rpow_mul hn0.le,
      show 1 / α * -α = -1 by field_simp, rpow_neg_one]
    congr 1
    field_simp
    ring

/-- **Norming constants of the law `1 - (1 - x)^α` on `[0, 1]`** ([EKM, Table 3.4.3]; uniform for
`α = 1`): `F^n(1 + n^{-1/α} x) → Ψ_α(x)`. -/
theorem tendsto_powerCDF_pow {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Tendsto (fun n : ℕ => powerCDF hα (1 + (n : ℝ) ^ (-1 / α) * x) ^ n) atTop
      (𝓝 (standardWeibullCDF hα x)) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [standardWeibullCDF_apply_nonneg_eq hα hx]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with n
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / α) * x := mul_nonneg (by positivity) hx
    rw [powerCDF_apply_of_one_le hα (by linarith), one_pow]
  · rw [standardWeibullCDF_apply_neg_eq hα hx]
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / α) * x) atTop (𝓝 (0 * x)) := by
      refine Tendsto.mul_const _ ?_
      have : -1 / α = -(1 / α) := by ring
      rw [this]
      exact (tendsto_rpow_neg_atTop (one_div_pos.2 hα)).comp tendsto_natCast_atTop_atTop
    rw [zero_mul] at ht
    refine (Real.tendsto_one_add_div_pow_exp (-((-x) ^ α))).congr' ?_
    filter_upwards [ht.eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)),
      eventually_ge_atTop 1] with n h1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hc : 0 < (n : ℝ) ^ (-1 / α) := rpow_pos_of_pos hn0 _
    have hneg : (n : ℝ) ^ (-1 / α) * x < 0 := mul_neg_of_pos_of_neg hc hx
    rw [powerCDF_apply_of_mem_Icc hα ⟨by linarith, by linarith⟩,
      show 1 - (1 + (n : ℝ) ^ (-1 / α) * x) = (n : ℝ) ^ (-1 / α) * -x by ring,
      mul_rpow hc.le (by linarith), ← rpow_mul hn0.le, show -1 / α * α = -1 by field_simp,
      rpow_neg_one]
    congr 1
    field_simp
    ring

/-- **Norming constants of the standard exponential law** ([EKM, Table 3.4.4]):
`F^n(x + log n) → Λ(x)`. -/
theorem tendsto_standardExponentialCDF_pow (x : ℝ) :
    Tendsto (fun n : ℕ => standardExponentialCDF (x + Real.log n) ^ n) atTop
      (𝓝 (standardGumbelCDF x)) := by
  rw [standardGumbelCDF_apply_eq]
  have ht : Tendsto (fun n : ℕ => x + Real.log n) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine (Real.tendsto_one_add_div_pow_exp (-Real.exp (-x))).congr' ?_
  filter_upwards [ht.eventually_ge_atTop 0, eventually_ge_atTop 1] with n h1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [standardExponentialCDF_apply_of_nonneg h1, neg_add, Real.exp_add, Real.exp_neg (Real.log n),
    Real.exp_log hn0]
  congr 1
  field_simp
  ring

/-! ### The domain of attraction is invariant under affine maps -/

variable {F : CumulativeDistributionFunction}

/-- The Fréchet domain is closed under affine transformations of the law. -/
theorem IsInMDAFrechet.smul {α : ℝ} {hα : 0 < α} (h : F.IsInMDAFrechet hα) (A : AffineIncrEquiv) :
    (A • F).IsInMDAFrechet hα := by
  obtain ⟨As, hAs⟩ := h
  exact ⟨fun n => As n * A⁻¹, fun x => by simpa [mul_smul] using hAs x⟩

/-- The Weibull domain is closed under affine transformations of the law. -/
theorem IsInMDAWeibull.smul {α : ℝ} {hα : 0 < α} (h : F.IsInMDAWeibull hα) (A : AffineIncrEquiv) :
    (A • F).IsInMDAWeibull hα := by
  obtain ⟨As, hAs⟩ := h
  exact ⟨fun n => As n * A⁻¹, fun x => by simpa [mul_smul] using hAs x⟩

/-- The Gumbel domain is closed under affine transformations of the law. -/
theorem IsInMDAGumbel.smul (h : F.IsInMDAGumbel) (A : AffineIncrEquiv) :
    (A • F).IsInMDAGumbel := by
  obtain ⟨As, hAs⟩ := h
  exact ⟨fun n => As n * A⁻¹, fun x => by simpa [mul_smul] using hAs x⟩

/-- `MDA(H_ξ)` is closed under affine transformations of the law. -/
theorem IsInMDAGEV.smul {ξ : ℝ} (h : F.IsInMDAGEV ξ) (A : AffineIncrEquiv) :
    (A • F).IsInMDAGEV ξ := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · exact (isInMDAGEV_iff_of_neg hξ).2 (((isInMDAGEV_iff_of_neg hξ).1 h).smul A)
  · exact isInMDAGEV_zero_iff.2 ((isInMDAGEV_zero_iff.1 h).smul A)
  · exact (isInMDAGEV_iff_of_pos hξ).2 (((isInMDAGEV_iff_of_pos hξ).1 h).smul A)

/-! ### Extreme value laws are in their own domains -/

/-- The Fréchet law is in its own domain: `Φ_α(n^{1/α} x)^n = Φ_α(x)` for `n ≥ 1`. -/
theorem isInMDAFrechet_standardFrechetCDF {α : ℝ} (hα : 0 < α) :
    (standardFrechetCDF hα).IsInMDAFrechet hα := by
  have ha : ∀ n : ℕ, 0 < max (n : ℝ) 1 ^ (1 / α) := fun n =>
    rpow_pos_of_pos (lt_max_of_lt_right one_pos) _
  refine ⟨fun n => (AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹, fun x => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : max (n : ℝ) 1 = n := max_eq_left (by exact_mod_cast hn)
  have happ : ((AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹ • standardFrechetCDF hα) x =
      standardFrechetCDF hα (max (n : ℝ) 1 ^ (1 / α) * x + 0) := by simp
  rw [happ, h1, standardFrechetCDF_pow_apply_rpow_mul hα hn]

/-- The Weibull law is in its own domain: `Ψ_α(n^{-1/α} x)^n = Ψ_α(x)` for `n ≥ 1`. -/
theorem isInMDAWeibull_standardWeibullCDF {α : ℝ} (hα : 0 < α) :
    (standardWeibullCDF hα).IsInMDAWeibull hα := by
  have ha : ∀ n : ℕ, 0 < max (n : ℝ) 1 ^ (-1 / α) := fun n =>
    rpow_pos_of_pos (lt_max_of_lt_right one_pos) _
  refine ⟨fun n => (AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹, fun x => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : max (n : ℝ) 1 = n := max_eq_left (by exact_mod_cast hn)
  have happ : ((AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹ • standardWeibullCDF hα) x =
      standardWeibullCDF hα (max (n : ℝ) 1 ^ (-1 / α) * x + 0) := by simp
  rw [happ, h1, standardWeibullCDF_pow_apply_rpow_mul hα hn]

/-- **The GEV law `H_ξ` is in its own domain `MDA(H_ξ)`.** -/
theorem isInMDAGEV_gevCDF (ξ : ℝ) : (gevCDF ξ).IsInMDAGEV ξ := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · rw [isInMDAGEV_iff_of_neg hξ, gevCDF_of_neg hξ]
    exact (isInMDAWeibull_standardWeibullCDF _).smul _
  · rw [isInMDAGEV_zero_iff, gevCDF_zero]
    exact isInMDAGumbel_standardGumbelCDF
  · rw [isInMDAGEV_iff_of_pos hξ, gevCDF_of_pos hξ]
    exact (isInMDAFrechet_standardFrechetCDF _).smul _

/-- **The location-scale GEV law `H_{ξ,μ,σ}` is in `MDA(H_ξ)`.** -/
theorem isInMDAGEV_gevLocScaleCDF (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (gevLocScaleCDF ξ μ hσ).IsInMDAGEV ξ :=
  (isInMDAGEV_gevCDF ξ).smul _

/-! ### The generalized Pareto law -/

section GPD

variable {ξ σ : ℝ}

/-- The tail of `GPD(ξ, σ)` on `[0, ∞)`, as a real number. -/
theorem measureReal_gpdMeasure_Ioi (hσ : 0 < σ) {x : ℝ} (hx : 0 ≤ x) :
    (gpdMeasure ξ σ).real (Ioi x) = gpdSurvivalAll ξ σ x := by
  rw [measureReal_def, gpdMeasure_Ioi hσ hx, ENNReal.toReal_ofReal (gpdSurvivalAll_nonneg _ _ _)]

/-- The tail of `GPD(ξ, σ)` is positive below `0`, where it equals `1`. -/
private lemma measureReal_gpdMeasure_Ioi_pos_of_neg (hσ : 0 < σ) {x : ℝ} (hx : x < 0) :
    0 < (gpdMeasure ξ σ).real (Ioi x) := by
  have h1 : (gpdMeasure ξ σ).real (Ioi 0) ≤ (gpdMeasure ξ σ).real (Ioi x) :=
    measureReal_mono (Ioi_subset_Ioi hx.le)
  have h2 : (gpdMeasure ξ σ).real (Ioi 0) = 1 := by
    rw [measureReal_gpdMeasure_Ioi hσ le_rfl, gpdSurvivalAll_zero_right]
  linarith

/-- For `ξ > 0`, the tail of `GPD(ξ, σ)` is regularly varying with index `-1/ξ`. -/
theorem isRegularlyVarying_measureReal_Ioi_gpdMeasure (hξ : 0 < ξ) (hσ : 0 < σ) :
    IsRegularlyVarying (fun x => (gpdMeasure ξ σ).real (Ioi x)) (-(1 / ξ)) := by
  have hb : IsRegularlyVarying (fun x : ℝ => 1 + ξ * x / σ) 1 := by
    refine (IsRegularlyVarying.rpow_id 1).of_tendsto_div (L := ξ / σ) ?_ (div_pos hξ hσ)
    have h : Tendsto (fun x : ℝ => x⁻¹ + ξ / σ) atTop (𝓝 (0 + ξ / σ)) :=
      tendsto_inv_atTop_zero.add_const _
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_one]
    field_simp
  have := hb.rpow (-(1 / ξ))
  rw [one_mul] at this
  refine this.congr ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  have hp : 0 ≤ 1 + ξ * x / σ := by positivity
  rw [measureReal_gpdMeasure_Ioi hσ hx, gpdSurvivalAll, ite_eq_right hξ.ne', max_eq_left hp]

/-- **`GPD(ξ, σ)` is in `MDA(H_ξ)`** for every `ξ`. -/
theorem isInMDAGEV_ofMeasure_gpdMeasure (ξ : ℝ) (hσ : 0 < σ) :
    (ofMeasure (gpdMeasure ξ σ)).IsInMDAGEV ξ := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · rw [isInMDAGEV_iff_of_neg hξ, isInMDAWeibull_ofMeasure_iff]
    have hxF : 0 < -σ / ξ := div_pos_of_neg_of_neg (by linarith) hξ
    have hξ0 : ξ ≠ 0 := hξ.ne
    have hval : ∀ x : ℝ, 1 + ξ * x / σ = ξ * (x - -σ / ξ) / σ := fun x => by
      field_simp
      ring
    refine ⟨-σ / ξ, ?_, fun x hx => ?_, ?_⟩
    · rw [measureReal_gpdMeasure_Ioi hσ hxF.le, gpdSurvivalAll, ite_eq_right hξ.ne, hval, sub_self,
        mul_zero, zero_div, max_self, Real.zero_rpow]
      have h1 : 0 < 1 / -ξ := one_div_pos.2 (by linarith)
      have h2 : -(1 / ξ) = 1 / -ξ := by field_simp
      rw [h2]
      exact h1.ne'
    · rcases lt_or_ge x 0 with hx0 | hx0
      · exact measureReal_gpdMeasure_Ioi_pos_of_neg hσ hx0
      · rw [measureReal_gpdMeasure_Ioi hσ hx0, gpdSurvivalAll, ite_eq_right hξ.ne]
        have hp : 0 < 1 + ξ * x / σ := by
          rw [hval]
          exact div_pos (mul_pos_of_neg_of_neg hξ (by linarith)) hσ
        rw [max_eq_left hp.le]
        exact rpow_pos_of_pos hp _
    · have hc : 0 < -ξ / σ := div_pos (by linarith) hσ
      have hR : IsRegularlyVarying
          (fun t : ℝ => (-ξ / σ) ^ (-(1 / ξ)) * t ^ (-(-1 / ξ))) (-(-1 / ξ)) :=
        (IsRegularlyVarying.rpow_id _).const_mul (rpow_pos_of_pos hc _)
      refine hR.congr ?_
      filter_upwards [eventually_gt_atTop ((-σ / ξ)⁻¹)] with t ht
      have ht0 : 0 < t := (inv_pos.2 hxF).trans ht
      have hle : t⁻¹ ≤ -σ / ξ := by
        rw [inv_le_comm₀ ht0 hxF]
        exact ht.le
      rw [measureReal_gpdMeasure_Ioi hσ (by linarith), gpdSurvivalAll, ite_eq_right hξ.ne, hval]
      have hv : ξ * (-σ / ξ - t⁻¹ - -σ / ξ) / σ = -ξ / σ * t⁻¹ := by
        field_simp
        ring
      rw [hv, max_eq_left (by positivity), mul_rpow hc.le (by positivity), inv_rpow ht0.le,
        ← rpow_neg ht0.le]
      congr 2
      ring
  · rw [isInMDAGEV_zero_iff, isInMDAGumbel_ofMeasure_iff_atTop]
    · refine ⟨fun _ => σ, Eventually.of_forall fun _ => hσ, fun x => ?_⟩
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (-(x * σ))] with t h1 h2
      rw [measureReal_gpdMeasure_Ioi hσ (by linarith), measureReal_gpdMeasure_Ioi hσ h1,
        gpdSurvivalAll, gpdSurvivalAll, ite_eq_left rfl, ite_eq_left rfl, ← Real.exp_sub]
      congr 1
      field_simp
      ring
    · intro x
      rcases lt_or_ge x 0 with hx0 | hx0
      · exact measureReal_gpdMeasure_Ioi_pos_of_neg hσ hx0
      · rw [measureReal_gpdMeasure_Ioi hσ hx0, gpdSurvivalAll, ite_eq_left rfl]
        exact Real.exp_pos _
  · rw [isInMDAGEV_iff_of_pos hξ, isInMDAFrechet_ofMeasure_iff]
    exact isRegularlyVarying_measureReal_Ioi_gpdMeasure hξ hσ

end GPD

/-! ### The Cauchy and Student t laws -/

/-- The tail of the Cauchy law is regularly varying with index `-1`: its density is regularly
varying with index `-2`. -/
theorem isRegularlyVarying_measureReal_Ioi_cauchyMeasure (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    IsRegularlyVarying (fun x => (cauchyMeasure x₀ γ).real (Ioi x)) (-1) := by
  have hγ0 : (0 : ℝ) < γ := by exact_mod_cast pos_iff_ne_zero.2 hγ
  have hb : IsRegularlyVarying (fun x : ℝ => (x - x₀) ^ 2 + (γ : ℝ) ^ 2) 2 := by
    refine (IsRegularlyVarying.rpow_id 2).of_tendsto_div (L := 1) ?_ one_pos
    have h : Tendsto (fun x : ℝ => (1 - x₀ * x⁻¹) ^ 2 + (γ * x⁻¹) ^ 2) atTop
        (𝓝 ((1 - x₀ * 0) ^ 2 + (γ * 0) ^ 2)) :=
      ((tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul _)).pow 2).add
        ((tendsto_inv_atTop_zero.const_mul _).pow 2)
    simp only [mul_zero, sub_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_two]
    field_simp
  have hd : IsRegularlyVarying (cauchyPDFReal x₀ γ) (-(1 + 1)) := by
    have := hb.inv.const_mul (a := π⁻¹ * γ) (by positivity)
    rw [show -(1 + 1 : ℝ) = -2 by norm_num]
    exact this
  have := isRegularlyVarying_measureReal_Ioi_withDensity (measurable_cauchyPDFReal x₀ γ)
    (fun x => (cauchyPDF_pos x₀ hγ x).le) (integrable_cauchyPDFReal x₀) hd one_pos
  rwa [show (volume.withDensity fun y => ENNReal.ofReal (cauchyPDFReal x₀ γ y)) =
    cauchyMeasure x₀ γ from (cauchyMeasure_of_scale_ne_zero x₀ hγ).symm] at this

/-- **The Cauchy law is in the Fréchet domain `MDA(Φ_1)`** ([EKM, Table 3.4.2]). -/
theorem isInMDAFrechet_ofMeasure_cauchyMeasure (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    (ofMeasure (cauchyMeasure x₀ γ)).IsInMDAFrechet one_pos :=
  (isInMDAFrechet_ofMeasure_iff one_pos).2 (isRegularlyVarying_measureReal_Ioi_cauchyMeasure x₀ hγ)

/-- **Student's t law with `ν` degrees of freedom is in the Fréchet domain `MDA(Φ_ν)`**. -/
theorem isInMDAFrechet_ofMeasure_studentTMeasure {ν : ℝ} (hν : 0 < ν) :
    (ofMeasure (studentTMeasure ν)).IsInMDAFrechet hν :=
  have := isProbabilityMeasure_studentTMeasure hν
  (isInMDAFrechet_ofMeasure_iff hν).2 (isRegularlyVarying_measureReal_Ioi_studentTMeasure hν)

end CumulativeDistributionFunction
