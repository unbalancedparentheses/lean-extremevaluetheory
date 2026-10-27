/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.StretchedExponential
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Distributions.Pareto

/-!
# Concrete subexponential laws: Weibull-type and Pareto

The criteria `IsSubexponential.of_tail_eq_exp_neg_rpow` and `IsSubexponential.of_isRegularlyVarying`
take a measure with a prescribed tail as hypothesis. Here we construct such measures, so that the
statements are not vacuous ([EKM, Table 1.4.3/1.4.4]).

## Main definitions

* `tail_stieltjesFunction_measure`: the tail of the Lebesgue–Stieltjes measure `F.measure` of a
  Stieltjes function with `F(∞) = 1` is `1 - F` (formerly stated for `lawOfCDF F`, now
  deprecated in favour of Mathlib's `F.measure`).
* `ExtremeValueTheory.weibullTailLaw τ hτ`: the Weibull law with `F̄(x) = exp(-x^τ)` on
  `[0, ∞)`, `τ > 0` (built from the c.d.f. `1 - exp(-(max x 0)^τ)`).

## Main results

* `tail_weibullTailLaw`: `F̄(x) = exp(-x^τ)` for `x ≥ 0`.
* `isSubexponential_weibullTailLaw`: for `0 < τ < 1` the Weibull law is subexponential
  ([EKM, Example 1.4.3 / Table 1.4.4]).
* `tail_paretoMeasure`: the Pareto law `paretoMeasure t r` (Mathlib) has tail `(t / x)^r` for
  `x ≥ t`.
* `isSubexponential_paretoMeasure`: Pareto laws are subexponential ([EKM, Corollary 1.3.2]).

Here [EKM] is Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events for Insurance and
Finance* (Springer, 1997).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

open Subexp

/-! ### Laws from c.d.f.s

The law of a Stieltjes function `F` with `F(-∞) = 0`, `F(∞) = 1` is Mathlib's Lebesgue–Stieltjes
measure `F.measure` (a probability measure by `StieltjesFunction.isProbabilityMeasure`); see
`ExtremeValueTheory/CDFBridge.lean` for the bridge between laws and c.d.f.s. -/

section LawOfCDF

variable {F : StieltjesFunction ℝ}

/-- The tail of the Lebesgue–Stieltjes measure of `F` is `1 - F`. -/
theorem tail_stieltjesFunction_measure (htop : Tendsto F atTop (𝓝 1)) (x : ℝ) :
    tail F.measure x = 1 - F x := by
  have h01 : F x ≤ 1 := F.mono.ge_of_tendsto htop x
  rw [tail, measureReal_def, F.measure_Ioi htop, ENNReal.toReal_ofReal (by linarith)]

/-- The Lebesgue–Stieltjes measure of `F` is concentrated on `[0, ∞)` when `F` vanishes on
`(-∞, 0]`. -/
theorem stieltjesFunction_measure_Iio_zero (hbot : Tendsto F atBot (𝓝 0))
    (h0 : ∀ x, x ≤ 0 → F x = 0) : F.measure (Iio 0) = 0 := by
  refine measure_mono_null Iio_subset_Iic_self ?_
  rw [F.measure_Iic hbot, h0 0 le_rfl, sub_zero, ENNReal.ofReal_zero]

/-- The probability measure with c.d.f. `F`. Deprecated: this is `F.measure`
(`StieltjesFunction.measure`). -/
@[deprecated StieltjesFunction.measure +typeChanged (since := "2026-10-23")]
noncomputable def lawOfCDF (F : StieltjesFunction ℝ) : Measure ℝ := F.measure

set_option linter.deprecated false in
@[deprecated StieltjesFunction.isProbabilityMeasure +typeChanged (since := "2026-10-23")]
theorem isProbabilityMeasure_lawOfCDF (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) : IsProbabilityMeasure (lawOfCDF F) :=
  F.isProbabilityMeasure hbot htop

set_option linter.deprecated false in
@[deprecated tail_stieltjesFunction_measure (since := "2026-10-23")]
theorem tail_lawOfCDF (htop : Tendsto F atTop (𝓝 1)) (x : ℝ) :
    tail (lawOfCDF F) x = 1 - F x :=
  tail_stieltjesFunction_measure htop x

set_option linter.deprecated false in
@[deprecated stieltjesFunction_measure_Iio_zero (since := "2026-10-23")]
theorem lawOfCDF_Iio_zero (hbot : Tendsto F atBot (𝓝 0)) (h0 : ∀ x, x ≤ 0 → F x = 0) :
    lawOfCDF F (Iio 0) = 0 :=
  stieltjesFunction_measure_Iio_zero hbot h0

end LawOfCDF

/-! ### Weibull-type laws -/

section Weibull

variable {τ : ℝ}

/-- The Weibull c.d.f. `x ↦ 1 - exp(-(max x 0)^τ)`, `τ > 0`. -/
noncomputable def weibullCDF (τ : ℝ) (hτ : 0 < τ) : StieltjesFunction ℝ where
  toFun x := 1 - exp (-(max x 0) ^ τ)
  mono' := by
    intro x y hxy
    have : (max x 0) ^ τ ≤ (max y 0) ^ τ :=
      rpow_le_rpow (le_max_right _ _) (max_le_max_right 0 hxy) hτ.le
    simp only [sub_le_sub_iff_left, exp_le_exp, neg_le_neg_iff]
    exact this
  right_continuous' x := by
    refine Continuous.continuousWithinAt ?_
    exact continuous_const.sub (continuous_exp.comp
      ((continuous_rpow_const hτ.le).comp (continuous_id.max continuous_const)).neg)

theorem weibullCDF_apply (hτ : 0 < τ) (x : ℝ) :
    weibullCDF τ hτ x = 1 - exp (-(max x 0) ^ τ) := rfl

theorem tendsto_weibullCDF_atBot (hτ : 0 < τ) : Tendsto (weibullCDF τ hτ) atBot (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_le_atBot 0] with x hx
  rw [weibullCDF_apply, max_eq_right hx, zero_rpow hτ.ne', neg_zero, exp_zero, sub_self]

theorem tendsto_weibullCDF_atTop (hτ : 0 < τ) : Tendsto (weibullCDF τ hτ) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => 1 - exp (-x ^ τ)) atTop (𝓝 (1 - 0)) :=
    (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop hτ)).const_sub 1
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [weibullCDF_apply, max_eq_left hx]

/-- The **Weibull law** with tail `F̄(x) = exp(-x^τ)` on `[0, ∞)`, `τ > 0`. -/
noncomputable def weibullTailLaw (τ : ℝ) (hτ : 0 < τ) : Measure ℝ := (weibullCDF τ hτ).measure

instance isProbabilityMeasure_weibullTailLaw (hτ : 0 < τ) :
    IsProbabilityMeasure (weibullTailLaw τ hτ) :=
  (weibullCDF τ hτ).isProbabilityMeasure (tendsto_weibullCDF_atBot hτ) (tendsto_weibullCDF_atTop hτ)

theorem weibullTailLaw_Iio_zero (hτ : 0 < τ) : weibullTailLaw τ hτ (Iio 0) = 0 :=
  stieltjesFunction_measure_Iio_zero (tendsto_weibullCDF_atBot hτ) fun x hx => by
    rw [weibullCDF_apply, max_eq_right hx, zero_rpow hτ.ne', neg_zero, exp_zero, sub_self]

/-- The Weibull law has tail `F̄(x) = exp(-x^τ)` for `x ≥ 0`. -/
theorem tail_weibullTailLaw (hτ : 0 < τ) {x : ℝ} (hx : 0 ≤ x) :
    tail (weibullTailLaw τ hτ) x = exp (-x ^ τ) := by
  rw [weibullTailLaw, tail_stieltjesFunction_measure (tendsto_weibullCDF_atTop hτ),
    weibullCDF_apply, max_eq_left hx, sub_sub_cancel]

/-- **Weibull laws with shape `0 < τ < 1` are subexponential** ([EKM, Example 1.4.3 and
Table 1.4.4]): the law with tail `F̄(x) = exp(-x^τ)` on `[0, ∞)`. -/
theorem isSubexponential_weibullTailLaw (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    IsSubexponential (weibullTailLaw τ hτ0) :=
  IsSubexponential.of_tail_eq_exp_neg_rpow (weibullTailLaw_Iio_zero hτ0) hτ0 hτ1
    fun _ hx => tail_weibullTailLaw hτ0 hx

end Weibull

/-! ### Pareto laws -/

section Pareto

variable {t r : ℝ}

/-- The Pareto law `paretoMeasure t r` has tail `F̄(x) = t^r x^{-r}` for `x ≥ t`. -/
theorem paretoMeasure_Ioi (ht : 0 < t) (hr : 0 < r) {x : ℝ} (hx : t ≤ x) :
    paretoMeasure t r (Ioi x) = ENNReal.ofReal (t ^ r * x ^ (-r)) := by
  have hx0 : 0 < x := ht.trans_le hx
  rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun measurableSet_Ioi
      (g := fun y => ENNReal.ofReal (r * t ^ r * y ^ (-(r + 1)))) (fun y hy =>
        paretoPDF_of_le (hx.trans (le_of_lt hy)))]
  have hint : IntegrableOn (fun y : ℝ => r * t ^ r * y ^ (-(r + 1))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
      show -(r + 1) + 1 = -r by ring]
    field_simp
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun y hy =>
      mul_nonneg (mul_nonneg hr.le (rpow_nonneg ht.le _)) (rpow_pos_of_pos (hx0.trans hy) _).le

theorem tail_paretoMeasure (ht : 0 < t) (hr : 0 < r) {x : ℝ} (hx : t ≤ x) :
    tail (paretoMeasure t r) x = t ^ r * x ^ (-r) := by
  rw [tail, measureReal_def, paretoMeasure_Ioi ht hr hx, ENNReal.toReal_ofReal]
  exact mul_nonneg (rpow_nonneg ht.le _) (rpow_nonneg (ht.le.trans hx) _)

theorem paretoMeasure_Iio_zero (ht : 0 < t) : paretoMeasure t r (Iio 0) = 0 := by
  rw [paretoMeasure, withDensity_apply _ measurableSet_Iio]
  refine (setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0) fun y hy =>
    paretoPDF_of_lt (show y < t from (show y < 0 from hy).trans ht)).trans lintegral_zero

/-- The tail of the Pareto law is regularly varying with index `-r`. -/
theorem isRegularlyVarying_tail_paretoMeasure (ht : 0 < t) (hr : 0 < r) :
    IsRegularlyVarying (tail (paretoMeasure t r)) (-r) :=
  ((IsRegularlyVarying.rpow_id (-r)).const_mul (rpow_pos_of_pos ht r)).congr
    (by filter_upwards [eventually_ge_atTop t] with x hx using (tail_paretoMeasure ht hr hx).symm)

/-- **Pareto laws are subexponential** ([EKM, Corollary 1.3.2 and Table 1.4.3]). -/
theorem isSubexponential_paretoMeasure (ht : 0 < t) (hr : 0 < r) :
    IsSubexponential (paretoMeasure t r) := by
  have := isProbabilityMeasure_paretoMeasure ht hr
  exact IsSubexponential.of_isRegularlyVarying (paretoMeasure_Iio_zero ht)
    (isRegularlyVarying_tail_paretoMeasure ht hr)

end Pareto

end ExtremeValueTheory
