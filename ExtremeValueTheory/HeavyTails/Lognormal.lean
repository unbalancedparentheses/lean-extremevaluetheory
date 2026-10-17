/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.StretchedExponential
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# The lognormal distribution is subexponential

The lognormal law `LN(m, v)`, the law of `exp Z` for `Z ∼ N(m, v)`, is subexponential
([EKM, Example 1.4.7 and Table 1.4.3]). It is the standard example of a subexponential law whose
tail is neither regularly varying nor of Weibull type.

## Main definitions

* `ExtremeValueTheory.gaussianTail m v c = P(Z > c)`, `Z ∼ N(m, v)`.
* `ExtremeValueTheory.lognormal m v`: the push-forward of `gaussianReal m v` under `exp`.

## Main results

* `gaussianTail_le`, `le_gaussianTail`: the **Mills-ratio bounds**: for `c > m`,
  `p(c) / ((c - m)(1/v + 1/(c - m)²)) ≤ Φ̄(c) ≤ v p(c) / (c - m)`, where `p = gaussianPDFReal m v`.
* `tendsto_gaussianTail_div`: the **Mills ratio** `Φ̄(c) ~ v p(c) / (c - m)` as `c → ∞`.
* `tail_lognormal`: `F̄(x) = Φ̄(log x)` for `x > 0`.
* `tendsto_tail_lognormal_sub_div`: the lognormal law is long-tailed.
* `IsSubexponential.lognormal`: **the lognormal law is subexponential**.

Here [EKM] is Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events for Insurance and
Finance* (Springer, 1997).

## Proof outline

We apply the dominated-convergence criterion `IsSubexponential.of_dominated`. With
`a = log (x - t)`, `b = log x`, the Mills bounds give, for `m + 1 ≤ a ≤ b`,
`Φ̄(a) / Φ̄(b) ≤ (b - m)/(a - m) · (1 + v/(b - m)²) · exp(((b - m)² - (a - m)²) / (2v))`.
For `x ≥ 2 e^{m+1}` and `0 ≤ t ≤ x/2` this yields
`F̄(x - t) / F̄(x) ≤ (1 + 2t/x)(1 + v/(log x - m)²) exp(2t (log x - m) / (v x))`, which tends to
`1` for fixed `t` (long tail) and, since `(log x - m)/x` is decreasing on `[e^{m+1}, ∞)`, is
dominated by `2(1 + v) exp((log (max (2t) e^{m+1}) - m)/v)`, a function of polynomial growth,
hence integrable against the lognormal law. Finally
`F̄(x/2)² / F̄(x) ≲ exp(-(log x)² / (2v) + O(log x)) → 0`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

open Subexp

section Mills

variable {m : ℝ} {v : ℝ≥0}

/-- The Gaussian tail `Φ̄(c) = P(Z > c)`, `Z ∼ N(m, v)`. -/
noncomputable def gaussianTail (m : ℝ) (v : ℝ≥0) (c : ℝ) : ℝ := (gaussianReal m v).real (Ioi c)

theorem gaussianTail_eq_integral (hv : v ≠ 0) (c : ℝ) :
    gaussianTail m v c = ∫ s in Ioi c, gaussianPDFReal m v s := by
  rw [gaussianTail, measureReal_def, gaussianReal_apply_eq_integral _ hv, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => gaussianPDFReal_nonneg _ _ _

private theorem hasDerivAt_gaussianPDFReal (s : ℝ) :
    HasDerivAt (gaussianPDFReal m v) (-(s - m) / v * gaussianPDFReal m v s) s := by
  have h1 : HasDerivAt (fun s : ℝ => -(s - m) ^ 2 / (2 * (v : ℝ)))
      (-(2 * (s - m) ^ 1 * 1) / (2 * (v : ℝ))) s :=
    (((hasDerivAt_id s).sub_const m).pow 2).neg.div_const _
  have h2 := h1.exp.const_mul (√(2 * π * v))⁻¹
  rw [gaussianPDFReal_def]
  convert h2 using 1
  rcases eq_or_ne (v : ℝ) 0 with hv | hv
  · simp [hv]
  · field_simp

private theorem tendsto_gaussianPDFReal_atTop (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atTop (𝓝 0) := by
  have hv' : (0 : ℝ) < v := by positivity
  rw [gaussianPDFReal_def]
  have : Tendsto (fun s : ℝ => -(s - m) ^ 2 / (2 * (v : ℝ))) atTop atBot := by
    have h := (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_atTop_add_const_right _ (-m)
      tendsto_id)
    have h2 := (tendsto_neg_atTop_atBot.comp h).atBot_div_const (by positivity : (0 : ℝ) < 2 * v)
    refine h2.congr fun s => ?_
    simp [sub_eq_add_neg]
  simpa using (tendsto_exp_atBot.comp this).const_mul (√(2 * π * v))⁻¹

/-- **Upper Mills bound.** For `c > m`, `Φ̄(c) ≤ v p(c) / (c - m)`. -/
theorem gaussianTail_le (hv : v ≠ 0) {c : ℝ} (hc : m < c) :
    gaussianTail m v c ≤ v * gaussianPDFReal m v c / (c - m) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hderiv : ∀ s ∈ Ici c, HasDerivAt (fun s => -gaussianPDFReal m v s)
      ((s - m) / v * gaussianPDFReal m v s) s := fun s _ => by
    convert (hasDerivAt_gaussianPDFReal (m := m) (v := v) s).neg using 1; ring
  have hpos : ∀ s ∈ Ioi c, 0 ≤ (s - m) / v * gaussianPDFReal m v s := fun s hs =>
    mul_nonneg (div_nonneg (by linarith [hs.out]) hv'.le) (gaussianPDFReal_nonneg _ _ _)
  have hlim : Tendsto (fun s => -gaussianPDFReal m v s) atTop (𝓝 (-0)) :=
    (tendsto_gaussianPDFReal_atTop hv).neg
  rw [neg_zero] at hlim
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  rw [zero_sub, neg_neg] at heq
  rw [gaussianTail_eq_integral hv, le_div_iff₀ (by linarith), ← heq, mul_comm,
    ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_mono_on ((integrable_gaussianPDFReal m v).integrableOn.const_mul _)
    (hint.const_mul _) measurableSet_Ioi fun s hs => ?_
  have hs' : c < s := hs
  rw [← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hv'.ne']
  exact mul_le_mul_of_nonneg_right (by linarith) (gaussianPDFReal_nonneg _ _ _)

/-- **Lower Mills bound.** For `c > m`, `p(c) / (c - m) ≤ (1 / v + 1 / (c - m)²) Φ̄(c)`. -/
theorem le_gaussianTail (hv : v ≠ 0) {c : ℝ} (hc : m < c) :
    gaussianPDFReal m v c / (c - m) ≤ (1 / v + 1 / (c - m) ^ 2) * gaussianTail m v c := by
  have hv' : (0 : ℝ) < v := by positivity
  set p := gaussianPDFReal m v
  have hderiv : ∀ s ∈ Ici c, HasDerivAt (fun s => -p s / (s - m))
      (p s * (1 / v + 1 / (s - m) ^ 2)) s := fun s hs => by
    have hs0 : s - m ≠ 0 := by linarith [hs.out]
    have := ((hasDerivAt_gaussianPDFReal (m := m) (v := v) s).neg).div
      ((hasDerivAt_id s).sub_const m) hs0
    convert this using 1
    · funext y; simp [p, id, neg_div]
    · simp only [id, Pi.neg_apply]
      field_simp
      ring
  have hpos : ∀ s ∈ Ioi c, 0 ≤ p s * (1 / v + 1 / (s - m) ^ 2) := fun s _ =>
    mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by positivity)
  have hlim : Tendsto (fun s => -p s / (s - m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (s - m)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-m) tendsto_id)
    simpa [div_eq_mul_inv] using (tendsto_gaussianPDFReal_atTop hv).neg.mul h1
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  rw [zero_sub, neg_div, neg_neg] at heq
  rw [← heq, gaussianTail_eq_integral hv, ← integral_const_mul]
  refine setIntegral_mono_on hint ((integrable_gaussianPDFReal m v).integrableOn.const_mul _)
    measurableSet_Ioi fun s hs => ?_
  have hs' : c < s := hs
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (gaussianPDFReal_nonneg _ _ _)
  gcongr

theorem gaussianTail_antitone : Antitone (gaussianTail m v) := fun _ _ h =>
  measureReal_mono (Ioi_subset_Ioi h)

theorem gaussianTail_pos (hv : v ≠ 0) (c : ℝ) : 0 < gaussianTail m v c := by
  have hv' : (0 : ℝ) < v := by positivity
  set c' := max c (m + 1)
  have hc' : m < c' := by have := le_max_right c (m + 1); linarith
  have h1 := le_gaussianTail hv hc'
  have h2 : 0 < gaussianPDFReal m v c' / (c' - m) :=
    div_pos (gaussianPDFReal_pos _ _ _ hv) (by linarith)
  have h3 : 0 < gaussianTail m v c' := by
    by_contra hneg
    have : gaussianTail m v c' ≤ 0 := not_lt.1 hneg
    have : (1 / (v : ℝ) + 1 / (c' - m) ^ 2) * gaussianTail m v c' ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    linarith
  exact h3.trans_le (gaussianTail_antitone (le_max_left _ _))

/-- **Mills ratio** ([EKM, Example 1.4.7]; Feller, Vol. I, Lemma VII.1.2):
`Φ̄(c) ~ v p(c) / (c - m)` as `c → ∞`. -/
theorem tendsto_gaussianTail_div (hv : v ≠ 0) :
    Tendsto (fun c => gaussianTail m v c / (v * gaussianPDFReal m v c / (c - m))) atTop
      (𝓝 1) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hlo : Tendsto (fun c : ℝ => (1 + v / (c - m) ^ 2)⁻¹) atTop (𝓝 (1 + 0)⁻¹) := by
    refine ((tendsto_const_nhds.div_atTop ?_).const_add 1).inv₀ (by norm_num)
    exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-m) tendsto_id)
  rw [add_zero, inv_one] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop m] with c hc
    have hcm : 0 < c - m := by linarith
    have hp := gaussianPDFReal_pos m v c hv
    have h := le_gaussianTail hv hc
    rw [le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
    calc v * gaussianPDFReal m v c / (c - m) = v * (gaussianPDFReal m v c / (c - m)) := by ring
      _ ≤ v * ((1 / v + 1 / (c - m) ^ 2) * gaussianTail m v c) := by gcongr
      _ = _ := by field_simp
  · filter_upwards [eventually_gt_atTop m] with c hc
    have hcm : 0 < c - m := by linarith
    have hp := gaussianPDFReal_pos m v c hv
    rw [div_le_one (by positivity)]
    exact gaussianTail_le hv hc

/-- Ratio bound: for `m + 1 ≤ a ≤ b`,
`Φ̄(a) ≤ (b - m)/(a - m) · (1 + v/(b - m)²) · exp(((b - m)² - (a - m)²) / (2v)) · Φ̄(b)`. -/
theorem gaussianTail_le_mul (hv : v ≠ 0) {a b : ℝ} (ha : m + 1 ≤ a) (hab : a ≤ b) :
    gaussianTail m v a ≤ (b - m) / (a - m) * (1 + v / (b - m) ^ 2) *
      exp (((b - m) ^ 2 - (a - m) ^ 2) / (2 * v)) * gaussianTail m v b := by
  have hv' : (0 : ℝ) < v := by positivity
  have ham : 0 < a - m := by linarith
  have hbm : 0 < b - m := by linarith
  have h1 := gaussianTail_le hv (show m < a by linarith)
  have h2 := le_gaussianTail hv (show m < b by linarith)
  have hp : gaussianPDFReal m v a =
      gaussianPDFReal m v b * exp (((b - m) ^ 2 - (a - m) ^ 2) / (2 * v)) := by
    simp only [gaussianPDFReal_def, mul_assoc, ← exp_add]
    congr 2
    field_simp
    ring
  have hE : 0 < exp (((b - m) ^ 2 - (a - m) ^ 2) / (2 * v)) := exp_pos _
  have h2' : gaussianPDFReal m v b ≤ (b - m) / v * (1 + v / (b - m) ^ 2) * gaussianTail m v b := by
    rw [div_le_iff₀ hbm] at h2
    calc gaussianPDFReal m v b ≤ (1 / v + 1 / (b - m) ^ 2) * gaussianTail m v b * (b - m) := h2
      _ = _ := by field_simp
  calc gaussianTail m v a ≤ v * gaussianPDFReal m v a / (a - m) := h1
    _ = v / (a - m) * exp (((b - m) ^ 2 - (a - m) ^ 2) / (2 * v)) * gaussianPDFReal m v b := by
        rw [hp]; ring
    _ ≤ v / (a - m) * exp (((b - m) ^ 2 - (a - m) ^ 2) / (2 * v)) *
          ((b - m) / v * (1 + v / (b - m) ^ 2) * gaussianTail m v b) := by gcongr
    _ = _ := by field_simp

end Mills

/-! ### The lognormal law -/

section Lognormal

variable {m : ℝ} {v : ℝ≥0}

/-- The **lognormal law** `LN(m, v)`: the law of `exp Z` for `Z ∼ N(m, v)`. -/
noncomputable def lognormal (m : ℝ) (v : ℝ≥0) : Measure ℝ := (gaussianReal m v).map exp

instance isProbabilityMeasure_lognormal : IsProbabilityMeasure (lognormal m v) :=
  by rw [lognormal]; infer_instance

theorem lognormal_Iio_zero : lognormal m v (Iio 0) = 0 := by
  rw [lognormal, Measure.map_apply measurable_exp measurableSet_Iio]
  convert measure_empty (μ := gaussianReal m v)
  ext y; simp [(exp_pos y).le]

theorem tail_lognormal {x : ℝ} (hx : 0 < x) :
    tail (lognormal m v) x = gaussianTail m v (log x) := by
  rw [tail, lognormal, map_measureReal_apply measurable_exp measurableSet_Ioi, gaussianTail]
  congr 1
  ext y; simp only [mem_preimage, mem_Ioi]
  rw [log_lt_iff_lt_exp hx]

theorem tail_lognormal_pos (hv : v ≠ 0) (x : ℝ) : 0 < tail (lognormal m v) x := by
  have h1 : 0 < tail (lognormal m v) (max x 1) := by
    rw [tail_lognormal (by positivity)]; exact gaussianTail_pos hv _
  exact h1.trans_le (tail_antitone (le_max_left _ _))

/-- The basic ratio estimate for the lognormal tail: for `x ≥ 2 e^{m+1}` and `0 ≤ t ≤ x / 2`,
`F̄(x - t) ≤ (1 + 2t/x) (1 + v/(log x - m)²) exp(2t (log x - m) / (v x)) F̄(x)`. -/
theorem tail_lognormal_sub_le (hv : v ≠ 0) {x t : ℝ} (hx : 2 * exp (m + 1) ≤ x) (ht : 0 ≤ t)
    (htx : t ≤ x / 2) :
    tail (lognormal m v) (x - t) ≤ (1 + 2 * t / x) * (1 + v / (log x - m) ^ 2) *
      exp (2 * t * ((log x - m) / x) / v) * tail (lognormal m v) x := by
  have hv' : (0 : ℝ) < v := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hxt : x / 2 ≤ x - t := by linarith
  have hxt0 : 0 < x - t := by linarith
  have he : exp (m + 1) ≤ x - t := by linarith
  set a := log (x - t) with ha_def
  set b := log x with hb_def
  have ha : m + 1 ≤ a := (le_log_iff_exp_le hxt0).2 he
  have hab : a ≤ b := log_le_log hxt0 (by linarith)
  have hba : b - a ≤ 2 * t / x := by
    have h1 : b - a = log (x / (x - t)) := by rw [log_div hx0.ne' hxt0.ne']
    have h2 := log_le_sub_one_of_pos (div_pos hx0 hxt0)
    have h3 : x / (x - t) - 1 ≤ 2 * t / x := by
      rw [div_sub_one hxt0.ne', div_le_div_iff₀ hxt0 hx0]; nlinarith
    linarith
  set d := 2 * t / x with hd
  have hd0 : 0 ≤ d := by positivity
  have hfac1 : (b - m) / (a - m) ≤ 1 + d := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hfac2 : ((b - m) ^ 2 - (a - m) ^ 2) / (2 * v) ≤ 2 * t * ((b - m) / x) / v := by
    have e : 2 * t * ((b - m) / x) = d * (b - m) := by rw [hd]; ring
    rw [e, div_le_div_iff₀ (by positivity) hv']
    have : (b - m) ^ 2 - (a - m) ^ 2 ≤ 2 * d * (b - m) := by nlinarith
    nlinarith
  rw [tail_lognormal hxt0, tail_lognormal hx0]
  refine (gaussianTail_le_mul hv ha hab).trans ?_
  have hQ := (gaussianTail_pos hv (m := m) b).le
  gcongr

/-- `(log x - m) / x` is antitone on `[e^{m+1}, ∞)`. -/
private theorem log_sub_div_antitone {m y x : ℝ} (hy : exp (m + 1) ≤ y) (hyx : y ≤ x) :
    (log x - m) / x ≤ (log y - m) / y := by
  have hy0 : 0 < y := lt_of_lt_of_le (exp_pos _) hy
  have hx0 : 0 < x := hy0.trans_le hyx
  have hk : 0 < exp (-m) := exp_pos _
  have e : ∀ z, 0 < z → (log z - m) / z = exp (-m) * (log (z * exp (-m)) / (z * exp (-m))) := by
    intro z hz
    rw [log_mul hz.ne' hk.ne', log_exp, exp_neg]
    field_simp
    ring
  have hmem : ∀ z, exp (m + 1) ≤ z → z * exp (-m) ∈ Ici (exp 1) := by
    intro z hz
    show exp 1 ≤ z * exp (-m)
    calc exp 1 = exp (m + 1) * exp (-m) := by rw [← exp_add]; ring_nf
      _ ≤ z * exp (-m) := by gcongr
  rw [e x hx0, e y hy0]
  exact mul_le_mul_of_nonneg_left
    (log_div_self_antitoneOn (hmem y hy) (hmem x (hy.trans hyx)) (by gcongr)) (exp_pos (-m)).le

/-- The dominating function for `F̄(x - t) / F̄(x)`, `0 ≤ t ≤ x / 2`. -/
private noncomputable def domFun (m : ℝ) (v : ℝ≥0) (t : ℝ) : ℝ :=
  1 / tail (lognormal m v) (2 * exp (m + 1)) +
    2 * (1 + v) * exp ((log (max (2 * t) (exp (m + 1))) - m) / v)

private theorem ratio_le_domFun (hv : v ≠ 0) {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x / 2) :
    tail (lognormal m v) (x - t) / tail (lognormal m v) x ≤ domFun m v t := by
  have hv' : (0 : ℝ) < v := by positivity
  set F := tail (lognormal m v)
  have hF := tail_lognormal_pos (m := m) hv
  have hsecond : 0 ≤ 2 * (1 + (v : ℝ)) * exp ((log (max (2 * t) (exp (m + 1))) - m) / v) := by
    positivity
  rcases lt_or_ge x (2 * exp (m + 1)) with hx | hx
  · -- small `x`
    have h1 : F (x - t) / F x ≤ 1 / F x :=
      div_le_div_of_nonneg_right (tail_le_one _) (hF x).le
    have h2 : 1 / F x ≤ 1 / F (2 * exp (m + 1)) :=
      one_div_le_one_div_of_le (hF _) (tail_antitone hx.le)
    unfold domFun; linarith
  · have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    have hxe : exp (m + 1) ≤ x := by linarith [exp_pos (m + 1)]
    have hlog : m + 1 ≤ log x := (le_log_iff_exp_le hx0).2 hxe
    have hb := tail_lognormal_sub_le hv hx ht htx
    rw [← div_le_iff₀ (hF x)] at hb
    refine hb.trans (le_trans ?_ (le_add_of_nonneg_left (div_nonneg zero_le_one (tail_nonneg _))))
    set y := max (2 * t) (exp (m + 1))
    have hy : exp (m + 1) ≤ y := le_max_right _ _
    have hyx : y ≤ x := max_le (by linarith) hxe
    have hy0 : 0 < y := lt_of_lt_of_le (exp_pos _) hy
    have hlogy : m + 1 ≤ log y := (le_log_iff_exp_le hy0).2 hy
    have h1 : 1 + 2 * t / x ≤ 2 := by
      have : 2 * t / x ≤ 1 := by rw [div_le_one hx0]; linarith
      linarith
    have h2 : 1 + (v : ℝ) / (log x - m) ^ 2 ≤ 1 + v := by
      have : (v : ℝ) / (log x - m) ^ 2 ≤ v :=
        div_le_self hv'.le (one_le_pow₀ (by linarith))
      linarith
    have h3 : 2 * t * ((log x - m) / x) / v ≤ (log y - m) / v := by
      gcongr
      have hh := log_sub_div_antitone hy hyx
      have hnn : 0 ≤ (log y - m) / y := div_nonneg (by linarith) hy0.le
      calc 2 * t * ((log x - m) / x) ≤ 2 * t * ((log y - m) / y) := by gcongr
        _ ≤ y * ((log y - m) / y) := by gcongr; exact le_max_left _ _
        _ = log y - m := by field_simp
    have hpos1 : 0 ≤ 1 + 2 * t / x := by positivity
    have hpos2 : 0 ≤ 1 + (v : ℝ) / (log x - m) ^ 2 := by positivity
    calc (1 + 2 * t / x) * (1 + v / (log x - m) ^ 2) * exp (2 * t * ((log x - m) / x) / v)
        ≤ 2 * (1 + v) * exp ((log y - m) / v) := by
          gcongr
      _ = _ := rfl

private theorem integrable_domFun (hv : v ≠ 0) : Integrable (domFun m v) (lognormal m v) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hmeas : Measurable (domFun m v) := by unfold domFun; fun_prop
  rw [lognormal, integrable_map_measure hmeas.aestronglyMeasurable measurable_exp.aemeasurable]
  set c1 := 1 / tail (lognormal m v) (2 * exp (m + 1))
  set C := 2 * (1 + (v : ℝ))
  have hbound : Integrable (fun s => c1 + C * (exp ((log 2 - m) / v) * exp ((1 / v) * s) +
      exp ((m + 1 - m) / v))) (gaussianReal m v) :=
    (integrable_const _).add ((((integrable_exp_mul_gaussianReal (1 / v)).const_mul _).add
      (integrable_const _)).const_mul _)
  refine hbound.mono' (hmeas.comp measurable_exp).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  have hc1 : 0 ≤ c1 := by unfold c1; exact div_nonneg zero_le_one (tail_nonneg _)
  have hnn : 0 ≤ domFun m v (exp s) := by unfold domFun; positivity
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hnn]
  unfold domFun
  gcongr
  have hA : exp ((log (2 * exp s) - m) / v) = exp ((log 2 - m) / v) * exp ((1 / v) * s) := by
    rw [log_mul two_ne_zero (exp_pos s).ne', log_exp, ← exp_add]; congr 1; field_simp; ring
  have hB : exp ((m + 1 - m) / v) = exp ((log (exp (m + 1)) - m) / v) := by rw [log_exp]
  rw [← hA, hB]
  rcases le_total (2 * exp s) (exp (m + 1)) with h | h
  · rw [max_eq_right h]; linarith [exp_pos ((log (2 * exp s) - m) / v)]
  · rw [max_eq_left h]; linarith [exp_pos ((log (exp (m + 1)) - m) / v)]

private theorem tendsto_log_sub_div_atTop :
    Tendsto (fun x => (log x - m) / x) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun x : ℝ => m / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have := h1.sub h2
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [pow_one, one_mul, add_zero]
  ring

/-- **The lognormal law is long-tailed**: `F̄(x - t) / F̄(x) → 1` for every `t ≥ 0`. -/
theorem tendsto_tail_lognormal_sub_div (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun x => tail (lognormal m v) (x - t) / tail (lognormal m v) x) atTop (𝓝 1) := by
  have hF := tail_lognormal_pos (m := m) hv
  have h1 : Tendsto (fun x : ℝ => 2 * t / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun x : ℝ => (v : ℝ) / (log x - m) ^ 2) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-m)
      tendsto_log_atTop)
  have h3 : Tendsto (fun x => exp (2 * t * ((log x - m) / x) / v)) atTop (𝓝 1) := by
    have := (continuous_exp.tendsto _).comp
      (((tendsto_log_sub_div_atTop (m := m)).const_mul (2 * t)).div_const (v : ℝ))
    simp only [mul_zero, zero_div, exp_zero] at this
    exact this
  have hU := ((h1.const_add 1).mul (h2.const_add 1)).mul h3
  simp only [add_zero, mul_one] at hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · exact Eventually.of_forall fun x => (one_le_div (hF x)).2 (tail_antitone (by linarith))
  · filter_upwards [eventually_ge_atTop (2 * exp (m + 1)), eventually_ge_atTop (2 * t)]
      with x hx hxt
    rw [div_le_iff₀ (hF x)]
    exact tail_lognormal_sub_le hv hx ht (by linarith)

/-- `F̄(x / 2)² / F̄(x) → 0` for the lognormal law. -/
theorem tendsto_tail_lognormal_half_sq_div (hv : v ≠ 0) :
    Tendsto (fun x => tail (lognormal m v) (x / 2) ^ 2 / tail (lognormal m v) x) atTop
      (𝓝 0) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hF := tail_lognormal_pos (m := m) hv
  set L := log 2
  set K := (√(2 * π * v))⁻¹
  set C := v * K * (2 * (1 + v))
  -- the exponent tends to `-∞`
  have harg : Tendsto (fun x => -(log x - L - m - 1) ^ 2 / (2 * v) + (1 + 2 * L) / (2 * v))
      atTop atBot := by
    refine tendsto_atBot_add_const_right _ _ ?_
    refine Tendsto.atBot_div_const (by positivity) ?_
    refine tendsto_neg_atTop_atBot.comp ?_
    exact (tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_right _ (-(L + m + 1)) tendsto_log_atTop |>.congr
        fun x => by ring)
  have hlim : Tendsto (fun x => C * exp (-(log x - L - m - 1) ^ 2 / (2 * v) +
      (1 + 2 * L) / (2 * v))) atTop (𝓝 (C * 0)) :=
    (tendsto_exp_atBot.comp harg).const_mul C
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (hF x).le) ?_
  filter_upwards [eventually_ge_atTop (4 * exp (m + 1))] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hx2 : 0 < x / 2 := by positivity
  have ha : m + 1 ≤ log (x / 2) := (le_log_iff_exp_le hx2).2 (by linarith)
  have haL : log (x / 2) = log x - L := log_div hx0.ne' two_ne_zero
  -- `F̄(x/2) ≤ v p(log(x/2))`
  have hup : tail (lognormal m v) (x / 2) ≤ v * K * exp (-(log x - L - m) ^ 2 / (2 * v)) := by
    rw [tail_lognormal hx2]
    refine (gaussianTail_le hv (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith), gaussianPDFReal_def, haL]
    have : 0 ≤ v * K * exp (-(log x - L - m) ^ 2 / (2 * v)) := by positivity
    have h1 : 1 ≤ log x - L - m := by linarith
    nlinarith
  -- `F̄(x/2) ≤ 2(1 + v) exp((log x - m)/v) F̄(x)`
  have hrat : tail (lognormal m v) (x / 2) ≤
      2 * (1 + v) * exp ((log x - m) / v) * tail (lognormal m v) x := by
    have h := tail_lognormal_sub_le hv (m := m) (x := x) (t := x / 2) (by linarith) hx2.le le_rfl
    rw [show x - x / 2 = x / 2 by ring] at h
    refine h.trans ?_
    have hlog : m + 1 ≤ log x := (le_log_iff_exp_le hx0).2 (by linarith [exp_pos (m + 1)])
    have e1 : 1 + 2 * (x / 2) / x = 2 := by field_simp; ring
    have e2 : 2 * (x / 2) * ((log x - m) / x) / v = (log x - m) / v := by field_simp
    rw [e1, e2]
    have : (v : ℝ) / (log x - m) ^ 2 ≤ v := div_le_self hv'.le (one_le_pow₀ (by linarith))
    have := hF x
    gcongr
  rw [div_le_iff₀ (hF x), sq]
  have hnn := (hF (x / 2)).le
  calc tail (lognormal m v) (x / 2) * tail (lognormal m v) (x / 2)
      ≤ (v * K * exp (-(log x - L - m) ^ 2 / (2 * v))) *
          (2 * (1 + v) * exp ((log x - m) / v) * tail (lognormal m v) x) :=
        mul_le_mul hup hrat hnn (by positivity)
    _ = C * exp (-(log x - L - m - 1) ^ 2 / (2 * v) + (1 + 2 * L) / (2 * v)) *
          tail (lognormal m v) x := by
        rw [show C * exp (-(log x - L - m - 1) ^ 2 / (2 * v) + (1 + 2 * L) / (2 * v)) =
          C * (exp (-(log x - L - m) ^ 2 / (2 * v)) * exp ((log x - m) / v)) by
            rw [← exp_add]; congr 2; field_simp; ring]
        ring

end Lognormal

/-- **The lognormal law is subexponential ([EKM, Example 1.4.7 and Table 1.4.3]).** For every
`m ∈ ℝ` and variance `v > 0`, the law of `exp Z`, `Z ∼ N(m, v)`, is subexponential. -/
theorem IsSubexponential.lognormal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    IsSubexponential (lognormal m v) :=
  IsSubexponential.of_dominated lognormal_Iio_zero (tail_lognormal_pos hv)
    (fun _ ht => tendsto_tail_lognormal_sub_div hv ht) (integrable_domFun hv)
    (fun _ _ ht htx => ratio_le_domFun hv ht htx) (tendsto_tail_lognormal_half_sq_div hv)

end ExtremeValueTheory
