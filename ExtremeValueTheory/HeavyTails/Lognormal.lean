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

end Lognormal

end ExtremeValueTheory
