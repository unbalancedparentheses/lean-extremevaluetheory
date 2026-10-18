/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Karamata

/-!
# Minimality of the hypotheses of Karamata's theorem

`ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div` (Karamata's theorem for tail
integrals) states: if `F` is antitone and regularly varying with index `-α`, `α > 1`, then

  `(∫ t in Ioi x, F t) / (x * F x) → 1 / (α - 1)`.

We show that the hypothesis `α > 1` cannot be weakened.

* `α < 1`: `not_tendsto_integral_Ioi_div_of_lt_one`: for **every** antitone `F` regularly
  varying with index `-α`, `α < 1`, the conclusion fails (the ratio is nonnegative, the claimed
  limit is negative). The mathematical reason is that the tail integral diverges, which we
  record for `F x = max x 1 ^ (-α)` in `not_integrableOn_Ioi_max_rpow`.
* `α = 1`: in Lean `1 / (1 - 1) = 0`, and a non-integrable `F` (such as `1 / x`) satisfies the
  conclusion only through the junk value `∫ = 0`. The honest statement is
  `tendsto_integral_Ioi_div_atTop_of_neg_one` ([BGT, Proposition 1.5.9b]): for **every**
  antitone `F` regularly varying with index `-1` whose tail is integrable, the ratio tends to
  `+∞`, so the conclusion fails (`not_tendsto_integral_Ioi_div_of_neg_one`). The hypotheses are
  not vacuous: `logTail 2 x = 1 / (x (log x)²)` (for `x ≥ e`) is an example
  (`logTail_two_karamata_counterexample`), with `(∫_x^∞ logTail 2) / (x logTail 2 x) = log x`.

The function `logTail a` (`= 1` on `(-∞, e)`, `= 1 / (x (log x)^a)` on `[e, ∞)`) is reused in
`ExtremeValueTheory.Minimality.ClassicalBreiman`.

## Summary

| hypothesis | status |
|---|---|
| `α > 1` | necessary: `α < 1` fails for every `F`; `α = 1` fails for every integrable `F` |
| `Antitone F` | weakened to measurability + local boundedness in
  `tendsto_integral_Ioi_div_of_measurable` (`KaramataConverse.lean`) |

[BGT] N. H. Bingham, C. M. Goldie, J. L. Teugels, *Regular Variation*, CUP 1987.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory.Minimality

/-! ### The functions `logTail a` -/

/-- `logTail a t = 1` for `t < e` and `(t (log t)^a)⁻¹` for `t ≥ e`: an antitone function,
regularly varying with index `-1`, with a slowly varying factor `(log t)^{-a}`. -/
noncomputable def logTail (a : ℕ) (t : ℝ) : ℝ :=
  if t < exp 1 then 1 else (t * log t ^ a)⁻¹

variable {a : ℕ} {t : ℝ}

theorem logTail_of_lt (ht : t < exp 1) : logTail a t = 1 := by simp [logTail, ht]

theorem logTail_of_ge (ht : exp 1 ≤ t) : logTail a t = (t * log t ^ a)⁻¹ := by
  simp [logTail, not_lt.2 ht]

theorem one_le_log_of_ge (ht : exp 1 ≤ t) : 1 ≤ log t := by
  rw [← log_exp 1]
  exact log_le_log (exp_pos 1) ht

theorem one_le_of_exp_one_le (ht : exp 1 ≤ t) : 1 ≤ t :=
  (one_le_exp zero_le_one).trans ht

theorem one_le_mul_log_pow (ht : exp 1 ≤ t) : 1 ≤ t * log t ^ a :=
  one_le_mul_of_one_le_of_one_le (one_le_of_exp_one_le ht) (one_le_pow₀ (one_le_log_of_ge ht))

theorem logTail_pos (a : ℕ) (t : ℝ) : 0 < logTail a t := by
  by_cases ht : t < exp 1
  · rw [logTail_of_lt ht]; exact one_pos
  · rw [logTail_of_ge (not_lt.1 ht)]
    exact inv_pos.2 (one_pos.trans_le (one_le_mul_log_pow (not_lt.1 ht)))

theorem logTail_le_one (a : ℕ) (t : ℝ) : logTail a t ≤ 1 := by
  by_cases ht : t < exp 1
  · rw [logTail_of_lt ht]
  · rw [logTail_of_ge (not_lt.1 ht)]
    exact inv_le_one_of_one_le₀ (one_le_mul_log_pow (not_lt.1 ht))

theorem antitone_logTail (a : ℕ) : Antitone (logTail a) := by
  intro s t hst
  by_cases ht : t < exp 1
  · rw [logTail_of_lt ht, logTail_of_lt (hst.trans_lt ht)]
  push Not at ht
  by_cases hs : s < exp 1
  · rw [logTail_of_lt hs]; exact logTail_le_one a t
  push Not at hs
  rw [logTail_of_ge ht, logTail_of_ge hs]
  have hs1 := one_le_mul_log_pow (a := a) hs
  refine inv_anti₀ (by linarith) ?_
  have hl : 0 ≤ log s := by linarith [one_le_log_of_ge hs]
  have hs0 : 0 < s := by linarith [one_le_of_exp_one_le hs]
  exact mul_le_mul hst (pow_le_pow_left₀ hl (log_le_log hs0 hst) a) (pow_nonneg hl a)
    (by linarith)

/-- `logTail a` is regularly varying with index `-1`. -/
theorem isRegularlyVarying_logTail (a : ℕ) : IsRegularlyVarying (logTail a) (-1) := by
  have h := (IsRegularlyVarying.rpow_id (-1)).mul
    (isSlowlyVarying_log.rpow (-(a : ℝ))).isRegularlyVarying
  rw [add_zero] at h
  refine h.congr ?_
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hl : 0 < log x := one_pos.trans_le (one_le_log_of_ge hx)
  rw [logTail_of_ge hx, rpow_neg_one, rpow_neg hl.le, rpow_natCast, mul_inv]

theorem continuousOn_logTail (a : ℕ) : ContinuousOn (fun t => (t * log t ^ a)⁻¹) (Ici (exp 1)) := by
  intro t ht
  have ht' : exp 1 ≤ t := ht
  have h0 : t ≠ 0 := by linarith [one_le_of_exp_one_le ht']
  refine ((continuousAt_id.mul ((continuousAt_log h0).pow a)).inv₀ ?_).continuousWithinAt
  exact (one_pos.trans_le (one_le_mul_log_pow ht')).ne'

theorem tendsto_logTail_atTop (a : ℕ) : Tendsto (logTail a) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t * log t ^ a) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (exp 1)] with t ht
    have := one_le_pow₀ (n := a) (one_le_log_of_ge ht)
    have := one_le_of_exp_one_le ht
    simp only [id]
    nlinarith
  refine h.inv_tendsto_atTop.congr' ?_
  filter_upwards [eventually_ge_atTop (exp 1)] with t ht
  rw [logTail_of_ge ht]
  rfl

/-- `∫_x^∞ dt / (t (log t)²) = 1 / log x` for `x > 1`. -/
theorem integral_Ioi_inv_mul_log_sq {x : ℝ} (hx : 1 < x) :
    ∫ t in Ioi x, (t * log t ^ 2)⁻¹ = (log x)⁻¹ := by
  have hderiv : ∀ t ∈ Ici x, HasDerivAt (fun t => -(log t)⁻¹) ((t * log t ^ 2)⁻¹) t := by
    intro t ht
    have ht1 : 1 < t := hx.trans_le ht
    have ht0 : 0 < t := by linarith
    have hl : log t ≠ 0 := (log_pos ht1).ne'
    convert ((hasDerivAt_log ht0.ne').inv hl).neg using 1
    field_simp
  have hlim : Tendsto (fun t => -(log t)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_log_atTop).neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv (fun t ht => ?_) hlim]
  · ring
  · have ht1 : 1 < t := hx.trans ht
    have : 0 < log t := log_pos ht1
    positivity

theorem integrableOn_Ioi_inv_mul_log_sq {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t => (t * log t ^ 2)⁻¹) (Ioi x) := by
  have hderiv : ∀ t ∈ Ici x, HasDerivAt (fun t => -(log t)⁻¹) ((t * log t ^ 2)⁻¹) t := by
    intro t ht
    have ht1 : 1 < t := hx.trans_le ht
    have ht0 : 0 < t := by linarith
    have hl : log t ≠ 0 := (log_pos ht1).ne'
    convert ((hasDerivAt_log ht0.ne').inv hl).neg using 1
    field_simp
  have hlim : Tendsto (fun t => -(log t)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_log_atTop).neg
  refine integrableOn_Ioi_deriv_of_nonneg' hderiv (fun t ht => ?_) hlim
  have ht1 : 1 < t := hx.trans ht
  have : 0 < log t := log_pos ht1
  positivity

theorem integral_Ioi_logTail_two {x : ℝ} (hx : exp 1 ≤ x) :
    ∫ t in Ioi x, logTail 2 t = (log x)⁻¹ := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t (ht : x < t) => logTail_of_ge (a := 2) (hx.trans ht.le))]
  exact integral_Ioi_inv_mul_log_sq ((one_lt_exp_iff.2 one_pos).trans_le hx)

theorem integrableOn_Ioi_logTail_two (x : ℝ) : IntegrableOn (logTail 2) (Ioi x) := by
  have hm : Measurable (logTail 2) := (antitone_logTail 2).measurable
  have he : IntegrableOn (logTail 2) (Ioi (exp 1)) := by
    refine (integrableOn_Ioi_inv_mul_log_sq (one_lt_exp_iff.2 one_pos)).congr_fun
      (fun t (ht : exp 1 < t) => (logTail_of_ge ht.le).symm) measurableSet_Ioi
  rcases le_or_gt (exp 1) x with h | h
  · exact he.mono_set (Ioi_subset_Ioi h)
  · have hb : IntegrableOn (logTail 2) (Ioc x (exp 1)) := by
      refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
        hm.aestronglyMeasurable ?_
      refine ae_of_all _ fun t => ?_
      rw [Real.norm_eq_abs, abs_of_pos (logTail_pos 2 t)]
      exact logTail_le_one 2 t
    rw [← Ioc_union_Ioi_eq_Ioi h.le]
    exact hb.union he

/-! ### The case `α < 1` -/

/-- **Karamata's theorem fails for every `α < 1`.** If `F` is antitone and regularly varying with
index `-α`, `α < 1`, then `(∫ t in Ioi x, F t) / (x * F x)` does not tend to `1 / (α - 1)`. -/
theorem not_tendsto_integral_Ioi_div_of_lt_one {F : ℝ → ℝ} {α : ℝ} (hF : Antitone F)
    (hRV : IsRegularlyVarying F (-α)) (hα : α < 1) :
    ¬ Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 (1 / (α - 1))) := by
  intro h
  have hFpos := IsRegularlyVarying.pos_of_antitone hF hRV.1
  have hnn : ∀ᶠ x in atTop, 0 ≤ (∫ t in Ioi x, F t) / (x * F x) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_nonneg (setIntegral_nonneg measurableSet_Ioi fun t _ => (hFpos t).le)
      (mul_pos hx (hFpos x)).le
  have := ge_of_tendsto h hnn
  have : 1 / (α - 1) < 0 := one_div_neg.2 (by linarith)
  linarith

/-- For `α < 1` the tail integral of `max x 1 ^ (-α)` diverges. -/
theorem not_integrableOn_Ioi_max_rpow {α : ℝ} (hα : α < 1) (x : ℝ) :
    ¬ IntegrableOn (fun t => max t 1 ^ (-α)) (Ioi x) := by
  intro h
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioi (max x 1)) := by
    refine (h.mono_set (Ioi_subset_Ioi (le_max_left x 1))).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    have : 1 < t := (le_max_right x 1).trans_lt ht
    simp only [max_eq_left this.le]
  exact (integrableOn_Ioi_rpow_iff (zero_lt_one.trans_le (le_max_right x 1))).1 h1 |>.not_ge
    (by linarith)

/-! ### The case `α = 1` -/

/-- **Karamata's theorem at index `-1`** ([BGT, Proposition 1.5.9b]): if `F` is antitone,
regularly varying with index `-1` and integrable on a half-line, then
`(∫ t in Ioi x, F t) / (x * F x) → ∞`. -/
theorem tendsto_integral_Ioi_div_atTop_of_neg_one {F : ℝ → ℝ} (hF : Antitone F)
    (hRV : IsRegularlyVarying F (-1)) {x₀ : ℝ} (hint : IntegrableOn F (Ioi x₀)) :
    Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop atTop := by
  have hFpos := IsRegularlyVarying.pos_of_antitone hF hRV.1
  have hFm : Measurable F := hF.measurable
  -- Change of variables `t = x * u`.
  have hsub : ∀ x > 0,
      ∫ u in Ioi (1 : ℝ), F (x * u) / F x = (∫ t in Ioi x, F t) / (x * F x) := by
    intro x hx
    rw [integral_div, integral_comp_mul_left_Ioi F 1 hx, mul_one, smul_eq_mul, inv_mul_eq_div,
      div_div]
  have hintx : ∀ x > max x₀ 0, IntegrableOn (fun u => F (x * u) / F x) (Ioi 1) := by
    intro x hx
    have hx0 : 0 < x := (le_max_right _ _).trans_lt hx
    have h1 : IntegrableOn F (Ioi (x * 1)) :=
      hint.mono_set (Ioi_subset_Ioi (by rw [mul_one]; exact (le_max_left _ _).trans hx.le))
    have := (integrableOn_Ioi_comp_mul_left_iff F 1 hx0).2 h1
    exact this.div_const _
  refine tendsto_atTop.2 fun M => ?_
  -- Truncate at `R = exp (M + 1)` and use dominated convergence on `(1, R]`.
  set R := exp (|M| + 1) with hR
  have hR1 : 1 < R := one_lt_exp_iff.2 (by positivity)
  have hlimR : Tendsto (fun x => ∫ u in Ioc 1 R, F (x * u) / F x) atTop
      (𝓝 (∫ u in Ioc 1 R, u ^ (-1 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        ((hFm.comp (measurable_id.const_mul x)).div_const _).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with x hx
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (hFpos _) (hFpos _)), div_le_one (hFpos _)]
      exact hF (le_mul_of_one_le_right hx.le hu.1.le)
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
      exact (hRV.2 u (zero_lt_one.trans hu.1)).congr fun x => by rw [mul_comm]
  have hval : ∫ u in Ioc 1 R, u ^ (-1 : ℝ) = |M| + 1 := by
    rw [← intervalIntegral.integral_of_le hR1.le]
    have : ∫ u in (1 : ℝ)..R, u ^ (-1 : ℝ) = ∫ u in (1 : ℝ)..R, u⁻¹ :=
      intervalIntegral.integral_congr fun u _ => rpow_neg_one u
    rw [this, integral_inv_of_pos one_pos (by linarith), div_one, hR, log_exp]
  rw [hval] at hlimR
  have hev := hlimR.eventually (lt_mem_nhds (show |M| < |M| + 1 by linarith))
  filter_upwards [hev, eventually_gt_atTop (max x₀ 0)] with x h1 h2
  have hx0 : 0 < x := (le_max_right _ _).trans_lt h2
  rw [← hsub x hx0]
  have hle : ∫ u in Ioc 1 R, F (x * u) / F x ≤ ∫ u in Ioi 1, F (x * u) / F x :=
    setIntegral_mono_set (hintx x h2)
      (ae_of_all _ fun u => (div_pos (hFpos _) (hFpos _)).le)
      (Ioc_subset_Ioi_self.eventuallyLE)
  linarith [le_abs_self M]

/-- **Karamata's theorem fails at `α = 1`.** For every antitone `F`, regularly varying with
index `-1` and integrable on a half-line, the ratio does not tend to `1 / (1 - 1) = 0` (it tends
to `+∞`, `tendsto_integral_Ioi_div_atTop_of_neg_one`). -/
theorem not_tendsto_integral_Ioi_div_of_neg_one {F : ℝ → ℝ} (hF : Antitone F)
    (hRV : IsRegularlyVarying F (-1)) {x₀ : ℝ} (hint : IntegrableOn F (Ioi x₀)) (L : ℝ) :
    ¬ Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop (tendsto_integral_Ioi_div_atTop_of_neg_one hF hRV hint) L

/-- For `F = logTail 2`, `(∫_x^∞ F) / (x F x) = log x` for `x ≥ e`. -/
theorem integral_Ioi_div_logTail_two {x : ℝ} (hx : exp 1 ≤ x) :
    (∫ t in Ioi x, logTail 2 t) / (x * logTail 2 x) = log x := by
  have hl : 0 < log x := one_pos.trans_le (one_le_log_of_ge hx)
  have hx0 : 0 < x := one_pos.trans_le (one_le_of_exp_one_le hx)
  rw [integral_Ioi_logTail_two hx, logTail_of_ge hx]
  field_simp

/-- **The hypothesis `α > 1` of Karamata's theorem is necessary, concrete counterexample at
`α = 1`.** `F = logTail 2` (`F x = 1 / (x (log x)²)` for `x ≥ e`) is antitone, regularly varying
with index `-1` and integrable on every half-line, but `(∫_x^∞ F) / (x F x) = log x → ∞`; in
particular it does not converge to `1 / (1 - 1)`, nor to any real number. -/
theorem logTail_two_karamata_counterexample :
    Antitone (logTail 2) ∧ IsRegularlyVarying (logTail 2) (-1) ∧
      (∀ x, IntegrableOn (logTail 2) (Ioi x)) ∧
      Tendsto (fun x => (∫ t in Ioi x, logTail 2 t) / (x * logTail 2 x)) atTop atTop ∧
      ∀ L, ¬ Tendsto (fun x => (∫ t in Ioi x, logTail 2 t) / (x * logTail 2 x)) atTop (𝓝 L) := by
  have h : Tendsto (fun x => (∫ t in Ioi x, logTail 2 t) / (x * logTail 2 x)) atTop atTop := by
    refine tendsto_log_atTop.congr' ?_
    filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    exact (integral_Ioi_div_logTail_two hx).symm
  exact ⟨antitone_logTail 2, isRegularlyVarying_logTail 2, integrableOn_Ioi_logTail_two, h,
    fun L => not_tendsto_nhds_of_tendsto_atTop h L⟩

/-- **Concrete counterexample for `α < 1`.** For `0 ≤ α < 1`, `F x = max x 1 ^ (-α)` is antitone
and regularly varying with index `-α`, its tail integrals diverge, and the conclusion of
Karamata's theorem fails. -/
theorem max_rpow_karamata_counterexample {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) :
    Antitone (fun x : ℝ => max x 1 ^ (-α)) ∧
      IsRegularlyVarying (fun x : ℝ => max x 1 ^ (-α)) (-α) ∧
      (∀ x, ¬ IntegrableOn (fun t : ℝ => max t 1 ^ (-α)) (Ioi x)) ∧
      ¬ Tendsto (fun x => (∫ t in Ioi x, max t 1 ^ (-α)) / (x * max x 1 ^ (-α))) atTop
        (𝓝 (1 / (α - 1))) := by
  have hanti : Antitone (fun x : ℝ => max x 1 ^ (-α)) := fun x y hxy =>
    rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (le_max_right _ _)) (max_le_max hxy le_rfl)
      (by linarith)
  have hRV : IsRegularlyVarying (fun x : ℝ => max x 1 ^ (-α)) (-α) :=
    (IsRegularlyVarying.rpow_id (-α)).congr (by
      filter_upwards [eventually_ge_atTop 1] with x hx
      rw [max_eq_left hx])
  exact ⟨hanti, hRV, not_integrableOn_Ioi_max_rpow hα,
    not_tendsto_integral_Ioi_div_of_lt_one hanti hRV hα⟩

end ExtremeValueTheory.Minimality
