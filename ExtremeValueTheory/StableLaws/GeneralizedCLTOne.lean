/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT

/-!
# The generalized central limit theorem for `α = 1`

Let `X₁, X₂, …` be i.i.d. with law `μ` whose two-sided tail `G(x) = P(|X| > x)` is regularly
varying with index `-1`, with tail balance `P(X > x) / G(x) → p` (so `P(X < -x) / G(x) → q = 1 - p`),
and let `aₙ > 0` with `n G(aₙ) → 1`. With the truncated centering
`bₙ = n E[X 1{|X| ≤ aₙ}]`, `(X₁ + ⋯ + Xₙ - bₙ) / aₙ` converges in law to the `1`-stable law with
characteristic function
`exp (-C₁ |t| + i (p - q) (c t - t log |t|))`
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2], [EKM, Theorem 2.2.8]), where
`C₁ = stableConst 1` (classically `π / 2`) and
`c = stableLogConst = 1 + ∫₀¹ (cos v - 1) / v dv + ∫₁^∞ cos v / v dv` (classically `1 - γ`,
`γ` the Euler–Mascheroni constant; the improper integral `∫₁^∞ cos v / v dv` is written as
`-sin 1 + ∫₁^∞ sin v / v² dv`). We keep both constants as explicit integrals.

## Main definitions

* `StableIntegral.truncSinDeriv t u = t cos (t u) - t 1{u < 1}`, the derivative of
  `u ↦ sin (t u) - t min (u, 1)` on `u ≥ 0`.
* `StableIntegral.cosLogConst = ∫₀¹ (cos v - 1) / v dv - sin 1 + ∫₁^∞ sin v / v² dv`.
* `StableIntegral.stableLogConst = 1 + cosLogConst`.
* `stableExponentOne c e κ t = -c |t| + i e (κ t - t log |t|)`.
* `HasStableOneCharFun c e κ μ`: `μ` is a probability measure with characteristic function
  `exp (stableExponentOne c e κ ·)`.

## Main results

* `StableIntegral.tendsto_setIntegral_truncSinDeriv_mul_inv`: the improper integral
  `∫₀^M (t cos (t u) - t 1{u < 1}) / u du → t (cosLogConst - log |t|)` as `M → ∞`
  (change of variables `v = |t| u`).
* `GCLT.tendsto_mul_integral_clampSin_max`: the one-sided sine part.
* `GCLT.tendsto_mul_sq_truncMean`: `n (t E[X 1{|X| ≤ aₙ}] / aₙ)² → 0` (Potter bounds).
* `tendsto_map_convPow_sub_of_isRegularlyVarying_one`: **the generalized CLT for `α = 1`**.

## Proof outline

Write `s = t / aₙ`, `mₙ = E[X 1{|X| ≤ aₙ}]`. The real part of `n (φ(s) - 1 - i s mₙ)` is
`-n ∫ (1 - cos (s x)) dμ → -C₁ |t|` (`GCLT.tendsto_mul_integral_one_sub_cos`). For the imaginary
part, with `Q(v) = sin (t v) - t clamp(v, -1, 1)` (continuous and odd),
`sin (t v) - t v 1{|v| ≤ 1} = Q(v) + t (1{v > 1} - 1{v < -1})`, so
`n ∫ (sin (s x) - s x 1{|x| ≤ aₙ}) dμ = n E Q(X⁺/aₙ) - n E Q(X⁻/aₙ) + t n (P(X > aₙ) - P(X < -aₙ))`.
The boundary term tends to `t (p - q)`. For a right tail `R` with `n R(aₙ u) → c / u`, the
truncated layer-cake formula `E Q(min (X⁺/a, M)) = ∫₀^M (t cos (t u) - t 1{u < 1}) R(a u) du`,
the truncation error `2 R(a M)` (`M ≥ 1`), Potter domination and the improper integral above give
`n E Q(X⁺/aₙ) → c t (cosLogConst - log |t|)`. Finally `n (t mₙ / aₙ)² → 0` and Lévy's continuity
theorem give the limit law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

namespace StableIntegral

/-- `∫₁^N cos v / v dv = sin N / N - sin 1 + ∫₁^N sin v / v² dv` for `N > 0`. -/
theorem intervalIntegral_cos_div_eq {N : ℝ} (hN : 0 < N) :
    ∫ v in (1 : ℝ)..N, cos v / v = sin N / N - sin 1 + ∫ v in (1 : ℝ)..N, sin v / v ^ 2 := by
  have hpos : ∀ x ∈ uIcc (1 : ℝ) N, 0 < x := fun x hx =>
    lt_of_lt_of_le (lt_min one_pos hN) hx.1
  have hu : ∀ x ∈ uIcc (1 : ℝ) N, HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx => hasDerivAt_inv (hpos x hx).ne'
  have hv : ∀ x ∈ uIcc (1 : ℝ) N, HasDerivAt sin (cos x) x := fun x _ => hasDerivAt_sin x
  have hu' : IntervalIntegrable (fun x : ℝ => -(x ^ 2)⁻¹) volume 1 N := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hpos x hx).ne')).neg.continuousWithinAt
  have hv' : IntervalIntegrable cos volume 1 N := continuous_cos.intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : ∫ v in (1 : ℝ)..N, cos v / v = ∫ x in (1 : ℝ)..N, x⁻¹ * cos x :=
    intervalIntegral.integral_congr fun x _ => by rw [div_eq_inv_mul]
  have e2 : ∫ x in (1 : ℝ)..N, -(x ^ 2)⁻¹ * sin x = -∫ v in (1 : ℝ)..N, sin v / v ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => by
      show -(x ^ 2)⁻¹ * sin x = -(sin x / x ^ 2)
      rw [div_eq_inv_mul]; ring
  rw [e1, h, e2, inv_one, one_mul, div_eq_inv_mul]
  ring

theorem integrableOn_sin_div_sq : IntegrableOn (fun v : ℝ => sin v / v ^ 2) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).mono'
    (measurable_sin.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v (hv : 1 < v) => ?_
  have hv0 : 0 < v := one_pos.trans hv
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hv0 2), rpow_neg hv0.le, rpow_two,
    div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.2 (by positivity)) (abs_sin_le_one v)

/-- `∫₁^N cos v / v dv → -sin 1 + ∫₁^∞ sin v / v² dv` as `N → ∞`. -/
theorem tendsto_intervalIntegral_cos_div :
    Tendsto (fun N => ∫ v in (1 : ℝ)..N, cos v / v) atTop
      (𝓝 (-sin 1 + ∫ v in Ioi (1 : ℝ), sin v / v ^ 2)) := by
  have h1 : Tendsto (fun N : ℝ => sin N / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 hN.le) (abs_sin_le_one N)
  have h2 := intervalIntegral_tendsto_integral_Ioi 1 integrableOn_sin_div_sq tendsto_id
  have := (h1.sub_const (sin 1)).add h2
  rw [zero_sub] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [intervalIntegral_cos_div_eq hN]
  rfl

/-- The constant `∫₀¹ (cos v - 1) / v dv + ∫₁^∞ cos v / v dv`, the improper integral written
after an integration by parts as `-sin 1 + ∫₁^∞ sin v / v² dv`. Classically it equals `-γ`. -/
noncomputable def cosLogConst : ℝ :=
  (∫ v in (0 : ℝ)..1, (cos v - 1) / v) - sin 1 + ∫ v in Ioi (1 : ℝ), sin v / v ^ 2

/-- The constant of the drift term of the `1`-stable limit,
`c = 1 + ∫₀¹ (cos v - 1) / v dv + ∫₁^∞ cos v / v dv` (classically `1 - γ`). -/
noncomputable def stableLogConst : ℝ := 1 + cosLogConst

theorem abs_cos_sub_one_div_le (v : ℝ) : |(cos v - 1) / v| ≤ |v| / 2 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rw [abs_div, abs_sub_comm, abs_of_nonneg (one_sub_cos_nonneg v), div_le_iff₀ (abs_pos.2 hv)]
  have h := one_sub_cos_le_sq v
  have : |v| / 2 * |v| = v ^ 2 / 2 := by
    rw [show |v| / 2 * |v| = (|v| * |v|) / 2 by ring, abs_mul_abs_self, sq]
  linarith

theorem intervalIntegrable_cos_sub_one_div (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => (cos v - 1) / v) volume a b := by
  refine (intervalIntegrable_const (c := (|a| + |b|) / 2)).mono_fun'
    ((measurable_cos.sub_const 1).div measurable_id).aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun v hv => ?_
  rw [Real.norm_eq_abs]
  refine (abs_cos_sub_one_div_le v).trans ?_
  obtain ⟨h1, h2⟩ := hv
  have h3 : max a b ≤ |a| + |b| :=
    max_le (by linarith [le_abs_self a, abs_nonneg b]) (by linarith [le_abs_self b, abs_nonneg a])
  have h4 : -(|a| + |b|) ≤ min a b :=
    le_min (by linarith [neg_abs_le a, abs_nonneg b]) (by linarith [neg_abs_le b, abs_nonneg a])
  have : |v| ≤ |a| + |b| := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

theorem intervalIntegrable_cos_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun v : ℝ => cos v / v) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ?_
  have hx0 : 0 < x := lt_of_lt_of_le (lt_min ha hb) hx.1
  exact (continuous_cos.continuousAt.div continuousAt_id hx0.ne').continuousWithinAt

theorem intervalIntegrable_inv' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun v : ℝ => v⁻¹) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ?_
  have hx0 : 0 < x := lt_of_lt_of_le (lt_min ha hb) hx.1
  exact (continuousAt_id.inv₀ hx0.ne').continuousWithinAt

/-- `g_t(u) = t cos (t u) - t 1{u < 1}`, the derivative of `u ↦ sin (t u) - t min (u, 1)`
(away from `u = 1`). -/
noncomputable def truncSinDeriv (t u : ℝ) : ℝ :=
  t * cos (t * u) - (Iio (1 : ℝ)).indicator (fun _ => t) u

@[fun_prop]
theorem measurable_truncSinDeriv (t : ℝ) : Measurable (truncSinDeriv t) :=
  (by fun_prop : Measurable fun u : ℝ => t * cos (t * u)).sub
    (measurable_const.indicator measurableSet_Iio)

theorem truncSinDeriv_neg (t u : ℝ) : truncSinDeriv (-t) u = -truncSinDeriv t u := by
  unfold truncSinDeriv
  by_cases h : u < 1
  · rw [indicator_of_mem (show u ∈ Iio (1 : ℝ) from h),
      indicator_of_mem (show u ∈ Iio (1 : ℝ) from h), neg_mul t u, cos_neg]
    ring
  · rw [indicator_of_notMem (show u ∉ Iio (1 : ℝ) from h),
      indicator_of_notMem (show u ∉ Iio (1 : ℝ) from h), neg_mul t u, cos_neg]
    ring

theorem abs_truncSinDeriv_le_two (t u : ℝ) : |truncSinDeriv t u| ≤ 2 * |t| := by
  unfold truncSinDeriv
  have h1 : |t * cos (t * u)| ≤ |t| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have h2 : |(Iio (1 : ℝ)).indicator (fun _ => t) u| ≤ |t| :=
    norm_indicator_le_norm_self (fun _ => t) u
  calc _ ≤ |t * cos (t * u)| + |(Iio (1 : ℝ)).indicator (fun _ => t) u| := abs_sub _ _
    _ ≤ _ := by linarith

theorem abs_truncSinDeriv_le (t : ℝ) {u : ℝ} (hu : 0 < u) :
    |truncSinDeriv t u| ≤ (|t| ^ 3 / 2 + |t|) * u ^ 2 := by
  unfold truncSinDeriv
  have hpos := mul_nonneg (abs_nonneg t) (sq_nonneg u)
  by_cases h : u < 1
  · rw [indicator_of_mem (show u ∈ Iio (1 : ℝ) from h)]
    have h1 : |t * cos (t * u) - t| = |t| * (1 - cos (t * u)) := by
      rw [show t * cos (t * u) - t = -t * (1 - cos (t * u)) by ring, abs_mul, abs_neg,
        abs_of_nonneg (one_sub_cos_nonneg _)]
    rw [h1]
    have h2 := one_sub_cos_le_sq (t * u)
    calc |t| * (1 - cos (t * u)) ≤ |t| * ((t * u) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |t| ^ 3 / 2 * u ^ 2 := by rw [mul_pow, ← sq_abs t]; ring
      _ ≤ _ := by rw [add_mul]; linarith
  · rw [indicator_of_notMem (show u ∉ Iio (1 : ℝ) from h), sub_zero, abs_mul]
    have hu1 : 1 ≤ u := not_lt.1 h
    have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
    have h3 : 0 ≤ |t| ^ 3 / 2 * u ^ 2 := by positivity
    calc |t| * |cos (t * u)| ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
      _ ≤ |t| * u ^ 2 := mul_le_mul_of_nonneg_left hu2 (abs_nonneg _)
      _ ≤ _ := by rw [add_mul]; linarith

theorem integrableOn_truncSinDeriv_mul_inv (t : ℝ) {M : ℝ} :
    IntegrableOn (fun u => truncSinDeriv t u * u⁻¹) (Ioo 0 M) := by
  refine Measure.integrableOn_of_bounded (M := (|t| ^ 3 / 2 + |t|) * M) measure_Ioo_lt_top.ne
    (by fun_prop) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 < u := hu.1
  rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hu0]
  have hC : 0 ≤ |t| ^ 3 / 2 + |t| := by positivity
  calc |truncSinDeriv t u| * u⁻¹ ≤ (|t| ^ 3 / 2 + |t|) * u ^ 2 * u⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_truncSinDeriv_le t hu0) (inv_nonneg.2 hu0.le)
    _ = (|t| ^ 3 / 2 + |t|) * u := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hu.2.le hC

/-- **Change of variables** `v = t u`: for `t > 0` and `M ≥ 1`,
`∫₀^M g_t(u) / u du = t (∫₀¹ (cos v - 1) / v dv + ∫₁^{t M} cos v / v dv - log t)`. -/
theorem setIntegral_truncSinDeriv_mul_inv {t M : ℝ} (ht : 0 < t) (hM : 1 ≤ M) :
    ∫ u in Ioo 0 M, truncSinDeriv t u * u⁻¹ =
      t * ((∫ v in (0 : ℝ)..1, (cos v - 1) / v) + (∫ v in (1 : ℝ)..t * M, cos v / v) -
        log t) := by
  have hM0 : 0 < M := one_pos.trans_le hM
  have hint := integrableOn_truncSinDeriv_mul_inv t (M := M)
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ico 1 M) :=
    Set.disjoint_left.2 fun x h1 h2 => (not_le.2 h1.2) h2.1
  rw [← Ioo_union_Ico_eq_Ioo one_pos hM, setIntegral_union hdisj measurableSet_Ico
    (hint.mono_set (Ioo_subset_Ioo_right hM)) (hint.mono_set fun x hx => ⟨by linarith [hx.1], hx.2⟩)]
  have h1 : ∫ u in Ioo 0 1, truncSinDeriv t u * u⁻¹ =
      ∫ u in Ioo 0 1, t * t * ((cos (t * u) - 1) / (t * u)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    simp only [truncSinDeriv]
    rw [indicator_of_mem (show u ∈ Iio (1 : ℝ) from hu.2)]
    have := hu.1.ne'
    field_simp
  have h2 : ∫ u in Ico 1 M, truncSinDeriv t u * u⁻¹ =
      ∫ u in Ico 1 M, t * t * (cos (t * u) / (t * u)) := by
    refine setIntegral_congr_fun measurableSet_Ico fun u hu => ?_
    simp only [truncSinDeriv]
    rw [indicator_of_notMem (show u ∉ Iio (1 : ℝ) from not_lt.2 hu.1), sub_zero]
    have : u ≠ 0 := by linarith [hu.1]
    field_simp
  rw [h1, h2, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le hM, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun v => (cos v - 1) / v) ht.ne',
    intervalIntegral.integral_comp_mul_left (fun v => cos v / v) ht.ne', mul_zero, mul_one,
    smul_eq_mul, smul_eq_mul]
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_cos_sub_one_div 0 1) (intervalIntegrable_cos_sub_one_div 1 t)
  have h4 : ∫ v in (1 : ℝ)..t, (cos v - 1) / v = (∫ v in (1 : ℝ)..t, cos v / v) - log t := by
    have e : ∫ v in (1 : ℝ)..t, (cos v - 1) / v = ∫ v in (1 : ℝ)..t, (cos v / v - v⁻¹) :=
      intervalIntegral.integral_congr fun v _ => by rw [sub_div, one_div]
    rw [e, intervalIntegral.integral_sub (intervalIntegrable_cos_div one_pos ht)
      (intervalIntegrable_inv' one_pos ht), integral_inv_of_pos one_pos ht, div_one]
  have h5 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_cos_div one_pos ht) (intervalIntegrable_cos_div ht (mul_pos ht hM0))
  rw [← h3, h4, ← h5]
  field_simp
  ring

/-- For `t > 0`: `∫₀^M g_t(u) / u du → t (cosLogConst - log t)` as `M → ∞`. -/
theorem tendsto_setIntegral_truncSinDeriv_mul_inv_of_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun M => ∫ u in Ioo 0 M, truncSinDeriv t u * u⁻¹) atTop
      (𝓝 (t * (cosLogConst - log t))) := by
  have h := ((tendsto_const_nhds (x := ∫ v in (0 : ℝ)..1, (cos v - 1) / v)).add
    (tendsto_intervalIntegral_cos_div.comp (tendsto_id.const_mul_atTop ht))).sub_const (log t)
    |>.const_mul t
  rw [show t * ((∫ v in (0 : ℝ)..1, (cos v - 1) / v) +
      (-sin 1 + ∫ v in Ioi (1 : ℝ), sin v / v ^ 2) - log t) = t * (cosLogConst - log t) by
    rw [cosLogConst]; ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [setIntegral_truncSinDeriv_mul_inv ht hM]
  rfl

/-- **The improper integral**: `∫₀^M (t cos (t u) - t 1{u < 1}) / u du → t (cosLogConst - log |t|)`
as `M → ∞`, for every `t`. -/
theorem tendsto_setIntegral_truncSinDeriv_mul_inv (t : ℝ) :
    Tendsto (fun M => ∫ u in Ioo 0 M, truncSinDeriv t u * u⁻¹) atTop
      (𝓝 (t * (cosLogConst - log |t|))) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := (tendsto_setIntegral_truncSinDeriv_mul_inv_of_pos (neg_pos.2 ht)).neg
    rw [abs_of_neg ht]
    convert h using 1
    · funext M
      rw [← integral_neg]
      congr 1; funext u
      rw [truncSinDeriv_neg]; ring
    · congr 1; ring
  · have : ∀ u, truncSinDeriv 0 u = 0 := fun u => by
      simp [truncSinDeriv]
    simp [this]
  · rw [abs_of_pos ht]
    exact tendsto_setIntegral_truncSinDeriv_mul_inv_of_pos ht

/-- `Q_t(v) = sin (t v) - t clamp(v, -1, 1)`: continuous, odd, and equal to
`sin (t v) - t min (v, 1)` for `v ≥ 0`. -/
noncomputable def clampSin (t v : ℝ) : ℝ := sin (t * v) - t * max (min v 1) (-1)

theorem continuous_clampSin (t : ℝ) : Continuous (clampSin t) :=
  (continuous_sin.comp (continuous_const.mul continuous_id)).sub
    (continuous_const.mul ((continuous_id.min continuous_const).max continuous_const))

theorem clampSin_neg (t v : ℝ) : clampSin t (-v) = -clampSin t v := by
  have h : max (min (-v) 1) (-1) = -max (min v 1) (-1) := by
    simp only [max_def, min_def]; split_ifs <;> linarith
  rw [clampSin, clampSin, h, mul_neg, sin_neg]; ring

theorem abs_clampSin_le (t v : ℝ) : |clampSin t v| ≤ 1 + |t| := by
  have h : |max (min v 1) (-1)| ≤ 1 :=
    abs_le.2 ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩
  unfold clampSin
  calc _ ≤ |sin (t * v)| + |t * max (min v 1) (-1)| := abs_sub _ _
    _ ≤ 1 + |t| * 1 := by
        rw [abs_mul]
        exact add_le_add (abs_sin_le_one _) (mul_le_mul_of_nonneg_left h (abs_nonneg _))
    _ = _ := by ring

end StableIntegral

section StableExponentOne

/-- The exponent `ψ(t) = -c |t| + i e (κ t - t log |t|)` of a `1`-stable characteristic function
(the `α = 1` parametrization of [ST, Definition 1.1.6]: `c = σ`, `e = (2 / π) σ β`, up to the
location term `κ`). -/
noncomputable def stableExponentOne (c e κ t : ℝ) : ℂ :=
  ((-(c * |t|) : ℝ) : ℂ) + ((e * (κ * t - t * Real.log |t|) : ℝ) : ℂ) * Complex.I

/-- `HasStableOneCharFun c e κ μ`: `μ` is a probability measure with characteristic function
`t ↦ exp (-c |t| + i e (κ t - t log |t|))`. -/
def HasStableOneCharFun (c e κ : ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t, charFun μ t = Complex.exp (stableExponentOne c e κ t)

theorem continuous_stableExponentOne (c e κ : ℝ) : Continuous (stableExponentOne c e κ) := by
  have h : stableExponentOne c e κ = fun t => ((-(c * |t|) : ℝ) : ℂ) +
      ((e * (κ * t - t * Real.log t) : ℝ) : ℂ) * Complex.I := by
    funext t; simp only [stableExponentOne, Real.log_abs]
  rw [h]
  have h1 : Continuous fun t : ℝ => e * (κ * t - t * Real.log t) :=
    continuous_const.mul ((continuous_const.mul continuous_id).sub Real.continuous_mul_log)
  exact (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun t : ℝ => -(c * |t|))).add
    ((Complex.continuous_ofReal.comp h1).mul continuous_const)

end StableExponentOne

namespace GCLT

open StableIntegral

section OneSided

theorem setIntegral_truncSinDeriv (t w : ℝ) :
    ∫ u in Ioo 0 w, truncSinDeriv t u = clampSin t (max w 0) := by
  have h1 : IntegrableOn (fun u : ℝ => t * cos (t * u)) (Ioo 0 w) :=
    (by fun_prop : Continuous fun u : ℝ => t * cos (t * u)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have h2 : IntegrableOn ((Iio (1 : ℝ)).indicator fun _ => t) (Ioo 0 w) :=
    Measure.integrableOn_of_bounded (M := |t|) measure_Ioo_lt_top.ne
      (measurable_const.indicator measurableSet_Iio).aestronglyMeasurable
      (ae_of_all _ fun u => (norm_indicator_le_norm_self (fun _ => t) u).trans_eq
        (Real.norm_eq_abs t))
  have hc : ∫ u in Ioo 0 w, t * cos (t * u) = sin (t * max w 0) := by
    rw [setIntegral_Ioo_eq_sub (hasDerivAt_sin_mul t) (by fun_prop) w]; simp
  have hi : ∫ u in Ioo 0 w, (Iio (1 : ℝ)).indicator (fun _ => t) u = t * max (min w 1) 0 := by
    rw [setIntegral_indicator measurableSet_Iio, Ioo_inter_Iio, setIntegral_const,
      Real.volume_real_Ioo, smul_eq_mul, sub_zero, mul_comm]
  have hm : max (min w 1) 0 = max (min (max w 0) 1) (-1) := by
    simp only [max_def, min_def]; split_ifs <;> linarith
  unfold truncSinDeriv
  rw [integral_sub h1 h2, hc, hi, hm, clampSin]

/-- **Truncation error**: for `M ≥ 1`, replacing `max (x / a) 0` by `max (min (x / a) M) 0` in
`Q_t` costs at most `2 ν (a M, ∞)`. -/
theorem abs_integral_clampSin_sub_le {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ) {a M : ℝ}
    (ha : 0 < a) (hM : 1 ≤ M) :
    |∫ x, clampSin t (max (x / a) 0) ∂ν - ∫ x, clampSin t (max (min (x / a) M) 0) ∂ν| ≤
      2 * ν.real (Ioi (a * M)) := by
  have hi : ∀ f : ℝ → ℝ, Continuous f → Integrable (fun x => clampSin t (f x)) ν := fun f hf =>
    Integrable.of_bound ((continuous_clampSin t).comp hf).aestronglyMeasurable (1 + |t|)
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_clampSin_le t _))
  have hs : ∀ f : ℝ → ℝ, Continuous f → Integrable (fun x => sin (t * f x)) ν := fun f hf =>
    Integrable.of_bound (by fun_prop) 1
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_sin_le_one _))
  have hpt : ∀ x, clampSin t (max (x / a) 0) - clampSin t (max (min (x / a) M) 0) =
      sin (t * max (x / a) 0) - sin (t * max (min (x / a) M) 0) := by
    intro x
    have : max (min (max (x / a) 0) 1) (-1) = max (min (max (min (x / a) M) 0) 1) (-1) := by
      simp only [max_def, min_def]; split_ifs <;> linarith
    rw [clampSin, clampSin, this]; ring
  rw [← integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop))]
  simp_rw [hpt]
  rw [integral_sub (hs _ (by fun_prop)) (hs _ (by fun_prop))]
  exact abs_integral_sub_min_le (F := fun v => sin (t * v)) (by fun_prop)
    (fun v => abs_sin_le_one _) ha M

/-- `tendsto_of_approx` with the truncation level restricted to `M ≥ 1`. -/
theorem tendsto_of_approx_of_one_le {L : ℕ → ℝ} {I R : ℝ → ℕ → ℝ} {J r : ℝ → ℝ} {c : ℝ}
    (hLI : ∀ M, 1 ≤ M → ∀ n, |L n - I M n| ≤ R M n)
    (hI : ∀ M, 1 ≤ M → Tendsto (I M) atTop (𝓝 (J M)))
    (hR : ∀ M, 1 ≤ M → Tendsto (R M) atTop (𝓝 (r M)))
    (hJ : Tendsto J atTop (𝓝 c)) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto L atTop (𝓝 c) := by
  have htop : Tendsto (fun M : ℝ => max M 1) atTop atTop :=
    tendsto_atTop_mono (fun M => le_max_left M 1) tendsto_id
  exact tendsto_of_approx (I := fun M => I (max M 1)) (R := fun M => R (max M 1))
    (J := fun M => J (max M 1)) (r := fun M => r (max M 1))
    (fun M _ n => hLI _ (le_max_right _ _) n) (fun M _ => hI _ (le_max_right _ _))
    (fun M _ => hR _ (le_max_right _ _)) (hJ.comp htop) (hr.comp htop)

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ} {a : ℕ → ℝ}

/-- **The one-sided sine part, `α = 1`**: if `P(X > x) / P(|X| > x) → c`, then
`n E Q_t(X⁺ / aₙ) → c t (cosLogConst - log |t|)`. -/
theorem tendsto_mul_integral_clampSin_max (hRV : IsRegularlyVarying (absTail μ) (-1))
    (ha : ∀ n, 0 < a n) (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1))
    (hc : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 c)) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, clampSin t (max (x / a n) 0) ∂μ) atTop
      (𝓝 (c * (t * (cosLogConst - log |t|)))) := by
  set δ : ℝ := 1 / 2 with hδ_def
  have hδ : 0 < δ := by norm_num [hδ_def]
  obtain ⟨K, hK⟩ := eventually_abs_mul_measureReal_Ioi_le one_pos hRV hna hδ
  refine tendsto_of_approx_of_one_le
    (I := fun M n => ∫ u in Ioo 0 M, truncSinDeriv t u * ((n : ℝ) * μ.real (Ioi (a n * u))))
    (R := fun M n => 2 * ((n : ℝ) * μ.real (Ioi (a n * M))))
    (J := fun M => c * ∫ u in Ioo 0 M, truncSinDeriv t u * u ^ (-(1 : ℝ)))
    (r := fun M => 2 * (c * M ^ (-(1 : ℝ)))) ?_ ?_ ?_ ?_ ?_
  · intro M hM n
    have e1 := integral_setIntegral_Ioo_min (ν := μ) (g := truncSinDeriv t)
      (measurable_truncSinDeriv t) (abs_truncSinDeriv_le_two t) (ha n) M
    simp only [setIntegral_truncSinDeriv] at e1
    have e : ∫ u in Ioo 0 M, truncSinDeriv t u * ((n : ℝ) * μ.real (Ioi (a n * u))) =
        (n : ℝ) * ∫ x, clampSin t (max (min (x / a n) M) 0) ∂μ := by
      rw [e1, ← integral_const_mul]; congr 1; funext u; ring
    rw [e, ← mul_sub, abs_mul, Nat.abs_cast]
    have := abs_integral_clampSin_sub_le (ν := μ) t (ha n) hM
    calc _ ≤ (n : ℝ) * (2 * μ.real (Ioi (a n * M))) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
      _ = _ := by ring
  · intro M hM
    have hM0 : 0 < M := one_pos.trans_le hM
    have h1 : IntegrableOn (fun u : ℝ => u ^ (1 - δ)) (Ioo 0 M) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM0.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by rw [hδ_def]; norm_num))).mono_set
          Ioo_subset_Ioc_self
    have h2 : IntegrableOn (fun u : ℝ => u ^ (1 + δ)) (Ioo 0 M) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM0.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by rw [hδ_def]; norm_num))).mono_set
          Ioo_subset_Ioc_self
    refine tendsto_setIntegral_mul_of_le measurableSet_Ioo (fun u hu => hu.1)
      (fun n => (measurable_measureReal_Ioi.comp (measurable_const.mul measurable_id)).const_mul _)
      (measurable_truncSinDeriv t) (fun u hu => tendsto_mul_measureReal_Ioi hRV hna hc hu) hK ?_
    refine ((h1.add h2).const_mul (|t| ^ 3 / 2 + |t|)).mono' (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu.1
    have hp : 0 ≤ u ^ (-1 - δ) + u ^ (-1 + δ) :=
      add_nonneg (rpow_nonneg hu0.le _) (rpow_nonneg hu0.le _)
    have e1 : u ^ 2 * u ^ (-1 - δ) = u ^ (1 - δ) := by
      rw [← rpow_natCast, ← rpow_add hu0]; congr 1; push_cast; ring
    have e2 : u ^ 2 * u ^ (-1 + δ) = u ^ (1 + δ) := by
      rw [← rpow_natCast, ← rpow_add hu0]; congr 1; push_cast; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hp)]
    calc |truncSinDeriv t u| * (u ^ (-1 - δ) + u ^ (-1 + δ))
        ≤ (|t| ^ 3 / 2 + |t|) * u ^ 2 * (u ^ (-1 - δ) + u ^ (-1 + δ)) :=
          mul_le_mul_of_nonneg_right (abs_truncSinDeriv_le t hu0) hp
      _ = (|t| ^ 3 / 2 + |t|) * (u ^ (1 - δ) + u ^ (1 + δ)) := by rw [← e1, ← e2]; ring
  · intro M hM
    exact (tendsto_mul_measureReal_Ioi hRV hna hc (one_pos.trans_le hM)).const_mul 2
  · refine ((tendsto_setIntegral_truncSinDeriv_mul_inv t).const_mul c).congr fun M => ?_
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioo fun u _ => by rw [rpow_neg_one]
  · simpa using ((tendsto_rpow_neg_atTop one_pos).const_mul c).const_mul 2

end OneSided

end GCLT

end ExtremeValueTheory
