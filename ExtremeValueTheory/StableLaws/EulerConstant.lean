/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLTOne
import ExtremeValueTheory.GEV.Moments

/-!
# The constant of the `1`-stable limit is `1 - γ`

The drift constant of the generalized CLT for `α = 1` is
`stableLogConst = 1 + cosLogConst`, `cosLogConst = ∫₀¹ (cos v - 1) / v dv + ∫₁^∞ cos v / v dv`.
We prove the classical value `cosLogConst = -γ`, `γ` the Euler–Mascheroni constant, so
`stableLogConst = 1 - γ`.

## Proof

* `tendsto_integral_exp_neg_trunc`: `∫₀¹ (e^{-v} - 1) / v dv + ∫₁^N e^{-v} / v dv → -γ`, by
  integrating `γ = -∫₀^∞ log t e^{-t} dt` by parts on `[0, 1]` and `[1, N]`.
* `tendsto_integral_cos_sub_exp_neg_div`: `∫₀^N (cos v - e^{-v}) / v dv → 0`. Writing
  `1 / v = ∫₀^∞ e^{-s v} ds` and using Fubini on `(0, N] × (0, ∞)`, the integral equals
  `∫₀^∞ h_N(s) ds` with `h_N(s) = s / (1 + s²) - 1 / (1 + s) + O(e^{-N s})`; by dominated
  convergence it tends to `∫₀^∞ (s / (1 + s²) - 1 / (1 + s)) ds = [log (√(1 + s²) / (1 + s))]₀^∞ = 0`.
* Subtracting, `cosLogConst = -γ`.

## Main results

* `StableIntegral.cosLogConst_eq`: `cosLogConst = -γ`.
* `StableIntegral.stableLogConst_eq`: `stableLogConst = 1 - γ`.
* `tendsto_map_convPow_sub_of_isRegularlyVarying_one_eulerMascheroni`: the generalized CLT for
  `α = 1` with characteristic function `exp (-(π/2) |t| + i (2p - 1) ((1 - γ) t - t log |t|))`.
-/

open MeasureTheory Filter Topology Set Real

namespace ExtremeValueTheory

namespace StableIntegral

/-! ### The exponential integral side -/

theorem one_sub_exp_neg_le (v : ℝ) : 1 - exp (-v) ≤ v := by linarith [add_one_le_exp (-v)]

theorem abs_exp_neg_sub_one_div_le {v : ℝ} (hv : 0 ≤ v) : |(exp (-v) - 1) / v| ≤ 1 := by
  rcases hv.eq_or_lt with rfl | hv
  · simp
  rw [abs_div, abs_of_pos hv, div_le_one hv, abs_sub_comm,
    abs_of_nonneg (by linarith [exp_le_one_iff.2 (neg_nonpos.2 hv.le)])]
  exact one_sub_exp_neg_le v

theorem intervalIntegrable_exp_neg_sub_one_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun v : ℝ => (exp (-v) - 1) / v) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ((by fun_prop : Measurable fun v : ℝ => exp (-v) - 1).div measurable_id).aestronglyMeasurable
    ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun v hv => ?_
  rw [Real.norm_eq_abs]
  exact abs_exp_neg_sub_one_div_le ((le_min ha hb).trans hv.1.le)

theorem intervalIntegrable_log_mul_exp_neg (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => log t * exp (-t)) volume a b :=
  intervalIntegral.intervalIntegrable_log'.mul_continuousOn (by fun_prop)

/-- Integration by parts on `[0, 1]`: `∫₀¹ (e^{-t} - 1) / t dt = ∫₀¹ log t e^{-t} dt`. -/
theorem integral_exp_neg_sub_one_div_eq :
    ∫ t in (0 : ℝ)..1, (exp (-t) - 1) / t = ∫ t in (0 : ℝ)..1, log t * exp (-t) := by
  set K : ℝ → ℝ := fun t => log t * (1 - exp (-t))
  have hK0 : ContinuousWithinAt K (Icc 0 1) 0 := by
    have hml : Tendsto (fun t : ℝ => t * log t) (𝓝 0) (𝓝 0) := by
      simpa using Real.continuous_mul_log.tendsto 0
    have : Tendsto K (𝓝[Icc 0 1] 0) (𝓝 0) := by
      have hml' : Tendsto (fun t : ℝ => ‖t * log t‖) (𝓝[Icc 0 1] 0) (𝓝 0) := by
        simpa using (hml.mono_left (nhdsWithin_le_nhds (s := Icc (0 : ℝ) 1))).norm
      refine squeeze_zero_norm' ?_ hml'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 : 0 ≤ 1 - exp (-t) := by linarith [exp_le_one_iff.2 (neg_nonpos.2 ht.1)]
      simp only [K, norm_mul, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg ht.1]
      rw [mul_comm t]
      exact mul_le_mul_of_nonneg_left (one_sub_exp_neg_le t) (abs_nonneg _)
    simpa [ContinuousWithinAt, K] using this
  have hcont : ContinuousOn K (Icc 0 1) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · exact hK0
    · exact ((continuousAt_log ht0.ne').mul (by fun_prop)).continuousWithinAt
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt K (-((exp (-t) - 1) / t) + log t * exp (-t)) t := by
    intro t ht
    have h1 := (hasDerivAt_log ht.1.ne').mul (((hasDerivAt_neg t).exp).const_sub 1)
    convert h1 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun t => -((exp (-t) - 1) / t) + log t * exp (-t)) volume 0 1 :=
    (intervalIntegrable_exp_neg_sub_one_div le_rfl zero_le_one).neg.add
      (intervalIntegrable_log_mul_exp_neg 0 1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [intervalIntegral.integral_add (f := fun t => -((exp (-t) - 1) / t))
    (g := fun t => log t * exp (-t))
    (intervalIntegrable_exp_neg_sub_one_div le_rfl zero_le_one).neg
    (intervalIntegrable_log_mul_exp_neg 0 1), intervalIntegral.integral_neg] at h
  simp only [K, log_one, zero_mul, log_zero, sub_zero] at h
  linarith

/-- Integration by parts on `[1, N]`:
`∫₁^N e^{-t} / t dt = ∫₁^N log t e^{-t} dt + log N e^{-N}`. -/
theorem integral_exp_neg_div_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ t in (1 : ℝ)..N, exp (-t) / t = (∫ t in (1 : ℝ)..N, log t * exp (-t)) + log N * exp (-N) := by
  set L : ℝ → ℝ := fun t => -(log t * exp (-t))
  have hpos : ∀ t ∈ Icc (1 : ℝ) N, 0 < t := fun t ht => one_pos.trans_le ht.1
  have hcont : ContinuousOn L (Icc 1 N) := fun t ht =>
    ((continuousAt_log (hpos t ht).ne').mul (by fun_prop)).neg.continuousWithinAt
  have hderiv : ∀ t ∈ Ioo (1 : ℝ) N,
      HasDerivAt L (-(exp (-t) / t) + log t * exp (-t)) t := by
    intro t ht
    have h1 := ((hasDerivAt_log (one_pos.trans ht.1).ne').mul ((hasDerivAt_neg t).exp)).neg
    convert h1 using 1
    field_simp
    ring
  have hc1 : ContinuousOn (fun t : ℝ => exp (-t) / t) (uIcc 1 N) := by
    rw [uIcc_of_le hN]
    exact fun t ht => ((by fun_prop : Continuous fun t : ℝ => exp (-t)).continuousAt.div
      continuousAt_id (hpos t ht).ne').continuousWithinAt
  have hint : IntervalIntegrable (fun t => -(exp (-t) / t) + log t * exp (-t)) volume 1 N :=
    hc1.intervalIntegrable.neg.add (intervalIntegrable_log_mul_exp_neg 1 N)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hN hcont hderiv hint
  rw [intervalIntegral.integral_add (f := fun t => -(exp (-t) / t))
    (g := fun t => log t * exp (-t)) hc1.intervalIntegrable.neg
    (intervalIntegrable_log_mul_exp_neg 1 N), intervalIntegral.integral_neg] at h
  simp only [L, log_one, zero_mul, neg_zero, sub_zero] at h
  linarith

/-- `∫₀¹ (e^{-v} - 1) / v dv + ∫₁^N e^{-v} / v dv → -γ`. -/
theorem tendsto_integral_exp_neg_trunc :
    Tendsto (fun N : ℝ => (∫ v in (0 : ℝ)..1, (exp (-v) - 1) / v) +
      ∫ v in (1 : ℝ)..N, exp (-v) / v) atTop (𝓝 (-eulerMascheroniConstant)) := by
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 integrableOn_log_mul_exp_neg tendsto_id
  have h2 : Tendsto (fun N : ℝ => log N * exp (-N)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun N : ℝ => N * exp (-N)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' ?_ ?_ h3
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact mul_nonneg (log_nonneg hN) (exp_pos _).le
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact mul_le_mul_of_nonneg_right ((log_le_sub_one_of_pos (one_pos.trans_le hN)).trans
        (by linarith)) (exp_pos _).le
  have := h1.add h2
  rw [add_zero] at this
  rw [eulerMascheroniConstant_eq_neg_integral_log, neg_neg]
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [id]
  rw [integral_exp_neg_div_eq hN, integral_exp_neg_sub_one_div_eq, ← add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_log_mul_exp_neg 0 1)
        (intervalIntegrable_log_mul_exp_neg 1 N)]

/-! ### The cosine side: `∫₀^N (cos v - e^{-v}) / v dv → 0` -/

theorem abs_cos_sub_exp_neg_div_le {v : ℝ} (hv : 0 < v) :
    |(cos v - exp (-v)) / v| ≤ v / 2 + 1 := by
  have h1 := abs_cos_sub_one_div_le v
  have h2 := abs_exp_neg_sub_one_div_le hv.le
  have : (cos v - exp (-v)) / v = (cos v - 1) / v - (exp (-v) - 1) / v := by ring
  rw [this]
  calc _ ≤ |(cos v - 1) / v| + |(exp (-v) - 1) / v| := abs_sub _ _
    _ ≤ |v| / 2 + 1 := add_le_add h1 h2
    _ = v / 2 + 1 := by rw [abs_of_pos hv]

/-- `1 / v = ∫₀^∞ e^{-v s} ds`. -/
theorem integral_exp_neg_mul_Ioi_inv {v : ℝ} (hv : 0 < v) :
    ∫ s in Ioi (0 : ℝ), exp (-v * s) = v⁻¹ := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hv) 0]
  simp

/-- The antiderivative in `v` of `(cos v - e^{-v}) e^{-v s}`. -/
theorem hasDerivAt_cosExpAntideriv {s : ℝ} (hs : 0 ≤ s) (v : ℝ) :
    HasDerivAt (fun v => exp (-v * s) * (sin v - s * cos v) / (1 + s ^ 2) +
      exp (-v * s - v) / (1 + s)) ((cos v - exp (-v)) * exp (-v * s)) v := by
  have h1 : HasDerivAt (fun v => exp (-v * s)) (exp (-v * s) * (-1 * s)) v :=
    ((hasDerivAt_neg v).mul_const s).exp
  have h2 : HasDerivAt (fun v => sin v - s * cos v) (cos v - s * -sin v) v :=
    (hasDerivAt_sin v).sub ((hasDerivAt_cos v).const_mul s)
  have h3 : HasDerivAt (fun v => exp (-v * s - v)) (exp (-v * s - v) * (-1 * s - 1)) v :=
    (((hasDerivAt_neg v).mul_const s).sub (hasDerivAt_id' v)).exp
  have h := ((h1.mul h2).div_const (1 + s ^ 2)).add (h3.div_const (1 + s))
  convert h using 1
  have hs1 : (1 + s ^ 2) ≠ 0 := by positivity
  have hs2 : (1 + s) ≠ 0 := by positivity
  rw [show exp (-v * s - v) = exp (-v) * exp (-v * s) by rw [← exp_add]; ring_nf]
  field_simp
  ring

/-- The inner integral `∫₀^N (cos v - e^{-v}) e^{-v s} dv` in closed form. -/
theorem integral_cos_sub_exp_neg_mul_exp {s N : ℝ} (hs : 0 ≤ s) (hN : 0 ≤ N) :
    ∫ v in Ioc 0 N, (cos v - exp (-v)) * exp (-v * s) =
      (exp (-N * s) * (sin N - s * cos N) / (1 + s ^ 2) + exp (-N * s - N) / (1 + s)) +
        (s / (1 + s ^ 2) - 1 / (1 + s)) := by
  rw [← intervalIntegral.integral_of_le hN,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_cosExpAntideriv hs v)
      ((by fun_prop : Continuous fun v : ℝ => (cos v - exp (-v)) * exp (-v * s)).intervalIntegrable
        _ _)]
  simp only [neg_zero, zero_mul, exp_zero, sin_zero, cos_zero, sub_zero, one_mul, mul_one]
  ring

/-- The remainder bound `|R_N(s)| ≤ 3 e^{-N s}`. -/
theorem abs_cosExpRemainder_le {s N : ℝ} (hs : 0 ≤ s) (hN : 0 ≤ N) :
    |exp (-N * s) * (sin N - s * cos N) / (1 + s ^ 2) + exp (-N * s - N) / (1 + s)| ≤
      3 * exp (-N * s) := by
  have hs1 : 0 < 1 + s ^ 2 := by positivity
  have hs2 : 0 < 1 + s := by positivity
  have he := exp_pos (-N * s)
  have hA : |sin N - s * cos N| ≤ 1 + s := by
    calc _ ≤ |sin N| + |s * cos N| := abs_sub _ _
      _ ≤ 1 + s * 1 := by
          rw [abs_mul, abs_of_nonneg hs]
          exact add_le_add (abs_sin_le_one N) (mul_le_mul_of_nonneg_left (abs_cos_le_one N) hs)
      _ = 1 + s := by ring
  have h1 : |exp (-N * s) * (sin N - s * cos N) / (1 + s ^ 2)| ≤ 2 * exp (-N * s) := by
    rw [abs_div, abs_mul, abs_of_pos he, abs_of_pos hs1, div_le_iff₀ hs1]
    have : 1 + s ≤ 2 * (1 + s ^ 2) := by nlinarith [sq_nonneg (s - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hA he.le]
  have h2 : |exp (-N * s - N) / (1 + s)| ≤ exp (-N * s) := by
    rw [abs_div, abs_of_pos (exp_pos _), abs_of_pos hs2, div_le_iff₀ hs2]
    have : exp (-N * s - N) ≤ exp (-N * s) := exp_le_exp.2 (by linarith)
    nlinarith
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * exp (-N * s) + exp (-N * s) := add_le_add h1 h2
    _ = _ := by ring

theorem abs_cosExpLimit_le {s : ℝ} (hs : 0 ≤ s) :
    |s / (1 + s ^ 2) - 1 / (1 + s)| ≤ (1 + s ^ 2)⁻¹ := by
  have hs1 : 0 < 1 + s ^ 2 := by positivity
  have hs2 : 0 < 1 + s := by positivity
  have : s / (1 + s ^ 2) - 1 / (1 + s) = (s - 1) / ((1 + s ^ 2) * (1 + s)) := by
    field_simp; ring
  rw [this, abs_div, abs_of_pos (mul_pos hs1 hs2), div_le_iff₀ (mul_pos hs1 hs2),
    inv_mul_cancel_left₀ hs1.ne']
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem integrableOn_cosExpLimit :
    IntegrableOn (fun s : ℝ => s / (1 + s ^ 2) - 1 / (1 + s)) (Ioi 0) := by
  refine integrable_inv_one_add_sq.integrableOn.mono' (by fun_prop) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun s hs => by
    rw [Real.norm_eq_abs]; exact abs_cosExpLimit_le (le_of_lt hs)

/-- `∫₀^∞ (s / (1 + s²) - 1 / (1 + s)) ds = 0`. -/
theorem integral_cosExpLimit :
    ∫ s in Ioi (0 : ℝ), (s / (1 + s ^ 2) - 1 / (1 + s)) = 0 := by
  set F : ℝ → ℝ := fun s => log (1 + s ^ 2) / 2 - log (1 + s)
  have hcont : ContinuousWithinAt F (Ici 0) 0 :=
    (((continuousAt_log (by norm_num)).comp (by fun_prop : ContinuousAt
      (fun s : ℝ => 1 + s ^ 2) 0)).div_const 2 |>.sub
      ((continuousAt_log (by norm_num)).comp (by fun_prop : ContinuousAt
        (fun s : ℝ => 1 + s) 0))).continuousWithinAt
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt F (s / (1 + s ^ 2) - 1 / (1 + s)) s := by
    intro s hs
    have hs : (0 : ℝ) < s := hs
    have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
      simpa using ((hasDerivAt_pow 2 s).const_add 1)
    have h2 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := by
      simpa using (hasDerivAt_id' s).const_add 1
    have h := ((h1.log (by positivity)).div_const 2).sub (h2.log (by positivity))
    convert h using 1
    field_simp
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hq : Tendsto (fun s : ℝ => 2 * s / (1 + s) ^ 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun s : ℝ => 2 / (1 + s)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_id)
      refine squeeze_zero' ?_ ?_ h0
      · filter_upwards [eventually_ge_atTop 0] with s hs; positivity
      · filter_upwards [eventually_ge_atTop 0] with s hs
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    have hr : Tendsto (fun s : ℝ => 1 - 2 * s / (1 + s) ^ 2) atTop (𝓝 1) := by
      simpa using hq.const_sub 1
    have hl := ((continuousAt_log one_ne_zero).tendsto.comp hr).div_const 2
    rw [log_one, zero_div] at hl
    refine hl.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    have h1 : 1 - 2 * s / (1 + s) ^ 2 = (1 + s ^ 2) / (1 + s) ^ 2 := by
      field_simp; ring
    simp only [Function.comp, F, h1]
    rw [log_div (by positivity) (by positivity), log_pow]
    push_cast
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv integrableOn_cosExpLimit hlim
  rw [h]
  simp [F]

/-- **`∫₀^N (cos v - e^{-v}) / v dv → 0`** (Fubini with `1 / v = ∫₀^∞ e^{-v s} ds`, then
dominated convergence). -/
theorem tendsto_integral_cos_sub_exp_neg_div :
    Tendsto (fun N : ℝ => ∫ v in (0 : ℝ)..N, (cos v - exp (-v)) / v) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun s => s / (1 + s ^ 2) - 1 / (1 + s)
  set H : ℝ → ℝ → ℝ := fun N s =>
    (exp (-N * s) * (sin N - s * cos N) / (1 + s ^ 2) + exp (-N * s - N) / (1 + s)) + g s
  -- Fubini
  have hfub : ∀ N : ℝ, 0 ≤ N →
      ∫ v in (0 : ℝ)..N, (cos v - exp (-v)) / v = ∫ s in Ioi (0 : ℝ), H N s := by
    intro N hN
    have hcontF : Continuous fun p : ℝ × ℝ => (cos p.1 - exp (-p.1)) * exp (-p.1 * p.2) := by
      fun_prop
    have hint : Integrable (Function.uncurry fun v s : ℝ => (cos v - exp (-v)) * exp (-v * s))
        ((volume.restrict (Ioc 0 N)).prod (volume.restrict (Ioi 0))) := by
      refine (integrable_prod_iff hcontF.aestronglyMeasurable).2 ?_
      refine ⟨?_, ?_⟩
      · rw [ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall fun v hv =>
          (integrableOn_exp_mul_Ioi (neg_neg_of_pos hv.1) 0).const_mul (cos v - exp (-v))
      · have hb : IntegrableOn (fun v : ℝ => |(cos v - exp (-v)) / v|) (Ioc 0 N) := by
          refine Measure.integrableOn_of_bounded (M := N / 2 + 1) measure_Ioc_lt_top.ne
            (continuous_abs.measurable.comp ((by fun_prop : Measurable fun v : ℝ =>
              cos v - exp (-v)).div measurable_id)).aestronglyMeasurable ?_
          rw [ae_restrict_iff' measurableSet_Ioc]
          refine Eventually.of_forall fun v hv => ?_
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_cos_sub_exp_neg_div_le hv.1).trans (by linarith [hv.2])
        refine hb.congr ?_
        rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun v hv => ?_
        simp only [norm_mul, Real.norm_eq_abs,
          abs_of_pos (exp_pos _)]
        rw [integral_const_mul, integral_exp_neg_mul_Ioi_inv hv.1, abs_div, abs_of_pos hv.1,
          div_eq_mul_inv]
    rw [intervalIntegral.integral_of_le hN]
    calc ∫ v in Ioc 0 N, (cos v - exp (-v)) / v
        = ∫ v in Ioc 0 N, ∫ s in Ioi 0, (cos v - exp (-v)) * exp (-v * s) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
          rw [integral_const_mul, integral_exp_neg_mul_Ioi_inv hv.1, div_eq_mul_inv]
      _ = ∫ s in Ioi 0, ∫ v in Ioc 0 N, (cos v - exp (-v)) * exp (-v * s) :=
          integral_integral_swap hint
      _ = ∫ s in Ioi 0, H N s := by
          refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
          exact integral_cos_sub_exp_neg_mul_exp (le_of_lt hs) hN
  -- dominated convergence
  have hdct : Tendsto (fun N => ∫ s in Ioi (0 : ℝ), H N s) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), g s)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => 3 * exp (-s) + (1 + s ^ 2)⁻¹) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun N => (by fun_prop : Measurable (H N)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with N hN
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun s (hs : 0 < s) => ?_
      rw [Real.norm_eq_abs]
      have h1 := abs_cosExpRemainder_le hs.le (zero_le_one.trans hN)
      have h2 := abs_cosExpLimit_le hs.le
      have h3 : exp (-N * s) ≤ exp (-s) := exp_le_exp.2 (by nlinarith)
      calc |H N s| ≤ _ := abs_add_le _ _
        _ ≤ 3 * exp (-N * s) + (1 + s ^ 2)⁻¹ := add_le_add h1 h2
        _ ≤ _ := by linarith
    · exact ((integrableOn_exp_neg_Ioi 0).const_mul 3).add integrable_inv_one_add_sq.integrableOn
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun s (hs : 0 < s) => ?_
      have he : Tendsto (fun N : ℝ => exp (-N * s)) atTop (𝓝 0) := by
        have : Tendsto (fun N : ℝ => -N * s) atTop atBot := by
          exact (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hs)).congr fun N => by simp [neg_mul]
        exact tendsto_exp_atBot.comp this
      have hR : Tendsto (fun N : ℝ => exp (-N * s) * (sin N - s * cos N) / (1 + s ^ 2) +
          exp (-N * s - N) / (1 + s)) atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ (by simpa only [mul_zero] using he.const_mul 3)
        filter_upwards [eventually_ge_atTop 0] with N hN
        rw [Real.norm_eq_abs]
        exact abs_cosExpRemainder_le hs.le hN
      simpa [H] using hR.add_const (g s)
  rw [integral_cosExpLimit] at hdct
  refine hdct.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with N hN
  exact (hfub N hN).symm

/-! ### The value of the constants -/

theorem intervalIntegrable_exp_neg_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun v : ℝ => exp (-v) / v) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ?_
  have hx0 : 0 < x := lt_of_lt_of_le (lt_min ha hb) hx.1
  exact ((by fun_prop : Continuous fun v : ℝ => exp (-v)).continuousAt.div continuousAt_id
    hx0.ne').continuousWithinAt

/-- **`∫₀¹ (cos v - 1) / v dv + ∫₁^∞ cos v / v dv = -γ`** (the cosine integral `Ci(1)` identity
`-γ = ∫₀¹ (cos v - 1) / v dv - Ci(1)`). -/
theorem cosLogConst_eq : cosLogConst = -eulerMascheroniConstant := by
  have hC : Tendsto (fun N : ℝ => (∫ v in (0 : ℝ)..1, (cos v - 1) / v) +
      ∫ v in (1 : ℝ)..N, cos v / v) atTop (𝓝 cosLogConst) := by
    have := tendsto_intervalIntegral_cos_div.const_add (∫ v in (0 : ℝ)..1, (cos v - 1) / v)
    rw [cosLogConst]
    convert this using 2
    ring
  have h := hC.sub tendsto_integral_exp_neg_trunc
  have heq : ∀ N : ℝ, 1 ≤ N →
      ((∫ v in (0 : ℝ)..1, (cos v - 1) / v) + ∫ v in (1 : ℝ)..N, cos v / v) -
        ((∫ v in (0 : ℝ)..1, (exp (-v) - 1) / v) + ∫ v in (1 : ℝ)..N, exp (-v) / v) =
      ∫ v in (0 : ℝ)..N, (cos v - exp (-v)) / v := by
    intro N hN
    have hN0 : 0 < N := one_pos.trans_le hN
    have i1 := intervalIntegrable_cos_sub_one_div 0 1
    have i2 := intervalIntegrable_exp_neg_sub_one_div (le_refl (0 : ℝ)) zero_le_one
    have i3 := intervalIntegrable_cos_div one_pos hN0
    have i4 := intervalIntegrable_exp_neg_div one_pos hN0
    have e1 : (∫ v in (0 : ℝ)..1, (cos v - 1) / v) - ∫ v in (0 : ℝ)..1, (exp (-v) - 1) / v =
        ∫ v in (0 : ℝ)..1, (cos v - exp (-v)) / v := by
      rw [← intervalIntegral.integral_sub i1 i2]
      exact intervalIntegral.integral_congr fun v _ => by ring
    have e2 : (∫ v in (1 : ℝ)..N, cos v / v) - ∫ v in (1 : ℝ)..N, exp (-v) / v =
        ∫ v in (1 : ℝ)..N, (cos v - exp (-v)) / v := by
      rw [← intervalIntegral.integral_sub i3 i4]
      exact intervalIntegral.integral_congr fun v _ => by ring
    have j1 : IntervalIntegrable (fun v : ℝ => (cos v - exp (-v)) / v) volume 0 1 :=
      (i1.sub i2).congr fun v _ => by ring
    have j2 : IntervalIntegrable (fun v : ℝ => (cos v - exp (-v)) / v) volume 1 N :=
      (i3.sub i4).congr fun v _ => by ring
    rw [← intervalIntegral.integral_add_adjacent_intervals j1 j2, ← e1, ← e2]
    ring
  have h2 : Tendsto (fun N : ℝ => ∫ v in (0 : ℝ)..N, (cos v - exp (-v)) / v) atTop
      (𝓝 (cosLogConst - -eulerMascheroniConstant)) := by
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact heq N hN
  have := tendsto_nhds_unique h2 tendsto_integral_cos_sub_exp_neg_div
  linarith

/-- **The drift constant of the `1`-stable limit is `1 - γ`**. -/
theorem stableLogConst_eq : stableLogConst = 1 - eulerMascheroniConstant := by
  rw [stableLogConst, cosLogConst_eq]
  ring

end StableIntegral

open GCLT StableIntegral Subexp in
/-- **Generalized central limit theorem, `α = 1`, with the classical constants**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2], [EKM, Theorem 2.2.8]): under the
hypotheses of `tendsto_map_convPow_sub_of_isRegularlyVarying_one`, the limit law has
characteristic function `exp (-(π / 2) |t| + i (2p - 1) ((1 - γ) t - t log |t|))`, `γ` the
Euler–Mascheroni constant. -/
theorem tendsto_map_convPow_sub_of_isRegularlyVarying_one_eulerMascheroni {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {p : ℝ} (hRV : IsRegularlyVarying (absTail μ) (-1))
    (hp : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p))
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) :
    ∃ ν : ProbabilityMeasure ℝ,
      HasStableOneCharFun (Real.pi / 2) (2 * p - 1) (1 - eulerMascheroniConstant)
        (ν : Measure ℝ) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map
          (fun x => (a n)⁻¹ * (x - n * ∫ y in Icc (-a n) (a n), y ∂μ)),
          inferInstance⟩) atTop (𝓝 ν) := by
  rw [← StableIntegral.stableLogConst_eq]
  exact tendsto_map_convPow_sub_of_isRegularlyVarying_one' hRV hp ha hna

end ExtremeValueTheory
