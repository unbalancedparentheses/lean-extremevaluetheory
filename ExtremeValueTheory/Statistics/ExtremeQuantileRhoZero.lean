/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ExtremeQuantileSecondOrder

/-!
# Extreme quantile estimation with second-order index `ρ = 0`

WIP
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### Uniform bounds for the extrapolation remainder -/

namespace IsSecondOrderRegularlyVarying

variable {U A : ℝ → ℝ} {γ ρ : ℝ}

/-- The extrapolation remainder `r(t, x) = log U(xt) - log U(t) - γ log x` is an additive
cocycle: `r(t, xy) = r(t, x) + r(xt, y)`. -/
theorem logRem_mul (U : ℝ → ℝ) (γ : ℝ) {t x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log (U (x * y * t)) - log (U t) - γ * log (x * y) =
      (log (U (x * t)) - log (U t) - γ * log x) +
        (log (U (y * (x * t))) - log (U (x * t)) - γ * log y) := by
  rw [log_mul hx hy, show x * y * t = y * (x * t) by ring]
  ring

/-- Core of `exists_bound_of_le`, for a measurable auxiliary function. -/
theorem exists_bound_of_le_of_measurable (h : IsSecondOrderRegularlyVarying U γ ρ A)
    (hU : Measurable U) (hA : Measurable A) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t ≥ t₀, ∀ x ≥ 1, ∀ a : ℝ, (∀ y ∈ Icc t (x * t), |A y| ≤ a) →
      |log (U (x * t)) - log (U t) - γ * log x| ≤ C * (1 + log x) * a := by
  set G : ℝ → ℝ := fun s => log (U (exp s)) - γ * s with hG
  set a : ℝ → ℝ := fun s => A (exp s) with ha
  have hGm : Measurable G := (hU.comp measurable_exp).log.sub (measurable_id.const_mul γ)
  have hGa : ∀ s u,
      G (s + u) - G s = log (U (exp u * exp s)) - log (U (exp s)) - γ * log (exp u) := by
    intro s u
    simp only [hG, log_exp, ← exp_add, add_comm u s]
    ring
  have hlim : ∀ u, Tendsto (fun s => (G (s + u) - G s) / a s) atTop
      (𝓝 (boxCox ρ (exp u))) := by
    intro u
    refine ((h.tendsto_log (exp_pos u)).comp tendsto_exp_atTop).congr fun s => ?_
    simp only [Function.comp_apply, hGa, ha]
  obtain ⟨x₀, hx₀, hApos, hP⟩ :=
    h.isRegularlyVarying_abs.potter_bound_of_measurable (continuous_abs.measurable.comp hA)
      one_pos one_lt_two
  have hK : ∀ s ≥ log x₀, ∀ ξ ∈ Icc (0 : ℝ) 1, |a (s + ξ)| ≤ 2 * exp 1 * |a s| := by
    intro s hs ξ hξ
    have hxs : x₀ ≤ exp s := (log_le_iff_le_exp hx₀).1 hs
    have hxsv : x₀ ≤ exp (s + ξ) := hxs.trans (exp_le_exp.2 (by linarith [hξ.1]))
    have h1 := hP (exp s) hxs (exp (s + ξ)) hxsv
    have hpos := hApos (exp s) hxs
    rw [div_le_iff₀ hpos] at h1
    have hr : exp (s + ξ) / exp s = exp ξ := by rw [exp_add]; field_simp
    rw [hr] at h1
    have hm : max (exp ξ ^ (ρ + 1)) (exp ξ ^ (ρ - 1)) ≤ exp 1 := by
      rw [← exp_mul, ← exp_mul]
      refine max_le (exp_le_exp.2 ?_) (exp_le_exp.2 ?_) <;> nlinarith [h.nonpos, hξ.1, hξ.2]
    calc |a (s + ξ)| ≤ 2 * max (exp ξ ^ (ρ + 1)) (exp ξ ^ (ρ - 1)) * |a s| := h1
      _ ≤ 2 * exp 1 * |a s| := by gcongr
  have ha0 : ∀ s ≥ log x₀, a s ≠ 0 := fun s hs =>
    abs_pos.1 (hApos _ ((log_le_iff_le_exp hx₀).1 hs))
  have hB : ∀ u ∈ Icc (0 : ℝ) 2, |boxCox ρ (exp u)| < 3 := by
    intro u hu
    obtain ⟨h1, h2⟩ := boxCox_exp_nonneg_le h.nonpos hu.1
    rw [abs_of_nonneg h1]
    linarith [hu.2]
  obtain ⟨S, hS⟩ := exists_abs_sub_le_of_tendsto hGm hlim hB ha0 hK
  set M := 3 * (1 + 2 * exp 1) with hM
  have hM0 : 0 ≤ M := by positivity
  have hiter := abs_sub_le_sum_of_le hM0 (S := max S (log x₀))
    (fun s hs ξ hξ => hS s ((le_max_left _ _).trans hs) ξ hξ)
  refine ⟨M, exp (max S (log x₀)), exp_pos _, fun t ht x hx b hb => ?_⟩
  have ht0 : 0 < t := (exp_pos _).trans_le ht
  have hx0 : 0 < x := one_pos.trans_le hx
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb t ⟨le_rfl, le_mul_of_one_le_left ht0.le hx⟩)
  set s := log t with hs
  set u := log x with hu
  have hsS : max S (log x₀) ≤ s := by rw [hs, le_log_iff_exp_le ht0]; exact ht
  have hu0 : 0 ≤ u := log_nonneg hx
  set m := ⌈u⌉₊ with hm
  have hum : u ≤ m := Nat.le_ceil u
  have hmu : (m : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
  have h1 := hiter m s hsS u ⟨hu0, hum⟩
  have h2 : ∑ j ∈ Finset.range m, |a (s + j)| ≤ m * b := by
    calc ∑ j ∈ Finset.range m, |a (s + j)| ≤ ∑ _j ∈ Finset.range m, b := by
          refine Finset.sum_le_sum fun j hj => hb _ ⟨?_, ?_⟩
          · rw [← exp_log ht0, ← hs]
            exact exp_le_exp.2 (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
          · have hj' : (j : ℝ) < u := Nat.lt_ceil.1 (Finset.mem_range.1 hj)
            rw [← exp_log ht0, ← exp_log hx0, ← hs, ← hu, ← exp_add]
            exact exp_le_exp.2 (by linarith)
      _ = m * b := by simp
  have e1 : G (s + u) - G s = log (U (x * t)) - log (U t) - γ * log x := by
    rw [hGa, hs, hu, exp_log ht0, exp_log hx0]
  rw [← e1]
  calc |G (s + u) - G s| ≤ M * ∑ j ∈ Finset.range m, |a (s + j)| := h1
    _ ≤ M * (m * b) := by gcongr
    _ ≤ M * ((1 + u) * b) := by gcongr; linarith
    _ = M * (1 + log x) * b := by rw [hu]; ring

/-- **Uniform bound for the extrapolation remainder, valid for every `ρ ≤ 0`** (in particular
for `ρ = 0`; compare [dHF, Theorem 2.3.9] and [BGT, Theorem 3.1.16]). If `U` is measurable,
there are `C` and `t₀ > 0` such that for all `t ≥ t₀`, `x ≥ 1` and every bound `a` for `|A|` on
`[t, xt]`,

  `|log U(xt) - log U(t) - γ log x| ≤ C (1 + log x) a`.

For `ρ < 0` the bound `exists_bound_of_neg` is sharper; for `ρ = 0` this is the natural form:
the limit `h_0(x) = log x` grows logarithmically, and `|A|`, being only slowly varying, is
controlled on `[t, xt]` by its supremum there and not by `|A(t)|` alone. -/
theorem exists_bound_of_le (h : IsSecondOrderRegularlyVarying U γ ρ A) (hU : Measurable U) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t ≥ t₀, ∀ x ≥ 1, ∀ a : ℝ, (∀ y ∈ Icc t (x * t), |A y| ≤ a) →
      |log (U (x * t)) - log (U t) - γ * log x| ≤ C * (1 + log x) * a := by
  obtain ⟨B, hBm, h2B, hBA⟩ := h.exists_measurable hU
  obtain ⟨C, t₀, ht₀, hC⟩ := h2B.exists_bound_of_le_of_measurable hU hBm
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 ((hBA.abs.eventually (gt_mem_nhds
    (by norm_num : |(1 : ℝ)| < 2))).and h.eventually_ne_zero)
  refine ⟨2 * C, max t₀ t₁, lt_max_of_lt_left ht₀, fun t ht x hx b hb => ?_⟩
  have h1 := hC t ((le_max_left _ _).trans ht) x hx (2 * b) fun y hy => ?_
  · linarith
  · have hy1 : t₁ ≤ y := (le_max_right _ _).trans (ht.trans hy.1)
    obtain ⟨h3, h4⟩ := ht₁ y hy1
    rw [abs_div, div_lt_iff₀ (abs_pos.2 h4)] at h3
    linarith [hb y hy]

/-- A vanishing extrapolation remainder gives the extrapolation ratio:
if `log U(d t) - log U(t) - γ log d → 0` with `t → ∞`, `d ≥ 1`, then `U(d t) / (U(t) d^γ) → 1`. -/
theorem tendsto_div_mul_rpow_of_tendsto (h : IsSecondOrderRegularlyVarying U γ ρ A)
    {ι : Type*} {l : Filter ι} {t d : ι → ℝ} (ht : Tendsto t l atTop)
    (hd : ∀ᶠ i in l, 1 ≤ d i)
    (hr : Tendsto (fun i => log (U (d i * t i)) - log (U (t i)) - γ * log (d i)) l (𝓝 0)) :
    Tendsto (fun i => U (d i * t i) / (U (t i) * d i ^ γ)) l (𝓝 1) := by
  have hdt : Tendsto (fun i => d i * t i) l atTop := by
    refine tendsto_atTop_mono' l ?_ ht
    filter_upwards [hd, ht.eventually_ge_atTop 0] with i h1 h2
    exact le_mul_of_one_le_left h2 h1
  have := (continuous_exp.tendsto 0).comp hr
  rw [exp_zero] at this
  refine this.congr' ?_
  filter_upwards [ht.eventually h.eventually_pos, hdt.eventually h.eventually_pos, hd]
    with i h1 h2 h3
  have h3' : 0 < d i := one_pos.trans_le h3
  simp only [Function.comp_apply]
  rw [exp_sub, exp_sub, exp_log h1, exp_log h2, rpow_def_of_pos h3', mul_comm (log (d i)),
    div_div]

/-- **Quantile extrapolation for any `ρ ≤ 0`**: if `t → ∞`, `d ≥ 1`, `|A| ≤ a` on `[t, d t]` and
`a (1 + log d) → 0`, then `U(d t) / (U(t) d^γ) → 1`. -/
theorem tendsto_div_mul_rpow_of_le (h : IsSecondOrderRegularlyVarying U γ ρ A)
    (hU : Measurable U) {ι : Type*} {l : Filter ι} {t d a : ι → ℝ} (ht : Tendsto t l atTop)
    (hd : ∀ᶠ i in l, 1 ≤ d i) (ha : ∀ᶠ i in l, ∀ y ∈ Icc (t i) (d i * t i), |A y| ≤ a i)
    (hal : Tendsto (fun i => a i * (1 + log (d i))) l (𝓝 0)) :
    Tendsto (fun i => U (d i * t i) / (U (t i) * d i ^ γ)) l (𝓝 1) := by
  obtain ⟨C, t₀, -, hC⟩ := h.exists_bound_of_le hU
  refine h.tendsto_div_mul_rpow_of_tendsto ht hd ?_
  have hb : Tendsto (fun i => |C| * |a i * (1 + log (d i))|) l (𝓝 0) := by
    simpa using hal.abs.const_mul |C|
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [ht.eventually_ge_atTop t₀, hd, ha] with i h1 h2 h3
  refine (hC (t i) h1 (d i) h2 (a i) h3).trans ?_
  rw [← abs_mul, show C * (1 + log (d i)) * a i = C * (a i * (1 + log (d i))) by ring]
  exact le_abs_self _

/-- Telescoping the extrapolation remainder over unit steps on the logarithmic scale:
`r(t, e^m x) = ∑_{j<m} r(e^j t, e) + r(e^m t, x)`. -/
theorem logRem_exp_nat_mul (U : ℝ → ℝ) (γ : ℝ) (t : ℝ) (m : ℕ) :
    ∀ x : ℝ, x ≠ 0 →
    log (U (exp m * x * t)) - log (U t) - γ * log (exp m * x) =
      ∑ j ∈ Finset.range m,
          (log (U (exp 1 * (exp j * t))) - log (U (exp j * t)) - γ * log (exp 1)) +
        (log (U (x * (exp m * t))) - log (U (exp m * t)) - γ * log x) := by
  induction m with
  | zero =>
    intro x hx
    simp only [CharP.cast_eq_zero, exp_zero, one_mul, Finset.range_zero, Finset.sum_empty,
      zero_add]
  | succ m ih =>
    intro x hx
    have he : exp ((m + 1 : ℕ) : ℝ) = exp m * exp 1 := by push_cast; rw [exp_add]
    have h1 := ih (exp 1 * x) (mul_ne_zero (exp_pos 1).ne' hx)
    have h2 := logRem_mul U γ (t := exp m * t) (x := exp 1) (y := x) (exp_pos 1).ne' hx
    rw [Finset.sum_range_succ, he, show exp m * exp 1 * x * t = exp m * (exp 1 * x) * t by ring,
      show exp m * exp 1 * x = exp m * (exp 1 * x) by ring,
      show exp m * exp 1 * t = exp 1 * (exp m * t) by ring, h1,
      show exp 1 * x * (exp m * t) = exp 1 * x * (exp m * t) from rfl, h2]
    ring

/-- **The extrapolation remainder for `ρ = 0`** ([dHF, Theorem 2.3.9] with `h_0(x) = log x`):
if `t → ∞`, `d → ∞`, and `A` is asymptotically constant on the extrapolation range,
`|A(y) / A(t) - 1| ≤ η → 0` for `y ∈ [t, d t]`, then

  `(log U(d t) - log U(t) - γ log d) / (A(t) log d) → 1`. -/
theorem tendsto_logRem_div_of_rho_eq_zero (h : IsSecondOrderRegularlyVarying U γ 0 A)
    (hU : Measurable U) {ι : Type*} {l : Filter ι} {t d η : ι → ℝ} (ht : Tendsto t l atTop)
    (hd : Tendsto d l atTop) (hη : Tendsto η l (𝓝 0))
    (hA : ∀ᶠ i in l, ∀ y ∈ Icc (t i) (d i * t i), |A y / A (t i) - 1| ≤ η i) :
    Tendsto (fun i => (log (U (d i * t i)) - log (U (t i)) - γ * log (d i)) /
      (A (t i) * log (d i))) l (𝓝 1) := by
  obtain ⟨C, t₀, ht₀, hC⟩ := h.exists_bound_of_le hU
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' := ε / 8 with hε'
  have hε'0 : 0 < ε' := by positivity
  -- unit steps
  have hstep := h.tendsto_log (exp_pos 1)
  rw [boxCox_zero, log_exp] at hstep
  obtain ⟨S, hS⟩ := eventually_atTop.1 ((hstep.eventually (Metric.ball_mem_nhds 1 hε'0)).and
    h.eventually_ne_zero)
  have hlogd : Tendsto (fun i => log (d i)) l atTop := tendsto_log_atTop.comp hd
  set K : ℝ := 8 * (4 * |C| + 1) / ε with hK
  filter_upwards [ht.eventually_ge_atTop (max S t₀), hd.eventually_ge_atTop 1,
    hlogd.eventually_ge_atTop (max K 1), hη.eventually (ge_mem_nhds (lt_min one_pos hε'0)), hA,
    ht.eventually h.eventually_ne_zero] with i hti hdi hui hηi hAi hA0
  have ht0 : 0 < t i := ht₀.trans_le ((le_max_right _ _).trans hti)
  have hd0 : 0 < d i := one_pos.trans_le hdi
  set u := log (d i) with hu
  have hu1 : 1 ≤ u := (le_max_right _ _).trans hui
  have hη1 : η i ≤ 1 := (le_min_iff.1 hηi).1
  have hηε : η i ≤ ε' := (le_min_iff.1 hηi).2
  have hη0 : 0 ≤ η i := by
    have := hAi (t i) ⟨le_rfl, le_mul_of_one_le_left ht0.le hdi⟩
    exact (abs_nonneg _).trans this
  set m := ⌊u⌋₊ with hm
  have hmu : (m : ℝ) ≤ u := Nat.floor_le (by linarith)
  have hum : u < m + 1 := Nat.lt_floor_add_one u
  set x := d i / exp m with hx
  have hxpos : 0 < x := div_pos hd0 (exp_pos _)
  have hdx : exp m * x = d i := by rw [hx]; field_simp
  have hem : exp m ≤ d i := by rw [← exp_log hd0, ← hu]; exact exp_le_exp.2 hmu
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (exp_pos _), one_mul]; exact hem
  have hlogx : log x < 1 := by
    rw [hx, log_div hd0.ne' (exp_pos _).ne', log_exp, ← hu]; linarith
  set At := |A (t i)| with hAt
  have hAt0 : 0 < At := abs_pos.2 hA0
  -- `|A| ≤ (1 + η) |A(t)|` and `|A - A(t)| ≤ η |A(t)|` on `[t, d t]`
  have hAy : ∀ y ∈ Icc (t i) (d i * t i), |A y - A (t i)| ≤ η i * At := by
    intro y hy
    have := hAi y hy
    rw [show A y / A (t i) - 1 = (A y - A (t i)) / A (t i) by field_simp, abs_div,
      div_le_iff₀ hAt0] at this
    exact this
  have hAy' : ∀ y ∈ Icc (t i) (d i * t i), |A y| ≤ (1 + η i) * At := by
    intro y hy
    have := hAy y hy
    have h3 := abs_sub_abs_le_abs_sub (A y) (A (t i))
    rw [← hAt] at h3
    linarith
  -- the telescoping decomposition
  set q : ℕ → ℝ := fun j =>
    log (U (exp 1 * (exp j * t i))) - log (U (exp j * t i)) - γ * log (exp 1) with hq
  set fr := log (U (x * (exp m * t i))) - log (U (exp m * t i)) - γ * log x with hfr_def
  have htel : log (U (d i * t i)) - log (U (t i)) - γ * log (d i) =
      ∑ j ∈ Finset.range m, q j + fr := by
    have := logRem_exp_nat_mul U γ (t i) m x hxpos.ne'
    rw [hdx] at this
    exact this
  clear_value q fr
  -- each unit step
  have hqj : ∀ j ∈ Finset.range m, |q j - A (t i)| ≤ (ε' * (1 + η i) + η i) * At := by
    intro j hj
    have hj' : (j : ℝ) < m := by exact_mod_cast Finset.mem_range.1 hj
    have hσ : exp j * t i ∈ Icc (t i) (d i * t i) := by
      refine ⟨le_mul_of_one_le_left ht0.le (one_le_exp (Nat.cast_nonneg _)), ?_⟩
      refine mul_le_mul_of_nonneg_right ?_ ht0.le
      exact (exp_le_exp.2 hj'.le).trans hem
    have hσS : S ≤ exp j * t i := ((le_max_left _ _).trans hti).trans hσ.1
    obtain ⟨h1, h2⟩ := hS _ hσS
    rw [Real.dist_eq] at h1
    have h1' : |q j - A (exp j * t i)| ≤ ε' * |A (exp j * t i)| := by
      have e : q j - A (exp j * t i) =
          ((log (U (exp 1 * (exp j * t i))) - log (U (exp j * t i)) - γ * 1) /
            A (exp j * t i) - 1) * A (exp j * t i) := by
        simp only [hq, log_exp]; field_simp
      rw [e, abs_mul]
      exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
    have h3 := hAy _ hσ
    have h4 := hAy' _ hσ
    calc |q j - A (t i)| ≤ |q j - A (exp j * t i)| + |A (exp j * t i) - A (t i)| :=
          abs_sub_le _ _ _
      _ ≤ ε' * ((1 + η i) * At) + η i * At := by
          gcongr
          exact h1'.trans (mul_le_mul_of_nonneg_left h4 hε'0.le)
      _ = (ε' * (1 + η i) + η i) * At := by ring
  have hsum : |∑ j ∈ Finset.range m, q j - m * A (t i)| ≤ m * ((ε' * (1 + η i) + η i) * At) := by
    have e : ∑ j ∈ Finset.range m, q j - m * A (t i) = ∑ j ∈ Finset.range m, (q j - A (t i)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hqj).trans ?_
    simp
  -- the fractional step
  have hfr : |fr| ≤ 2 * |C| * ((1 + η i) * At) := by
    have hb := hC (exp m * t i) ((le_max_right _ _).trans (hti.trans
      (le_mul_of_one_le_left ht0.le (one_le_exp (Nat.cast_nonneg _))))) x hx1 ((1 + η i) * At)
      (fun y hy => hAy' y ⟨(le_mul_of_one_le_left ht0.le
        (one_le_exp (Nat.cast_nonneg _))).trans hy.1,
        by rw [← mul_assoc, mul_comm x, hdx] at hy; exact hy.2⟩)
    rw [hfr_def]
    refine hb.trans ?_
    have h0 : 0 ≤ (1 + η i) * At := by positivity
    have h1 : 1 + log x ≤ 2 := by linarith
    have hl0 : 0 ≤ 1 + log x := by linarith [log_nonneg hx1]
    calc C * (1 + log x) * ((1 + η i) * At) ≤ |C| * (1 + log x) * ((1 + η i) * At) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hl0) h0
      _ ≤ |C| * 2 * ((1 + η i) * At) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg C)) h0
      _ = 2 * |C| * ((1 + η i) * At) := by ring
  -- conclusion
  have hA0' : A (t i) * u ≠ 0 := mul_ne_zero hA0 (by linarith)
  have hupos : 0 < u := by linarith
  rw [Real.dist_eq, htel]
  have e : (∑ j ∈ Finset.range m, q j + fr) / (A (t i) * u) - 1 =
      ((∑ j ∈ Finset.range m, q j - m * A (t i)) + fr - (u - m) * A (t i)) / (A (t i) * u) := by
    field_simp
    ring
  rw [e, abs_div, abs_mul, ← hAt, abs_of_pos hupos, div_lt_iff₀ (by positivity)]
  have h5 : |(∑ j ∈ Finset.range m, q j - m * A (t i)) + fr - (u - m) * A (t i)| ≤
      m * ((ε' * (1 + η i) + η i) * At) + 2 * |C| * ((1 + η i) * At) + At := by
    have h6 : |(u - m) * A (t i)| ≤ At := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      calc (u - m) * At ≤ 1 * At := by gcongr; linarith
        _ = At := one_mul _
    calc _ ≤ |(∑ j ∈ Finset.range m, q j - m * A (t i)) + fr| + |(u - m) * A (t i)| :=
          abs_sub _ _
      _ ≤ |∑ j ∈ Finset.range m, q j - m * A (t i)| + |fr| + |(u - m) * A (t i)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by gcongr
  refine h5.trans_lt ?_
  -- `m ≤ u`, `η ≤ ε'`, `η ≤ 1` and `u ≥ K`
  have hKu : K ≤ u := (le_max_left _ _).trans hui
  have hKu' : 8 * (4 * |C| + 1) ≤ ε * u := by
    rw [hK, div_le_iff₀ hε] at hKu; linarith
  have h7 : m * ((ε' * (1 + η i) + η i) * At) ≤ u * ((ε' * 2 + ε') * At) := by
    have hc : ε' * (1 + η i) + η i ≤ ε' * 2 + ε' := by nlinarith
    exact mul_le_mul hmu (mul_le_mul_of_nonneg_right hc hAt0.le) (by positivity) (by linarith)
  have h8 : 2 * |C| * ((1 + η i) * At) + At ≤ (4 * |C| + 1) * At := by
    have : 2 * |C| * (1 + η i) ≤ 4 * |C| := by nlinarith [abs_nonneg C]
    nlinarith [mul_le_mul_of_nonneg_right this hAt0.le]
  have h9 : (4 * |C| + 1) * At ≤ ε / 8 * u * At := by
    have : (4 * |C| + 1) ≤ ε / 8 * u := by linarith
    exact mul_le_mul_of_nonneg_right this hAt0.le
  have h10 : u * ((ε' * 2 + ε') * At) + ε / 8 * u * At < ε * (At * u) := by
    have e : u * ((ε' * 2 + ε') * At) + ε / 8 * u * At = ε / 2 * (At * u) := by
      rw [hε']; ring
    rw [e]
    exact mul_lt_mul_of_pos_right (by linarith) (by positivity)
  linarith

end IsSecondOrderRegularlyVarying

/-! ### Consistency of the Weissman estimator for `ρ ≤ 0` -/

section Weissman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Consistency of the Weissman estimator for any `ρ ≤ 0`** ([dHF, §4.3]). Let
`X_0, X_1, …` be iid with tail quantile function `U` of second-order regular variation with
`γ > 0`, `ρ ≤ 0` (in particular `ρ = 0`) and auxiliary function `A`. Let `k → ∞`, `k / n → 0`,
`√k A(n/k) → λ`, let the extrapolation factor `d_n = k / (n p_n)` satisfy `d_n ≥ 1` eventually
and `log d_n / √k → 0`, and let `a_n` bound `|A|` on `[n/k, 1/p_n]` with
`a_n (1 + log d_n) → 0`. Then `x̂_{p_n} / x_{p_n} → 1` in probability. -/
theorem tendstoInMeasure_weissman_div_of_le {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ} {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {p : ℕ → ℝ}
    (hp0 : ∀ᶠ n in atTop, 0 < p n) (hd1 : ∀ᶠ n in atTop, 1 ≤ (k n : ℝ) / (n * p n))
    (hd : Tendsto (fun n => Real.log ((k n : ℝ) / (n * p n)) / √(k n : ℝ)) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc ((n : ℝ) / k n) (p n)⁻¹, |A y| ≤ a n)
    (hal : Tendsto (fun n => a n * (1 + Real.log ((k n : ℝ) / (n * p n)))) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => weissman (fun i : Fin n => X i ω) (k n) (p n) /
      tailQuantile P (X 0) (p n)) atTop (fun _ => 1) := by
  have hα : 0 < 1 / γ := one_div_pos.2 hγ
  have hRV := h2.isRegularlyVarying_survival (hX 0) hγ
  have hrate := isBoundedInProbability_hill hX hindep hident hγ h2 hk hkn hlam
  have hUm := measurable_tailQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hnk : Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  have hdt : ∀ᶠ n in atTop, (k n : ℝ) / (n * p n) * ((n : ℝ) / k n) = (p n)⁻¹ := by
    filter_upwards [hkR.eventually_gt_atTop 0,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0, hp0] with n hk0 hn0 hpn
    field_simp
  have h := h2.tendsto_div_mul_rpow_of_le hUm hnk hd1 (by
    filter_upwards [ha, hdt] with n hn hdn
    rwa [hdn]) hal
  have hbias : Tendsto (fun n => tailQuantile P (X 0) (p n) /
      (tailQuantile P (X 0) ((k n : ℝ) / n) * ((k n : ℝ) / (n * p n)) ^ γ)) atTop (𝓝 1) := by
    refine h.congr' ?_
    filter_upwards [hkR.eventually_gt_atTop 0,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0,
      hkn.eventually (gt_mem_nhds one_pos), hp0, hd1] with n hk0 hn0 hkn1 hpn hdn
    have hr0 : 0 < (k n : ℝ) / n := div_pos hk0 hn0
    have hpk : p n ≤ (k n : ℝ) / n := by
      rw [le_div_iff₀ (mul_pos hn0 hpn)] at hdn
      rw [le_div_iff₀ hn0]
      linarith
    have hp1 : p n < 1 := hpk.trans_lt hkn1
    rw [tailQuantile_eq_survivalQuantile hpn hp1, tailQuantile_eq_survivalQuantile hr0 hkn1]
    congr 3
    · field_simp
    · rw [inv_div]
  rw [← one_div_one_div γ] at hrate hbias
  exact tendstoInMeasure_weissman_div_of_isBoundedInProbability hX hindep hident hα hRV hk hkn
    hp0 hrate hd hbias

/-- **Consistency of the Weissman estimator for `ρ = 0` with monotone `|A|`**. If, in the
setting of `tendstoInMeasure_weissman_div_of_le`, `|A|` is eventually nonincreasing, then the
conditions reduce to those of the case `ρ < 0`: `k → ∞`, `k / n → 0`, `√k A(n/k) → λ`,
`d_n ≥ 1` eventually and `log d_n / √k → 0` (so that `A(n/k) log d_n → 0`) imply
`x̂_{p_n} / x_{p_n} → 1` in probability, for every `ρ ≤ 0`. -/
theorem tendstoInMeasure_weissman_div_of_antitoneOn {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ} {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A)
    {t₁ : ℝ} (hAm : AntitoneOn (fun t => |A t|) (Ici t₁)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {p : ℕ → ℝ}
    (hp0 : ∀ᶠ n in atTop, 0 < p n) (hd1 : ∀ᶠ n in atTop, 1 ≤ (k n : ℝ) / (n * p n))
    (hd : Tendsto (fun n => Real.log ((k n : ℝ) / (n * p n)) / √(k n : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => weissman (fun i : Fin n => X i ω) (k n) (p n) /
      tailQuantile P (X 0) (p n)) atTop (fun _ => 1) := by
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hnk : Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  refine tendstoInMeasure_weissman_div_of_le hX hindep hident hγ h2 hk hkn hlam hp0 hd1 hd
    (a := fun n => |A (n / k n)|) ?_ ?_
  · filter_upwards [hnk.eventually_ge_atTop t₁] with n hn y hy
    exact hAm hn (hn.trans hy.1) hy.1
  · have h1 : Tendsto (fun n => |A (n / k n)|) atTop (𝓝 0) := by
      simpa using (h2.tendsto_zero.comp hnk).abs
    have h3 := h1.add (hlam.abs.mul hd)
    rw [zero_add, mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [hkR.eventually_gt_atTop 0] with n hk0
    have hs : 0 < √(k n : ℝ) := sqrt_pos.2 hk0
    rw [abs_mul, abs_of_pos hs]
    field_simp

end Weissman

/-! ### Consistency of the tail probability estimator for `ρ ≤ 0` -/

section TailProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Consistency of the tail probability estimator for any `ρ ≤ 0`** ([dHF, §4.4]). Let
`X_0, X_1, …` be iid with tail quantile function of second-order regular variation with
`γ > 0`, `ρ ≤ 0` and auxiliary function `A`. Let `k → ∞`, `k / n → 0`, `√k A(n/k) → λ`, let
the levels `y_n` satisfy `x_{k/n} ≤ y_n` eventually and `log (y_n / x_{k/n}) / √k → 0`, and let
`a_n` bound `|A|` on `[n/k, 1/F̄(y_n)]` with `a_n (1 + log D_n) → 0`, where
`D_n = k / (n F̄(y_n))`. Then `p̂(y_n) / P(X > y_n) → 1` in probability. -/
theorem tendstoInMeasure_tailProbEstimator_div_of_le {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ} {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {y : ℕ → ℝ}
    (hy : ∀ᶠ n in atTop, tailQuantile P (X 0) ((k n : ℝ) / n) ≤ y n)
    (he : Tendsto (fun n => Real.log (y n / tailQuantile P (X 0) ((k n : ℝ) / n)) /
      √(k n : ℝ)) atTop (𝓝 0)) {a : ℕ → ℝ}
    (ha : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc ((n : ℝ) / k n) ((P {ω | y n < X 0 ω}).toReal)⁻¹,
      |A z| ≤ a n)
    (hal : Tendsto (fun n => a n *
      (1 + Real.log ((k n : ℝ) / (n * (P {ω | y n < X 0 ω}).toReal)))) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => tailProbEstimator (fun i : Fin n => X i ω) (k n) (y n) /
      (P {ω | y n < X 0 ω}).toReal) atTop (fun _ => 1) := by
  have hα : 0 < 1 / γ := one_div_pos.2 hγ
  have hRV := h2.isRegularlyVarying_survival (hX 0) hγ
  have hrate := isBoundedInProbability_hill hX hindep hident hγ h2 hk hkn hlam
  have hUm := measurable_tailQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hnk : Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  have hbias := tendsto_tailProb_div_of_extrapolation (hX 0) hγ h2 hk hkn hy
    fun D hD1 hDs => by
      have hDe : ∀ᶠ n in atTop, D n = (k n : ℝ) / (n * (P {ω | y n < X 0 ω}).toReal) := by
        filter_upwards [hDs, hkR.eventually_gt_atTop 0,
          (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0] with n hn hk0 hn0
        have hF := survival_pos hRV (y n)
        change D n * ((n : ℝ) / k n) = (survival P (X 0) (y n))⁻¹ at hn
        change D n = (k n : ℝ) / (n * survival P (X 0) (y n))
        field_simp at hn ⊢
        linarith
      refine h2.tendsto_div_mul_rpow_of_le hUm hnk hD1 (a := a) ?_ (hal.congr' ?_)
      · filter_upwards [ha, hDs] with n hn hdn
        rw [hdn]
        exact hn
      · filter_upwards [hDe] with n hn
        rw [hn]
  rw [← one_div_one_div γ] at hrate
  have hy0 : ∀ᶠ n in atTop, 0 < y n := by
    filter_upwards [hy, hnk.eventually h2.eventually_pos,
      hkR.eventually_gt_atTop 0,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0,
      hkn.eventually (gt_mem_nhds one_pos)] with n h1 h3 hk0 hn0 hkn1
    rw [tailQuantile_eq_survivalQuantile (div_pos hk0 hn0) hkn1, inv_div] at h1
    exact h3.trans_le h1
  exact tendstoInMeasure_tailProbEstimator_div_of_isBoundedInProbability hX hindep hident hα hRV
    hk hkn hy0 hrate he hbias

end TailProbability

/-! ### Asymptotic normality of the Weissman estimator for `ρ ≤ 0` -/

section Normality

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Asymptotic normality of the Weissman estimator with an explicit extrapolation bias**
(any `ρ ≤ 0`; [dHF, §4.3]). Let `X_0, X_1, …` be iid with tail quantile function `U` of
second-order regular variation with `γ > 0`, `ρ ≤ 0` and auxiliary function `A`, let `k → ∞`,
`k / n → 0`, `√k A(n/k) → λ`, and let `d_n = k / (n p_n) → ∞` with `log d_n / √k → 0`. If the
deterministic extrapolation remainder `r_n = log U(d_n n/k) - log U(n/k) - γ log d_n` satisfies
`√k r_n / log d_n → μ`, then, for `Z ~ N(λ / (1 - ρ), γ²)`,

  `(√k / log d_n) (x̂_{p_n} / x_{p_n} - 1) ⇒ Z - μ ~ N(λ / (1 - ρ) - μ, γ²)`.

For `ρ < 0`, `μ = 0` (`tendstoInDistribution_weissman`); for `ρ = 0`, typically `μ = λ`
(`tendstoInDistribution_weissman_of_rho_eq_zero`). -/
theorem tendstoInDistribution_weissman_of_tendsto_bias {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {p : ℕ → ℝ}
    (hp0 : ∀ᶠ n in atTop, 0 < p n) (hd : Tendsto (fun n => (k n : ℝ) / (n * p n)) atTop atTop)
    (hdk : Tendsto (fun n => Real.log ((k n : ℝ) / (n * p n)) / √(k n : ℝ)) atTop (𝓝 0))
    {μ : ℝ} (hμ : Tendsto (fun n => √(k n : ℝ) *
      (log (survivalQuantile (survival P (X 0)) ((k n : ℝ) / (n * p n) * (n / k n))) -
        log (survivalQuantile (survival P (X 0)) (n / k n)) -
        γ * log ((k n : ℝ) / (n * p n))) / log ((k n : ℝ) / (n * p n))) atTop (𝓝 μ))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal (lam / (1 - ρ)) (γ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) / Real.log ((k n : ℝ) / (n * p n)) *
      (weissman (fun i : Fin n => X i ω) (k n) (p n) / tailQuantile P (X 0) (p n) - 1))
      atTop (fun ω => Z ω - μ) (fun _ => P) P' := by
  set U := survivalQuantile (survival P (X 0)) with hUdef
  have hUm := measurable_tailQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  set d : ℕ → ℝ := fun n => (k n : ℝ) / (n * p n) with hd_def
  set ℓ : ℕ → ℝ := fun n => Real.log (d n) with hℓ_def
  set h : ℕ → ℝ := fun n => ℓ n / √(k n : ℝ) with hh_def
  set t : ℕ → ℝ := fun n => (n : ℝ) / k n with ht_def
  have hnk : Tendsto t atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  set r : ℕ → ℝ := fun n => log (U (d n * t n)) - log (U (t n)) - γ * log (d n) with hr_def
  have hℓ : Tendsto ℓ atTop atTop := tendsto_log_atTop.comp hd
  have hℓinv : Tendsto (fun n => (ℓ n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hℓ
  have hrdet : Tendsto (fun n => √(k n : ℝ) * r n / ℓ n) atTop (𝓝 μ) := hμ
  -- the random terms
  have hW := tendstoInDistribution_hill hX hindep hident hγ h2 hk hkn hlam hZ
  have hV := isBoundedInProbability_log_orderStat hX hindep hident h2 hk hkn hlam
  have hOS : ∀ n, Measurable fun ω => orderStat (fun i : Fin n => X i ω) (k n) := fun n =>
    measurable_orderStat (fun i => hX i) _
  have hH : ∀ n, Measurable fun ω => hill (fun i : Fin n => X i ω) (k n) := fun n =>
    (measurable_hill_pi n (k n)).comp (measurable_pi_iff.2 fun i => hX i)
  set W : ℕ → Ω → ℝ := fun n ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - γ)
    with hW_def
  set V : ℕ → Ω → ℝ := fun n ω => √(k n : ℝ) *
    (log (orderStat (fun i : Fin n => X i ω) (k n)) - log (U (t n))) with hV_def
  set Y : ℕ → Ω → ℝ := fun n ω => (ℓ n)⁻¹ * V n ω - √(k n : ℝ) * r n / ℓ n with hY_def
  have hY : TendstoInMeasure P Y atTop (fun _ => -μ) := by
    have h1 := tendstoInMeasure_mul_zero_of_isBoundedInProbability hV hℓinv
    have h2' := tendstoInMeasure_const_of_tendsto (P := P) hrdet
    have := tendstoInMeasure_comp₂ h1 h2' (φ := fun q => q.1 - q.2) (by fun_prop)
    simp only [zero_sub] at this
    exact this
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (measurable_const.mul (measurable_const.mul ((hOS n).log.sub measurable_const))).sub
      measurable_const
  set Z' : Ω' → ℝ := fun ω => Z ω - μ with hZ'_def
  have hZ0 : (fun ω => Z' ω + 0) = Z' := by funext ω; simp
  set G : ℕ → Ω → ℝ := fun n => W n + Y n with hG_def
  have hG : TendstoInDistribution G atTop Z' (fun _ => P) P' := by
    have := hW.add_of_tendstoInMeasure_const hY fun n => (hYm n).aemeasurable
    have e : (fun ω => Z ω + -μ) = Z' := by funext ω; simp [hZ'_def, sub_eq_add_neg]
    rwa [e] at this
  have hGm : ∀ n, Measurable (G n) := fun n =>
    (measurable_const.mul ((hH n).sub measurable_const)).add (hYm n)
  have hGt := isBoundedInProbability_of_tendstoInDistribution hG
  have hhG : TendstoInMeasure P (fun n ω => h n * G n ω) atTop (fun _ => 0) :=
    tendstoInMeasure_mul_zero_of_isBoundedInProbability hGt hdk
  have hφ := tendstoInMeasure_comp hhG (φ := fun y => expSlope y - 1)
    (continuousAt_expSlope.sub continuousAt_const)
  simp only [expSlope_zero, sub_self] at hφ
  have hY2 := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hGt hφ
  have hY2m : ∀ n, Measurable fun ω => (expSlope (h n * G n ω) - 1) * G n ω := fun n =>
    ((measurable_expSlope.comp (measurable_const.mul (hGm n))).sub_const 1).mul (hGm n)
  set T' : ℕ → Ω → ℝ := fun n => G n + fun ω => (expSlope (h n * G n ω) - 1) * G n ω
    with hT'_def
  have hT' : TendstoInDistribution T' atTop Z' (fun _ => P) P' := by
    have := hG.add_of_tendstoInMeasure_const hY2 fun n => (hY2m n).aemeasurable
    rwa [hZ0] at this
  have hT'm : ∀ n, Measurable (T' n) := fun n => (hGm n).add (hY2m n)
  set T : ℕ → Ω → ℝ := fun n ω => √(k n : ℝ) / Real.log ((k n : ℝ) / (n * p n)) *
    (weissman (fun i : Fin n => X i ω) (k n) (p n) / tailQuantile P (X 0) (p n) - 1) with hT_def
  have hTm : ∀ n, Measurable (T n) := by
    intro n
    have h1 := hOS n
    have h3 := hH n
    simp only [hT_def, weissman]
    fun_prop
  -- the event `X_{(k+1)} ≤ 0` is asymptotically negligible
  have hRV := h2.isRegularlyVarying_survival (hX 0) hγ
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have hr0 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < k n / n := by
    filter_upwards [hkpos, hnpos] with n h1 h2; positivity
  obtain ⟨hs, -⟩ := tendsto_tailQuantile (hX 0) hRV hr0 hkn
  have hbad : Tendsto (fun n => P {ω | orderStat (fun i : Fin n => X i ω) (k n) ≤ 0}) atTop
      (𝓝 0) := by
    have hloc := tendstoInMeasure_orderStat_div_tailQuantile hX hindep hident
      (one_div_pos.2 hγ) hRV hk hkn
    rw [tendstoInMeasure_iff_dist] at hloc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hloc 1 one_pos)
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hs.eventually_gt_atTop 0] with n hsn
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq, Real.dist_eq] at hω ⊢
    have : orderStat (fun i : Fin n => X i ω) (k n) / tailQuantile P (X 0) ((k n : ℝ) / n) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hω hsn.le
    rw [abs_sub_comm]
    exact (le_abs_self _).trans' (by linarith)
  have hdt : Tendsto (fun n => d n * t n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hnk
    filter_upwards [hd.eventually_ge_atTop 1, hnk.eventually_ge_atTop 0] with n h1 h3
    exact le_mul_of_one_le_left h3 h1
  have hD : TendstoInMeasure P (fun n ω => T n ω - T' n ω) atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr_of_measure_ne (g := fun _ _ => 0)
      (tendstoInMeasure_const_of_tendsto tendsto_const_nhds) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hkpos, hnpos, hp0, hkn.eventually (gt_mem_nhds one_pos),
      hd.eventually_gt_atTop 1, hnk.eventually h2.eventually_pos,
      hdt.eventually h2.eventually_pos] with n hk0 hn0 hpn hkn1 hd1 hUt hUdt
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra ho
    rw [not_le] at ho
    apply hω
    set o := orderStat (fun i : Fin n => X i ω) (k n) with ho_def
    set g := hill (fun i : Fin n => X i ω) (k n) with hg_def
    have hd0 : 0 < d n := one_pos.trans hd1
    have hℓ0 : 0 < ℓ n := log_pos hd1
    have hsk : 0 < √(k n : ℝ) := sqrt_pos.2 hk0
    have hh0 : h n ≠ 0 := (div_pos hℓ0 hsk).ne'
    -- the extreme quantile is `U(d t)`
    have hpk : p n ≤ (k n : ℝ) / n := by
      have := hd1.le
      simp only [hd_def] at this
      rw [le_div_iff₀ (mul_pos hn0 hpn)] at this
      rw [le_div_iff₀ hn0]
      linarith
    have hxp : tailQuantile P (X 0) (p n) = U (d n * t n) := by
      rw [tailQuantile_eq_survivalQuantile hpn (hpk.trans_lt hkn1)]
      congr 1
      simp only [hd_def, ht_def]
      field_simp
    have key : h n * G n ω = log o + log (d n) * g - log (U (d n * t n)) := by
      have hℓ0' : log (d n) ≠ 0 := hℓ0.ne'
      simp only [hG_def, hW_def, hY_def, hV_def, hr_def, hh_def, Pi.add_apply, hℓ_def]
      field_simp
      ring
    have hw : weissman (fun i : Fin n => X i ω) (k n) (p n) / tailQuantile P (X 0) (p n) =
        exp (h n * G n ω) := by
      rw [key, exp_sub, exp_add, exp_log ho, exp_log hUdt, hxp, weissman,
        rpow_def_of_pos hd0]
    have hT'e : T' n ω = (exp (h n * G n ω) - 1) / h n := by
      rw [← mul_expSlope_mul hh0]
      simp only [hT'_def, Pi.add_apply]
      ring
    simp only [hT_def]
    rw [hw, hT'e, sub_eq_zero]
    simp only [hh_def, hℓ_def, hd_def]
    field_simp
  have hfinal := hT'.add_of_tendstoInMeasure_const hD fun n => ((hTm n).sub (hT'm n)).aemeasurable
  rw [hZ0] at hfinal
  have e : (fun n => T' n + fun ω => T n ω - T' n ω) = T := by
    funext n ω
    simp
  rw [e] at hfinal
  exact hfinal

end Normality

end ExtremeValueTheory
