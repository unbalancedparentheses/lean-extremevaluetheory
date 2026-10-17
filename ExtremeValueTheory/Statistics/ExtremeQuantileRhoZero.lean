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

end ExtremeValueTheory
