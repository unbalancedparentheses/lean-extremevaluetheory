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

end IsSecondOrderRegularlyVarying

end ExtremeValueTheory
