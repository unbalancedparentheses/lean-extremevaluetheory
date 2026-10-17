/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.UniformConvergence
import ExtremeValueTheory.RegularVariation.KaramataConverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Field.GeomSum

/-!
# Second-order regular variation

TODO
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

/-- The function `h_ρ(x) = (x^ρ - 1) / ρ`, with `h_0(x) = log x`, the limit function of
second-order regular variation ([dHF, §2.3]). -/
noncomputable def boxCox (ρ x : ℝ) : ℝ :=
  if ρ = 0 then log x else (x ^ ρ - 1) / ρ

theorem boxCox_zero (x : ℝ) : boxCox 0 x = log x := by simp [boxCox]

theorem boxCox_of_ne {ρ : ℝ} (hρ : ρ ≠ 0) (x : ℝ) : boxCox ρ x = (x ^ ρ - 1) / ρ := by
  simp [boxCox, hρ]

theorem boxCox_exp (ρ u : ℝ) :
    boxCox ρ (exp u) = if ρ = 0 then u else (exp (ρ * u) - 1) / ρ := by
  unfold boxCox
  split_ifs with h
  · exact log_exp u
  · rw [← exp_mul, mul_comm]

/-- For `u ≥ 0`, `0 ≤ h_ρ(e^u) ≤ u` when `ρ ≤ 0`. -/
theorem boxCox_exp_nonneg_le {ρ u : ℝ} (hρ : ρ ≤ 0) (hu : 0 ≤ u) :
    0 ≤ boxCox ρ (exp u) ∧ boxCox ρ (exp u) ≤ u := by
  rw [boxCox_exp]
  split_ifs with h
  · exact ⟨hu, le_rfl⟩
  · have hρ' : ρ < 0 := lt_of_le_of_ne hρ h
    have h1 : exp (ρ * u) ≤ 1 := exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hρ hu)
    have h2 : 1 + ρ * u ≤ exp (ρ * u) := by linarith [add_one_le_exp (ρ * u)]
    constructor
    · exact div_nonneg_of_nonpos (by linarith) hρ
    · rw [div_le_iff_of_neg hρ']
      linarith

theorem boxCox_pos_of_one_lt {ρ x : ℝ} (hx : 1 < x) : 0 < boxCox ρ x := by
  unfold boxCox
  split_ifs with h
  · exact log_pos hx
  · rcases lt_or_gt_of_ne h with hρ | hρ
    · exact div_pos_of_neg_of_neg (by linarith [rpow_lt_one_of_one_lt_of_neg hx hρ]) hρ
    · exact div_pos (by linarith [one_lt_rpow hx hρ]) hρ

/-- **Second-order regular variation** ([dHF, Definition 2.3.1 and Theorem 2.3.3], in the case
`γ > 0` relevant for heavy tails). A function `U`, eventually positive, is of second-order regular
variation with first-order index `γ`, second-order index `ρ ≤ 0` and auxiliary function `A` if
`A` has eventually constant sign, `A(t) → 0`, `|A|` is regularly varying with index `ρ`, and for
every `x > 0`

  `(U(xt) / U(t) - x^γ) / A(t) → x^γ (x^ρ - 1) / ρ` as `t → ∞`. -/
structure IsSecondOrderRegularlyVarying (U : ℝ → ℝ) (γ ρ : ℝ) (A : ℝ → ℝ) : Prop where
  eventually_pos : ∀ᶠ t in atTop, 0 < U t
  nonpos : ρ ≤ 0
  tendsto_zero : Tendsto A atTop (𝓝 0)
  sign : (∀ᶠ t in atTop, 0 < A t) ∨ (∀ᶠ t in atTop, A t < 0)
  isRegularlyVarying_abs : IsRegularlyVarying (fun t => |A t|) ρ
  tendsto : ∀ x, 0 < x →
    Tendsto (fun t => (U (x * t) / U t - x ^ γ) / A t) atTop (𝓝 (x ^ γ * boxCox ρ x))

namespace IsSecondOrderRegularlyVarying

variable {U A : ℝ → ℝ} {γ ρ : ℝ}

theorem eventually_ne_zero (h : IsSecondOrderRegularlyVarying U γ ρ A) :
    ∀ᶠ t in atTop, A t ≠ 0 := by
  rcases h.sign with h' | h'
  · exact h'.mono fun _ ht => ht.ne'
  · exact h'.mono fun _ ht => ht.ne

/-- `|log(1 + y) - y| ≤ 2 y²` for `|y| ≤ 1/2`. -/
private lemma abs_log_one_add_sub_le {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |log (1 + y) - y| ≤ 2 * y ^ 2 := by
  have h := abs_log_sub_add_sum_range_le (x := -y) (by rw [abs_neg]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, sub_neg_eq_add, abs_neg] at h
  rw [show log (1 + y) - y = -y + log (1 + y) by ring]
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith), ← sq_abs y, show (1 + 1 : ℕ) = 2 from rfl]
  nlinarith [mul_nonneg (sq_nonneg |y|) (by linarith : (0 : ℝ) ≤ 1 - 2 * |y|)]

/-- The logarithmic form of second-order regular variation:
`(log U(xt) - log U(t) - γ log x) / A(t) → h_ρ(x)`. -/
theorem tendsto_log (h : IsSecondOrderRegularlyVarying U γ ρ A) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t => (log (U (x * t)) - log (U t) - γ * log x) / A t) atTop
      (𝓝 (boxCox ρ x)) := by
  have hxγ : 0 < x ^ γ := rpow_pos_of_pos hx γ
  set y : ℝ → ℝ := fun t => U (x * t) / (x ^ γ * U t) - 1 with hy
  have hyA : Tendsto (fun t => y t / A t) atTop (𝓝 (boxCox ρ x)) := by
    have := (h.tendsto x hx).div_const (x ^ γ)
    rw [mul_div_cancel_left₀ _ hxγ.ne'] at this
    refine this.congr' ?_
    filter_upwards [h.eventually_pos] with t ht
    simp only [hy]
    field_simp
  have hy0 : Tendsto y atTop (𝓝 0) := by
    have := hyA.mul h.tendsto_zero
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [h.eventually_ne_zero] with t ht
    field_simp
  have hxt : ∀ᶠ t in atTop, 0 < U (x * t) :=
    (tendsto_id.const_mul_atTop hx).eventually h.eventually_pos
  have hsmall : ∀ᶠ t in atTop, |y t| ≤ 1 / 2 := by
    have := hy0.abs
    rw [abs_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have herr : Tendsto (fun t => (log (1 + y t) - y t) / A t) atTop (𝓝 0) := by
    have hb : Tendsto (fun t => 2 * |y t / A t| * |y t|) atTop (𝓝 0) := by
      have := ((hyA.abs.const_mul 2).mul hy0.abs)
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hsmall] with t ht
    rw [Real.norm_eq_abs, abs_div, abs_div]
    rcases eq_or_ne (A t) 0 with hA | hA
    · simp [hA]
    have hA' : 0 < |A t| := abs_pos.2 hA
    rw [div_le_iff₀ hA']
    calc |log (1 + y t) - y t| ≤ 2 * y t ^ 2 := abs_log_one_add_sub_le ht
      _ = 2 * (|y t| / |A t|) * |y t| * |A t| := by
          rw [← sq_abs (y t)]; field_simp

  have := hyA.add herr
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [h.eventually_pos, hxt] with t ht hxt
  have e : log (U (x * t)) - log (U t) - γ * log x = log (1 + y t) := by
    simp only [hy, add_sub_cancel]
    rw [log_div hxt.ne' (mul_pos hxγ ht).ne', log_mul hxγ.ne' ht.ne', log_rpow hx]
    ring
  rw [e]
  ring

/-- The auxiliary function can be replaced by any asymptotically equivalent function. -/
theorem of_tendsto_div (h : IsSecondOrderRegularlyVarying U γ ρ A) {A' : ℝ → ℝ}
    (hA' : Tendsto (fun t => A' t / A t) atTop (𝓝 1)) :
    IsSecondOrderRegularlyVarying U γ ρ A' := by
  have hpos : ∀ᶠ t in atTop, 0 < A' t / A t := hA'.eventually (lt_mem_nhds one_pos)
  have hinv : Tendsto (fun t => A t / A' t) atTop (𝓝 1) := by
    have := hA'.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp [inv_div]
  have hne' : ∀ᶠ t in atTop, A' t ≠ 0 := by
    filter_upwards [hpos] with t ht h0
    simp [h0] at ht
  refine ⟨h.eventually_pos, h.nonpos, ?_, ?_, ?_, ?_⟩
  · have := hA'.mul h.tendsto_zero
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [h.eventually_ne_zero] with t ht
    field_simp
  · rcases h.sign with h' | h'
    · left
      filter_upwards [h', hpos] with t h1 h2
      have := mul_pos h2 h1
      rwa [div_mul_cancel₀ _ h1.ne'] at this
    · right
      filter_upwards [h', hpos] with t h1 h2
      have := mul_neg_of_pos_of_neg h2 h1
      rwa [div_mul_cancel₀ _ h1.ne] at this
  · have hr := IsRegularlyVarying.of_tendsto one_pos (by simpa using hA'.abs)
    have := hr.mul h.isRegularlyVarying_abs
    rw [zero_add] at this
    refine this.congr ?_
    filter_upwards [h.eventually_ne_zero] with t ht
    rw [← abs_mul, div_mul_cancel₀ _ ht]
  · intro x hx
    have := (h.tendsto x hx).mul hinv
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [h.eventually_ne_zero, hne'] with t h1 h2
    field_simp

/-- A measurable auxiliary function: if `U` is measurable, then
`A'(t) = (log U(2t) - log U(t) - γ log 2) / h_ρ(2)` is a measurable auxiliary function with
`A'(t) / A(t) → 1`. -/
theorem exists_measurable (h : IsSecondOrderRegularlyVarying U γ ρ A) (hU : Measurable U) :
    ∃ A' : ℝ → ℝ, Measurable A' ∧ IsSecondOrderRegularlyVarying U γ ρ A' ∧
      Tendsto (fun t => A' t / A t) atTop (𝓝 1) := by
  have hb : 0 < boxCox ρ 2 := boxCox_pos_of_one_lt one_lt_two
  set A' : ℝ → ℝ := fun t => (log (U (2 * t)) - log (U t) - γ * log 2) / boxCox ρ 2 with hA'
  have hlim : Tendsto (fun t => A' t / A t) atTop (𝓝 1) := by
    have := (h.tendsto_log (x := 2) two_pos).div_const (boxCox ρ 2)
    rw [div_self hb.ne'] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [hA']
    ring
  refine ⟨A', ?_, h.of_tendsto_div hlim, hlim⟩
  exact ((((hU.comp (measurable_const_mul 2)).log).sub hU.log).sub_const _).div_const _

end IsSecondOrderRegularlyVarying

end ExtremeValueTheory
