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

Following de Haan and Ferreira, *Extreme Value Theory: An Introduction* (Springer, 2006),
henceforth [dHF], §2.3, a function `U` is of *second-order regular variation* with first-order
index `γ`, second-order index `ρ ≤ 0` and auxiliary function `A` if `A` has eventually constant
sign, `A(t) → 0`, `|A|` is regularly varying with index `ρ`, and

  `(U(xt) / U(t) - x^γ) / A(t) → x^γ h_ρ(x)`, `h_ρ(x) = (x^ρ - 1) / ρ` (`= log x` for `ρ = 0`).

This is the condition that controls the bias of tail estimators such as the Hill estimator
([dHF, Theorem 3.2.5]).

## Main definitions

* `ExtremeValueTheory.boxCox ρ x`: the limit function `h_ρ(x)`.
* `ExtremeValueTheory.IsSecondOrderRegularlyVarying U γ ρ A`: second-order regular variation.

## Main results

* `IsSecondOrderRegularlyVarying.tendsto_log`: the logarithmic form
  `(log U(xt) - log U(t) - γ log x) / A(t) → h_ρ(x)`.
* `IsSecondOrderRegularlyVarying.of_tendsto_div`: the auxiliary function may be replaced by an
  asymptotically equivalent one.
* `IsSecondOrderRegularlyVarying.exists_measurable`: for measurable `U` there is a measurable
  auxiliary function, `A'(t) = (log U(2t) - log U(t) - γ log 2) / h_ρ(2)`.
* `IsSecondOrderRegularlyVarying.exists_bound`: the **uniform bound**
  `|log U(xt) - log U(t) - γ log x| ≤ C |A(t)| x^δ` for `t ≥ t₀`, `x ≥ 1` (a one-sided form of
  [dHF, Theorem 2.3.9]), for measurable `U` and `A`.
* `isSecondOrderRegularlyVarying_add_const`: `U(t) = t + c` is second-order regularly varying
  with `γ = 1`, `ρ = -1`.
* `IsSecondOrderRegularlyVarying.exists_bound_of_neg`: for `ρ < 0`, the bound
  `|log U(xt) - log U(t) - γ log x| ≤ C |A(t)|` uniformly in `x ≥ 1`.

## Proof of the uniform bound

Working additively (`s = log t`, `u = log x`), we first show that
`|G(s + ξ) - G(s)| ≤ M |a(s)|` for `ξ ∈ [0, 1]` and `s` large, by the measure-theoretic
(Steinhaus-type) argument of the uniform convergence theorem
(`exists_abs_sub_le_of_tendsto`, compare `ExtremeValueTheory.RegularVariation.UniformConvergence`
and [BGT, §3.1]). Iterating over unit steps and using the Potter bounds for `|A|` gives the
exponential bound `C |a(s)| e^{δ u}` (`abs_sub_le_sum_of_le`).

## References

* [dHF] L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*, Springer, 2006.
* [BGT] N. H. Bingham, C. M. Goldie, J. L. Teugels, *Regular Variation*, Cambridge University
  Press, 1987.
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

/-! ### Uniform bounds -/

section UniformBound

/-- The measure-theoretic (Steinhaus-type) core of the uniform bound: if
`(G(s + u) - G(s)) / a(s) → H(u)` for every `u`, with `G` measurable, `|H| < B` on `[0, 2]`
and `|a(s + ξ)| ≤ K |a(s)|` for `ξ ∈ [0, 1]`, then `|G(s + ξ) - G(s)| ≤ B (1 + K) |a(s)|` for
`ξ ∈ [0, 1]` and `s` large. Compare [dHF, Theorem B.2.9] and [BGT, §3.1]. -/
theorem exists_abs_sub_le_of_tendsto {G a H : ℝ → ℝ} (hG : Measurable G)
    (hlim : ∀ u, Tendsto (fun s => (G (s + u) - G s) / a s) atTop (𝓝 (H u))) {B : ℝ}
    (hB : ∀ u ∈ Icc (0 : ℝ) 2, |H u| < B) {K s₀ : ℝ} (ha0 : ∀ s ≥ s₀, a s ≠ 0)
    (hK : ∀ s ≥ s₀, ∀ ξ ∈ Icc (0 : ℝ) 1, |a (s + ξ)| ≤ K * |a s|) :
    ∃ S, ∀ s ≥ S, ∀ ξ ∈ Icc (0 : ℝ) 1, |G (s + ξ) - G s| ≤ B * (1 + K) * |a s| := by
  set D : ℝ → Set ℝ := fun s => Icc 0 2 ∩ {u | B ≤ |(G (s + u) - G s) / a s|} with hD
  have hDm : ∀ s, MeasurableSet (D s) := fun s =>
    measurableSet_Icc.inter (measurableSet_le measurable_const
      (continuous_abs.measurable.comp (((hG.comp (measurable_const_add s)).sub_const _).div_const
        _)))
  have hvol : Tendsto (fun s => volume (D s)) atTop (𝓝 (volume (∅ : Set ℝ))) := by
    refine tendsto_measure_of_tendsto_indicator atTop hDm measurableSet_Icc
      (by simp [Real.volume_Icc]) (Eventually.of_forall fun s => inter_subset_left) fun u => ?_
    by_cases hu : u ∈ Icc (0 : ℝ) 2
    · filter_upwards [(hlim u).abs.eventually (gt_mem_nhds (hB u hu))] with s hs
      simp only [hD, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and,
        not_le]
      exact fun _ => hs
    · exact Eventually.of_forall fun s => by simp [hD, hu]
  rw [measure_empty] at hvol
  obtain ⟨S₁, hS₁⟩ := eventually_atTop.1
    ((tendsto_order.1 hvol).2 (2⁻¹ : ENNReal) (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top))
  refine ⟨max S₁ s₀, fun s hs ξ hξ => ?_⟩
  have hs1 : S₁ ≤ s := (le_max_left _ _).trans hs
  have hs0 : s₀ ≤ s := (le_max_right _ _).trans hs
  by_contra hcon
  rw [not_le] at hcon
  have has : 0 < |a s| := abs_pos.2 (ha0 s hs0)
  have hasξ : 0 < |a (s + ξ)| := abs_pos.2 (ha0 _ (by linarith [hξ.1]))
  have hKs := hK s hs0 ξ hξ
  have hsub : Icc (1 : ℝ) 2 ⊆ D s ∪ (fun u => u + -ξ) ⁻¹' D (s + ξ) := by
    intro u hu
    by_cases h1 : B ≤ |(G (s + u) - G s) / a s|
    · exact Or.inl ⟨⟨by linarith [hu.1], hu.2⟩, h1⟩
    · refine Or.inr ⟨⟨by linarith [hu.1, hξ.2], by linarith [hu.2, hξ.1]⟩, ?_⟩
      show B ≤ |(G (s + ξ + (u + -ξ)) - G (s + ξ)) / a (s + ξ)|
      rw [show s + ξ + (u + -ξ) = s + u by ring]
      by_contra h2
      rw [not_le, abs_div, div_lt_iff₀ hasξ] at h2
      rw [not_le, abs_div, div_lt_iff₀ has] at h1
      have h3 := abs_sub_le (G (s + ξ)) (G (s + u)) (G s)
      rw [abs_sub_comm (G (s + ξ)) (G (s + u))] at h3
      have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨le_rfl, zero_le_two⟩).le
      nlinarith
  have h1 := measure_mono (μ := volume) hsub
  have h2 := measure_union_le (μ := volume) (D s) ((fun u => u + -ξ) ⁻¹' D (s + ξ))
  rw [measure_preimage_add_right] at h2
  rw [Real.volume_Icc] at h1
  have h3 : volume (D s) + volume (D (s + ξ)) < 2⁻¹ + 2⁻¹ :=
    ENNReal.add_lt_add (hS₁ s hs1) (hS₁ _ (by linarith [hξ.1]))
  rw [ENNReal.inv_two_add_inv_two] at h3
  have : ENNReal.ofReal (2 - 1) = 1 := by norm_num
  rw [this] at h1
  exact lt_irrefl _ (h1.trans_lt (h2.trans_lt h3))

/-- Iterating a bound on `[0, 1]`: `|G(s + u) - G(s)| ≤ M ∑_{j<m} |a(s + j)|` for
`u ∈ [0, m]`. -/
theorem abs_sub_le_sum_of_le {G a : ℝ → ℝ} {M S : ℝ} (hM : 0 ≤ M)
    (h1 : ∀ s ≥ S, ∀ ξ ∈ Icc (0 : ℝ) 1, |G (s + ξ) - G s| ≤ M * |a s|) :
    ∀ m : ℕ, ∀ s ≥ S, ∀ u ∈ Icc (0 : ℝ) m,
      |G (s + u) - G s| ≤ M * ∑ j ∈ Finset.range m, |a (s + j)| := by
  intro m
  induction m with
  | zero =>
    intro s _ u hu
    have : u = 0 := le_antisymm (by simpa using hu.2) hu.1
    simp [this]
  | succ m ih =>
    intro s hs u hu
    rw [Finset.sum_range_succ, mul_add]
    push_cast at hu
    have hpos : 0 ≤ M * |a (s + m)| := mul_nonneg hM (abs_nonneg _)
    rcases le_or_gt u m with hum | hum
    · exact (ih s hs u ⟨hu.1, hum⟩).trans (le_add_of_nonneg_right hpos)
    · have e1 := h1 (s + m) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) (u - m)
        ⟨by linarith, by linarith [hu.2]⟩
      have e2 := ih s hs m ⟨Nat.cast_nonneg m, le_rfl⟩
      rw [show s + m + (u - m) = s + u by ring] at e1
      have := abs_sub_le (G (s + u)) (G (s + m)) (G s)
      linarith

end UniformBound

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

/-- **Uniform bound for second-order regular variation** (a one-sided form of [dHF, Theorem 2.3.9]
and of the Drees inequalities). If `U` and `A` are measurable, then for every `δ > 0` there are
`C` and `t₀ > 0` with

  `|log U(xt) - log U(t) - γ log x| ≤ C |A(t)| x^δ` for all `t ≥ t₀`, `x ≥ 1`. -/
theorem exists_bound (h : IsSecondOrderRegularlyVarying U γ ρ A) (hU : Measurable U)
    (hA : Measurable A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t ≥ t₀, ∀ x ≥ 1,
      |log (U (x * t)) - log (U t) - γ * log x| ≤ C * |A t| * x ^ δ := by
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
  -- Potter bounds for `|A|`
  obtain ⟨x₀, hx₀, hApos, hP⟩ :=
    h.isRegularlyVarying_abs.potter_bound_of_measurable (continuous_abs.measurable.comp hA) hδ
      one_lt_two
  have hPot : ∀ s ≥ log x₀, ∀ v ≥ (0 : ℝ), |a (s + v)| ≤ 2 * |a s| * exp (δ * v) := by
    intro s hs v hv
    have hxs : x₀ ≤ exp s := (log_le_iff_le_exp hx₀).1 hs
    have hxsv : x₀ ≤ exp (s + v) := hxs.trans (exp_le_exp.2 (by linarith))
    have h1 := hP (exp s) hxs (exp (s + v)) hxsv
    have hpos := hApos (exp s) hxs
    rw [div_le_iff₀ hpos] at h1
    have hr : exp (s + v) / exp s = exp v := by rw [exp_add]; field_simp
    rw [hr] at h1
    have hm : max (exp v ^ (ρ + δ)) (exp v ^ (ρ - δ)) ≤ exp (δ * v) := by
      rw [← exp_mul, ← exp_mul]
      refine max_le (exp_le_exp.2 ?_) (exp_le_exp.2 ?_) <;> nlinarith [h.nonpos]
    calc |a (s + v)| ≤ 2 * max (exp v ^ (ρ + δ)) (exp v ^ (ρ - δ)) * |a s| := h1
      _ ≤ 2 * exp (δ * v) * |a s| := by gcongr
      _ = 2 * |a s| * exp (δ * v) := by ring
  have ha0 : ∀ s ≥ log x₀, a s ≠ 0 := fun s hs =>
    abs_pos.1 (hApos _ ((log_le_iff_le_exp hx₀).1 hs))
  have hK : ∀ s ≥ log x₀, ∀ ξ ∈ Icc (0 : ℝ) 1, |a (s + ξ)| ≤ 2 * exp δ * |a s| := by
    intro s hs ξ hξ
    refine (hPot s hs ξ hξ.1).trans ?_
    have : exp (δ * ξ) ≤ exp δ := exp_le_exp.2 (by nlinarith [hξ.2])
    calc 2 * |a s| * exp (δ * ξ) ≤ 2 * |a s| * exp δ := by gcongr
      _ = 2 * exp δ * |a s| := by ring
  have hB : ∀ u ∈ Icc (0 : ℝ) 2, |boxCox ρ (exp u)| < 3 := by
    intro u hu
    obtain ⟨h1, h2⟩ := boxCox_exp_nonneg_le h.nonpos hu.1
    rw [abs_of_nonneg h1]
    linarith [hu.2]
  obtain ⟨S, hS⟩ := exists_abs_sub_le_of_tendsto hGm hlim hB ha0 hK
  set M := 3 * (1 + 2 * exp δ) with hM
  have hM0 : 0 ≤ M := by positivity
  have hiter := abs_sub_le_sum_of_le hM0 (S := max S (log x₀))
    (fun s hs ξ hξ => hS s ((le_max_left _ _).trans hs) ξ hξ)
  set r := exp δ with hr
  have hr1 : 1 < r := one_lt_exp_iff.2 hδ
  refine ⟨2 * M * r / (r - 1), exp (max S (log x₀)), exp_pos _, fun t ht x hx => ?_⟩
  have ht0 : 0 < t := (exp_pos _).trans_le ht
  have hx0 : 0 < x := one_pos.trans_le hx
  set s := log t with hs
  set u := log x with hu
  have hsS : max S (log x₀) ≤ s := by rw [hs, le_log_iff_exp_le ht0]; exact ht
  have hu0 : 0 ≤ u := log_nonneg hx
  set m := ⌈u⌉₊ with hm
  have hum : u ≤ m := Nat.le_ceil u
  have hmu : (m : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
  have h1 := hiter m s hsS u ⟨hu0, hum⟩
  have h2 : ∑ j ∈ Finset.range m, |a (s + j)| ≤ 2 * |a s| * (r ^ m / (r - 1)) := by
    calc ∑ j ∈ Finset.range m, |a (s + j)|
        ≤ ∑ j ∈ Finset.range m, 2 * |a s| * r ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hr, ← exp_nat_mul, mul_comm (j : ℝ) δ]
          exact hPot s ((le_max_right _ _).trans hsS) j (Nat.cast_nonneg j)
      _ = 2 * |a s| * ((r ^ m - 1) / (r - 1)) := by
          rw [← Finset.mul_sum, geom_sum_eq hr1.ne']
      _ ≤ 2 * |a s| * (r ^ m / (r - 1)) := by
          gcongr
          linarith
  have h3 : r ^ m ≤ r * x ^ δ := by
    rw [hr, ← exp_nat_mul, rpow_def_of_pos hx0, ← exp_add]
    exact exp_le_exp.2 (by rw [← hu]; nlinarith)
  have e1 : G (s + u) - G s = log (U (x * t)) - log (U t) - γ * log x := by
    rw [hGa, hs, hu, exp_log ht0, exp_log hx0]
  have e2 : a s = A t := by simp [ha, hs, exp_log ht0]
  rw [← e1, ← e2]
  calc |G (s + u) - G s| ≤ M * ∑ j ∈ Finset.range m, |a (s + j)| := h1
    _ ≤ M * (2 * |a s| * (r ^ m / (r - 1))) := by gcongr
    _ ≤ M * (2 * |a s| * (r * x ^ δ / (r - 1))) := by gcongr
    _ = 2 * M * r / (r - 1) * |a s| * x ^ δ := by ring

/-- **Uniform bound for second-order regular variation with `ρ < 0`** ([dHF, Theorem 2.3.9]).
If `ρ < 0` and `U`, `A` are measurable, there are `C` and `t₀ > 0` with

  `|log U(xt) - log U(t) - γ log x| ≤ C |A(t)|` for all `t ≥ t₀`, `x ≥ 1`,

uniformly in `x`: since `|A|` decays like `t^ρ`, the remainder no longer grows with `x`. -/
theorem exists_bound_of_neg (h : IsSecondOrderRegularlyVarying U γ ρ A) (hU : Measurable U)
    (hA : Measurable A) (hρ : ρ < 0) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t ≥ t₀, ∀ x ≥ 1,
      |log (U (x * t)) - log (U t) - γ * log x| ≤ C * |A t| := by
  set δ : ℝ := -ρ / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
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
    h.isRegularlyVarying_abs.potter_bound_of_measurable (continuous_abs.measurable.comp hA) hδ
      one_lt_two
  have hPot : ∀ s ≥ log x₀, ∀ v ≥ (0 : ℝ), |a (s + v)| ≤ 2 * |a s| * exp ((ρ + δ) * v) := by
    intro s hs v hv
    have hxs : x₀ ≤ exp s := (log_le_iff_le_exp hx₀).1 hs
    have hxsv : x₀ ≤ exp (s + v) := hxs.trans (exp_le_exp.2 (by linarith))
    have h1 := hP (exp s) hxs (exp (s + v)) hxsv
    have hpos := hApos (exp s) hxs
    rw [div_le_iff₀ hpos] at h1
    have hr : exp (s + v) / exp s = exp v := by rw [exp_add]; field_simp
    rw [hr] at h1
    have hm : max (exp v ^ (ρ + δ)) (exp v ^ (ρ - δ)) ≤ exp ((ρ + δ) * v) := by
      rw [← exp_mul, ← exp_mul]
      refine max_le (exp_le_exp.2 (by rw [mul_comm])) (exp_le_exp.2 ?_)
      nlinarith
    calc |a (s + v)| ≤ 2 * max (exp v ^ (ρ + δ)) (exp v ^ (ρ - δ)) * |a s| := h1
      _ ≤ 2 * exp ((ρ + δ) * v) * |a s| := by gcongr
      _ = 2 * |a s| * exp ((ρ + δ) * v) := by ring
  have hρδ : ρ + δ < 0 := by rw [hδdef]; linarith
  have ha0 : ∀ s ≥ log x₀, a s ≠ 0 := fun s hs =>
    abs_pos.1 (hApos _ ((log_le_iff_le_exp hx₀).1 hs))
  have hK : ∀ s ≥ log x₀, ∀ ξ ∈ Icc (0 : ℝ) 1, |a (s + ξ)| ≤ 2 * |a s| := by
    intro s hs ξ hξ
    refine (hPot s hs ξ hξ.1).trans ?_
    have : exp ((ρ + δ) * ξ) ≤ 1 := exp_le_one_iff.2 (by nlinarith [hξ.1])
    calc 2 * |a s| * exp ((ρ + δ) * ξ) ≤ 2 * |a s| * 1 := by gcongr
      _ = 2 * |a s| := by ring
  have hB : ∀ u ∈ Icc (0 : ℝ) 2, |boxCox ρ (exp u)| < 3 := by
    intro u hu
    obtain ⟨h1, h2⟩ := boxCox_exp_nonneg_le h.nonpos hu.1
    rw [abs_of_nonneg h1]
    linarith [hu.2]
  obtain ⟨S, hS⟩ := exists_abs_sub_le_of_tendsto hGm hlim hB ha0 hK
  set M : ℝ := 3 * (1 + 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hiter := abs_sub_le_sum_of_le hM0 (S := max S (log x₀))
    (fun s hs ξ hξ => hS s ((le_max_left _ _).trans hs) ξ hξ)
  set r := exp (ρ + δ) with hr
  have hr0 : 0 < r := exp_pos _
  have hr1 : r < 1 := exp_lt_one_iff.2 hρδ
  refine ⟨2 * M / (1 - r), exp (max S (log x₀)), exp_pos _, fun t ht x hx => ?_⟩
  have ht0 : 0 < t := (exp_pos _).trans_le ht
  have hx0 : 0 < x := one_pos.trans_le hx
  set s := log t with hs
  set u := log x with hu
  have hsS : max S (log x₀) ≤ s := by rw [hs, le_log_iff_exp_le ht0]; exact ht
  have hu0 : 0 ≤ u := log_nonneg hx
  set m := ⌈u⌉₊ with hm
  have hum : u ≤ m := Nat.le_ceil u
  have h1 := hiter m s hsS u ⟨hu0, hum⟩
  have h2 : ∑ j ∈ Finset.range m, |a (s + j)| ≤ 2 * |a s| * (1 / (1 - r)) := by
    calc ∑ j ∈ Finset.range m, |a (s + j)|
        ≤ ∑ j ∈ Finset.range m, 2 * |a s| * r ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hr, ← exp_nat_mul, mul_comm (j : ℝ) (ρ + δ)]
          exact hPot s ((le_max_right _ _).trans hsS) j (Nat.cast_nonneg j)
      _ = 2 * |a s| * ((1 - r ^ m) / (1 - r)) := by
          rw [← Finset.mul_sum, geom_sum_eq hr1.ne, ← neg_div_neg_eq]
          ring_nf
      _ ≤ 2 * |a s| * (1 / (1 - r)) := by
          gcongr
          linarith [pow_pos hr0 m]
  have e1 : G (s + u) - G s = log (U (x * t)) - log (U t) - γ * log x := by
    rw [hGa, hs, hu, exp_log ht0, exp_log hx0]
  have e2 : a s = A t := by simp [ha, hs, exp_log ht0]
  rw [← e1, ← e2]
  calc |G (s + u) - G s| ≤ M * ∑ j ∈ Finset.range m, |a (s + j)| := h1
    _ ≤ M * (2 * |a s| * (1 / (1 - r))) := by gcongr
    _ = 2 * M / (1 - r) * |a s| := by ring

end IsSecondOrderRegularlyVarying

/-! ### Example: a shifted identity -/

/-- **A shifted identity is second-order regularly varying** ([dHF, §2.3]; a member of
Hall's class): if `U(t) = t + c` eventually, with `c > 0`, then `U` is of second-order regular
variation with `γ = 1`, `ρ = -1` and `A(t) = -c / (t + c)`, since
`(U(xt) / U(t) - x) / A(t) = x - 1 = x · h_{-1}(x)`. For instance `U` is the tail quantile function
of `Y + c` with `Y ∼ Pareto(1, 1)`. -/
theorem isSecondOrderRegularlyVarying_add_const {U : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hU : ∀ᶠ t in atTop, U t = t + c) :
    IsSecondOrderRegularlyVarying U 1 (-1) (fun t => -(c / (t + c))) := by
  have hden : Tendsto (fun t : ℝ => t + c) atTop atTop := tendsto_atTop_add_const_right _ c tendsto_id
  refine ⟨?_, by norm_num, ?_, Or.inr ?_, ⟨?_, fun l hl => ?_⟩, fun x hx => ?_⟩
  · filter_upwards [hU, eventually_gt_atTop 0] with t h ht
    rw [h]; linarith
  · simpa using ((tendsto_const_nhds (x := c)).div_atTop hden).neg
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have : 0 < c / (t + c) := by positivity
    linarith
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have : 0 < c / (t + c) := by positivity
    rw [abs_neg]; exact abs_pos.2 this.ne'
  · -- `|A(lt)| / |A(t)| = (t + c) / (l t + c) → l⁻¹`
    have h : Tendsto (fun t : ℝ => (1 + c * t⁻¹) / (l + c * t⁻¹)) atTop
        (𝓝 ((1 + c * 0) / (l + c * 0))) :=
      ((tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul c))).div
        (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul c)) (by simp [hl.ne'])
    rw [mul_zero, add_zero, add_zero, one_div, ← rpow_neg_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have h1 : 0 < l * t + c := by positivity
    have h2 : 0 < t + c := by positivity
    rw [abs_neg, abs_neg, abs_of_pos (div_pos hc h1), abs_of_pos (div_pos hc h2)]
    field_simp
  · have hlim : x ^ (1 : ℝ) * boxCox (-1) x = x - 1 := by
      rw [boxCox_of_ne (by norm_num), rpow_one, rpow_neg_one]
      field_simp
      ring
    rw [hlim]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hU, (tendsto_id.const_mul_atTop hx).eventually hU, eventually_gt_atTop 0]
      with t ht hxt htpos
    simp only [id] at hxt
    rw [ht, hxt, rpow_one]
    have : t + c ≠ 0 := by linarith
    field_simp
    ring

end ExtremeValueTheory
