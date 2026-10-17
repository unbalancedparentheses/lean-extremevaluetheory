/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.RandomSums
import ExtremeValueTheory.RegularVariation.Karamata

/-!
# Ruin probabilities with subexponential claims

In the Cramér–Lundberg model with claim size distribution `F` (on `[0, ∞)`, mean `m`) and safety
loading `ρ > 0`, the **Pollaczek–Khinchine formula** ([EKM, Theorem 1.2.2 / (1.11)]) expresses
the ruin probability as a geometric compound of the *integrated tail distribution*
`F_I(x) = m⁻¹ ∫₀ˣ F̄(y) dy`:

  `ψ(u) = (1 - p) ∑ₙ pⁿ F̄_I^{*n}(u)`, `p = 1 / (1 + ρ)`.

We take the right-hand side as the definition `pkRuin ρ F_I u` (deriving it from the risk
process is outside the scope of this file), and prove the **Embrechts–Veraverbeke theorem**
([EKM, Theorem 1.3.6]): if `F_I` is subexponential, then `ψ(u) / F̄_I(u) → ρ⁻¹`.

Combined with Karamata's theorem (`IsRegularlyVarying.tendsto_integral_Ioi_div`), claims with
regularly varying tails `F̄ ∈ RV_{-α}`, `α > 1`, have a subexponential integrated tail and
`ψ(u) ~ (ρ m)⁻¹ ∫ᵤ^∞ F̄ ~ u F̄(u) / (ρ m (α - 1))` ([EKM, Example 1.3.8]).

## Main definitions

* `ExtremeValueTheory.pkRuin ρ ν u`: the Pollaczek–Khinchine geometric compound.
* `ExtremeValueTheory.integratedTail μ`: the integrated tail distribution `F_I`, with density
  `F̄(y) / m` on `(0, ∞)`, where `m = ∫₀^∞ F̄`.

## Main results

* `IsSubexponential.tendsto_geometric_compound_div`: `(1 - q) ∑ qⁿ F̄^{*n}(u) / F̄(u) → q/(1 - q)`.
* `IsSubexponential.tendsto_pkRuin_div`: **Embrechts–Veraverbeke**, `ψ(u) / F̄_I(u) → 1/ρ`.
* `isSubexponential_integratedTail_of_isRegularlyVarying`, `tendsto_pkRuin_div_integral`,
  `tendsto_pkRuin_div_mul_tail`: the regularly varying case.

Here [EKM] is Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events for Insurance and
Finance* (Springer, 1997).
-/

open Filter Topology Set Real MeasureTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

open Subexp

/-- The Pollaczek–Khinchine geometric compound
`ψ(u) = (1 - p) ∑ₙ pⁿ F̄_I^{*n}(u)` with `p = 1 / (1 + ρ)`, i.e. `1 - p = ρ / (1 + ρ)`. By the
Pollaczek–Khinchine formula ([EKM, Theorem 1.2.2]) this is the ruin probability with initial
capital `u` in the Cramér–Lundberg model with safety loading `ρ` and integrated tail law `ν`. -/
noncomputable def pkRuin (ρ : ℝ) (ν : Measure ℝ) (u : ℝ) : ℝ :=
  ρ / (1 + ρ) * ∑' n : ℕ, (1 / (1 + ρ)) ^ n * tail (Subexp.convPow ν n) u

namespace IsSubexponential

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- **Geometric compounds of subexponential laws ([EKM, Theorem A3.20] with geometric `N`).**
For `0 ≤ q < 1`, `((1 - q) ∑ₙ qⁿ F̄^{*n}(u)) / F̄(u) → q / (1 - q)`. -/
theorem tendsto_geometric_compound_div (h : IsSubexponential μ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Tendsto (fun u => ((1 - q) * ∑' n : ℕ, q ^ n * tail (Subexp.convPow μ n) u) / tail μ u)
      atTop (𝓝 (q / (1 - q))) := by
  set ε := (1 - q) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hr0 : 0 ≤ q * (1 + ε) := by positivity
  have hr1 : q * (1 + ε) < 1 := by rw [hε_def]; nlinarith
  have hs : Summable fun n : ℕ => (1 - q) * q ^ n * (1 + ε) ^ n := by
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (1 - q)).congr fun n => ?_
    rw [mul_pow, mul_assoc]
  have h1 := h.tendsto_tsum_tail_convPow_div (p := fun n => (1 - q) * q ^ n)
    (fun n => by have := pow_nonneg hq0 n; nlinarith) hε hs
  have hsum : ∑' n : ℕ, (n : ℝ) * ((1 - q) * q ^ n) = q / (1 - q) := by
    have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
    have hne : (1 - q) ≠ 0 := by linarith
    have e : ∀ n : ℕ, (n : ℝ) * ((1 - q) * q ^ n) = (1 - q) * (n * q ^ n) := fun n => by ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hq]
    field_simp
  rw [hsum] at h1
  refine h1.congr fun u => ?_
  rw [← tsum_mul_left]
  simp_rw [mul_assoc]

/-- **Embrechts–Veraverbeke theorem ([EKM, Theorem 1.3.6]).** If the integrated tail law `ν` is
subexponential and the safety loading is `ρ > 0`, then the Pollaczek–Khinchine ruin probability
satisfies `ψ(u) / F̄_I(u) → 1 / ρ` as `u → ∞`. -/
theorem tendsto_pkRuin_div (h : IsSubexponential μ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun u => pkRuin ρ μ u / tail μ u) atTop (𝓝 (1 / ρ)) := by
  have hq0 : 0 ≤ 1 / (1 + ρ) := by positivity
  have hq1 : 1 / (1 + ρ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h1 := h.tendsto_geometric_compound_div hq0 hq1
  have e1 : 1 - 1 / (1 + ρ) = ρ / (1 + ρ) := by field_simp; ring
  have e2 : 1 / (1 + ρ) / (1 - 1 / (1 + ρ)) = 1 / ρ := by rw [e1]; field_simp
  rw [e2, e1] at h1
  exact h1

end IsSubexponential

/-- If `f / g → L > 0` and `g` is regularly varying with index `ρ`, then so is `f`. -/
theorem IsRegularlyVarying.of_tendsto_div {f g : ℝ → ℝ} {ρ L : ℝ} (hg : IsRegularlyVarying g ρ)
    (hfg : Tendsto (fun x => f x / g x) atTop (𝓝 L)) (hL : 0 < L) : IsRegularlyVarying f ρ := by
  have hpos : ∀ᶠ x in atTop, 0 < f x := by
    filter_upwards [(tendsto_order.1 hfg).1 0 hL, hg.1] with x h1 h2
    exact (div_pos_iff_of_pos_right h2).1 h1
  refine ⟨hpos, fun c hc => ?_⟩
  have hcx : Tendsto (fun x => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h := ((hfg.comp hcx).mul (hg.2 c hc)).div hfg hL.ne'
  rw [mul_div_cancel_left₀ _ hL.ne'] at h
  refine h.congr' ?_
  filter_upwards [hg.1, hcx.eventually hg.1, hpos] with x h1 h2 h3
  simp only [Function.comp_apply, Pi.div_apply]
  field_simp

/-- The **integrated tail distribution** `F_I` of `μ` ([EKM, §1.3.3]): the law with density
`F̄(y) / m` on `(0, ∞)`, where `m = ∫₀^∞ F̄(y) dy` is the mean of `μ` (for `μ` on `[0, ∞)`). -/
noncomputable def integratedTail (μ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (∫ t in Ioi 0, tail μ t)⁻¹ •
    (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (tail μ t)

section IntegratedTail

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem integratedTail_apply_aux (hint : IntegrableOn (tail μ) (Ioi 0)) {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    integratedTail μ s = ENNReal.ofReal ((∫ t in Ioi 0, tail μ t)⁻¹ * ∫ t in s, tail μ t) := by
  rw [integratedTail, Measure.smul_apply, withDensity_apply _ hs, Measure.restrict_restrict hs,
    inter_eq_left.2 hs0, ← ofReal_integral_eq_lintegral_ofReal (hint.mono_set hs0)
      (ae_of_all _ fun t => tail_nonneg t), smul_eq_mul, ← ENNReal.ofReal_mul]
  exact inv_nonneg.2 (setIntegral_nonneg measurableSet_Ioi fun t _ => tail_nonneg t)

omit [IsProbabilityMeasure μ] in
/-- `F_I` is a probability measure when `0 < m = ∫₀^∞ F̄ < ∞`. -/
theorem isProbabilityMeasure_integratedTail (hint : IntegrableOn (tail μ) (Ioi 0))
    (hm : 0 < ∫ t in Ioi 0, tail μ t) : IsProbabilityMeasure (integratedTail μ) := by
  constructor
  rw [integratedTail, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun t => tail_nonneg t), smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hm.le),
    inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one]

omit [IsProbabilityMeasure μ] in
theorem integratedTail_Iio_zero : integratedTail μ (Iio 0) = 0 := by
  rw [integratedTail, Measure.smul_apply, withDensity_apply _ measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, Ioo_self, Measure.restrict_empty,
    lintegral_zero_measure, smul_zero]

omit [IsProbabilityMeasure μ] in
/-- The tail of the integrated tail law: `F̄_I(u) = m⁻¹ ∫ᵤ^∞ F̄` for `u ≥ 0`. -/
theorem tail_integratedTail (hint : IntegrableOn (tail μ) (Ioi 0)) {u : ℝ} (hu : 0 ≤ u) :
    tail (integratedTail μ) u = (∫ t in Ioi 0, tail μ t)⁻¹ * ∫ t in Ioi u, tail μ t := by
  rw [tail, measureReal_def, integratedTail_apply_aux hint measurableSet_Ioi
    (Ioi_subset_Ioi hu), ENNReal.toReal_ofReal]
  exact mul_nonneg (inv_nonneg.2 (setIntegral_nonneg measurableSet_Ioi fun t _ => tail_nonneg t))
    (setIntegral_nonneg measurableSet_Ioi fun t _ => tail_nonneg t)

variable {α : ℝ}

/-- For `F̄ ∈ RV_{-α}`, `α > 1`, the mean `m = ∫₀^∞ F̄` is finite and positive. -/
theorem integral_tail_pos_of_isRegularlyVarying (hRV : IsRegularlyVarying (tail μ) (-α))
    (hα : 1 < α) : 0 < ∫ t in Ioi 0, tail μ t := by
  have hK := IsRegularlyVarying.tendsto_integral_Ioi_div tail_antitone hRV hα
  have hpos := IsRegularlyVarying.pos_of_antitone tail_antitone hRV.1
  have hα1 : 0 < 1 / (α - 1) := one_div_pos.2 (by linarith)
  obtain ⟨x, hx, hx0⟩ :=
    (((tendsto_order.1 hK).1 0 hα1).and (eventually_gt_atTop (0 : ℝ))).exists
  have hIx : 0 < ∫ t in Ioi x, tail μ t :=
    (div_pos_iff_of_pos_right (mul_pos hx0 (hpos x))).1 hx
  refine hIx.trans_le (setIntegral_mono_set
    (IsRegularlyVarying.integrableOn_Ioi tail_antitone hRV hα 0)
    (ae_of_all _ fun t => tail_nonneg t) (Eventually.of_forall (Ioi_subset_Ioi hx0.le)))

/-- **Integrated tails of regularly varying laws are regularly varying.** If `F̄ ∈ RV_{-α}`
with `α > 1`, then `F̄_I ∈ RV_{-(α - 1)}`, with `F̄_I(u) / (u F̄(u)) → 1 / (m (α - 1))`
(Karamata's theorem). -/
theorem tendsto_tail_integratedTail_div (hRV : IsRegularlyVarying (tail μ) (-α)) (hα : 1 < α) :
    Tendsto (fun u => tail (integratedTail μ) u / (u * tail μ u)) atTop
      (𝓝 ((∫ t in Ioi 0, tail μ t)⁻¹ * (1 / (α - 1)))) := by
  have hK := IsRegularlyVarying.tendsto_integral_Ioi_div tail_antitone hRV hα
  have hint := IsRegularlyVarying.integrableOn_Ioi tail_antitone hRV hα 0
  refine (hK.const_mul _).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [tail_integratedTail hint hu, mul_div_assoc]

theorem isRegularlyVarying_tail_integratedTail (hRV : IsRegularlyVarying (tail μ) (-α))
    (hα : 1 < α) : IsRegularlyVarying (tail (integratedTail μ)) (-(α - 1)) := by
  have hg : IsRegularlyVarying (fun u => u * tail μ u) (-(α - 1)) := by
    have := (IsRegularlyVarying.rpow_id 1).mul hRV
    rw [show (1 : ℝ) + -α = -(α - 1) by ring] at this
    exact this.congr (Eventually.of_forall fun u => by simp)
  refine IsRegularlyVarying.of_tendsto_div hg (tendsto_tail_integratedTail_div hRV hα) ?_
  have := integral_tail_pos_of_isRegularlyVarying hRV hα
  have : 0 < α - 1 := by linarith
  positivity

/-- **Regularly varying claims have a subexponential integrated tail** ([EKM, Corollary 1.3.2
and §1.3.3]). -/
theorem isSubexponential_integratedTail_of_isRegularlyVarying (hRV : IsRegularlyVarying (tail μ) (-α)) (hα : 1 < α) :
    IsSubexponential (integratedTail μ) := by
  have := isProbabilityMeasure_integratedTail
    (IsRegularlyVarying.integrableOn_Ioi tail_antitone hRV hα 0)
    (integral_tail_pos_of_isRegularlyVarying hRV hα)
  exact IsSubexponential.of_isRegularlyVarying integratedTail_Iio_zero
    (isRegularlyVarying_tail_integratedTail hRV hα)

/-- **Ruin with regularly varying claims, integrated form ([EKM, Theorem 1.3.6 and
Example 1.3.8]).** If `F̄ ∈ RV_{-α}`, `α > 1`, and `ρ > 0`, then
`ψ(u) ~ (ρ m)⁻¹ ∫ᵤ^∞ F̄(y) dy`, where `m = ∫₀^∞ F̄` is the mean claim size. -/
theorem tendsto_pkRuin_div_integral (hRV : IsRegularlyVarying (tail μ) (-α)) (hα : 1 < α) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun u => pkRuin ρ (integratedTail μ) u /
      ((ρ * ∫ t in Ioi 0, tail μ t)⁻¹ * ∫ t in Ioi u, tail μ t)) atTop (𝓝 1) := by
  have := isProbabilityMeasure_integratedTail
    (IsRegularlyVarying.integrableOn_Ioi tail_antitone hRV hα 0)
    (integral_tail_pos_of_isRegularlyVarying hRV hα)
  have h := ((isSubexponential_integratedTail_of_isRegularlyVarying hRV hα).tendsto_pkRuin_div
    hρ).const_mul ρ
  rw [mul_one_div_cancel hρ.ne'] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [tail_integratedTail (IsRegularlyVarying.integrableOn_Ioi tail_antitone hRV hα 0) hu,
    mul_inv]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- **Ruin with regularly varying claims ([EKM, Example 1.3.8]).** If `F̄ ∈ RV_{-α}`, `α > 1`,
and `ρ > 0`, then `ψ(u) ~ u F̄(u) / (ρ m (α - 1))`, where `m = ∫₀^∞ F̄` is the mean claim size:
`ψ(u) / (u F̄(u)) → 1 / (ρ m (α - 1))`. -/
theorem tendsto_pkRuin_div_mul_tail (hRV : IsRegularlyVarying (tail μ) (-α)) (hα : 1 < α) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun u => pkRuin ρ (integratedTail μ) u / (u * tail μ u)) atTop
      (𝓝 (1 / (ρ * (∫ t in Ioi 0, tail μ t) * (α - 1)))) := by
  have := isProbabilityMeasure_integratedTail
    (IsRegularlyVarying.integrableOn_Ioi tail_antitone hRV hα 0)
    (integral_tail_pos_of_isRegularlyVarying hRV hα)
  have hS := isSubexponential_integratedTail_of_isRegularlyVarying hRV hα
  have h := (hS.tendsto_pkRuin_div hρ).mul (tendsto_tail_integratedTail_div hRV hα)
  have hm := integral_tail_pos_of_isRegularlyVarying hRV hα
  have hα1 : α - 1 ≠ 0 := by linarith
  rw [show 1 / ρ * ((∫ t in Ioi 0, tail μ t)⁻¹ * (1 / (α - 1))) =
    1 / (ρ * (∫ t in Ioi 0, tail μ t) * (α - 1)) by field_simp] at h
  refine h.congr fun u => ?_
  rw [div_mul_div_cancel₀ (hS.tail_pos u).ne']

end IntegratedTail

end ExtremeValueTheory
