/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic

/-!
# Breiman's lemma

Let `X` and `Y` be independent real random variables, where the survival function
`F̄ x = P(X > x)` of `X` is regularly varying with index `-α`, `α > 0`, and `Y ≥ 0` has a
finite moment of order `α + ε` for some `ε > 0`. **Breiman's lemma** (Breiman 1965; see also
Jessen and Mikosch, *Regularly varying functions*, 2006, Lemma 4.2(1)) states that

  `P(X * Y > x) / P(X > x) → E[Y ^ α]` as `x → ∞`.

## Main results

* `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_div`: the analytic core. If `F` is
  antitone and regularly varying with index `-α`, `α > 0`, and `μ` is a finite measure on
  `[0, ∞)` with `∫ y ^ (α + ε) dμ < ∞`, then
  `(∫ y, (if 0 < y then F (x / y) else 0) ∂μ) / F x → ∫ y, y ^ α ∂μ`.
* `ExtremeValueTheory.tendsto_measure_mul_div_measure`: Breiman's lemma.

## Proof

Conditioning on `Y` (independence makes the joint law a product measure) gives
`P(X * Y > x) = ∫ F̄ (x / y) dP_Y(y)` for `x > 0`. The integrand divided by `F̄ x` tends to
`y ^ α` pointwise. For domination, the Potter bounds give, with `0 < δ ≤ ε`, `δ < α`,
* `F̄ (x / y) / F̄ x ≤ 2 * max (y ^ (α - δ)) (y ^ (α + δ))` when `x, x / y ≥ x₀`;
* `F̄ x ≥ F̄ x₀ / 2 * (x / x₀) ^ (-(α + δ))` for `x ≥ x₀`, so that when `x / y < x₀`,
  `F̄ (x / y) / F̄ x ≤ 2 * F̄ 0 / F̄ x₀ * y ^ (α + δ)`.
Both bounds are at most a constant times `1 + y ^ (α + ε)`, which is `P_Y`-integrable, and
dominated convergence concludes.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-- An antitone, eventually positive function is positive everywhere. -/
private lemma pos_of_antitone' {F : ℝ → ℝ} (hF : Antitone F) (hpos : ∀ᶠ x in atTop, 0 < F x)
    (t : ℝ) : 0 < F t := by
  obtain ⟨s, hs, hts⟩ := (hpos.and (eventually_ge_atTop t)).exists
  exact hs.trans_le (hF hts)

private lemma rpow_le_one_add_rpow {y p q : ℝ} (hy : 0 < y) (hp : 0 ≤ p) (hpq : p ≤ q) :
    y ^ p ≤ 1 + y ^ q := by
  rcases le_total y 1 with h | h
  · have := rpow_le_one hy.le h hp
    have := rpow_nonneg hy.le q
    linarith
  · have := rpow_le_rpow_of_exponent_le h hpq
    linarith

namespace IsRegularlyVarying

variable {F : ℝ → ℝ} {α : ℝ}

/-- **Analytic core of Breiman's lemma.** Let `F` be antitone and regularly varying with index
`-α`, `α > 0`, and let `μ` be a finite measure concentrated on `[0, ∞)` such that
`y ↦ y ^ (α + ε)` is `μ`-integrable for some `ε > 0`. Then
`(∫ y, (if 0 < y then F (x / y) else 0) ∂μ) / F x → ∫ y, y ^ α ∂μ` as `x → ∞`. -/
theorem tendsto_integral_div (hF : Antitone F) (hRV : IsRegularlyVarying F (-α)) (hα : 0 < α)
    {ε : ℝ} (hε : 0 < ε) {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : ∀ᵐ y ∂μ, 0 ≤ y)
    (hint : Integrable (fun y => y ^ (α + ε)) μ) :
    Tendsto (fun x => (∫ y, (if 0 < y then F (x / y) else 0) ∂μ) / F x) atTop
      (𝓝 (∫ y, y ^ α ∂μ)) := by
  set δ := min ε α / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; have := lt_min hε hα; linarith
  have hδε : δ ≤ ε := by rw [hδ_def]; have := min_le_left ε α; linarith
  have hδα : δ < α := by rw [hδ_def]; have := min_le_right ε α; linarith
  obtain ⟨x₀, hx₀, -, hP⟩ :=
    hRV.potter_bound (a := 0) (Or.inr (hF.antitoneOn _)) hδ one_lt_two
  have hFpos := pos_of_antitone' hF hRV.1
  have hFm : Measurable F := hF.measurable
  set K := 2 * F 0 / F x₀ + 2 with hK_def
  have hK0 : 0 ≤ 2 * F 0 / F x₀ := by have := hFpos 0; have := hFpos x₀; positivity
  -- Lower bound on `F`.
  have hlow : ∀ x ≥ x₀, F x₀ / F x ≤ 2 * (x / x₀) ^ (α + δ) := by
    intro x hx
    have hx0 : 0 < x := hx₀.trans_le hx
    have h := hP x hx x₀ le_rfl
    have ht0 : 0 < x₀ / x := div_pos hx₀ hx0
    have ht1 : x₀ / x ≤ 1 := (div_le_one hx0).2 hx
    rw [max_eq_right (rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith))] at h
    rwa [show -α - δ = -(α + δ) by ring, rpow_neg ht0.le, ← inv_rpow ht0.le, inv_div] at h
  rw [show (fun x => (∫ y, (if 0 < y then F (x / y) else 0) ∂μ) / F x) =
      fun x => ∫ y, (if 0 < y then F (x / y) else 0) / F x ∂μ from
    funext fun x => (integral_div _ _).symm]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => K * (1 + y ^ (α + ε)))
    ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun x => ?_
    exact ((Measurable.ite measurableSet_Ioi (hFm.comp (measurable_const.div measurable_id))
      measurable_const).div_const _).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop x₀] with x hx
    filter_upwards [hμ] with y hy
    have hx0 : 0 < x := hx₀.trans_le hx
    have hFx := hFpos x
    have hKb : 0 ≤ 1 + y ^ (α + ε) := by have := rpow_nonneg hy (α + ε); linarith
    rcases hy.eq_or_lt with h0 | hy0
    · subst h0
      simp only [lt_irrefl, ↓reduceIte, zero_div, norm_zero]
      exact mul_nonneg (by linarith) hKb
    simp only [hy0, ↓reduceIte]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (hFpos _) hFx)]
    rcases le_or_gt x₀ (x / y) with hxy | hxy
    · have h := hP x hx (x / y) hxy
      have hinv : ∀ p : ℝ, (x / y / x) ^ p = y ^ (-p) := fun p => by
        rw [div_div_cancel_left' hx0.ne', inv_rpow hy0.le, rpow_neg hy0.le]
      rw [hinv, hinv, show -(-α + δ) = α - δ by ring, show -(-α - δ) = α + δ by ring] at h
      have hm : max (y ^ (α - δ)) (y ^ (α + δ)) ≤ 1 + y ^ (α + ε) :=
        max_le (rpow_le_one_add_rpow hy0 (by linarith) (by linarith))
          (rpow_le_one_add_rpow hy0 (by linarith) (by linarith))
      calc F (x / y) / F x ≤ 2 * max (y ^ (α - δ)) (y ^ (α + δ)) := h
        _ ≤ 2 * (1 + y ^ (α + ε)) := by linarith
        _ ≤ K * (1 + y ^ (α + ε)) :=
          mul_le_mul_of_nonneg_right (by rw [hK_def]; linarith) hKb
    · have hF0 : F (x / y) ≤ F 0 := hF (div_pos hx0 hy0).le
      have hxx : x / x₀ ≤ y := by
        rw [div_lt_iff₀ hy0] at hxy
        rw [div_le_iff₀ hx₀]; linarith
      have h1 := hlow x hx
      have h2 : (x / x₀) ^ (α + δ) ≤ y ^ (α + δ) :=
        rpow_le_rpow (div_pos hx0 hx₀).le hxx (by linarith)
      have h3 : y ^ (α + δ) ≤ 1 + y ^ (α + ε) :=
        rpow_le_one_add_rpow hy0 (by linarith) (by linarith)
      have hFx0 := hFpos x₀
      have e : F (x / y) / F x = F (x / y) / F x₀ * (F x₀ / F x) := by
        field_simp
      calc F (x / y) / F x = F (x / y) / F x₀ * (F x₀ / F x) := e
        _ ≤ F 0 / F x₀ * (2 * (1 + y ^ (α + ε))) := by
          apply mul_le_mul (div_le_div_of_nonneg_right hF0 hFx0.le) (by linarith)
            (div_pos hFx0 hFx).le (div_pos (hFpos 0) hFx0).le
        _ = 2 * F 0 / F x₀ * (1 + y ^ (α + ε)) := by ring
        _ ≤ K * (1 + y ^ (α + ε)) :=
          mul_le_mul_of_nonneg_right (by rw [hK_def]; linarith) hKb
  · exact ((integrable_const 1).add hint).const_mul K
  · filter_upwards [hμ] with y hy
    rcases hy.eq_or_lt with h0 | hy0
    · subst h0
      simp only [lt_irrefl, ↓reduceIte, zero_div, zero_rpow hα.ne']
      exact tendsto_const_nhds
    simp only [hy0, ↓reduceIte]
    have h := hRV.2 y⁻¹ (inv_pos.2 hy0)
    rw [rpow_neg (inv_pos.2 hy0).le, inv_rpow hy0.le, inv_inv] at h
    exact h.congr fun x => by rw [div_eq_inv_mul x y]

end IsRegularlyVarying

/-- **Breiman's lemma** (Breiman 1965; Jessen–Mikosch 2006, Lemma 4.2(1)). Let `X` and `Y` be
independent real random variables on a probability space, such that the survival function
`x ↦ P(X > x)` of `X` is regularly varying with index `-α`, `α > 0`, and `Y ≥ 0` almost surely
with `E[Y ^ (α + ε)] < ∞` for some `ε > 0`. Then `P(X * Y > x) / P(X > x) → E[Y ^ α]`.

(No sign condition on `X` is needed: for `x > 0` only the positive part of `X` matters.) -/
theorem tendsto_measure_mul_div_measure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X ω}).toReal) (-α))
    (hmom : Integrable (fun ω => Y ω ^ (α + ε)) P) :
    Tendsto (fun x => (P {ω | x < X ω * Y ω}).toReal / (P {ω | x < X ω}).toReal) atTop
      (𝓝 (∫ ω, Y ω ^ α ∂P)) := by
  set F : ℝ → ℝ := fun x => (P {ω | x < X ω}).toReal with hF_def
  have hFanti : Antitone F := by
    intro a b hab
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    exact lt_of_le_of_lt hab hω
  set μ := P.map Y with hμ_def
  have hμ : ∀ᵐ y ∂μ, 0 ≤ y := (ae_map_iff hY.aemeasurable measurableSet_Ici).2 hY0
  have hint : Integrable (fun y => y ^ (α + ε)) μ :=
    (integrable_map_measure (continuous_id.rpow_const fun _ => Or.inr (by linarith)
      ).measurable.aestronglyMeasurable hY.aemeasurable).2 hmom
  have hcore := IsRegularlyVarying.tendsto_integral_div hFanti hRV hα hε hμ hint
  have hlim : ∫ y, y ^ α ∂μ = ∫ ω, Y ω ^ α ∂P :=
    integral_map hY.aemeasurable (continuous_id.rpow_const fun _ => Or.inr hα.le
      ).measurable.aestronglyMeasurable
  rw [hlim] at hcore
  refine hcore.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  congr 1
  -- Conditioning on `Y`.
  set S : Set (ℝ × ℝ) := {p | x < p.1 * p.2} with hS_def
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_fst.mul measurable_snd)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have h1 : P {ω | x < X ω * Y ω} = ∫⁻ y, (P.map X) ((fun a => (a, y)) ⁻¹' S) ∂μ := by
    rw [← Measure.prod_apply_symm hS, ← hprod, Measure.map_apply (hX.prodMk hY) hS]
    rfl
  rw [h1, ← integral_toReal (measurable_measure_prodMk_right hS).aemeasurable
    (Eventually.of_forall fun _ => measure_lt_top _ _)]
  refine integral_congr_ae ?_
  filter_upwards [hμ] with y hy
  rcases hy.eq_or_lt with h0 | hy0
  · subst h0
    have : (fun a : ℝ => (a, (0 : ℝ))) ⁻¹' S = ∅ := by
      ext a; simp [hS_def, hx.not_gt]
    simp [this]
  · have : (fun a : ℝ => (a, y)) ⁻¹' S = Ioi (x / y) := by
      ext a; simp [hS_def, div_lt_iff₀ hy0]
    simp only [hy0, ↓reduceIte]
    rw [this, Measure.map_apply hX measurableSet_Ioi]
    rfl

end ExtremeValueTheory
