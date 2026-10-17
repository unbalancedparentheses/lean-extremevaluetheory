/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.Subexponential
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

/-!
# Tails of linear processes with regularly varying noise

Let `(Z_j)` be iid real random variables with `P(|Z| > x)` regularly varying with index `-α` and
*tail balance* `P(Z > x) / P(|Z| > x) → p`, `q = 1 - p`. For real coefficients `ψ_j`,

  `P(∑ ψ_j Z_j > x) / P(|Z| > x) → ∑ |ψ_j|^α (p 1{ψ_j > 0} + q 1{ψ_j < 0})`.

We follow Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events* (Springer, 1997),
Lemma A3.26 and §5.5 [EKM], Davis and Resnick, *Limit theory for moving averages of random
variables with regularly varying tail probabilities*, Ann. Probab. 13 (1985) [DR85], and Kulik and
Soulier, *Heavy-Tailed Time Series* (Springer, 2020), Chapter 15 [KS20].

## Main results

* `LinearProcess.tendsto_measureReal_add_div`: for independent real `X`, `Y` (no sign condition)
  with `P(X > x) / L(x) → a` and `P(Y > x) / L(x) → b`, `L` regularly varying,
  `P(X + Y > x) / L(x) → a + b`.
* `LinearProcess.tendsto_measureReal_finsetSum_div`: the same for finitely many independent
  summands.
* `LinearProcess.tendsto_measureReal_mul_div`: the tail of `ψ Z`, `P(ψ Z > x) / P(|Z| > x) →
  tailWeight α p ψ = |ψ|^α (p 1{ψ > 0} + q 1{ψ < 0})`.
* `LinearProcess.tendsto_measureReal_sum_mul_div`: the finite moving average
  `P(∑_{j ∈ s} ψ_j Z_j > x) / P(|Z| > x) → ∑_{j ∈ s} tailWeight α p ψ_j` ([EKM, Lemma A3.26],
  [DR85]).

## Proof

For the sum of two independent variables and `0 < ε < 1`,
* `{X + Y > x} ⊆ {X > (1-ε)x} ∪ {Y > (1-ε)x} ∪ {X > εx, Y > εx}`, and the last event has
  probability `P(X > εx) P(Y > εx) = o(L(x))`;
* `{X + Y > x} ⊇ {X > (1+ε)x, |Y| ≤ εx} ⊔ {Y > (1+ε)x, |X| ≤ εx}`, a disjoint union with
  probability `P(X > (1+ε)x) P(|Y| ≤ εx) + P(Y > (1+ε)x) P(|X| ≤ εx)`.
Regular variation of `L` turns these into `limsup ≤ (a + b)(1-ε)^{-α}` and
`liminf ≥ (a + b)(1+ε)^{-α}`; let `ε → 0`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

namespace LinearProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If `F(x) / L(x) → a` with `L` regularly varying with index `-α`, then
`F(c x) / L(x) → a c^{-α}` for `c > 0`. -/
theorem tendsto_comp_mul_div {F L : ℝ → ℝ} {α a : ℝ} (hL : IsRegularlyVarying L (-α))
    (hF : Tendsto (fun x => F x / L x) atTop (𝓝 a)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => F (c * x) / L x) atTop (𝓝 (a * c ^ (-α))) := by
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h1 := hF.comp hcx
  refine (h1.mul (hL.2 c hc)).congr' ?_
  filter_upwards [hL.1, hcx.eventually hL.1] with x hx hcx'
  simp only [Function.comp]
  field_simp

/-- The tail `P(Y > x)` of a random variable tends to `0`. -/
theorem tendsto_measureReal_lt [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) :
    Tendsto (fun x => P.real {ω | x < Y ω}) atTop (𝓝 0) := by
  refine (Subexp.tendsto_tail_atTop (μ := P.map Y)).congr fun x => ?_
  rw [tail, measureReal_def, Measure.map_apply hY measurableSet_Ioi]
  rfl

private theorem measureReal_inter_eq_mul {X Y : Ω → ℝ} (hXY : IndepFun X Y P) {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.real (X ⁻¹' s ∩ Y ⁻¹' t) = P.real (X ⁻¹' s) * P.real (Y ⁻¹' t) := by
  simp only [measureReal_def, hXY.measure_inter_preimage_eq_mul _ _ hs ht, ENNReal.toReal_mul]

/-- Choosing `ε ∈ (0, 1)` with `c (1 + s ε)^{-α}` close to `c`. -/
private theorem exists_eps {c α : ℝ} (s : ℝ) {B : ℝ} (hB : c < B) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ c * (1 + s * ε) ^ (-α) < B ∧ c * (1 - s * ε) ^ (-α) < B := by
  have hcont : ∀ t : ℝ, ContinuousAt (fun ε : ℝ => c * (1 + t * ε) ^ (-α)) 0 := fun t =>
    continuousAt_const.mul ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)
      ).rpow_const (Or.inl (by simp)))
  have h1 := (hcont s).eventually (gt_mem_nhds (show _ < B by simpa using hB))
  have h2 := (hcont (-s)).eventually (gt_mem_nhds (show _ < B by simpa using hB))
  obtain ⟨ε, ⟨h1, h2, h3⟩, h4⟩ := (((h1.and (h2.and (gt_mem_nhds one_pos))).filter_mono
    (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  refine ⟨ε, h4, h3, h1, ?_⟩
  simpa [sub_eq_add_neg] using h2

private theorem exists_eps' {c α : ℝ} {A : ℝ} (hA : A < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ A < c * (1 + ε) ^ (-α) := by
  have hcont : ContinuousAt (fun ε : ℝ => c * (1 + ε) ^ (-α)) 0 :=
    continuousAt_const.mul ((continuousAt_const.add continuousAt_id).rpow_const
      (Or.inl (by simp)))
  have h1 := hcont.eventually (lt_mem_nhds (show A < _ by simpa using hA))
  obtain ⟨ε, ⟨h1, h3⟩, h4⟩ := (((h1.and (gt_mem_nhds one_pos)).filter_mono
    (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  exact ⟨ε, h4, h3, h1⟩

/-- **Tail of a sum of two independent regularly varying variables** ([EKM, Lemma A3.26]).
Let `X`, `Y` be independent real random variables (no sign condition) and `L` regularly varying
with index `-α`, such that `P(X > x) / L(x) → a` and `P(Y > x) / L(x) → b`. Then
`P(X + Y > x) / L(x) → a + b`. -/
theorem tendsto_measureReal_add_div [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y P) {L : ℝ → ℝ} {α : ℝ}
    (hL : IsRegularlyVarying L (-α)) {a b : ℝ}
    (ha : Tendsto (fun x => P.real {ω | x < X ω} / L x) atTop (𝓝 a))
    (hb : Tendsto (fun x => P.real {ω | x < Y ω} / L x) atTop (𝓝 b)) :
    Tendsto (fun x => P.real {ω | x < X ω + Y ω} / L x) atTop (𝓝 (a + b)) := by
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro A hA
    obtain ⟨ε, hε, -, hAε⟩ := exists_eps' (α := α) hA
    have hpos : (0 : ℝ) < 1 + ε := by linarith
    have hXa := tendsto_comp_mul_div hL ha hpos
    have hYb := tendsto_comp_mul_div hL hb hpos
    have hεx : Tendsto (fun x : ℝ => ε * x) atTop atTop := tendsto_id.const_mul_atTop hε
    have hXs := (tendsto_measureReal_lt (P := P) (continuous_abs.measurable.comp hX)).comp hεx
    have hYs := (tendsto_measureReal_lt (P := P) (continuous_abs.measurable.comp hY)).comp hεx
    have hlim : Tendsto (fun x => P.real {ω | (1 + ε) * x < X ω} / L x *
        (1 - P.real {ω | ε * x < |Y ω|}) + P.real {ω | (1 + ε) * x < Y ω} / L x *
        (1 - P.real {ω | ε * x < |X ω|})) atTop (𝓝 ((a + b) * (1 + ε) ^ (-α))) := by
      have := (hXa.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hYs)).add
        (hYb.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hXs))
      simp only [sub_zero, mul_one] at this
      rw [add_mul]
      exact this
    filter_upwards [hlim.eventually (lt_mem_nhds hAε), hL.1, eventually_ge_atTop 0]
      with x hx hLx hx0
    refine hx.trans_le ?_
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right hLx]
    -- the two disjoint events
    set E1 := X ⁻¹' Ioi ((1 + ε) * x) ∩ (fun ω => |Y ω|) ⁻¹' Iic (ε * x)
    set E2 := Y ⁻¹' Ioi ((1 + ε) * x) ∩ (fun ω => |X ω|) ⁻¹' Iic (ε * x)
    have hcompl : ∀ (W : Ω → ℝ), Measurable W →
        P.real ((fun ω => |W ω|) ⁻¹' Iic (ε * x)) = 1 - P.real {ω | ε * x < |W ω|} := by
      intro W hW
      have hm : MeasurableSet {ω | ε * x < |W ω|} :=
        measurableSet_lt measurable_const (continuous_abs.measurable.comp hW)
      rw [← probReal_compl_eq_one_sub hm]
      congr 1
      ext ω; simp
    have hE1 : P.real E1 = P.real {ω | (1 + ε) * x < X ω} * (1 - P.real {ω | ε * x < |Y ω|}) := by
      have h := measureReal_inter_eq_mul (P := P) (X := X) (Y := fun ω => |Y ω|)
        (hXY.comp measurable_id continuous_abs.measurable) (measurableSet_Ioi (a := (1 + ε) * x))
        (measurableSet_Iic (a := ε * x))
      exact h.trans (by rw [hcompl Y hY]; rfl)
    have hE2 : P.real E2 = P.real {ω | (1 + ε) * x < Y ω} * (1 - P.real {ω | ε * x < |X ω|}) := by
      have h := measureReal_inter_eq_mul (P := P) (X := Y) (Y := fun ω => |X ω|)
        (hXY.symm.comp measurable_id continuous_abs.measurable)
        (measurableSet_Ioi (a := (1 + ε) * x)) (measurableSet_Iic (a := ε * x))
      exact h.trans (by rw [hcompl X hX]; rfl)
    have hdisj : Disjoint E1 E2 := by
      rw [Set.disjoint_left]
      rintro ω ⟨h1, -⟩ ⟨-, h2⟩
      simp only [mem_preimage, mem_Ioi, mem_Iic] at h1 h2
      have := le_abs_self (X ω)
      nlinarith
    have hE2m : MeasurableSet E2 :=
      (hY measurableSet_Ioi).inter ((continuous_abs.measurable.comp hX) measurableSet_Iic)
    have hsub : E1 ∪ E2 ⊆ {ω | x < X ω + Y ω} := by
      rintro ω (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
        simp only [mem_preimage, mem_Ioi, mem_Iic] at h1 h2 <;> simp only [mem_ofPred_eq]
      · have := neg_abs_le (Y ω); linarith
      · have := neg_abs_le (X ω); linarith
    rw [← hE1, ← hE2, ← measureReal_union hdisj hE2m]
    exact measureReal_mono hsub
  · -- upper bound
    intro B hB
    obtain ⟨ε, hε, hε1, -, hBε⟩ := exists_eps (c := a + b) (α := α) 1 hB
    rw [one_mul] at hBε
    have hpos : (0 : ℝ) < 1 - ε := by linarith
    have hXa := tendsto_comp_mul_div hL ha hpos
    have hYb := tendsto_comp_mul_div hL hb hpos
    have hXe := tendsto_comp_mul_div hL ha hε
    have hεx : Tendsto (fun x : ℝ => ε * x) atTop atTop := tendsto_id.const_mul_atTop hε
    have hYs := (tendsto_measureReal_lt (P := P) hY).comp hεx
    have hlim : Tendsto (fun x => P.real {ω | (1 - ε) * x < X ω} / L x +
        P.real {ω | (1 - ε) * x < Y ω} / L x +
        P.real {ω | ε * x < X ω} / L x * P.real {ω | ε * x < Y ω}) atTop
        (𝓝 ((a + b) * (1 - ε) ^ (-α))) := by
      have := (hXa.add hYb).add (hXe.mul hYs)
      simp only [mul_zero, add_zero] at this
      rw [add_mul]
      exact this
    filter_upwards [hlim.eventually (gt_mem_nhds hBε), hL.1] with x hx hLx
    refine lt_of_le_of_lt ?_ hx
    rw [div_mul_eq_mul_div, ← add_div, ← add_div, div_le_div_iff_of_pos_right hLx]
    have hsub : {ω | x < X ω + Y ω} ⊆ ({ω | (1 - ε) * x < X ω} ∪ {ω | (1 - ε) * x < Y ω}) ∪
        (X ⁻¹' Ioi (ε * x) ∩ Y ⁻¹' Ioi (ε * x)) := by
      intro ω hω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage, mem_Ioi] at hω ⊢
      by_contra h
      push Not at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      by_cases hXε : ε * x < X ω
      · have := h3 hXε; linarith
      · linarith
    calc P.real {ω | x < X ω + Y ω}
        ≤ P.real (({ω | (1 - ε) * x < X ω} ∪ {ω | (1 - ε) * x < Y ω}) ∪
          (X ⁻¹' Ioi (ε * x) ∩ Y ⁻¹' Ioi (ε * x))) := measureReal_mono hsub
      _ ≤ P.real {ω | (1 - ε) * x < X ω} + P.real {ω | (1 - ε) * x < Y ω} +
          P.real (X ⁻¹' Ioi (ε * x) ∩ Y ⁻¹' Ioi (ε * x)) :=
        (measureReal_union_le _ _).trans (by gcongr; exact measureReal_union_le _ _)
      _ = _ := by
        rw [measureReal_inter_eq_mul hXY measurableSet_Ioi measurableSet_Ioi]
        rfl

end LinearProcess

end ExtremeValueTheory
