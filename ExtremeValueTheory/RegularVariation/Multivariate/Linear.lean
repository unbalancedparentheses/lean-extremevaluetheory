/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TailProcess
import Mathlib.Topology.Algebra.Module.Cardinality
import ExtremeValueTheory.RegularVariation.Multivariate.Polar

/-!
# Multivariate regular variation: linear combinations and full dependence

Linear combinations of a regularly varying vector (the "⇒" half of the Cramér–Wold device
of [BDM02]): `P(L X > x) / P(‖X‖ > x) → μ {L > 1}`. Examples: the exponent measure is supported in
any closed cone containing `X`, the fully dependent vector `X = (Z, Z)` has its exponent
measure on the diagonal, and independent components give an exponent measure on the axes.

## Main results

* `IsRegVarVector.tendsto_linear`: **Tails of linear combinations** ([BDM02, Theorem 1.1, "⇒"],
  [Res07, §6.5]): if `X` is regularly varying with exponent measure `μ`, then for every continuous
  linear functional `L`, `P(L X > x) / P(‖X‖ > x) → μ {y | L y > 1}`.
* `IsRegVarVector.tendsto_inner`: **Tails of linear combinations, inner product form**: `P(⟪c, X⟫ >
  x) / P(‖X‖ > x) → μ {y | ⟪c, y⟫ > 1}`.
* `IsRegVarVector.measure_compl_eq_zero`: **Support of the exponent measure in a closed cone**: if
  `X` takes values in a closed cone `C` (stable under multiplication by positive scalars), the
  exponent measure is concentrated on `C`.
* `IsRegVarVector.measure_offDiag_eq_zero`: **Full asymptotic dependence**: for `X = (Z, Z)`, the
  exponent measure is concentrated on the diagonal.
* `IsRegVarVector.measure_ne_zero_ne_zero_eq_zero`: **Asymptotic independence** ([Res07, §6.5.1]):
  if `X = (X₁, X₂)` has independent components and is regularly varying, its exponent measure is
  concentrated on the axes: `μ {y | y₁ ≠ 0 ∧ y₂ ≠ 0} = 0`.
* `isRegVarVector_diag`: **Full asymptotic dependence, existence**: if `Z ≥ 0` has a regularly
  varying tail with index `-α`, then `X = (Z, Z)` is regularly varying, with spectral measure
  `δ_(1,1)` (on the unit sphere of the sup norm); its exponent measure is concentrated on the
  diagonal (`IsRegVarVector.measure_offDiag_eq_zero`).

This file is part of the proof in `ExtremeValueTheory.RegularVariation.Multivariate`.

## References

* S. I. Resnick, *Heavy-Tail Phenomena*, Springer (2007), Chapter 6 [Res07].
* B. Basrak, R. A. Davis and T. Mikosch, *A characterization of multivariate regular
  variation*, Ann. Appl. Probab. 12 (2002) [BDM02].
* H. Hult and F. Lindskog, *Regular variation for measures on metric spaces*, Publ. Inst. Math.
  80 (2006) [HL06].
* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020), Chapter 2 [KS20].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal Pointwise

namespace ExtremeValueTheory

/-! ### Linear combinations -/

section Linear

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Ω → E} {α : ℝ} {μ : Measure E}

omit [IsFiniteMeasure P] in
/-- The level sets `{L = c}`, `c > 0`, of a continuous linear functional are null for the
exponent measure. -/
theorem IsRegVarVector.measure_linear_eq_zero (h : IsRegVarVector P X α μ) (L : E →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) : μ {y | L y = c} = 0 := by
  by_cases hL : L = 0
  · subst hL
    have : {y : E | (0 : E →L[ℝ] ℝ) y = c} = ∅ := by
      ext y; simp [hc.ne]
    rw [this, measure_empty]
  have hLpos : 0 < ‖L‖ := norm_pos_iff.2 hL
  refine h.measure_level_eq_zero L.continuous.measurable
    (fun t _ y => by rw [L.map_smul, smul_eq_mul]) hc (r := c / 2 / ‖L‖)
    (div_pos (half_pos hc) hLpos) fun y hy => ?_
  rw [div_lt_iff₀ hLpos]
  calc c / 2 < L y := hy
    _ ≤ |L y| := le_abs_self _
    _ ≤ ‖L‖ * ‖y‖ := by simpa [Real.norm_eq_abs] using L.le_opNorm y
    _ = ‖y‖ * ‖L‖ := mul_comm _ _

/-- **Tails of linear combinations** ([BDM02, Theorem 1.1, "⇒"], [Res07, §6.5]): if `X` is
regularly varying with exponent measure `μ`, then for every continuous linear functional `L`,
`P(L X > x) / P(‖X‖ > x) → μ {y | L y > 1}`. -/
theorem IsRegVarVector.tendsto_linear (h : IsRegVarVector P X α μ) (hX : Measurable X)
    (L : E →L[ℝ] ℝ) :
    Tendsto (fun x => P.real {ω | x < L (X ω)} / P.real {ω | x < ‖X ω‖}) atTop
      (𝓝 (μ.real {y | 1 < L y})) := by
  by_cases hL : L = 0
  · subst hL
    have h0 : {y : E | 1 < (0 : E →L[ℝ] ℝ) y} = ∅ := by ext y; simp
    rw [h0, measureReal_empty]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have : {ω | x < (0 : E →L[ℝ] ℝ) (X ω)} = ∅ := by
      ext ω; simp [hx.le]
    rw [this, measureReal_empty, zero_div]
  have hLpos : 0 < ‖L‖ := norm_pos_iff.2 hL
  have hm : MeasurableSet {y : E | 1 < L y} := measurableSet_lt measurable_const L.measurable
  have hA : {y : E | 1 < L y} ⊆ {y | ‖L‖⁻¹ ≤ ‖y‖} := fun y (hy : 1 < L y) => by
    have h1 : 1 ≤ ‖L‖ * ‖y‖ := by
      have := L.le_opNorm y
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (L y)]
    show ‖L‖⁻¹ ≤ ‖y‖
    rw [inv_eq_one_div, div_le_iff₀ hLpos]
    linarith [mul_comm ‖L‖ ‖y‖]
  have key := h.tendsto_measureReal hX hm (inv_pos.2 hLpos) hA
    (measure_mono_null (frontier_lt_subset_eq continuous_const L.continuous) (by
      simpa [eq_comm] using h.measure_linear_eq_zero L one_pos))
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have : {ω | 1 < L (x⁻¹ • X ω)} = {ω | x < L (X ω)} := by
    ext ω
    show 1 < L (x⁻¹ • X ω) ↔ x < L (X ω)
    rw [L.map_smul, smul_eq_mul, lt_inv_mul_iff₀ hx, mul_one]
  rw [this]

/-- **Tails of linear combinations, inner product form**: `P(⟪c, X⟫ > x) / P(‖X‖ > x) →
μ {y | ⟪c, y⟫ > 1}`. -/
theorem IsRegVarVector.tendsto_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {Y : Ω → F} {ν : Measure F}
    (h : IsRegVarVector P Y α ν) (hY : Measurable Y) (c : F) :
    Tendsto (fun x => P.real {ω | x < inner ℝ c (Y ω)} / P.real {ω | x < ‖Y ω‖}) atTop
      (𝓝 (ν.real {y | 1 < inner ℝ c y})) :=
  h.tendsto_linear hY (innerSL ℝ c)

end Linear

/-! ### Examples: asymptotic dependence and independence -/

section Examples

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Ω → E} {α : ℝ} {μ : Measure E}

omit [NormedSpace ℝ E] in
/-- If `∫ g dμ = 0` for a nonnegative bounded continuous `g` vanishing near the origin, then
`g = 0` `μ`-almost everywhere. -/
theorem measure_pos_eq_zero_of_integral_eq_zero (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞)
    (g : E →ᵇ ℝ) (hg0 : ∀ y, 0 ≤ g y) (hgv : VanishesNearZero g) (hint : ∫ y, g y ∂μ = 0) :
    μ {y | 0 < g y} = 0 := by
  obtain ⟨r, hr, hgr⟩ := hgv
  have hsupp : Function.support g ⊆ {y | r / 2 < ‖y‖} := fun y hy => by
    by_contra h'
    exact hy (hgr y (by simp only [mem_ofPred_eq, not_lt] at h'; linarith))
  have hInt : Integrable g μ :=
    (integrableOn_iff_integrable_of_support_subset hsupp).1
      (Measure.integrableOn_of_bounded (hμ _ (half_pos hr)).ne
        g.continuous.aestronglyMeasurable (M := ‖g‖)
        (ae_of_all _ fun y => g.norm_coe_le_norm y))
  have hae := (integral_eq_zero_iff_of_nonneg hg0 hInt).1 hint
  exact measure_mono_null (fun y (hy : 0 < g y) => (ne_of_gt hy : g y ≠ 0)) (ae_iff.1 hae)

/-- **Support of the exponent measure in a closed cone**: if `X` takes values in a closed cone
`C` (stable under multiplication by positive scalars), the exponent measure is concentrated on
`C`. -/
theorem IsRegVarVector.measure_compl_eq_zero (h : IsRegVarVector P X α μ) {C : Set E}
    (hC : IsClosed C) (hcone : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C)
    (hXC : ∀ᵐ ω ∂P, X ω ∈ C) : μ Cᶜ = 0 := by
  have hCne : C.Nonempty := by
    obtain ⟨ω, hω⟩ := hXC.exists
    exact ⟨X ω, hω⟩
  have hpiece : ∀ r > 0, μ {y | y ∉ C ∧ r ≤ ‖y‖} = 0 := by
    intro r hr
    let d : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun y => min 1 (Metric.infDist y C))
      (continuous_const.min (Metric.continuous_infDist_pt C)) 1 fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one Metric.infDist_nonneg)]
        exact min_le_left _ _
    let g : E →ᵇ ℝ := d * normCutoffBCF r
    have hg : ∀ y, g y = min 1 (Metric.infDist y C) * normCutoff r y := fun y => rfl
    have hg0 : ∀ y, 0 ≤ g y := fun y => by
      rw [hg]; exact mul_nonneg (le_min zero_le_one Metric.infDist_nonneg) (NNReal.coe_nonneg _)
    have hint : ∫ y, g y ∂μ = 0 := by
      refine tendsto_nhds_unique (h.tendsto g (vanishesNearZero_mul_normCutoffBCF hr d))
        (tendsto_const_nhds.congr' ?_)
      filter_upwards [eventually_gt_atTop 0] with x hx
      have : ∫ ω, g (x⁻¹ • X ω) ∂P = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hXC] with ω hω
        rw [hg, Metric.infDist_zero_of_mem (hcone _ (inv_pos.2 hx) _ hω),
          min_eq_right zero_le_one, zero_mul]
        rfl
      rw [this, mul_zero]
    refine measure_mono_null (fun y ⟨hyC, hyr⟩ => ?_)
      (measure_pos_eq_zero_of_integral_eq_zero h.measure_lt_top g hg0
        (vanishesNearZero_mul_normCutoffBCF hr d) hint)
    show 0 < g y
    rw [hg, normCutoff_eq_one hr hyr, NNReal.coe_one, mul_one]
    exact lt_min one_pos ((hC.notMem_iff_infDist_pos hCne).1 hyC)
  have hsub : Cᶜ ⊆ {0} ∪ ⋃ n : ℕ, {y | y ∉ C ∧ 1 / ((n : ℝ) + 1) ≤ ‖y‖} := by
    intro y hy
    by_cases h0 : y = 0
    · exact Or.inl h0
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 h0)
      exact Or.inr (mem_iUnion.2 ⟨n, hy, hn.le⟩)
  refine measure_mono_null hsub (measure_union_null h.measure_zero
    (measure_iUnion_null fun n => hpiece _ (by positivity)))

/-- **Full asymptotic dependence**: for `X = (Z, Z)`, the exponent measure is concentrated on the
diagonal. -/
theorem IsRegVarVector.measure_offDiag_eq_zero {Z : Ω → ℝ} {ν : Measure (ℝ × ℝ)}
    (h : IsRegVarVector P (fun ω => (Z ω, Z ω)) α ν) : ν {y | y.1 ≠ y.2} = 0 := by
  have := h.measure_compl_eq_zero (C := {y : ℝ × ℝ | y.1 = y.2})
    (isClosed_eq continuous_fst continuous_snd)
    (fun t _ y (hy : y.1 = y.2) => show t * y.1 = t * y.2 by rw [hy])
    (ae_of_all _ fun ω => rfl)
  simpa only [compl_ofPred, ne_eq] using this

omit [IsProbabilityMeasure P] in
/-- Tails of a real random variable vanish. -/
theorem tendsto_measureReal_lt_atTop [IsFiniteMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) :
    Tendsto (fun c => P.real {ω | c < Y ω}) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := P) (s := fun c : ℝ => {ω | c < Y ω})
    (fun c => (measurableSet_lt measurable_const hY).nullMeasurableSet)
    (fun a b hab ω (hω : b < Y ω) => show a < Y ω by linarith) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ c : ℝ, {ω | c < Y ω}) = ∅ := by
    ext ω; simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact ⟨Y ω, le_rfl⟩
  rw [he, measure_empty] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at this
  exact this

omit [IsProbabilityMeasure P] in
/-- **Asymptotic independence** ([Res07, §6.5.1]): if `X = (X₁, X₂)` has independent components
and is regularly varying, its exponent measure is concentrated on the axes:
`μ {y | y₁ ≠ 0 ∧ y₂ ≠ 0} = 0`. -/
theorem IsRegVarVector.measure_ne_zero_ne_zero_eq_zero [IsFiniteMeasure P] {X₁ X₂ : Ω → ℝ} {ν : Measure (ℝ × ℝ)}
    (h : IsRegVarVector P (fun ω => (X₁ ω, X₂ ω)) α ν) (h₁ : Measurable X₁)
    (h₂ : Measurable X₂) (hind : IndepFun X₁ X₂ P) :
    ν {y | y.1 ≠ 0 ∧ y.2 ≠ 0} = 0 := by
  have hX : Measurable fun ω => (X₁ ω, X₂ ω) := h₁.prodMk h₂
  have hpiece : ∀ r > 0, ν {y : ℝ × ℝ | r ≤ |y.1| ∧ r ≤ |y.2|} = 0 := by
    intro r hr
    let φ : ℝ →ᵇ ℝ := normCutoffBCF r
    let g : ℝ × ℝ →ᵇ ℝ := φ.compContinuous ⟨Prod.fst, continuous_fst⟩ *
      φ.compContinuous ⟨Prod.snd, continuous_snd⟩
    have hg : ∀ y : ℝ × ℝ, g y = (normCutoff r y.1 : ℝ) * normCutoff r y.2 := fun y => rfl
    have hφ0 : ∀ s : ℝ, 0 ≤ (normCutoff r s : ℝ) := fun s => NNReal.coe_nonneg _
    have hφ1 : ∀ s : ℝ, (normCutoff r s : ℝ) ≤ 1 := fun s => by
      exact_mod_cast normCutoff_le_one r s
    have hφm : Measurable fun s : ℝ => (normCutoff r s : ℝ) :=
      measurable_coe_nnreal_real.comp (measurable_normCutoff r)
    have hg0 : ∀ y, 0 ≤ g y := fun y => by rw [hg]; exact mul_nonneg (hφ0 _) (hφ0 _)
    have hgv : VanishesNearZero g := ⟨r / 2, half_pos hr, fun y hy => by
      rw [hg, normCutoff_eq_zero hr (show ‖y.1‖ ≤ r / 2 from (norm_fst_le y).trans hy.le),
        NNReal.coe_zero, zero_mul]⟩
    -- the cutoff is dominated by the indicator of `{|s| > r / 2}`
    have hφind : ∀ s : ℝ, (normCutoff r s : ℝ) ≤ {s : ℝ | r / 2 < |s|}.indicator 1 s := by
      intro s
      by_cases hs : r / 2 < |s|
      · rw [indicator_of_mem (show s ∈ {s : ℝ | r / 2 < |s|} from hs)]; exact hφ1 s
      · rw [indicator_of_notMem (show s ∉ {s : ℝ | r / 2 < |s|} from hs),
          normCutoff_eq_zero hr (by rw [Real.norm_eq_abs]; exact not_lt.1 hs), NNReal.coe_zero]
    have hbound : ∀ x : ℝ, 0 < x → ∀ Y : Ω → ℝ, Measurable Y →
        ∫ ω, (normCutoff r (x⁻¹ * Y ω) : ℝ) ∂P ≤ P.real {ω | r / 2 * x < |Y ω|} := by
      intro x hx Y hY
      have hset : {ω | r / 2 * x < |Y ω|} = (fun ω => x⁻¹ * Y ω) ⁻¹' {s : ℝ | r / 2 < |s|} := by
        ext ω
        simp only [mem_ofPred_eq, mem_preimage, abs_mul, abs_inv, abs_of_pos hx]
        rw [lt_inv_mul_iff₀ hx, mul_comm]
      rw [hset, ← integral_indicator_one (s := (fun ω => x⁻¹ * Y ω) ⁻¹' {s : ℝ | r / 2 < |s|})
        ((measurableSet_lt measurable_const continuous_abs.measurable).preimage
          (measurable_const.mul hY))]
      refine integral_mono (Integrable.of_bound
        ((hφm.comp (measurable_const.mul hY)).aestronglyMeasurable) 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]; exact hφ1 _))
        ((integrable_const 1).indicator ((measurableSet_lt measurable_const
          continuous_abs.measurable).preimage (measurable_const.mul hY))) fun ω => ?_
      exact hφind _
    have hint : ∫ y, g y ∂ν = 0 := by
      have hlim := h.tendsto g hgv
      have hRV := h.isRegularlyVarying.tendsto (half_pos hr)
      have h0 := (tendsto_measureReal_lt_atTop (P := P)
        (continuous_abs.measurable.comp h₁ : Measurable fun ω => |X₁ ω|)).comp
        (tendsto_id.const_mul_atTop (half_pos hr))
      have hup := h0.mul hRV
      rw [zero_mul] at hup
      refine tendsto_nhds_unique hlim (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        hup ?_ ?_)
      · filter_upwards with x
        exact mul_nonneg (inv_nonneg.2 measureReal_nonneg) (integral_nonneg fun ω => hg0 _)
      · filter_upwards [eventually_gt_atTop 0, h.isRegularlyVarying.eventually_pos] with x hx hpos
        simp only [Function.comp_apply, id]
        have hsplit : ∫ ω, g (x⁻¹ • (X₁ ω, X₂ ω)) ∂P =
            (∫ ω, (normCutoff r (x⁻¹ * X₁ ω) : ℝ) ∂P) *
              ∫ ω, (normCutoff r (x⁻¹ * X₂ ω) : ℝ) ∂P := by
          have := (hind.comp (hφm.comp (measurable_const_mul x⁻¹))
            (hφm.comp (measurable_const_mul x⁻¹))).integral_mul_eq_mul_integral
            ((hφm.comp (measurable_const_mul x⁻¹)).comp h₁).aestronglyMeasurable
            ((hφm.comp (measurable_const_mul x⁻¹)).comp h₂).aestronglyMeasurable
          simpa [hg] using this
        have hb1 := hbound x hx X₁ h₁
        have hb2 : ∫ ω, (normCutoff r (x⁻¹ * X₂ ω) : ℝ) ∂P ≤
            P.real {ω | r / 2 * x < ‖(X₁ ω, X₂ ω)‖} :=
          (hbound x hx X₂ h₂).trans (measureReal_mono fun ω (hω : r / 2 * x < |X₂ ω|) =>
            show r / 2 * x < ‖(X₁ ω, X₂ ω)‖ from
              lt_of_lt_of_le hω (by rw [← Real.norm_eq_abs]; exact norm_snd_le (X₁ ω, X₂ ω)))
        rw [hsplit, div_eq_mul_inv]
        have hi1 : 0 ≤ ∫ ω, (normCutoff r (x⁻¹ * X₁ ω) : ℝ) ∂P := integral_nonneg fun _ => hφ0 _
        have hi2 : 0 ≤ ∫ ω, (normCutoff r (x⁻¹ * X₂ ω) : ℝ) ∂P := integral_nonneg fun _ => hφ0 _
        have hinv : 0 ≤ (P.real {ω | x < ‖(X₁ ω, X₂ ω)‖})⁻¹ := inv_nonneg.2 measureReal_nonneg
        calc (P.real {ω | x < ‖(X₁ ω, X₂ ω)‖})⁻¹ *
              ((∫ ω, (normCutoff r (x⁻¹ * X₁ ω) : ℝ) ∂P) *
                ∫ ω, (normCutoff r (x⁻¹ * X₂ ω) : ℝ) ∂P)
            ≤ (P.real {ω | x < ‖(X₁ ω, X₂ ω)‖})⁻¹ *
              (P.real {ω | r / 2 * x < |X₁ ω|} *
                P.real {ω | r / 2 * x < ‖(X₁ ω, X₂ ω)‖}) := by
              gcongr
          _ = P.real {ω | r / 2 * x < |X₁ ω|} *
              (P.real {ω | r / 2 * x < ‖(X₁ ω, X₂ ω)‖} *
                (P.real {ω | x < ‖(X₁ ω, X₂ ω)‖})⁻¹) := by ring
    refine measure_mono_null (fun y ⟨hy1, hy2⟩ => ?_)
      (measure_pos_eq_zero_of_integral_eq_zero h.measure_lt_top g hg0 hgv hint)
    show 0 < g y
    rw [hg, normCutoff_eq_one hr (by rwa [Real.norm_eq_abs]),
      normCutoff_eq_one hr (by rwa [Real.norm_eq_abs]), NNReal.coe_one, mul_one]
    exact one_pos
  have hsub : {y : ℝ × ℝ | y.1 ≠ 0 ∧ y.2 ≠ 0} ⊆
      ⋃ n : ℕ, {y : ℝ × ℝ | 1 / ((n : ℝ) + 1) ≤ |y.1| ∧ 1 / ((n : ℝ) + 1) ≤ |y.2|} := by
    rintro y ⟨h1, h2⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (abs_pos.2 h1) (abs_pos.2 h2))
    exact mem_iUnion.2 ⟨n, (hn.trans_le (min_le_left _ _)).le,
      (hn.trans_le (min_le_right _ _)).le⟩
  exact measure_mono_null hsub (measure_iUnion_null fun n => hpiece _ (by positivity))

end Examples

section ExamplesPolar

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {α : ℝ}

/-- **A regularly varying vector with a single direction**: if `Z ≥ 0` has a regularly varying
tail with index `-α` and `‖v‖ = 1`, then `X = Z v` is regularly varying, with spectral measure
`δ_v` and exponent measure `(α r ^ (-α - 1) dr) ⊗ δ_v`. -/
theorem isRegVarVector_smul_const (hα : 0 < α) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) {v : E} (hv : ‖v‖ = 1)
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α)) :
    IsRegVarVector P (fun ω => Z ω • v) α (polarMeasure α (Measure.dirac v)) := by
  have hnorm : ∀ ω, ‖Z ω • v‖ = Z ω := fun ω => by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]
  refine isRegVarVector_polarMeasure hα (hZ.smul_const v) ?_ ?_
  · simpa only [hnorm] using hRV
  intro f
  simp only [hnorm]
  rw [integral_dirac]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hRV.eventually_pos, eventually_gt_atTop 0] with x hx hx0
  have hne : P {ω | x < Z ω} ≠ 0 := by
    intro h0; rw [measureReal_def, h0, ENNReal.toReal_zero] at hx; exact lt_irrefl _ hx
  have := cond_isProbabilityMeasure hne
  rw [integral_congr_ae (g := fun _ => f v) ?_, integral_const, probReal_univ, one_smul]
  filter_upwards [ae_cond_mem (measurableSet_lt measurable_const hZ)] with ω hω
  rw [smul_smul, inv_mul_cancel₀ (hx0.trans hω).ne', one_smul]

/-- **Full asymptotic dependence, existence**: if `Z ≥ 0` has a regularly varying tail with index
`-α`, then `X = (Z, Z)` is regularly varying, with spectral measure `δ_(1,1)` (on the unit sphere of
the sup norm); its exponent measure is concentrated on the diagonal
(`IsRegVarVector.measure_offDiag_eq_zero`). -/
theorem isRegVarVector_diag (hα : 0 < α) {Z : Ω → ℝ} (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α)) :
    IsRegVarVector P (fun ω => (Z ω, Z ω)) α
      (polarMeasure α (Measure.dirac ((1 : ℝ), (1 : ℝ)))) := by
  have := isRegVarVector_smul_const hα hZ hZ0 (v := ((1 : ℝ), (1 : ℝ))) (by simp) hRV
  simpa [Prod.smul_mk] using this

end ExamplesPolar

end ExtremeValueTheory
