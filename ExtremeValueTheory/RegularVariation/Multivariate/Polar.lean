/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TailProcess
import Mathlib.Topology.Algebra.Module.Cardinality
import ExtremeValueTheory.RegularVariation.Multivariate.Basic

/-!
# Multivariate regular variation: the polar decomposition

The spectral measure of a regularly varying random vector and the polar decomposition: `X` is
regularly varying iff `P(‖X‖ > x)` is regularly varying and the law of `X / ‖X‖` given
`‖X‖ > x` converges weakly; the exponent measure is then `μ = (α r ^ (-α - 1) dr) ⊗ S` in polar
coordinates, with `S` the spectral measure on the unit sphere.

## Main definitions

* `spectralMeasure`: The *spectral measure* of an exponent measure `μ`: the law of `Y / ‖Y‖` for `Y`
  distributed as `μ` restricted to `{‖y‖ > 1}`.
* `radialMeasure`: The radial measure `α r ^ (-α - 1) dr` on `(0, ∞)`: `ν_α (r, ∞) = r ^ (-α)`.
* `polarMeasure`: The measure `(α r ^ (-α - 1) dr) ⊗ S` in polar coordinates: the image of
  `radialMeasure α ⊗ S` under `(r, θ) ↦ r • θ`.

## Main results

* `IsRegVarVector.tendstoLawCond_spectralMeasure`: **Polar decomposition, spectral part** ([BDM02],
  [Res07, Theorem 6.1], [KS20, §2.2]): if `X` is regularly varying, the law of `X / ‖X‖` given `‖X‖
  > x` converges weakly to the spectral measure of `μ`.
* `isRegVarVector_polarMeasure`: **Polar decomposition, converse** ([Res07, Theorem 6.1], [BDM02]):
  if `‖X‖` has a regularly varying tail with index `-α` and the law of `X / ‖X‖` given `‖X‖ > x`
  converges weakly to a probability measure `S`, then `X` is regularly varying with exponent measure
  `μ = (α r ^ (-α - 1) dr) ⊗ S` in polar coordinates.
* `isRegVarVector_iff`: **The polar decomposition** ([Res07, Theorem 6.1], [BDM02], [KS20, §2.2]):
  for `α > 0`, `X` is regularly varying with index `α` if and only if `P(‖X‖ > x)` is regularly
  varying with index `-α` and the law of `X / ‖X‖` given `‖X‖ > x` converges weakly to some
  probability measure (the spectral measure).
* `IsRegVarVector.eq_polarMeasure`: **The exponent measure in polar coordinates** ([Res07, §6.1]):
  `μ` is the image of `(α r ^ (-α - 1) dr) ⊗ S` under `(r, θ) ↦ r • θ`, with `S` the spectral
  measure.
* `IsRegVarVector.ae_norm_spectralMeasure`: The spectral measure lives on the unit sphere.

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

/-! ### The polar decomposition -/

/-- Two finite measures on `ℝ` with the same total mass agreeing on all half-lines `(a, ∞)` are
equal. -/
theorem measure_ext_of_Ioi {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (huniv : μ univ = ν univ) (h : ∀ a, μ (Ioi a) = ν (Ioi a)) : μ = ν :=
  Measure.ext_of_Iic μ ν fun a => by
    rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
      measure_compl measurableSet_Ioi (measure_ne_top _ _), huniv, h]

theorem paretoMeasure_one_Ioi_of_lt_one {α : ℝ} (hα : 0 < α) {a : ℝ} (ha : a < 1) :
    paretoMeasure 1 α (Ioi a) = 1 := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = paretoMeasure 1 α (Ioi 1) := by
        rw [paretoMeasure_one_Ioi hα le_rfl, Real.one_rpow, ENNReal.ofReal_one]
    _ ≤ paretoMeasure 1 α (Ioi a) := measure_mono (Ioi_subset_Ioi ha.le)

section Polar

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {X : Ω → E} {α : ℝ} {μ : Measure E}

/-- The *spectral measure* of an exponent measure `μ`: the law of `Y / ‖Y‖` for `Y` distributed
as `μ` restricted to `{‖y‖ > 1}`. -/
noncomputable def spectralMeasure (μ : Measure E) : Measure E :=
  (μ.restrict {y | 1 < ‖y‖}).map fun y => ‖y‖⁻¹ • y

namespace IsRegVarVector

omit [SecondCountableTopology E] in
theorem isProbabilityMeasure_restrict (h : IsRegVarVector P X α μ) (hX : Measurable X) :
    IsProbabilityMeasure (μ.restrict {y | 1 < ‖y‖}) :=
  ⟨by rw [Measure.restrict_apply_univ, h.measure_one_lt_norm hX]⟩

omit [SecondCountableTopology E] in
theorem isProbabilityMeasure_spectralMeasure (h : IsRegVarVector P X α μ) (hX : Measurable X) :
    IsProbabilityMeasure (spectralMeasure μ) := by
  have := h.isProbabilityMeasure_restrict hX
  unfold spectralMeasure; infer_instance

/-- The law of `(‖X‖ / x, X / x)` given `‖X‖ > x` converges weakly to the law of `(‖Y‖, Y)` for
`Y` distributed as `μ` restricted to `{‖y‖ > 1}` ([KS20, §2.2]). -/
theorem tendstoLawCond_norm (h : IsRegVarVector P X α μ) (hX : Measurable X) :
    TendstoLawCond P (fun x => {ω | x < ‖X ω‖}) (fun x ω => (‖X ω‖ / x, x⁻¹ • X ω)) atTop
      ((μ.restrict {y | 1 < ‖y‖}).map fun y => (‖y‖, y)) := by
  intro F
  have hm : MeasurableSet {y : E | 1 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  let H : E →ᵇ ℝ := F.compContinuous ⟨fun y => (‖y‖, y), continuous_norm.prodMk continuous_id⟩
  have key := h.tendsto_integral_indicator hX H continuous_norm one_pos (c := 1)
    (fun y hy => hy.le) (h.measure_norm_eq_zero one_pos)
  have hφ : Measurable fun y : E => (‖y‖, y) :=
    (continuous_norm.prodMk continuous_id).measurable
  rw [integral_map hφ.aemeasurable F.continuous.aestronglyMeasurable, ← integral_indicator hm]
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [integral_cond_eq, smul_eq_mul,
    ← integral_indicator (measurableSet_lt measurable_const hX.norm)]
  congr 2
  ext ω
  by_cases hω : x < ‖X ω‖
  · have h1 : 1 < ‖x⁻¹ • X ω‖ := (setOf_one_lt_norm_smul hx _).2 hω
    rw [indicator_of_mem (show x⁻¹ • X ω ∈ {y : E | 1 < ‖y‖} from h1),
      indicator_of_mem (show ω ∈ {ω | x < ‖X ω‖} from hω)]
    simp only [H, compContinuous_apply, ContinuousMap.coe_mk]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hx, inv_mul_eq_div]
  · have h1 : ¬ 1 < ‖x⁻¹ • X ω‖ := fun h' => hω ((setOf_one_lt_norm_smul hx _).1 h')
    rw [indicator_of_notMem (show x⁻¹ • X ω ∉ {y : E | 1 < ‖y‖} from h1),
      indicator_of_notMem (show ω ∉ {ω | x < ‖X ω‖} from hω)]

omit [SecondCountableTopology E] in
/-- The radial part of the exponent measure, restricted to `{‖y‖ > 1}`, is the Pareto law. -/
theorem map_norm_restrict (hα : 0 < α) (h : IsRegVarVector P X α μ) (hX : Measurable X) :
    (μ.restrict {y | 1 < ‖y‖}).map (fun y => ‖y‖) = paretoMeasure 1 α := by
  have := h.isProbabilityMeasure_restrict hX
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  refine measure_ext_of_Ioi (by simp) fun a => ?_
  rw [Measure.map_apply continuous_norm.measurable measurableSet_Ioi,
    Measure.restrict_apply (continuous_norm.measurable measurableSet_Ioi)]
  rcases le_or_gt 1 a with ha | ha
  · rw [paretoMeasure_one_Ioi hα ha, ← h.measure_lt_norm hX (one_pos.trans_le ha)]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_ofPred_eq]
    exact ⟨fun hy => hy.1, fun hy => ⟨hy, lt_of_le_of_lt ha hy⟩⟩
  · rw [paretoMeasure_one_Ioi_of_lt_one hα ha, ← h.measure_one_lt_norm hX]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_ofPred_eq]
    exact ⟨fun hy => hy.2, fun hy => ⟨ha.trans hy, hy⟩⟩

/-- **Polar decomposition, spectral part** ([BDM02], [Res07, Theorem 6.1], [KS20, §2.2]): if `X`
is regularly varying, the law of `X / ‖X‖` given `‖X‖ > x` converges weakly to the spectral
measure of `μ`. -/
theorem tendstoLawCond_spectralMeasure (hα : 0 < α) (h : IsRegVarVector P X α μ)
    (hX : Measurable X) :
    TendstoLawCond P (fun x => {ω | x < ‖X ω‖}) (fun _ ω => ‖X ω‖⁻¹ • X ω) atTop
      (spectralMeasure μ) := by
  have hφ : Measurable fun y : E => (‖y‖, y) := (continuous_norm.prodMk continuous_id).measurable
  have hν : ((μ.restrict {y | 1 < ‖y‖}).map fun y => (‖y‖, y)).map Prod.fst =
      paretoMeasure 1 α := by
    rw [Measure.map_map measurable_fst hφ]
    exact h.map_norm_restrict hα hX
  have key := tendstoLawCond_spectral_of_tendstoLawCond (Z := fun ω => ‖X ω‖) (V := X) hX.norm hν
    (h.tendstoLawCond_norm hX)
  have hψ : Measurable fun p : ℝ × E => p.1⁻¹ • p.2 := (measurable_fst.inv).smul measurable_snd
  rwa [Measure.map_map hψ hφ] at key

end IsRegVarVector

end Polar

/-! ### The radial measure and polar coordinates -/

section Radial

variable {α : ℝ}

/-- The radial measure `α r ^ (-α - 1) dr` on `(0, ∞)`: `ν_α (r, ∞) = r ^ (-α)`. -/
noncomputable def radialMeasure (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun r => ENNReal.ofReal (α * r ^ (-α - 1))

instance : SFinite (radialMeasure α) := by
  unfold radialMeasure; infer_instance

theorem radialMeasure_Ioi (hα : 0 < α) {u : ℝ} (hu : 0 < u) :
    radialMeasure α (Ioi u) = ENNReal.ofReal (u ^ (-α)) := by
  rw [radialMeasure, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.2 hu.le]
  have hint : IntegrableOn (fun y : ℝ => α * y ^ (-α - 1)) (Ioi u) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hu).const_mul α
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hu,
      show -α - 1 + 1 = -α by ring]
    field_simp
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun y hy =>
      mul_nonneg hα.le (Real.rpow_pos_of_pos (hu.trans hy) _).le

theorem radialMeasure_Iic_zero : radialMeasure α (Iic 0) = 0 := by
  rw [radialMeasure, withDensity_apply _ measurableSet_Iic]
  exact setLIntegral_measure_zero _ _ (by rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi, Ioc_self, measure_empty])

/-- Restricted to `(c, ∞)`, the radial measure is `c ^ (-α)` times the law of `c R`, `R`
Pareto(`α`). -/
theorem radialMeasure_restrict_Ioi (hα : 0 < α) {c : ℝ} (hc : 0 < c) :
    (radialMeasure α).restrict (Ioi c) =
      ENNReal.ofReal (c ^ (-α)) • (paretoMeasure 1 α).map (fun s => c * s) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hmeas : Measurable fun s : ℝ => c * s := measurable_const.mul measurable_id
  have : IsFiniteMeasure ((radialMeasure α).restrict (Ioi c)) :=
    ⟨by rw [Measure.restrict_apply_univ, radialMeasure_Ioi hα hc]; exact ENNReal.ofReal_lt_top⟩
  have : IsFiniteMeasure (ENNReal.ofReal (c ^ (-α)) • (paretoMeasure 1 α).map (fun s => c * s)) :=
    ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact ENNReal.ofReal_lt_top⟩
  have hval : ∀ a, (radialMeasure α).restrict (Ioi c) (Ioi a) =
      ENNReal.ofReal (max a c ^ (-α)) := fun a => by
    rw [Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi,
      radialMeasure_Ioi hα (lt_max_of_lt_right hc)]
  refine measure_ext_of_Ioi ?_ fun a => ?_
  · rw [Measure.restrict_apply_univ, radialMeasure_Ioi hα hc, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
  rw [hval, Measure.smul_apply, Measure.map_apply hmeas measurableSet_Ioi, smul_eq_mul]
  have hpre : (fun s => c * s) ⁻¹' Ioi a = Ioi (a / c) := by
    ext s; simp [div_lt_iff₀' hc]
  rw [hpre]
  rcases le_or_gt c a with hca | hca
  · rw [max_eq_left hca, paretoMeasure_one_Ioi hα ((one_le_div hc).2 hca),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
      Real.div_rpow (hc.le.trans hca) hc.le, mul_div_cancel₀ _
        (Real.rpow_pos_of_pos hc _).ne']
  · rw [max_eq_right hca.le, paretoMeasure_one_Ioi_of_lt_one hα ((div_lt_one hc).2 hca),
      mul_one]

end Radial

section PolarMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {α : ℝ} {S : Measure E}

/-- The measure `(α r ^ (-α - 1) dr) ⊗ S` in polar coordinates: the image of
`radialMeasure α ⊗ S` under `(r, θ) ↦ r • θ`. -/
noncomputable def polarMeasure (α : ℝ) (S : Measure E) : Measure E :=
  ((radialMeasure α).prod S).map fun p => p.1 • p.2

omit [NormedSpace ℝ E] [BorelSpace E] in
theorem ae_radialMeasure_prod [IsProbabilityMeasure S] (hS : ∀ᵐ θ ∂S, ‖θ‖ = 1) :
    ∀ᵐ p ∂(radialMeasure α).prod S, 0 < p.1 ∧ ‖p.2‖ = 1 := by
  have h1 : ∀ᵐ p ∂(radialMeasure α).prod S, 0 < p.1 := by
    refine ae_of_ae_map measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul, ae_iff]
    have hI : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext; simp
    rw [hI]
    exact radialMeasure_Iic_zero
  have h2 : ∀ᵐ p ∂(radialMeasure α).prod S, ‖p.2‖ = 1 := by
    refine ae_of_ae_map (f := Prod.snd) (p := fun θ : E => ‖θ‖ = 1)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod]
    exact Measure.ae_smul_measure hS _
  filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩

theorem polarMeasure_restrict (hα : 0 < α) [IsProbabilityMeasure S] (hS : ∀ᵐ θ ∂S, ‖θ‖ = 1)
    {c : ℝ} (hc : 0 < c) :
    (polarMeasure α S).restrict {y | c < ‖y‖} =
      ENNReal.ofReal (c ^ (-α)) • ((paretoMeasure 1 α).prod S).map
        (fun p => (c * p.1) • p.2) := by
  have hsm : Measurable fun p : ℝ × E => p.1 • p.2 := measurable_fst.smul measurable_snd
  have hB : MeasurableSet {y : E | c < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hmeas : Measurable fun s : ℝ => c * s := measurable_const.mul measurable_id
  rw [polarMeasure, Measure.restrict_map hsm hB]
  have hset : (fun p : ℝ × E => p.1 • p.2) ⁻¹' {y | c < ‖y‖} =ᵐ[(radialMeasure α).prod S]
      (Ioi c ×ˢ univ : Set (ℝ × E)) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [ae_radialMeasure_prod hS] with p hp
    simp [norm_smul, hp.2, abs_of_pos hp.1]
  have hprod : ((paretoMeasure 1 α).map (fun s => c * s)).prod S =
      ((paretoMeasure 1 α).prod S).map (Prod.map (fun s => c * s) id) := by
    rw [← Measure.map_prod_map _ _ hmeas measurable_id, Measure.map_id]
  rw [Measure.restrict_congr_set hset, ← Measure.prod_restrict, Measure.restrict_univ,
    radialMeasure_restrict_Ioi hα hc, Measure.prod_smul_left, Measure.map_smul, hprod,
    Measure.map_map hsm (hmeas.prodMap measurable_id)]
  · rfl
  · exact hsm.aemeasurable

theorem polarMeasure_zero [IsProbabilityMeasure S] (hS : ∀ᵐ θ ∂S, ‖θ‖ = 1) :
    polarMeasure α S {0} = 0 := by
  have hsm : Measurable fun p : ℝ × E => p.1 • p.2 := measurable_fst.smul measurable_snd
  rw [polarMeasure, Measure.map_apply hsm (measurableSet_singleton 0),
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_radialMeasure_prod hS] with p hp
  simp only [mem_preimage, mem_singleton_iff]
  exact smul_ne_zero hp.1.ne' (by rw [← norm_ne_zero_iff, hp.2]; exact one_ne_zero)

theorem polarMeasure_lt_norm (hα : 0 < α) [IsProbabilityMeasure S] (hS : ∀ᵐ θ ∂S, ‖θ‖ = 1)
    {c : ℝ} (hc : 0 < c) : polarMeasure α S {y | c < ‖y‖} = ENNReal.ofReal (c ^ (-α)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rw [← Measure.restrict_apply_univ, polarMeasure_restrict hα hS hc, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]

end PolarMeasure

section Converse

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {X : Ω → E} {α : ℝ} {μ : Measure E}

omit [IsProbabilityMeasure P] [SecondCountableTopology E] in
/-- A weak limit of the law of `X / ‖X‖` given `‖X‖ > x` lives on the unit sphere. -/
theorem ae_norm_eq_one_of_tendstoLawCond (hX : Measurable X) {S : Measure E} [IsFiniteMeasure S]
    (hS : TendstoLawCond P (fun x => {ω | x < ‖X ω‖}) (fun _ ω => ‖X ω‖⁻¹ • X ω) atTop S) :
    ∀ᵐ θ ∂S, ‖θ‖ = 1 := by
  let g : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun θ => min 1 |‖θ‖ - 1|)
    (continuous_const.min ((continuous_norm.sub continuous_const).abs)) 1 fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg _))]
      exact min_le_left _ _
  have key := hS.ae_eq_zero g (fun θ => le_min zero_le_one (abs_nonneg _)) ?_
  · filter_upwards [key] with θ hθ
    simp only [g, BoundedContinuousFunction.coe_ofNormedAddCommGroup] at hθ
    rcases min_eq_iff.1 hθ with h' | h'
    · exact absurd h'.1 one_ne_zero
    · exact sub_eq_zero.1 (abs_eq_zero.1 h'.1)
  · filter_upwards [eventually_gt_atTop 0] with x hx
    filter_upwards [ae_cond_mem (measurableSet_lt measurable_const hX.norm)] with ω hω
    have h0 : ‖X ω‖ ≠ 0 := (hx.trans hω).ne'
    simp [g, norm_smul, h0]

/-- **Polar decomposition, converse** ([Res07, Theorem 6.1], [BDM02]): if `‖X‖` has a regularly
varying tail with index `-α` and the law of `X / ‖X‖` given `‖X‖ > x` converges weakly to a
probability measure `S`, then `X` is regularly varying with exponent measure
`μ = (α r ^ (-α - 1) dr) ⊗ S` in polar coordinates. -/
theorem isRegVarVector_polarMeasure (hα : 0 < α) (hX : Measurable X) {S : Measure E}
    [IsProbabilityMeasure S]
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < ‖X ω‖}) (-α))
    (hS : TendstoLawCond P (fun x => {ω | x < ‖X ω‖}) (fun _ ω => ‖X ω‖⁻¹ • X ω) atTop S) :
    IsRegVarVector P X α (polarMeasure α S) := by
  have hS1 := ae_norm_eq_one_of_tendstoLawCond hX hS
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  refine ⟨hRV, polarMeasure_zero hS1, fun r hr => ?_, ?_⟩
  · rw [polarMeasure_lt_norm hα hS1 hr]; exact ENNReal.ofReal_lt_top
  intro f ⟨r, hr, hf⟩
  set c := r / 2 with hcdef
  have hc : 0 < c := half_pos hr
  have hsmT := tendstoLawCond_smul (Z := fun ω => ‖X ω‖) (T := fun ω => ‖X ω‖⁻¹ • X ω) hα
    hX.norm (hX.norm.inv.smul hX) hRV hS
  let g : E →ᵇ ℝ := f.compContinuous ⟨fun y => c • y, continuous_const_smul c⟩
  have h1 := (hsmT g).comp (tendsto_id.const_mul_atTop hc)
  have h2 := hRV.tendsto hc
  have hsm : Measurable fun p : ℝ × E => p.1 • p.2 := measurable_fst.smul measurable_snd
  have hsm' : Measurable fun p : ℝ × E => (c * p.1) • p.2 :=
    (measurable_const.mul measurable_fst).smul measurable_snd
  have hval : ∫ y, f y ∂polarMeasure α S =
      c ^ (-α) * ∫ y, g y ∂(((paretoMeasure 1 α).prod S).map fun p => p.1 • p.2) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := {y | c < ‖y‖})
      (fun y hy => hf y (by simp only [mem_ofPred_eq, not_lt] at hy; linarith)),
      polarMeasure_restrict hα hS1 hc, integral_smul_measure,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hc.le _), smul_eq_mul,
      integral_map hsm'.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map hsm.aemeasurable g.continuous.aestronglyMeasurable]
    congr 2
    ext p
    simp [g, smul_smul]
  rw [hval]
  have hpt : ∀ x : ℝ, 0 < x → ∀ ω,
      c • ((‖X ω‖ / (c * x)) • ‖X ω‖⁻¹ • X ω) = x⁻¹ • X ω := by
    intro x hx ω
    by_cases h0 : X ω = 0
    · simp [h0]
    · have hn : ‖X ω‖ ≠ 0 := norm_ne_zero_iff.2 h0
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
  refine (h2.mul h1).congr' ?_
  filter_upwards [eventually_gt_atTop 0, (tendsto_id.const_mul_atTop hc).eventually
    hRV.eventually_pos] with x hx hpos
  simp only [Function.comp_apply, id] at hpos ⊢
  rw [integral_cond_eq, smul_eq_mul]
  have hint : ∫ ω in {ω | c * x < ‖X ω‖}, g ((‖X ω‖ / (c * x)) • ‖X ω‖⁻¹ • X ω) ∂P =
      ∫ ω, f (x⁻¹ • X ω) ∂P := by
    simp only [g, compContinuous_apply, ContinuousMap.coe_mk, hpt x hx]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ω hω => hf _ ?_
    simp only [mem_ofPred_eq, not_lt] at hω
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hx, inv_mul_lt_iff₀ hx]
    nlinarith
  rw [hint, div_eq_mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hpos.ne', one_mul]

/-- **The polar decomposition** ([Res07, Theorem 6.1], [BDM02], [KS20, §2.2]): for `α > 0`, `X`
is regularly varying with index `α` if and only if `P(‖X‖ > x)` is regularly varying with index
`-α` and the law of `X / ‖X‖` given `‖X‖ > x` converges weakly to some probability measure (the
spectral measure). -/
theorem isRegVarVector_iff (hα : 0 < α) (hX : Measurable X) :
    (∃ μ : Measure E, IsRegVarVector P X α μ) ↔
      IsRegularlyVarying (fun x => P.real {ω | x < ‖X ω‖}) (-α) ∧
        ∃ S : Measure E, IsProbabilityMeasure S ∧
          TendstoLawCond P (fun x => {ω | x < ‖X ω‖}) (fun _ ω => ‖X ω‖⁻¹ • X ω) atTop S := by
  constructor
  · rintro ⟨μ, h⟩
    exact ⟨h.isRegularlyVarying, spectralMeasure μ, h.isProbabilityMeasure_spectralMeasure hX,
      h.tendstoLawCond_spectralMeasure hα hX⟩
  · rintro ⟨hRV, S, hS, hconv⟩
    exact ⟨_, isRegVarVector_polarMeasure hα hX hRV hconv⟩

/-- **The exponent measure in polar coordinates** ([Res07, §6.1]): `μ` is the image of
`(α r ^ (-α - 1) dr) ⊗ S` under `(r, θ) ↦ r • θ`, with `S` the spectral measure. -/
theorem IsRegVarVector.eq_polarMeasure (hα : 0 < α) (h : IsRegVarVector P X α μ)
    (hX : Measurable X) : μ = polarMeasure α (spectralMeasure μ) := by
  have := h.isProbabilityMeasure_spectralMeasure hX
  exact h.unique (isRegVarVector_polarMeasure hα hX h.isRegularlyVarying
    (h.tendstoLawCond_spectralMeasure hα hX))

/-- The spectral measure lives on the unit sphere. -/
theorem IsRegVarVector.ae_norm_spectralMeasure (hα : 0 < α) (h : IsRegVarVector P X α μ)
    (hX : Measurable X) : ∀ᵐ θ ∂spectralMeasure μ, ‖θ‖ = 1 := by
  have := h.isProbabilityMeasure_spectralMeasure hX
  exact ae_norm_eq_one_of_tendstoLawCond hX (h.tendstoLawCond_spectralMeasure hα hX)

end Converse

end ExtremeValueTheory
