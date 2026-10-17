/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TailProcess
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Multivariate regular variation

TODO docs
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal Pointwise

namespace ExtremeValueTheory

/-! ### Convergence on sets bounded away from the origin -/

section M0

variable {E : Type*} [NormedAddCommGroup E]

/-- A function `f` vanishes on a neighbourhood of the origin: `f y = 0` for `‖y‖ < r`, some
`r > 0`. Bounded continuous functions with this property are the test functions of convergence
on sets bounded away from the origin (Hult–Lindskog's `M₀`-convergence). -/
def VanishesNearZero (f : E → ℝ) : Prop := ∃ r > 0, ∀ y, ‖y‖ < r → f y = 0

/-- A continuous cutoff: `0` on `‖y‖ ≤ r / 2`, `1` on `‖y‖ ≥ r`, with values in `[0, 1]`. -/
noncomputable def normCutoff (r : ℝ) (y : E) : ℝ≥0 := Real.toNNReal (min 1 (2 * ‖y‖ / r - 1))

variable {r : ℝ}

theorem continuous_normCutoff (r : ℝ) : Continuous (normCutoff (E := E) r) :=
  continuous_real_toNNReal.comp (continuous_const.min
    (((continuous_const.mul continuous_norm).div_const r).sub continuous_const))

theorem normCutoff_le_one (r : ℝ) (y : E) : normCutoff r y ≤ 1 :=
  Real.toNNReal_le_one.2 (min_le_left _ _)

theorem normCutoff_eq_one (hr : 0 < r) {y : E} (hy : r ≤ ‖y‖) : normCutoff r y = 1 := by
  have : 1 ≤ 2 * ‖y‖ / r - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hr]; linarith
  simp [normCutoff, min_eq_left this]

theorem normCutoff_eq_zero (hr : 0 < r) {y : E} (hy : ‖y‖ ≤ r / 2) : normCutoff r y = 0 := by
  have : 2 * ‖y‖ / r - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hr]; linarith
  exact Real.toNNReal_eq_zero.2 (min_le_of_right_le this)

theorem coe_normCutoff_le_indicator (hr : 0 < r) (y : E) :
    (normCutoff r y : ℝ≥0∞) ≤ {y : E | r / 2 < ‖y‖}.indicator 1 y := by
  by_cases hy : r / 2 < ‖y‖
  · rw [indicator_of_mem (show y ∈ {y : E | r / 2 < ‖y‖} from hy), Pi.one_apply]
    exact_mod_cast normCutoff_le_one r y
  · rw [normCutoff_eq_zero hr (not_lt.1 hy)]; simp

/-- The cutoff as a bounded continuous function. -/
noncomputable def normCutoffBCF (r : ℝ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofAbsLe (fun y => (normCutoff r y : ℝ))
    (NNReal.continuous_coe.comp (continuous_normCutoff r)) 1 fun y => by
      rw [NNReal.abs_eq]; exact_mod_cast normCutoff_le_one r y

@[simp] theorem normCutoffBCF_apply (r : ℝ) (y : E) :
    normCutoffBCF r y = (normCutoff r y : ℝ) := rfl

theorem vanishesNearZero_mul_normCutoffBCF (hr : 0 < r) (g : E →ᵇ ℝ) :
    VanishesNearZero (⇑(g * normCutoffBCF r : E →ᵇ ℝ)) :=
  ⟨r / 2, half_pos hr, fun y hy => by
    simp [BoundedContinuousFunction.coe_mul, normCutoff_eq_zero hr hy.le]⟩

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_normCutoff (r : ℝ) : Measurable (normCutoff (E := E) r) :=
  (continuous_normCutoff r).measurable


/-- The measure `μ` weighted by the cutoff. -/
noncomputable def cutoffMeasure (μ : Measure E) (r : ℝ) : Measure E :=
  μ.withDensity fun y => (normCutoff r y : ℝ≥0∞)

theorem isFiniteMeasure_cutoffMeasure {μ : Measure E} (hr : 0 < r)
    (hμ : μ {y | r / 2 < ‖y‖} < ∞) : IsFiniteMeasure (cutoffMeasure μ r) := by
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top hμ.ne ?_)
  rw [← lintegral_indicator_one (measurableSet_lt measurable_const continuous_norm.measurable)]
  exact lintegral_mono fun y => coe_normCutoff_le_indicator hr y

theorem integral_cutoffMeasure (μ : Measure E) (r : ℝ) (g : E → ℝ) :
    ∫ y, g y ∂(cutoffMeasure μ r) = ∫ y, g y * normCutoffBCF r y ∂μ := by
  rw [cutoffMeasure, integral_withDensity_eq_integral_smul (measurable_normCutoff r)]
  congr 1; ext y
  simp [NNReal.smul_def, mul_comm]

theorem cutoffMeasure_restrict_eq (μ : Measure E) (hr : 0 < r) :
    (cutoffMeasure μ r).restrict {y | r < ‖y‖} = μ.restrict {y | r < ‖y‖} := by
  have hs : MeasurableSet {y : E | r < ‖y‖} := measurableSet_lt measurable_const
    continuous_norm.measurable
  rw [cutoffMeasure, restrict_withDensity hs]
  conv_rhs => rw [← withDensity_one (μ := μ.restrict {y | r < ‖y‖})]
  refine withDensity_congr_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall fun y hy => ?_))
  simp [normCutoff_eq_one hr (le_of_lt hy)]

variable {ι : Type*} {l : Filter ι} {μs : ι → Measure E} {μ : Measure E}

/-- Convergence on sets bounded away from the origin gives weak convergence of the measures
weighted by a cutoff. -/
theorem tendsto_integral_cutoffMeasure (hr : 0 < r)
    (h : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
      Tendsto (fun i => ∫ y, f y ∂μs i) l (𝓝 (∫ y, f y ∂μ))) (g : E →ᵇ ℝ) :
    Tendsto (fun i => ∫ y, g y ∂(cutoffMeasure (μs i) r)) l
      (𝓝 (∫ y, g y ∂(cutoffMeasure μ r))) := by
  simp only [integral_cutoffMeasure]
  exact h _ (vanishesNearZero_mul_normCutoffBCF hr g)

/-- **Uniqueness of limits on sets bounded away from the origin.** Two measures with no mass at
the origin, finite on the complements of balls, which agree on all bounded continuous functions
vanishing near the origin, are equal. -/
theorem ext_of_forall_integral_eq_of_vanishesNearZero {ν : Measure E} (hμ0 : μ {0} = 0)
    (hν0 : ν {0} = 0) (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞) (hν : ∀ r > 0, ν {y | r < ‖y‖} < ∞)
    (h : ∀ f : E →ᵇ ℝ, VanishesNearZero f → ∫ y, f y ∂μ = ∫ y, f y ∂ν) : μ = ν := by
  have hrestr : ∀ r > 0, μ.restrict {y | r < ‖y‖} = ν.restrict {y | r < ‖y‖} := by
    intro r hr
    have := isFiniteMeasure_cutoffMeasure (μ := μ) hr (hμ _ (half_pos hr))
    have := isFiniteMeasure_cutoffMeasure (μ := ν) hr (hν _ (half_pos hr))
    have heq : cutoffMeasure μ r = cutoffMeasure ν r :=
      ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => by
        simp only [integral_cutoffMeasure]
        exact h _ (vanishesNearZero_mul_normCutoffBCF hr g)
    rw [← cutoffMeasure_restrict_eq μ hr, ← cutoffMeasure_restrict_eq ν hr, heq]
  have hU : ({0}ᶜ : Set E) = ⋃ n : ℕ, {y : E | 1 / ((n : ℝ) + 1) < ‖y‖} := by
    ext y
    simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hy
      exact exists_nat_one_div_lt (norm_pos_iff.2 hy)
    · rintro ⟨n, hn⟩ rfl
      simp at hn; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
  have hμc : μ.restrict ({0}ᶜ : Set E) = μ :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 hμ0)
  have hνc : ν.restrict ({0}ᶜ : Set E) = ν :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 hν0)
  rw [← hμc, ← hνc, hU, Measure.restrict_iUnion_congr]
  exact fun n => hrestr _ (by positivity)

omit [BorelSpace E] in
theorem isFiniteMeasure_cutoffMeasure_of_isFiniteMeasure (μ : Measure E) [IsFiniteMeasure μ]
    (r : ℝ) : IsFiniteMeasure (cutoffMeasure μ r) := by
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top μ univ) ?_)
  calc ∫⁻ y, (normCutoff r y : ℝ≥0∞) ∂μ ≤ ∫⁻ _, 1 ∂μ :=
        lintegral_mono fun y => ENNReal.coe_le_one_iff.2 (normCutoff_le_one r y)
    _ = μ univ := lintegral_one

theorem integral_cutoffMeasure_of_ne_zero (μ : Measure E) (hr : 0 < r) {g : E → ℝ}
    (hg : ∀ y, g y ≠ 0 → r ≤ ‖y‖) : ∫ y, g y ∂(cutoffMeasure μ r) = ∫ y, g y ∂μ := by
  rw [integral_cutoffMeasure]
  congr 1; ext y
  by_cases hy : g y = 0
  · simp [hy]
  · simp [normCutoff_eq_one hr (hg y hy)]

omit [BorelSpace E] in
theorem cutoffMeasure_apply_of_subset (μ : Measure E) (hr : 0 < r) {A : Set E}
    (hAm : MeasurableSet A) (hA : A ⊆ {y | r ≤ ‖y‖}) : cutoffMeasure μ r A = μ A := by
  rw [cutoffMeasure, withDensity_apply _ hAm,
    setLIntegral_congr_fun hAm (g := fun _ => 1) (fun y hy => by
      simp [normCutoff_eq_one hr (hA hy)]), setLIntegral_one]

/-- **Portmanteau on sets bounded away from the origin, indicator form.** If finite measures `μs i`
converge to `μ` on bounded continuous functions vanishing near the origin, then also
`∫ H · 1{c < ψ} dμs i → ∫ H · 1{c < ψ} dμ` for `H` bounded continuous and `ψ` continuous with
`{c < ψ}` bounded away from the origin and `μ {ψ = c} = 0`. -/
theorem tendsto_integral_indicator_of_vanishesNearZero (hμs : ∀ i, IsFiniteMeasure (μs i))
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞)
    (h : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
      Tendsto (fun i => ∫ y, f y ∂μs i) l (𝓝 (∫ y, f y ∂μ)))
    (H : E →ᵇ ℝ) {ψ : E → ℝ} (hψ : Continuous ψ) {c : ℝ} (hr : 0 < r)
    (hψr : ∀ y, c < ψ y → r ≤ ‖y‖) (hc : μ {y | ψ y = c} = 0) :
    Tendsto (fun i => ∫ y, {y | c < ψ y}.indicator H y ∂μs i) l
      (𝓝 (∫ y, {y | c < ψ y}.indicator H y ∂μ)) := by
  have := isFiniteMeasure_cutoffMeasure (μ := μ) hr (hμ _ (half_pos hr))
  have key := tendsto_integral_indicator_of_forall_integral_tendsto_of_isFiniteMeasure
    (fun i => isFiniteMeasure_cutoffMeasure_of_isFiniteMeasure (μs i) r)
    (tendsto_integral_cutoffMeasure hr h) H hψ (c := c)
    (withDensity_absolutelyContinuous μ _ hc)
  have hg : ∀ y, {y | c < ψ y}.indicator H y ≠ 0 → r ≤ ‖y‖ := fun y hy =>
    hψr y (by by_contra h'; exact hy (indicator_of_notMem (s := {y | c < ψ y}) h' _))
  simp only [integral_cutoffMeasure_of_ne_zero _ hr hg] at key
  exact key

/-- **Portmanteau on sets bounded away from the origin.** If finite measures `μs i` converge to
`μ` on bounded continuous functions vanishing near the origin, then `μs i A → μ A` for every
measurable `A` bounded away from the origin with `μ (∂A) = 0`. -/
theorem tendsto_measureReal_of_vanishesNearZero (hμs : ∀ i, IsFiniteMeasure (μs i))
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞)
    (h : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
      Tendsto (fun i => ∫ y, f y ∂μs i) l (𝓝 (∫ y, f y ∂μ)))
    {A : Set E} (hAm : MeasurableSet A) (hr : 0 < r) (hA : A ⊆ {y | r ≤ ‖y‖})
    (hfr : μ (frontier A) = 0) : Tendsto (fun i => (μs i).real A) l (𝓝 (μ.real A)) := by
  have := isFiniteMeasure_cutoffMeasure (μ := μ) hr (hμ _ (half_pos hr))
  have key := tendsto_measureReal_of_null_frontier_of_forall_integral_tendsto
    (fun i => isFiniteMeasure_cutoffMeasure_of_isFiniteMeasure (μs i) r)
    (tendsto_integral_cutoffMeasure hr h) (E := A)
    (withDensity_absolutelyContinuous μ _ hfr)
  simp only [measureReal_def, cutoffMeasure_apply_of_subset _ hr hAm hA] at key
  exact key

end M0

/-! ### Regularly varying random vectors -/

section Definition

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Ω → E} {α : ℝ} {μ : Measure E}

/-- The normalized law `P(X / x ∈ ·) / P(‖X‖ > x)`. -/
noncomputable def tailLaw (P : Measure Ω) (X : Ω → E) (x : ℝ) : Measure E :=
  ENNReal.ofReal (P.real {ω | x < ‖X ω‖})⁻¹ • P.map fun ω => x⁻¹ • X ω

instance [IsFiniteMeasure P] (x : ℝ) : IsFiniteMeasure (tailLaw P X x) :=
  ⟨by rw [tailLaw, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem integral_tailLaw (hX : Measurable X) (x : ℝ) {g : E → ℝ} (hg : Measurable g) :
    ∫ y, g y ∂(tailLaw P X x) = (P.real {ω | x < ‖X ω‖})⁻¹ * ∫ ω, g (x⁻¹ • X ω) ∂P := by
  have hm : Measurable fun ω => x⁻¹ • X ω := hX.const_smul _
  rw [tailLaw, integral_smul_measure, integral_map hm.aemeasurable
    hg.aestronglyMeasurable, smul_eq_mul, ENNReal.toReal_ofReal (inv_nonneg.2 measureReal_nonneg)]

theorem tailLaw_real_apply (hX : Measurable X) (x : ℝ) {A : Set E} (hA : MeasurableSet A) :
    (tailLaw P X x).real A = (P.real {ω | x < ‖X ω‖})⁻¹ * P.real {ω | x⁻¹ • X ω ∈ A} := by
  have hm : Measurable fun ω => x⁻¹ • X ω := hX.const_smul _
  rw [measureReal_def, tailLaw, Measure.smul_apply, Measure.map_apply hm hA,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 measureReal_nonneg),
    measureReal_def]
  rfl

/-- **Multivariate regular variation** ([KS20, Definition 2.1.?], Hult–Lindskog's
`M₀`-convergence, [Res07, §6.1]). A random vector `X` is regularly varying with index `α` and
(tail, or exponent) measure `μ` if the tail `P(‖X‖ > x)` of its norm is regularly varying with
index `-α` and
`E[f(X / x)] / P(‖X‖ > x) → ∫ f dμ` as `x → ∞`
for every bounded continuous `f` vanishing on a neighbourhood of the origin; the measure `μ` has no
mass at the origin and is finite on the complement of every ball around the origin. -/
structure IsRegVarVector (P : Measure Ω) (X : Ω → E) (α : ℝ) (μ : Measure E) : Prop where
  isRegularlyVarying : IsRegularlyVarying (fun x => P.real {ω | x < ‖X ω‖}) (-α)
  measure_zero : μ {0} = 0
  measure_lt_top : ∀ r > 0, μ {y | r < ‖y‖} < ∞
  tendsto : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
    Tendsto (fun x => (P.real {ω | x < ‖X ω‖})⁻¹ * ∫ ω, f (x⁻¹ • X ω) ∂P) atTop
      (𝓝 (∫ y, f y ∂μ))

namespace IsRegVarVector

theorem tendsto_tailLaw (h : IsRegVarVector P X α μ) (hX : Measurable X) (f : E →ᵇ ℝ)
    (hf : VanishesNearZero f) :
    Tendsto (fun x => ∫ y, f y ∂(tailLaw P X x)) atTop (𝓝 (∫ y, f y ∂μ)) := by
  simp only [integral_tailLaw hX _ f.continuous.measurable]
  exact h.tendsto f hf

/-- **Portmanteau**: `P(X / x ∈ A) / P(‖X‖ > x) → μ(A)` for measurable `A` bounded away from
the origin with `μ(∂A) = 0`. -/
theorem tendsto_measureReal [IsFiniteMeasure P] (h : IsRegVarVector P X α μ) (hX : Measurable X) {A : Set E}
    (hAm : MeasurableSet A) {r : ℝ} (hr : 0 < r) (hA : A ⊆ {y | r ≤ ‖y‖})
    (hfr : μ (frontier A) = 0) :
    Tendsto (fun x => P.real {ω | x⁻¹ • X ω ∈ A} / P.real {ω | x < ‖X ω‖}) atTop
      (𝓝 (μ.real A)) := by
  have key := tendsto_measureReal_of_vanishesNearZero (fun x => inferInstance)
    h.measure_lt_top (h.tendsto_tailLaw hX) hAm hr hA hfr
  simp only [tailLaw_real_apply hX _ hAm] at key
  exact key.congr fun x => by rw [div_eq_inv_mul]

/-- Portmanteau, indicator form. -/
theorem tendsto_integral_indicator [IsFiniteMeasure P] (h : IsRegVarVector P X α μ) (hX : Measurable X)
    (H : E →ᵇ ℝ) {ψ : E → ℝ} (hψ : Continuous ψ) {c r : ℝ} (hr : 0 < r)
    (hψr : ∀ y, c < ψ y → r ≤ ‖y‖) (hc : μ {y | ψ y = c} = 0) :
    Tendsto (fun x => (P.real {ω | x < ‖X ω‖})⁻¹ *
      ∫ ω, {y | c < ψ y}.indicator H (x⁻¹ • X ω) ∂P) atTop
      (𝓝 (∫ y, {y | c < ψ y}.indicator H y ∂μ)) := by
  have key := tendsto_integral_indicator_of_vanishesNearZero (fun x => inferInstance)
    h.measure_lt_top (h.tendsto_tailLaw hX) H hψ hr hψr hc
  simp only [integral_tailLaw hX _
    ((H.continuous.measurable).indicator (measurableSet_lt measurable_const hψ.measurable))]
    at key
  exact key

/-- The exponent measure is unique. -/
theorem unique {μ' : Measure E} (h : IsRegVarVector P X α μ) (h' : IsRegVarVector P X α μ') :
    μ = μ' :=
  ext_of_forall_integral_eq_of_vanishesNearZero h.measure_zero h'.measure_zero h.measure_lt_top
    h'.measure_lt_top fun f hf => tendsto_nhds_unique (h.tendsto f hf) (h'.tendsto f hf)

/-- **Homogeneity of the exponent measure** ([Res07, Theorem 6.1]): `μ(t⁻¹ · A) = t ^ α μ(A)`,
i.e. the image of `μ` under `y ↦ t • y` is `t ^ α • μ`, for `t > 0`. -/
theorem map_smul (h : IsRegVarVector P X α μ) {t : ℝ} (ht : 0 < t) :
    μ.map (fun y => t • y) = ENNReal.ofReal (t ^ α) • μ := by
  have hsm : Measurable fun y : E => t • y := measurable_const_smul t
  refine ext_of_forall_integral_eq_of_vanishesNearZero ?_ ?_ ?_ ?_ ?_
  · rw [Measure.map_apply hsm (measurableSet_singleton 0)]
    convert h.measure_zero using 2
    ext y; simp [ht.ne']
  · rw [Measure.smul_apply, h.measure_zero, smul_zero]
  · intro r hr
    rw [Measure.map_apply hsm (measurableSet_lt measurable_const continuous_norm.measurable)]
    convert h.measure_lt_top (r / t) (div_pos hr ht) using 2
    ext y
    simp [norm_smul, abs_of_pos ht, div_lt_iff₀ ht, mul_comm]
  · intro r hr
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.measure_lt_top r hr)
  intro f ⟨r, hr, hf⟩
  rw [integral_map hsm.aemeasurable f.continuous.aestronglyMeasurable, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _), smul_eq_mul]
  let g : E →ᵇ ℝ := f.compContinuous ⟨fun y => t • y, continuous_const_smul t⟩
  have hg : VanishesNearZero g := ⟨r / t, div_pos hr ht, fun y hy => hf _ (by
    show ‖t • y‖ < r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rwa [lt_div_iff₀ ht, mul_comm] at hy)⟩
  have h1 := h.tendsto g hg
  have hlim2 := (h.tendsto f ⟨r, hr, hf⟩).comp (tendsto_id.const_mul_atTop (inv_pos.2 ht))
  have hRV := h.isRegularlyVarying.tendsto (inv_pos.2 ht)
  rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv] at hRV
  refine tendsto_nhds_unique h1 ((hRV.mul hlim2).congr' ?_)
  filter_upwards [(tendsto_id.const_mul_atTop (inv_pos.2 ht)).eventually
    h.isRegularlyVarying.eventually_pos, eventually_gt_atTop 0] with x hx hx0
  have hfun : (fun ω => f ((t⁻¹ * x)⁻¹ • X ω)) = fun ω => g (x⁻¹ • X ω) := by
    funext ω
    simp only [g, compContinuous_apply, ContinuousMap.coe_mk, smul_smul]
    congr 2
    field_simp
  show _ * ((P.real {ω | t⁻¹ * x < ‖X ω‖})⁻¹ * ∫ ω, f ((t⁻¹ * x)⁻¹ • X ω) ∂P) = _
  rw [hfun, div_eq_mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ (show P.real {ω | t⁻¹ * x < ‖X ω‖} ≠ 0 from hx.ne'), one_mul]

/-- The exponent measure of a set scaled by `t > 0`: `μ(t • A) = t ^ (-α) μ(A)`. -/
theorem measure_smul_set (h : IsRegVarVector P X α μ) {t : ℝ} (ht : 0 < t) {A : Set E}
    (hA : MeasurableSet A) : μ (t • A) = ENNReal.ofReal (t ^ (-α)) * μ A := by
  have := congrArg (fun ν : Measure E => ν A) (h.map_smul (inv_pos.2 ht))
  simp only [Measure.map_apply (measurable_const_smul _) hA, Measure.smul_apply,
    smul_eq_mul] at this
  rw [Set.preimage_smul_inv₀ ht.ne', Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this
  exact this

/-- Level sets `{ψ = c}`, `c > 0`, of a positively homogeneous function `ψ` are null for the
exponent measure: there are uncountably many disjoint level sets `{ψ = t}`, `t ∈ (c / 2, c)`, in a
region of finite mass, and they all have proportional masses by homogeneity. -/
theorem measure_level_eq_zero (h : IsRegVarVector P X α μ) {ψ : E → ℝ} (hψ : Measurable ψ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ y, ψ (t • y) = t * ψ y) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hψr : ∀ y, c / 2 < ψ y → r < ‖y‖) : μ {y | ψ y = c} = 0 := by
  have hfin : IsFiniteMeasure (μ.restrict {y | r < ‖y‖}) :=
    isFiniteMeasure_restrict.2 (h.measure_lt_top r hr).ne
  have hcount := Measure.countable_meas_level_set_pos (μ := μ.restrict {y | r < ‖y‖}) hψ
  obtain ⟨t, ht, hct⟩ := (hcount.dense_compl ℝ).exists_between (show c / 2 < c by linarith)
  have ht0 : 0 < t := lt_trans (half_pos hc) hct.1
  have hνt : μ.restrict {y | r < ‖y‖} {y | ψ y = t} = 0 := by
    simpa using ht
  have hμt : μ {y | ψ y = t} = 0 := by
    rw [Measure.restrict_apply (measurableSet_eq_fun hψ measurable_const)] at hνt
    rwa [inter_eq_left.2 (show {y | ψ y = t} ⊆ {y | r < ‖y‖} from
      fun y (hy : ψ y = t) => hψr y (by rw [hy]; exact hct.1))] at hνt
  have hpre : {y | ψ y = c} = (fun y => (t / c) • y) ⁻¹' {y | ψ y = t} := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, hhom _ (div_pos ht0 hc)]
    rw [div_mul_eq_mul_div, div_eq_iff hc.ne']
    exact ⟨fun hy => by rw [hy], fun hy => mul_left_cancel₀ ht0.ne' hy⟩
  have := congrArg (fun ν : Measure E => ν {y | ψ y = t}) (h.map_smul (div_pos ht0 hc))
  simp only [Measure.map_apply (measurable_const_smul _)
    (measurableSet_eq_fun hψ measurable_const), Measure.smul_apply, smul_eq_mul, hμt,
    mul_zero] at this
  rw [hpre, this]

/-- The spheres `{‖y‖ = c}`, `c > 0`, are null for the exponent measure. -/
theorem measure_norm_eq_zero (h : IsRegVarVector P X α μ) {c : ℝ} (hc : 0 < c) :
    μ {y | ‖y‖ = c} = 0 :=
  h.measure_level_eq_zero continuous_norm.measurable
    (fun t ht y => by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]) hc (half_pos hc)
    fun _ hy => hy

omit [MeasurableSpace E] [BorelSpace E] in
theorem setOf_one_lt_norm_smul {x : ℝ} (hx : 0 < x) (v : E) :
    1 < ‖x⁻¹ • v‖ ↔ x < ‖v‖ := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hx, lt_inv_mul_iff₀ hx, mul_one]

/-- The exponent measure is normalized: `μ {‖y‖ > 1} = 1`. -/
theorem measure_one_lt_norm [IsFiniteMeasure P] (h : IsRegVarVector P X α μ)
    (hX : Measurable X) : μ {y | 1 < ‖y‖} = 1 := by
  have hm : MeasurableSet {y : E | 1 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have key := h.tendsto_measureReal hX hm one_pos (fun y (hy : 1 < ‖y‖) => hy.le)
    (measure_mono_null (frontier_lt_subset_eq continuous_const continuous_norm) (by
      simpa [eq_comm] using h.measure_norm_eq_zero one_pos))
  have h1 : μ.real {y | 1 < ‖y‖} = 1 := by
    refine tendsto_nhds_unique key (tendsto_const_nhds.congr' ?_)
    filter_upwards [h.isRegularlyVarying.eventually_pos, eventually_gt_atTop 0] with x hx hx0
    have : {ω | 1 < ‖x⁻¹ • X ω‖} = {ω | x < ‖X ω‖} := by
      ext ω; exact setOf_one_lt_norm_smul hx0 (X ω)
    rw [this, div_self hx.ne']
  rw [← ofReal_measureReal (h.measure_lt_top 1 one_pos).ne, h1, ENNReal.ofReal_one]

/-- The radial part of the exponent measure is Pareto: `μ {‖y‖ > u} = u ^ (-α)`. -/
theorem measure_lt_norm [IsFiniteMeasure P] (h : IsRegVarVector P X α μ) (hX : Measurable X)
    {u : ℝ} (hu : 0 < u) : μ {y | u < ‖y‖} = ENNReal.ofReal (u ^ (-α)) := by
  have := congrArg (fun ν : Measure E => ν {y | 1 < ‖y‖}) (h.map_smul (inv_pos.2 hu))
  simp only [Measure.map_apply (measurable_const_smul _)
    (measurableSet_lt measurable_const continuous_norm.measurable), Measure.smul_apply,
    smul_eq_mul, h.measure_one_lt_norm hX, mul_one] at this
  rw [Real.inv_rpow hu.le, ← Real.rpow_neg hu.le] at this
  rw [← this]
  congr 1
  ext y
  exact (setOf_one_lt_norm_smul hu y).symm

end IsRegVarVector

end Definition

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
`Y` distributed as `μ` restricted to `{‖y‖ > 1}` ([KS20, Proposition 2.1.?]). -/
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
  let g : E →ᵇ ℝ := BoundedContinuousFunction.ofAbsLe (fun θ => min 1 |‖θ‖ - 1|)
    (continuous_const.min ((continuous_norm.sub continuous_const).abs)) 1 fun θ => by
      rw [abs_of_nonneg (le_min zero_le_one (abs_nonneg _))]; exact min_le_left _ _
  have key := hS.ae_eq_zero g (fun θ => le_min zero_le_one (abs_nonneg _)) ?_
  · filter_upwards [key] with θ hθ
    simp only [g, BoundedContinuousFunction.ofAbsLe_apply] at hθ
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
    let d : E →ᵇ ℝ := BoundedContinuousFunction.ofAbsLe (fun y => min 1 (Metric.infDist y C))
      (continuous_const.min (Metric.continuous_infDist_pt C)) 1 fun y => by
        rw [abs_of_nonneg (le_min zero_le_one Metric.infDist_nonneg)]; exact min_le_left _ _
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
