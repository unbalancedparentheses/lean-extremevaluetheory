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

end ExtremeValueTheory
