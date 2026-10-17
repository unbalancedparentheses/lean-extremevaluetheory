/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TailProcess

/-!
# Multivariate regular variation

TODO docs
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

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

end ExtremeValueTheory
