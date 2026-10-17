/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak convergence of families of measures, tested against functions

Mathlib states weak convergence for families `μs : γ → ProbabilityMeasure Ω`. In applications the
measures are often only *eventually* probability measures (for example conditional laws
`P[|{x < Z}]`, which are probability measures only once `P {x < Z} ≠ 0`). Here we restate a few
portmanteau-type results for families `μs : γ → Measure Ω` which are eventually probability
measures, with weak convergence phrased through integrals of bounded continuous functions.

## Main results

* `MeasureTheory.tendsto_integral_of_forall_lipschitz`: convergence of the integrals of bounded
  Lipschitz functions implies convergence for all bounded continuous functions.
* `MeasureTheory.tendsto_measure_of_null_frontier_of_forall_integral_tendsto`: the portmanteau
  implication for sets with null frontier.
-/

open Filter Topology Set BoundedContinuousFunction

namespace MeasureTheory

variable {γ Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A family of measures which are eventually probability measures agrees eventually with a
family of probability measures. -/
theorem exists_probabilityMeasure_eventuallyEq {F : Filter γ} {μs : γ → Measure Ω}
    (hμs : ∀ᶠ i in F, IsProbabilityMeasure (μs i)) (μ : ProbabilityMeasure Ω) :
    ∃ νs : γ → ProbabilityMeasure Ω, ∀ᶠ i in F, (νs i : Measure Ω) = μs i := by
  classical
  refine ⟨fun i => if h : IsProbabilityMeasure (μs i) then ⟨μs i, h⟩ else μ, ?_⟩
  filter_upwards [hμs] with i hi
  simp [hi]

/-- A family of measures, eventually probability measures, whose integrals of bounded continuous
functions converge to those of a probability measure `μ`, converges weakly to `μ` after
replacing it by a family of probability measures. -/
theorem exists_tendsto_probabilityMeasure [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {F : Filter γ} {μs : γ → Measure Ω} (hμs : ∀ᶠ i in F, IsProbabilityMeasure (μs i))
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂μ))) :
    ∃ νs : γ → ProbabilityMeasure Ω, (∀ᶠ i in F, (νs i : Measure Ω) = μs i) ∧
      Tendsto νs F (𝓝 ⟨μ, inferInstance⟩) := by
  obtain ⟨νs, hνs⟩ := exists_probabilityMeasure_eventuallyEq hμs ⟨μ, inferInstance⟩
  refine ⟨νs, hνs, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_⟩
  refine (h f).congr' ?_
  filter_upwards [hνs] with i hi
  rw [hi]

/-- Weak convergence can be tested on bounded Lipschitz functions: version for families of
measures which are eventually probability measures. -/
theorem tendsto_integral_of_forall_lipschitz [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {F : Filter γ} [F.IsCountablyGenerated] {μs : γ → Measure Ω}
    (hμs : ∀ᶠ i in F, IsProbabilityMeasure (μs i)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ∀ f : Ω → ℝ, (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) → (∃ L, LipschitzWith L f) →
      Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂μ)))
    (f : Ω →ᵇ ℝ) : Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂μ)) := by
  obtain ⟨νs, hνs⟩ := exists_probabilityMeasure_eventuallyEq hμs ⟨μ, inferInstance⟩
  have key : Tendsto νs F (𝓝 ⟨μ, inferInstance⟩) := by
    refine tendsto_iff_forall_lipschitz_integral_tendsto.2 fun g hgb hgL => ?_
    refine (h g hgb hgL).congr' ?_
    filter_upwards [hνs] with i hi
    rw [hi]
  refine ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 key) f).congr' ?_
  filter_upwards [hνs] with i hi
  rw [hi]

/-- The portmanteau implication for sets with null frontier: version for families of measures
which are eventually probability measures, with weak convergence tested on bounded continuous
functions. -/
theorem tendsto_measure_of_null_frontier_of_forall_integral_tendsto [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] {F : Filter γ} {μs : γ → Measure Ω}
    (hμs : ∀ᶠ i in F, IsProbabilityMeasure (μs i)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂μ)))
    {E : Set Ω} (hE : μ (frontier E) = 0) : Tendsto (fun i => μs i E) F (𝓝 (μ E)) := by
  obtain ⟨νs, hνs, key⟩ := exists_tendsto_probabilityMeasure hμs h
  refine (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' key hE).congr' ?_
  filter_upwards [hνs] with i hi
  rw [hi]

/-- A continuous real function with `|f| ≤ C`, as a bounded continuous function. -/
noncomputable def _root_.BoundedContinuousFunction.ofAbsLe [TopologicalSpace Ω] (f : Ω → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : Ω →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C) fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    linarith [abs_sub (f x) (f y), hC x, hC y]

@[simp]
theorem _root_.BoundedContinuousFunction.ofAbsLe_apply [TopologicalSpace Ω] (f : Ω → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) (x : Ω) :
    BoundedContinuousFunction.ofAbsLe f hf C hC x = f x := rfl

/-- Weak convergence, tested on bounded continuous functions, extends to `H · 1{c < ψ}` for
`H` bounded continuous and `ψ` continuous, provided the limit gives no mass to `{ψ = c}`. -/
theorem tendsto_integral_indicator_of_forall_integral_tendsto [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] {F : Filter γ} {μs : γ → Measure Ω}
    (hμs : ∀ᶠ i in F, IsProbabilityMeasure (μs i)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂μ)))
    (H : Ω →ᵇ ℝ) {ψ : Ω → ℝ} (hψ : Continuous ψ) {c : ℝ} (hc : μ {y | ψ y = c} = 0) :
    Tendsto (fun i => ∫ y, {y | c < ψ y}.indicator H y ∂μs i) F
      (𝓝 (∫ y, {y | c < ψ y}.indicator H y ∂μ)) := by
  set M := ‖H‖
  have hM : ∀ y, |H y| ≤ M := fun y => by simpa [Real.norm_eq_abs] using H.norm_coe_le_norm y
  have hM0 : 0 ≤ M := norm_nonneg _
  have hmeasS : MeasurableSet {y | c < ψ y} := measurableSet_lt measurable_const hψ.measurable
  -- the approximations
  let φ : ℝ → Ω → ℝ := fun η y => min 1 (max 0 ((ψ y - c) / η))
  let χ : ℝ → Ω → ℝ := fun η y => min 1 (max 0 (2 - |ψ y - c| / η))
  have hφc : ∀ η, Continuous (φ η) := fun η =>
    continuous_const.min (continuous_const.max ((hψ.sub continuous_const).div_const η))
  have hχc : ∀ η, Continuous (χ η) := fun η =>
    continuous_const.min (continuous_const.max
      (continuous_const.sub ((hψ.sub continuous_const).abs.div_const η)))
  have hφb : ∀ η y, |φ η y| ≤ 1 := fun η y => by
    rw [abs_le]; constructor
    · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (le_min zero_le_one (le_max_left _ _))
    · exact min_le_left _ _
  have hχ0 : ∀ η y, 0 ≤ χ η y := fun η y => le_min zero_le_one (le_max_left _ _)
  have hχb : ∀ η y, |χ η y| ≤ 1 := fun η y => by
    rw [abs_of_nonneg (hχ0 η y)]; exact min_le_left _ _
  have hkey : ∀ η, 0 < η → ∀ y,
      |{y | c < ψ y}.indicator H y - H y * φ η y| ≤ M * χ η y := by
    intro η hη y
    by_cases h1 : c < ψ y
    · rw [indicator_of_mem (show y ∈ {y | c < ψ y} from h1), ← mul_one_sub, abs_mul]
      by_cases h2 : ψ y < c + η
      · have hχ1 : χ η y = 1 := by
          refine min_eq_left (le_max_of_le_right ?_)
          rw [abs_of_pos (sub_pos.2 h1), le_sub_comm, div_le_iff₀ hη]
          linarith
        rw [hχ1, mul_one]
        have h3 : |1 - φ η y| ≤ 1 := by
          rw [abs_le]; constructor
          · linarith [min_le_left 1 (max 0 ((ψ y - c) / η))]
          · linarith [le_min zero_le_one (le_max_left 0 ((ψ y - c) / η))]
        nlinarith [hM y, abs_nonneg (H y), abs_nonneg (1 - φ η y)]
      · have hφ1 : φ η y = 1 := by
          refine min_eq_left (le_max_of_le_right ?_)
          rw [le_div_iff₀ hη]; linarith
        rw [hφ1, sub_self, abs_zero, mul_zero]
        exact mul_nonneg hM0 (hχ0 η y)
    · have hφ0 : φ η y = 0 := by
        refine le_antisymm (min_le_of_right_le (max_le le_rfl ?_)) (le_min zero_le_one
          (le_max_left _ _))
        exact div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 h1]) hη.le
      rw [indicator_of_notMem (show y ∉ {y | c < ψ y} from h1), hφ0, mul_zero, sub_zero,
        abs_zero]
      exact mul_nonneg hM0 (hχ0 η y)
  -- `∫ χ_η dμ → 0`
  have hχlim : Tendsto (fun n : ℕ => ∫ y, χ (1 / ((n : ℝ) + 1)) y ∂μ) atTop (𝓝 0) := by
    have hlim : ∀ y, Tendsto (fun n : ℕ => χ (1 / ((n : ℝ) + 1)) y) atTop
        (𝓝 ({y | ψ y = c}.indicator 1 y)) := by
      intro y
      by_cases hy : ψ y = c
      · rw [indicator_of_mem (show y ∈ {y | ψ y = c} from hy)]
        refine tendsto_const_nhds.congr fun n => ?_
        simp [χ, hy]
      · rw [indicator_of_notMem (show y ∉ {y | ψ y = c} from hy)]
        have hpos : 0 < |ψ y - c| := abs_pos.2 (sub_ne_zero.2 hy)
        have : Tendsto (fun n : ℕ => 2 - |ψ y - c| / (1 / ((n : ℝ) + 1))) atTop atBot := by
          simp only [div_div_eq_mul_div, div_one]
          exact tendsto_atBot_add_const_left _ 2 (tendsto_neg_atTop_atBot.comp
            (Tendsto.const_mul_atTop hpos (tendsto_atTop_add_const_right _ 1
              tendsto_natCast_atTop_atTop)) |>.congr fun n => by simp)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [this.eventually (eventually_le_atBot 0)] with n hn
        show 0 = min 1 (max 0 (2 - |ψ y - c| / (1 / ((n : ℝ) + 1))))
        rw [max_eq_left hn, min_eq_right zero_le_one]
    have := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
      (fun n => (hχc _).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hχb _ y)
      (ae_of_all _ hlim)
    rwa [integral_indicator_one (measurableSet_eq_fun hψ.measurable measurable_const),
      measureReal_def, hc, ENNReal.toReal_zero] at this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (hχlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (4 * (M + 1)) by
    positivity))).exists
  set η : ℝ := 1 / ((n : ℝ) + 1)
  have hη : 0 < η := by positivity
  let χb := BoundedContinuousFunction.ofAbsLe (χ η) (hχc η) 1 (hχb η)
  let Hφ := BoundedContinuousFunction.ofAbsLe (fun y => H y * φ η y)
    (H.continuous.mul (hφc η)) M fun y => by
      rw [abs_mul]; nlinarith [hM y, hφb η y, abs_nonneg (H y), abs_nonneg (φ η y)]
  have h1 := (h χb).eventually (gt_mem_nhds hn)
  have h2 := Metric.tendsto_nhds.1 (h Hφ) (ε / 4) (by positivity)
  have hint : ∀ ν : Measure Ω, IsProbabilityMeasure ν →
      |∫ y, {y | c < ψ y}.indicator H y ∂ν - ∫ y, H y * φ η y ∂ν| ≤ M * ∫ y, χ η y ∂ν := by
    intro ν hν
    have hi1 : Integrable ({y | c < ψ y}.indicator H) ν :=
      (H.integrable ν).indicator hmeasS
    have hi2 : Integrable (fun y => H y * φ η y) ν := Hφ.integrable ν
    rw [← integral_sub hi1 hi2, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono (hi1.sub hi2).abs
      ((χb.integrable ν).const_mul M) fun y => hkey η hη y)
  filter_upwards [h1, h2, hμs] with i hi1 hi2 hi3
  simp only [χb, Hφ, BoundedContinuousFunction.ofAbsLe_apply] at hi1 hi2
  rw [Real.dist_eq] at hi2 ⊢
  have e1 := hint (μs i) hi3
  have e2 := hint μ inferInstance
  have hM1 : M * ∫ y, χ η y ∂μs i ≤ (M + 1) * (ε / (4 * (M + 1))) := by
    have := integral_nonneg (μ := μs i) (f := χ η) (hχ0 η)
    have : 0 < ε / (4 * (M + 1)) := by positivity
    nlinarith
  have hM2 : M * ∫ y, χ η y ∂μ ≤ (M + 1) * (ε / (4 * (M + 1))) := by
    have := integral_nonneg (μ := μ) (f := χ η) (hχ0 η)
    have : 0 < ε / (4 * (M + 1)) := by positivity
    nlinarith
  have hfrac : (M + 1) * (ε / (4 * (M + 1))) = ε / 4 := by field_simp
  have t1 := abs_sub_le (∫ y, {y | c < ψ y}.indicator H y ∂μs i) (∫ y, H y * φ η y ∂μs i)
    (∫ y, {y | c < ψ y}.indicator H y ∂μ)
  have t2 := abs_sub_le (∫ y, H y * φ η y ∂μs i) (∫ y, H y * φ η y ∂μ)
    (∫ y, {y | c < ψ y}.indicator H y ∂μ)
  rw [abs_sub_comm (∫ y, H y * φ η y ∂μ)] at t2
  linarith

/-- Limits of weak convergence, tested on bounded continuous functions, are unique. -/
theorem eq_of_forall_integral_tendsto [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {F : Filter γ} [F.NeBot] {μs : γ → Measure Ω} {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂μ)))
    (hν : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂ν))) : μ = ν :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => tendsto_nhds_unique (hμ f) (hν f)

end MeasureTheory
