/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.MeasureTheory.Measure.Portmanteau

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

/-- Limits of weak convergence, tested on bounded continuous functions, are unique. -/
theorem eq_of_forall_integral_tendsto [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {F : Filter γ} [F.NeBot] {μs : γ → Measure Ω} {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂μ)))
    (hν : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ ω, f ω ∂μs i) F (𝓝 (∫ ω, f ω ∂ν))) : μ = ν :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => tendsto_nhds_unique (hμ f) (hν f)

end MeasureTheory
