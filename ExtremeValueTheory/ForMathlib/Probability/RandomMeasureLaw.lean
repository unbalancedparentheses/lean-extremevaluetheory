/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.PoissonRandomMeasureLaplace
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.UnitInterval

/-!
# The law of a random measure is determined by its Laplace functional

-/

open MeasureTheory Filter Finset Topology
open scoped ENNReal NNReal unitInterval BoundedContinuousFunction

namespace ProbabilityTheory

section Moments

variable {k : ℕ}

/-- The coordinate functions of the cube `[0, 1] ^ k`, as bounded continuous functions. -/
noncomputable def cubeCoord (i : Fin k) : (Fin k → I) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun y ↦ (y i : ℝ), by fun_prop⟩

/-- The monomials on the cube `[0, 1] ^ k`, as bounded continuous functions. -/
noncomputable def cubeMonomial (a : Fin k → ℕ) : (Fin k → I) →ᵇ ℝ :=
  ∏ i, cubeCoord i ^ a i

lemma cubeMonomial_apply (a : Fin k → ℕ) (y : Fin k → I) :
    cubeMonomial a y = ∏ i, (y i : ℝ) ^ a i := by
  simp [cubeMonomial, cubeCoord, BoundedContinuousFunction.coe_prod]

/-- **Finite measures on the cube `[0, 1] ^ k` are determined by their moments.** -/
theorem ext_of_forall_integral_prod_pow_eq {μ ν : Measure (Fin k → I)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ a : Fin k → ℕ, ∫ y, ∏ i, (y i : ℝ) ^ a i ∂μ = ∫ y, ∏ i, (y i : ℝ) ^ a i ∂ν) :
    μ = ν := by
  set V := Submodule.span ℝ (Set.range (cubeMonomial (k := k))) with hV
  have hint : ∀ g ∈ V, ∫ y, g y ∂μ = ∫ y, g y ∂ν := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, rfl⟩ := hg
      simp_rw [cubeMonomial_apply]
      exact h a
    | zero => simp
    | add f g _ _ hf hg =>
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
      rw [integral_add (f.integrable μ) (g.integrable μ),
        integral_add (f.integrable ν) (g.integrable ν), hf, hg]
    | smul r f _ hf =>
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hf]
  have hmul : ∀ f ∈ V, ∀ g ∈ V, f * g ∈ V := by
    intro f hf g hg
    have : f * g ∈ V * V := Submodule.mul_mem_mul hf hg
    rw [hV, Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    refine ⟨a + b, ?_⟩
    simp only [cubeMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  have hA : ∀ g ∈ StarAlgebra.adjoin ℝ (Set.range (cubeCoord (k := k))), g ∈ V := by
    intro g hg
    induction hg using StarAlgebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine Submodule.subset_span ⟨Pi.single i 1, ?_⟩
      ext y
      simp [cubeMonomial_apply, cubeCoord, Pi.single_apply, Finset.prod_ite_eq']
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      refine Submodule.smul_mem _ r (Submodule.subset_span ⟨0, ?_⟩)
      simp [cubeMonomial]
    | add f g _ _ hf hg => exact add_mem hf hg
    | mul f g _ _ hf hg => exact hmul f hf g hg
    | star f _ hf =>
      have : star f = f := by
        ext y
        simp
      rwa [this]
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable (𝕜 := ℝ)
    (A := StarAlgebra.adjoin ℝ (Set.range (cubeCoord (k := k)))) ?_ fun g hg ↦ hint g (hA g hg)
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h'
    exact hxy (funext h')
  refine ⟨_, ⟨_, ⟨cubeCoord i, StarAlgebra.subset_adjoin ℝ _ ⟨i, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  simpa [cubeCoord, Subtype.ext_iff] using hi

end Moments

end ProbabilityTheory
