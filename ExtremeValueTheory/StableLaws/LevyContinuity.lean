/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Lévy's continuity theorem, existence form

Mathlib's `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` is Lévy's convergence
theorem when the limit is already known to be a probability measure. Here we prove the full
continuity theorem ([Feller, Vol. II, §XV.3, Theorem 2]): if the characteristic functions of a
sequence of probability measures converge pointwise to a function `f` that is continuous at
`0`, then `f` *is* the characteristic function of a probability measure `ν`, and the sequence
converges weakly to `ν`.

The proof combines Mathlib's tightness criterion `isTightMeasureSet_of_tendsto_charFun`,
Prokhorov's theorem `isCompact_closure_of_isTightMeasureSet`, and continuity of
`ν ↦ charFun ν t` for the weak topology: a cluster point `ν` of the sequence has
`charFun ν = f`, and convergence then follows from Mathlib's Lévy convergence theorem.
-/

open MeasureTheory Filter Topology Set

namespace ExtremeValueTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- `ν ↦ charFun ν t` is continuous for the topology of weak convergence. -/
theorem continuous_charFun_probabilityMeasure (t : E) :
    Continuous fun ν : ProbabilityMeasure E => charFun (ν : Measure E) t := by
  rw [continuous_iff_continuousAt]
  intro ν
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ
    (μs := fun m : ProbabilityMeasure E => m) (F := 𝓝 ν) (μ := ν)).1 tendsto_id (BoundedContinuousFunction.innerProbChar t)
  simpa [ContinuousAt, ← charFun_eq_integral_innerProbChar] using h

/-- **Lévy's continuity theorem** ([Feller, Vol. II, §XV.3, Theorem 2]). If the characteristic
functions of probability measures `μ n` converge pointwise to a function `f` continuous at `0`,
then there is a probability measure `ν` with `charFun ν = f`, and `μ n → ν` weakly. -/
theorem exists_tendsto_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure E} {f : E → ℂ}
    (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n => charFun (μ n : Measure E) t) atTop (𝓝 (f t))) :
    ∃ ν : ProbabilityMeasure E, charFun (ν : Measure E) = f ∧ Tendsto μ atTop (𝓝 ν) := by
  have htight := isTightMeasureSet_of_tendsto_charFun (μ := fun n => (μ n : Measure E)) hf h
  have hS : {m : Measure E | ∃ ν ∈ range μ, (ν : Measure E) = m} =
      range fun n => (μ n : Measure E) := by
    ext m; simp
  have hK := isCompact_closure_of_isTightMeasureSet (S := range μ) (by rw [hS]; exact htight)
  have hle : map μ atTop ≤ 𝓟 (closure (range μ)) :=
    tendsto_principal.2 (Eventually.of_forall fun n => subset_closure (mem_range_self n))
  obtain ⟨ν, -, hν⟩ := hK.exists_clusterPt hle
  have hchar : charFun (ν : Measure E) = f := by
    funext t
    have hc := hν.map (continuous_charFun_probabilityMeasure t).continuousAt
      (ly := 𝓝 (f t)) (tendsto_map'_iff.2 (h t))
    exact eq_of_nhds_neBot hc
  refine ⟨ν, hchar, ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_⟩
  rw [hchar]; exact h t

end ExtremeValueTheory
