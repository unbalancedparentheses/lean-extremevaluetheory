/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Mixing

/-!
# `β`-mixing and the block condition

`β`-mixing coefficients are at most `1` (`betaMixingCoeff_le_one`, `betaMixing_le_one`), so the
inequality `α ≤ β` passes to real parts and `β`-mixing with a rate gives the block condition
`𝒜(uₙ)` directly (`conditionA_of_betaMixing`), as strong mixing does
(`conditionA_of_alphaMixing`). For `m`-dependent sequences the `β` coefficients vanish beyond lag
`m` (`IsMDependent.betaMixing_eq_zero`, already in `ForMathlib/Probability/Process/Mixing.lean`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The `β`-mixing coefficient of two sub-σ-algebras is at most `1`. -/
theorem betaMixingCoeff_le_one [IsProbabilityMeasure P] {m₁ m₂ : MeasurableSpace Ω}
    (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) : betaMixingCoeff m₁ m₂ P ≤ 1 := by
  simp only [betaMixingCoeff, iSup_le_iff]
  intro k l A hA hdA huA B hB hdB huB
  rw [ENNReal.ofReal_le_one]
  have hAm : ∀ i, MeasurableSet[mΩ] (A i) := fun i => h₁ _ (hA i)
  have hBm : ∀ j, MeasurableSet[mΩ] (B j) := fun j => h₂ _ (hB j)
  have hsA : ∑ i, P.real (A i) = 1 := by
    rw [← measureReal_iUnion_fintype (μ := P) hdA hAm, huA, probReal_univ]
  have hsB : ∑ j, P.real (B j) = 1 := by
    rw [← measureReal_iUnion_fintype (μ := P) hdB hBm, huB, probReal_univ]
  have hsAB : ∑ i, ∑ j, P.real (A i ∩ B j) = 1 := by
    rw [← hsA]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← measureReal_iUnion_fintype (μ := P) (f := fun j => A i ∩ B j)
      (fun j j' hjj' => ((hdB hjj').mono Set.inter_subset_right Set.inter_subset_right))
      fun j => (hAm i).inter (hBm j), ← Set.inter_iUnion, huB, Set.inter_univ]
  have hle : ∀ i j, |P.real (A i ∩ B j) - P.real (A i) * P.real (B j)| ≤
      P.real (A i ∩ B j) + P.real (A i) * P.real (B j) := fun i j =>
    (abs_sub _ _).trans_eq (by
      rw [abs_of_nonneg measureReal_nonneg,
        abs_of_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)])
  calc 2⁻¹ * ∑ i, ∑ j, |P.real (A i ∩ B j) - P.real (A i) * P.real (B j)|
      ≤ 2⁻¹ * ∑ i, ∑ j, (P.real (A i ∩ B j) + P.real (A i) * P.real (B j)) := by
        gcongr with i _ j _
        exact hle i j
    _ = 2⁻¹ * (∑ i, ∑ j, P.real (A i ∩ B j) + (∑ i, P.real (A i)) * ∑ j, P.real (B j)) := by
        rw [Finset.sum_mul_sum]
        simp only [Finset.sum_add_distrib]
    _ = 1 := by rw [hsAB, hsA, hsB]; norm_num

/-- The `β`-mixing coefficients of a process are at most `1`. -/
theorem betaMixing_le_one [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E]
    {X : ℕ → Ω → E} (hX : ∀ t, Measurable (X t)) (h : ℕ) : betaMixing X P h ≤ 1 :=
  iSup_le fun s => betaMixingCoeff_le_one (pastMeasurableSpace_le hX s)
    (futureMeasurableSpace_le hX _)

theorem betaMixing_ne_top [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E]
    {X : ℕ → Ω → E} (hX : ∀ t, Measurable (X t)) (h : ℕ) : betaMixing X P h ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (betaMixing_le_one hX h)

/-- `α(h) ≤ β(h)` for the real parts of the mixing coefficients. -/
theorem alphaMixing_toReal_le_betaMixing_toReal [IsProbabilityMeasure P] {E : Type*}
    [MeasurableSpace E] {X : ℕ → Ω → E} (hX : ∀ t, Measurable (X t)) (h : ℕ) :
    (alphaMixing X P h).toReal ≤ (betaMixing X P h).toReal :=
  ENNReal.toReal_mono (betaMixing_ne_top hX h) (alphaMixing_le_betaMixing hX h)

/-- **`β`-mixing implies the block condition**: if `X` is stationary, `rₙ → ∞`, `rₙ / n → 0`,
`lₙ / rₙ → 0`, `(n / rₙ) β(lₙ) → 0` for the `β`-mixing coefficients of `X`, and `n P(X 0 > uₙ)`
is bounded, then `𝒜(uₙ)` holds. -/
theorem conditionA_of_betaMixing [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hs : IsStationary X P) (hX : ∀ t, Measurable (X t)) {u : ℕ → ℝ} {r l : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlr : Tendsto (fun n => (l n : ℝ) / r n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => (n : ℝ) / r n * (betaMixing X P (l n)).toReal) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n : ℕ in atTop, (n : ℝ) * P.real {ω | u n < X 0 ω} ≤ C) :
    ConditionA X P u r :=
  conditionA_of_forall_abs_le hs hX (fun n _ _ _ _ hAB =>
    (abs_measureReal_maxLE_union_sub_le_alphaMixing hAB (u n)).trans
      (alphaMixing_toReal_le_betaMixing_toReal hX _)) hr hrn hlr hβ hC

end ExtremeValueTheory
