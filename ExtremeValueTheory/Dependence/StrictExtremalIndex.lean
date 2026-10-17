/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MDependentExamples
import ExtremeValueTheory.Dependence.InfiniteMovingAverageTailProcess
import ExtremeValueTheory.Dependence.AR1
import ExtremeValueTheory.Dependence.ThetaLeVartheta

/-!
# Exceedance levels for regularly varying tails and strict extremal indices

`HasExtremalIndex X P θ` quantifies over level sequences `uₙ` with `n P(X_0 > uₙ) → τ`; it is
vacuous at values `τ` attained by no such sequence. `HasExtremalIndexStrict` adds the existence of
such levels for every `τ > 0`, which makes `θ` unique (`HasExtremalIndexStrict.unique`).

For a regularly varying tail `F̄(x) = P(X_0 > x)` such levels always exist ([LLR, Theorem 1.7.13]):
`F̄(x-) / F̄(x) → 1`, so the quantile levels `uₙ ≈ inf {x : F̄(x) ≤ τ / n}` satisfy
`n F̄(uₙ) → τ`. We prove this without left limits: `F̄((1 - ε) uₙ) > τ / n ≥ F̄(uₙ)` and
`F̄((1 - ε) x) / F̄(x) → (1 - ε)^ρ`, which is close to `1` for small `ε`.

## Main results

* `hasExceedanceLevels_of_isRegularlyVarying`: a regularly varying marginal tail (any index)
  admits exceedance levels.
* `HasSpectralTailProcess.hasExceedanceLevels_abs`: hence `(|X_n|)` admits exceedance levels
  whenever `X` has a spectral tail process.
* Strict versions (`HasExtremalIndexStrict`, so `θ` is unique) of the extremal-index theorems:
  `HasSpectralTailProcess.hasExtremalIndex_abs_strict`,
  `HasSpectralTailProcess.hasExtremalIndex_of_isMDependent_strict`,
  `hasExtremalIndex_movingMax_of_isMDependent_strict`, `MovingAverage.hasExtremalIndex_strict`,
  `InfiniteMovingAverage.hasExtremalIndex_strict`, `AR1.hasExtremalIndex_strict`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace ExtremeValueTheory

section Levels

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- A regularly varying marginal tail gives the strict extremal index from the extremal index. -/
theorem HasExtremalIndex.strict_of_isRegularlyVarying {θ : ℝ} (h : HasExtremalIndex X P θ)
    (hX0 : Measurable (X 0)) {ρ : ℝ}
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < X 0 ω}) ρ) :
    HasExtremalIndexStrict X P θ :=
  ⟨h, hasExceedanceLevels_of_isRegularlyVarying hX0 hRV⟩

end Levels

section TailProcess

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

omit [IsProbabilityMeasure Q] in
/-- The nonnegative version of `HasSpectralTailProcess.hasExceedanceLevels_abs`. -/
theorem HasSpectralTailProcess.hasExceedanceLevels_of_nonneg
    (h : HasSpectralTailProcess P X α Q Θ) (hX0 : Measurable (X 0)) (hnn : ∀ ω, 0 ≤ X 0 ω) :
    HasExceedanceLevels (fun k : ℕ => X k) P :=
  hasExceedanceLevels_of_isRegularlyVarying (X := fun k : ℕ => X k) (by simpa using hX0)
    (by simpa [abs_of_nonneg (hnn _)] using h.1)

/-- **Strict form of `HasSpectralTailProcess.hasExtremalIndex_abs`**: `θ = ϑ` for `(|X_n|)`, and
`θ` is the unique extremal index. -/
theorem HasSpectralTailProcess.hasExtremalIndex_abs_strict (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hcond : ∀ τ > 0, ∀ u : ℕ → ℝ,
      Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ) →
        ForwardAntiClusteringAt P X u r ∧ ConditionA (fun k : ℕ => |X k|) P u r) :
    HasExtremalIndexStrict (fun k : ℕ => |X k|) P (candidateExtremalIndex Q Θ α).toReal :=
  ⟨h.hasExtremalIndex_abs hα hX hΘm hstat hr hrn hcond, h.hasExceedanceLevels_abs hX⟩

/-- **Strict form of `HasSpectralTailProcess.hasExtremalIndex_of_isMDependent`**. -/
theorem HasSpectralTailProcess.hasExtremalIndex_of_isMDependent_strict (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {m : ℕ}
    (hm : IsMDependent (fun n : ℕ => X n) m P) :
    HasExtremalIndexStrict (fun k : ℕ => |X k|) P (candidateExtremalIndex Q Θ α).toReal :=
  ⟨h.hasExtremalIndex_of_isMDependent hα hX hΘm hstat hm, h.hasExceedanceLevels_abs hX⟩

end TailProcess

section Examples

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℤ → Ω → ℝ} {α : ℝ}

/-- **Strict form of `hasExtremalIndex_movingMax_of_isMDependent`**: the moving maximum of iid
Pareto noise has the unique extremal index `1/2`. -/
theorem hasExtremalIndex_movingMax_of_isMDependent_strict (hα : 0 < α)
    (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω) :
    HasExtremalIndexStrict (fun n : ℕ => movingMax Z n) P 2⁻¹ :=
  ⟨hasExtremalIndex_movingMax_of_isMDependent hα hZ hind hlaw hpos,
    (hasSpectralTailProcess_movingMax hα hZ hind hlaw hpos).hasExceedanceLevels_of_nonneg
      ((hZ 0).max (hZ (0 + 1))) fun ω => (hpos 0 ω).trans (le_max_left _ _)⟩

/-- **Strict form of `MovingAverage.hasExtremalIndex`**. -/
theorem MovingAverage.hasExtremalIndex_strict {m : ℕ} {ψ : ℕ → ℝ} (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψm : ∀ j, m < j → ψ j = 0) (hW : 0 < MovingAverage.weightSum m ψ α) :
    HasExtremalIndexStrict (fun n : ℕ => MovingAverage.process m ψ Z n) P
      ((Finset.range (m + 1)).sup' Finset.nonempty_range_add_one ψ ^ α /
        ∑ j ∈ Finset.range (m + 1), ψ j ^ α) :=
  ⟨MovingAverage.hasExtremalIndex hZ hind hident hZ0 hα hL hψ0 hψm hW,
    (MovingAverage.exists_hasSpectralTailProcess_candidateExtremalIndex_eq hZ hind hident hZ0 hα
      hL hψ0 hψm hW).1.hasExceedanceLevels_of_nonneg (MovingAverage.measurable_process hZ 0)
      (MovingAverage.process_nonneg hψ0 hZ0 0)⟩

/-- **Strict form of `InfiniteMovingAverage.hasExtremalIndex`**. -/
theorem InfiniteMovingAverage.hasExtremalIndex_strict {ψ : ℕ → ℝ} {δ : ℝ}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasExtremalIndexStrict (fun n : ℕ => InfiniteMovingAverage.process ψ Z n) P
      ((⨆ j, ψ j) ^ α / ∑' j, ψ j ^ α) :=
  ⟨InfiniteMovingAverage.hasExtremalIndex hZ hind hident hZ0 hδ hδα hα1 hL hψ0 hψ hpos,
    (InfiniteMovingAverage.hasSpectralTailProcess hZ hind hident hZ0 hδ hδα hα1 hL hψ0 hψ
      hpos).hasExceedanceLevels_of_nonneg (InfiniteMovingAverage.measurable_process hZ 0)
      (InfiniteMovingAverage.process_nonneg hψ0 hZ0 0)⟩

/-- **Strict form of `AR1.hasExtremalIndex`**: the AR(1) process has the unique extremal index
`1 - φ^α`. -/
theorem AR1.hasExtremalIndex_strict {φ : ℝ} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hα1 : α < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    HasExtremalIndexStrict (fun n : ℕ => AR1.process φ Z n) P (1 - φ ^ α) := by
  have hδ : 0 < α / 2 := by positivity
  exact ⟨AR1.hasExtremalIndex hZ hind hident hZ0 hα hα1 hL hφ0 hφ1,
    (InfiniteMovingAverage.hasSpectralTailProcess (ψ := fun j => φ ^ j) hZ hind hident hZ0 hδ
      (by linarith) hα1 hL (fun j => pow_nonneg hφ0.le j) (AR1.summable_rpow hφ0 hφ1 hδ)
      ⟨0, by simp⟩).hasExceedanceLevels_of_nonneg
      (InfiniteMovingAverage.measurable_process hZ 0)
      (InfiniteMovingAverage.process_nonneg (fun j => pow_nonneg hφ0.le j) hZ0 0)⟩

end Examples

end ExtremeValueTheory
