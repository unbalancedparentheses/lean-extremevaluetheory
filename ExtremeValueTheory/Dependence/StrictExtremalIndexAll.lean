/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.StrictExtremalIndex
import ExtremeValueTheory.Dependence.MarkovTailChain
import ExtremeValueTheory.Dependence.EchoProcess

/-!
# Strict extremal indices: all `α > 0`, ARMAX and the echo process

Strict versions (`HasExtremalIndexStrict`, so `θ` is unique by `HasExtremalIndexStrict.unique`)
of further extremal-index theorems, complementing `Dependence/StrictExtremalIndex.lean`. In each
case the marginal tail is regularly varying, so exceedance levels exist for every `τ > 0`
(`hasExceedanceLevels_of_isRegularlyVarying`).

## Main results

* `InfiniteMovingAverage.hasExtremalIndex_of_summable_rpow_strict`: infinite moving averages, all
  `α > 0`.
* `AR1.hasExtremalIndex_of_pos_strict`: the AR(1) process, all `α > 0`.
* `ARMAX.hasExtremalIndex_candidate_strict`: `θ = ϑ` for ARMAX, in the strict sense.
* `logEchoProcess_hasExtremalIndex_strict`: the logarithmic echo process has the unique
  extremal index `1/2` (while `ϑ = 1`, `logEchoProcess_theta_lt_vartheta`);
  `logEchoProcess_not_hasExtremalIndex_one`: in particular `1` is not an extremal index, so the
  gap `θ < ϑ` is not an artifact of a vacuous definition.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace ExtremeValueTheory

section Linear

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℤ → Ω → ℝ} {α : ℝ}

/-- **Strict form of `InfiniteMovingAverage.hasExtremalIndex_of_summable_rpow`** (all `α > 0`). -/
theorem InfiniteMovingAverage.hasExtremalIndex_of_summable_rpow_strict {ψ : ℕ → ℝ} {δ : ℝ}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasExtremalIndexStrict (fun n : ℕ => InfiniteMovingAverage.process ψ Z n) P
      ((⨆ j, ψ j) ^ α / ∑' j, ψ j ^ α) :=
  ⟨InfiniteMovingAverage.hasExtremalIndex_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ hpos,
    (InfiniteMovingAverage.hasSpectralTailProcess_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0
      hψ hpos).hasExceedanceLevels_of_nonneg (InfiniteMovingAverage.measurable_process hZ 0)
      (InfiniteMovingAverage.process_nonneg hψ0 hZ0 0)⟩

/-- **Strict form of `AR1.hasExtremalIndex_of_pos`**: for all `α > 0`, the AR(1) process has
the unique extremal index `1 - φ^α`. -/
theorem AR1.hasExtremalIndex_of_pos_strict {φ : ℝ} (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    HasExtremalIndexStrict (fun n : ℕ => AR1.process φ Z n) P (1 - φ ^ α) :=
  ⟨AR1.hasExtremalIndex_of_pos hZ hind hident hZ0 hα hL hφ0 hφ1,
    (AR1.hasSpectralTailProcess_of_pos hZ hind hident hZ0 hα hL hφ0
      hφ1).hasExceedanceLevels_of_nonneg (InfiniteMovingAverage.measurable_process hZ 0)
      (InfiniteMovingAverage.process_nonneg (fun j => pow_nonneg hφ0.le j) hZ0 0)⟩

end Linear

section ARMAX

variable {φ α : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X₀ : Ω → ℝ} {V : ℕ → Ω → ℝ}

/-- **Strict form of `ARMAX.hasExtremalIndex_candidate`**: the unique extremal index of the
stationary ARMAX chain is the candidate extremal index `ϑ = 1 - φ^α` of its tail chain. -/
theorem ARMAX.hasExtremalIndex_candidate_strict (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα : 0 < α)
    (hX₀ : Measurable X₀) (hV : ∀ n, Measurable (V n))
    (hind : IndepFun X₀ (fun ω n => V n ω) P) (hiid : iIndepFun V P)
    (hlaw : ∀ n, P.map (V n) = paretoMeasure 1 α)
    (hinv : ((P.map X₀).prod (paretoMeasure 1 α)).map (Function.uncurry (ARMAX.step φ)) =
      P.map X₀)
    (Q : Measure (ℕ → ℝ)) [IsProbabilityMeasure Q] :
    HasExtremalIndexStrict (RandomIteration.chain (ARMAX.step φ) X₀ V) P
      (candidateExtremalIndex Q (RandomIteration.spectralWalk fun _ : ℝ => φ) α).toReal := by
  rw [ARMAX.candidateExtremalIndex_tailChain hφ0 hφ1 hα Q, ENNReal.toReal_ofReal
    (by linarith [Real.rpow_lt_one hφ0.le hφ1 hα])]
  exact ARMAX.hasExtremalIndexStrict hφ0 hφ1 hα hX₀ hV hind hiid hlaw hinv

end ARMAX

section Echo

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- **Strict form of the extremal-index part of `logEchoProcess_theta_lt_vartheta`**: the
logarithmic echo process has the unique extremal index `θ = 1/2` (while `ϑ = 1`). -/
theorem logEchoProcess_hasExtremalIndex_strict (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) :
    HasExtremalIndexStrict (fun k : ℕ => echoProcess logLag Z k) P (1 / 2) := by
  have hrv := isRegularlyVarying_echoProcess (P := P) hα hZ hind hlaw hpos measurable_logLag
    one_le_logLag
  simp only [abs_of_nonneg (echoProcess_nonneg hpos _ _)] at hrv
  exact (logEchoProcess_theta_lt_vartheta hα hZ hind hlaw hpos).2.2.2.strict_of_isRegularlyVarying
    (measurable_echoProcess hZ measurable_logLag _) hrv

/-- **`1 = ϑ` is not an extremal index of the logarithmic echo process**: by uniqueness of the
strict extremal index, the gap `θ = 1/2 < 1 = ϑ` is genuine. -/
theorem logEchoProcess_not_hasExtremalIndex_one (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) :
    ¬ HasExtremalIndex (fun k : ℕ => echoProcess logLag Z k) P 1 := by
  intro h1
  have s := logEchoProcess_hasExtremalIndex_strict hα hZ hind hlaw hpos
  have := (HasExtremalIndexStrict.mk h1 s.2).unique s
  norm_num at this

end Echo

end ExtremeValueTheory

/-! ### Deprecated names -/

namespace ExtremeValueTheory

@[deprecated (since := "2026-10-23")] alias InfiniteMovingAverage.hasExtremalIndex_of_lt_one_strict := InfiniteMovingAverage.hasExtremalIndex_of_summable_rpow_strict

end ExtremeValueTheory
