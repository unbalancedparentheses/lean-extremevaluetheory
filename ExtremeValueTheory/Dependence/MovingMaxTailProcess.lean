/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Examples
import ExtremeValueTheory.Dependence.TailProcess

/-!
# The tail process of the moving maximum

PLACEHOLDER
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### The spectral tail process -/

/-- The fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin :=
  ⟨by simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- The location `0` (for `b = true`) or `1` (for `b = false`) of the large innovation. -/
def movingMaxPeak (b : Bool) : ℤ := if b then 0 else 1

/-- The spectral tail process of the moving maximum `X_t = max(Z_t, Z_{t+1})`: with `b` a fair
coin, `Θ_t = 1` if `t` or `t + 1` is the peak location (`0` if `b`, `1` otherwise), and `Θ_t = 0`
otherwise. Thus `Θ = (…, 0, 1, 1, 0, …)` at times `(-1, 0)` or `(0, 1)` with probability `1/2`
each. -/
noncomputable def movingMaxSpectral (t : ℤ) (b : Bool) : ℝ :=
  if t = movingMaxPeak b ∨ t + 1 = movingMaxPeak b then 1 else 0

theorem measurable_movingMaxSpectral (t : ℤ) : Measurable (movingMaxSpectral t) :=
  measurable_from_top

/-- **The candidate extremal index of the moving maximum is `1/2`**: for `b = true` (peak at `0`)
the process vanishes at positive times, so the integrand is `1`; for `b = false` (peak at `1`),
`Θ_1 = 1` and the integrand is `0`. -/
theorem candidateExtremalIndex_movingMax {α : ℝ} (hα : 0 < α) :
    candidateExtremalIndex fairCoin movingMaxSpectral α = 2⁻¹ := by
  have hT0 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral k true|) = 1 := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0
      (by simp [movingMaxSpectral, movingMaxPeak]))
    unfold movingMaxSpectral; split_ifs <;> simp
  have hT1 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral (k + 1) true|) = 0 := by
    refine ENNReal.iSup_eq_zero.2 fun k => ?_
    simp only [movingMaxSpectral, movingMaxPeak, ↓reduceIte]
    split_ifs with h
    · omega
    · simp
  have hF0 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral k false|) = 1 := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0
      (by simp [movingMaxSpectral, movingMaxPeak]))
    unfold movingMaxSpectral; split_ifs <;> simp
  have hF1 : (⨆ k : ℕ, ENNReal.ofReal |movingMaxSpectral (k + 1) false|) = 1 := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0 (by simp [movingMaxSpectral,
      movingMaxPeak]))
    unfold movingMaxSpectral; split_ifs <;> simp
  rw [candidateExtremalIndex, fairCoin, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac, lintegral_dirac, hT0, hT1, hF0, hF1, ENNReal.zero_rpow_of_pos hα]
  simp

end ExtremeValueTheory
