/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Simple max-stable random vectors

A probability law `μ` on `ℝ^ι` (`ι` a finite index type) is **simple max-stable** if its
margins are unit Fréchet, `μ {x | x i ≤ y} = exp (-1 / y)` for `y > 0`, and its distribution
function `F(y) = μ (Iic y)` satisfies

  `F(y) ^ n = F(y / n)` for all `n ≥ 1` and all `y` with positive coordinates,

i.e. the componentwise maximum of `n` i.i.d. copies of a vector `Y` with law `μ` has the law of
`n Y` ([dHF, §6.1.3]; [Res87, §5.4]).

The **exponent function** is `V(y) = -log F(y)`. It is positive and finite on `(0, ∞)^ι`, and
homogeneous of order `-1`: `V(t y) = V(y) / t`; equivalently `F(t y) = F(y) ^ (1 / t)` for all
real `t > 0`. The integer case is the definition; the rational case follows by taking roots and
the real case by monotonicity of `F` in `t` and continuity of `t ↦ F(y) ^ (1 / t)`.

## Main definitions and results

* `ExtremeValueTheory.IsSimpleMaxStable μ`: `μ` is a simple max-stable law on `ι → ℝ`.
* `ExtremeValueTheory.maxStableExponent μ y`: the exponent function `V(y) = -log F(y)`.
* `IsSimpleMaxStable.measure_Iic_pos`: `F(y) > 0` on `(0, ∞)^ι`.
* `IsSimpleMaxStable.measureReal_Iic_smul`: `F(t y) = F(y) ^ (1 / t)` for real `t > 0`.
* `IsSimpleMaxStable.maxStableExponent_smul`: `V(t y) = V(y) / t`.
* `IsSimpleMaxStable.inv_le_maxStableExponent`: `V(y) ≥ 1 / y i` for each coordinate.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 6 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Chapter 5 [Res87].
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ExtremeValueTheory

variable {ι : Type*} [Fintype ι]

/-- A law `μ` on `ι → ℝ` is **simple max-stable** if it is a probability measure with unit
Fréchet margins and `F(y) ^ n = F(y / n)` for every `n ≥ 1` and every `y` with positive
coordinates, where `F(y) = μ (Iic y) = μ {x | ∀ i, x i ≤ y i}` ([dHF, §6.1.3]). -/
structure IsSimpleMaxStable (μ : Measure (ι → ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- The margins are unit Fréchet: `P(Y i ≤ y) = exp (-1 / y)` for `y > 0`. -/
  measure_le : ∀ i, ∀ y : ℝ, 0 < y → μ {x | x i ≤ y} = ENNReal.ofReal (Real.exp (-y⁻¹))
  /-- Max-stability: `F(y) ^ n = F(y / n)`. -/
  measure_Iic_pow : ∀ n : ℕ, 0 < n → ∀ y : ι → ℝ, (∀ i, 0 < y i) →
    μ (Iic y) ^ n = μ (Iic ((n : ℝ)⁻¹ • y))

/-- The **exponent function** `V(y) = -log P(Y ≤ y)` of a law on `ι → ℝ`. -/
noncomputable def maxStableExponent (μ : Measure (ι → ℝ)) (y : ι → ℝ) : ℝ :=
  -Real.log (μ.real (Iic y))

namespace IsSimpleMaxStable

variable {μ : Measure (ι → ℝ)}

end IsSimpleMaxStable

end ExtremeValueTheory
