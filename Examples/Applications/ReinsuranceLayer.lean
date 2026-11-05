import ExtremeValueTheory

/-!
# A reinsurance layer

**The problem.** Individual losses, in millions, follow a Pareto law with minimum `1` and tail index
`α = 2`, so `P(X > x) = x⁻²` for `x ≥ 1`. A reinsurer writes the layer `2 xs 2`: on a loss `x` it pays
`min ((x - 2)⁺, 2)`, the part of the loss between 2 and 4. These numbers are illustrative.

**What a practitioner learns.** A loss above 100 has probability `1/10000`. The layer is reached with
probability `1/4` and exhausted with probability `1/16`. Its expected payout per loss is the integral
of the tail over the layer, which here is exactly `1/4`. The general formula is
`integral_layerPayout`, for any law, and it is exact, not asymptotic.

**What the theorem does not say.**

* It assumes the loss is **exactly Pareto with known parameters**. There is no estimation, so no
  statement about parameter uncertainty, and none about a law that is Pareto only in the tail.
* It is about **one loss**. The number of losses in a year, and their dependence, are not modelled. The
  library has random-sum results (`IsSubexponential.tendsto_tail_compound_div`), but they are not
  applied here.
* The expected payout is a **net premium** at best: no loading, expenses, reinstatements, aggregate
  limits or discounting.
* It says nothing about the choice of the Pareto model or of a threshold above which it applies.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory
open ExtremeValueTheory

namespace Examples.Applications.ReinsuranceLayer

/-- The loss law: Pareto with minimum `1` and index `2`. -/
noncomputable abbrev loss : Measure ℝ := paretoMeasure 1 2

/-- The tail of the loss: `P(X > x) = x⁻²` for `x ≥ 1`. -/
theorem tail_loss {x : ℝ} (hx : 1 ≤ x) : tail loss x = (x ^ (2 : ℝ))⁻¹ := by
  rw [loss, tail_paretoMeasure one_pos two_pos hx, Real.one_rpow, one_mul,
    Real.rpow_neg (by linarith)]

/-- **The checked statement.** For a Pareto(1, 2) loss: `P(X > 100) = 1/10000`, the layer `2 xs 2` is
reached with probability `1/4` and exhausted with probability `1/16`, and its expected payout is
`1/4`. -/
theorem reinsuranceLayer :
    tail loss 100 = 1 / 10000 ∧
    tail loss 2 = 1 / 4 ∧
    tail loss 4 = 1 / 16 ∧
    ∫ x, layerPayout 2 2 x ∂loss = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tail_loss (by norm_num), Real.rpow_two]; norm_num
  · rw [tail_loss (by norm_num), Real.rpow_two]; norm_num
  · rw [tail_loss (by norm_num), Real.rpow_two]; norm_num
  · rw [loss, integral_layerPayout_paretoMeasure one_pos two_pos (by norm_num) (by norm_num)
      (by norm_num), Real.one_rpow, one_mul, show (1 - 2 : ℝ) = -1 by norm_num,
      Real.rpow_neg_one, Real.rpow_neg_one]
    norm_num

/-- The exact statement behind the numbers, for any law: the expected payout of a layer is the integral
of the tail over the layer. -/
example (μ : Measure ℝ) [IsFiniteMeasure μ] (d : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    ∫ x, layerPayout d l x ∂μ = ∫ t in d..(d + l), μ.real (Ioi t) :=
  integral_layerPayout μ d hl

end Examples.Applications.ReinsuranceLayer
