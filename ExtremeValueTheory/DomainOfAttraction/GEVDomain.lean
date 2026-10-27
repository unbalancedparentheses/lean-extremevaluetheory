/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.PeaksOverThreshold.Balkema
import ExtremeValueTheory.DomainOfAttraction.VonMises

/-!
# The unified domain of attraction `MDA(H_ξ)`: API and examples

`CumulativeDistributionFunction.IsInMDAGEV F ξ` (defined with the Pickands–Balkema–de Haan
theorem) is a case split on the sign of `ξ`. This file unfolds it into the three classical domains
and places the textbook examples in it, with the de Haan–Ferreira sign convention
`ξ = 1/α` (Fréchet), `ξ = 0` (Gumbel), `ξ = -1/α` (Weibull).

## Main results

* `isInMDAGEV_iff_of_pos`, `isInMDAGEV_iff_of_neg`, `isInMDAGEV_zero_iff`: the three cases.
* `IsInMDAFrechet.isInMDAGEV`, `IsInMDAWeibull.isInMDAGEV`, `IsInMDAGumbel.isInMDAGEV`.
* `isInMDAGEV_paretoCDF`: Pareto(`α`) is in `MDA(H_{1/α})`.
* `isInMDAGEV_powerCDF`: `1 - (1 - x)^α` (uniform for `α = 1`) is in `MDA(H_{-1/α})`.
* `isInMDAGEV_standardExponentialCDF`: the standard exponential law is in `MDA(H_0)`.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.1.3 [dHF].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events for Insurance and
  Finance*, Springer (1997), Tables 3.4.2–3.4.4 [EKM].
-/

open Real

namespace CumulativeDistributionFunction

variable {F : CumulativeDistributionFunction}

/-- For `ξ > 0`, `MDA(H_ξ)` is the Fréchet domain `MDA(Φ_{1/ξ})`. -/
theorem isInMDAGEV_iff_of_pos {ξ : ℝ} (hξ : 0 < ξ) :
    F.IsInMDAGEV ξ ↔ F.IsInMDAFrechet (one_div_pos.2 hξ) := by
  rw [IsInMDAGEV, dif_pos hξ]

/-- For `ξ < 0`, `MDA(H_ξ)` is the Weibull domain `MDA(Ψ_{-1/ξ})`. -/
theorem isInMDAGEV_iff_of_neg {ξ : ℝ} (hξ : ξ < 0) :
    F.IsInMDAGEV ξ ↔ F.IsInMDAWeibull (div_pos_of_neg_of_neg neg_one_lt_zero hξ) := by
  rw [IsInMDAGEV, dif_neg hξ.not_gt, dif_pos hξ]

/-- `MDA(H_0)` is the Gumbel domain `MDA(Λ)`. -/
theorem isInMDAGEV_zero_iff : F.IsInMDAGEV 0 ↔ F.IsInMDAGumbel := by
  rw [IsInMDAGEV, dif_neg (lt_irrefl 0), dif_neg (lt_irrefl 0)]

/-- The Fréchet domain `MDA(Φ_α)` is `MDA(H_{1/α})`. -/
theorem IsInMDAFrechet.isInMDAGEV {α : ℝ} {hα : 0 < α} (h : F.IsInMDAFrechet hα) :
    F.IsInMDAGEV (1 / α) := by
  rw [isInMDAGEV_iff_of_pos (one_div_pos.2 hα)]
  convert h using 2
  simp

/-- The Weibull domain `MDA(Ψ_α)` is `MDA(H_{-1/α})`. -/
theorem IsInMDAWeibull.isInMDAGEV {α : ℝ} {hα : 0 < α} (h : F.IsInMDAWeibull hα) :
    F.IsInMDAGEV (-1 / α) := by
  rw [isInMDAGEV_iff_of_neg (div_neg_of_neg_of_pos neg_one_lt_zero hα)]
  convert h using 2
  field_simp

/-- The Gumbel domain `MDA(Λ)` is `MDA(H_0)`. -/
theorem IsInMDAGumbel.isInMDAGEV (h : F.IsInMDAGumbel) : F.IsInMDAGEV 0 :=
  isInMDAGEV_zero_iff.2 h

/-- **Pareto(`α`) is in `MDA(H_{1/α})`** ([EKM, Table 3.4.2]). -/
theorem isInMDAGEV_paretoCDF {α : ℝ} (hα : 0 < α) : (paretoCDF hα).IsInMDAGEV (1 / α) :=
  (isInMDAFrechet_paretoCDF hα).isInMDAGEV

/-- **`1 - (1 - x)^α` on `[0, 1]` is in `MDA(H_{-1/α})`**; for `α = 1`, the uniform law is in
`MDA(H_{-1})` ([EKM, Table 3.4.3]). -/
theorem isInMDAGEV_powerCDF {α : ℝ} (hα : 0 < α) : (powerCDF hα).IsInMDAGEV (-1 / α) :=
  (isInMDAWeibull_powerCDF hα).isInMDAGEV

/-- **The standard exponential law is in `MDA(H_0)`** ([EKM, Table 3.4.4]). -/
theorem isInMDAGEV_standardExponentialCDF : standardExponentialCDF.IsInMDAGEV 0 :=
  isInMDAGumbel_standardExponentialCDF.isInMDAGEV

end CumulativeDistributionFunction
