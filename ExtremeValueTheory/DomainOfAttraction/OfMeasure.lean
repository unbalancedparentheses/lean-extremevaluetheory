/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.CDFBridge
import ExtremeValueTheory.DomainOfAttraction.Weibull
import ExtremeValueTheory.DomainOfAttraction.GumbelNecessity

/-!
# Domains of attraction of laws and of random variables

The domains of attraction `IsInMDAFrechet`, `IsInMDAWeibull`, `IsInMDAGumbel` are predicates on a
`CumulativeDistributionFunction`. Through the bridge `CumulativeDistributionFunction.ofMeasure`
(`ExtremeValueTheory/CDFBridge.lean`) Gnedenko's characterizations read directly in terms of the
tail `x ↦ μ (x, ∞)` of a probability measure `μ` on `ℝ`, or `x ↦ P(X > x)` of a random variable.

## Main statements

* `isInMDAFrechet_ofMeasure_iff`, `isInMDAFrechet_ofMeasure_map_iff`: `μ` (resp. the law of `X`)
  is in the Fréchet domain iff its tail is regularly varying with index `-α`.
* `isInMDAWeibull_ofMeasure_iff`: the Weibull domain in terms of the right endpoint and the tail.
* `isInMDAGumbel_ofMeasure_iff_atTop`: the Gumbel domain, for an unbounded support, in terms of
  the tail ratio `μ (t + x f(t), ∞) / μ (t, ∞)`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology ExtremeValueTheory

namespace CumulativeDistributionFunction

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- **Gnedenko's theorem (Fréchet) for laws**: `μ` is in the Fréchet domain of attraction iff its
tail `x ↦ μ (x, ∞)` is regularly varying with index `-α`. -/
theorem isInMDAFrechet_ofMeasure_iff (hα : 0 < α) :
    (ofMeasure μ).IsInMDAFrechet hα ↔ IsRegularlyVarying (fun x ↦ μ.real (Ioi x)) (-α) := by
  rw [isInMDAFrechet_iff, isRegularlyVarying_one_sub_ofMeasure_iff]

/-- **Gnedenko's theorem (Fréchet) in law form**: `F` is in the Fréchet domain of attraction iff
the tail of its law is regularly varying with index `-α`. -/
theorem isInMDAFrechet_iff_measure (F : CumulativeDistributionFunction) (hα : 0 < α) :
    F.IsInMDAFrechet hα ↔ IsRegularlyVarying (fun x ↦ F.measure.real (Ioi x)) (-α) := by
  rw [isInMDAFrechet_iff, isRegularlyVarying_one_sub_iff]

/-- **Gnedenko's theorem (Fréchet) for random variables**: the law of `X` is in the Fréchet domain
of attraction iff `x ↦ P(X > x)` is regularly varying with index `-α`. -/
theorem isInMDAFrechet_ofMeasure_map_iff {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) (hα : 0 < α) :
    (ofMeasure (P.map X)).IsInMDAFrechet hα ↔
      IsRegularlyVarying (fun x ↦ P.real {ω | x < X ω}) (-α) := by
  rw [isInMDAFrechet_iff]
  simp only [one_sub_ofMeasure_map_apply hX]

/-- **Gnedenko's theorem (Weibull) for laws**: `μ` is in the Weibull domain of attraction iff it
has a finite right endpoint `x_F` (`μ (x_F, ∞) = 0` and `μ (x, ∞) > 0` for `x < x_F`) and
`t ↦ μ (x_F - t⁻¹, ∞)` is regularly varying with index `-α`. -/
theorem isInMDAWeibull_ofMeasure_iff (hα : 0 < α) :
    (ofMeasure μ).IsInMDAWeibull hα ↔ ∃ xF : ℝ, μ.real (Ioi xF) = 0 ∧
      (∀ x < xF, 0 < μ.real (Ioi x)) ∧
      IsRegularlyVarying (fun t ↦ μ.real (Ioi (xF - t⁻¹))) (-α) := by
  rw [isInMDAWeibull_iff]
  simp only [← one_sub_ofMeasure_apply, sub_eq_zero, sub_pos]
  exact exists_congr fun _ ↦ and_congr eq_comm Iff.rfl

/-- **The Gumbel domain for laws with unbounded support**, in terms of the tail of the law:
`μ` is in the Gumbel domain of attraction iff, for some auxiliary `f > 0`,
`μ (t + x f(t), ∞) / μ (t, ∞) → e^{-x}` as `t → ∞`. -/
theorem isInMDAGumbel_ofMeasure_iff_atTop (hμ : ∀ x, 0 < μ.real (Ioi x)) :
    (ofMeasure μ).IsInMDAGumbel ↔ ∃ f : ℝ → ℝ, (∀ᶠ t in atTop, 0 < f t) ∧
      ∀ x, Tendsto (fun t ↦ μ.real (Ioi (t + x * f t)) / μ.real (Ioi t)) atTop
        (𝓝 (Real.exp (-x))) := by
  rw [isInMDAGumbel_iff_atTop _ fun x ↦ by
    simpa [← one_sub_ofMeasure_apply, sub_pos] using hμ x]
  simp only [one_sub_ofMeasure_apply]

end CumulativeDistributionFunction
