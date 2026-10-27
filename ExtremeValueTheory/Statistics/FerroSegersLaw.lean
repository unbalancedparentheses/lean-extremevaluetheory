/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ExtremalIndexEstimatorsIntervals

/-!
# The Ferro–Segers law: integrability and the case `θ = 1`

Basic API for `ExtremeValueTheory.ferroSegersLaw θ = (1 - θ) δ₀ + θ Exp(θ)`, the limit law of
the normalized inter-exceedance times of a sequence with extremal index `θ`.

## Main results

* `integrable_pow_ferroSegersLaw`: every moment `x ↦ x^j` is integrable; in particular
  `integrable_id_ferroSegersLaw` and `integrable_sq_ferroSegersLaw`. These are the hypotheses
  under which the strong law of large numbers gives the moment conditions of
  `tendstoInMeasure_intervalsEstimator₁` for iid inter-exceedance times.
* `ferroSegersLaw_one`: with `θ = 1` (no clustering) the law is the standard exponential law.

## References

* C. A. T. Ferro and J. Segers, *Inference for clusters of extreme values*, JRSS B 65 (2003),
  Theorem 1.
-/

open MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-- All moments of the Ferro–Segers law are finite: `x ↦ x^j` is integrable. -/
theorem integrable_pow_ferroSegersLaw {θ : ℝ} (hθ0 : 0 < θ) (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j) (ferroSegersLaw θ) := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  have hmeas : Measurable fun x : ℝ => x / θ := by fun_prop
  have hint : Integrable (fun x : ℝ => x ^ j) ((expMeasure 1).map (· / θ)) := by
    rw [integrable_map_measure (by fun_prop) hmeas.aemeasurable]
    have := (integrable_pow_expMeasure j).div_const (θ ^ j)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [div_pow]
  have hdirac : Integrable (fun x : ℝ => x ^ j) (Measure.dirac 0) := integrable_dirac (by simp)
  rw [ferroSegersLaw]
  exact (hdirac.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hint.smul_measure ENNReal.ofReal_ne_top)

/-- The Ferro–Segers law has a finite mean. -/
theorem integrable_id_ferroSegersLaw {θ : ℝ} (hθ0 : 0 < θ) :
    Integrable (fun x : ℝ => x) (ferroSegersLaw θ) := by
  simpa using integrable_pow_ferroSegersLaw hθ0 1

/-- The Ferro–Segers law has a finite second moment. -/
theorem integrable_sq_ferroSegersLaw {θ : ℝ} (hθ0 : 0 < θ) :
    Integrable (fun x : ℝ => x ^ 2) (ferroSegersLaw θ) :=
  integrable_pow_ferroSegersLaw hθ0 2

/-- **No clustering**: with extremal index `θ = 1` the Ferro–Segers law is the standard
exponential law ([Ferro–Segers 2003, Theorem 1]). -/
@[simp] theorem ferroSegersLaw_one : ferroSegersLaw 1 = expMeasure 1 := by
  simp [ferroSegersLaw]

end ExtremeValueTheory
