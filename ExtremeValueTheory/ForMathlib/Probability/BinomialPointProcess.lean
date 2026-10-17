/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.MeasureTheory.Measure.Vague
public import ExtremeValueTheory.ForMathlib.Probability.PoissonRandomMeasure
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Poisson approximation of binomial point processes

Let `Z 0, Z 1, …` be i.i.d. with law `μ`. The *binomial point process* with `n` points is the
random counting measure `∑_{k < n} δ_{Z k}`. We compute its Laplace functional and prove that if
`n • μₙ → ν` vaguely, then the Laplace functionals of the binomial point processes with `n`
points and law `μₙ` converge to `exp (-∫ (1 - exp (-f)) dν)`, the Laplace functional of a Poisson
random measure with intensity `ν`. This is the Laplace functional form of the Poisson
approximation of point processes (Resnick, *Extreme values, regular variation and point
processes*, Proposition 3.21).

## Main statements

* `ProbabilityTheory.integral_exp_neg_integral_sumDiracRange_infinitePi`: the Laplace functional
  of a binomial point process.
* `ProbabilityTheory.tendsto_laplace_sumDiracRange_of_tendstoVaguely`: convergence of the Laplace
  functionals of binomial point processes towards the Poisson Laplace functional.
* `ProbabilityTheory.tendsto_laplace_sumDiracRange_poissonSampleMeasure`: the same limit, written
  as the Laplace functional of the Poisson random measure `∑_{k < K} δ_{Z k}` when the intensity
  is finite.

## References

* [S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*][resnick1987]
-/

public section

open MeasureTheory Filter Finset Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- **Laplace functional of a binomial point process.** If `Z` is an i.i.d. sequence with law
`μ`, then `E exp (-∫ f d(∑_{k < n} δ_{Z k})) = (∫ exp (-f) dμ) ^ n`. -/
lemma integral_exp_neg_integral_sumDiracRange_infinitePi (μ : Measure E) [IsProbabilityMeasure μ]
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) :
    ∫ z, Real.exp (-∫ x, f x ∂(sumDiracRange n z)) ∂(Measure.infinitePi fun _ : ℕ ↦ μ) =
      (∫ x, Real.exp (-f x) ∂μ) ^ n := by
  simp_rw [integral_sumDiracRange hf, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact integral_prod_range_infinitePi (Real.measurable_exp.comp hf.neg) n

variable [TopologicalSpace E] [OpensMeasurableSpace E]

/-- **Poisson approximation of binomial point processes, Laplace functional form.** Let `μ n` be
probability measures such that `n • μ n → ν` vaguely. Then for every continuous compactly
supported `f ≥ 0`, the Laplace functional of the binomial point process with `n` i.i.d. points of
law `μ n` converges to `exp (-∫ (1 - exp (-f)) dν)`. -/
theorem tendsto_laplace_sumDiracRange_of_tendstoVaguely {μ : ℕ → Measure E}
    [∀ n, IsProbabilityMeasure (μ n)] {ν : Measure E}
    (h : Measure.TendstoVaguely (fun n : ℕ ↦ (n : ℝ≥0∞) • μ n) atTop ν) {f : E → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : 0 ≤ f) :
    Tendsto (fun n ↦ ∫ z, Real.exp (-∫ x, f x ∂(sumDiracRange n z))
        ∂(Measure.infinitePi fun _ : ℕ ↦ μ n)) atTop
      (𝓝 (Real.exp (-∫ x, (1 - Real.exp (-f x)) ∂ν))) := by
  have hfm : Measurable f := hf.measurable
  simp_rw [integral_exp_neg_integral_sumDiracRange_infinitePi _ hfm]
  -- The function `1 - exp (-f)` is continuous and compactly supported.
  set g : E → ℝ := fun x ↦ 1 - Real.exp (-f x) with hg_def
  have hgc : Continuous g := continuous_const.sub (Real.continuous_exp.comp hf.neg)
  have hgs : HasCompactSupport g := hfs.mono fun x hx ↦ by
    simp only [Function.mem_support, hg_def] at hx ⊢
    intro hfx
    simp [hfx] at hx
  have hint (n : ℕ) : Integrable (fun x ↦ Real.exp (-f x)) (μ n) := by
    refine Integrable.of_bound (Real.measurable_exp.comp hfm.neg).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact hf0 x
  have heq (n : ℕ) : ∫ x, Real.exp (-f x) ∂(μ n) = 1 + -(∫ x, g x ∂(μ n)) := by
    rw [hg_def, integral_sub (integrable_const _) (hint n)]
    simp
  simp_rw [heq]
  refine Real.tendsto_one_add_pow_exp_of_tendsto ?_
  have := (h g hgc hgs).neg
  refine this.congr fun n ↦ ?_
  rw [integral_smul_measure]
  simp

/-- **Poisson approximation of binomial point processes.** If `n • μ n → c • μ₀` vaguely, then
the Laplace functionals of the binomial point processes with `n` i.i.d. points of law `μ n`
converge to the Laplace functional of the Poisson random measure `∑_{k < K} δ_{Z k}` with
intensity `c • μ₀` (see `ProbabilityTheory.isPoissonRandomMeasure_sumDiracRange`). -/
theorem tendsto_laplace_sumDiracRange_poissonSampleMeasure {μ : ℕ → Measure E}
    [∀ n, IsProbabilityMeasure (μ n)] {c : ℝ≥0} {μ₀ : Measure E} [IsProbabilityMeasure μ₀]
    (h : Measure.TendstoVaguely (fun n : ℕ ↦ (n : ℝ≥0∞) • μ n) atTop (c • μ₀)) {f : E → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : 0 ≤ f) :
    Tendsto (fun n ↦ ∫ z, Real.exp (-∫ x, f x ∂(sumDiracRange n z))
        ∂(Measure.infinitePi fun _ : ℕ ↦ μ n)) atTop
      (𝓝 (∫ ω, Real.exp (-∫ x, f x ∂(sumDiracRange ω.1 ω.2)) ∂(poissonSampleMeasure c μ₀))) := by
  rw [integral_exp_neg_integral_sumDiracRange hf.measurable hf0]
  exact tendsto_laplace_sumDiracRange_of_tendstoVaguely h hf hfs hf0

end ProbabilityTheory
