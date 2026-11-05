import ExtremeValueTheory

/-!
# A tail index estimated with Hill

**The problem.** Observations come from a Pareto law with minimum `1` and an unknown tail index, in fact
`α = 2`. We estimate it from the largest `k = ⌊√n⌋` observations of a sample of size `n`, with the Hill
estimator `H`, and report `1 / H` as the estimate of `α`.

**What a practitioner learns.** With this `k`, the estimator is consistent: `H → 1/2` and `1 / H → 2` in
probability. Its error has size `1/√k`: `√k (H - 1/2)` converges in distribution to `N(0, 1/4)`. With
`k = ⌊√n⌋` that is the rate `n^{-1/4}`, not `n^{-1/2}`, because only the top `k` observations are used.

**What the theorem does not say.**

* It says nothing about **choosing `k`**. `⌊√n⌋` is one sequence with `k → ∞` and `k/n → 0`, not a
  recommendation, and no theorem here compares it with another. In practice this is the hard question.
* The sample is **exactly Pareto and iid**. For an exact Pareto law the Hill estimator has no asymptotic
  bias, whereas for a law that is Pareto only in the tail the bias depends on `k` and on second-order
  behaviour. Consistency extends to any regularly varying tail (`tendstoInMeasure_hill_of_hasLaw`), but
  the normal limit stated here does not, without a second-order condition
  (`tendstoInDistribution_hill`).
* It is **asymptotic**: it says nothing about a sample of any given size, or about a Hill plot.
* The normal limit is stated for `H`, not for `1 / H`, and no confidence interval is stated here.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory
open ExtremeValueTheory

namespace Examples.Applications.HillTailIndex

/-- The law of the observations: Pareto with minimum `1` and index `2`. -/
noncomputable abbrev obs : Measure ℝ := paretoMeasure 1 2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

/-- **The checked statement.** For an iid Pareto(1, 2) sample and `k n = ⌊√n⌋`: the Hill estimator tends to
`1/2` in probability, its inverse tends to `2` in probability, and `√k (H - 1/2) ⇒ N(0, 1/4)`. -/
theorem hillTailIndex (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, HasLaw (X i) obs P)
    (hind : iIndepFun X P) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (Nat.sqrt n)) atTop
        (fun _ ↦ 1 / 2) ∧
    TendstoInMeasure P (fun n ω ↦ (hill (fun i : Fin n ↦ X i ω) (Nat.sqrt n))⁻¹) atTop
        (fun _ ↦ 2) ∧
    TendstoInDistribution
        (fun n ω ↦ √(Nat.sqrt n : ℝ) * (hill (fun i : Fin n ↦ X i ω) (Nat.sqrt n) - 2⁻¹))
        atTop id (fun _ ↦ P) (gaussianReal 0 (((2 : ℝ)⁻¹ ^ 2).toNNReal)) := by
  have hRV := isRegularlyVarying_tail_paretoMeasure (t := 1) (r := 2) one_pos two_pos
  refine ⟨tendstoInMeasure_hill_of_hasLaw hX hlaw hind two_pos hRV tendsto_sqrt_atTop
      tendsto_sqrt_div,
    tendstoInMeasure_inv_hill_of_hasLaw hX hlaw hind two_pos hRV tendsto_sqrt_atTop
      tendsto_sqrt_div, ?_⟩
  refine tendstoInDistribution_hill_pareto hX hind (fun i ↦ (hlaw i).identDistrib (hlaw 0))
    two_pos (fun x hx ↦ ?_) tendsto_sqrt_atTop ?_ HasLaw.id
  · have h := tail_paretoMeasure (t := 1) (r := 2) one_pos two_pos hx
    rw [Real.one_rpow, one_mul] at h
    rw [(hlaw 0).measure_eq (p := (x < ·)) measurableSet_Ioi]
    exact h
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact Nat.sqrt_lt_self hn

/-- The hypotheses of `hillTailIndex` can be met: such a sample exists. -/
theorem exists_sample :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) obs P) ∧
        iIndepFun X P := by
  have := isProbabilityMeasure_paretoMeasure (t := 1) (r := 2) one_pos two_pos
  obtain ⟨Ω, _, P, X, hXm, hlaw, hind, hP⟩ := exists_iid ℕ obs
  exact ⟨Ω, _, P, X, hP, hXm, hlaw, hind⟩

end Examples.Applications.HillTailIndex
