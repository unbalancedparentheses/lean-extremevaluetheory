/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.MeasureTheory.Measure.Vague
import ExtremeValueTheory.ForMathlib.Probability.PoissonLimit
import Mathlib.Probability.Independence.InfinitePi

/-!
# Convergence in law of point processes towards Poisson random measures

We define convergence in law of random measures through their finite-dimensional count
distributions (`ProbabilityTheory.TendstoInLawVaguely`), and prove that binomial point processes
`∑_{k < n} δ_{Z k}`, with `Z` i.i.d. of law `μ n` and `n • μ n → ν` vaguely, converge in this sense
to the Poisson random measure with intensity `ν` (Resnick, *Extreme values, regular variation and
point processes*, Proposition 3.21).

## Main definitions

* `ProbabilityTheory.TendstoInLawVaguely N P l N' P' ν`: for all pairwise disjoint relatively
  compact measurable sets `B 0, …, B (k-1)` with `ν (∂ B j) = 0`, the joint laws of the counts
  `(N i (B j))_j` converge to that of `(N' (B j))_j` (pointwise convergence of the probability
  mass functions on `ℕ ^ k`).

## Main statements

* `ProbabilityTheory.IsPoissonRandomMeasure.measureReal_forall_apply_eq`: the joint probability
  mass function of the counts of a Poisson random measure on disjoint sets.
* `ProbabilityTheory.tendstoInLawVaguely_sumDiracRange`: binomial point processes converge in law
  to Poisson random measures.

## Implementation notes

The definition of `TendstoInLawVaguely` only involves disjoint sets. For a Poisson limit this is
no loss of generality: the counts on finitely many relatively compact `ν`-continuity sets are
sums of counts on the atoms of the generated Boolean algebra, which are again disjoint relatively
compact `ν`-continuity sets. Since the counts take values in `ℕ ^ k`, pointwise convergence of the
probability mass functions is equivalent to weak convergence of the laws.

## References

* [O. Kallenberg, *Random Measures, Theory and Applications*][kallenberg2017]
* [S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*][resnick1987]
-/

open MeasureTheory Filter Finset Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- The point probabilities of the counts of a Poisson random measure on disjoint sets of finite
intensity: `P(N (B j) = m j ∀ j) = ∏ j, exp (-ν (B j)) ν (B j) ^ m j / m j !`. -/
lemma IsPoissonRandomMeasure.measureReal_forall_apply_eq {N : Ω → Measure E} {ν : Measure E}
    {P : Measure Ω} (hN : IsPoissonRandomMeasure N ν P) {k : ℕ} {B : Fin k → Set E}
    (hB : ∀ j, MeasurableSet (B j)) (hνB : ∀ j, ν (B j) ≠ ∞)
    (hd : Pairwise (Function.onFun Disjoint B)) (m : Fin k → ℕ) :
    P.real {ω | ∀ j, N ω (B j) = m j} =
      ∏ j, Real.exp (-(ν (B j)).toReal) * (ν (B j)).toReal ^ m j / (m j).factorial := by
  have hm : Measurable fun ω (j : Fin k) ↦ N ω (B j) :=
    Measurable.of_eval fun j ↦ hN.measurable_apply (hB j)
  have hset : {ω | ∀ j, N ω (B j) = m j} =
      (fun ω (j : Fin k) ↦ N ω (B j)) ⁻¹' Set.univ.pi fun j ↦ {(m j : ℝ≥0∞)} := by
    ext ω
    simp
  rw [hset, measureReal_def, ← Measure.map_apply hm
    (MeasurableSet.univ_pi fun j ↦ measurableSet_singleton _), hN.map_eq_pi B hB hνB hd,
    Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' {(m j : ℝ≥0∞)} = {m j} := by
    ext x
    simp
  rw [this, ← measureReal_def, poissonMeasure_real_singleton, ENNReal.coe_toNNReal_eq_toReal]

/-- The mass that `∑_{k < n} δ_{z k}` gives to a measurable set `A` is the number of indices
`k < n` with `z k ∈ A`. -/
lemma sumDiracRange_apply_eq_card (n : ℕ) (z : ℕ → E) {A : Set E} [DecidablePred (· ∈ A)]
    (hA : MeasurableSet A) :
    sumDiracRange n z A = #{k ∈ range n | z k ∈ A} := by
  rw [sumDiracRange_apply _ _ hA, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : z k ∈ A <;> simp [hk]

variable [TopologicalSpace E]

/-- Random measures `N i` (under `P i`) *converge in law* to `N'` (under `P'`) relative to the
measure `ν`, in the sense of finite-dimensional distributions of counts: for all pairwise disjoint
relatively compact measurable sets `B 0, …, B (k-1)` with `ν (∂ B j) = 0`, the joint laws of the
counts `(N i (B 0), …, N i (B (k-1)))` converge to that of `(N' (B 0), …, N' (B (k-1)))`, as laws
on `ℕ ^ k` (that is, pointwise convergence of the probability mass functions).

When `N'` is a Poisson random measure with intensity `ν`, the sets `B` with `ν (∂ B) = 0` are
exactly the sets whose boundary carries almost surely no point of `N'`. -/
def TendstoInLawVaguely {ι Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (N : ι → Ω → Measure E)
    (P : ι → Measure Ω) (l : Filter ι) (N' : Ω' → Measure E) (P' : Measure Ω')
    (ν : Measure E) : Prop :=
  ∀ ⦃k : ℕ⦄ (B : Fin k → Set E), (∀ j, MeasurableSet (B j)) → (∀ j, IsCompact (closure (B j))) →
    (∀ j, ν (frontier (B j)) = 0) → Pairwise (Function.onFun Disjoint B) → ∀ m : Fin k → ℕ,
    Tendsto (fun i ↦ (P i).real {ω | ∀ j, N i ω (B j) = m j}) l
      (𝓝 (P'.real {ω | ∀ j, N' ω (B j) = m j}))

open scoped Classical in
/-- **Poisson approximation of binomial point processes.** Let `μ n` be probability measures with
`n • μ n → ν` vaguely, `ν` regular. Then the binomial point processes `∑_{k < n} δ_{Z k}` with
`Z` i.i.d. of law `μ n` converge in law to any Poisson random measure with intensity `ν`
(Resnick, *Extreme values, regular variation and point processes*, Proposition 3.21). -/
theorem tendstoInLawVaguely_sumDiracRange [T2Space E] [LocallyCompactSpace E] [RegularSpace E]
    [OpensMeasurableSpace E] {μ : ℕ → Measure E} [∀ n, IsProbabilityMeasure (μ n)]
    {ν : Measure E} [ν.Regular]
    (h : Measure.TendstoVaguely (fun n : ℕ ↦ (n : ℝ≥0∞) • μ n) atTop ν)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {N' : Ω' → Measure E} {P' : Measure Ω'}
    (hN' : IsPoissonRandomMeasure N' ν P') :
    TendstoInLawVaguely (fun n z ↦ sumDiracRange n z)
      (fun n ↦ Measure.infinitePi fun _ : ℕ ↦ μ n) atTop N' P' ν := by
  intro k B hB hBc hBf hd m
  have hνB (j : Fin k) : ν (B j) ≠ ∞ :=
    (measure_mono subset_closure).trans_lt (hBc j).measure_lt_top |>.ne
  have : ∀ n : ℕ, IsFiniteMeasureOnCompacts ((n : ℝ≥0∞) • μ n) := fun n ↦
    ⟨fun K _ ↦ by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩
  -- `n μ n (B j) → ν (B j)`
  have hconv (j : Fin k) : Tendsto (fun n : ℕ ↦ (n : ℝ) * (μ n).real (B j)) atTop
      (𝓝 (ν (B j)).toReal) := by
    have := (ENNReal.tendsto_toReal (hνB j)).comp
      (h.tendsto_measure_of_null_frontier (hBc j) (hBf j))
    refine this.congr fun n ↦ ?_
    simp [Measure.real]
  have hpre (n i : ℕ) (j : Fin k) : (Measure.infinitePi fun _ : ℕ ↦ μ n).real
      ((fun z : ℕ → E ↦ z i) ⁻¹' B j) = (μ n).real (B j) := by
    rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply i) (hB j),
      Measure.infinitePi_map_eval, measureReal_def]
  have hcore := tendsto_measureReal_card_filter_range_eq (P := fun n ↦ Measure.infinitePi
    fun _ : ℕ ↦ μ n) (Z := fun _ i z ↦ z i) (fun _ i ↦ measurable_pi_apply i)
    (fun n ↦ iIndepFun_infinitePi (X := fun _ ↦ id) fun _ ↦ measurable_id) hB hd
    (r := fun j ↦ (ν (B j)).toNNReal) (fun j ↦ ?_) (fun ε hε ↦ ?_) m
  · rw [hN'.measureReal_forall_apply_eq hB hνB hd]
    convert hcore using 3 with n
    · ext z
      simp [sumDiracRange_apply_eq_card _ _ (hB _)]
    · simp [ENNReal.coe_toNNReal_eq_toReal]
  · simp_rw [hpre, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simpa [ENNReal.coe_toNNReal_eq_toReal] using hconv j
  · have hzero (j : Fin k) : Tendsto (fun n : ℕ ↦ (μ n).real (B j)) atTop (𝓝 0) := by
      have := (hconv j).div_atTop tendsto_natCast_atTop_atTop
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    have hev : ∀ᶠ n in atTop, ∀ j, (μ n).real (B j) ≤ ε := by
      rw [eventually_all]
      exact fun j ↦ (hzero j).eventually (eventually_le_nhds hε)
    filter_upwards [hev] with n hn i _ j
    rw [hpre]
    exact hn j

end ProbabilityTheory
