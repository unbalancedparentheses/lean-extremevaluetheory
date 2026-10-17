/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Tightness of sequences converging in distribution

A sequence of real random variables which converges in distribution is tight (bounded in
probability): for every `ε > 0` there is `M` with `P(M ≤ |X_n|) ≤ ε` eventually. This follows
from the portmanteau theorem applied to the closed sets `{x | M ≤ |x|}`.

## Main results

* `MeasureTheory.TendstoInDistribution.exists_measure_le_abs_le`: tightness of a sequence of
  real random variables converging in distribution.
-/

open Filter Topology Set

namespace MeasureTheory

variable {ι Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ} {l : Filter ι}

/-- **Tightness of a sequence converging in distribution**: if `X_i ⇒ Z` (real valued), then for
every `ε > 0` there is `M` with `μ_i {M ≤ |X_i|} ≤ ε` eventually. -/
theorem TendstoInDistribution.exists_measure_le_abs_le (h : TendstoInDistribution X l Z μ μ')
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ᶠ i in l, μ i {ω | M ≤ |X i ω|} ≤ ε := by
  set ν : Measure ℝ := μ'.map Z with hν
  -- the closed sets `{M ≤ |x|}` decrease to `∅`, so their `ν`-measure tends to `0`
  have hlim : Tendsto (fun M : ℕ => ν {x : ℝ | (M : ℝ) ≤ |x|}) atTop (𝓝 0) := by
    have h0 : ν (⋂ M : ℕ, {x : ℝ | (M : ℝ) ≤ |x|}) = 0 := by
      have : (⋂ M : ℕ, {x : ℝ | (M : ℝ) ≤ |x|}) = ∅ := by
        ext x
        simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
          not_le]
        obtain ⟨M, hM⟩ := exists_nat_gt |x|
        exact ⟨M, hM⟩
      rw [this, measure_empty]
    rw [← h0]
    refine tendsto_measure_iInter_atTop (fun M => ?_) (fun a b hab x hx => ?_)
      ⟨0, measure_ne_top _ _⟩
    · exact (measurableSet_le measurable_const continuous_abs.measurable).nullMeasurableSet
    · simp only [mem_ofPred_eq] at hx ⊢
      exact le_trans (by exact_mod_cast hab) hx
  obtain ⟨M, hM⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨M, ?_⟩
  have hclosed : IsClosed {x : ℝ | (M : ℝ) ≤ |x|} := isClosed_le continuous_const continuous_abs
  have hls := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hclosed
  have hlt : (l.limsup fun i => (μ i).map (X i) {x : ℝ | (M : ℝ) ≤ |x|}) < ε :=
    lt_of_le_of_lt hls hM
  filter_upwards [eventually_lt_of_limsup_lt hlt] with i hi
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable i)
    (measurableSet_le measurable_const continuous_abs.measurable)] at hi
  exact hi.le

end MeasureTheory
