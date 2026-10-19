/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.OrderStatistics

/-!
# Order statistics of a sorted sample

Evaluation lemmas for `ExtremeValueTheory.orderStat` on a sample whose sorting permutation is
known: for an increasing sample the descending order statistics are the sample read backwards,
`X_{(j+1)} = x_{n-1-j}`. These are the lemmas needed to evaluate an estimator on an explicit
sample.

## Main results

* `orderStat_eq_of_monotone_comp`: if `x ∘ σ` is increasing, `orderStat x j = x (σ (rev j))`.
* `orderStat_of_monotone`: if `x` is increasing, `orderStat x j = x (rev j)`.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006), §3.2.
-/

namespace ExtremeValueTheory

variable {n : ℕ}

/-- If the permutation `σ` sorts the sample `x` increasingly, the `(j+1)`-th largest entry of
`x` is `x (σ (n - 1 - j))`. -/
theorem orderStat_eq_of_monotone_comp {x : Fin n → ℝ} (σ : Equiv.Perm (Fin n))
    (hσ : Monotone (x ∘ σ)) {j : ℕ} (hj : j < n) :
    orderStat x j = x (σ (Fin.rev ⟨j, hj⟩)) := by
  rw [orderStat_of_lt x hj]
  exact (congrFun (Tuple.comp_sort_eq_comp_iff_monotone.2 hσ) _).symm

/-- For an increasing sample the descending order statistics are the sample read backwards:
`orderStat x j = x (n - 1 - j)`. -/
theorem orderStat_of_monotone {x : Fin n → ℝ} (hx : Monotone x) {j : ℕ} (hj : j < n) :
    orderStat x j = x (Fin.rev ⟨j, hj⟩) := by
  rw [orderStat_of_lt x hj, Tuple.sort_eq_refl_iff_monotone.2 hx]
  rfl

end ExtremeValueTheory
