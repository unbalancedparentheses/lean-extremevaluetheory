/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Upper-tail quantiles

The library has one quantile concept for the upper tail. For a survival function
`S(x) = P(X > x)` and an exceedance probability `p`,

  `upperQuantile S p = S^←(p) = inf {x | S x ≤ p}`,

the level-`p` upper quantile `x_p` (so `P(X > x_p) ≤ p`, with equality for continuous laws).

The return-period parametrisation of de Haan and Ferreira, `U(t) = F^←(1 - 1/t)`, is the same
object at level `p = 1/t`:

* `ExtremeValueTheory.survivalQuantile S t = upperQuantile S t⁻¹` for `t > 1` (and `0` for
  `t ≤ 1`), on a raw survival function;
* `CumulativeDistributionFunction.tailQuantile F t = upperQuantile (1 - F) (1 / t)`, on a
  distribution function (in `DomainOfAttraction/Quantile.lean`).

The quantile of a random variable `Y` under `P` is `upperQuantile (survival P Y) p`; the
former name `ExtremeValueTheory.tailQuantile P Y p` is a deprecated abbreviation for it.

## Main definitions

* `ExtremeValueTheory.upperQuantile S p`: the canonical upper quantile at level `p`.
* `ExtremeValueTheory.survivalQuantile S t`: the tail quantile function `U(t)`, return period `t`.
-/

open Set

namespace ExtremeValueTheory

/-- The **upper quantile at level `p`** of a survival function `S`:
`S^←(p) = inf {x | S x ≤ p}`. If `S x = P(X > x)` and `0 < p < 1`, this is the quantile `x_p`
with `P(X > x_p) ≤ p`, i.e. `F^←(1 - p)` for `F = 1 - S`. This is the library's one definition
of an upper-tail quantile; the return-period forms `survivalQuantile` and
`CumulativeDistributionFunction.tailQuantile` are defined from it. -/
noncomputable def upperQuantile (S : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {x | S x ≤ p}

theorem upperQuantile_def (S : ℝ → ℝ) (p : ℝ) : upperQuantile S p = sInf {x | S x ≤ p} := rfl

/-- The **tail quantile function** `U(t) = (1 / S)^←(t) = inf {x | S x ≤ 1/t}` of a
survival function `S`, for return periods `t > 1` ([dHF, §1.1.2]); we set `U(t) = 0` for
`t ≤ 1`. It is `upperQuantile S t⁻¹` for `t > 1` (`survivalQuantile_of_one_lt`). -/
noncomputable def survivalQuantile (S : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 1 < t then upperQuantile S t⁻¹ else 0

theorem survivalQuantile_of_one_lt {S : ℝ → ℝ} {t : ℝ} (ht : 1 < t) :
    survivalQuantile S t = upperQuantile S t⁻¹ := by
  simp [survivalQuantile, ht]

theorem survivalQuantile_of_le_one {S : ℝ → ℝ} {t : ℝ} (ht : t ≤ 1) :
    survivalQuantile S t = 0 := by
  simp [survivalQuantile, not_lt.2 ht]

/-- The level form in terms of the return-period form: `x_p = U(1/p)` for `0 < p < 1`. -/
theorem upperQuantile_eq_survivalQuantile {S : ℝ → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    upperQuantile S p = survivalQuantile S p⁻¹ := by
  rw [survivalQuantile_of_one_lt ((one_lt_inv₀ hp0).2 hp1), inv_inv]

end ExtremeValueTheory
