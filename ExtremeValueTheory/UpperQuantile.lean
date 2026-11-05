/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.Measure.Real

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
* `ExtremeValueTheory.survival P Y x = P(Y > x)`: the survival function of a random variable, the
  library's one definition of it.

## Main results

* `upperQuantile_spec`: for `S` antitone and right-continuous, `S (x_p) ≤ p` and `S y > p` for
  every `y < x_p` (the Galois connection of the generalized inverse).
* `upperQuantile_spec_of_tendsto_atTop`: the same, with the bound `M ≤ x_p` whenever `p < S M`,
  for `S → 0` at `+∞`.
* `upperQuantile_le`, `le_upperQuantile`: the two halves of the Galois connection.
-/

open Set Filter Topology

namespace ExtremeValueTheory

/-- The **upper quantile at level `p`** of a survival function `S`:
`S^←(p) = inf {x | S x ≤ p}`. If `S x = P(X > x)` and `0 < p < 1`, this is the quantile `x_p`
with `P(X > x_p) ≤ p`, i.e. `F^←(1 - p)` for `F = 1 - S`. This is the library's one definition
of an upper-tail quantile; the return-period forms `survivalQuantile` and
`CumulativeDistributionFunction.tailQuantile` are defined from it. -/
noncomputable def upperQuantile (S : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {x | S x ≤ p}

theorem upperQuantile_def (S : ℝ → ℝ) (p : ℝ) : upperQuantile S p = sInf {x | S x ≤ p} := rfl

section Spec

variable {S : ℝ → ℝ} {p : ℝ}

/-- If `S y ≤ p` and `S` stays above `p` somewhere (so the set is bounded below), then
`x_p ≤ y`. -/
theorem upperQuantile_le (hS : Antitone S) {M y : ℝ} (hM : p < S M) (hy : S y ≤ p) :
    upperQuantile S p ≤ y := by
  refine csInf_le ⟨M, fun x hx => ?_⟩ hy
  by_contra h
  exact absurd ((hS (not_le.1 h).le).trans hx) (not_le.2 hM)

/-- If `S` falls to `p` somewhere and `p < S y`, then `y ≤ x_p`. -/
theorem le_upperQuantile (hS : Antitone S) (hne : ∃ x, S x ≤ p) {y : ℝ} (hy : p < S y) :
    y ≤ upperQuantile S p := by
  obtain ⟨x, hx⟩ := hne
  refine le_csInf ⟨x, hx⟩ fun z hz => ?_
  by_contra h
  exact absurd ((hS (not_le.1 h).le).trans hz) (not_le.2 hy)

/-- **The upper quantile of an antitone right-continuous function**: if `S x ≤ p` for some `x`
and `p < S y` for some `y`, then `S (x_p) ≤ p` and `p < S y` for every `y < x_p`. -/
theorem upperQuantile_spec (hS : Antitone S) (hrc : ∀ x, ContinuousWithinAt S (Ici x) x)
    (hne : ∃ x, S x ≤ p) (hbdd : ∃ y, p < S y) :
    S (upperQuantile S p) ≤ p ∧ ∀ y < upperQuantile S p, p < S y := by
  obtain ⟨y₀, hy₀⟩ := hbdd
  have hB : BddBelow {x | S x ≤ p} := ⟨y₀, fun x hx => by
    by_contra hcon
    exact absurd ((hS (not_le.1 hcon).le).trans hx) (not_le.2 hy₀)⟩
  have hne' : ({x | S x ≤ p} : Set ℝ).Nonempty := hne
  rw [upperQuantile_def]
  set s := sInf {x | S x ≤ p}
  constructor
  · have hlim : Tendsto S (𝓝[>] s) (𝓝 (S s)) :=
      (hrc s).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun x hx => ?_)
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne' (show s < x from hx)
    exact (hS hyx.le).trans hy
  · intro y hy
    by_contra hcon
    exact absurd (csInf_le hB (not_lt.1 hcon)) (not_le.2 hy)

/-- `upperQuantile_spec` for a function tending to `0` at `+∞` and a level `0 < p < S M`: then
also `M ≤ x_p`. -/
theorem upperQuantile_spec_of_tendsto_atTop (hS : Antitone S)
    (hrc : ∀ x, ContinuousWithinAt S (Ici x) x) (h0 : Tendsto S atTop (𝓝 0)) {M : ℝ}
    (hp : 0 < p) (hM : p < S M) :
    S (upperQuantile S p) ≤ p ∧ (∀ x < upperQuantile S p, p < S x) ∧ M ≤ upperQuantile S p := by
  have hne : ∃ x, S x ≤ p := by
    obtain ⟨x, hx⟩ := (h0.eventually (gt_mem_nhds hp)).exists
    exact ⟨x, hx.le⟩
  obtain ⟨h1, h2⟩ := upperQuantile_spec hS hrc hne ⟨M, hM⟩
  exact ⟨h1, h2, le_upperQuantile hS hne hM⟩

end Spec

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

section Survival

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The survival function `x ↦ P(Y > x)` of a real random variable. This is the library's one
definition of the survival function of a random variable. -/
noncomputable def survival (P : MeasureTheory.Measure Ω) (Y : Ω → ℝ) (x : ℝ) : ℝ :=
  (P {ω | x < Y ω}).toReal

theorem survival_eq_measureReal (P : MeasureTheory.Measure Ω) (Y : Ω → ℝ) (x : ℝ) :
    survival P Y x = P.real {ω | x < Y ω} := rfl

end Survival

end ExtremeValueTheory
