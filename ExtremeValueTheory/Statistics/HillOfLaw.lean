/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Hill
import ExtremeValueTheory.ForMathlib.Probability.DeltaMethod

/-!
# Hill consistency for a sample with a given law

`tendstoInMeasure_hill` states its hypothesis on the random variables, as regular variation of
`x ↦ P(X₀ > x)`. Most uses start from a named law `μ` with `HasLaw (X i) μ P`, whose tail is
regularly varying; this file packages that step, and reads the limit as a statement on the tail
index `α` rather than on `γ = 1/α`.

## Main results

* `tendstoInMeasure_hill_of_hasLaw`: `H_{k,n} → 1/α` for an iid sample of a law `μ` whose tail is
  regularly varying with index `-α`.
* `tendstoInMeasure_inv_hill_of_hasLaw`: the same for the tail index estimate, `1 / H_{k,n} → α`.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Consistency of the Hill estimator for a sample with a given law**: if `X` is iid with law
`μ`, the tail of `μ` is regularly varying with index `-α`, `k → ∞` and `k/n → 0`, then
`H_{k,n} → 1/α` in probability. -/
theorem tendstoInMeasure_hill_of_hasLaw {μ : Measure ℝ} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, HasLaw (X i) μ P) (hindep : iIndepFun X P)
    {α : ℝ} (hα : 0 < α) (hRV : IsRegularlyVarying (fun x => μ.real (Ioi x)) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  refine tendstoInMeasure_hill hX hindep (fun i => (hlaw i).identDistrib (hlaw 0)) hα ?_ hk hkn
  refine hRV.congr (Eventually.of_forall fun x => ?_)
  show _ = (P _).toReal
  rw [(hlaw 0).measure_eq (p := (x < ·)) measurableSet_Ioi]
  rfl

/-- **The Hill estimate of the tail index**: under the hypotheses of
`tendstoInMeasure_hill_of_hasLaw`, `1 / H_{k,n} → α` in probability. -/
theorem tendstoInMeasure_inv_hill_of_hasLaw {μ : Measure ℝ} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, HasLaw (X i) μ P) (hindep : iIndepFun X P)
    {α : ℝ} (hα : 0 < α) (hRV : IsRegularlyVarying (fun x => μ.real (Ioi x)) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => (hill (fun i : Fin n => X i ω) (k n))⁻¹) atTop
      (fun _ => α) := by
  have hc : ContinuousAt (fun x : ℝ => x⁻¹) (1 / α) :=
    continuousAt_inv₀ (one_div_pos.2 hα).ne'
  simpa using (tendstoInMeasure_hill_of_hasLaw hX hlaw hindep hα hRV hk hkn).comp_continuousAt hc

end ExtremeValueTheory
