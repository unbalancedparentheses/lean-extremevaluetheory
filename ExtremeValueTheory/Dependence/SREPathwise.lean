/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.SRE
import ExtremeValueTheory.Dependence.AR1Uniqueness

/-!
# The pathwise stationary solution of a stochastic recurrence equation

Let `(A_t, B_t)_{t ∈ ℤ}` be iid with law `ν`, `E log |A| < 0`, `E log⁺ |B| < ∞`. The series

  `X_t = ∑_{k ≥ 0} A_t A_{t-1} ⋯ A_{t-k+1} B_{t-k}`

(the perpetuity of the past `(A_{t-k}, B_{t-k})_{k ≥ 0}`) converges absolutely almost surely,
solves `X_t = A_t X_{t-1} + B_t` for all `t` almost surely, and is the only solution which is
bounded in probability (in particular the only strictly stationary one) [BDM16, Theorem 2.1.3;
Brandt 1986; Bougerol–Picard 1992]. Its marginal law is `stationaryLaw ν`.

## Main results

* `SRE.ae_solution_eq`: the recursion holds almost surely, for all `t ∈ ℤ`.
* `SRE.map_solution`: `X_t` has law `stationaryLaw ν`.
* `SRE.ae_eq_solution_of_tight`, `SRE.ae_eq_solution_of_identDistrib`: uniqueness among
  solutions bounded in probability, resp. with identically distributed marginals. The proof
  reuses the core `AR1.ae_eq_of_tight_of_iterate` of the AR(1) uniqueness theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal

namespace ExtremeValueTheory

namespace SRE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {V : ℤ → Ω → ℝ × ℝ}

/-- The innovations seen backwards from time `t`: `k ↦ (A_{t-k}, B_{t-k})`. -/
def past (V : ℤ → Ω → ℝ × ℝ) (t : ℤ) (ω : Ω) : ℕ → ℝ × ℝ := fun k => V (t - k) ω

/-- The stationary solution `X_t = ∑_{k ≥ 0} A_t ⋯ A_{t-k+1} B_{t-k}`. -/
noncomputable def solution (V : ℤ → Ω → ℝ × ℝ) (t : ℤ) (ω : Ω) : ℝ := perpetuity (past V t ω)

theorem shift_past (t : ℤ) (ω : Ω) : shift (past V t ω) = past V (t - 1) ω := by
  funext k
  simp only [shift, past]
  congr 1
  push_cast
  ring

theorem past_zero (t : ℤ) (ω : Ω) : past V t ω 0 = V t ω := by simp [past]

theorem measurable_past (hV : ∀ t, Measurable (V t)) (t : ℤ) : Measurable (past V t) :=
  Measurable.of_eval fun k => hV (t - k)

/-- The recursion `X_t = A_t X_{t-1} + B_t`, wherever the series at time `t` converges. -/
theorem solution_eq {t : ℤ} {ω : Ω} (h : Summable (term (past V t ω))) :
    solution V t ω = affine (solution V (t - 1) ω) (V t ω) := by
  rw [solution, perpetuity_eq h, shift_past, past_zero, solution]

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- The past of an iid sequence is iid with the same law. -/
theorem map_past (hV : ∀ t, Measurable (V t)) (hiid : iIndepFun V P) (hid : ∀ t, P.map (V t) = ν)
    (t : ℤ) : P.map (past V t) = seqLaw ν :=
  RandomIteration.map_path_eq_infinitePi (V := fun k : ℕ => V (t - k)) (fun k => hV _)
    (hiid.precomp fun a b h => by simpa using h) fun k => hid _

theorem ae_contracting_past (hV : ∀ t, Measurable (V t)) (hiid : iIndepFun V P)
    (hid : ∀ t, P.map (V t) = ν) (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) (t : ℤ) :
    ∀ᵐ ω ∂P, Contracting ((∫ p, log |p.1| ∂ν) / 2) (past V t ω) := by
  have h : ∀ᵐ v ∂P.map (past V t), Contracting ((∫ p, log |p.1| ∂ν) / 2) v := by
    rw [map_past hV hiid hid]; exact ae_contracting_seqLaw hA hneg hB
  exact ae_of_ae_map (measurable_past hV t).aemeasurable h

/-- **The stationary solution solves the recursion** ([BDM16, Theorem 2.1.3]): almost surely,
`X_t = A_t X_{t-1} + B_t` for all `t ∈ ℤ`. -/
theorem ae_solution_eq (hV : ∀ t, Measurable (V t)) (hiid : iIndepFun V P)
    (hid : ∀ t, P.map (V t) = ν) (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) :
    ∀ᵐ ω ∂P, ∀ t, solution V t ω = (V t ω).1 * solution V (t - 1) ω + (V t ω).2 := by
  have hc : (∫ p, log |p.1| ∂ν) / 2 < 0 := by linarith
  rw [ae_all_iff]
  intro t
  filter_upwards [ae_contracting_past hV hiid hid hA hneg hB t] with ω hω
  exact solution_eq (hω.summable_term hc)

omit [IsProbabilityMeasure ν] in
/-- The stationary solution has law `stationaryLaw ν` at every time. -/
theorem map_solution (hV : ∀ t, Measurable (V t)) (hiid : iIndepFun V P)
    (hid : ∀ t, P.map (V t) = ν) (t : ℤ) : P.map (solution V t) = stationaryLaw ν := by
  rw [stationaryLaw, ← map_past hV hiid hid t,
    Measure.map_map measurable_perpetuity (measurable_past hV t)]
  rfl

/-- The iterated recursion: `Y_t = backward (Y_{t-n}) (past t) n`, i.e.
`Y_t = ∑_{k < n} A_t ⋯ A_{t-k+1} B_{t-k} + A_t ⋯ A_{t-n+1} Y_{t-n}`. -/
theorem eq_backward {Y : ℤ → Ω → ℝ} {ω : Ω}
    (h : ∀ t, Y t ω = (V t ω).1 * Y (t - 1) ω + (V t ω).2) (n : ℕ) (t : ℤ) :
    Y t ω = backward (Y (t - n) ω) (past V t ω) n := by
  induction n generalizing t with
  | zero => simp [backward_zero]
  | succ n ih =>
    rw [backward_succ, shift_past, past_zero, h t, ih (t - 1), affine,
      show t - 1 - (n : ℤ) = t - ((n + 1 : ℕ) : ℤ) by push_cast; ring]

/-- **Uniqueness of the stationary solution** ([BDM16, Theorem 2.1.3]; [Brandt 1986]): every
solution `Y` of `Y_t = A_t Y_{t-1} + B_t` which is bounded in probability equals the series
solution almost surely, at every time. -/
theorem ae_eq_solution_of_tight [IsProbabilityMeasure P] {Y : ℤ → Ω → ℝ}
    (hV : ∀ t, Measurable (V t)) (hiid : iIndepFun V P)
    (hid : ∀ t, P.map (V t) = ν) (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν)
    (hrec : ∀ᵐ ω ∂P, ∀ t, Y t ω = (V t ω).1 * Y (t - 1) ω + (V t ω).2)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ, ∀ s, P {ω | C < |Y s ω|} ≤ ε) (t : ℤ) :
    Y t =ᵐ[P] solution V t := by
  have hc : (∫ p, log |p.1| ∂ν) / 2 < 0 := by linarith
  have hpm := measurable_past hV t
  refine AR1.ae_eq_of_tight_of_iterate
    (S := fun n ω => backward 0 (past V t ω) n)
    (R := fun n ω => ∏ i ∈ Finset.range n, (past V t ω i).1) t
    (fun n => (((measurable_backward n).comp (measurable_const.prodMk hpm))).aestronglyMeasurable)
    (fun n => (Finset.measurable_prod _ fun i _ =>
      measurable_fst.comp ((measurable_pi_apply i).comp hpm)).aestronglyMeasurable) ?_ ?_ ?_
    htight
  · filter_upwards [hrec] with ω hω n
    rw [eq_backward hω n t]
    simp [backward]
  · filter_upwards [ae_contracting_past hV hiid hid hA hneg hB t] with ω hω
    exact hω.tendsto_backward hc 0
  · filter_upwards [ae_contracting_past hV hiid hid hA hneg hB t] with ω hω
    exact hω.tendsto_prod hc

/-- **Uniqueness among stationary solutions**: a solution with identically distributed marginals
(e.g. a strictly stationary one) equals the series solution almost surely. -/
theorem ae_eq_solution_of_identDistrib [IsProbabilityMeasure P] {Y : ℤ → Ω → ℝ}
    (hY : ∀ t, Measurable (Y t)) (hV : ∀ t, Measurable (V t)) (hiid : iIndepFun V P)
    (hid : ∀ t, P.map (V t) = ν) (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν)
    (hrec : ∀ᵐ ω ∂P, ∀ t, Y t ω = (V t ω).1 * Y (t - 1) ω + (V t ω).2)
    (hYid : ∀ t, IdentDistrib (Y t) (Y 0) P P) (t : ℤ) :
    Y t =ᵐ[P] solution V t :=
  ae_eq_solution_of_tight hV hiid hid hA hneg hB hrec (AR1.tight_of_identDistrib hY hYid) t

end SRE

end ExtremeValueTheory
