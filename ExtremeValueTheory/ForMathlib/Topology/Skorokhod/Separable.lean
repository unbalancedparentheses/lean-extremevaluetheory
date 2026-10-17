/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Metric
public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Cadlag
public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.TimeChange

/-!
# Separability of the Skorokhod space

We prove that the Skorokhod space `D([0, 1], E)` with the `J₁` topology is separable when `E`
is ([Billingsley, *Convergence of Probability Measures*, Theorem 12.2][billingsley1999]).

The countable dense family consists of step functions with rational jump points and values in a
countable dense subset of `E`. To compare a càdlàg function with such a step function we use
time changes that move finitely many given points to rational points
(`unitInterval.exists_orderIso_dist_lt_rat`).

## Main statements

* `SkorokhodSpace.separableSpace_of_countable`: a countable family of functions approximating
  every càdlàg function in the Skorokhod distance gives separability.
* `SkorokhodSpace.instSeparableSpace`: `D([0, 1], E)` is separable when `E` is.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

public section

open Filter Set Topology Metric unitInterval TopologicalSpace
open scoped ENNReal

namespace SkorokhodSpace

variable {E : Type*} [PseudoEMetricSpace E]

/-- If a countable family `T` of functions `I → E` approximates every càdlàg function arbitrarily
well in the Skorokhod distance, then the Skorokhod space is separable. The functions in `T` need
not be càdlàg. -/
lemma separableSpace_of_countable {T : Set (I → E)} (hT : T.Countable)
    (h : ∀ x : SkorokhodSpace E, ∀ ε > 0, ∃ τ ∈ T, skorokhodEDist τ x < ε) :
    SeparableSpace (SkorokhodSpace E) := by
  rcases isEmpty_or_nonempty (SkorokhodSpace E) with hD | hD
  · exact ⟨⟨∅, countable_empty, fun x ↦ (IsEmpty.false x).elim⟩⟩
  have : Countable T := hT.to_subtype
  let pick : T × ℕ → SkorokhodSpace E := fun p ↦
    Classical.epsilon fun y : SkorokhodSpace E ↦ skorokhodEDist p.1.1 y < (p.2 : ℝ≥0∞)⁻¹
  refine ⟨⟨range pick, countable_range pick, EMetric.dense_iff.2 fun x r hr ↦ ?_⟩⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.half_pos hr.ne').ne'
  obtain ⟨τ, hτ, hτx⟩ := h x _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  have hy : skorokhodEDist τ (pick (⟨τ, hτ⟩, n)) < (n : ℝ≥0∞)⁻¹ :=
    Classical.epsilon_spec (p := fun y : SkorokhodSpace E ↦ skorokhodEDist τ y < (n : ℝ≥0∞)⁻¹)
      ⟨x, hτx⟩
  refine ⟨pick (⟨τ, hτ⟩, n), ?_, mem_range_self _⟩
  rw [mem_eball, edist_def, ← ENNReal.add_halves r]
  calc skorokhodEDist (pick (⟨τ, hτ⟩, n)) x
      ≤ skorokhodEDist (pick (⟨τ, hτ⟩, n)) τ + skorokhodEDist τ x := skorokhodEDist_triangle _ _ _
    _ < r / 2 + r / 2 := by
      rw [skorokhodEDist_comm]
      exact ENNReal.add_lt_add (hy.trans hn) (hτx.trans hn)

/-- **Billingsley, Theorem 12.2.** The Skorokhod space `D([0, 1], E)` with the `J₁` topology is
separable when `E` is. A countable dense family is given by the step functions with rational
jump points and values in a countable dense subset of `E`. -/
instance instSeparableSpace [SeparableSpace E] : SeparableSpace (SkorokhodSpace E) := by
  classical
  rcases isEmpty_or_nonempty E with hE | ⟨⟨e₀⟩⟩
  · exact ⟨⟨∅, countable_empty, fun x ↦ (IsEmpty.false (x 0)).elim⟩⟩
  obtain ⟨C, hCc, hCd⟩ := exists_countable_dense E
  have : Countable C := hCc.to_subtype
  -- The step function with jumps at the points of `Q` and value `w q` on `[q, next point)`.
  let step (Q : Finset ℚ) (w : ℚ → E) (t : I) : E :=
    if h : (Q.filter fun q : ℚ ↦ (q : ℝ) ≤ t).Nonempty then
      w ((Q.filter fun q : ℚ ↦ (q : ℝ) ≤ t).max' h)
    else e₀
  let ext (Q : Finset ℚ) (w : Q → C) (q : ℚ) : E := if hq : q ∈ Q then (w ⟨q, hq⟩ : E) else e₀
  refine separableSpace_of_countable (T := ⋃ Q : Finset ℚ, range fun w : Q → C ↦ step Q (ext Q w))
    (countable_iUnion fun Q ↦ countable_range _) fun x ε hε ↦ ?_
  obtain ⟨ε₀, hε₀, hε₀ε⟩ := exists_between hε
  have hε₀2 : 0 < ε₀ / 2 := ENNReal.half_pos hε₀.ne'
  obtain ⟨s, hs⟩ := x.isCadlag.exists_finset_edist_lt hε₀2
  obtain ⟨φ, hφδ, hφR⟩ := unitInterval.exists_orderIso_dist_lt_rat (insert 0 s)
    (ENNReal.toReal_pos hε₀.ne' hε₀ε.ne_top)
  choose! ρ hρ using hφR
  set Q : Finset ℚ := (insert 0 s).image ρ
  have hC (y : E) : ∃ c ∈ C, edist y c < ε₀ / 2 := EMetric.mem_closure_iff.1 (hCd y) _ hε₀2
  choose cv hcvC hcv using hC
  let w : Q → C := fun q ↦ ⟨cv (x (φ (projIcc 0 1 zero_le_one (q : ℝ)))), hcvC _⟩
  refine ⟨_, mem_iUnion.2 ⟨Q, mem_range_self w⟩,
    (skorokhodEDist_le_of_forall φ (fun t ↦ ?_) (fun t ↦ ?_)).trans_lt hε₀ε⟩
  · rw [edist_dist]
    exact ENNReal.ofReal_le_of_le_toReal (hφδ t).le
  -- The last rational jump point `qm ≤ t` is `φ⁻¹ rm` for a cut point `rm ≤ φ t`, and no cut
  -- point lies in `(rm, φ t]`.
  obtain ⟨F, hFdef⟩ : ∃ F, F = Q.filter fun q : ℚ ↦ (q : ℝ) ≤ t := ⟨_, rfl⟩
  have h0 : ρ 0 ∈ F := by
    rw [hFdef]
    refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem ρ (Finset.mem_insert_self 0 s), ?_⟩
    rw [← hρ 0 (Finset.mem_insert_self 0 s), show φ.symm 0 = 0 from φ.symm.map_bot]
    exact t.2.1
  have hF : F.Nonempty := ⟨_, h0⟩
  have hsubF (q : ℚ) (hq : q ∈ F) : q ∈ Q ∧ (q : ℝ) ≤ t := by
    rw [hFdef] at hq
    exact Finset.mem_filter.1 hq
  have hqmQ : F.max' hF ∈ Q := (hsubF _ (F.max'_mem hF)).1
  have hqmt : ((F.max' hF : ℚ) : ℝ) ≤ t := (hsubF _ (F.max'_mem hF)).2
  obtain ⟨rm, hrm, hrmq⟩ := Finset.mem_image.1 hqmQ
  have hφrm : ((φ.symm rm : I) : ℝ) = F.max' hF := by rw [hρ rm hrm, hrmq]
  have hval : step Q (ext Q w) t = cv (x rm) := by
    simp only [step, ← hFdef, hF, hqmQ, ext, w, dite_true]
    rw [← hφrm, projIcc_val, OrderIso.apply_symm_apply]
  have hrm_le : rm ≤ φ t := by
    rw [← φ.symm_apply_le, ← Subtype.coe_le_coe, hφrm]
    exact hqmt
  have hcut : ∀ r ∈ s, r ≤ rm ∨ φ t < r := by
    intro r hr
    by_contra! hcon
    have hrQ : r ∈ insert 0 s := Finset.mem_insert_of_mem hr
    have hrF : ρ r ∈ F := by
      rw [hFdef]
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem ρ hrQ, ?_⟩
      rw [← hρ r hrQ, Subtype.coe_le_coe, φ.symm_apply_le]
      exact hcon.2
    have : ((φ.symm r : I) : ℝ) ≤ φ.symm rm := by
      rw [hρ r hrQ, hφrm]
      exact_mod_cast F.le_max' _ hrF
    exact (not_le.2 hcon.1) (φ.symm.le_iff_le.1 (Subtype.coe_le_coe.1 this))
  rw [hval, ← ENNReal.add_halves ε₀]
  calc edist (cv (x rm)) (x (φ t)) ≤ edist (cv (x rm)) (x rm) + edist (x rm) (x (φ t)) :=
        edist_triangle _ _ _
    _ ≤ ε₀ / 2 + ε₀ / 2 := by
      rw [edist_comm]
      exact add_le_add (hcv _).le (hs rm (φ t) hrm_le hcut).le

end SkorokhodSpace
