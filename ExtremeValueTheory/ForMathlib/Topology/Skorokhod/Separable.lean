/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Metric
public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Cadlag
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Topology.Instances.Rat

/-!
# Separability of the Skorokhod space

We prove that the Skorokhod space `D([0, 1], E)` with the `J₁` topology is separable when `E`
is ([Billingsley, *Convergence of Probability Measures*, Theorem 12.2][billingsley1999]).

The countable dense family consists of step functions with rational jump points and values in a
countable dense subset of `E`. To compare a càdlàg function with such a step function we use
time changes that move finitely many given points to rational points.

## Main statements

* `unitInterval.exists_orderIso_dist_lt_rat`: for finitely many points `R` of `I` and `δ > 0`
  there is a time change `φ` within `δ` of the identity such that `φ⁻¹ r` is rational for every
  `r ∈ R`.
* `SkorokhodSpace.instSeparableSpace`: `D([0, 1], E)` is separable when `E` is.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

public section

open Filter Set Topology Metric unitInterval
open scoped ENNReal

namespace unitInterval

/-- The tent function on `[u, v]` with peak `1` at `b`. -/
private noncomputable def tent (u b v t : ℝ) : ℝ := max 0 (min ((t - u) / (b - u)) ((v - t) / (v - b)))

private lemma continuous_tent (u b v : ℝ) : Continuous (tent u b v) := by
  unfold tent; fun_prop

private lemma tent_eq_zero {u b v t : ℝ} (hub : u < b) (hbv : b < v) (ht : t ≤ u ∨ v ≤ t) :
    tent u b v t = 0 := by
  refine max_eq_left (min_le_iff.2 ?_)
  rcases ht with ht | ht
  · exact Or.inl (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  · exact Or.inr (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

private lemma tent_self {u b v : ℝ} (hub : u < b) (hbv : b < v) : tent u b v b = 1 := by
  simp [tent, div_self (sub_pos.2 hub).ne', div_self (sub_pos.2 hbv).ne']

private lemma tent_nonneg (u b v t : ℝ) : 0 ≤ tent u b v t := le_max_left _ _

private lemma tent_le_one {u b v t : ℝ} (hub : u < b) (hbv : b < v) : tent u b v t ≤ 1 := by
  refine max_le zero_le_one ?_
  rcases le_total t b with htb | htb
  · exact (min_le_left _ _).trans ((div_le_one (sub_pos.2 hub)).2 (by linarith))
  · exact (min_le_right _ _).trans ((div_le_one (sub_pos.2 hbv)).2 (by linarith))

private lemma abs_tent_sub_le {u b v : ℝ} (hub : u < b) (hbv : b < v) (t t' : ℝ) :
    |tent u b v t' - tent u b v t| ≤ max (|t' - t| / (b - u)) (|t' - t| / (v - b)) := by
  have key (A A' B B' : ℝ) :
      |max 0 (min A' B') - max 0 (min A B)| ≤ max |A' - A| |B' - B| := by
    rw [max_comm 0, max_comm 0 (min A B)]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_min_sub_min_le_max _ _ _ _)
  refine (key _ _ _ _).trans_eq ?_
  have e1 : (t' - u) / (b - u) - (t - u) / (b - u) = (t' - t) / (b - u) := by ring
  have e2 : (v - t') / (v - b) - (v - t) / (v - b) = -((t' - t) / (v - b)) := by ring
  rw [e1, e2, abs_neg, abs_div, abs_div, abs_of_pos (sub_pos.2 hub), abs_of_pos (sub_pos.2 hbv)]

/-- A time change of `I` moving the point `b` to `b'` and fixing everything outside `(u, v)`. -/
lemma exists_orderIso_apply_eq {u b b' v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) (hub : u < b)
    (hbv : b < v) (hbb' : |b' - b| < min (b - u) (v - b)) :
    ∃ ν : I ≃o I, (∀ t : I, (t : ℝ) = b → (ν t : ℝ) = b') ∧
      (∀ t : I, (t : ℝ) ≤ u ∨ v ≤ t → ν t = t) ∧ ∀ t, dist (ν t) t ≤ |b' - b| := by
  set c := b' - b
  set g : ℝ → ℝ := fun t ↦ t + c * tent u b v t with hg
  have hgcont : Continuous g := continuous_id.add (continuous_const.mul (continuous_tent u b v))
  have hgmono : StrictMono g := by
    intro t t' htt'
    have hd : 0 < t' - t := sub_pos.2 htt'
    have h1 : |c| * |t' - t| / (b - u) < t' - t := by
      rw [div_lt_iff₀ (sub_pos.2 hub), abs_of_pos hd, mul_comm]
      exact mul_lt_mul_of_pos_left (hbb'.trans_le (min_le_left _ _)) hd
    have h2 : |c| * |t' - t| / (v - b) < t' - t := by
      rw [div_lt_iff₀ (sub_pos.2 hbv), abs_of_pos hd, mul_comm]
      exact mul_lt_mul_of_pos_left (hbb'.trans_le (min_le_right _ _)) hd
    have h3 : |c * (tent u b v t' - tent u b v t)| < t' - t := by
      rw [abs_mul]
      refine (mul_le_mul_of_nonneg_left (abs_tent_sub_le hub hbv t t') (abs_nonneg c)).trans_lt ?_
      rw [mul_max_of_nonneg _ _ (abs_nonneg c), ← mul_div_assoc, ← mul_div_assoc]
      exact max_lt h1 h2
    have := neg_abs_le (c * (tent u b v t' - tent u b v t))
    simp only [hg]
    nlinarith
  have hfix (t : ℝ) (ht : t ≤ u ∨ v ≤ t) : g t = t := by
    simp [hg, tent_eq_zero hub hbv ht]
  have hg0 : g 0 = 0 := hfix 0 (Or.inl hu)
  have hg1 : g 1 = 1 := hfix 1 (Or.inr hv)
  have hgI (t : I) : g t ∈ I :=
    ⟨hg0 ▸ hgmono.monotone t.2.1, hg1 ▸ hgmono.monotone t.2.2⟩
  set gI : I → I := fun t ↦ ⟨g t, hgI t⟩
  have hgImono : StrictMono gI := fun t t' h ↦ hgmono (Subtype.coe_lt_coe.2 h)
  have hgIsurj : Function.Surjective gI := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc zero_le_one hgcont.continuousOn
      (by rwa [hg0, hg1])
    exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
  refine ⟨StrictMono.orderIsoOfSurjective gI hgImono hgIsurj, fun t ht ↦ ?_, fun t ht ↦ ?_,
    fun t ↦ ?_⟩
  · change g t = b'
    simp [hg, ht, tent_self hub hbv, c]
  · exact Subtype.ext (hfix t ht)
  · change dist (g t) t ≤ |c|
    rw [Real.dist_eq, hg]
    simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg (tent_nonneg u b v t)]
    exact mul_le_of_le_one_right (abs_nonneg c) (tent_le_one hub hbv)

end unitInterval
