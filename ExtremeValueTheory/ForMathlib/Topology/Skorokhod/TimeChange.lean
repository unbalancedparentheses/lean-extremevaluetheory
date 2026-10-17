/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Piecewise linear time changes of the unit interval

A *time change* is an order automorphism of the unit interval `I = [0, 1]`. We construct time
changes that move finitely many prescribed points to prescribed nearby positions while staying
uniformly close to the identity. These are the time changes used to compare step functions in
the Skorokhod `J₁` metric
([Billingsley, *Convergence of Probability Measures*, §12][billingsley1999]).

## Main statements

* `unitInterval.exists_orderIso_apply_eq`: a time change moving one point `b` to `b'` and fixing
  everything outside a neighbourhood `(u, v)` of `b`.
* `unitInterval.exists_orderIso_apply_eq_of_separated`: a time change moving finitely many
  well separated points `r` to nearby targets `g r` at once.
* `unitInterval.exists_orderIso_dist_lt_rat`: for finitely many points `R` of `I` and `δ > 0`
  there is a time change `φ` within `δ` of the identity such that `φ⁻¹ r` is rational for every
  `r ∈ R`.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

public section

open Set Metric

namespace unitInterval

/-- The tent function on `[u, v]` with peak `1` at `b`. -/
private noncomputable def tent (u b v t : ℝ) : ℝ :=
  max 0 (min ((t - u) / (b - u)) ((v - t) / (v - b)))

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

/-- For finitely many points `R` of `I` and `δ > 0` there is a time change `φ` within `δ` of the
identity such that `φ⁻¹ r` is rational for every `r ∈ R`. -/
theorem exists_orderIso_dist_lt_rat (R : Finset I) {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ : I ≃o I, (∀ t, dist (φ t) t < δ) ∧ ∀ r ∈ R, ∃ q : ℚ, ((φ.symm r : I) : ℝ) = q := by
  classical
  induction R using Finset.induction_on generalizing δ with
  | empty => exact ⟨OrderIso.refl I, by simpa using hδ, by simp⟩
  | insert a R haR ih =>
    obtain ⟨φ, hφδ, hφR⟩ := ih (half_pos hδ)
    set b : ℝ := ((φ.symm a : I) : ℝ) with hb_def
    by_cases hb : ∃ q : ℚ, b = q
    · refine ⟨φ, fun t ↦ (hφδ t).trans (half_lt_self hδ), ?_⟩
      rw [Finset.forall_mem_insert]
      exact ⟨hb, hφR⟩
    push Not at hb
    -- A ball around `b` avoiding `0`, `1` and the points `φ⁻¹ r`, `r ∈ R`.
    set K : Finset ℝ := R.image fun r ↦ (φ.symm r : ℝ)
    have hbK : b ∉ K := by
      simp only [K, Finset.mem_image, not_exists, not_and]
      intro r hr hrb
      exact haR (φ.symm.injective (Subtype.ext hrb) ▸ hr)
    have hb0 : b ≠ 0 := fun h ↦ hb 0 (by simp [h])
    have hb1 : b ≠ 1 := fun h ↦ hb 1 (by simp [h])
    have hbO : b ∈ Ioo (0 : ℝ) 1 ∩ (K : Set ℝ)ᶜ :=
      ⟨⟨lt_of_le_of_ne (φ.symm a).2.1 hb0.symm, lt_of_le_of_ne (φ.symm a).2.2 hb1⟩, hbK⟩
    obtain ⟨η, hη, hηO⟩ :=
      Metric.isOpen_iff.1 (isOpen_Ioo.inter K.finite_toSet.isClosed.isOpen_compl) b hbO
    have hball {x : ℝ} (hx : |x - b| < η) : x ∈ Ioo (0 : ℝ) 1 ∩ (K : Set ℝ)ᶜ :=
      hηO (by rwa [mem_ball, Real.dist_eq])
    set u := b - η / 2 with hu_def
    set v := b + η / 2 with hv_def
    obtain ⟨q, hbq, hqb⟩ := exists_rat_btwn
      (lt_add_of_pos_right b (lt_min (by positivity : 0 < η / 4) (half_pos hδ)))
    have hqb' : |b - q| < min (η / 4) (δ / 2) := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.2 hbq)]
      linarith
    have hu : 0 ≤ u :=
      (hball (x := u) (by rw [abs_lt]; constructor <;> linarith)).1.1.le
    have hv : v ≤ 1 :=
      (hball (x := v) (by rw [abs_lt]; constructor <;> linarith)).1.2.le
    have hη4 : |b - q| < η / 4 := hqb'.trans_le (min_le_left _ _)
    have hη4' := abs_lt.1 hη4
    obtain ⟨ν, hνq, hνfix, hνdist⟩ := exists_orderIso_apply_eq (b := q) (b' := b) hu hv
      (by linarith) (by linarith) (lt_min (by linarith) (by linarith))
    have hqI : (q : ℝ) ∈ I := ⟨by linarith [hbO.1.1], by linarith⟩
    refine ⟨ν.trans φ, fun t ↦ ?_, ?_⟩
    · calc dist (φ (ν t)) t ≤ dist (φ (ν t)) (ν t) + dist (ν t) t := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le (hφδ _)
            ((hνdist t).trans (hqb'.le.trans (min_le_right _ _)))
        _ = δ := add_halves δ
    · simp only [Finset.forall_mem_insert, OrderIso.symm_trans_apply]
      constructor
      · refine ⟨q, ?_⟩
        have : ν ⟨q, hqI⟩ = φ.symm a := Subtype.ext (hνq _ rfl)
        rw [← this, OrderIso.symm_apply_apply]
      · intro r hr
        have hk : ((φ.symm r : I) : ℝ) ≤ u ∨ v ≤ (φ.symm r : I) := by
          by_contra! h
          refine (hball (x := φ.symm r) ?_).2 (Finset.mem_image_of_mem _ hr)
          rw [abs_lt]
          constructor <;> linarith [h.1, h.2]
        rw [ν.symm_apply_eq.2 (hνfix _ hk).symm]
        exact hφR r hr

/-- A time change moving finitely many points `r ∈ R` to targets `g r` at once, provided the
points are `4η`-separated from each other and `2η`-separated from the endpoints, and each moves
by less than `η`. It fixes every point at distance at least `2η` from `R`, and it moves every
point by at most the total displacement `∑ r ∈ R, dist (g r) r`. -/
theorem exists_orderIso_apply_eq_of_separated (R : Finset I) (g : I → I) {η : ℝ}
    (hR₀ : ∀ r ∈ R, 2 * η ≤ (r : ℝ) ∧ (r : ℝ) + 2 * η ≤ 1)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 4 * η ≤ dist r r') (hg : ∀ r ∈ R, dist (g r) r < η) :
    ∃ φ : I ≃o I, (∀ r ∈ R, φ r = g r) ∧ (∀ t, (∀ r ∈ R, 2 * η ≤ dist t r) → φ t = t) ∧
      ∀ t, dist (φ t) t ≤ ∑ r ∈ R, dist (g r) r := by
  classical
  induction R using Finset.induction_on with
  | empty => exact ⟨OrderIso.refl I, by simp, by simp, by simp⟩
  | insert a R haR ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hR₀ hR hg
    obtain ⟨φ, hφR, hφfix, hφdist⟩ := ih hR₀.2 (fun r hr r' hr' ↦ (hR.2 r hr).2 r' hr') hg.2
    have hga := hg.1
    rw [Subtype.dist_eq, Real.dist_eq] at hga
    have hη : 0 < η := (abs_nonneg _).trans_lt hga
    -- The one-knot time change moving `a` to `g a` inside `(a - 2η, a + 2η)`.
    obtain ⟨ν, hνa, hνfix, hνdist⟩ := exists_orderIso_apply_eq (b := a) (b' := g a)
      (u := a - 2 * η) (v := a + 2 * η) (by linarith [hR₀.1.1]) hR₀.1.2
      (by linarith [abs_nonneg ((g a : ℝ) - a)]) (by linarith [abs_nonneg ((g a : ℝ) - a)])
      (lt_min (by linarith) (by linarith))
    have hνfix' (t : I) (ht : 2 * η ≤ dist t a) : ν t = t := by
      refine hνfix t ?_
      rw [Subtype.dist_eq, Real.dist_eq] at ht
      rcases le_abs'.1 ht with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hsep (r : I) (hr : r ∈ R) : 4 * η ≤ dist r a :=
      (hR.2 r hr).1 fun h ↦ haR (h ▸ hr)
    refine ⟨φ.trans ν, ?_, fun t ht ↦ ?_, fun t ↦ ?_⟩
    · simp only [Finset.mem_insert, forall_eq_or_imp, OrderIso.trans_apply]
      refine ⟨?_, fun r hr ↦ ?_⟩
      · rw [hφfix a fun r hr ↦ ?_]
        · exact Subtype.ext (hνa a rfl)
        · rw [dist_comm]
          linarith [hsep r hr]
      · rw [hφR r hr]
        refine hνfix' _ ?_
        have := dist_triangle_right r a (g r)
        rw [dist_comm r (g r), dist_comm a (g r)] at this
        linarith [hsep r hr, hg.2 r hr]
    · simp only [Finset.mem_insert, forall_eq_or_imp] at ht
      rw [OrderIso.trans_apply, hφfix t ht.2, hνfix' t ht.1]
    · rw [Finset.sum_insert haR, OrderIso.trans_apply]
      calc dist (ν (φ t)) t ≤ dist (ν (φ t)) (φ t) + dist (φ t) t := dist_triangle _ _ _
        _ ≤ dist (g a) a + ∑ r ∈ R, dist (g r) r := by
          gcongr
          · exact (hνdist _).trans_eq (by rw [Subtype.dist_eq, Real.dist_eq])
          · exact hφdist t

end unitInterval
