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

open Filter Set Topology Metric unitInterval TopologicalSpace
open scoped ENNReal

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

end unitInterval

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
