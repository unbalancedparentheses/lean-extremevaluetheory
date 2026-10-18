/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Complete

/-!
# The càdlàg modulus and relatively compact sets of the Skorokhod space

For `x : I → E` and `δ > 0`, Billingsley's *càdlàg modulus* is
`w'_x(δ) = inf_R max_i sup_{s, t ∈ [t_{i-1}, t_i)} edist (x s) (x t)`,
the infimum running over the `δ`-sparse partitions `0 = t_0 < ⋯ < t_v = 1` (all gaps larger than
`δ`) ([Billingsley, *Convergence of Probability Measures*, (12.6)][billingsley1999]). We encode
a partition as a finite set `R ⊆ I` containing `0` and `1` whose distinct points are more than
`δ` apart (`IsSparsePartition δ R`); two points `s ≤ t` lie in the same cell `[t_{i-1}, t_i)`
exactly when no point of `R` lies in `(s, t]`.

We prove the sufficiency half of the Arzelà–Ascoli theorem for `D([0, 1], E)`
([Billingsley, Theorem 12.3][billingsley1999]): a set `K` of càdlàg functions with values in a
totally bounded set and with `sup_{x ∈ K} w'_x(δ) → 0` as `δ → 0` has compact closure.

The proof shows that `K` is totally bounded for Billingsley's complete metric `d°`: a function
`x ∈ K` with a `δ`-sparse partition `R` of small oscillation is close in `d°` to a step function
with jumps on the grid `{j / m}` and values in a finite net of the range: a time change with
log-slope norm `O(|R| / (m δ))` moves the points of `R` onto the grid
(`unitInterval.exists_orderIso_apply_eq_of_separated_and_slope`), and `|R| ≤ ⌊1 / δ⌋ + 1`.

## Main definitions

* `cellOscillation x R`: the largest oscillation of `x` on a cell of the partition `R`.
* `IsSparsePartition δ R`: `R` is a partition of `[0, 1]` with all gaps larger than `δ`.
* `cadlagModulus x δ`: Billingsley's càdlàg modulus `w'_x(δ)`.

## Main statements

* `IsSparsePartition.card_le`: a `δ`-sparse partition has at most `⌊1 / δ⌋ + 1` points.
* `SkorokhodSpace.Billingsley.totallyBounded_of_forall_exists`: a set approximated by finite
  families of arbitrary functions in `d°` is totally bounded.
* `SkorokhodSpace.isCompact_closure_of_cadlagModulus`: **Billingsley, Theorem 12.3**
  (sufficiency).

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

@[expose] public section

open Filter Set Topology Metric unitInterval
open scoped ENNReal

variable {E : Type*}

section Modulus

variable [PseudoEMetricSpace E]

/-- The oscillation of `x` on the cells of the partition `R`: the supremum of `edist (x s) (x t)`
over the points `s ≤ t` with no point of `R` in `(s, t]`. -/
noncomputable def cellOscillation (x : I → E) (R : Finset I) : ℝ≥0∞ :=
  ⨆ (s : I) (t : I) (_ : s ≤ t) (_ : ∀ r ∈ R, r ≤ s ∨ t < r), edist (x s) (x t)

/-- `R` is a `δ`-sparse partition of `[0, 1]`: it contains `0` and `1`, and its distinct points
are more than `δ` apart. -/
def IsSparsePartition (δ : ℝ) (R : Finset I) : Prop :=
  0 ∈ R ∧ 1 ∈ R ∧ ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → δ < dist r r'

/-- Billingsley's càdlàg modulus `w'_x(δ)`
([Billingsley, *Convergence of Probability Measures*, (12.6)][billingsley1999]): the infimum over
the `δ`-sparse partitions `R` of the oscillation of `x` on the cells of `R`. -/
noncomputable def cadlagModulus (x : I → E) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ (R : Finset I) (_ : IsSparsePartition δ R), cellOscillation x R

lemma edist_le_cellOscillation {x : I → E} {R : Finset I} {s t : I} (hst : s ≤ t)
    (h : ∀ r ∈ R, r ≤ s ∨ t < r) : edist (x s) (x t) ≤ cellOscillation x R := by
  unfold cellOscillation
  exact le_iSup_of_le s (le_iSup_of_le t (le_iSup_of_le hst (le_iSup_of_le h le_rfl)))

lemma IsSparsePartition.mono {δ δ' : ℝ} {R : Finset I} (h : δ ≤ δ')
    (hR : IsSparsePartition δ' R) : IsSparsePartition δ R :=
  ⟨hR.1, hR.2.1, fun r hr r' hr' hne ↦ h.trans_lt (hR.2.2 r hr r' hr' hne)⟩

/-- The càdlàg modulus is monotone in `δ`. -/
lemma cadlagModulus_mono (x : I → E) {δ δ' : ℝ} (h : δ ≤ δ') :
    cadlagModulus x δ ≤ cadlagModulus x δ' :=
  iInf₂_mono' fun R hR ↦ ⟨R, hR.mono h, le_rfl⟩

lemma exists_isSparsePartition_of_cadlagModulus_lt {x : I → E} {δ : ℝ} {ε : ℝ≥0∞}
    (h : cadlagModulus x δ < ε) : ∃ R, IsSparsePartition δ R ∧ cellOscillation x R < ε := by
  simp only [cadlagModulus, iInf_lt_iff] at h
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, hR, h⟩

/-- A `δ`-sparse partition has at most `⌊1 / δ⌋ + 1` points. -/
lemma IsSparsePartition.card_le {δ : ℝ} (hδ : 0 < δ) {R : Finset I}
    (hR : IsSparsePartition δ R) : R.card ≤ ⌊1 / δ⌋₊ + 1 := by
  have h := Finset.card_le_card_of_injOn (fun r : I ↦ ⌊(r : ℝ) / δ⌋₊)
    (t := Finset.range (⌊1 / δ⌋₊ + 1)) (fun r _ ↦ by
      refine Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_mono ?_))
      exact div_le_div_of_nonneg_right r.2.2 hδ.le) (fun r hr r' hr' hrr' ↦ by
      by_contra hne
      have hd := hR.2.2 r hr r' hr' hne
      have e : ⌊(r : ℝ) / δ⌋₊ = ⌊(r' : ℝ) / δ⌋₊ := hrr'
      have h1 := Nat.floor_le (div_nonneg r.2.1 hδ.le)
      have h2 := Nat.lt_floor_add_one ((r : ℝ) / δ)
      have h3 := Nat.floor_le (div_nonneg r'.2.1 hδ.le)
      have h4 := Nat.lt_floor_add_one ((r' : ℝ) / δ)
      rw [e] at h1 h2
      have : |(r : ℝ) / δ - r' / δ| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
      rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at this
      rw [Subtype.dist_eq, Real.dist_eq] at hd
      linarith)
  simpa using h

end Modulus

namespace SkorokhodSpace

namespace Billingsley

/-- A set of the Skorokhod space which, for every `ε > 0`, is approximated within `ε` in
Billingsley's metric `d°` by a finite family of (arbitrary) functions `I → E` is totally bounded
for `d°`. -/
lemma totallyBounded_of_forall_exists [PseudoEMetricSpace E] {K : Set (Billingsley E)}
    (h : ∀ ε > 0, ∃ T : Set (I → E), T.Finite ∧ ∀ x ∈ K, ∃ τ ∈ T, billingsleyEDist τ x < ε) :
    TotallyBounded K := by
  rw [EMetric.totallyBounded_iff]
  intro ε hε
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · exact ⟨∅, finite_empty, empty_subset _⟩
  obtain ⟨T, hT, hK⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  have : Nonempty (Billingsley E) := ⟨x₀⟩
  let pick : (I → E) → Billingsley E := fun τ ↦
    Classical.epsilon fun y : Billingsley E ↦ billingsleyEDist τ y < ε / 2
  refine ⟨pick '' T, hT.image _, fun x hx ↦ ?_⟩
  obtain ⟨τ, hτ, hτx⟩ := hK x hx
  have hy : billingsleyEDist τ (pick τ) < ε / 2 :=
    Classical.epsilon_spec (p := fun y : Billingsley E ↦ billingsleyEDist τ y < ε / 2) ⟨x, hτx⟩
  refine mem_iUnion₂.2 ⟨pick τ, mem_image_of_mem _ hτ, ?_⟩
  rw [mem_eball, edist_def, ← ENNReal.add_halves ε]
  calc billingsleyEDist x (pick τ) ≤ billingsleyEDist x τ + billingsleyEDist τ (pick τ) :=
        billingsleyEDist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [billingsleyEDist_comm]
        exact ENNReal.add_lt_add hτx hy

end Billingsley

/-- **Billingsley, Theorem 12.3** (sufficiency), for pseudo extended metric spaces. -/
theorem isCompact_closure_of_cadlagModulus' [PseudoEMetricSpace E] [CompleteSpace E]
    {K : Set (SkorokhodSpace E)} {C : Set E} (hC : TotallyBounded C)
    (hKC : ∀ x ∈ K, ∀ t, x t ∈ C)
    (hK : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, cadlagModulus (⇑x) δ < ε) : IsCompact (closure K) := by
  classical
  have htb : TotallyBounded (homeomorphBillingsley '' K : Set (Billingsley E)) := by
    refine Billingsley.totallyBounded_of_forall_exists fun ε hε ↦ ?_
    rcases K.eq_empty_or_nonempty with hK0 | ⟨x₀, -⟩
    · exact ⟨∅, finite_empty, by simp [hK0]⟩
    obtain ⟨e, -, hpos, he⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have he0 : 0 < e := ENNReal.ofReal_pos.1 hpos
    set r := ENNReal.ofReal (e / 2) with hr_def
    have hr : 0 < r := ENNReal.ofReal_pos.2 (by linarith)
    have hrr : r + r = ENNReal.ofReal e := by
      rw [hr_def, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      ring_nf
    obtain ⟨δ, hδ, hKδ⟩ := hK r hr
    obtain ⟨N, hNf, hN⟩ := EMetric.totallyBounded_iff.1 hC r hr
    have hcv : ∀ y : C, ∃ c : N, edist (y : E) c < r := fun y ↦ by
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 (hN y.2)
      exact ⟨⟨c, hc⟩, hyc⟩
    choose cv hcv using hcv
    set Cd : ℕ := ⌊1 / δ⌋₊ + 1
    obtain ⟨m, hm⟩ := exists_nat_gt (max (4 / δ) (4 * Cd / (δ * e)))
    have hm1 : 4 / δ < m := (le_max_left _ _).trans_lt hm
    have hm2 : 4 * Cd / (δ * e) < m := (le_max_right _ _).trans_lt hm
    have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm1
    have hmδ : 1 / (m : ℝ) < δ / 4 := by
      rw [div_lt_iff₀ hm0]
      rw [div_lt_iff₀ hδ] at hm1
      linarith
    -- the grid map `t ↦ ⌊m t⌋ / m`
    let g : I → I := fun t ↦ projIcc 0 1 zero_le_one ((⌊(m : ℝ) * t⌋₊ : ℝ) / m)
    have hgv (t : I) : ((g t : I) : ℝ) = (⌊(m : ℝ) * t⌋₊ : ℝ) / m := by
      refine congrArg Subtype.val (projIcc_of_mem _ ⟨by positivity, ?_⟩)
      rw [div_le_one hm0]
      exact (Nat.floor_le (by have := t.2.1; positivity)).trans
        (by have := t.2.2; nlinarith)
    have hdist (t : I) : dist (g t) t < 1 / m := by
      rw [Subtype.dist_eq, hgv, Real.dist_eq, abs_lt]
      have h1 := Nat.floor_le (show (0 : ℝ) ≤ m * t by have := t.2.1; positivity)
      have h2 := Nat.lt_floor_add_one ((m : ℝ) * t)
      have a : (⌊(m : ℝ) * t⌋₊ : ℝ) / m ≤ t := by
        rw [div_le_iff₀ hm0]; linarith [mul_comm (m : ℝ) t]
      have b : (t : ℝ) - 1 / m < (⌊(m : ℝ) * t⌋₊ : ℝ) / m := by
        rw [lt_div_iff₀ hm0, sub_mul, one_div, inv_mul_cancel₀ hm0.ne']
        linarith [mul_comm (m : ℝ) t]
      have : (0 : ℝ) < 1 / m := by positivity
      constructor <;> linarith
    have hg0 : g 0 = 0 := Subtype.ext (by rw [hgv]; simp)
    have hg1 : g 1 = 1 := Subtype.ext (by rw [hgv]; simp [hm0.ne'])
    set Gm : Finset I := (Finset.range (m + 1)).image fun j : ℕ ↦
      projIcc 0 1 zero_le_one ((j : ℝ) / m)
    have hgG (t : I) : g t ∈ Gm := by
      refine Finset.mem_image.2 ⟨⌊(m : ℝ) * t⌋₊, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩
      exact Nat.floor_le_of_le (by have := t.2.2; nlinarith)
    -- the step functions
    let step (Q : Finset I) (w : I → E) (t : I) : E :=
      if h : (Q.filter fun q ↦ q ≤ t).Nonempty then w ((Q.filter fun q ↦ q ≤ t).max' h)
      else w 0
    let ext (v : Gm → N) (q : I) : E := if hq : q ∈ Gm then (v ⟨q, hq⟩ : E) else x₀ 0
    have : Finite N := hNf.to_subtype
    refine ⟨⋃ Q ∈ (Gm.powerset : Set (Finset I)), range fun v : Gm → N ↦ step Q (ext v),
      (Gm.powerset.finite_toSet).biUnion fun Q _ ↦ finite_range _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨R, hR, hRosc⟩ := exists_isSparsePartition_of_cadlagModulus_lt (hKδ x hx)
    set R' := R.filter fun r ↦ r ≠ 0 ∧ r ≠ 1 with hR'
    have hR'R : R' ⊆ R := Finset.filter_subset _ _
    obtain ⟨φ, hφR, -, -, hφs⟩ := exists_orderIso_apply_eq_of_separated_and_slope R' g
      (η := δ / 4) (fun r hr ↦ by
        obtain ⟨hrR, hr0, hr1⟩ := Finset.mem_filter.1 hr
        have d0 := hR.2.2 r hrR 0 hR.1 hr0
        have d1 := hR.2.2 r hrR 1 hR.2.1 hr1
        rw [Subtype.dist_eq, Real.dist_eq, Icc.coe_zero, sub_zero, abs_of_nonneg r.2.1] at d0
        rw [Subtype.dist_eq, Real.dist_eq, Icc.coe_one, abs_of_nonpos (by linarith [r.2.2])]
          at d1
        constructor <;> linarith)
      (fun r hr r' hr' hne ↦ by
        have := hR.2.2 r (hR'R hr) r' (hR'R hr') hne
        linarith)
      (fun r _ ↦ (hdist r).trans hmδ)
    have hφ (r : I) (hr : r ∈ R) : φ r = g r := by
      by_cases h0 : r = 0
      · subst h0; rw [hg0]; exact φ.map_bot
      by_cases h1 : r = 1
      · subst h1; rw [hg1]; exact φ.map_top
      exact hφR r (Finset.mem_filter.2 ⟨hr, h0, h1⟩)
    -- the log-slope norm of `φ`
    set S := 2 * ∑ r ∈ R', dist (g r) r / (2 * (δ / 4)) with hS_def
    have hcard : (R'.card : ℝ) ≤ Cd := by
      exact_mod_cast (Finset.card_le_card hR'R).trans (hR.card_le hδ)
    have hS : S ≤ e := by
      have h1 : S ≤ 2 * (R'.card * (1 / m / (2 * (δ / 4)))) := by
        rw [hS_def]
        gcongr
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun r _ ↦
          div_le_div_of_nonneg_right (hdist r).le (by positivity)
      have h2 : 2 * ((R'.card : ℝ) * (1 / m / (2 * (δ / 4)))) = 4 * R'.card / (m * δ) := by
        field_simp
      rw [div_lt_iff₀ (by positivity)] at hm2
      refine h1.trans (h2.le.trans ?_)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hlog : logSlopeNorm φ.symm ≤ ENNReal.ofReal e := by
      rw [logSlopeNorm_symm]
      exact ((logSlopeNorm_le_ofReal_iff (mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ ↦
        div_nonneg dist_nonneg (by positivity)))).2 hφs).trans
        (ENNReal.ofReal_le_ofReal hS)
    -- the approximating step function
    set Q := R.image g
    have hQ : Q ∈ Gm.powerset :=
      Finset.mem_powerset.2 fun q hq ↦ by
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hq
        exact hgG r
    let v : Gm → N := fun q ↦ cv ⟨x (φ.symm q), hKC x hx _⟩
    refine ⟨step Q (ext v), mem_iUnion₂.2 ⟨Q, hQ, mem_range_self v⟩, ?_⟩
    refine lt_of_le_of_lt (billingsleyEDist_le_of_forall φ.symm hlog fun t ↦ ?_) he
    show edist (step Q (ext v) t) (x (φ.symm t)) ≤ ENNReal.ofReal e
    obtain ⟨F, hFdef⟩ : ∃ F, F = Q.filter fun q ↦ q ≤ t := ⟨_, rfl⟩
    have h0F : (0 : I) ∈ F := by
      rw [hFdef]
      exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨0, hR.1, hg0⟩, nonneg'⟩
    have hF : F.Nonempty := ⟨0, h0F⟩
    have hsubF (q : I) (hq : q ∈ F) : q ∈ Q ∧ q ≤ t := by
      rw [hFdef] at hq
      exact Finset.mem_filter.1 hq
    obtain ⟨hqmQ, hqmt⟩ := hsubF _ (F.max'_mem hF)
    obtain ⟨rm, hrm, hrmq⟩ := Finset.mem_image.1 hqmQ
    have hφrm : φ rm = F.max' hF := (hφ rm hrm).trans hrmq
    have hval : step Q (ext v) t = (cv ⟨x rm, hKC x hx _⟩ : E) := by
      have hG : F.max' hF ∈ Gm := hrmq ▸ hgG rm
      simp only [step, ← hFdef, hF, dite_true, ext, hG, v]
      congr 3
      rw [← hφrm, OrderIso.symm_apply_apply]
    have hrm_le : rm ≤ φ.symm t := by
      rw [OrderIso.le_symm_apply, hφrm]
      exact hqmt
    have hcut : ∀ r ∈ R, r ≤ rm ∨ φ.symm t < r := by
      intro r hr
      by_contra! hcon
      have hrF : φ r ∈ F := by
        rw [hFdef]
        refine Finset.mem_filter.2 ⟨?_, ?_⟩
        · rw [hφ r hr]; exact Finset.mem_image_of_mem g hr
        · rw [← OrderIso.le_symm_apply]; exact hcon.2
      have := F.le_max' _ hrF
      rw [← hφrm] at this
      exact (not_le.2 hcon.1) (φ.le_iff_le.1 this)
    rw [hval, ← hrr]
    calc edist (cv ⟨x rm, hKC x hx _⟩ : E) (x (φ.symm t))
        ≤ edist (cv ⟨x rm, hKC x hx _⟩ : E) (x rm) + edist (x rm) (x (φ.symm t)) :=
          edist_triangle _ _ _
      _ ≤ r + r := by
          refine add_le_add ?_ ((edist_le_cellOscillation hrm_le hcut).trans hRosc.le)
          rw [edist_comm]
          exact (hcv ⟨x rm, hKC x hx _⟩).le
  have hc := htb.closure.isCompact_of_isClosed isClosed_closure
  have := (homeomorphBillingsley (E := E)).isCompact_preimage.2 hc
  rwa [Homeomorph.preimage_closure, Homeomorph.preimage_image] at this

/-- **Billingsley, Theorem 12.3** (sufficiency; Arzelà–Ascoli theorem for `D([0, 1], E)`).
A set `K` of càdlàg functions with values in a totally bounded set `C` and with
`sup_{x ∈ K} w'_x(δ) → 0` as `δ → 0` has compact closure in the Skorokhod `J₁` topology. -/
theorem isCompact_closure_of_cadlagModulus [MetricSpace E] [CompleteSpace E]
    {K : Set (SkorokhodSpace E)} {C : Set E} (hC : TotallyBounded C)
    (hKC : ∀ x ∈ K, ∀ t, x t ∈ C)
    (hK : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, cadlagModulus (⇑x) δ < ε) : IsCompact (closure K) :=
  isCompact_closure_of_cadlagModulus' hC hKC hK

end SkorokhodSpace
