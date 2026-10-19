/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT
import ExtremeValueTheory.StableLaws.LevyContinuity
import ExtremeValueTheory.RegularVariation.KaramataConverse
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverse.CanonicalMeasure

/-!
# Converse GCLT with a given symmetric stable limit

Step 5 of the converse of the generalized central limit theorem (symmetric case) when the
limit is a given symmetric `α`-stable law: the tail `P(|X| > ·)` is regularly varying with index
`-α`. Also the characterization of the possible scaling limits: an additive antitone function is
linear, so a limit of `T(l x) / T(x)` is a power of `l`.

## Main results

* `GCLTConverse.isRegularlyVarying_of_tendsto_isSymmStable`: **Converse of the generalized central
  limit theorem, symmetric case** ([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35]).
* `GCLTConverse.exists_rpow_of_tendsto_div`: **Characterization of the limit.** If `T > 0` is
  nonincreasing and `T(l x) / T(x) → g(l)` with `g(l) > 0` for every `l > 0`, then `g(l) = l ^ ρ`
  for some `ρ ≤ 0`.

This file is part of the proof in `ExtremeValueTheory.StableLaws.GeneralizedCLTConverse`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), §VIII.8 and §XVII.5 [Feller].
* B. V. Gnedenko and A. N. Kolmogorov, *Limit Distributions for Sums of Independent Random
  Variables*, Addison-Wesley (1954), §35 [GK].
* N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge (1987) [BGT].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace GCLTConverse

open Subexp

section Main

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

omit [IsProbabilityMeasure μ] in
theorem nh_const_mul {r : ℝ} (hr : r ≠ 0) (n : ℕ) (u : ℝ) :
    nh μ (fun n => r * a n) n u = nh μ a n (u / r) := by
  simp only [nh, mul_inv]
  congr 3
  field_simp

theorem integral_gfun_pos (P : ProbabilityMeasure ℝ) {x : ℝ} (hx : 0 < x) :
    0 < ∫ y, gfun hx y ∂(P : Measure ℝ) := by
  have hpos : ∀ y, 0 < gfun hx y := fun y => by
    rw [gfun_apply]
    exact div_pos (by positivity) (lt_of_lt_of_le (by positivity) (le_max_right _ _))
  refine (integral_pos_iff_support_of_nonneg (fun y => (hpos y).le)
    ((gfun hx).integrable _)).2 ?_
  have : Function.support (fun y => gfun hx y) = univ :=
    Function.support_eq_univ fun y => (hpos y).ne'
  rw [this, measure_univ]
  exact one_pos

/-- From the converse pipeline to regular variation: if `n T(aₙ x) → K x ^ (-α)` for all
`x > 0`, with `K > 0` and `0 < α < 2`, then the tail is regularly varying with index `-α`,
`U` with index `2 - α`, and `n P(|X| > aₙ) → K (2 - α) / 2`. -/
theorem isRegularlyVarying_of_tendsto_mul_sqRatio (ha : ∀ n, 0 < a n) {K α : ℝ} (hK : 0 < K)
    (hα0 : 0 < α) (hα2 : α < 2)
    (hL : ∀ x, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (K * x ^ (-α)))) :
    IsRegularlyVarying (absTail μ) (-α) ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 (K * ((2 - α) / 2))) := by
  have hL1 : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n)) atTop (𝓝 K) := by
    simpa using hL 1 one_pos
  have hTpos : ∀ x, 0 < x → 0 < sqRatio μ x := by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hL1).1 0 hK).exists
    have h1 : 0 < sqRatio μ (a n) := by
      by_contra hc
      have : sqRatio μ (a n) = 0 := le_antisymm (not_lt.1 hc) (sqRatio_nonneg _)
      rw [this, mul_zero] at hn
      exact lt_irrefl _ hn
    exact fun x hx => sqRatio_pos_of_pos (ha n) h1 hx
  have hT : IsRegularlyVarying (sqRatio μ) (-α) :=
    isRegularlyVarying_of_tendsto_mul_comp sqRatio_antitoneOn hTpos ha hK hL
  have hZ : IsRegularlyVarying (minSqMoment μ) (2 - α) := by
    have := (IsRegularlyVarying.rpow_id 2).mul hT
    rw [← sub_eq_add_neg] at this
    refine this.congr ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqRatio_eq_div hx.ne', Real.rpow_two]
    field_simp
  have hG := isRegularlyVarying_absTail_of_minSqMoment (by linarith) hZ
  rw [show 2 - α - 2 = -α by ring] at hG
  refine ⟨hG, isRegularlyVarying_truncSecondMoment_of_minSqMoment (by linarith) hZ, ?_⟩
  have hatop := tendsto_atTop_of_tendsto_mul_comp (L := fun _ => K) sqRatio_antitoneOn hTpos ha hL1
  have hr := (tendsto_sq_mul_absTail_div_minSqMoment hZ).comp hatop
  refine (hL1.mul hr).congr' ?_
  filter_upwards [hatop.eventually hZ.1] with n hn
  simp only [Function.comp_apply]
  rw [sqRatio_eq_div (ha n).ne']
  have := (ha n).ne'
  field_simp

/-- **Converse of the generalized central limit theorem, symmetric case**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35]). Let `μ` be a symmetric probability law on
`ℝ`, `aₙ > 0`, and suppose the laws of `(X₁ + ⋯ + Xₙ) / aₙ` converge weakly to the symmetric
`α`-stable law `ν` with characteristic function `exp (-c |t| ^ α)`, `0 < α < 2`, `c > 0`.
Then the two-sided tail `P(|X| > x)` is regularly varying with index `-α`, the truncated second
moment `U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α`, and
`n P(|X| > aₙ)` converges to a positive constant. -/
theorem isRegularlyVarying_of_tendsto_isSymmStable (hsymm : μ.map (fun x => -x) = μ)
    (ha : ∀ n, 0 < a n) {α c : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hc : 0 < c)
    {ν : ProbabilityMeasure ℝ} (hν : IsSymmStable α c (ν : Measure ℝ))
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) :
    IsRegularlyVarying (absTail μ) (-α) ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      ∃ K > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 K) := by
  obtain ⟨δ, hδ, hb⟩ := exists_nh_le hsymm hconv
  set B := Real.log 2
  have hB0 : 0 ≤ B := Real.log_nonneg one_le_two
  set h : ℝ → ℝ := fun u => c * |u| ^ α with hh
  have hBa : ∀ᶠ n in atTop, ∀ u, |nh μ a n u| ≤ B * (|u| / δ + 1) ^ 2 := by
    filter_upwards [eventually_ge_atTop 3] with n hn u
    rw [abs_of_nonneg (nh_nonneg _ _)]
    exact hb n hn u
  have hlim : ∀ u, Tendsto (fun n => nh μ a n u) atTop (𝓝 (h u)) := by
    intro u
    have := (tendsto_nh hsymm hconv hb u).2
    rwa [hν.2 u, Complex.ofReal_re, Real.log_exp, neg_neg] at this
  have hhc : Continuous h := continuous_const.mul (continuous_abs.rpow_const fun _ => Or.inr hα0.le)
  have hhb : ∀ u, |h u| ≤ B * (|u| / δ + 1) ^ 2 := by
    intro u
    rw [abs_of_nonneg (by positivity)]
    exact le_of_tendsto (hlim u) (by
      filter_upwards [hBa] with n hn
      exact (le_abs_self _).trans (hn u))
  have hpos : 0 < lap h 0 := lap_pos hB0 hδ hhc hhb (by simp [hh, Real.zero_rpow hα0.ne'])
    (fun u => by positivity) one_pos (by simp [hh, hc])
  obtain ⟨P, hP⟩ := exists_charFun_eq_lap hsymm hB0 hδ hBa hlim hpos hhc hhb
  set L : ℝ → ℝ := fun x => lap h 0 * ∫ y, (1 + y ^ 2) / max (y ^ 2) (x ^ 2) ∂(P : Measure ℝ)
  have hlimL : ∀ x (hx : 0 < x), Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (L x)) := fun x hx => tendsto_mul_sqRatio hsymm ha hB0 hδ hBa hlim hpos P hP hx
  -- scaling: `L (r x) = r ^ (-α) L x`
  have hscale : ∀ r x, 0 < r → 0 < x → L (r * x) = r ^ (-α) * L x := by
    intro r x hr hx
    set h' : ℝ → ℝ := fun u => r ^ (-α) * h u
    have hlap : ∀ t, lap h' t = r ^ (-α) * lap h t := lap_smul _ _
    have hr' : 0 < r ^ (-α) := Real.rpow_pos_of_pos hr _
    have hBa' : ∀ᶠ n in atTop, ∀ u, |nh μ (fun n => r * a n) n u| ≤
        B * (|u| / (r * δ) + 1) ^ 2 := by
      filter_upwards [hBa] with n hn u
      rw [nh_const_mul hr.ne', ← div_div, ← abs_of_pos hr, ← abs_div, abs_of_pos hr]
      exact hn _
    have hlim' : ∀ u, Tendsto (fun n => nh μ (fun n => r * a n) n u) atTop (𝓝 (h' u)) := by
      intro u
      simp_rw [nh_const_mul hr.ne']
      convert hlim (u / r) using 2
      simp only [h', hh]
      rw [abs_div, abs_of_pos hr, Real.div_rpow (abs_nonneg _) hr.le, Real.rpow_neg hr.le]
      field_simp
    have hpos' : 0 < lap h' 0 := by rw [hlap]; exact mul_pos hr' hpos
    have hP' : ∀ t, charFun (P : Measure ℝ) t = ((lap h' t / lap h' 0 : ℝ) : ℂ) := by
      intro t; rw [hP, hlap, hlap, mul_div_mul_left _ _ hr'.ne']
    have h1 := tendsto_mul_sqRatio (a := fun n => r * a n) hsymm (fun n => mul_pos hr (ha n))
      hB0 (mul_pos hr hδ) hBa' hlim' hpos' P hP' hx
    have h2 := hlimL (r * x) (mul_pos hr hx)
    have e : ∀ n, r * a n * x = a n * (r * x) := fun n => by ring
    simp_rw [e] at h1
    rw [hlap] at h1
    have := tendsto_nhds_unique h2 h1
    rw [this, mul_assoc]
    rfl
  have hL1 : 0 < L 1 := mul_pos hpos (integral_gfun_pos P one_pos)
  obtain ⟨hG, hU, hK⟩ := isRegularlyVarying_of_tendsto_mul_sqRatio (μ := μ) ha hL1 hα0 hα2
    (fun x hx => by
      have := hscale x 1 hx one_pos
      rw [mul_one] at this
      rw [← mul_comm (x ^ (-α)), ← this]
      exact hlimL x hx)
  exact ⟨hG, hU, _, mul_pos hL1 (by linarith), hK⟩

end Main

section Characterization

/-- An additive antitone function `ℝ → ℝ` is linear. -/
theorem eq_mul_of_add_of_antitone {φ : ℝ → ℝ} (hadd : ∀ u v, φ (u + v) = φ u + φ v)
    (hanti : Antitone φ) (u : ℝ) : φ u = u * φ 1 := by
  set f : ℝ →+ ℝ := AddMonoidHom.mk' φ hadd
  have hq : ∀ q : ℚ, φ q = q * φ 1 := fun q => by
    have := map_ratCast_smul f ℝ ℝ q 1
    simpa [f] using this
  set c := φ 1
  have h0 : φ 0 = 0 := by have := hadd 0 0; rw [add_zero] at this; linarith
  have hc : c ≤ 0 := h0 ▸ hanti zero_le_one
  have hη : ∀ ε : ℝ, 0 < ε → 0 < ε / (1 - c) := fun ε hε => div_pos hε (by linarith)
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u - ε / (1 - c) < u by linarith [hη ε hε])
    have h1 : φ u ≤ φ q := hanti hq2.le
    rw [hq] at h1
    have h2 : (q : ℝ) * c ≤ (u - ε / (1 - c)) * c := mul_le_mul_of_nonpos_right hq1.le hc
    have h3 : -(ε / (1 - c)) * c ≤ ε := by
      have : ε / (1 - c) * (1 - c) = ε := div_mul_cancel₀ _ (by linarith)
      nlinarith [hη ε hε]
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < u + ε / (1 - c) by linarith [hη ε hε])
    have h1 : φ q ≤ φ u := hanti hq1.le
    rw [hq] at h1
    have h2 : (u + ε / (1 - c)) * c ≤ (q : ℝ) * c := mul_le_mul_of_nonpos_right hq2.le hc
    have h3 : -(ε / (1 - c)) * c ≤ ε := by
      have : ε / (1 - c) * (1 - c) = ε := div_mul_cancel₀ _ (by linarith)
      nlinarith [hη ε hε]
    linarith

/-- **Characterization of the limit.** If `T > 0` is nonincreasing and `T(l x) / T(x) → g(l)`
with `g(l) > 0` for every `l > 0`, then `g(l) = l ^ ρ` for some `ρ ≤ 0`. -/
theorem exists_rpow_of_tendsto_div {T g : ℝ → ℝ} (hT : AntitoneOn T (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < T x) (hg0 : ∀ l, 0 < l → 0 < g l)
    (hg : ∀ l, 0 < l → Tendsto (fun x => T (l * x) / T x) atTop (𝓝 (g l))) :
    ∃ ρ : ℝ, ρ ≤ 0 ∧ ∀ l, 0 < l → g l = l ^ ρ := by
  have hmul : ∀ l m, 0 < l → 0 < m → g (l * m) = g l * g m := by
    intro l m hl hm
    have h1 := ((hg l hl).comp (tendsto_id.const_mul_atTop hm)).mul (hg m hm)
    refine tendsto_nhds_unique (hg (l * m) (mul_pos hl hm)) (h1.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, id]
    have := (hpos _ (mul_pos hm hx)).ne'
    rw [mul_assoc l m x]
    field_simp
  have hmono : ∀ l m, 0 < l → l ≤ m → g m ≤ g l := by
    intro l m hl hlm
    refine le_of_tendsto_of_tendsto (hg m (hl.trans_le hlm)) (hg l hl) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_le_div_of_nonneg_right (hT (mul_pos hl hx) (mul_pos (hl.trans_le hlm) hx)
      (mul_le_mul_of_nonneg_right hlm hx.le)) (hpos x hx).le
  set φ : ℝ → ℝ := fun u => Real.log (g (Real.exp u))
  have hadd : ∀ u v, φ (u + v) = φ u + φ v := by
    intro u v
    simp only [φ, Real.exp_add]
    rw [hmul _ _ (Real.exp_pos _) (Real.exp_pos _),
      Real.log_mul (hg0 _ (Real.exp_pos _)).ne' (hg0 _ (Real.exp_pos _)).ne']
  have hanti : Antitone φ := fun u v huv =>
    Real.log_le_log (hg0 _ (Real.exp_pos _))
      (hmono _ _ (Real.exp_pos _) (Real.exp_le_exp.2 huv))
  refine ⟨φ 1, ?_, fun l hl => ?_⟩
  · have := hanti zero_le_one
    have h0 : φ 0 = 0 := by
      have := hadd 0 0; simp only [add_zero] at this; linarith
    linarith
  · have := eq_mul_of_add_of_antitone hadd hanti (Real.log l)
    simp only [φ, Real.exp_log hl] at this
    rw [Real.rpow_def_of_pos hl, ← this, Real.exp_log (hg0 l hl)]

end Characterization

end GCLTConverse

end ExtremeValueTheory
