/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.PoissonRandomMeasure
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The Laplace functional of a Poisson random measure

If `N` is a Poisson random measure with σ-finite intensity `ν`, then for every measurable
`f : E → [0, ∞]`,

`E exp (-∫ f dN) = exp (-∫ (1 - exp (-f)) dν)`.

To allow arbitrary `f` (for which `∫ f dN` may be infinite), the statement is in `[0, ∞]`, with
`exp (-a)` written `EReal.exp (-(a : EReal))`, so that `exp (-∞) = 0`.

## Main statements

* `ProbabilityTheory.IsPoissonRandomMeasure.lintegral_exp_neg_lintegral_simpleFunc`: the
  Laplace functional on simple functions whose nonzero level sets have finite intensity.
* `ProbabilityTheory.IsPoissonRandomMeasure.lintegral_exp_neg_lintegral`: the Laplace
  functional for all measurable `f ≥ 0`, by approximation from below by simple functions
  supported on sets of finite intensity and monotone convergence.

## References

* [O. Kallenberg, *Random Measures, Theory and Applications*][kallenberg2017]
* [G. Last, M. Penrose, *Lectures on the Poisson Process*][lastpenrose2017]
-/

open MeasureTheory Filter Finset Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- `a ↦ exp (-a)` is continuous on `[0, ∞]` (with `exp (-∞) = 0`). -/
lemma continuous_ereal_exp_neg_coe : Continuous fun a : ℝ≥0∞ ↦ EReal.exp (-(a : EReal)) :=
  ENNReal.continuous_exp.comp (continuous_neg.comp continuous_coe_ennreal_ereal)

/-- `exp (-a) = exp (-a.toReal)` for a finite `a ∈ [0, ∞)`. -/
lemma ereal_exp_neg_coe_of_ne_top {a : ℝ≥0∞} (ha : a ≠ ∞) :
    EReal.exp (-(a : EReal)) = ENNReal.ofReal (Real.exp (-a.toReal)) := by
  rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_neg, EReal.exp_coe]

/-- `exp (-a) ≤ 1` for `a ∈ [0, ∞]`. -/
lemma ereal_exp_neg_coe_le_one (a : ℝ≥0∞) : EReal.exp (-(a : EReal)) ≤ 1 := by
  rw [EReal.exp_le_one_iff, EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg a

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- The integral of `g ∘ s` for a simple function `s`, as a sum over the nonzero values of `s`
indexed by `Fin m`. -/
lemma _root_.MeasureTheory.SimpleFunc.lintegral_comp_eq_sum_fin (s : SimpleFunc E ℝ≥0∞)
    {g : ℝ≥0∞ → ℝ≥0∞} (hg : g 0 = 0) (μ : Measure E) [DecidablePred (· ≠ (0 : ℝ≥0∞))] :
    ∫⁻ x, g (s x) ∂μ = ∑ i, g ((s.range.filter (· ≠ 0)).equivFin.symm i) *
      μ (s ⁻¹' {((s.range.filter (· ≠ 0)).equivFin.symm i : ℝ≥0∞)}) := by
  set R := s.range.filter (· ≠ 0)
  have h1 : ∫⁻ x, g (s x) ∂μ = ∑ c ∈ R, g c * μ (s ⁻¹' {c}) := by
    rw [show (fun x ↦ g (s x)) = ⇑(s.map g) from rfl, SimpleFunc.lintegral_eq_lintegral,
      SimpleFunc.map_lintegral]
    refine (Finset.sum_filter_of_ne fun c _ hc ↦ ?_).symm
    rintro rfl
    simp [hg] at hc
  rw [h1, ← Finset.sum_coe_sort R]
  exact (Equiv.sum_comp R.equivFin.symm fun c : R ↦ g c * μ (s ⁻¹' {(c : ℝ≥0∞)})).symm

namespace IsPoissonRandomMeasure

variable {N : Ω → Measure E} {ν : Measure E} {P : Measure Ω}

/-- The count of a set of finite intensity is almost surely finite. -/
lemma ae_apply_ne_top (hN : IsPoissonRandomMeasure N ν P) {A : Set E} (hA : MeasurableSet A)
    (hνA : ν A ≠ ∞) : ∀ᵐ ω ∂P, N ω A ≠ ∞ := by
  have h := (hN.hasLaw hA hνA).map_eq
  have : ∀ᵐ y ∂(P.map fun ω ↦ N ω A), y ≠ ∞ := by
    rw [h]
    refine (ae_map_iff (p := fun y ↦ y ≠ ∞) (by fun_prop)
      (measurableSet_singleton ∞).compl).2 ?_
    exact ae_of_all _ fun n ↦ ENNReal.natCast_ne_top n
  exact ae_of_ae_map (hN.measurable_apply hA).aemeasurable this

/-- **Laplace functional of a Poisson random measure on simple functions**, in `[0, ∞]`-valued
form: for a simple function `s ≥ 0` with finite values whose nonzero level sets have finite
intensity, `E exp (-∫ s dN) = exp (-∫ (1 - exp (-s)) dν)`. -/
lemma lintegral_exp_neg_lintegral_simpleFunc (hN : IsPoissonRandomMeasure N ν P)
    (s : SimpleFunc E ℝ≥0∞) (hs_top : ∀ x, s x ≠ ∞)
    (hs_fin : ∀ c ∈ s.range, c ≠ 0 → ν (s ⁻¹' {c}) ≠ ∞) :
    ∫⁻ ω, EReal.exp (-(∫⁻ x, s x ∂(N ω) : EReal)) ∂P =
      EReal.exp (-(∫⁻ x, (1 - EReal.exp (-(s x : EReal))) ∂ν : EReal)) := by
  classical
  have := hN.isProbabilityMeasure
  set R := s.range.filter (· ≠ 0) with hR
  set e : Fin R.card ≃ R := R.equivFin.symm with he
  set A : Fin R.card → Set E := fun i ↦ s ⁻¹' {((e i : R) : ℝ≥0∞)} with hAdef
  set a : Fin R.card → ℝ := fun i ↦ ((e i : R) : ℝ≥0∞).toReal with hadef
  have hmem (i : Fin R.card) : ((e i : R) : ℝ≥0∞) ∈ s.range ∧ ((e i : R) : ℝ≥0∞) ≠ 0 :=
    Finset.mem_filter.1 (e i).2
  have hA (i : Fin R.card) : MeasurableSet (A i) := s.measurableSet_fiber _
  have hνA (i : Fin R.card) : ν (A i) ≠ ∞ := hs_fin _ (hmem i).1 (hmem i).2
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hi hj ↦ hij (e.injective (Subtype.ext ?_))
    exact (Set.mem_singleton_iff.1 hi).symm.trans (Set.mem_singleton_iff.1 hj)
  have hval (i : Fin R.card) : ((e i : R) : ℝ≥0∞) = ENNReal.ofReal (a i) := by
    rw [hadef, ENNReal.ofReal_toReal]
    obtain ⟨x, hx⟩ := SimpleFunc.mem_range.1 (hmem i).1
    rw [← hx]
    exact hs_top x
  -- the left-hand side
  have hL : ∀ᵐ ω ∂P, EReal.exp (-(∫⁻ x, s x ∂(N ω) : EReal)) =
      ENNReal.ofReal (Real.exp (-∑ i, a i * (N ω (A i)).toReal)) := by
    have hfin : ∀ᵐ ω ∂P, ∀ i, N ω (A i) ≠ ∞ :=
      ae_all_iff.2 fun i ↦ hN.ae_apply_ne_top (hA i) (hνA i)
    filter_upwards [hfin] with ω hω
    have hsum : ∫⁻ x, s x ∂(N ω) = ENNReal.ofReal (∑ i, a i * (N ω (A i)).toReal) := by
      have hid := SimpleFunc.lintegral_comp_eq_sum_fin s (g := id) rfl (N ω)
      simp only [id] at hid
      rw [hid, ENNReal.ofReal_sum_of_nonneg
        fun i _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hω i), ← hval i]
    rw [hsum, ereal_exp_neg_coe_of_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ ↦
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  have hmeasL : Measurable fun ω ↦ Real.exp (-∑ i, a i * (N ω (A i)).toReal) :=
    Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ ↦
      ((hN.measurable_apply (hA i)).ennreal_toReal.const_mul _)).neg
  rw [lintegral_congr_ae hL, ← ofReal_integral_eq_lintegral_ofReal
    (Integrable.of_bound hmeasL.aestronglyMeasurable 1 (Eventually.of_forall fun ω ↦ ?_))
    (Eventually.of_forall fun ω ↦ (Real.exp_pos _).le), hN.integral_exp_neg_sum hA hνA hd a]
  · -- the right-hand side
    have hφ0 : (1 - EReal.exp (-((0 : ℝ≥0∞) : EReal))) = 0 := by simp
    have hsumR : ∫⁻ x, (1 - EReal.exp (-(s x : EReal))) ∂ν =
        ENNReal.ofReal (∑ i, (ν (A i)).toReal * (1 - Real.exp (-a i))) := by
      rw [SimpleFunc.lintegral_comp_eq_sum_fin s (g := fun c ↦ 1 - EReal.exp (-(c : EReal))) hφ0,
        ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg ENNReal.toReal_nonneg
          (sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ENNReal.toReal_nonneg)))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hνA i), mul_comm,
        ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
      congr 2
      rw [hval i, ereal_exp_neg_coe_of_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    rw [hsumR, ereal_exp_neg_coe_of_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg ENNReal.toReal_nonneg
        (sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ENNReal.toReal_nonneg))))]
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- **Laplace functional of a Poisson random measure.** If `N` is a Poisson random measure with
σ-finite intensity `ν`, then for every measurable `f : E → [0, ∞]`,
`E exp (-∫ f dN) = exp (-∫ (1 - exp (-f)) dν)`, where `exp (-∞) = 0`. -/
theorem lintegral_exp_neg_lintegral (hN : IsPoissonRandomMeasure N ν P) [SigmaFinite ν]
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, EReal.exp (-(∫⁻ x, f x ∂(N ω) : EReal)) ∂P =
      EReal.exp (-(∫⁻ x, (1 - EReal.exp (-(f x : EReal))) ∂ν : EReal)) := by
  have := hN.isProbabilityMeasure
  set S := spanningSets ν with hS
  set s : ℕ → SimpleFunc E ℝ≥0∞ := fun k ↦ (SimpleFunc.eapprox f k).restrict (S k) with hsdef
  have hs_apply (k : ℕ) (x : E) : s k x = (S k).indicator (SimpleFunc.eapprox f k) x :=
    SimpleFunc.restrict_apply _ (measurableSet_spanningSets ν k) x
  have hmono (x : E) : Monotone fun k ↦ s k x := by
    intro k l hkl
    simp only [hs_apply]
    by_cases hx : x ∈ S k
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (monotone_spanningSets ν hkl hx)]
      exact SimpleFunc.monotone_eapprox f hkl x
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have htend (x : E) : Tendsto (fun k ↦ s k x) atTop (𝓝 (f x)) := by
    refine (SimpleFunc.tendsto_eapprox hf x).congr' ?_
    filter_upwards [eventually_ge_atTop (spanningSetsIndex ν x)] with k hk
    rw [hs_apply, Set.indicator_of_mem (mem_spanningSets_of_index_le ν x hk)]
  have hs_top (k : ℕ) (x : E) : s k x ≠ ∞ := by
    rw [hs_apply]
    by_cases hx : x ∈ S k
    · rw [Set.indicator_of_mem hx]
      exact (SimpleFunc.eapprox_lt_top f k x).ne
    · rw [Set.indicator_of_notMem hx]
      exact ENNReal.zero_ne_top
  have hs_fin (k : ℕ) (c : ℝ≥0∞) (_ : c ∈ (s k).range) (hc : c ≠ 0) :
      ν (s k ⁻¹' {c}) ≠ ∞ := by
    refine ((measure_mono fun x hx ↦ ?_).trans_lt (measure_spanningSets_lt_top ν k)).ne
    by_contra hxS
    have : s k x = c := hx
    rw [hs_apply, Set.indicator_of_notMem hxS] at this
    exact hc this.symm
  have hk (k : ℕ) := hN.lintegral_exp_neg_lintegral_simpleFunc (s k) (hs_top k) (hs_fin k)
  -- convergence of the left-hand sides
  have hL : Tendsto (fun k ↦ ∫⁻ ω, EReal.exp (-(∫⁻ x, s k x ∂(N ω) : EReal)) ∂P) atTop
      (𝓝 (∫⁻ ω, EReal.exp (-(∫⁻ x, f x ∂(N ω) : EReal)) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ 1) (fun k ↦ ?_)
      (fun k ↦ ae_of_all _ fun ω ↦ ereal_exp_neg_coe_le_one _) (by simp)
      (ae_of_all _ fun ω ↦ ?_)
    · exact continuous_ereal_exp_neg_coe.measurable.comp
        ((Measure.measurable_lintegral (s k).measurable).comp hN.measurable)
    · exact (continuous_ereal_exp_neg_coe.tendsto _).comp
        (lintegral_tendsto_of_tendsto_of_monotone (fun k ↦ (s k).measurable.aemeasurable)
          (ae_of_all _ hmono) (ae_of_all _ htend))
  -- convergence of the right-hand sides
  have hφ : Continuous fun a : ℝ≥0∞ ↦ 1 - EReal.exp (-(a : EReal)) :=
    (ENNReal.continuous_sub_left ENNReal.one_ne_top).comp continuous_ereal_exp_neg_coe
  have hφmono : Monotone fun a : ℝ≥0∞ ↦ 1 - EReal.exp (-(a : EReal)) := by
    intro a b hab
    refine tsub_le_tsub_left (EReal.exp_monotone ?_) 1
    exact EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 hab)
  have hR : Tendsto (fun k ↦ EReal.exp (-(∫⁻ x, (1 - EReal.exp (-(s k x : EReal))) ∂ν : EReal)))
      atTop (𝓝 (EReal.exp (-(∫⁻ x, (1 - EReal.exp (-(f x : EReal))) ∂ν : EReal)))) := by
    refine (continuous_ereal_exp_neg_coe.tendsto _).comp
      (lintegral_tendsto_of_tendsto_of_monotone (fun k ↦ ?_)
        (ae_of_all _ fun x ↦ hφmono.comp (hmono x))
        (ae_of_all _ fun x ↦ (hφ.tendsto _).comp (htend x)))
    exact (hφ.measurable.comp (s k).measurable).aemeasurable
  simp_rw [hk] at hL
  exact tendsto_nhds_unique hL hR

end IsPoissonRandomMeasure

end ProbabilityTheory
