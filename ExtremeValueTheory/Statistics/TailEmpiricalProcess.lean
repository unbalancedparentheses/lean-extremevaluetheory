/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.TriangularArrayCLT
import Mathlib.Probability.BrownianMotion.Basic

/-!
# The uniform tail empirical process

Let `U 0, U 1, …` be i.i.d. uniform on `[0, 1]` and let `k = k n` be an intermediate sequence,
`k → ∞`, `k / n → 0`. The **uniform tail empirical process** is
`W_n(t) = √k ((1/k) ∑_{i < n} 1{U_i ≥ 1 - (k/n) t} - t)`, `t ≥ 0`:
it counts the `k t` expected exceedances of the high level `1 - (k/n) t` and centers and scales
the count. (We use the non-strict inequality `U_i ≥ 1 - (k/n) t` so that the paths
`t ↦ W_n(t)` are càdlàg; for every fixed `t` this differs from `U_i > 1 - (k/n) t` only on a
null event.)

We prove that the finite-dimensional distributions of `W_n` converge to those of a standard
Brownian motion ([de Haan–Ferreira, *Extreme Value Theory*, Theorem 2.4.8 / 5.1.4];
[Einmahl 1992]): for every finite set of times `I`, the vector `(W_n(t))_{t ∈ I}` converges in
distribution to the centered Gaussian vector with covariance `min s t`, i.e. to
`ProbabilityTheory.BrownianReal.projectiveFamily I`.

The proof is the Cramér–Wold device together with a central limit theorem for triangular arrays
with uniformly small summands (`ProbabilityTheory.tendsto_charFun_sum_range_of_bounded`): a linear
combination `∑_{t ∈ I} a_t W_n(t)` is the row sum `∑_{i < n} f_n(U_i)` with
`f_n(u) = k^{-1/2} ∑_t a_t (1{u ≥ 1 - (k/n) t} - (k/n) t)`, which is centered, bounded by
`O(k^{-1/2})`, and has `n ∫ f_n ^ 2 = ∑_{s, t} a_s a_t (min s t - (k/n) s t) → ∑ a_s a_t min s t`.

## Main definitions

* `ExtremeValueTheory.tailEmpiricalProcess U n k t ω`: the uniform tail empirical process.

## Main statements

* `ExtremeValueTheory.tendstoInDistribution_tailEmpiricalProcess_fdd`: convergence of the
  finite-dimensional distributions to `BrownianReal.projectiveFamily I`.
* `ExtremeValueTheory.tendstoInDistribution_tailEmpiricalProcess_fdd_of_isPreBrownianReal`: the
  same statement with the limit given by a (pre-)Brownian motion.

## References

* [L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*], Theorems 2.4.8 and 5.1.4
* [J. H. J. Einmahl, *Limit theorems for tail processes with application to intermediate quantile
  estimation*, J. Statist. Plann. Inference 32 (1992)]
* [H. Drees, *On smooth statistical tail functionals*, Scand. J. Statist. 25 (1998)]
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Complex
open scoped ENNReal NNReal Real

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The **uniform tail empirical process**
`W_n(t) = √k ((1/k) ∑_{i < n} 1{U_i ≥ 1 - (k/n) t} - t)`. -/
noncomputable def tailEmpiricalProcess (U : ℕ → Ω → ℝ) (n k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  √k * ((k : ℝ)⁻¹ * ∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator 1 (U i ω) - t)

/-- The uniform law on `[0, 1]`. -/
noncomputable abbrev μU : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure μU := ⟨by simp⟩

lemma measureReal_uniform_Ici {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    μU.real (Set.Ici (1 - x)) = x := by
  have e : Set.Ici (1 - x) ∩ Set.Icc 0 1 = Set.Icc (1 - x) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ici, e, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

lemma integral_uniform_indicator_Ici {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ u, (Set.Ici (1 - x)).indicator (1 : ℝ → ℝ) u ∂μU = x := by
  rw [integral_indicator_one measurableSet_Ici, measureReal_uniform_Ici hx0 hx1]

lemma indicator_Ici_mul_indicator_Ici (x y u : ℝ) :
    (Set.Ici x).indicator (1 : ℝ → ℝ) u * (Set.Ici y).indicator 1 u =
      (Set.Ici (max x y)).indicator 1 u := by
  simp only [Set.indicator, Set.mem_Ici, max_le_iff, Pi.one_apply]
  split_ifs <;> simp_all

/-- The summand of the row sum representing the linear combination `∑_t a_t W_n(t)`. -/
noncomputable def tailSummand {I : Finset ℝ≥0} (a : I → ℝ) (n k : ℕ) (u : ℝ) : ℝ :=
  (√k)⁻¹ * ∑ t : I, a t * ((Set.Ici (1 - k / n * (t : ℝ))).indicator 1 u - k / n * t)

lemma measurable_tailSummand {I : Finset ℝ≥0} (a : I → ℝ) (n k : ℕ) :
    Measurable (tailSummand a n k) := by
  unfold tailSummand
  refine Measurable.const_mul (Finset.measurable_sum _ fun t _ ↦ ?_) _
  exact ((measurable_one.indicator measurableSet_Ici).sub_const _).const_mul _

lemma sqrt_mul_inv_sub_eq {n k : ℕ} (hn : n ≠ 0) (S t : ℝ) :
    √(k : ℝ) * ((k : ℝ)⁻¹ * S - t) = (√(k : ℝ))⁻¹ * (S - n * (k / n * t)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hs : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hk').ne'
  have hsq : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk'.le
  field_simp
  rw [hsq]

lemma sum_mul_tailEmpiricalProcess_eq {I : Finset ℝ≥0} (a : I → ℝ) (U : ℕ → Ω → ℝ) {n : ℕ}
    (hn : n ≠ 0) (k : ℕ) (ω : Ω) :
    ∑ t : I, a t * tailEmpiricalProcess U n k t ω = ∑ i ∈ range n, tailSummand a n k (U i ω) := by
  unfold tailEmpiricalProcess tailSummand
  simp_rw [sqrt_mul_inv_sub_eq hn]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

lemma integrable_uniform_indicator_Ici (x : ℝ) :
    Integrable ((Set.Ici x).indicator (1 : ℝ → ℝ)) μU :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Ici

lemma integral_uniform_indicator_sub_mul {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    ∫ u, ((Set.Ici (1 - x)).indicator 1 u - x) * ((Set.Ici (1 - y)).indicator 1 u - y) ∂μU =
      min x y - x * y := by
  have e : (fun u ↦ ((Set.Ici (1 - x)).indicator (1 : ℝ → ℝ) u - x) *
      ((Set.Ici (1 - y)).indicator 1 u - y)) = fun u ↦
      (Set.Ici (1 - min x y)).indicator 1 u - (y * (Set.Ici (1 - x)).indicator 1 u +
        x * (Set.Ici (1 - y)).indicator 1 u) + x * y := by
    ext u
    have := indicator_Ici_mul_indicator_Ici (1 - x) (1 - y) u
    rw [max_sub_sub_left] at this
    rw [← this]
    ring
  have i0 := integrable_uniform_indicator_Ici (1 - min x y)
  have ix := integrable_uniform_indicator_Ici (1 - x)
  have iy := integrable_uniform_indicator_Ici (1 - y)
  rw [e, integral_add (by exact i0.sub ((ix.const_mul _).add (iy.const_mul _)))
      (integrable_const _),
    integral_sub (by exact i0) (by exact (ix.const_mul _).add (iy.const_mul _)),
    integral_add (by exact ix.const_mul _) (by exact iy.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_uniform_indicator_Ici (le_min hx0 hy0) ((min_le_left _ _).trans hx1),
    integral_uniform_indicator_Ici hx0 hx1, integral_uniform_indicator_Ici hy0 hy1]
  simp only [integral_const, probReal_univ, one_smul]
  ring

lemma integral_tailSummand {I : Finset ℝ≥0} (a : I → ℝ) {n k : ℕ}
    (hp : ∀ t : I, (k : ℝ) / n * t ≤ 1) : ∫ u, tailSummand a n k u ∂μU = 0 := by
  unfold tailSummand
  rw [integral_const_mul, integral_finsetSum _ fun t _ ↦ by
    exact ((integrable_uniform_indicator_Ici _).sub (integrable_const _)).const_mul _]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ ↦ ?_)
  rw [integral_const_mul, integral_sub (integrable_uniform_indicator_Ici _) (integrable_const _),
    integral_uniform_indicator_Ici (by positivity) (hp t)]
  simp

lemma abs_tailSummand_le {I : Finset ℝ≥0} (a : I → ℝ) (n k : ℕ) (u : ℝ) :
    |tailSummand a n k u| ≤ (√(k : ℝ))⁻¹ * ∑ t : I, |a t| * (1 + k / n * t) := by
  unfold tailSummand
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun t _ ↦ ?_)) (by positivity)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
  · by_cases h : u ∈ Set.Ici (1 - k / n * (t : ℝ)) <;> simp [h]
  · rw [abs_of_nonneg (by positivity)]

lemma mul_integral_tailSummand_sq {I : Finset ℝ≥0} (a : I → ℝ) {n k : ℕ} (hn : n ≠ 0)
    (hk : k ≠ 0) (hp : ∀ t : I, (k : ℝ) / n * t ≤ 1) :
    n * ∫ u, tailSummand a n k u ^ 2 ∂μU =
      ∑ t : I, ∑ s : I, a t * a s * (min (t : ℝ) s - k / n * t * s) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hp0 : (0 : ℝ) ≤ k / n := by positivity
  set g : I → ℝ → ℝ := fun t u ↦ (Set.Ici (1 - k / n * (t : ℝ))).indicator 1 u - k / n * t
  have hg (t : I) : Integrable (g t) μU :=
    (integrable_uniform_indicator_Ici _).sub (integrable_const _)
  have hsq (u : ℝ) : tailSummand a n k u ^ 2 =
      (k : ℝ)⁻¹ * ∑ t : I, ∑ s : I, a t * a s * (g t u * g s u) := by
    unfold tailSummand
    rw [mul_pow, inv_pow, Real.sq_sqrt hk'.le, sq, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    ring
  simp_rw [hsq]
  have hint (t s : I) : Integrable (fun u ↦ a t * a s * (g t u * g s u)) μU := by
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (C := (1 + k / n * t) * (1 + k / n * s))
      ((hg t).aestronglyMeasurable.mul (hg s).aestronglyMeasurable) (ae_of_all _ fun u ↦ ?_)
    rw [norm_mul]
    have hb (r : I) : ‖g r u‖ ≤ 1 + k / n * r := by
      simp only [g, Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · by_cases h : u ∈ Set.Ici (1 - k / n * (r : ℝ)) <;> simp [h]
      · rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (hb t) (hb s) (norm_nonneg _) (by positivity)
  rw [integral_const_mul, integral_finsetSum _ fun t _ ↦ integrable_finsetSum _ fun s _ ↦
    hint t s]
  simp_rw [integral_finsetSum _ fun s _ ↦ hint _ s, integral_const_mul]
  rw [← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have := integral_uniform_indicator_sub_mul (x := k / n * t) (y := k / n * s) (by positivity)
    (hp t) (by positivity) (hp s)
  simp only [g]
  rw [this, ← mul_min_of_nonneg _ _ hp0]
  field_simp

end ExtremeValueTheory
