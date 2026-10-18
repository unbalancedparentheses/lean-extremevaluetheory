/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Probability.Independence.Integration

/-!
# Second and fourth moments of sums of independent centered random variables

For independent, centered, bounded real random variables `X 0, X 1, …`,
`E (∑_{i < n} X i) ^ 2 = ∑_{i < n} E (X i) ^ 2` and
`E (∑_{i < n} X i) ^ 4 ≤ ∑_{i < n} E (X i) ^ 4 + 3 (∑_{i < n} E (X i) ^ 2) ^ 2`.
The fourth-moment bound is the input of moment criteria for tightness and maximal inequalities
(e.g. for empirical processes).

## Main statements

* `ProbabilityTheory.integral_sum_range_sq_eq`: the variance of a sum of independent centered
  bounded random variables is the sum of the variances.
* `ProbabilityTheory.integral_sum_range_pow_four_le`: the fourth-moment bound.
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrable_pow_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C)
    (k : ℕ) : Integrable (fun ω ↦ f ω ^ k) P :=
  Integrable.of_bound (C := C ^ k) (hf.pow_const k).aestronglyMeasurable (ae_of_all _ fun ω ↦ by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) k)

variable {X : ℕ → Ω → ℝ} {C : ℝ}

lemma abs_sum_range_le (hC : ∀ i ω, |X i ω| ≤ C) (n : ℕ) (ω : Ω) :
    |∑ i ∈ range n, X i ω| ≤ n * C :=
  (Finset.abs_sum_le_sum_abs _ _).trans <| by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ range n) ↦ hC i ω

lemma measurable_sum_range (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable fun ω ↦ ∑ i ∈ range n, X i ω :=
  Finset.measurable_sum _ fun i _ ↦ hX i

omit [IsProbabilityMeasure P] in
lemma indepFun_sum_range (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (n : ℕ) :
    IndepFun (fun ω ↦ ∑ i ∈ range n, X i ω) (X n) P := by
  have := hind.indepFun_finsetSum_of_notMem hX (s := range n) (i := n) (by simp)
  convert this using 1
  ext ω
  simp

lemma integral_sum_range_eq_zero (hX : ∀ i, Measurable (X i)) (hC : ∀ i ω, |X i ω| ≤ C)
    (h0 : ∀ i, ∫ ω, X i ω ∂P = 0) (n : ℕ) : ∫ ω, ∑ i ∈ range n, X i ω ∂P = 0 := by
  rw [integral_finsetSum _ fun i _ ↦ by simpa using integrable_pow_of_abs_le (hX i) (hC i) 1]
  simp [h0]

/-- The variance of a sum of independent centered bounded random variables is the sum of the
variances. -/
theorem integral_sum_range_sq_eq (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hC : ∀ i ω, |X i ω| ≤ C) (h0 : ∀ i, ∫ ω, X i ω ∂P = 0) (n : ℕ) :
    ∫ ω, (∑ i ∈ range n, X i ω) ^ 2 ∂P = ∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    set S : Ω → ℝ := fun ω ↦ ∑ i ∈ range n, X i ω with hS
    have hSm : Measurable S := measurable_sum_range hX n
    have hSC : ∀ ω, |S ω| ≤ n * C := abs_sum_range_le hC n
    have hind' := indepFun_sum_range hX hind n
    have e : (fun ω ↦ (∑ i ∈ range (n + 1), X i ω) ^ 2) =
        fun ω ↦ (S ω ^ 2 + X n ω ^ 2) + 2 * (S ω * X n ω) := by
      ext ω; simp only [Finset.sum_range_succ, hS]; ring
    have iS2 := integrable_pow_of_abs_le (P := P) hSm hSC 2
    have iX2 := integrable_pow_of_abs_le (P := P) (hX n) (hC n) 2
    have iSX : Integrable (fun ω ↦ S ω * X n ω) P := by
      refine Integrable.of_bound (C := n * C * C) (hSm.mul (hX n)).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hSC ω) (hC n ω) (abs_nonneg _) ((abs_nonneg _).trans (hSC ω))
    rw [e, integral_add (by exact iS2.add iX2) (by exact iSX.const_mul 2), integral_add iS2 iX2,
      integral_const_mul, hind'.integral_fun_mul_eq_mul_integral hSm.aestronglyMeasurable
        (hX n).aestronglyMeasurable, h0 n, mul_zero, mul_zero, add_zero]
    have ih' : ∫ ω, S ω ^ 2 ∂P = ∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P := ih
    rw [ih', Finset.sum_range_succ]

/-- **Fourth moment of a sum of independent centered random variables**:
`E (∑_{i < n} X i) ^ 4 ≤ ∑_{i < n} E (X i) ^ 4 + 3 (∑_{i < n} E (X i) ^ 2) ^ 2`. -/
theorem integral_sum_range_pow_four_le (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hC : ∀ i ω, |X i ω| ≤ C) (h0 : ∀ i, ∫ ω, X i ω ∂P = 0) (n : ℕ) :
    ∫ ω, (∑ i ∈ range n, X i ω) ^ 4 ∂P ≤
      ∑ i ∈ range n, ∫ ω, X i ω ^ 4 ∂P + 3 * (∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    set S : Ω → ℝ := fun ω ↦ ∑ i ∈ range n, X i ω with hS
    have hSm : Measurable S := measurable_sum_range hX n
    have hSC : ∀ ω, |S ω| ≤ n * C := abs_sum_range_le hC n
    have hind' := indepFun_sum_range hX hind n
    have hprod (a b : ℕ) : ∫ ω, S ω ^ a * X n ω ^ b ∂P =
        (∫ ω, S ω ^ a ∂P) * ∫ ω, X n ω ^ b ∂P :=
      (hind'.comp (measurable_id.pow_const a)
        (measurable_id.pow_const b)).integral_fun_mul_eq_mul_integral
        (hSm.pow_const a).aestronglyMeasurable ((hX n).pow_const b).aestronglyMeasurable
    have iprod (a b : ℕ) : Integrable (fun ω ↦ S ω ^ a * X n ω ^ b) P := by
      refine Integrable.of_bound (C := (n * C) ^ a * C ^ b)
        ((hSm.pow_const a).mul ((hX n).pow_const b)).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hSC ω) a)
        (pow_le_pow_left₀ (abs_nonneg _) (hC n ω) b) (by positivity)
        (pow_nonneg ((abs_nonneg _).trans (hSC ω)) a)
    have e : (fun ω ↦ (∑ i ∈ range (n + 1), X i ω) ^ 4) = fun ω ↦
        S ω ^ 4 * X n ω ^ 0 + 4 * (S ω ^ 3 * X n ω ^ 1) + 6 * (S ω ^ 2 * X n ω ^ 2) +
          4 * (S ω ^ 1 * X n ω ^ 3) + S ω ^ 0 * X n ω ^ 4 := by
      ext ω; simp only [Finset.sum_range_succ, hS]; ring
    have j1 : Integrable (fun ω ↦ S ω ^ 4 * X n ω ^ 0) P := iprod 4 0
    have j2 : Integrable (fun ω ↦ S ω ^ 4 * X n ω ^ 0 + 4 * (S ω ^ 3 * X n ω ^ 1)) P :=
      j1.add ((iprod 3 1).const_mul 4)
    have j3 : Integrable (fun ω ↦ S ω ^ 4 * X n ω ^ 0 + 4 * (S ω ^ 3 * X n ω ^ 1) +
        6 * (S ω ^ 2 * X n ω ^ 2)) P := j2.add ((iprod 2 2).const_mul 6)
    have j4 : Integrable (fun ω ↦ S ω ^ 4 * X n ω ^ 0 + 4 * (S ω ^ 3 * X n ω ^ 1) +
        6 * (S ω ^ 2 * X n ω ^ 2) + 4 * (S ω ^ 1 * X n ω ^ 3)) P :=
      j3.add ((iprod 1 3).const_mul 4)
    rw [e, integral_add j4 (iprod 0 4), integral_add j3 ((iprod 1 3).const_mul 4),
      integral_add j2 ((iprod 2 2).const_mul 6), integral_add j1 ((iprod 3 1).const_mul 4),
      integral_const_mul,
      integral_const_mul, integral_const_mul, hprod, hprod, hprod, hprod, hprod]
    have h1 : ∫ ω, X n ω ^ 1 ∂P = 0 := by simpa using h0 n
    have hS1 : ∫ ω, S ω ^ 1 ∂P = 0 := by simpa [hS] using integral_sum_range_eq_zero hX hC h0 n
    have hS2 : ∫ ω, S ω ^ 2 ∂P = ∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P :=
      integral_sum_range_sq_eq hX hind hC h0 n
    have hS4 : ∫ ω, S ω ^ 4 ∂P ≤
        ∑ i ∈ range n, ∫ ω, X i ω ^ 4 ∂P + 3 * (∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P) ^ 2 := ih
    have hX2 : 0 ≤ ∫ ω, X n ω ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg _
    have hV : 0 ≤ ∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P :=
      Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
    simp only [pow_zero, integral_const, probReal_univ, one_smul, h1, hS1, mul_zero, zero_mul,
      add_zero, mul_one, one_mul]
    rw [hS2, Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith [mul_nonneg hV hX2, sq_nonneg (∫ ω, X n ω ^ 2 ∂P)]

end ProbabilityTheory
