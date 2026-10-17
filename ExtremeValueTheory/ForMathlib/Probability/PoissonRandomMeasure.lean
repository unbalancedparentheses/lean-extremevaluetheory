/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Poisson random measures

Let `ν` be a measure on a measurable space `E`. A *Poisson random measure* with intensity `ν`
is a random measure `N : Ω → Measure E` such that for all pairwise disjoint measurable sets
`A₁, …, Aₙ` of finite `ν`-measure, the counts `N(A₁), …, N(Aₙ)` are independent and `N(Aᵢ)`
is Poisson distributed with mean `ν(Aᵢ)`.

## Main definitions

* `ProbabilityTheory.IsPoissonRandomMeasure N ν P`: the random measure `N` is a Poisson random
  measure with intensity `ν` under `P`.
* `ProbabilityTheory.sumDiracRange n z`: the counting measure `∑_{k < n} δ_{z k}`.
* `ProbabilityTheory.poissonSampleMeasure c μ`: the law of a pair `(K, Z)` where `K` is Poisson
  with mean `c` and `Z` is an independent i.i.d. sequence with law `μ`.

## Main statements

* `ProbabilityTheory.IsPoissonRandomMeasure.hasLaw`: `N(A)` is Poisson distributed with mean
  `ν(A)`.
* `ProbabilityTheory.IsPoissonRandomMeasure.iIndepFun`: counts on disjoint sets are independent.
* `ProbabilityTheory.isPoissonRandomMeasure_sumDiracRange`: the random measure `∑_{k < K} δ_{Z k}`
  is a Poisson random measure with intensity `c • μ`.
* `ProbabilityTheory.integral_exp_neg_integral_sumDiracRange`: the Laplace functional of this
  Poisson random measure, `E exp(-∫ f dN) = exp(-∫ (1 - exp (-f)) dν)`.
* `ProbabilityTheory.exists_isPoissonRandomMeasure`: every finite measure is the intensity of a
  Poisson random measure.
-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- A random measure `N : Ω → Measure E` is a *Poisson random measure* with intensity `ν` under
the measure `P` if it is measurable and for all pairwise disjoint measurable sets
`A 0, …, A (n - 1)` of finite `ν`-measure, the joint law of the counts `N (A i)` is the product of
the Poisson distributions with means `ν (A i)`. -/
structure IsPoissonRandomMeasure (N : Ω → Measure E) (ν : Measure E) (P : Measure Ω) : Prop where
  /-- A Poisson random measure is a measurable map into the space of measures. -/
  measurable : Measurable N
  /-- The joint law of the counts on disjoint sets of finite intensity is a product of Poisson
  distributions. -/
  map_eq_pi : ∀ {n : ℕ} (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) → (∀ i, ν (A i) ≠ ∞) →
    Pairwise (Function.onFun Disjoint A) →
    P.map (fun ω i ↦ N ω (A i)) =
      Measure.pi fun i ↦ (poissonMeasure (ν (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)

namespace IsPoissonRandomMeasure

variable {N : Ω → Measure E} {ν : Measure E} {P : Measure Ω}

/-- The count `N A` of a measurable set is a measurable random variable. -/
lemma measurable_apply (hN : IsPoissonRandomMeasure N ν P) {A : Set E} (hA : MeasurableSet A) :
    Measurable fun ω ↦ N ω A :=
  (Measure.measurable_coe hA).comp hN.measurable

/-- The underlying measure of a Poisson random measure is a probability measure. -/
lemma isProbabilityMeasure (hN : IsPoissonRandomMeasure N ν P) : IsProbabilityMeasure P := by
  have h := hN.map_eq_pi (n := 0) Fin.elim0 (fun i ↦ i.elim0) (fun i ↦ i.elim0)
    (fun i ↦ i.elim0)
  constructor
  have hm : Measurable fun ω (i : Fin 0) ↦ N ω (Fin.elim0 i) := Measurable.of_eval fun (i : Fin 0) ↦ i.elim0
  have := congrArg (fun m ↦ m Set.univ) h
  simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at this
  rw [this, Measure.pi_univ]
  simp

/-- For a set `A` of finite intensity, `N A` is Poisson distributed with mean `ν A`. -/
lemma hasLaw (hN : IsPoissonRandomMeasure N ν P) {A : Set E} (hA : MeasurableSet A)
    (hνA : ν A ≠ ∞) :
    HasLaw (fun ω ↦ N ω A) ((poissonMeasure (ν A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  have := hN.isProbabilityMeasure
  have h := hN.map_eq_pi (n := 1) (fun _ ↦ A) (fun _ ↦ hA) (fun _ ↦ hνA)
    (fun i j hij ↦ absurd (Subsingleton.elim i j) hij)
  refine ⟨(hN.measurable_apply hA).aemeasurable, ?_⟩
  have hm : Measurable fun ω (_ : Fin 1) ↦ N ω A :=
    Measurable.of_eval fun _ ↦ hN.measurable_apply hA
  calc P.map (fun ω ↦ N ω A)
      = (P.map fun ω (_ : Fin 1) ↦ N ω A).map (Function.eval 0) := by
        rw [Measure.map_map (measurable_pi_apply 0) hm]; rfl
    _ = _ := by
        rw [h, Measure.pi_map_eval]
        simp

/-- Counts of a Poisson random measure on pairwise disjoint sets of finite intensity are
independent. -/
lemma iIndepFun (hN : IsPoissonRandomMeasure N ν P) {n : ℕ} {A : Fin n → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hνA : ∀ i, ν (A i) ≠ ∞)
    (hd : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω ↦ N ω (A i)) P := by
  have := hN.isProbabilityMeasure
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hN.measurable_apply (hA i)).aemeasurable,
    hN.map_eq_pi A hA hνA hd]
  congr with i : 1
  exact ((hN.hasLaw (hA i) (hνA i)).map_eq).symm

end IsPoissonRandomMeasure

/-! ### Construction for a finite intensity -/

section Construction

/-- The counting measure `∑_{k < n} δ_{z k}` of the first `n` points of a sequence `z`. -/
noncomputable def sumDiracRange (n : ℕ) (z : ℕ → E) : Measure E :=
  ∑ k ∈ range n, Measure.dirac (z k)

lemma sumDiracRange_apply (n : ℕ) (z : ℕ → E) {A : Set E} (hA : MeasurableSet A) :
    sumDiracRange n z A = ∑ k ∈ range n, A.indicator 1 (z k) := by
  simp [sumDiracRange, Measure.coe_finsetSum, Finset.sum_apply, Measure.dirac_apply' _ hA]

/-- The law of a pair `(K, Z)` where `K` is Poisson distributed with mean `c` and
`Z` is an independent sequence of i.i.d. random variables with law `μ`. -/
noncomputable def poissonSampleMeasure (c : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    Measure (ℕ × (ℕ → E)) :=
  (poissonMeasure c).prod (Measure.infinitePi fun _ : ℕ ↦ μ)

variable {c : ℝ≥0} {μ : Measure E} [IsProbabilityMeasure μ]

instance : IsProbabilityMeasure (poissonSampleMeasure c μ) := by
  unfold poissonSampleMeasure; infer_instance

/-- A function `ω ↦ F ω.1 ω.2` on `ℕ × (ℕ → E)` is measurable as soon as each `F n` is. -/
lemma measurable_of_measurable_nat_prod {β : Type*} {mβ : MeasurableSpace β}
    {F : ℕ → (ℕ → E) → β} (hF : ∀ n, Measurable (F n)) :
    Measurable fun ω : ℕ × (ℕ → E) ↦ F ω.1 ω.2 :=
  measurable_from_prod_countable_right hF

lemma measurable_sumDiracRange :
    Measurable fun ω : ℕ × (ℕ → E) ↦ sumDiracRange ω.1 ω.2 := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [sumDiracRange_apply _ _ hA]
  refine measurable_of_measurable_nat_prod
    (F := fun n z ↦ ∑ k ∈ range n, A.indicator 1 (z k)) fun n ↦ ?_
  exact Finset.measurable_sum _ fun k _ ↦
    (measurable_one.indicator hA).comp (measurable_pi_apply k)

/-- The expectation of `∏_{k < n} g (Z k)` for an i.i.d. sequence `Z` with law `μ`. -/
lemma integral_prod_range_infinitePi {g : E → ℂ} (hg : Measurable g) (n : ℕ) :
    ∫ z, ∏ k ∈ range n, g (z k) ∂(Measure.infinitePi fun _ : ℕ ↦ μ) = (∫ x, g x ∂μ) ^ n := by
  have := integral_restrict_infinitePi (μ := fun _ : ℕ ↦ μ) (s := range n)
    (f := fun y ↦ ∏ k : range n, g (y k)) ?_
  · have hcoe (y : ℕ → E) : ∏ k : range n, g (y k) = ∏ k ∈ range n, g (y k) :=
      Finset.prod_coe_sort (range n) fun k ↦ g (y k)
    simp only [Finset.restrict, hcoe] at this
    rw [this,
      integral_fintype_prod_eq_prod (f := fun _ : range n ↦ g)]
    simp
  · exact (Finset.measurable_prod _ fun k _ ↦ hg.comp (measurable_pi_apply k)).aestronglyMeasurable

/-- Key generating functional computation: if `K` is Poisson with mean `c` and `Z` is an
independent i.i.d. sequence with law `μ`, then for every measurable `g` bounded by `1`,
`E ∏_{k < K} g (Z k) = exp (c (∫ g dμ - 1))`. -/
lemma integral_prod_range_poissonSampleMeasure {g : E → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ 1) :
    ∫ ω, ∏ k ∈ range ω.1, g (ω.2 k) ∂(poissonSampleMeasure c μ) =
      Complex.exp (c * ((∫ x, g x ∂μ) - 1)) := by
  have hmeas : Measurable fun ω : ℕ × (ℕ → E) ↦ ∏ k ∈ range ω.1, g (ω.2 k) :=
    measurable_of_measurable_nat_prod fun n ↦
      Finset.measurable_prod _ fun k _ ↦ hg.comp (measurable_pi_apply k)
  have hint : Integrable (fun ω : ℕ × (ℕ → E) ↦ ∏ k ∈ range ω.1, g (ω.2 k))
      (poissonSampleMeasure c μ) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun ω ↦ ?_)
    exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
      fun k _ ↦ hg1 _)
  rw [poissonSampleMeasure, integral_prod _ hint]
  simp_rw [integral_prod_range_infinitePi hg]
  rw [integral_poissonMeasure]
  set m := ∫ x, g x ∂μ
  calc ∑' n, (Real.exp (-c) * c ^ n / n.factorial : ℝ) • m ^ n
      = ∑' n, (Real.exp (-c) : ℂ) * ((c * m) ^ n / n.factorial) := by
        congr with n
        rw [Complex.real_smul]
        push_cast
        ring
    _ = (Real.exp (-c) : ℂ) * ∑' n, ((c * m) ^ n / n.factorial) := tsum_mul_left
    _ = (Real.exp (-c) : ℂ) * Complex.exp (c * m) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp ((c : ℂ) * m)).tsum_eq, Complex.exp_eq_exp_ℂ]
    _ = Complex.exp (c * (m - 1)) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        push_cast
        ring_nf

omit [MeasurableSpace E] in
/-- Pointwise identity behind the joint characteristic function of the counts on disjoint sets. -/
lemma cexp_sum_indicator_eq {n : ℕ} {A : Fin n → Set E}
    (hd : Pairwise (Function.onFun Disjoint A)) (t : Fin n → ℝ) (z : E) :
    Complex.exp ((∑ i, t i * (A i).indicator 1 z : ℝ) * Complex.I) =
      1 + ∑ i, (A i).indicator (fun _ ↦ Complex.exp (t i * Complex.I) - 1) z := by
  by_cases hz : ∃ j, z ∈ A j
  · obtain ⟨j, hj⟩ := hz
    have hnot : ∀ i, i ≠ j → z ∉ A i := fun i hij hi ↦
      Set.disjoint_left.1 (hd hij) hi hj
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by simp [hnot i hij]) (by simp),
      Finset.sum_eq_single j (fun i _ hij ↦ by simp [hnot i hij]) (by simp)]
    simp [hj]
  · push Not at hz
    simp [hz]

/-- The joint law of the real counts `#{k < K | Z k ∈ A i}` on disjoint sets. -/
lemma map_count_poissonSampleMeasure {n : ℕ} {A : Fin n → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Function.onFun Disjoint A)) :
    (poissonSampleMeasure c μ).map
        (fun ω i ↦ ∑ k ∈ range ω.1, (A i).indicator (1 : E → ℝ) (ω.2 k)) =
      Measure.pi fun i ↦ (poissonMeasure (c * μ.real (A i)).toNNReal).map (Nat.cast : ℕ → ℝ) := by
  set Y : ℕ × (ℕ → E) → (Fin n → ℝ) :=
    fun ω i ↦ ∑ k ∈ range ω.1, (A i).indicator (1 : E → ℝ) (ω.2 k) with hYdef
  have hY : Measurable Y := by
    refine Measurable.of_eval fun i ↦ ?_
    exact measurable_of_measurable_nat_prod
      (F := fun n z ↦ ∑ k ∈ range n, (A i).indicator (1 : E → ℝ) (z k)) fun m ↦
        Finset.measurable_sum _ fun k _ ↦
          (measurable_one.indicator (hA i)).comp (measurable_pi_apply k)
  refine (charFun_eq_pi_iff).1 fun t ↦ ?_
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop),
    integral_map hY.aemeasurable (by fun_prop)]
  set g : E → ℂ := fun z ↦ Complex.exp ((∑ i, t i * (A i).indicator 1 z : ℝ) * Complex.I)
    with hg_def
  have hg : Measurable g := by
    refine (Complex.measurable_exp.comp (Measurable.mul_const ?_ _))
    refine Complex.measurable_ofReal.comp ?_
    exact Finset.measurable_sum _ fun i _ ↦
      (measurable_one.indicator (hA i)).const_mul _
  have hg1 : ∀ z, ‖g z‖ ≤ 1 := fun z ↦ by
    simp only [hg_def, Complex.norm_exp_ofReal_mul_I, le_refl]
  have key (ω : ℕ × (ℕ → E)) : Complex.exp (inner ℝ (WithLp.toLp 2 (Y ω)) t * Complex.I) =
      ∏ k ∈ range ω.1, g (ω.2 k) := by
    rw [hg_def, ← Complex.exp_sum, ← Finset.sum_mul]
    congr 1
    simp only [PiLp.inner_apply, hYdef, Real.inner_apply]
    push_cast
    rw [Finset.sum_comm]
    simp [Finset.mul_sum, mul_comm]
  simp_rw [key]
  rw [integral_prod_range_poissonSampleMeasure hg hg1]
  have hint : ∫ x, g x ∂μ - 1 =
      ∑ i, (μ.real (A i) : ℂ) * (Complex.exp (t i * Complex.I) - 1) := by
    simp_rw [hg_def, cexp_sum_indicator_eq hd]
    rw [integral_add (integrable_const _), integral_finsetSum]
    · simp [integral_indicator_const _ (hA _), mul_comm]
    · intro i _
      exact (integrable_const _).indicator (hA i)
    · exact integrable_finsetSum _ fun i _ ↦ (integrable_const _).indicator (hA i)
  rw [hint, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [charFun_map_cast_poissonMeasure, ← mul_assoc]
  congr 2
  rw [show (((c * μ.real (A i)).toNNReal : ℝ≥0) : ℂ) = ((c * μ.real (A i)).toNNReal : ℝ) from rfl,
    Real.coe_toNNReal _ (by positivity)]
  push_cast
  ring

end Construction

end ProbabilityTheory
