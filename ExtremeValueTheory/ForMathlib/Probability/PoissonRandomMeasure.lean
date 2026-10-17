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

universe u

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

/-- The mass that `∑_{k < n} δ_{z k}` gives to a measurable set `A` is the number of indices
`k < n` with `z k ∈ A`. -/
lemma sumDiracRange_apply (n : ℕ) (z : ℕ → E) {A : Set E} (hA : MeasurableSet A) :
    sumDiracRange n z A = ∑ k ∈ range n, A.indicator 1 (z k) := by
  simp [sumDiracRange, Measure.coe_finsetSum, Finset.sum_apply, Measure.dirac_apply' _ hA]

/-- The mass that `∑_{k < n} δ_{z k}` gives to a measurable set, written via a real-valued
count. -/
lemma sumDiracRange_apply_eq_ofReal (n : ℕ) (z : ℕ → E) {A : Set E} (hA : MeasurableSet A) :
    sumDiracRange n z A = ENNReal.ofReal (∑ k ∈ range n, A.indicator (1 : E → ℝ) (z k)) := by
  rw [sumDiracRange_apply _ _ hA, ENNReal.ofReal_sum_of_nonneg
    (f := fun k ↦ A.indicator (1 : E → ℝ) (z k)) fun k _ ↦
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : z k ∈ A <;> simp [hk]

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

/-- The random measure `ω ↦ ∑_{k < ω.1} δ_{ω.2 k}` is measurable. -/
lemma measurable_sumDiracRange :
    Measurable fun ω : ℕ × (ℕ → E) ↦ sumDiracRange ω.1 ω.2 := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [sumDiracRange_apply _ _ hA]
  refine measurable_of_measurable_nat_prod
    (F := fun n z ↦ ∑ k ∈ range n, A.indicator 1 (z k)) fun n ↦ ?_
  exact Finset.measurable_sum _ fun k _ ↦
    (measurable_one.indicator hA).comp (measurable_pi_apply k)

/-- The expectation of `∏_{k < n} g k (Z k)` for a sequence `Z` of independent random variables
with laws `μ k`. -/
lemma integral_prod_range_infinitePi_of_ne {X : ℕ → Type*} [∀ k, MeasurableSpace (X k)]
    {ρ : (k : ℕ) → Measure (X k)} [∀ k, IsProbabilityMeasure (ρ k)] {𝕜 : Type*} [RCLike 𝕜]
    {g : (k : ℕ) → X k → 𝕜} (hg : ∀ k, Measurable (g k)) (n : ℕ) :
    ∫ z, ∏ k ∈ range n, g k (z k) ∂(Measure.infinitePi ρ) = ∏ k ∈ range n, ∫ x, g k x ∂(ρ k) := by
  have := integral_restrict_infinitePi (μ := ρ) (s := range n)
    (f := fun y ↦ ∏ k : range n, g k (y k)) ?_
  · have hcoe (y : (k : ℕ) → X k) : ∏ k : range n, g k (y k) = ∏ k ∈ range n, g k (y k) :=
      Finset.prod_coe_sort (range n) fun k ↦ g k (y k)
    simp only [Finset.restrict, hcoe] at this
    rw [this, integral_fintype_prod_eq_prod (f := fun k : range n ↦ g k)]
    exact Finset.prod_coe_sort (range n) fun k ↦ ∫ x, g k x ∂(ρ k)
  · exact (Finset.measurable_prod (s := univ)
      (f := fun (k : range n) (y : (i : range n) → X i) ↦ g k (y k))
      fun k _ ↦ (hg k).comp (measurable_pi_apply k)).aestronglyMeasurable

/-- The expectation of `∏_{k < n} g (Z k)` for an i.i.d. sequence `Z` with law `μ`. -/
lemma integral_prod_range_infinitePi {𝕜 : Type*} [RCLike 𝕜] {g : E → 𝕜} (hg : Measurable g)
    (n : ℕ) :
    ∫ z, ∏ k ∈ range n, g (z k) ∂(Measure.infinitePi fun _ : ℕ ↦ μ) = (∫ x, g x ∂μ) ^ n := by
  rw [integral_prod_range_infinitePi_of_ne (g := fun _ ↦ g) (fun _ ↦ hg), Finset.prod_const,
    card_range]

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

/-- The mean of the Poisson distribution with parameter `r` is `r`. -/
lemma lintegral_natCast_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure r) = r := by
  have hsum : HasSum (fun n : ℕ ↦ Real.exp (-r) * r ^ n / n.factorial * n) r := by
    refine (hasSum_nat_add_iff' 1).1 ?_
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
    convert (hasSum_one_poissonMeasure r).mul_left (r : ℝ) using 1
    · ext n
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    · ring
  rw [poissonMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hr : (r : ℝ≥0∞) =
      ENNReal.ofReal (∑' n : ℕ, Real.exp (-r) * r ^ n / n.factorial * n) := by
    rw [hsum.tsum_eq, ENNReal.ofReal_coe_nnreal]
  rw [hr, ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum.summable]
  refine tsum_congr fun n ↦ ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

/-- The expected number of points of `∑_{k < K} δ_{Z k}` in a measurable set `A` is
`c * μ A`. -/
lemma lintegral_sumDiracRange_poissonSampleMeasure {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ ω, sumDiracRange ω.1 ω.2 A ∂(poissonSampleMeasure c μ) = c * μ A := by
  have hm : Measurable fun ω : ℕ × (ℕ → E) ↦ sumDiracRange ω.1 ω.2 A :=
    (Measure.measurable_coe hA).comp measurable_sumDiracRange
  rw [poissonSampleMeasure, lintegral_prod _ hm.aemeasurable]
  have hinner (n : ℕ) : ∫⁻ z, sumDiracRange n z A ∂(Measure.infinitePi fun _ : ℕ ↦ μ) =
      n * μ A := by
    simp_rw [sumDiracRange_apply _ _ hA]
    rw [lintegral_finsetSum (f := fun k (z : ℕ → E) ↦ A.indicator 1 (z k)) _ fun k _ ↦
      (measurable_one.indicator hA).comp (measurable_pi_apply k)]
    have hk (k : ℕ) : ∫⁻ z, A.indicator 1 (z k) ∂(Measure.infinitePi fun _ : ℕ ↦ μ) = μ A := by
      rw [(measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) k).lintegral_comp
        (f := A.indicator 1) (measurable_one.indicator hA), lintegral_indicator_one hA]
    simp [hk]
  simp_rw [hinner]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_natCast_poissonMeasure]

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

/-- Joint characteristic function of the counts `#{k < K | Z k ∈ A i}` on disjoint sets. -/
lemma integral_cexp_count_poissonSampleMeasure {n : ℕ} {A : Fin n → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) (t : Fin n → ℝ) :
    ∫ ω, Complex.exp ((∑ i, t i * ∑ k ∈ range ω.1, (A i).indicator (1 : E → ℝ) (ω.2 k) : ℝ) *
        Complex.I) ∂(poissonSampleMeasure c μ) =
      Complex.exp (∑ i, ((c * μ.real (A i) : ℝ) : ℂ) * (Complex.exp (t i * Complex.I) - 1)) := by
  set g : E → ℂ := fun z ↦ Complex.exp ((∑ i, t i * (A i).indicator 1 z : ℝ) * Complex.I)
    with hg_def
  have hg : Measurable g := by
    refine (Complex.measurable_exp.comp (Measurable.mul_const ?_ _))
    refine Complex.measurable_ofReal.comp ?_
    exact Finset.measurable_sum _ fun i _ ↦
      (measurable_one.indicator (hA i)).const_mul _
  have hg1 : ∀ z, ‖g z‖ ≤ 1 := fun z ↦ by
    simp only [hg_def, Complex.norm_exp_ofReal_mul_I, le_refl]
  have key (ω : ℕ × (ℕ → E)) :
      Complex.exp ((∑ i, t i * ∑ k ∈ range ω.1, (A i).indicator (1 : E → ℝ) (ω.2 k) : ℝ) *
        Complex.I) = ∏ k ∈ range ω.1, g (ω.2 k) := by
    rw [hg_def, ← Complex.exp_sum, ← Finset.sum_mul]
    congr 1
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
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
  rw [hint, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring

/-- The characteristic function of a vector of independent Poisson random variables. -/
lemma charFun_pi_poissonMeasure {n : ℕ} (r : Fin n → ℝ≥0) (t : Fin n → ℝ) :
    ∏ i, charFun ((poissonMeasure (r i)).map (Nat.cast : ℕ → ℝ)) (t i) =
      Complex.exp (∑ i, ((r i : ℝ) : ℂ) * (Complex.exp (t i * Complex.I) - 1)) := by
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [charFun_map_cast_poissonMeasure]

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
  have hinner (ω : ℕ × (ℕ → E)) : inner ℝ (WithLp.toLp 2 (Y ω)) t = ∑ i, t i * Y ω i := by
    simp [PiLp.inner_apply]
  simp_rw [hinner, hYdef]
  rw [integral_cexp_count_poissonSampleMeasure hA hd, charFun_pi_poissonMeasure]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.coe_toNNReal _ (by positivity)]

/-- **Existence of Poisson random measures with finite intensity.** If `K` is Poisson
distributed with mean `c` and `Z` is an independent i.i.d. sequence with law `μ`, then
`∑_{k < K} δ_{Z k}` is a Poisson random measure with intensity `c • μ`. -/
theorem isPoissonRandomMeasure_sumDiracRange (c : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsPoissonRandomMeasure (fun ω : ℕ × (ℕ → E) ↦ sumDiracRange ω.1 ω.2) (c • μ)
      (poissonSampleMeasure c μ) where
  measurable := measurable_sumDiracRange
  map_eq_pi := by
    intro n A hA _ hd
    have hY : Measurable fun (ω : ℕ × (ℕ → E)) (i : Fin n) ↦
        ∑ k ∈ range ω.1, (A i).indicator (1 : E → ℝ) (ω.2 k) := by
      refine Measurable.of_eval fun i ↦ ?_
      exact measurable_of_measurable_nat_prod
        (F := fun n z ↦ ∑ k ∈ range n, (A i).indicator (1 : E → ℝ) (z k)) fun m ↦
          Finset.measurable_sum _ fun k _ ↦
            (measurable_one.indicator (hA i)).comp (measurable_pi_apply k)
    have hcount : (fun (ω : ℕ × (ℕ → E)) (i : Fin n) ↦ sumDiracRange ω.1 ω.2 (A i)) =
        (fun (y : Fin n → ℝ) i ↦ ENNReal.ofReal (y i)) ∘
          fun ω i ↦ ∑ k ∈ range ω.1, (A i).indicator (1 : E → ℝ) (ω.2 k) := by
      ext ω i
      exact sumDiracRange_apply_eq_ofReal _ _ (hA i)
    rw [hcount, ← Measure.map_map (by fun_prop) hY, map_count_poissonSampleMeasure hA hd,
      Measure.pi_map_pi (fun i ↦ by fun_prop)]
    congr with i : 1
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : ((c • μ) (A i)).toNNReal = (c * μ.real (A i)).toNNReal := by
      rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
        Real.toNNReal_mul c.coe_nonneg]
      simp [Measure.real]
    rw [this]
    congr 1
    funext m
    simp

/-- The integral of a measurable function against `∑_{k < n} δ_{z k}`. -/
lemma integral_sumDiracRange {f : E → ℝ} (hf : Measurable f) (n : ℕ) (z : ℕ → E) :
    ∫ x, f x ∂(sumDiracRange n z) = ∑ k ∈ range n, f (z k) := by
  rw [sumDiracRange, integral_finsetSum_measure fun k _ ↦
    integrable_dirac' hf.stronglyMeasurable (by simp)]
  exact Finset.sum_congr rfl fun k _ ↦ integral_dirac' _ _ hf.stronglyMeasurable

/-- **Laplace functional** of the Poisson random measure `∑_{k < K} δ_{Z k}` with intensity
`ν = c • μ`: for every measurable `f ≥ 0`, `E exp(-∫ f dN) = exp(-∫ (1 - exp (-f)) dν)`. -/
theorem integral_exp_neg_integral_sumDiracRange {f : E → ℝ} (hf : Measurable f) (hf0 : 0 ≤ f) :
    ∫ ω, Real.exp (-∫ x, f x ∂(sumDiracRange ω.1 ω.2)) ∂(poissonSampleMeasure c μ) =
      Real.exp (-∫ x, (1 - Real.exp (-f x)) ∂(c • μ)) := by
  have hexp : Measurable fun x ↦ Real.exp (-f x) := Real.measurable_exp.comp hf.neg
  have hexp1 : ∀ x, ‖Real.exp (-f x)‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact hf0 x
  have hint : Integrable (fun x ↦ Real.exp (-f x)) μ :=
    Integrable.of_bound hexp.aestronglyMeasurable 1 (Eventually.of_forall hexp1)
  have h1 (ω : ℕ × (ℕ → E)) : Real.exp (-∫ x, f x ∂(sumDiracRange ω.1 ω.2)) =
      ∏ k ∈ range ω.1, Real.exp (-f (ω.2 k)) := by
    rw [integral_sumDiracRange hf, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [h1]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_prod]
  rw [integral_prod_range_poissonSampleMeasure (g := fun x ↦ (Real.exp (-f x) : ℂ))
    (Complex.measurable_ofReal.comp hexp) (fun x ↦ by rw [Complex.norm_real]; exact hexp1 x),
    integral_complex_ofReal, integral_smul_nnreal_measure, integral_sub (integrable_const _) hint]
  simp only [integral_const, probReal_univ, NNReal.smul_def, smul_eq_mul]
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

end Construction

/-! ### Existence for a finite intensity -/

section Existence

/-- The Poisson distribution with mean `0` is the Dirac mass at `0`. -/
lemma poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n ↦ ?_
  rw [poissonMeasure_singleton]
  rcases n with _ | n
  · simp
  · simp [Measure.dirac_apply']

/-- The zero random measure is a Poisson random measure with intensity `0`. -/
lemma isPoissonRandomMeasure_zero {P : Measure Ω} [IsProbabilityMeasure P] :
    IsPoissonRandomMeasure (fun _ : Ω ↦ (0 : Measure E)) 0 P where
  measurable := measurable_const
  map_eq_pi := by
    intro n A _ _ _
    simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.toNNReal_zero, poissonMeasure_zero]
    rw [Measure.map_const, measure_univ, one_smul]
    simp_rw [Measure.map_dirac' (by fun_prop : Measurable (Nat.cast : ℕ → ℝ≥0∞)), Nat.cast_zero]
    rw [← Measure.infinitePi_eq_pi, Measure.infinitePi_dirac]

/-- **Existence of Poisson random measures**: every finite measure is the intensity of a Poisson
random measure, defined on a probability space in the same universe. -/
theorem exists_isPoissonRandomMeasure {E : Type u} [MeasurableSpace E] (ν : Measure E)
    [IsFiniteMeasure ν] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure E),
      IsProbabilityMeasure P ∧ IsPoissonRandomMeasure N ν P := by
  rcases eq_or_ne ν 0 with rfl | hν
  · exact ⟨PUnit, inferInstance, Measure.dirac PUnit.unit, fun _ ↦ 0, inferInstance,
      isPoissonRandomMeasure_zero⟩
  have h0 : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.2 hν
  have htop : ν Set.univ ≠ ∞ := measure_ne_top ν _
  let μ : Measure E := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure μ :=
    ⟨by simp [μ, ENNReal.inv_mul_cancel h0 htop]⟩
  have hcμ : (ν Set.univ).toNNReal • μ = ν := by
    ext A hA
    simp only [μ, Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, ENNReal.coe_toNNReal htop]
    rw [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]
  refine ⟨ℕ × (ℕ → E), inferInstance, poissonSampleMeasure (ν Set.univ).toNNReal μ,
    fun ω ↦ sumDiracRange ω.1 ω.2, inferInstance, ?_⟩
  have h := isPoissonRandomMeasure_sumDiracRange (ν Set.univ).toNNReal μ
  rwa [hcμ] at h

end Existence



end ProbabilityTheory
