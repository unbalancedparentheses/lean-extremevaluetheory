/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.GiryMonad

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
* `ProbabilityTheory.poissonSampleSeqMeasure c μ`: the law of a sequence of independent such
  pairs `(K n, Z n)` with parameters `c n` and `μ n`.

## Main statements

* `ProbabilityTheory.IsPoissonRandomMeasure.hasLaw`: `N(A)` is Poisson distributed with mean
  `ν(A)`.
* `ProbabilityTheory.IsPoissonRandomMeasure.iIndepFun`: counts on disjoint sets are independent.
* `ProbabilityTheory.IsPoissonRandomMeasure.integral_exp_neg_sum`: the Laplace functional of a
  Poisson random measure evaluated at simple functions.
* `ProbabilityTheory.IsPoissonRandomMeasure.of_map_eq_pi`: for a σ-finite intensity, the
  condition that sets of infinite intensity have a.s. infinite count follows from the others.
* `ProbabilityTheory.isPoissonRandomMeasure_sumDiracRange`: the random measure `∑_{k < K} δ_{Z k}`
  is a Poisson random measure with intensity `c • μ`.
* `ProbabilityTheory.integral_exp_neg_integral_sumDiracRange`: the Laplace functional of this
  Poisson random measure, `E exp(-∫ f dN) = exp(-∫ (1 - exp (-f)) dν)`.
* `ProbabilityTheory.isPoissonRandomMeasure_sum_sumDiracRange`: superposition, the random measure
  `∑ₙ ∑_{k < K n} δ_{Z n k}` is a Poisson random measure with intensity `∑ₙ c n • μ n`.
* `ProbabilityTheory.exists_isPoissonRandomMeasure`: every s-finite (in particular every
  σ-finite) measure is the intensity of a Poisson random measure.

## Implementation notes

The defining property `IsPoissonRandomMeasure.map_eq_pi` packages the Poisson marginals and the
independence of counts on disjoint sets into the single statement that the joint law of the
counts is a product of Poisson distributions. The extra field `IsPoissonRandomMeasure.ae_eq_top`
asks that sets of infinite intensity have almost surely infinite count; it is needed for intensities
that are s-finite but not σ-finite, and is proved for the superposition construction by comparing
with the partial superpositions, whose Laplace transforms tend to `0`. The joint laws are identified
through characteristic functions (`charFun_eq_pi_iff`), and the countable superposition by dominated
convergence of the characteristic functions of the partial sums.

## References

* [O. Kallenberg, *Random Measures, Theory and Applications*][kallenberg2017]
* [G. Last, M. Penrose, *Lectures on the Poisson Process*][lastpenrose2017]
* [S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*][resnick1987]
-/

@[expose] public section

universe u

open MeasureTheory Filter Finset Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- A random measure `N : Ω → Measure E` is a *Poisson random measure* with intensity `ν` under
the measure `P` if it is measurable, for all pairwise disjoint measurable sets
`A 0, …, A (n - 1)` of finite `ν`-measure the joint law of the counts `N (A i)` is the product of
the Poisson distributions with means `ν (A i)`, and every measurable set of infinite intensity
almost surely has infinite count.

The last condition is automatic when `ν` is σ-finite (`IsPoissonRandomMeasure.of_map_eq_pi`), but
not for general (for instance s-finite) intensities: without it the zero random measure would be a
Poisson random measure with intensity `∞ • Measure.dirac x`. -/
structure IsPoissonRandomMeasure (N : Ω → Measure E) (ν : Measure E) (P : Measure Ω) : Prop where
  /-- A Poisson random measure is a measurable map into the space of measures. -/
  measurable : Measurable N
  /-- The joint law of the counts on disjoint sets of finite intensity is a product of Poisson
  distributions. -/
  map_eq_pi : ∀ {n : ℕ} (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) → (∀ i, ν (A i) ≠ ∞) →
    Pairwise (Function.onFun Disjoint A) →
    P.map (fun ω i ↦ N ω (A i)) =
      Measure.pi fun i ↦ (poissonMeasure (ν (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)
  /-- A measurable set of infinite intensity almost surely contains infinitely many points. -/
  ae_eq_top : ∀ {A : Set E}, MeasurableSet A → ν A = ∞ → ∀ᵐ ω ∂P, N ω A = ∞

/-! ### Consequences of the product-law condition

The following auxiliary statements only use the measurability of `N` and the product-law
condition `IsPoissonRandomMeasure.map_eq_pi`; they are used to show that for a σ-finite intensity
the condition `IsPoissonRandomMeasure.ae_eq_top` follows from the other two. -/

section MapEqPi

variable {N : Ω → Measure E} {ν : Measure E} {P : Measure Ω}

lemma isProbabilityMeasure_of_map_eq_pi
    (hmap : ∀ {n : ℕ} (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) → (∀ i, ν (A i) ≠ ∞) →
      Pairwise (Function.onFun Disjoint A) →
      P.map (fun ω i ↦ N ω (A i)) =
        Measure.pi fun i ↦ (poissonMeasure (ν (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) :
    IsProbabilityMeasure P := by
  have h := hmap (n := 0) Fin.elim0 (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)
  constructor
  have hm : Measurable fun ω (i : Fin 0) ↦ N ω (Fin.elim0 i) :=
    Measurable.of_eval fun (i : Fin 0) ↦ i.elim0
  have := congrArg (fun m ↦ m Set.univ) h
  simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at this
  rw [this, Measure.pi_univ]
  simp

lemma integral_exp_neg_sum_of_map_eq_pi (hmeas : Measurable N)
    (hmap : ∀ {n : ℕ} (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) → (∀ i, ν (A i) ≠ ∞) →
      Pairwise (Function.onFun Disjoint A) →
      P.map (fun ω i ↦ N ω (A i)) =
        Measure.pi fun i ↦ (poissonMeasure (ν (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞))
    {n : ℕ} {A : Fin n → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hνA : ∀ i, ν (A i) ≠ ∞)
    (hd : Pairwise (Function.onFun Disjoint A)) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (-∑ i, a i * (N ω (A i)).toReal) ∂P =
      Real.exp (-∑ i, (ν (A i)).toReal * (1 - Real.exp (-a i))) := by
  have hm : Measurable fun ω (i : Fin n) ↦ N ω (A i) :=
    Measurable.of_eval fun i ↦ (Measure.measurable_coe (hA i)).comp hmeas
  have h := integral_map (μ := P) hm.aemeasurable
    (f := fun x : Fin n → ℝ≥0∞ ↦ ∏ i, Real.exp (-(a i * (x i).toReal)))
    (Finset.measurable_prod _ fun i _ ↦ Real.measurable_exp.comp
      (((measurable_pi_apply i).ennreal_toReal.const_mul (a i)).neg)).aestronglyMeasurable
  simp only at h
  simp_rw [← Finset.sum_neg_distrib, Real.exp_sum, ← h, hmap A hA hνA hd,
    integral_fintype_prod_eq_prod (f := fun i (x : ℝ≥0∞) ↦ Real.exp (-(a i * x.toReal)))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [integral_map (by fun_prop) (by fun_prop), integral_poissonMeasure]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
  set r : ℝ≥0 := (ν (A i)).toNNReal
  have hr : (ν (A i)).toReal = r := rfl
  rw [hr]
  calc ∑' k : ℕ, Real.exp (-r) * r ^ k / k.factorial * Real.exp (-(a i * k))
      = ∑' k : ℕ, Real.exp (-r) * ((r * Real.exp (-a i)) ^ k / k.factorial) := by
        congr with k
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf
    _ = Real.exp (-r) * Real.exp (r * Real.exp (-a i)) := by
        rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp (r * Real.exp (-a i))).tsum_eq,
          Real.exp_eq_exp_ℝ]
    _ = Real.exp (-(r * (1 - Real.exp (-a i)))) := by
        rw [← Real.exp_add]
        ring_nf

lemma integral_exp_neg_apply_of_map_eq_pi (hmeas : Measurable N)
    (hmap : ∀ {n : ℕ} (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) → (∀ i, ν (A i) ≠ ∞) →
      Pairwise (Function.onFun Disjoint A) →
      P.map (fun ω i ↦ N ω (A i)) =
        Measure.pi fun i ↦ (poissonMeasure (ν (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞))
    {A : Set E} (hA : MeasurableSet A) (hνA : ν A ≠ ∞) :
    ∫ ω, Real.exp (-(N ω A).toReal) ∂P = Real.exp (-((ν A).toReal * (1 - Real.exp (-1)))) := by
  have := integral_exp_neg_sum_of_map_eq_pi hmeas hmap (n := 1) (A := fun _ ↦ A) (fun _ ↦ hA)
    (fun _ ↦ hνA) (fun i j hij ↦ absurd (Subsingleton.elim i j) hij) (fun _ ↦ 1)
  simpa using this

end MapEqPi

/-- If random variables `Y M ≤ X` satisfy `E exp (-Y M) → 0`, then `X = ∞` almost surely. -/
lemma ae_eq_top_of_tendsto_integral_exp_neg {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ≥0∞} {Y : ℕ → Ω → ℝ≥0∞} (hY : ∀ M, Measurable (Y M))
    (hle : ∀ M, ∀ᵐ ω ∂P, Y M ω ≤ X ω)
    (h : Tendsto (fun M ↦ ∫ ω, Real.exp (-(Y M ω).toReal) ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, X ω = ∞ := by
  have hj (j : ℕ) : P {ω | X ω ≤ j} = 0 := by
    have hbound (M : ℕ) : P.real {ω | X ω ≤ j} ≤
        Real.exp j * ∫ ω, Real.exp (-(Y M ω).toReal) ∂P := by
      have hint : Integrable (fun ω ↦ Real.exp (-(Y M ω).toReal)) P := by
        refine Integrable.of_bound ((hY M).ennreal_toReal.neg.exp).aestronglyMeasurable 1
          (Eventually.of_forall fun ω ↦ ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
        exact ENNReal.toReal_nonneg
      have hmarkov := mul_meas_ge_le_integral_of_nonneg
        (Eventually.of_forall fun ω ↦ (Real.exp_pos _).le) hint (Real.exp (-j))
      have hsub : P.real {ω | X ω ≤ j} ≤
          P.real {ω | Real.exp (-j) ≤ Real.exp (-(Y M ω).toReal)} := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
        filter_upwards [hle M] with ω hω hX
        have hYj : Y M ω ≤ j := hω.trans hX
        have hYj' : (Y M ω).toReal ≤ j := by
          simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top j) hYj
        exact Real.exp_le_exp.2 (by linarith)
      calc P.real {ω | X ω ≤ j}
          ≤ P.real {ω | Real.exp (-j) ≤ Real.exp (-(Y M ω).toReal)} := hsub
        _ = Real.exp j * (Real.exp (-j) *
            P.real {ω | Real.exp (-j) ≤ Real.exp (-(Y M ω).toReal)}) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le
    have hlim := h.const_mul (Real.exp j)
    rw [mul_zero] at hlim
    have h0 : P.real {ω | X ω ≤ j} ≤ 0 := ge_of_tendsto' hlim hbound
    exact (measureReal_eq_zero_iff).1 (le_antisymm h0 measureReal_nonneg)
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∉ {ω | X ω ≤ j} :=
    ae_all_iff.2 fun j ↦ measure_eq_zero_iff_ae_notMem.1 (hj j)
  filter_upwards [hall] with ω hω
  by_contra hne
  obtain ⟨j, hj⟩ := ENNReal.exists_nat_gt hne
  exact hω j hj.le

/-- If `r M` are finite and tend to `∞`, then `exp (-(r M * a)) → 0` for `a > 0`. -/
lemma tendsto_exp_neg_toReal_mul {r : ℕ → ℝ≥0∞} (hr : ∀ M, r M ≠ ∞)
    (hrt : Tendsto r atTop (𝓝 ∞)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun M ↦ Real.exp (-((r M).toReal * a))) atTop (𝓝 0) := by
  have htop : Tendsto (fun M ↦ (r M).toReal) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    filter_upwards [ENNReal.tendsto_nhds_top_iff_nnreal.1 hrt b.toNNReal] with M hM
    have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hr M)).2 hM
    rw [ENNReal.coe_toReal] at this
    exact (Real.le_coe_toNNReal b).trans this.le
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (htop.atTop_mul_const ha))

namespace IsPoissonRandomMeasure

variable {N : Ω → Measure E} {ν : Measure E} {P : Measure Ω}

/-- The count `N A` of a measurable set is a measurable random variable. -/
lemma measurable_apply (hN : IsPoissonRandomMeasure N ν P) {A : Set E} (hA : MeasurableSet A) :
    Measurable fun ω ↦ N ω A :=
  (Measure.measurable_coe hA).comp hN.measurable

/-- The underlying measure of a Poisson random measure is a probability measure. -/
lemma isProbabilityMeasure (hN : IsPoissonRandomMeasure N ν P) : IsProbabilityMeasure P :=
  isProbabilityMeasure_of_map_eq_pi hN.map_eq_pi

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

/-- **Laplace functional of a Poisson random measure on simple functions.** For pairwise
disjoint measurable sets `A i` of finite intensity and `a i ≥ 0`,
`E exp (-∑ i, a i * N (A i)) = exp (-∑ i, ν (A i) * (1 - exp (-a i)))`. -/
lemma integral_exp_neg_sum (hN : IsPoissonRandomMeasure N ν P) {n : ℕ} {A : Fin n → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hνA : ∀ i, ν (A i) ≠ ∞)
    (hd : Pairwise (Function.onFun Disjoint A)) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (-∑ i, a i * (N ω (A i)).toReal) ∂P =
      Real.exp (-∑ i, (ν (A i)).toReal * (1 - Real.exp (-a i))) :=
  integral_exp_neg_sum_of_map_eq_pi hN.measurable hN.map_eq_pi hA hνA hd a

/-- **Laplace transform of a count.** For a measurable set `A` of finite intensity,
`E exp (-N A) = exp (-ν A * (1 - exp (-1)))`. -/
lemma integral_exp_neg_apply (hN : IsPoissonRandomMeasure N ν P) {A : Set E}
    (hA : MeasurableSet A) (hνA : ν A ≠ ∞) :
    ∫ ω, Real.exp (-(N ω A).toReal) ∂P = Real.exp (-((ν A).toReal * (1 - Real.exp (-1)))) :=
  integral_exp_neg_apply_of_map_eq_pi hN.measurable hN.map_eq_pi hA hνA

/-- **For a σ-finite intensity, the infinite-count condition is automatic.** A measurable random
measure whose counts on disjoint sets of finite intensity have the product Poisson law is a Poisson
random measure, provided the intensity is σ-finite: a set `A` of infinite intensity is exhausted by
the sets `A ∩ spanningSets ν M` of finite intensity, whose counts are Poisson with means tending
to `∞`. -/
theorem of_map_eq_pi [SigmaFinite ν] (hmeas : Measurable N)
    (hmap : ∀ {n : ℕ} (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) → (∀ i, ν (A i) ≠ ∞) →
      Pairwise (Function.onFun Disjoint A) →
      P.map (fun ω i ↦ N ω (A i)) =
        Measure.pi fun i ↦ (poissonMeasure (ν (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) :
    IsPoissonRandomMeasure N ν P where
  measurable := hmeas
  map_eq_pi := hmap
  ae_eq_top := by
    intro A hA hνA
    have := isProbabilityMeasure_of_map_eq_pi hmap
    have hB (M : ℕ) : MeasurableSet (A ∩ spanningSets ν M) :=
      hA.inter (measurableSet_spanningSets ν M)
    have hνB (M : ℕ) : ν (A ∩ spanningSets ν M) ≠ ∞ :=
      ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top ν M)).ne
    refine ae_eq_top_of_tendsto_integral_exp_neg (X := fun ω ↦ N ω A)
      (Y := fun M ω ↦ N ω (A ∩ spanningSets ν M))
      (fun M ↦ (Measure.measurable_coe (hB M)).comp hmeas)
      (fun M ↦ ae_of_all _ fun ω ↦ measure_mono Set.inter_subset_left) ?_
    simp_rw [integral_exp_neg_apply_of_map_eq_pi hmeas hmap (hB _) (hνB _)]
    refine tendsto_exp_neg_toReal_mul hνB ?_ (a := 1 - Real.exp (-1))
      (sub_pos.2 (Real.exp_lt_one_iff.2 (by norm_num)))
    have h := tendsto_measure_iUnion_atTop (μ := ν) (s := fun M ↦ A ∩ spanningSets ν M)
      fun i j hij ↦ Set.inter_subset_inter_right _ (monotone_spanningSets ν hij)
    rwa [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ, hνA] at h

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
noncomputable def poissonSampleMeasure (c : ℝ≥0) (μ : Measure E) :
    Measure (ℕ × (ℕ → E)) :=
  (poissonMeasure c).prod (Measure.infinitePi fun _ : ℕ ↦ μ)

variable {c : ℝ≥0} {μ : Measure E} [IsProbabilityMeasure μ]

instance : IsProbabilityMeasure (poissonSampleMeasure c μ) := by
  unfold poissonSampleMeasure; infer_instance

/-- A function `ω ↦ F ω.1 ω.2` on `ℕ × (ℕ → E)` is measurable as soon as each `F n` is.
(A specialization of `measurable_from_prod_countable_right` which elaborates better.) -/
private lemma measurable_of_measurable_nat_prod {β : Type*} {mβ : MeasurableSpace β}
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
  ae_eq_top := fun _ hνA ↦ absurd hνA (by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))

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

/-! ### Superposition: construction for an s-finite intensity -/

section Superposition

/-- The law of a sequence of independent pairs `(K n, Z n)`, where `K n` is Poisson distributed
with mean `c n` and `Z n` is an independent i.i.d. sequence with law `μ n`. -/
noncomputable def poissonSampleSeqMeasure (c : ℕ → ℝ≥0) (μ : ℕ → Measure E) :
    Measure (ℕ → ℕ × (ℕ → E)) :=
  Measure.infinitePi fun n ↦ poissonSampleMeasure (c n) (μ n)

variable {c : ℕ → ℝ≥0} {μ : ℕ → Measure E} [∀ n, IsProbabilityMeasure (μ n)]

instance : IsProbabilityMeasure (poissonSampleSeqMeasure c μ) := by
  unfold poissonSampleSeqMeasure; infer_instance

/-- The superposition `∑ₙ ∑_{k < Kₙ} δ_{Zₙ k}` is a measurable random measure. -/
lemma measurable_sum_sumDiracRange :
    Measurable fun ω : ℕ → ℕ × (ℕ → E) ↦ Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2 := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [Measure.sum_apply _ hA]
  exact Measurable.tsum fun n ↦
    ((Measure.measurable_coe hA).comp measurable_sumDiracRange).comp (measurable_pi_apply n)

/-- Joint characteristic function of the counts of the first `M` copies on disjoint sets. -/
lemma integral_cexp_count_poissonSampleSeqMeasure {m : ℕ} {A : Fin m → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) (t : Fin m → ℝ)
    (M : ℕ) :
    ∫ ω, Complex.exp ((∑ i, t i * ∑ n ∈ range M,
        ∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k) : ℝ) * Complex.I)
        ∂(poissonSampleSeqMeasure c μ) =
      Complex.exp (∑ i, ((∑ n ∈ range M, c n * (μ n).real (A i) : ℝ) : ℂ) *
        (Complex.exp (t i * Complex.I) - 1)) := by
  set G : ℕ → ℕ × (ℕ → E) → ℂ := fun n x ↦
    Complex.exp ((∑ i, t i * ∑ k ∈ range x.1, (A i).indicator (1 : E → ℝ) (x.2 k) : ℝ) *
      Complex.I) with hG
  have hGm (n : ℕ) : Measurable (G n) := by
    refine Complex.measurable_exp.comp (Measurable.mul_const ?_ _)
    refine Complex.measurable_ofReal.comp ?_
    refine Finset.measurable_sum _ fun i _ ↦ Measurable.const_mul ?_ _
    exact measurable_of_measurable_nat_prod
      (F := fun n z ↦ ∑ k ∈ range n, (A i).indicator (1 : E → ℝ) (z k)) fun m ↦
        Finset.measurable_sum _ fun k _ ↦
          (measurable_one.indicator (hA i)).comp (measurable_pi_apply k)
  have key (ω : ℕ → ℕ × (ℕ → E)) :
      Complex.exp ((∑ i, t i * ∑ n ∈ range M,
        ∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k) : ℝ) * Complex.I) =
      ∏ n ∈ range M, G n (ω n) := by
    rw [hG, ← Complex.exp_sum, ← Finset.sum_mul]
    congr 1
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [key]
  rw [poissonSampleSeqMeasure, integral_prod_range_infinitePi_of_ne hGm]
  simp_rw [hG, integral_cexp_count_poissonSampleMeasure hA hd t, ← Complex.exp_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_mul]
  push_cast
  rfl

/-- In the superposition `∑ₙ ∑_{k < K n} δ_{Z n k}`, a set of infinite intensity
`∑ₙ c n • μ n` almost surely contains infinitely many points: the partial counts are independent
Poisson variables whose means have divergent sum. -/
lemma ae_sum_sumDiracRange_eq_top {A : Set E} (hA : MeasurableSet A)
    (hνA : (Measure.sum fun n ↦ c n • μ n) A = ∞) :
    ∀ᵐ ω ∂(poissonSampleSeqMeasure c μ),
      (Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) A = ∞ := by
  have hfin (n : ℕ) : (c n • μ n) A ≠ ∞ := by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
  have hcnt (x : ℕ × (ℕ → E)) : sumDiracRange x.1 x.2 A ≠ ∞ := by
    rw [sumDiracRange_apply_eq_ofReal _ _ hA]
    exact ENNReal.ofReal_ne_top
  have hm1 : Measurable fun x : ℕ × (ℕ → E) ↦ sumDiracRange x.1 x.2 A :=
    (Measure.measurable_coe hA).comp measurable_sumDiracRange
  have hYm (M : ℕ) : Measurable fun ω : ℕ → ℕ × (ℕ → E) ↦
      ∑ n ∈ range M, sumDiracRange (ω n).1 (ω n).2 A :=
    Finset.measurable_sum _ fun n _ ↦ hm1.comp (measurable_pi_apply n)
  have hle (M : ℕ) (ω : ℕ → ℕ × (ℕ → E)) : ∑ n ∈ range M, sumDiracRange (ω n).1 (ω n).2 A ≤
      (Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) A := by
    rw [Measure.sum_apply _ hA]
    exact ENNReal.sum_le_tsum _
  refine ae_eq_top_of_tendsto_integral_exp_neg hYm (fun M ↦ ae_of_all _ (hle M)) ?_
  have hprod (M : ℕ) (ω : ℕ → ℕ × (ℕ → E)) :
      Real.exp (-(∑ n ∈ range M, sumDiracRange (ω n).1 (ω n).2 A).toReal) =
        ∏ n ∈ range M, Real.exp (-(sumDiracRange (ω n).1 (ω n).2 A).toReal) := by
    rw [ENNReal.toReal_sum fun n _ ↦ hcnt _, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [hprod]
  have hint (M : ℕ) : ∫ ω, ∏ n ∈ range M, Real.exp (-(sumDiracRange (ω n).1 (ω n).2 A).toReal)
      ∂(poissonSampleSeqMeasure c μ) =
        ∏ n ∈ range M, Real.exp (-(((c n • μ n) A).toReal * (1 - Real.exp (-1)))) := by
    have hg : Measurable fun x : ℕ × (ℕ → E) ↦ Real.exp (-(sumDiracRange x.1 x.2 A).toReal) :=
      Real.measurable_exp.comp hm1.ennreal_toReal.neg
    rw [poissonSampleSeqMeasure, integral_prod_range_infinitePi_of_ne (𝕜 := ℝ)
      (X := fun _ ↦ ℕ × (ℕ → E)) (ρ := fun n ↦ poissonSampleMeasure (c n) (μ n))
      (g := fun _ x ↦ Real.exp (-(sumDiracRange x.1 x.2 A).toReal)) (fun _ ↦ hg)]
    refine Finset.prod_congr rfl fun n _ ↦ ?_
    exact (isPoissonRandomMeasure_sumDiracRange (c n) (μ n)).integral_exp_neg_apply hA (hfin n)
  simp_rw [hint]
  have hsum : Tendsto (fun M ↦ ∑ n ∈ range M, (c n • μ n) A) atTop (𝓝 ∞) := by
    have h := ENNReal.tendsto_nat_tsum fun n ↦ (c n • μ n) A
    rwa [← Measure.sum_apply _ hA, hνA] at h
  refine (tendsto_exp_neg_toReal_mul (fun M ↦ ENNReal.sum_ne_top.2 fun n _ ↦ hfin n) hsum
    (a := 1 - Real.exp (-1)) (sub_pos.2 (Real.exp_lt_one_iff.2 (by norm_num)))).congr fun M ↦ ?_
  rw [ENNReal.toReal_sum fun n _ ↦ hfin n, Finset.sum_mul, ← Finset.sum_neg_distrib,
    Real.exp_sum]

/-- **Superposition of Poisson random measures.** If `(K n, Z n)` are independent, `K n` is
Poisson distributed with mean `c n` and `Z n` is an independent i.i.d. sequence with law `μ n`,
then `∑ₙ ∑_{k < K n} δ_{Z n k}` is a Poisson random measure with intensity `∑ₙ c n • μ n`. -/
theorem isPoissonRandomMeasure_sum_sumDiracRange (c : ℕ → ℝ≥0) (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] :
    IsPoissonRandomMeasure
      (fun ω : ℕ → ℕ × (ℕ → E) ↦ Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2)
      (Measure.sum fun n ↦ c n • μ n) (poissonSampleSeqMeasure c μ) where
  measurable := measurable_sum_sumDiracRange
  map_eq_pi := by
    intro m A hA hνA hd
    -- measurability of the real counts of each copy
    have hXm (n : ℕ) (i : Fin m) : Measurable fun ω : ℕ → ℕ × (ℕ → E) ↦
        ∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k) :=
      (measurable_of_measurable_nat_prod
        (F := fun n z ↦ ∑ k ∈ range n, (A i).indicator (1 : E → ℝ) (z k)) fun m ↦
          Finset.measurable_sum _ fun k _ ↦
            (measurable_one.indicator (hA i)).comp (measurable_pi_apply k)).comp
        (measurable_pi_apply n)
    have hX0 (n : ℕ) (ω : ℕ → ℕ × (ℕ → E)) (i : Fin m) :
        0 ≤ ∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k) :=
      Finset.sum_nonneg fun k _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
    have hNA (ω : ℕ → ℕ × (ℕ → E)) (i : Fin m) :
        (Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) (A i) =
          ∑' n, ENNReal.ofReal
            (∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k)) := by
      rw [Measure.sum_apply _ (hA i)]
      simp_rw [sumDiracRange_apply_eq_ofReal _ _ (hA i)]
    have hNm (i : Fin m) : Measurable fun ω : ℕ → ℕ × (ℕ → E) ↦
        (Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) (A i) :=
      (Measure.measurable_coe (hA i)).comp measurable_sum_sumDiracRange
    have hνAi (i : Fin m) : (Measure.sum fun n ↦ c n • μ n) (A i) =
        ∑' n, ENNReal.ofReal (c n * (μ n).real (A i)) := by
      rw [Measure.sum_apply _ (hA i)]
      refine tsum_congr fun n ↦ ?_
      rw [Measure.smul_apply, ENNReal.ofReal_mul (c n).coe_nonneg, ofReal_measureReal]
      simp [ENNReal.smul_def]
    -- the counts are almost surely finite
    have hfin : ∀ᵐ ω ∂(poissonSampleSeqMeasure c μ), ∀ i,
        (Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) (A i) ≠ ∞ := by
      rw [ae_all_iff]
      intro i
      have hlin : ∫⁻ ω, (Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) (A i)
          ∂(poissonSampleSeqMeasure c μ) = (Measure.sum fun n ↦ c n • μ n) (A i) := by
        simp_rw [Measure.sum_apply _ (hA i)]
        rw [lintegral_tsum (f := fun n (ω : ℕ → ℕ × (ℕ → E)) ↦ sumDiracRange (ω n).1 (ω n).2 (A i))
          fun n ↦ (((Measure.measurable_coe (hA i)).comp
            measurable_sumDiracRange).comp (measurable_pi_apply n)).aemeasurable]
        refine tsum_congr fun n ↦ ?_
        rw [poissonSampleSeqMeasure, (measurePreserving_eval_infinitePi
          (fun n ↦ poissonSampleMeasure (c n) (μ n)) n).lintegral_comp
          (f := fun x ↦ sumDiracRange x.1 x.2 (A i))
          ((Measure.measurable_coe (hA i)).comp measurable_sumDiracRange),
          lintegral_sumDiracRange_poissonSampleMeasure (hA i), Measure.smul_apply,
          ENNReal.smul_def, smul_eq_mul]
      filter_upwards [ae_lt_top (hNm i) (hlin ▸ hνA i)] with ω hω using hω.ne
    -- the real-valued counts
    obtain ⟨T, hT⟩ : ∃ T : (ℕ → ℕ × (ℕ → E)) → Fin m → ℝ, T = fun ω i ↦
        ((Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) (A i)).toReal := ⟨_, rfl⟩
    have hTm : Measurable T := hT ▸ Measurable.of_eval fun i ↦ (hNm i).ennreal_toReal
    have hconv : ∀ᵐ ω ∂(poissonSampleSeqMeasure c μ), ∀ i, Tendsto (fun M ↦ ∑ n ∈ range M,
        ∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k)) atTop (𝓝 (T ω i)) := by
      filter_upwards [hfin] with ω hω i
      have h1 := ENNReal.tendsto_nat_tsum fun n ↦ ENNReal.ofReal
        (∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k))
      rw [← hNA] at h1
      have h2 := (ENNReal.tendsto_toReal (hω i)).comp h1
      rw [hT]
      refine h2.congr fun M ↦ ?_
      simp only [Function.comp_apply]
      rw [ENNReal.toReal_sum fun n _ ↦ ENNReal.ofReal_ne_top]
      exact Finset.sum_congr rfl fun n _ ↦ ENNReal.toReal_ofReal (hX0 n ω i)
    have hrate (i : Fin m) : Tendsto (fun M ↦ ∑ n ∈ range M, (c n : ℝ) * (μ n).real (A i)) atTop
        (𝓝 ((Measure.sum fun n ↦ c n • μ n) (A i)).toReal) := by
      have h1 := ENNReal.tendsto_nat_tsum fun n ↦ ENNReal.ofReal (c n * (μ n).real (A i))
      rw [← hνAi] at h1
      refine ((ENNReal.tendsto_toReal (hνA i)).comp h1).congr fun M ↦ ?_
      simp only [Function.comp_apply]
      rw [ENNReal.toReal_sum fun n _ ↦ ENNReal.ofReal_ne_top]
      exact Finset.sum_congr rfl fun n _ ↦ ENNReal.toReal_ofReal (by positivity)
    have hchar (t : Fin m → ℝ) : ∫ ω, Complex.exp ((∑ i, t i * T ω i : ℝ) * Complex.I)
        ∂(poissonSampleSeqMeasure c μ) = Complex.exp (∑ i,
          (((Measure.sum fun n ↦ c n • μ n) (A i)).toReal : ℂ) *
            (Complex.exp (t i * Complex.I) - 1)) := by
      have hlim1 : Tendsto (fun M ↦ ∫ ω, Complex.exp ((∑ i, t i * ∑ n ∈ range M,
          ∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k) : ℝ) * Complex.I)
            ∂(poissonSampleSeqMeasure c μ)) atTop
          (𝓝 (∫ ω, Complex.exp ((∑ i, t i * T ω i : ℝ) * Complex.I)
            ∂(poissonSampleSeqMeasure c μ))) := by
        refine tendsto_integral_of_dominated_convergence (fun _ ↦ 1) (fun M ↦ ?_)
          (integrable_const 1) (fun M ↦ ae_of_all _ fun ω ↦ ?_) ?_
        · refine (Complex.measurable_exp.comp (Measurable.mul_const ?_ _)).aestronglyMeasurable
          exact Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ ↦
            (Finset.measurable_sum _ fun n _ ↦ hXm n i).const_mul _)
        · simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
        · filter_upwards [hconv] with ω hω
          refine Tendsto.cexp (Tendsto.mul_const _ ?_)
          refine (Complex.continuous_ofReal.tendsto _).comp ?_
          exact tendsto_finsetSum _ fun i _ ↦ (hω i).const_mul (t i)
      have hlim2 : Tendsto (fun M ↦ ∫ ω, Complex.exp ((∑ i, t i * ∑ n ∈ range M,
          ∑ k ∈ range (ω n).1, (A i).indicator (1 : E → ℝ) ((ω n).2 k) : ℝ) * Complex.I)
            ∂(poissonSampleSeqMeasure c μ)) atTop
          (𝓝 (Complex.exp (∑ i, (((Measure.sum fun n ↦ c n • μ n) (A i)).toReal : ℂ) *
            (Complex.exp (t i * Complex.I) - 1)))) := by
        simp_rw [integral_cexp_count_poissonSampleSeqMeasure hA hd t]
        refine Tendsto.cexp (tendsto_finsetSum _ fun i _ ↦ Tendsto.mul_const _ ?_)
        exact (Complex.continuous_ofReal.tendsto _).comp (hrate i)
      exact tendsto_nhds_unique hlim1 hlim2
    have hlawT : (poissonSampleSeqMeasure c μ).map T = Measure.pi fun i ↦
        (poissonMeasure ((Measure.sum fun n ↦ c n • μ n) (A i)).toNNReal).map
          (Nat.cast : ℕ → ℝ) := by
      refine (charFun_eq_pi_iff).1 fun t ↦ ?_
      rw [charFun_apply, integral_map (by fun_prop) (by fun_prop),
        integral_map hTm.aemeasurable (by fun_prop)]
      have hinner (ω : ℕ → ℕ × (ℕ → E)) :
          inner ℝ (WithLp.toLp 2 (T ω)) t = ∑ i, t i * T ω i := by
        simp [PiLp.inner_apply]
      simp_rw [hinner]
      rw [hchar, charFun_pi_poissonMeasure]
      rfl
    have hae : (fun ω i ↦ (Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2) (A i))
        =ᵐ[poissonSampleSeqMeasure c μ] (fun (y : Fin m → ℝ) i ↦ ENNReal.ofReal (y i)) ∘ T := by
      filter_upwards [hfin] with ω hω
      ext i
      simp [hT, ENNReal.ofReal_toReal (hω i)]
    rw [Measure.map_congr hae, ← Measure.map_map (by fun_prop) hTm, hlawT,
      Measure.pi_map_pi (fun i ↦ by fun_prop)]
    congr with i : 1
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext k
    simp
  ae_eq_top hA hνA := ae_sum_sumDiracRange_eq_top hA hνA

end Superposition

/-! ### Existence -/

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
  ae_eq_top := fun _ h ↦ absurd h (by simp)

/-- A finite measure on a nonempty space is a nonnegative multiple of a probability measure. -/
lemma exists_isProbabilityMeasure_smul_eq [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν] :
    ∃ (c : ℝ≥0) (μ : Measure E), IsProbabilityMeasure μ ∧ c • μ = ν := by
  rcases eq_or_ne ν 0 with rfl | hν
  · exact ⟨0, Measure.dirac (Classical.arbitrary E), inferInstance, zero_smul _ _⟩
  have h0 : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.2 hν
  have htop : ν Set.univ ≠ ∞ := measure_ne_top ν _
  refine ⟨(ν Set.univ).toNNReal, (ν Set.univ)⁻¹ • ν,
    ⟨by simp [ENNReal.inv_mul_cancel h0 htop]⟩, ?_⟩
  ext A hA
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, ENNReal.coe_toNNReal htop]
  rw [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]

/-- **Existence of Poisson random measures**: every s-finite (in particular every σ-finite)
measure is the intensity of a Poisson random measure, defined on a probability space in the same
universe. -/
theorem exists_isPoissonRandomMeasure {E : Type u} [MeasurableSpace E] (ν : Measure E)
    [SFinite ν] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure E),
      IsProbabilityMeasure P ∧ IsPoissonRandomMeasure N ν P := by
  rcases isEmpty_or_nonempty E with hE | hE
  · rw [Measure.eq_zero_of_isEmpty ν]
    exact ⟨PUnit, inferInstance, Measure.dirac PUnit.unit, fun _ ↦ 0, inferInstance,
      isPoissonRandomMeasure_zero⟩
  choose c μ hμ hcμ using fun n ↦ exists_isProbabilityMeasure_smul_eq (sfiniteSeq ν n)
  have hsum : (Measure.sum fun n ↦ c n • μ n) = ν := by
    simp_rw [hcμ]
    exact sum_sfiniteSeq ν
  refine ⟨ℕ → ℕ × (ℕ → E), inferInstance, poissonSampleSeqMeasure c μ,
    fun ω ↦ Measure.sum fun n ↦ sumDiracRange (ω n).1 (ω n).2, inferInstance, ?_⟩
  rw [← hsum]
  exact isPoissonRandomMeasure_sum_sumDiracRange c μ

end Existence

end ProbabilityTheory
