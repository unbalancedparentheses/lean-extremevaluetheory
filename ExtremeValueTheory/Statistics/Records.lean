/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Records of an iid sequence

For a sequence `x_0, x_1, …` of reals, `x_k` is a (strict upper) *record* if it exceeds all the
earlier values, `x_k > max_{i < k} x_i` (in particular `x_0` is always a record). For an iid
sequence `X_0, X_1, …` with a continuous distribution function, the record indicators
`I_k = 1{X_k is a record}` satisfy `P(I_k = 1) = 1 / (k + 1)` (Rényi's theorem, [EKM, §5.4],
[Resnick, Proposition 4.1]): by exchangeability, each of `X_0, …, X_k` is equally likely to be
the (almost surely unique) largest of them. The same exchangeability argument shows that the
record indicators are pairwise independent, `P(I_j = 1, I_k = 1) = P(I_j = 1) P(I_k = 1)` for
`j ≠ k`. Consequently the number `N_n = ∑_{k < n} I_k` of records among the first `n`
observations has mean the harmonic number `H_n = ∑_{k ≤ n} 1 / k ~ log n` and variance at most
`H_n`, and Chebyshev's inequality gives the weak law of large numbers `N_n / log n → 1` in
probability.

Indices start at `0`, so the `k`-th observation `X_k` corresponds to `X_{k+1}` in [EKM].

## The hypotheses

The observations `X : ℕ → Ω → ℝ` are measurable, independent (`iIndepFun X P`), identically
distributed (`P.map (X i) = P.map (X 0)`), and their common law has no atoms
(`P {ω | X 0 ω = x} = 0` for all `x`, i.e. the distribution function is continuous).

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §5.4 [EKM].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Chapter 4 [Resnick].

## Main definitions and results

* `ExtremeValueTheory.IsRecord x k`: `x k` is a record of `x`.
* `ExtremeValueTheory.recordCount x n`: the number of records among `x 0, …, x (n - 1)`.
* `measureReal_isRecord`: `P(X_k is a record) = 1 / (k + 1)`.
* `measureReal_isRecord_and_isRecord`: for `j ≠ k`, `P(X_j and X_k are records) =
  1 / (j + 1) * (1 / (k + 1))` (pairwise independence of the record indicators).
* `integral_recordCount`: `E N_n = H_n`.
* `integral_sq_recordCount_sub_le`: `E (N_n - H_n) ^ 2 ≤ H_n`.
* `tendstoInMeasure_recordCount_div_log`: `N_n / log n → 1` in probability.
-/

open Finset MeasureTheory ProbabilityTheory Filter Topology

namespace ExtremeValueTheory

/-- `x k` is a (strict upper) record of the sequence `x`: it exceeds all earlier values. -/
def IsRecord (x : ℕ → ℝ) (k : ℕ) : Prop := ∀ i < k, x i < x k

open Classical in
/-- The number `N_n` of records among `x 0, …, x (n - 1)`. -/
noncomputable def recordCount (x : ℕ → ℝ) (n : ℕ) : ℕ := #{k ∈ range n | IsRecord x k}

/-- The set of sequences whose `m`-th term is the strict maximum of the first `K` terms. -/
private def topSet (K m : ℕ) : Set (ℕ → ℝ) := {y | ∀ i < K, i ≠ m → y i < y m}

private lemma measurableSet_topSet (K m : ℕ) : MeasurableSet (topSet K m) := by
  simp only [topSet, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => MeasurableSet.iInter
    fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply m)

private lemma isRecord_iff_mem_topSet (y : ℕ → ℝ) (k : ℕ) :
    IsRecord y k ↔ y ∈ topSet (k + 1) k := by
  simp only [IsRecord, topSet, Set.mem_ofPred_eq]
  constructor
  · intro h i hi hik; exact h i (by omega)
  · intro h i hi; exact h i (by omega) (by omega)

private lemma measurableSet_isRecord (k : ℕ) : MeasurableSet {y : ℕ → ℝ | IsRecord y k} := by
  have : {y : ℕ → ℝ | IsRecord y k} = topSet (k + 1) k := by
    ext y; exact isRecord_iff_mem_topSet y k
  rw [this]; exact measurableSet_topSet _ _

private lemma swap_lt {K m m' i : ℕ} (hm : m < K) (hm' : m' < K) (hi : i < K) :
    Equiv.swap m m' i < K := by
  rw [Equiv.swap_apply_def]; split_ifs <;> assumption

/-- Swapping the `m`-th and `m'`-th coordinates exchanges `topSet K m` and `topSet K m'`. -/
private lemma comp_swap_mem_topSet {K m m' : ℕ} (hm : m < K) (hm' : m' < K) (y : ℕ → ℝ) :
    (fun i => y (Equiv.swap m m' i)) ∈ topSet K m ↔ y ∈ topSet K m' := by
  simp only [topSet, Set.mem_ofPred_eq, Equiv.swap_apply_left]
  constructor
  · intro h j hj hjm'
    have := h (Equiv.swap m m' j) (swap_lt hm hm' hj) (by
      intro h'
      apply hjm'
      simpa using congrArg (Equiv.swap m m') h')
    simpa using this
  · intro h i hi him
    exact h _ (swap_lt hm hm' hi) (by
      intro h'
      apply him
      simpa using congrArg (Equiv.swap m m') h')

/-- Swapping two coordinates after `j` does not affect whether `y j` is a record. -/
private lemma isRecord_comp_swap {j m m' : ℕ} (hm : j < m) (hm' : j < m') (y : ℕ → ℝ) :
    IsRecord (fun i => y (Equiv.swap m m' i)) j ↔ IsRecord y j := by
  have hfix : ∀ i ≤ j, Equiv.swap m m' i = i := fun i hi =>
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  simp only [IsRecord, hfix j le_rfl]
  constructor
  · intro h i hi; simpa [hfix i hi.le] using h i hi
  · intro h i hi; simpa [hfix i hi.le] using h i hi

section Exchangeability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- **Exchangeability of iid sequences**: reindexing an iid sequence by an injection does not
change its joint law. -/
theorem measure_reindex_eq (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) {g : ℕ → ℕ} (hg : g.Injective)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S) :
    P {ω | (fun i => X (g i) ω) ∈ S} = P {ω | (fun i => X i ω) ∈ S} := by
  have h1 := (hind.precomp hg).map_fun_eq_infinitePi_map (fun i => hX (g i))
  have h2 := hind.map_fun_eq_infinitePi_map hX
  have hm1 : Measurable (fun ω i => X (g i) ω) := Measurable.of_eval fun i => hX (g i)
  have hm2 : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
  change P ((fun ω i => X (g i) ω) ⁻¹' S) = P ((fun ω i => X i ω) ⁻¹' S)
  rw [← Measure.map_apply hm1 hS, ← Measure.map_apply hm2 hS, h1, h2]
  congr 2
  funext i
  rw [hident (g i), hident i]

/-- **No ties**: for iid observations with a continuous distribution, `P(X_i = X_j) = 0` for
`i ≠ j`. -/
theorem measure_eq_eq_zero (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) (hcont : ∀ x, P {ω | X 0 ω = x} = 0)
    {i j : ℕ} (hij : i ≠ j) : P {ω | X i ω = X j ω} = 0 := by
  have hpair := (hind.indepFun hij).map_prod_eq_prod_map_map (hX i).aemeasurable
    (hX j).aemeasurable
  have hset : {ω | X i ω = X j ω} = (fun ω => (X i ω, X j ω)) ⁻¹' Set.diagonal ℝ := by
    ext ω; simp [Set.diagonal]
  rw [hset, ← Measure.map_apply ((hX i).prodMk (hX j)) measurableSet_diagonal, hpair,
    Measure.prod_apply measurableSet_diagonal]
  have h0 : ∀ x, (P.map (X j)) (Prod.mk x ⁻¹' Set.diagonal ℝ) = 0 := by
    intro x
    have hs : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by ext y; simp [Set.diagonal, eq_comm]
    rw [hs, hident j, Measure.map_apply (hX 0) (measurableSet_singleton x)]
    exact hcont x
  simp [h0]

/-- Almost surely the first `K` observations have a unique strict maximum. -/
private lemma ae_exists_topSet (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) (hcont : ∀ x, P {ω | X 0 ω = x} = 0)
    {K : ℕ} (hK : 0 < K) :
    ∀ᵐ ω ∂P, ∃ m < K, (fun i => X i ω) ∈ topSet K m := by
  have hties : ∀ᵐ ω ∂P, ∀ i j, i ≠ j → X i ω ≠ X j ω := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun ω h => absurd hij h
    · rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) (measure_eq_eq_zero hX hind hident hcont hij)
      simp only [Set.mem_ofPred_eq, not_imp, not_not] at hω ⊢
      exact hω.2
  filter_upwards [hties] with ω hω
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range K) (fun i => X i ω)
    ⟨0, mem_range.2 hK⟩
  exact ⟨m, mem_range.1 hm, fun i hi him =>
    lt_of_le_of_ne (hmax i (mem_range.2 hi)) (hω i m him)⟩

/-- The events `{X_m is the strict maximum of X_0, …, X_{K-1}}`, `m < K`, cover `Ω` up to a
null set. -/
private lemma measure_compl_iUnion_topSet (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) (hcont : ∀ x, P {ω | X 0 ω = x} = 0)
    {K : ℕ} (hK : 0 < K) :
    P (⋃ m ∈ range K, {ω | (fun i => X i ω) ∈ topSet K m})ᶜ = 0 := by
  have hae := ae_exists_topSet hX hind hident hcont hK
  rw [ae_iff] at hae
  refine measure_mono_null (fun ω hω => ?_) hae
  simp only [Set.mem_compl_iff, Set.mem_iUnion, mem_range, exists_prop, not_exists,
    not_and] at hω
  simp only [Set.mem_ofPred_eq, not_exists, not_and]
  exact hω

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
private lemma pairwiseDisjoint_topSet (K : ℕ) :
    Set.PairwiseDisjoint (↑(range K)) fun m => {ω | (fun i => X i ω) ∈ topSet K m} := by
  intro a ha b hb hab
  refine Set.disjoint_left.2 fun ω h1 h2 => ?_
  have ha' : a < K := mem_range.1 ha
  have hb' : b < K := mem_range.1 hb
  have e1 := h1 b hb' (Ne.symm hab)
  have e2 := h2 a ha' hab
  exact lt_asymm e1 e2

/-- Each of `X_0, …, X_{K-1}` is the strict maximum with probability `1 / K`. -/
private lemma measureReal_topSet (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) (hcont : ∀ x, P {ω | X 0 ω = x} = 0)
    {K m : ℕ} (hm : m < K) :
    P.real {ω | (fun i => X i ω) ∈ topSet K m} = 1 / K := by
  have hK : 0 < K := by omega
  set A : ℕ → Set Ω := fun m => {ω | (fun i => X i ω) ∈ topSet K m} with hA
  have hmeas : ∀ m, MeasurableSet (A m) := fun m =>
    (Measurable.of_eval hX) (measurableSet_topSet K m)
  have heq : ∀ m < K, P.real (A m) = P.real (A 0) := by
    intro m hm
    have := measure_reindex_eq hX hind hident (Equiv.swap 0 m).injective
      (measurableSet_topSet K 0)
    have hs : {ω | (fun i => X (Equiv.swap 0 m i) ω) ∈ topSet K 0} = A m := by
      ext ω; exact comp_swap_mem_topSet hK hm (fun i => X i ω)
    rw [hs] at this
    rw [measureReal_def, measureReal_def, this]
  have hU : P.real (⋃ m ∈ range K, A m) = 1 := by
    have h1 : P (⋃ m ∈ range K, A m) = 1 :=
      (prob_compl_eq_zero_iff (MeasurableSet.biUnion (Set.to_countable _)
        fun m _ => hmeas m)).1 (measure_compl_iUnion_topSet hX hind hident hcont hK)
    rw [measureReal_def, h1, ENNReal.toReal_one]
  rw [measureReal_biUnion_finset (pairwiseDisjoint_topSet K) (fun m _ => hmeas m),
    Finset.sum_congr rfl (fun m hm => heq m (mem_range.1 hm)), sum_const, card_range,
    nsmul_eq_mul] at hU
  rw [heq m hm, eq_div_iff (by positivity), mul_comm]
  exact hU

/-- **Rényi's theorem, marginals** ([EKM, §5.4], [Resnick, Proposition 4.1]): for iid
observations with a continuous distribution, `X_k` is a record with probability
`1 / (k + 1)`. -/
theorem measureReal_isRecord (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) (hcont : ∀ x, P {ω | X 0 ω = x} = 0) (k : ℕ) :
    P.real {ω | IsRecord (fun i => X i ω) k} = 1 / (k + 1) := by
  simp_rw [isRecord_iff_mem_topSet]
  rw [measureReal_topSet hX hind hident hcont (Nat.lt_succ_self k)]
  push_cast
  ring

/-- **Rényi's theorem, pairwise independence** ([EKM, §5.4], [Resnick, Proposition 4.1]): for
iid observations with a continuous distribution and `j < k`,
`P(X_j and X_k are records) = 1 / (j + 1) * (1 / (k + 1))`. -/
theorem measureReal_isRecord_and_isRecord_of_lt (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hident : ∀ i, P.map (X i) = P.map (X 0))
    (hcont : ∀ x, P {ω | X 0 ω = x} = 0) {j k : ℕ} (hjk : j < k) :
    P.real {ω | IsRecord (fun i => X i ω) j ∧ IsRecord (fun i => X i ω) k} =
      1 / (j + 1) * (1 / (k + 1)) := by
  set K := k + 1 with hKdef
  have hK : 0 < K := by omega
  set A : ℕ → Set Ω := fun m => {ω | (fun i => X i ω) ∈ topSet K m} with hA
  set R : Set Ω := {ω | IsRecord (fun i => X i ω) j} with hR
  have hmeasA : ∀ m, MeasurableSet (A m) := fun m =>
    (Measurable.of_eval hX) (measurableSet_topSet K m)
  have hmeasR : MeasurableSet R := (Measurable.of_eval hX) (measurableSet_isRecord j)
  have htarget : {ω | IsRecord (fun i => X i ω) j ∧ IsRecord (fun i => X i ω) k} = R ∩ A k := by
    ext ω
    simp only [hR, hA, Set.mem_inter_iff, Set.mem_ofPred_eq, isRecord_iff_mem_topSet _ k]
    exact Iff.rfl
  set f : ℕ → ℝ := fun m => P.real (R ∩ A m) with hf
  -- the decomposition of `P(R)` along the a.s. partition `{A m}`
  have hsum : P.real R = ∑ m ∈ range K, f m := by
    have hc := measure_compl_iUnion_topSet hX hind hident hcont hK (P := P)
    have : P.real R = P.real (R ∩ ⋃ m ∈ range K, A m) := by
      rw [measureReal_def, measureReal_def, measure_inter_conull hc]
    rw [this, Set.inter_iUnion₂, measureReal_biUnion_finset]
    · intro a ha b hb hab
      exact ((pairwiseDisjoint_topSet K (X := X) ha hb hab).mono Set.inter_subset_right
        Set.inter_subset_right)
    · exact fun m _ => hmeasR.inter (hmeasA m)
  -- `m < j`: `X_m` cannot be the maximum if `X_j` is a record
  have hlt : ∀ m < j, f m = 0 := by
    intro m hm
    have : R ∩ A m = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hr ha
      exact lt_asymm (hr m hm) (ha j (by omega) (by omega))
    simp [hf, this]
  -- `m = j`
  have hj : f j = 1 / K := by
    have : R ∩ A j = A j := by
      refine Set.inter_eq_right.2 fun ω ha i hi => ha i (by omega) (by omega)
    show P.real (R ∩ A j) = _
    rw [this]
    exact measureReal_topSet hX hind hident hcont (m := j) (by omega)
  -- `j < m < K`: exchange `X_m` and `X_k`
  have hgt : ∀ m, j < m → m < K → f m = f k := by
    intro m hjm hmK
    have hS : MeasurableSet ({y : ℕ → ℝ | IsRecord y j} ∩ topSet K m) :=
      (measurableSet_isRecord j).inter (measurableSet_topSet K m)
    have := measure_reindex_eq hX hind hident (Equiv.swap m k).injective hS
    have hs : {ω | (fun i => X (Equiv.swap m k i) ω) ∈ {y : ℕ → ℝ | IsRecord y j} ∩ topSet K m}
        = R ∩ A k := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hR, hA]
      rw [isRecord_comp_swap hjm hjk (fun i => X i ω),
        comp_swap_mem_topSet hmK (by omega) (fun i => X i ω)]
    rw [hs] at this
    show P.real (R ∩ A m) = P.real (R ∩ A k)
    rw [measureReal_def, measureReal_def, this]
    rfl
  have hPR : P.real R = 1 / (j + 1) := measureReal_isRecord hX hind hident hcont j
  rw [hsum, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (j + 1))
    (show j + 1 ≤ K by omega), Finset.sum_Ico_succ_top (Nat.zero_le j),
    Finset.sum_congr rfl (fun m hm => hlt m (Finset.mem_Ico.1 hm).2),
    Finset.sum_congr rfl (fun m hm => hgt m (by have := (Finset.mem_Ico.1 hm).1; omega)
      (Finset.mem_Ico.1 hm).2), hj] at hPR
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_zero, zero_add] at hPR
  rw [htarget]
  change f k = _
  have hkj : (0 : ℝ) < k - j := by
    have : (j : ℝ) < k := by exact_mod_cast hjk
    linarith
  have hcast : ((K - (j + 1) : ℕ) : ℝ) = k - j := by
    rw [Nat.cast_sub (by omega)]; push_cast [hKdef]; ring
  rw [hcast, hKdef] at hPR
  push_cast at hPR
  field_simp at hPR ⊢
  nlinarith [hPR]

/-- Pairwise independence of the record indicators: for `j ≠ k`,
`P(X_j and X_k are records) = P(X_j is a record) P(X_k is a record)`. -/
theorem measureReal_isRecord_and_isRecord (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hident : ∀ i, P.map (X i) = P.map (X 0))
    (hcont : ∀ x, P {ω | X 0 ω = x} = 0) {j k : ℕ} (hjk : j ≠ k) :
    P.real {ω | IsRecord (fun i => X i ω) j ∧ IsRecord (fun i => X i ω) k} =
      1 / (j + 1) * (1 / (k + 1)) := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact measureReal_isRecord_and_isRecord_of_lt hX hind hident hcont h
  · have : {ω | IsRecord (fun i => X i ω) j ∧ IsRecord (fun i => X i ω) k} =
        {ω | IsRecord (fun i => X i ω) k ∧ IsRecord (fun i => X i ω) j} := by
      ext ω; simp [and_comm]
    rw [this, measureReal_isRecord_and_isRecord_of_lt hX hind hident hcont h, mul_comm]

end Exchangeability

section Counting

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

private lemma recordCount_eq_sum (x : ℕ → ℝ) (n : ℕ) :
    (recordCount x n : ℝ) = ∑ k ∈ range n, {y : ℕ → ℝ | IsRecord y k}.indicator 1 x := by
  rw [recordCount, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : IsRecord x k <;> simp [h]

omit [MeasurableSpace Ω] in
private lemma recordCount_eq_sum' (n : ℕ) (ω : Ω) :
    (recordCount (fun i => X i ω) n : ℝ) =
      ∑ k ∈ range n, {ω | IsRecord (fun i => X i ω) k}.indicator 1 ω := by
  rw [recordCount_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : IsRecord (fun i => X i ω) k <;> simp [h]

omit [IsProbabilityMeasure P] in
private lemma integrable_indicator_one' {A : Set Ω} (hA : MeasurableSet A) [IsFiniteMeasure P] :
    Integrable (A.indicator (1 : Ω → ℝ)) P :=
  (integrable_const (1 : ℝ)).indicator hA

omit [MeasurableSpace Ω] in
private lemma indicator_sub_mul_eq (A B : Set Ω) (a b : ℝ) (ω : Ω) :
    (A.indicator (1 : Ω → ℝ) ω - a) * (B.indicator 1 ω - b) =
      (A ∩ B).indicator 1 ω - a * B.indicator 1 ω - b * A.indicator 1 ω + a * b := by
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb] <;> ring

private lemma integrable_indicator_sub_mul {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (a b : ℝ) :
    Integrable (fun ω => (A.indicator (1 : Ω → ℝ) ω - a) * (B.indicator 1 ω - b)) P := by
  simp_rw [indicator_sub_mul_eq]
  exact (((integrable_indicator_one' (hA.inter hB)).sub
    ((integrable_indicator_one' hB).const_mul a)).sub
    ((integrable_indicator_one' hA).const_mul b)).add (integrable_const _)

private lemma integral_indicator_sub_mul {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (a b : ℝ) :
    ∫ ω, (A.indicator (1 : Ω → ℝ) ω - a) * (B.indicator 1 ω - b) ∂P =
      P.real (A ∩ B) - a * P.real B - b * P.real A + a * b := by
  have iA := integrable_indicator_one' hA (P := P)
  have iB := integrable_indicator_one' hB (P := P)
  have iAB := integrable_indicator_one' (hA.inter hB) (P := P)
  simp_rw [indicator_sub_mul_eq]
  rw [integral_add (f := fun ω => (A ∩ B).indicator (1 : Ω → ℝ) ω - a * B.indicator 1 ω -
      b * A.indicator 1 ω) (g := fun _ => a * b)
      ((iAB.sub (iB.const_mul a)).sub (iA.const_mul b)) (integrable_const _),
    integral_sub (f := fun ω => (A ∩ B).indicator (1 : Ω → ℝ) ω - a * B.indicator 1 ω)
      (g := fun ω => b * A.indicator 1 ω) (iAB.sub (iB.const_mul a)) (iA.const_mul b),
    integral_sub (f := (A ∩ B).indicator (1 : Ω → ℝ)) (g := fun ω => a * B.indicator 1 ω)
      iAB (iB.const_mul a), integral_const_mul, integral_const_mul,
    integral_indicator_one (hA.inter hB), integral_indicator_one hA,
    integral_indicator_one hB, integral_const]
  simp

/-- **Expected number of records** ([EKM, §5.4], [Resnick, Proposition 4.1]): for iid
observations with a continuous distribution, `E N_n = H_n = ∑_{k ≤ n} 1 / k`. -/
theorem integral_recordCount (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) (hcont : ∀ x, P {ω | X 0 ω = x} = 0) (n : ℕ) :
    ∫ ω, (recordCount (fun i => X i ω) n : ℝ) ∂P = harmonic n := by
  have hR : ∀ k, MeasurableSet {ω | IsRecord (fun i => X i ω) k} := fun k =>
    (Measurable.of_eval hX) (measurableSet_isRecord k)
  simp_rw [recordCount_eq_sum']
  rw [integral_finsetSum _ (fun k _ => integrable_indicator_one' (hR k))]
  simp_rw [integral_indicator_one (hR _), measureReal_isRecord hX hind hident hcont]
  simp [harmonic]

/-- **Variance bound for the number of records**: by the pairwise independence of the record
indicators, `E (N_n - H_n) ^ 2 = ∑_{k ≤ n} (1 / k - 1 / k ^ 2) ≤ H_n`. -/
theorem integral_sq_recordCount_sub_le (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = P.map (X 0)) (hcont : ∀ x, P {ω | X 0 ω = x} = 0) (n : ℕ) :
    Integrable (fun ω => ((recordCount (fun i => X i ω) n : ℝ) - harmonic n) ^ 2) P ∧
    ∫ ω, ((recordCount (fun i => X i ω) n : ℝ) - harmonic n) ^ 2 ∂P ≤ harmonic n := by
  set R : ℕ → Set Ω := fun k => {ω | IsRecord (fun i => X i ω) k} with hRdef
  have hR : ∀ k, MeasurableSet (R k) := fun k =>
    (Measurable.of_eval hX) (measurableSet_isRecord k)
  set p : ℕ → ℝ := fun k => 1 / (k + 1) with hp
  have hH : (harmonic n : ℝ) = ∑ k ∈ range n, p k := by simp [harmonic, hp]
  have hpt : ∀ ω, ((recordCount (fun i => X i ω) n : ℝ) - harmonic n) ^ 2 =
      ∑ j ∈ range n, ∑ k ∈ range n,
        ((R j).indicator 1 ω - p j) * ((R k).indicator 1 ω - p k) := by
    intro ω
    rw [recordCount_eq_sum', hH, ← sum_sub_distrib, sq, sum_mul_sum]
  simp_rw [hpt]
  have hint : ∀ j k, Integrable
      (fun ω => ((R j).indicator (1 : Ω → ℝ) ω - p j) * ((R k).indicator 1 ω - p k)) P :=
    fun j k => integrable_indicator_sub_mul (hR j) (hR k) _ _
  refine ⟨integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k, ?_⟩
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ k]
  have hPR : ∀ k, P.real (R k) = p k := fun k => measureReal_isRecord hX hind hident hcont k
  have hterm : ∀ j k, ∫ ω, ((R j).indicator (1 : Ω → ℝ) ω - p j) *
      ((R k).indicator 1 ω - p k) ∂P = if j = k then p k - p k ^ 2 else 0 := by
    intro j k
    rw [integral_indicator_sub_mul (hR j) (hR k), hPR, hPR]
    split_ifs with h
    · subst h
      rw [Set.inter_self, hPR]
      ring
    · have : P.real (R j ∩ R k) = p j * p k :=
        measureReal_isRecord_and_isRecord hX hind hident hcont h
      rw [this]
      ring
  simp_rw [hterm, Finset.sum_ite_eq]
  rw [hH]
  refine Finset.sum_le_sum fun k hk => ?_
  simp only [hk, ite_true]
  nlinarith [sq_nonneg (p k)]

/-- **Weak law of large numbers for the number of records** ([EKM, §5.4], [Resnick,
Proposition 4.1]): for iid observations with a continuous distribution, `N_n / log n → 1` in
probability. -/
theorem tendstoInMeasure_recordCount_div_log (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hident : ∀ i, P.map (X i) = P.map (X 0))
    (hcont : ∀ x, P {ω | X 0 ω = x} = 0) :
    TendstoInMeasure P (fun (n : ℕ) ω => (recordCount (fun i => X i ω) n : ℝ) / Real.log n)
      atTop (fun _ => 1) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  set b : ℕ → ℝ := fun n => (1 + Real.log n) / (ε / 2 * Real.log n) ^ 2 with hbdef
  have hb : Tendsto b atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hlog
    have := ((hinv.pow 2).add hinv).const_mul (4 / ε ^ 2)
    rw [show (4 / ε ^ 2) * ((0 : ℝ) ^ 2 + 0) = 0 by ring] at this
    refine this.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    simp only [hbdef]
    field_simp
    ring
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hb
  filter_upwards [hlog.eventually_ge_atTop (2 / ε)] with n hn
  set L := Real.log n with hLdef
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hn
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n
    simp [hLdef] at hL
  have hle : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hn1) (by push_cast; linarith)
  have hHL1 : L ≤ harmonic n := hle.trans (log_add_one_le_harmonic n)
  have hHL2 : (harmonic n : ℝ) ≤ 1 + L := harmonic_le_one_add_log n
  set δ := (ε / 2 * L) ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hεL : 2 ≤ ε * L := by
    rw [div_le_iff₀ hε] at hn; linarith
  have hsub : {ω | ε ≤ dist ((recordCount (fun i => X i ω) n : ℝ) / L) 1} ⊆
      {ω | δ ≤ ((recordCount (fun i => X i ω) n : ℝ) - harmonic n) ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
    set N : ℝ := (recordCount (fun i => X i ω) n : ℝ)
    have h1 : ε * L ≤ |N - L| := by
      have : N / L - 1 = (N - L) / L := by field_simp
      rw [this, abs_div, abs_of_pos hL, le_div_iff₀ hL] at hω
      exact hω
    have h2 : |N - L| ≤ |N - harmonic n| + |(harmonic n : ℝ) - L| := abs_sub_le _ _ _
    have h3 : |(harmonic n : ℝ) - L| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have h4 : ε / 2 * L ≤ |N - harmonic n| := by linarith
    calc δ = (ε / 2 * L) ^ 2 := rfl
      _ ≤ |N - harmonic n| ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      _ = (N - harmonic n) ^ 2 := sq_abs _
  obtain ⟨hint, hle⟩ := integral_sq_recordCount_sub_le hX hind hident hcont n
  calc P.real {ω | ε ≤ dist ((recordCount (fun i => X i ω) n : ℝ) / L) 1}
      ≤ P.real {ω | δ ≤ ((recordCount (fun i => X i ω) n : ℝ) - harmonic n) ^ 2} :=
        measureReal_mono hsub
    _ ≤ (∫ ω, ((recordCount (fun i => X i ω) n : ℝ) - harmonic n) ^ 2 ∂P) / δ := by
        rw [le_div_iff₀ hδ, mul_comm]
        exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) hint δ
    _ ≤ harmonic n / δ := div_le_div_of_nonneg_right hle hδ.le
    _ ≤ b n := div_le_div_of_nonneg_right hHL2 hδ.le

end Counting

end ExtremeValueTheory
