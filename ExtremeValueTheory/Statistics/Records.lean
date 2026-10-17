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

end ExtremeValueTheory
