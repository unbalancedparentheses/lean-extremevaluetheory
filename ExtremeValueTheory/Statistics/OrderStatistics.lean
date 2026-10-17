/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic

/-!
# Descending order statistics

For a sample `x : Fin n → ℝ` we define the *descending order statistics*
`X_{(1)} ≥ X_{(2)} ≥ ⋯ ≥ X_{(n)}`. To make the Hill estimator easy to write we index them by
natural numbers starting at `0`: `orderStat x j = X_{(j+1)}` is the `(j+1)`-th largest value of
the sample, for `j < n` (and `orderStat x j = 0`, a junk value, for `j ≥ n`).

The order statistics are obtained from `Tuple.sort`, which sorts a tuple increasingly, by
reversing the order.

This is the setting of de Haan and Ferreira, *Extreme Value Theory: An Introduction* (Springer,
2006), §3.2, and of Mason, *Laws of large numbers for sums of extreme values*
(Ann. Probab. 10, 1982), where tail estimators are built from the top `k + 1` order statistics.

## Main definitions

* `ExtremeValueTheory.orderStat x j`: the `(j+1)`-th largest entry of `x : Fin n → ℝ`.
* `ExtremeValueTheory.exceedCount x a`: the number `#{i | a < x i}` of exceedances of `a`.

## Main results

* `orderStat_perm`: the order statistics are a permutation of the sample.
* `sum_orderStat`: sums of a function over the order statistics and over the sample agree.
* `orderStat_anti`: the order statistics are decreasing.
* `lt_orderStat_iff`: `a < X_{(j+1)} ↔ j + 1 ≤ #{i | a < x i}`, the basic duality between
  order statistics and exceedance counts.
* `measurable_orderStat`: the order statistics of measurable random variables are measurable.
* `measure_lt_orderStat_eq`: `P(X_{(j+1)} > a) = P(#{i | X_i > a} ≥ j + 1)`.
* `measure_exceedCount_eq`: for independent `X_i` with common exceedance probability
  `p = P(X_i > a)`, the exceedance count is binomial:
  `P(#{i | X_i > a} = m) = (n choose m) p ^ m (1 - p) ^ (n - m)`.
* `measure_lt_orderStat_eq_sum`: consequently
  `P(X_{(j+1)} > a) = ∑_{m = j+1}^{n} (n choose m) p ^ m (1 - p) ^ (n - m)`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

variable {n : ℕ}

/-- The descending order statistics of a sample `x : Fin n → ℝ`, indexed from `0`:
`orderStat x j` is `X_{(j+1)}`, the `(j+1)`-th largest entry of `x`, when `j < n`, and `0`
(a junk value) otherwise. Thus `orderStat x 0 ≥ orderStat x 1 ≥ ⋯ ≥ orderStat x (n - 1)`. -/
noncomputable def orderStat (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x (Tuple.sort x (Fin.rev ⟨j, h⟩)) else 0

/-- The number of entries of the sample `x` exceeding the level `a`. -/
noncomputable def exceedCount (x : Fin n → ℝ) (a : ℝ) : ℕ :=
  #{i | a < x i}

theorem orderStat_of_lt (x : Fin n → ℝ) {j : ℕ} (h : j < n) :
    orderStat x j = x (Tuple.sort x (Fin.rev ⟨j, h⟩)) := by
  simp [orderStat, h]

theorem orderStat_of_le (x : Fin n → ℝ) {j : ℕ} (h : n ≤ j) : orderStat x j = 0 := by
  simp [orderStat, Nat.not_lt.2 h]

/-- The order statistics are a permutation of the sample. -/
theorem orderStat_perm (x : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j : Fin n, orderStat x j = x (σ j) :=
  ⟨Fin.revPerm.trans (Tuple.sort x), fun j => by simp [orderStat_of_lt x j.2]⟩

/-- Sums over the order statistics and over the sample agree. -/
theorem sum_orderStat (x : Fin n → ℝ) {M : Type*} [AddCommMonoid M] (f : ℝ → M) :
    ∑ j ∈ range n, f (orderStat x j) = ∑ i, f (x i) := by
  obtain ⟨σ, hσ⟩ := orderStat_perm x
  rw [← Fin.sum_univ_eq_sum_range (fun j => f (orderStat x j))]
  simp_rw [hσ]
  exact Equiv.sum_comp σ (fun i => f (x i))

/-- The order statistics are decreasing. -/
theorem orderStat_anti (x : Fin n → ℝ) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    orderStat x j ≤ orderStat x i := by
  rw [orderStat_of_lt x hj, orderStat_of_lt x (hij.trans_lt hj)]
  exact Tuple.monotone_sort x (Fin.rev_le_rev.2 (by simpa [Fin.le_def] using hij))

/-- **Duality between order statistics and exceedance counts**: the `(j+1)`-th largest entry
exceeds `a` if and only if at least `j + 1` entries exceed `a`. -/
theorem lt_orderStat_iff (x : Fin n → ℝ) {j : ℕ} (hj : j < n) (a : ℝ) :
    a < orderStat x j ↔ j + 1 ≤ exceedCount x a := by
  set σ := Tuple.sort x
  set y := x ∘ σ with hy
  have hmono : Monotone y := Tuple.monotone_sort x
  have hcount : exceedCount x a = #{m | a < y m} := by
    unfold exceedCount
    exact Finset.card_bij (fun i _ => σ.symm i) (fun i hi => by simpa [hy] using hi)
      (fun _ _ _ _ h => σ.symm.injective h) (fun b hb => ⟨σ b, by simpa [hy] using hb, by simp⟩)
  rw [orderStat_of_lt x hj, hcount]
  set r : Fin n := Fin.rev ⟨j, hj⟩ with hr
  have hrv : (r : ℕ) = n - (j + 1) := by simp [hr, Fin.val_rev]
  change a < y r ↔ _
  constructor
  · intro h
    have hsub : Ici r ⊆ ({m | a < y m} : Finset (Fin n)) := by
      intro m hm
      simp only [Finset.mem_Ici] at hm
      simpa using h.trans_le (hmono hm)
    have := card_le_card hsub
    rw [Fin.card_Ici, hrv] at this
    omega
  · intro h
    by_contra hle
    push Not at hle
    have hsub : ({m | a < y m} : Finset (Fin n)) ⊆ Ioi r := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Ioi]
      by_contra hmr
      push Not at hmr
      exact absurd ((hmono hmr).trans hle) (not_le.2 hm)
    have := card_le_card hsub
    rw [Fin.card_Ioi, hrv] at this
    omega

/-- The dual form of `lt_orderStat_iff`. -/
theorem orderStat_le_iff (x : Fin n → ℝ) {j : ℕ} (hj : j < n) (a : ℝ) :
    orderStat x j ≤ a ↔ exceedCount x a ≤ j := by
  rw [← not_lt, lt_orderStat_iff x hj]
  omega

theorem exceedCount_eq_sum (x : Fin n → ℝ) (a : ℝ) :
    (exceedCount x a : ℝ) = ∑ i, if a < x i then (1 : ℝ) else 0 := by
  simp only [exceedCount]
  rw [Finset.natCast_card_filter]

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_exceedCount {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (a : ℝ) :
    Measurable fun ω => exceedCount (fun i => X i ω) a := by
  have : (fun ω => exceedCount (fun i => X i ω) a) =
      fun ω => ∑ i, if a < X i ω then (1 : ℕ) else 0 := by
    funext ω; simp only [exceedCount, Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_lt measurable_const (hX i)) measurable_const
    measurable_const

/-- The order statistics of measurable random variables are measurable. -/
theorem measurable_orderStat {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (j : ℕ) :
    Measurable fun ω => orderStat (fun i => X i ω) j := by
  by_cases hj : j < n
  · refine measurable_of_Ioi fun a => ?_
    have : (fun ω => orderStat (fun i => X i ω) j) ⁻¹' Set.Ioi a =
        (fun ω => exceedCount (fun i => X i ω) a) ⁻¹' {m | j + 1 ≤ m} := by
      ext ω
      simp [lt_orderStat_iff _ hj]
    rw [this]
    exact measurable_exceedCount hX a (MeasurableSet.of_discrete)
  · simp_rw [orderStat_of_le _ (Nat.not_lt.1 hj)]
    exact measurable_const

/-- `P(X_{(j+1)} > a) = P(#{i | X_i > a} ≥ j + 1)`. -/
theorem measure_lt_orderStat_eq (P : Measure Ω) (X : Fin n → Ω → ℝ) {j : ℕ} (hj : j < n)
    (a : ℝ) :
    P {ω | a < orderStat (fun i => X i ω) j} =
      P {ω | j + 1 ≤ exceedCount (fun i => X i ω) a} := by
  congr 1
  ext ω
  exact lt_orderStat_iff _ hj a

/-- **The exceedance count is binomial.** If `X_0, …, X_{n-1}` are independent and all exceed
the level `a` with the same probability `p`, then
`P(#{i | X_i > a} = m) = (n choose m) p ^ m (1 - p) ^ (n - m)`. -/
theorem measure_exceedCount_eq {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {a : ℝ} {p : ENNReal}
    (hp : ∀ i, P {ω | a < X i ω} = p) (m : ℕ) :
    P {ω | exceedCount (fun i => X i ω) a = m} = n.choose m * p ^ m * (1 - p) ^ (n - m) := by
  classical
  -- the event `{exactly the indices in s exceed a}`
  let E : Finset (Fin n) → Set Ω := fun s =>
    ⋂ i ∈ (univ : Finset (Fin n)), X i ⁻¹' (if i ∈ s then Set.Ioi a else Set.Iic a)
  have hE : ∀ s ω, ω ∈ E s ↔ ({i | a < X i ω} : Finset (Fin n)) = s := by
    intro s ω
    simp only [E, Set.mem_iInter, Set.mem_preimage, Finset.mem_univ, forall_const]
    constructor
    · intro h
      ext i
      have := h i
      by_cases hi : i ∈ s
      · simp only [hi, ite_true, Set.mem_Ioi] at this; simp [hi, this]
      · simp only [hi, ite_false, Set.mem_Iic] at this; simp [hi, not_lt.2 this]
    · rintro rfl i
      by_cases hi : a < X i ω
      · simp [hi]
      · simp [hi, not_lt.1 hi]
  have hset : {ω | exceedCount (fun i => X i ω) a = m} = ⋃ s ∈ powersetCard m univ, E s := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hE, mem_powersetCard, subset_univ, true_and,
      exists_prop, exists_eq_right', exceedCount]
  have hmeasE : ∀ s, MeasurableSet (E s) := by
    intro s
    refine MeasurableSet.biInter (Set.to_countable _) fun i _ => hX i ?_
    split_ifs
    · exact measurableSet_Ioi
    · exact measurableSet_Iic
  have hPE : ∀ s : Finset (Fin n), P (E s) = p ^ s.card * (1 - p) ^ (n - s.card) := by
    intro s
    rw [hind.measure_inter_preimage_eq_mul univ (sets := fun i =>
      if i ∈ s then Set.Ioi a else Set.Iic a) (fun i _ => by
        split_ifs
        · exact measurableSet_Ioi
        · exact measurableSet_Iic)]
    have hq : ∀ i, P (X i ⁻¹' Set.Iic a) = 1 - p := by
      intro i
      have hc : X i ⁻¹' Set.Iic a = {ω | a < X i ω}ᶜ := by ext ω; simp
      rw [hc, prob_compl_eq_one_sub (measurableSet_lt measurable_const (hX i)), hp]
    have h1 : ∀ i, P (X i ⁻¹' (if i ∈ s then Set.Ioi a else Set.Iic a)) =
        if i ∈ s then p else 1 - p := by
      intro i
      split_ifs
      · exact hp i
      · exact hq i
    simp_rw [h1]
    rw [Finset.prod_ite, prod_const, prod_const]
    congr 2
    · congr 1; ext i; simp
    · have : (filter (fun i => i ∉ s) univ) = sᶜ := by ext i; simp
      rw [this, card_compl, Fintype.card_fin]
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun s hs => by rw [hPE s, (mem_powersetCard.1 hs).2]]
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  · intro s _ t _ hst
    refine Set.disjoint_left.2 fun ω h1 h2 => hst ?_
    rw [hE] at h1 h2
    exact h1.symm.trans h2
  · exact fun s _ => hmeasE s

/-- The distribution of an order statistic in terms of binomial probabilities: for independent
`X_i` with common exceedance probability `p = P(X_i > a)`,
`P(X_{(j+1)} > a) = ∑_{m = j+1}^{n} (n choose m) p ^ m (1 - p) ^ (n - m)`. -/
theorem measure_lt_orderStat_eq_sum {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {a : ℝ}
    {p : ENNReal} (hp : ∀ i, P {ω | a < X i ω} = p) {j : ℕ} (hj : j < n) :
    P {ω | a < orderStat (fun i => X i ω) j} =
      ∑ m ∈ Finset.Ioc j n, n.choose m * p ^ m * (1 - p) ^ (n - m) := by
  classical
  rw [measure_lt_orderStat_eq P X hj a]
  have hset : {ω | j + 1 ≤ exceedCount (fun i => X i ω) a} =
      ⋃ m ∈ Finset.Ioc j n, {ω | exceedCount (fun i => X i ω) a = m} := by
    ext ω
    have hle : exceedCount (fun i => X i ω) a ≤ n := (card_le_univ _).trans (by simp)
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Ioc, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨by omega, hle⟩, rfl⟩
    · rintro ⟨m, hm, rfl⟩; omega
  rw [hset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun m _ => measure_exceedCount_eq hX hind hp m
  · intro s _ t _ hst
    exact Set.disjoint_left.2 fun ω h1 h2 => hst (h1.symm.trans h2)
  · exact fun m _ => measurable_exceedCount hX a (measurableSet_singleton m)

end Measurability

end ExtremeValueTheory
