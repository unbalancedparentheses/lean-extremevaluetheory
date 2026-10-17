/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.OrderStatistics
import ExtremeValueTheory.LimitRelationManipulation
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# Limit laws of the upper order statistics

Let `X_1, X_2, …` be iid with c.d.f. `F` and let `X_{(1)} ≥ X_{(2)} ≥ ⋯ ≥ X_{(n)}` be the
descending order statistics of the first `n` observations. If the levels `u_n` satisfy
`n (1 - F (u_n)) → τ ∈ [0, ∞)`, then the number of exceedances of `u_n` is binomial with
parameters `n` and `1 - F (u_n)`, hence asymptotically Poisson with mean `τ`, and so

`P(X_{(k)} ≤ u_n) = P(#{i ≤ n | X_i > u_n} < k) → e^{-τ} ∑_{j < k} τ ^ j / j!`

([EKM, Theorem 4.2.3], [LLR, Theorem 2.2.2]). In particular, if `F` is in the maximum domain
of attraction of `H` with normalizations `A_n`, then the normalized `k`-th largest value has
limit law `H(x) ∑_{j < k} (-log H(x)) ^ j / j!`.

For two levels `u_n ≥ v_n` with `n (1 - F (u_n)) → τ₁` and `n (1 - F (v_n)) → τ₂`, counting
the observations in `(v_n, u_n]` and above `u_n` (a multinomial count) gives the joint limit
law of the two largest order statistics,

`P(X_{(1)} ≤ u_n, X_{(2)} ≤ v_n) → e^{-τ₂} (1 + τ₂ - τ₁)`

([EKM, Theorem 4.2.6 / §4.2], [LLR, Theorem 2.3.2]).

Order statistics are indexed from `0` as in `ExtremeValueTheory.orderStat`: `orderStat x j` is
`X_{(j+1)}`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §4.2 [EKM].
* M. R. Leadbetter, G. Lindgren and H. Rootzén, *Extremes and Related Properties of Random
  Sequences and Processes*, Springer (1983), §2.2–2.3 [LLR].

## Main results

* `measure_orderStat_le_eq_sum`, `measureReal_orderStat_le_eq_sum`: the finite-sample law
  `P(X_{(j+1)} ≤ a) = ∑_{m ≤ j} (n choose m) (1 - F a) ^ m (F a) ^ (n - m)`.
* `tendsto_measureReal_orderStat_le`: **Poisson limit of the `k`-th largest** ([EKM, Theorem
  4.2.3]).
* `tendsto_measureReal_affine_orderStat_le`: the corresponding limit law of the normalized
  `k`-th largest, `H(x) ∑_{m ≤ j} (-log H(x)) ^ m / m!`, from the max-domain-of-attraction
  limit relation.
* `measureReal_orderStat_zero_le_and_orderStat_one_le`: the finite-sample joint law
  `P(X_{(1)} ≤ u, X_{(2)} ≤ v) = F(v) ^ n + n (F u - F v) F(v) ^ (n - 1)` for `v ≤ u`.
* `tendsto_measureReal_orderStat_zero_le_and_orderStat_one_le`: its limit
  `e^{-τ₂} (1 + τ₂ - τ₁)`.
* `tendsto_measureReal_affine_orderStat_zero_one`: the joint limit law of the two largest
  normalized order statistics.
-/

open Finset MeasureTheory ProbabilityTheory Filter Topology

namespace ExtremeValueTheory

section FiniteSample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- `P(X_{(j+1)} ≤ a) = P(#{i | X_i > a} ≤ j) = ∑_{m ≤ j} (n choose m) p ^ m (1 - p) ^ (n - m)`,
for independent `X_i` with common exceedance probability `p = P(X_i > a)`. -/
theorem measure_orderStat_le_eq_sum {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {a : ℝ} {p : ENNReal} (hp : ∀ i, P {ω | a < X i ω} = p) {j : ℕ}
    (hj : j < n) :
    P {ω | orderStat (fun i => X i ω) j ≤ a} =
      ∑ m ∈ range (j + 1), n.choose m * p ^ m * (1 - p) ^ (n - m) := by
  classical
  have hset : {ω | orderStat (fun i => X i ω) j ≤ a} =
      ⋃ m ∈ range (j + 1), {ω | exceedCount (fun i => X i ω) a = m} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
      orderStat_le_iff _ hj]
    constructor
    · intro h; exact ⟨_, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩; omega
  rw [hset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun m _ => measure_exceedCount_eq hX hind hp m
  · intro s _ t _ hst
    exact Set.disjoint_left.2 fun ω h1 h2 => hst (h1.symm.trans h2)
  · exact fun m _ => measurable_exceedCount hX a (measurableSet_singleton m)

/-- Real-valued form of `measure_orderStat_le_eq_sum` in terms of the common value
`q = P(X_i ≤ a) = F a` of the c.d.f. at the level `a`:
`P(X_{(j+1)} ≤ a) = ∑_{m ≤ j} (n choose m) (1 - q) ^ m q ^ (n - m)`. -/
theorem measureReal_orderStat_le_eq_sum {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {a q : ℝ} (hq : ∀ i, P.real {ω | X i ω ≤ a} = q) {j : ℕ}
    (hj : j < n) :
    P.real {ω | orderStat (fun i => X i ω) j ≤ a} =
      ∑ m ∈ range (j + 1), n.choose m * (1 - q) ^ m * q ^ (n - m) := by
  have i0 : Fin n := ⟨0, by omega⟩
  have hq0 : 0 ≤ q := hq i0 ▸ measureReal_nonneg
  have hq1 : q ≤ 1 := hq i0 ▸ measureReal_le_one
  have h1q : 0 ≤ 1 - q := by linarith
  have hp : ∀ i, P {ω | a < X i ω} = ENNReal.ofReal (1 - q) := by
    intro i
    have hc : {ω | a < X i ω} = {ω | X i ω ≤ a}ᶜ := by ext ω; simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_le (hX i) measurable_const),
      ← ofReal_measureReal, hq i, ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
  have h1p : 1 - ENNReal.ofReal (1 - q) = ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
    rw [sub_sub_cancel]
  rw [measureReal_def, measure_orderStat_le_eq_sum hX hind hp hj, h1p]
  have key : ∀ m, (n.choose m : ENNReal) * ENNReal.ofReal (1 - q) ^ m * ENNReal.ofReal q ^ (n - m)
      = ENNReal.ofReal (n.choose m * (1 - q) ^ m * q ^ (n - m)) := by
    intro m
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow h1q, ENNReal.ofReal_pow hq0, ENNReal.ofReal_natCast]
  simp_rw [key]
  rw [← ENNReal.ofReal_sum_of_nonneg, ENNReal.toReal_ofReal]
  · exact Finset.sum_nonneg fun m _ => by positivity
  · exact fun m _ => by positivity

omit [IsProbabilityMeasure P] in
/-- Real-valued product formula for independent random variables. -/
private lemma measureReal_iInter_preimage_eq_prod {X : Fin n → Ω → ℝ} (hind : iIndepFun X P)
    {s : Fin n → Set ℝ} (hs : ∀ i, MeasurableSet (s i)) :
    P.real (⋂ i ∈ (univ : Finset (Fin n)), X i ⁻¹' s i) = ∏ i, P.real (X i ⁻¹' s i) := by
  rw [measureReal_def, hind.measure_inter_preimage_eq_mul univ (fun i _ => hs i),
    ENNReal.toReal_prod]
  rfl

private lemma exceedCount_eq_zero_iff (x : Fin n → ℝ) (a : ℝ) :
    exceedCount x a = 0 ↔ ∀ i, x i ≤ a := by
  simp [exceedCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private lemma exceedCount_le_one_iff (x : Fin n → ℝ) (a : ℝ) :
    exceedCount x a ≤ 1 ↔ ∀ i l, a < x i → a < x l → i = l := by
  simp only [exceedCount, Finset.card_le_one, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h i l hi hl => h i hi l hl, fun h i hi l hl => h i l hi hl⟩

/-- **Joint law of the two largest order statistics, finite sample.** For independent `X_i`
with common c.d.f. values `q_u = P(X_i ≤ u)` and `q_v = P(X_i ≤ v)` at levels `v ≤ u`,
`P(X_{(1)} ≤ u, X_{(2)} ≤ v) = q_v ^ n + n (q_u - q_v) q_v ^ (n - 1)`: either no observation
exceeds `v`, or exactly one observation lies in `(v, u]` and the others are at most `v`. -/
theorem measureReal_orderStat_zero_le_and_orderStat_one_le {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {u v qu qv : ℝ} (hvu : v ≤ u)
    (hqu : ∀ i, P.real {ω | X i ω ≤ u} = qu) (hqv : ∀ i, P.real {ω | X i ω ≤ v} = qv)
    (hn : 2 ≤ n) :
    P.real {ω | orderStat (fun i => X i ω) 0 ≤ u ∧ orderStat (fun i => X i ω) 1 ≤ v} =
      qv ^ n + n * (qu - qv) * qv ^ (n - 1) := by
  classical
  -- no exceedance of `v`
  set A : Set Ω := ⋂ i ∈ (univ : Finset (Fin n)), X i ⁻¹' Set.Iic v with hA
  -- exactly the `i`-th observation exceeds `v`, and it does not exceed `u`
  set s : Fin n → Fin n → Set ℝ := fun i l => if l = i then Set.Ioc v u else Set.Iic v with hs
  set B : Fin n → Set Ω := fun i => ⋂ l ∈ (univ : Finset (Fin n)), X l ⁻¹' s i l with hB
  have hsm : ∀ i l, MeasurableSet (s i l) := by
    intro i l
    simp only [hs]
    split_ifs
    · exact measurableSet_Ioc
    · exact measurableSet_Iic
  have hmemA : ∀ ω, ω ∈ A ↔ ∀ l, X l ω ≤ v := by
    intro ω; simp [hA]
  have hmemB : ∀ i ω, ω ∈ B i ↔ (v < X i ω ∧ X i ω ≤ u) ∧ ∀ l, l ≠ i → X l ω ≤ v := by
    intro i ω
    simp only [hB, hs, Set.mem_iInter, Set.mem_preimage, Finset.mem_univ, forall_const]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun l hl => by simpa [hl] using h l⟩
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = i
      · subst hl; simpa using h1
      · simpa [hl] using h2 l hl
  have hset : {ω | orderStat (fun i => X i ω) 0 ≤ u ∧ orderStat (fun i => X i ω) 1 ≤ v} =
      A ∪ ⋃ i ∈ (univ : Finset (Fin n)), B i := by
    ext ω
    simp only [Set.mem_ofPred_eq, orderStat_le_iff _ (show 0 < n by omega),
      orderStat_le_iff _ (show 1 < n by omega), Nat.le_zero, exceedCount_eq_zero_iff,
      exceedCount_le_one_iff, Set.mem_union, Set.mem_iUnion, Finset.mem_univ, exists_const,
      hmemA, hmemB]
    constructor
    · rintro ⟨hu, hv⟩
      by_cases h : ∃ i, v < X i ω
      · obtain ⟨i, hi⟩ := h
        refine Or.inr ⟨i, ⟨hi, hu i⟩, fun l hl => ?_⟩
        by_contra hlv
        exact hl (hv l i (lt_of_not_ge hlv) hi)
      · push Not at h
        exact Or.inl h
    · rintro (h | ⟨i, ⟨hi, hiu⟩, hl⟩)
      · exact ⟨fun l => (h l).trans hvu, fun i l hi _ => absurd hi (not_lt.2 (h i))⟩
      · refine ⟨fun l => ?_, fun l l' h1 h2 => ?_⟩
        · by_cases hli : l = i
          · subst hli; exact hiu
          · exact (hl l hli).trans hvu
        · by_contra hne
          by_cases hli : l = i
          · subst hli
            exact absurd h2 (not_lt.2 (hl l' (Ne.symm hne)))
          · exact absurd h1 (not_lt.2 (hl l hli))
  have hAm : MeasurableSet A :=
    MeasurableSet.biInter (Set.to_countable _) fun i _ => hX i measurableSet_Iic
  have hBm : ∀ i, MeasurableSet (B i) := fun i =>
    MeasurableSet.biInter (Set.to_countable _) fun l _ => hX l (hsm i l)
  have hdisjB : Set.PairwiseDisjoint (↑(univ : Finset (Fin n))) B := by
    intro i _ i' _ hii'
    refine Set.disjoint_left.2 fun ω h1 h2 => ?_
    rw [hmemB] at h1 h2
    exact absurd h2.1.1 (not_lt.2 (h1.2 i' (Ne.symm hii')))
  have hdisjAB : Disjoint A (⋃ i ∈ (univ : Finset (Fin n)), B i) := by
    refine Set.disjoint_left.2 fun ω h1 h2 => ?_
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_const] at h2
    obtain ⟨i, hi⟩ := h2
    rw [hmemA] at h1
    rw [hmemB] at hi
    exact absurd hi.1.1 (not_lt.2 (h1 i))
  have hPA : P.real A = qv ^ n := by
    rw [hA, measureReal_iInter_preimage_eq_prod hind (fun _ => measurableSet_Iic)]
    simp only [Set.preimage, Set.mem_Iic]
    simp [hqv]
  have hIoc : ∀ i, P.real (X i ⁻¹' Set.Ioc v u) = qu - qv := by
    intro i
    have : X i ⁻¹' Set.Ioc v u = {ω | X i ω ≤ u} \ {ω | X i ω ≤ v} := by
      ext ω; simp [and_comm]
    have hsub : {ω | X i ω ≤ v} ⊆ {ω | X i ω ≤ u} := fun ω (h : X i ω ≤ v) => h.trans hvu
    rw [this, measureReal_sdiff hsub (measurableSet_le (hX i) measurable_const), hqu, hqv]
  have hPB : ∀ i, P.real (B i) = (qu - qv) * qv ^ (n - 1) := by
    intro i
    rw [hB, measureReal_iInter_preimage_eq_prod hind (hsm i), Fintype.prod_eq_mul_prod_compl i]
    have h2 : ∀ l ∈ ({i}ᶜ : Finset (Fin n)), P.real (X l ⁻¹' s i l) = qv := by
      intro l hl
      have hli : l ≠ i := by simpa using hl
      simp only [hs, hli, ite_false]
      exact hqv l
    rw [Finset.prod_congr rfl h2, prod_const, card_compl, card_singleton, Fintype.card_fin]
    simp only [hs, ite_true]
    rw [hIoc]
  rw [hset, measureReal_union hdisjAB (MeasurableSet.biUnion (Set.to_countable _)
    fun i _ => hBm i) (h₂ := measure_ne_top _ _), measureReal_biUnion_finset hdisjB (fun i _ => hBm i), hPA]
  simp_rw [hPB]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end FiniteSample

/-- An orientation preserving affine map `A` satisfies `A y ≤ x ↔ y ≤ A⁻¹ x`. -/
lemma AffineIncrEquiv.apply_le_iff (A : AffineIncrEquiv) (y x : ℝ) : A y ≤ x ↔ y ≤ A⁻¹ x := by
  constructor
  · intro h
    have := (A⁻¹).mono h
    rwa [← AffineIncrEquiv.mul_apply_eq_comp_apply, inv_mul_cancel,
      AffineIncrEquiv.one_apply] at this
  · intro h
    have := A.mono h
    rwa [← AffineIncrEquiv.mul_apply_eq_comp_apply, mul_inv_cancel,
      AffineIncrEquiv.one_apply] at this

section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Poisson limit of the `k`-th largest order statistic** ([EKM, Theorem 4.2.3],
[LLR, Theorem 2.2.2]). Let `X_0, X_1, …` be iid with c.d.f. `F` and let the levels `u_n` satisfy
`n (1 - F (u_n)) → τ`. Then for every `j`,
`P(X_{(j+1)} ≤ u_n) → e^{-τ} ∑_{m ≤ j} τ ^ m / m!`, where `X_{(j+1)}` is the `(j+1)`-th largest
of `X_0, …, X_{n-1}`. -/
theorem tendsto_measureReal_orderStat_le {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {F : ℝ → ℝ} (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x)
    {u : ℕ → ℝ} {τ : ℝ} (hu : Tendsto (fun n : ℕ => (n : ℝ) * (1 - F (u n))) atTop (𝓝 τ))
    (j : ℕ) :
    Tendsto (fun n : ℕ => P.real {ω | orderStat (fun i : Fin n => X i ω) j ≤ u n}) atTop
      (𝓝 (Real.exp (-τ) * ∑ m ∈ range (j + 1), τ ^ m / m.factorial)) := by
  have heq : (fun n : ℕ => P.real {ω | orderStat (fun i : Fin n => X i ω) j ≤ u n})
      =ᶠ[atTop] fun n => ∑ m ∈ range (j + 1),
        n.choose m * (1 - F (u n)) ^ m * (1 - (1 - F (u n))) ^ (n - m) := by
    filter_upwards [eventually_gt_atTop j] with n hn
    rw [measureReal_orderStat_le_eq_sum (fun i => hX i) (hind.precomp Fin.val_injective)
      (fun i => hF i (u n)) hn]
    simp only [sub_sub_cancel]
  rw [Finset.mul_sum]
  refine Tendsto.congr' heq.symm (tendsto_finsetSum _ fun m _ => ?_)
  rw [← mul_div_assoc]
  exact tendsto_choose_mul_pow_of_tendsto_mul_atTop m hu

/-- **Limit law of the normalized `k`-th largest order statistic** ([EKM, Theorem 4.2.3],
[LLR, Theorem 2.2.2]). If `X_0, X_1, …` are iid with c.d.f. `F` and the normalized maxima
converge at `x`, `((A_n • F) x) ^ n → H x ∈ (0, 1)` (as in the definitions of the maximum
domains of attraction), then
`P(A_n (X_{(j+1)}) ≤ x) → H(x) ∑_{m ≤ j} (-log H(x)) ^ m / m!`. -/
theorem tendsto_measureReal_affine_orderStat_le {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {F G : CumulativeDistributionFunction}
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {As : ℕ → AffineIncrEquiv} {x : ℝ}
    (hGx : G x ∈ Set.Ioo 0 1)
    (h : Tendsto (fun n : ℕ => ((As n • F) x) ^ n) atTop (𝓝 (G x))) (j : ℕ) :
    Tendsto (fun n : ℕ => P.real {ω | As n (orderStat (fun i : Fin n => X i ω) j) ≤ x}) atTop
      (𝓝 (G x * ∑ m ∈ range (j + 1), (-Real.log (G x)) ^ m / m.factorial)) := by
  have h3 := ((tfae_ev_limit_relation As hGx).out 1 3).1 h
  simp only [CumulativeDistributionFunction.mulAction_apply_eq] at h3
  have := tendsto_measureReal_orderStat_le hX hind hF h3 j
  rw [neg_neg, Real.exp_log hGx.1] at this
  refine this.congr fun n => ?_
  congr 1
  ext ω
  exact (AffineIncrEquiv.apply_le_iff _ _ _).symm

/-- **Joint limit law of the two largest order statistics** ([EKM, §4.2], [LLR, Theorem 2.3.2]).
Let `X_0, X_1, …` be iid with c.d.f. `F` and let `v_n ≤ u_n` be levels with
`n (1 - F (u_n)) → τ₁` and `n (1 - F (v_n)) → τ₂`. Then
`P(X_{(1)} ≤ u_n, X_{(2)} ≤ v_n) → e^{-τ₂} (1 + τ₂ - τ₁)`. -/
theorem tendsto_measureReal_orderStat_zero_le_and_orderStat_one_le {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {F : ℝ → ℝ}
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {u v : ℕ → ℝ} (hvu : ∀ᶠ n in atTop, v n ≤ u n)
    {τ₁ τ₂ : ℝ} (hu : Tendsto (fun n : ℕ => (n : ℝ) * (1 - F (u n))) atTop (𝓝 τ₁))
    (hv : Tendsto (fun n : ℕ => (n : ℝ) * (1 - F (v n))) atTop (𝓝 τ₂)) :
    Tendsto (fun n : ℕ => P.real {ω | orderStat (fun i : Fin n => X i ω) 0 ≤ u n ∧
        orderStat (fun i : Fin n => X i ω) 1 ≤ v n}) atTop
      (𝓝 (Real.exp (-τ₂) * (1 + τ₂ - τ₁))) := by
  have heq : (fun n : ℕ => P.real {ω | orderStat (fun i : Fin n => X i ω) 0 ≤ u n ∧
        orderStat (fun i : Fin n => X i ω) 1 ≤ v n}) =ᶠ[atTop]
      fun n => F (v n) ^ n + n * (F (u n) - F (v n)) * F (v n) ^ (n - 1) := by
    filter_upwards [eventually_ge_atTop 2, hvu] with n hn hvun
    exact measureReal_orderStat_zero_le_and_orderStat_one_le (fun i => hX i)
      (hind.precomp Fin.val_injective) hvun (fun i => hF i (u n)) (fun i => hF i (v n)) hn
  refine Tendsto.congr' heq.symm ?_
  -- `F (v n) ^ n → e^{-τ₂}`
  have hpow : Tendsto (fun n : ℕ => F (v n) ^ n) atTop (𝓝 (Real.exp (-τ₂))) := by
    have hg : Tendsto (fun n : ℕ => (n : ℝ) * (-(1 - F (v n)))) atTop (𝓝 (-τ₂)) :=
      hv.neg.congr fun n => by ring
    refine (Real.tendsto_one_add_pow_exp_of_tendsto hg).congr fun n => ?_
    rw [show 1 + -(1 - F (v n)) = F (v n) by ring]
  have hv1 : Tendsto (fun n : ℕ => F (v n)) atTop (𝓝 1) := by
    have := tendsto_zero_of_tendsto_mul_atTop hv
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hpow' : Tendsto (fun n : ℕ => F (v n) ^ (n - 1)) atTop (𝓝 (Real.exp (-τ₂))) := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < F (v n) := hv1.eventually (lt_mem_nhds one_pos)
    have := hpow.div hv1 one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
    show F (v n) ^ n / F (v n) = F (v n) ^ (n - 1)
    rw [div_eq_iff hn.ne', ← pow_succ, Nat.sub_add_cancel hn1]
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ) * (F (u n) - F (v n))) atTop (𝓝 (τ₂ - τ₁)) := by
    refine (hv.sub hu).congr fun n => ?_
    ring
  rw [show Real.exp (-τ₂) * (1 + τ₂ - τ₁) =
    Real.exp (-τ₂) + (τ₂ - τ₁) * Real.exp (-τ₂) by ring]
  exact hpow.add (hdiff.mul hpow')

/-- **Joint limit law of the two largest normalized order statistics** ([EKM, §4.2],
[LLR, Theorem 2.3.2]). If `X_0, X_1, …` are iid with c.d.f. `F`, `y ≤ x`, and the normalized
maxima converge at `x` and at `y`, `((A_n • F) z) ^ n → H z ∈ (0, 1)` for `z = x, y`, then
`P(A_n (X_{(1)}) ≤ x, A_n (X_{(2)}) ≤ y) → H(y) (1 + log H(x) - log H(y))`. -/
theorem tendsto_measureReal_affine_orderStat_zero_one {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {F G : CumulativeDistributionFunction}
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {As : ℕ → AffineIncrEquiv} {x y : ℝ}
    (hyx : y ≤ x) (hGx : G x ∈ Set.Ioo 0 1) (hGy : G y ∈ Set.Ioo 0 1)
    (hx : Tendsto (fun n : ℕ => ((As n • F) x) ^ n) atTop (𝓝 (G x)))
    (hy : Tendsto (fun n : ℕ => ((As n • F) y) ^ n) atTop (𝓝 (G y))) :
    Tendsto (fun n : ℕ => P.real {ω | As n (orderStat (fun i : Fin n => X i ω) 0) ≤ x ∧
        As n (orderStat (fun i : Fin n => X i ω) 1) ≤ y}) atTop
      (𝓝 (G y * (1 + Real.log (G x) - Real.log (G y)))) := by
  have hx3 := ((tfae_ev_limit_relation As hGx).out 1 3).1 hx
  have hy3 := ((tfae_ev_limit_relation As hGy).out 1 3).1 hy
  simp only [CumulativeDistributionFunction.mulAction_apply_eq] at hx3 hy3
  have := tendsto_measureReal_orderStat_zero_le_and_orderStat_one_le hX hind hF
    (Eventually.of_forall fun n => (As n)⁻¹.mono hyx) hx3 hy3
  rw [neg_neg, Real.exp_log hGy.1] at this
  rw [show G y * (1 + Real.log (G x) - Real.log (G y)) =
    G y * (1 + -Real.log (G y) - -Real.log (G x)) by ring]
  refine this.congr fun n => ?_
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, AffineIncrEquiv.apply_le_iff]

end Limit

end ExtremeValueTheory
