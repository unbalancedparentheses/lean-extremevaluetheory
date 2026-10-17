/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.Process.Stationary
import ExtremeValueTheory.ForMathlib.MeasureTheory.Measure.Bonferroni
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Extremes of stationary sequences: Leadbetter's conditions `D(uₙ)` and `D'(uₙ)`

Let `(X t)_{t ∈ ℕ}` be a stationary real sequence and `M n = max (X 0, …, X (n - 1))`. We
formalize Leadbetter's mixing condition `D(uₙ)` and anti-clustering condition `D'(uₙ)`, and prove

* the block approximation `P(M n ≤ uₙ) - P(M ⌊n/k⌋ ≤ uₙ)^k → 0` under `D(uₙ)`
  [LLR, Lemma 3.3.2], [EKM, Lemma 4.4.? (block argument)];
* **Leadbetter's theorem**: under `D(uₙ)`, `D'(uₙ)` and `n P(X 0 > uₙ) → τ`,
  `P(M n ≤ uₙ) → exp (-τ)` [LLR, Theorem 3.4.1], [EKM, Theorem 4.4.3];
* the lower bound `liminf P(M n ≤ uₙ) ≥ exp (-τ)` under `D(uₙ)` alone.

## Main definitions

* `ExtremeValueTheory.partialMax X n`: the partial maximum `M n = max_{t < n} X t`.
* `ExtremeValueTheory.maxLE X A u`: the event `{max_{t ∈ A} X t ≤ u}`.
* `ExtremeValueTheory.ConditionD X P u`: Leadbetter's condition `D(uₙ)`.
* `ExtremeValueTheory.ConditionD' X P u`: Leadbetter's condition `D'(uₙ)`.

## Main results

* `ExtremeValueTheory.tendsto_measureReal_partialMax_sub_pow`: the block approximation.
* `ExtremeValueTheory.tendsto_measureReal_partialMax_le_exp`: Leadbetter's theorem.

## Conventions

Time is indexed from `0`, so `X 0` plays the role of `X₁` in [LLR] and [EKM], and the lags
`1 ≤ j < ⌊n/k⌋` in `D'(uₙ)` correspond to the indices `2 ≤ j ≤ ⌊n/k⌋` there.

## References

* M. R. Leadbetter, G. Lindgren and H. Rootzén, *Extremes and Related Properties of Random
  Sequences and Processes*, Springer (1983), Chapter 3 [LLR].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Section 4.4 [EKM].
* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020), Chapter 7.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ### Partial maxima and block events -/

/-- The partial maximum `M n = max (X 0, …, X (n - 1))` of a sequence. For `n = 0` (an empty
maximum) it takes the junk value `X 0 ω`. -/
noncomputable def partialMax (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  partialSups (fun t ↦ X t ω) (n - 1)

lemma partialMax_le_iff {n : ℕ} (hn : 0 < n) {ω : Ω} {u : ℝ} :
    partialMax X n ω ≤ u ↔ ∀ t < n, X t ω ≤ u := by
  simp only [partialMax, partialSups_le_iff]
  exact ⟨fun h t ht ↦ h t (by omega), fun h t ht ↦ h t (by omega)⟩

/-- The event `{max_{t ∈ A} X t ≤ u}` that the sequence does not exceed `u` on the index set
`A`. -/
def maxLE (X : ℕ → Ω → ℝ) (A : Finset ℕ) (u : ℝ) : Set Ω := {ω | ∀ t ∈ A, X t ω ≤ u}

lemma measurableSet_maxLE (hX : ∀ t, Measurable (X t)) (A : Finset ℕ) (u : ℝ) :
    MeasurableSet (maxLE X A u) := by
  have : maxLE X A u = ⋂ t ∈ A, {ω | X t ω ≤ u} := by ext; simp [maxLE]
  rw [this]
  exact Finset.measurableSet_biInter _ fun t _ ↦ measurableSet_le (hX t) measurable_const

@[simp] lemma maxLE_empty (u : ℝ) : maxLE X ∅ u = Set.univ := by ext; simp [maxLE]

lemma maxLE_union (A B : Finset ℕ) (u : ℝ) :
    maxLE X (A ∪ B) u = maxLE X A u ∩ maxLE X B u := by
  ext ω; simp only [maxLE, mem_union, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun h ↦ ⟨fun t ht ↦ h t (Or.inl ht), fun t ht ↦ h t (Or.inr ht)⟩,
    fun h t ht ↦ ht.elim (h.1 t) (h.2 t)⟩

lemma maxLE_anti {A B : Finset ℕ} (h : A ⊆ B) (u : ℝ) : maxLE X B u ⊆ maxLE X A u :=
  fun _ hω t ht ↦ hω t (h ht)

lemma measureReal_partialMax_le {n : ℕ} (hn : 0 < n) (u : ℝ) :
    P.real {ω | partialMax X n ω ≤ u} = P.real (maxLE X (range n) u) := by
  congr 1; ext ω; simp [maxLE, partialMax_le_iff hn]

/-- The complement of `{max_{t < r} X t ≤ u}` is the union of the exceedance events. -/
lemma maxLE_range_eq_compl (r : ℕ) (u : ℝ) :
    maxLE X (range r) u = (⋃ t ∈ range r, {ω | u < X t ω})ᶜ := by
  ext ω; simp [maxLE]

/-! ### Consequences of stationarity -/

section Stationary



lemma _root_.ProbabilityTheory.IsStationary.measureReal_lt_eq (hs : IsStationary X P) (hX : ∀ t, Measurable (X t))
    (t : ℕ) (u : ℝ) : P.real {ω | u < X t ω} = P.real {ω | u < X 0 ω} := by
  have := (hs.identDistrib hX t).measure_mem_eq (measurableSet_Ioi (a := u))
  simp only [Measure.real]
  exact congrArg ENNReal.toReal this

/-- Block events of a stationary sequence are shift invariant. -/
lemma _root_.ProbabilityTheory.IsStationary.measureReal_maxLE_Ico (hs : IsStationary X P) (hX : ∀ t, Measurable (X t))
    (s m : ℕ) (u : ℝ) :
    P.real (maxLE X (Ico s (s + m)) u) = P.real (maxLE X (range m) u) := by
  set C : Set (ℕ → ℝ) := {x | ∀ t ∈ range m, x t ≤ u}
  have hC : MeasurableSet C := by
    have : C = ⋂ t ∈ range m, {x | x t ≤ u} := by ext; simp [C]
    rw [this]
    exact Finset.measurableSet_biInter _ fun t _ ↦
      measurableSet_le (measurable_pi_apply t) measurable_const
  have e1 : maxLE X (Ico s (s + m)) u = (fun ω n ↦ X (n + s) ω) ⁻¹' C := by
    ext ω; simp only [maxLE, mem_Ico, Set.mem_ofPred_eq, Set.mem_preimage, C, mem_range]
    refine ⟨fun h t ht ↦ h (t + s) ⟨by omega, by omega⟩, fun h t ht ↦ ?_⟩
    have := h (t - s) (by omega)
    rwa [Nat.sub_add_cancel ht.1] at this
  have e2 : maxLE X (range m) u = (fun ω n ↦ X n ω) ⁻¹' C := by
    ext ω; simp [maxLE, C]
  rw [e1, e2, hs.measureReal_preimage_shift hX s hC]

/-- Joint exceedance probabilities of a stationary sequence depend only on the lag. -/
lemma _root_.ProbabilityTheory.IsStationary.measureReal_lt_and_lt (hs : IsStationary X P) (hX : ∀ t, Measurable (X t))
    {i j : ℕ} (hij : i ≤ j) (u : ℝ) :
    P.real {ω | u < X i ω ∧ u < X j ω} = P.real {ω | u < X 0 ω ∧ u < X (j - i) ω} := by
  set C : Set (ℕ → ℝ) := {x | u < x 0 ∧ u < x (j - i)}
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_lt measurable_const (measurable_pi_apply _))
  have e1 : {ω | u < X i ω ∧ u < X j ω} = (fun ω n ↦ X (n + i) ω) ⁻¹' C := by
    ext ω; simp [C, Nat.sub_add_cancel hij]
  have e2 : {ω | u < X 0 ω ∧ u < X (j - i) ω} = (fun ω n ↦ X n ω) ⁻¹' C := rfl
  rw [e1, e2, hs.measureReal_preimage_shift hX i hC]

/-- If `A ⊆ B ⊆ A ∪ S`, then `P(max_A X ≤ u) - P(max_B X ≤ u) ≤ #S P(X 0 > u)`. -/
lemma _root_.ProbabilityTheory.IsStationary.measureReal_maxLE_sub_le [IsFiniteMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {A B S : Finset ℕ} (hAB : A ⊆ B) (hBS : B ⊆ A ∪ S) (u : ℝ) :
    0 ≤ P.real (maxLE X A u) - P.real (maxLE X B u) ∧
      P.real (maxLE X A u) - P.real (maxLE X B u) ≤ #S * P.real {ω | u < X 0 ω} := by
  have hsub : maxLE X B u ⊆ maxLE X A u := maxLE_anti hAB u
  refine ⟨sub_nonneg.2 (measureReal_mono hsub), ?_⟩
  rw [← measureReal_sdiff hsub (measurableSet_maxLE hX B u)]
  calc P.real (maxLE X A u \ maxLE X B u)
      ≤ P.real (⋃ t ∈ S, {ω | u < X t ω}) := by
        refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
        simp only [maxLE, Set.mem_sdiff, Set.mem_ofPred_eq, not_forall, not_le] at hω
        obtain ⟨hA, t, htB, ht⟩ := hω
        have htS : t ∈ S := by
          rcases mem_union.1 (hBS htB) with h | h
          · exact absurd (hA t h) (not_le.2 ht)
          · exact h
        exact Set.mem_biUnion htS ht
    _ ≤ ∑ t ∈ S, P.real {ω | u < X t ω} := measureReal_biUnion_finset_le _ _
    _ = #S * P.real {ω | u < X 0 ω} := by
        simp [hs.measureReal_lt_eq hX]

lemma _root_.ProbabilityTheory.IsStationary.abs_measureReal_maxLE_sub_le [IsFiniteMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {A B S : Finset ℕ} (hAB : A ⊆ B) (hBS : B ⊆ A ∪ S) (u : ℝ) :
    |P.real (maxLE X B u) - P.real (maxLE X A u)| ≤ #S * P.real {ω | u < X 0 ω} := by
  obtain ⟨h1, h2⟩ := hs.measureReal_maxLE_sub_le hX hAB hBS u
  rw [abs_sub_comm, abs_of_nonneg h1]
  exact h2

end Stationary

/-! ### The block approximation -/

/-- `|a ^ k - b ^ k| ≤ k |a - b|` for `a, b ∈ [0, 1]`. -/
lemma abs_pow_sub_pow_le_of_mem_Icc {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) : |a ^ k - b ^ k| ≤ k * |a - b| := by
  have hmax : max |a| |b| ^ (k - 1) ≤ 1 :=
    pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
      (max_le (by rw [abs_of_nonneg ha.1]; exact ha.2) (by rw [abs_of_nonneg hb.1]; exact hb.2))
  have h0 : 0 ≤ |a - b| * k := mul_nonneg (abs_nonneg _) k.cast_nonneg
  calc |a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1) := abs_pow_sub_pow_le a b k
    _ ≤ |a - b| * k * 1 := mul_le_mul_of_nonneg_left hmax h0
    _ = k * |a - b| := by ring

lemma measureReal_maxLE_mem_Icc [IsProbabilityMeasure P] (A : Finset ℕ) (u : ℝ) :
    P.real (maxLE X A u) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- **The block estimate** behind [LLR, Lemma 3.3.2]: split `{0, …, n - 1}` into `k` blocks of
length `r = ⌊n/k⌋`, remove the last `l` indices of every block, and use the mixing bound `α`
for index sets at distance `l` to factor the probability. -/
theorem _root_.ProbabilityTheory.IsStationary.abs_measureReal_maxLE_range_sub_pow_le
    [IsProbabilityMeasure P] (hs : IsStationary X P) (hX : ∀ t, Measurable (X t)) {u α : ℝ}
    {n k l : ℕ} (hk : 0 < k)
    (hD : ∀ A B : Finset ℕ, A ⊆ range n → B ⊆ range n → (∀ a ∈ A, ∀ b ∈ B, a + l ≤ b) →
      |P.real (maxLE X (A ∪ B) u) - P.real (maxLE X A u) * P.real (maxLE X B u)| ≤ α) :
    |P.real (maxLE X (range n) u) - P.real (maxLE X (range (n / k)) u) ^ k| ≤
      (2 * k * l + k) * P.real {ω | u < X 0 ω} + k * α := by
  set r := n / k with hr
  set p := P.real {ω | u < X 0 ω} with hp
  have hp0 : 0 ≤ p := measureReal_nonneg
  set I : ℕ → Finset ℕ := fun j ↦ Ico (j * r) (j * r + (r - l)) with hI
  set U : ℕ → Finset ℕ := fun m ↦ (range m).biUnion I with hU
  have hkr : k * r ≤ n := by rw [hr, mul_comm]; exact Nat.div_mul_le_self n k
  have hQ : ∀ j, P.real (maxLE X (I j) u) = P.real (maxLE X (range (r - l)) u) :=
    fun j ↦ hs.measureReal_maxLE_Ico hX _ _ u
  have hQ0 := measureReal_maxLE_mem_Icc (P := P) (X := X) (range (r - l)) u
  have hIsub : ∀ j, j < k → I j ⊆ range n := by
    intro j hj t ht
    simp only [hI, mem_Ico] at ht
    have h1 : (j + 1) * r ≤ k * r := Nat.mul_le_mul_right _ hj
    have h2 : (j + 1) * r = j * r + r := by ring
    rw [mem_range]; omega
  have hUsub : ∀ m, m ≤ k → U m ⊆ range n := by
    intro m hm t ht
    simp only [hU, mem_biUnion, mem_range] at ht
    obtain ⟨j, hj, htj⟩ := ht
    exact hIsub j (by omega) htj
  -- Step 1: factorization over the `k` shortened blocks.
  have hstep1 : ∀ m, m ≤ k →
      |P.real (maxLE X (U m) u) - P.real (maxLE X (range (r - l)) u) ^ m| ≤ m * α := by
    intro m
    induction m with
    | zero => intro _; simp [hU]
    | succ m ih =>
      intro hm
      have hUs : U (m + 1) = U m ∪ I m := by
        simp only [hU, range_add_one, biUnion_insert, union_comm]
      have hgap : ∀ a ∈ U m, ∀ b ∈ I m, a + l ≤ b := by
        intro a ha b hb
        simp only [hU, mem_biUnion, mem_range, hI, mem_Ico] at ha hb
        obtain ⟨j, hj, ha1, ha2⟩ := ha
        have h1 : (j + 1) * r ≤ m * r := Nat.mul_le_mul_right _ hj
        have h2 : (j + 1) * r = j * r + r := by ring
        omega
      have hDm := hD (U m) (I m) (hUsub m (by omega)) (hIsub m (by omega)) hgap
      have hih := ih (by omega)
      rw [hQ m] at hDm
      rw [hUs, pow_succ]
      set Q := P.real (maxLE X (range (r - l)) u)
      set y := P.real (maxLE X (U m) u)
      set x := P.real (maxLE X (U m ∪ I m) u)
      have e : x - Q ^ m * Q = (x - y * Q) + (y - Q ^ m) * Q := by ring
      have h3 : |(y - Q ^ m) * Q| ≤ m * α := by
        rw [abs_mul, abs_of_nonneg hQ0.1]
        exact (mul_le_of_le_one_right (abs_nonneg _) hQ0.2).trans hih
      rw [e]
      calc |x - y * Q + (y - Q ^ m) * Q| ≤ |x - y * Q| + |(y - Q ^ m) * Q| := abs_add_le _ _
        _ ≤ α + m * α := add_le_add hDm h3
        _ = ((m + 1 : ℕ) : ℝ) * α := by push_cast; ring
  -- Step 2: the removed short blocks and the remainder have small probability.
  set S : Finset ℕ := (range k).biUnion (fun j ↦ Ico (j * r + (r - l)) (j * r + r)) ∪
    Ico (k * r) n with hS
  have hcover : range n ⊆ U k ∪ S := by
    intro t ht
    rw [mem_range] at ht
    rw [mem_union]
    by_cases h : k * r ≤ t
    · exact Or.inr (mem_union.2 (Or.inr (mem_Ico.2 ⟨h, ht⟩)))
    · push Not at h
      have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · rw [h0, mul_zero] at h; omega
        · exact h0
      have hj : t / r < k := (Nat.div_lt_iff_lt_mul hr0).2 h
      have h1 : t / r * r ≤ t := Nat.div_mul_le_self t r
      have h2 : t < t / r * r + r := Nat.lt_div_mul_add hr0
      by_cases h3 : t < t / r * r + (r - l)
      · left
        simp only [hU, hI, mem_biUnion, mem_range, mem_Ico]
        exact ⟨t / r, hj, h1, h3⟩
      · right
        refine mem_union.2 (Or.inl ?_)
        simp only [mem_biUnion, mem_range, mem_Ico]
        exact ⟨t / r, hj, by omega, h2⟩
  have hcardS : (#S : ℝ) ≤ k * l + k := by
    have h1 : #((range k).biUnion (fun j ↦ Ico (j * r + (r - l)) (j * r + r))) ≤ k * l := by
      refine (card_biUnion_le).trans ?_
      calc ∑ j ∈ range k, #(Ico (j * r + (r - l)) (j * r + r)) ≤ ∑ _j ∈ range k, l := by
            refine sum_le_sum fun j _ ↦ ?_
            rw [Nat.card_Ico]; omega
        _ = k * l := by simp
    have h2 : #(Ico (k * r) n) ≤ k := by
      rw [Nat.card_Ico]
      have := Nat.div_add_mod n k
      have := Nat.mod_lt n hk
      rw [hr]; omega
    have : #S ≤ k * l + k := (card_union_le _ _).trans (add_le_add h1 h2)
    exact_mod_cast this
  have hstep2 : |P.real (maxLE X (range n) u) - P.real (maxLE X (U k) u)| ≤ (k * l + k) * p :=
    (hs.abs_measureReal_maxLE_sub_le hX (hUsub k le_rfl) hcover u).trans
      (mul_le_mul_of_nonneg_right hcardS hp0)
  -- Step 3: shortening one block costs at most `l p`.
  have hstep3 : |P.real (maxLE X (range r) u) - P.real (maxLE X (range (r - l)) u)| ≤ l * p := by
    have hsub : range (r - l) ⊆ range r := range_subset_range.2 (Nat.sub_le r l)
    have hcov : range r ⊆ range (r - l) ∪ Ico (r - l) r := by
      intro t ht; rw [mem_range] at ht; rw [mem_union, mem_range, mem_Ico]; omega
    refine (hs.abs_measureReal_maxLE_sub_le hX hsub hcov u).trans
      (mul_le_mul_of_nonneg_right ?_ hp0)
    rw [Nat.card_Ico]; exact_mod_cast (show r - (r - l) ≤ l by omega)
  have hstep4 : |P.real (maxLE X (range (r - l)) u) ^ k - P.real (maxLE X (range r) u) ^ k| ≤
      k * (l * p) := by
    refine (abs_pow_sub_pow_le_of_mem_Icc hQ0 (measureReal_maxLE_mem_Icc _ u) k).trans ?_
    rw [abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hstep3 k.cast_nonneg
  have h1 := hstep1 k le_rfl
  calc |P.real (maxLE X (range n) u) - P.real (maxLE X (range r) u) ^ k|
      ≤ |P.real (maxLE X (range n) u) - P.real (maxLE X (U k) u)|
        + |P.real (maxLE X (U k) u) - P.real (maxLE X (range (r - l)) u) ^ k|
        + |P.real (maxLE X (range (r - l)) u) ^ k - P.real (maxLE X (range r) u) ^ k| :=
        by linarith [abs_sub_le (P.real (maxLE X (range n) u)) (P.real (maxLE X (U k) u))
              (P.real (maxLE X (range r) u) ^ k),
            abs_sub_le (P.real (maxLE X (U k) u)) (P.real (maxLE X (range (r - l)) u) ^ k)
              (P.real (maxLE X (range r) u) ^ k)]
    _ ≤ (k * l + k) * p + k * α + k * (l * p) := by gcongr
    _ = (2 * k * l + k) * p + k * α := by ring

/-! ### Leadbetter's conditions -/

/-- **Leadbetter's mixing condition `D(uₙ)`** [LLR, §3.2], [EKM, Condition 4.4.2]: there are
gaps `lₙ = o(n)` and mixing coefficients `αₙ → 0` such that for all index sets
`A, B ⊆ {0, …, n - 1}` separated by at least `lₙ` (every element of `B` exceeds every element of
`A` by at least `lₙ`),
`|P(max_{A ∪ B} X ≤ uₙ) - P(max_A X ≤ uₙ) P(max_B X ≤ uₙ)| ≤ αₙ`. -/
def ConditionD (X : ℕ → Ω → ℝ) (P : Measure Ω) (u : ℕ → ℝ) : Prop :=
  ∃ (l : ℕ → ℕ) (α : ℕ → ℝ), Tendsto (fun n : ℕ ↦ (l n : ℝ) / n) atTop (𝓝 0) ∧
    Tendsto α atTop (𝓝 0) ∧
    ∀ n (A B : Finset ℕ), A ⊆ range n → B ⊆ range n → (∀ a ∈ A, ∀ b ∈ B, a + l n ≤ b) →
      |P.real (maxLE X (A ∪ B) (u n)) - P.real (maxLE X A (u n)) * P.real (maxLE X B (u n))|
        ≤ α n

/-- **Leadbetter's anti-clustering condition `D'(uₙ)`** [LLR, (3.4.3)], [EKM, Condition 4.4.4]:
`limsup_{n → ∞} n ∑_{1 ≤ j < ⌊n/k⌋} P(X 0 > uₙ, X j > uₙ) → 0` as `k → ∞`. Since the terms are
nonnegative, we state it as: for every `ε > 0` there is `k₀` such that for every `k ≥ k₀`,
eventually in `n` the sum is at most `ε`. -/
def ConditionD' (X : ℕ → Ω → ℝ) (P : Measure Ω) (u : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ᶠ n : ℕ in atTop,
    (n : ℝ) * ∑ j ∈ Ico 1 (n / k), P.real {ω | u n < X 0 ω ∧ u n < X j ω} ≤ ε

/-! ### The block approximation and Leadbetter's theorem -/

/-- If `n pₙ → τ` then `pₙ → 0`. -/
lemma tendsto_zero_of_tendsto_natCast_mul' {p : ℕ → ℝ} {τ : ℝ}
    (h : Tendsto (fun n : ℕ ↦ n * p n) atTop (𝓝 τ)) : Tendsto p atTop (𝓝 0) := by
  have := h.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Block approximation** [LLR, Lemma 3.3.2]: under `D(uₙ)` and `n P(X 0 > uₙ) → τ`, for
every fixed `k ≥ 1`, `P(M n ≤ uₙ) - P(M ⌊n/k⌋ ≤ uₙ) ^ k → 0`. -/
theorem tendsto_measureReal_partialMax_sub_pow [IsProbabilityMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {u : ℕ → ℝ} (hD : ConditionD X P u) {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ)) {k : ℕ}
    (hk : 0 < k) :
    Tendsto (fun n ↦ P.real {ω | partialMax X n ω ≤ u n} -
      P.real {ω | partialMax X (n / k) ω ≤ u n} ^ k) atTop (𝓝 0) := by
  obtain ⟨l, α, hl, hα, hDn⟩ := hD
  have hp := tendsto_zero_of_tendsto_natCast_mul' hτ
  have hlp : Tendsto (fun n ↦ (l n : ℝ) * P.real {ω | u n < X 0 ω}) atTop (𝓝 0) := by
    have := hl.mul hτ
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hbound : Tendsto (fun n ↦ (2 * k * l n + k) * P.real {ω | u n < X 0 ω} + k * α n)
      atTop (𝓝 0) := by
    have := ((hlp.const_mul (2 * (k : ℝ))).add (hp.const_mul (k : ℝ))).add (hα.const_mul (k : ℝ))
    simp only [mul_zero, add_zero] at this
    exact this.congr fun n ↦ by ring
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [Real.norm_eq_abs, measureReal_partialMax_le (by omega),
    measureReal_partialMax_le (Nat.div_pos hn hk)]
  exact hs.abs_measureReal_maxLE_range_sub_pow_le hX hk (hDn n)

/-- **Bonferroni bounds** for the block maximum of a stationary sequence:
`1 - r p ≤ P(M r ≤ u) ≤ 1 - r p + r ∑_{1 ≤ j < r} P(X 0 > u, X j > u)`, `p = P(X 0 > u)`. -/
theorem _root_.ProbabilityTheory.IsStationary.measureReal_maxLE_range_bounds
    [IsProbabilityMeasure P] (hs : IsStationary X P) (hX : ∀ t, Measurable (X t)) (r : ℕ)
    (u : ℝ) :
    1 - r * P.real {ω | u < X 0 ω} ≤ P.real (maxLE X (range r) u) ∧
      P.real (maxLE X (range r) u) ≤ 1 - r * P.real {ω | u < X 0 ω} +
        r * ∑ j ∈ Ico 1 r, P.real {ω | u < X 0 ω ∧ u < X j ω} := by
  constructor
  · have := (hs.measureReal_maxLE_sub_le hX (empty_subset (range r))
      (show range r ⊆ ∅ ∪ range r by simp) u).2
    simp only [maxLE_empty, probReal_univ, card_range] at this
    linarith
  · have hA : ∀ t, MeasurableSet {ω | u < X t ω} :=
      fun t ↦ measurableSet_lt measurable_const (hX t)
    have hBon := sum_measureReal_sub_sum_inter_le_measureReal_biUnion (μ := P) hA r
    have hcompl : P.real (maxLE X (range r) u) =
        1 - P.real (⋃ t ∈ range r, {ω | u < X t ω}) := by
      rw [maxLE_range_eq_compl, probReal_compl_eq_one_sub
        (Finset.measurableSet_biUnion _ fun t _ ↦ hA t)]
    have hsum1 : ∑ i ∈ range r, P.real {ω | u < X i ω} = r * P.real {ω | u < X 0 ω} := by
      simp [hs.measureReal_lt_eq hX]
    set g : ℕ → ℝ := fun j ↦ P.real {ω | u < X 0 ω ∧ u < X j ω} with hg
    have hinner : ∀ t ∈ range r,
        ∑ i ∈ range t, P.real ({ω | u < X i ω} ∩ {ω | u < X t ω}) ≤ ∑ j ∈ Ico 1 r, g j := by
      intro t ht
      rw [mem_range] at ht
      calc ∑ i ∈ range t, P.real ({ω | u < X i ω} ∩ {ω | u < X t ω})
          = ∑ i ∈ range t, g (t - i) := by
            refine sum_congr rfl fun i hi ↦ ?_
            rw [mem_range] at hi
            exact hs.measureReal_lt_and_lt hX hi.le u
        _ = ∑ j ∈ Ico 1 (t + 1), g j := by
            refine sum_nbij' (fun i ↦ t - i) (fun j ↦ t - j) ?_ ?_ ?_ ?_ ?_
            · intro i hi; simp at hi ⊢; omega
            · intro j hj; simp at hj ⊢; omega
            · intro i hi; simp at hi; omega
            · intro j hj; simp at hj; omega
            · intro i _; rfl
        _ ≤ ∑ j ∈ Ico 1 r, g j :=
            sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl (by omega))
              fun _ _ _ ↦ measureReal_nonneg
    have hdouble : ∑ t ∈ range r, ∑ i ∈ range t,
        P.real ({ω | u < X i ω} ∩ {ω | u < X t ω}) ≤ r * ∑ j ∈ Ico 1 r, g j := by
      calc _ ≤ ∑ _t ∈ range r, ∑ j ∈ Ico 1 r, g j := sum_le_sum hinner
        _ = r * ∑ j ∈ Ico 1 r, g j := by simp
    rw [hcompl]
    linarith

/-- **Leadbetter's theorem** [LLR, Theorem 3.4.1], [EKM, Theorem 4.4.3]: for a stationary
sequence satisfying `D(uₙ)` and `D'(uₙ)` with `n P(X 0 > uₙ) → τ`, `P(M n ≤ uₙ) → exp (-τ)`,
exactly as for an iid sequence. -/
theorem tendsto_measureReal_partialMax_le_exp [IsProbabilityMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {u : ℕ → ℝ} (hD : ConditionD X P u) (hD' : ConditionD' X P u)
    {τ : ℝ} (hτ : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ)) :
    Tendsto (fun n ↦ P.real {ω | partialMax X n ω ≤ u n}) atTop (𝓝 (Real.exp (-τ))) := by
  have hp := tendsto_zero_of_tendsto_natCast_mul' hτ
  have hrp : ∀ k : ℕ, 0 < k →
      Tendsto (fun n ↦ ((n / k : ℕ) : ℝ) * P.real {ω | u n < X 0 ω}) atTop (𝓝 (τ / k)) := by
    intro k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hup : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω} / k) atTop (𝓝 (τ / k)) :=
      hτ.div_const _
    have hlow : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω} / k -
        P.real {ω | u n < X 0 ω}) atTop (𝓝 (τ / k)) := by
      simpa using hup.sub hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n ↦ ?_) (fun n ↦ ?_)
    · have h : n < n / k * k + k := Nat.lt_div_mul_add hk
      have h' : (n : ℝ) < ((n / k : ℕ) : ℝ) * k + k := by exact_mod_cast h
      have h'' : (n : ℝ) / k - 1 ≤ ((n / k : ℕ) : ℝ) := by
        rw [div_sub_one hk'.ne', div_le_iff₀ hk']; linarith
      have e : (n : ℝ) * P.real {ω | u n < X 0 ω} / k - P.real {ω | u n < X 0 ω} =
          ((n : ℝ) / k - 1) * P.real {ω | u n < X 0 ω} := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h'' measureReal_nonneg
    · have h : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
      have e : (n : ℝ) * P.real {ω | u n < X 0 ω} / k =
          ((n : ℝ) / k) * P.real {ω | u n < X 0 ω} := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h measureReal_nonneg
  rw [tendsto_order]
  constructor
  · -- lower bound: only `D(uₙ)` is used
    intro a ha
    have hlim := Real.tendsto_one_add_div_pow_exp (-τ)
    obtain ⟨k, hk1, hkτ, hka⟩ : ∃ k : ℕ, 0 < k ∧ τ < k ∧ a < (1 + -τ / k) ^ k :=
      ((eventually_gt_atTop 0).and ((tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop τ)).and (hlim.eventually (lt_mem_nhds ha)))).exists
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk1
    have hblock := tendsto_measureReal_partialMax_sub_pow hs hX hD hτ hk1
    have hlow : Tendsto (fun n ↦ (1 - ((n / k : ℕ) : ℝ) * P.real {ω | u n < X 0 ω}) ^ k +
        (P.real {ω | partialMax X n ω ≤ u n} - P.real {ω | partialMax X (n / k) ω ≤ u n} ^ k))
        atTop (𝓝 ((1 + -τ / k) ^ k)) := by
      have := (((hrp k hk1).const_sub 1).pow k).add hblock
      rw [add_zero] at this
      convert this using 3
      ring
    have hτk : τ / k < 1 := by rw [div_lt_one hk']; exact hkτ
    filter_upwards [hlow.eventually (lt_mem_nhds hka), eventually_ge_atTop k,
      (hrp k hk1).eventually (gt_mem_nhds hτk)] with n h1 h2 h3
    have hn : 0 < n / k := Nat.div_pos h2 hk1
    have hB := (hs.measureReal_maxLE_range_bounds hX (n / k) (u n)).1
    rw [← measureReal_partialMax_le hn] at hB
    have := pow_le_pow_left₀ (by linarith) hB k
    linarith
  · -- upper bound: uses `D'(uₙ)`
    intro b hb
    have hb0 : 0 < b := (Real.exp_pos _).trans hb
    have hlogb : -τ < Real.log b := by rwa [Real.lt_log_iff_exp_lt hb0]
    set ε := (Real.log b + τ) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hεb : Real.exp (-τ + ε) < b := by
      rw [← Real.exp_log hb0]
      exact Real.exp_lt_exp.2 (by rw [hεdef]; linarith)
    obtain ⟨k₀, hk₀⟩ := hD' ε hε
    set k := max k₀ (⌈τ⌉₊ + 1) with hkdef
    have hk1 : 0 < k := lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkτ : τ < k := by
      have h1 : τ ≤ ⌈τ⌉₊ := Nat.le_ceil τ
      have h2 : ((⌈τ⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast le_max_right _ _
      push_cast at h2
      linarith
    have hblock := tendsto_measureReal_partialMax_sub_pow hs hX hD hτ hk1
    have hup : Tendsto (fun n ↦
        (1 - ((n / k : ℕ) : ℝ) * P.real {ω | u n < X 0 ω} + ε / k) ^ k +
        (P.real {ω | partialMax X n ω ≤ u n} - P.real {ω | partialMax X (n / k) ω ≤ u n} ^ k))
        atTop (𝓝 ((1 - τ / k + ε / k) ^ k)) := by
      have := ((((hrp k hk1).const_sub 1).add_const (ε / k)).pow k).add hblock
      rwa [add_zero] at this
    have hlt : (1 - τ / k + ε / k) ^ k < b := by
      have hτk : τ / k < 1 := by rw [div_lt_one hk']; exact hkτ
      have h0 : 0 ≤ 1 + (-τ + ε) / k := by
        have : (-τ + ε) / k = -(τ / k) + ε / k := by ring
        rw [this]; have := div_pos hε hk'; linarith
      calc (1 - τ / k + ε / k) ^ k = (1 + (-τ + ε) / k) ^ k := by ring
        _ ≤ (Real.exp ((-τ + ε) / k)) ^ k :=
            pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp ((-τ + ε) / k)]) k
        _ = Real.exp (-τ + ε) := by
            rw [← Real.exp_nat_mul]; congr 1; field_simp
        _ < b := hεb
    filter_upwards [hup.eventually (gt_mem_nhds hlt), hk₀ k (le_max_left _ _),
      eventually_ge_atTop k] with n h1 h2 h3
    have hn : 0 < n / k := Nat.div_pos h3 hk1
    have hB := (hs.measureReal_maxLE_range_bounds hX (n / k) (u n)).2
    have hsum0 : 0 ≤ ∑ j ∈ Ico 1 (n / k), P.real {ω | u n < X 0 ω ∧ u n < X j ω} :=
      sum_nonneg fun _ _ ↦ measureReal_nonneg
    have hkr : ((n / k : ℕ) : ℝ) * k ≤ n := by exact_mod_cast Nat.div_mul_le_self n k
    have hrs : ((n / k : ℕ) : ℝ) *
        ∑ j ∈ Ico 1 (n / k), P.real {ω | u n < X 0 ω ∧ u n < X j ω} ≤ ε / k := by
      rw [le_div_iff₀ hk']
      calc _ = ((n / k : ℕ) : ℝ) * k *
            ∑ j ∈ Ico 1 (n / k), P.real {ω | u n < X 0 ω ∧ u n < X j ω} := by ring
        _ ≤ n * ∑ j ∈ Ico 1 (n / k), P.real {ω | u n < X 0 ω ∧ u n < X j ω} :=
            mul_le_mul_of_nonneg_right hkr hsum0
        _ ≤ ε := h2
    rw [← measureReal_partialMax_le hn] at hB
    have := pow_le_pow_left₀ measureReal_nonneg (hB.trans (show _ ≤ 1 - ((n / k : ℕ) : ℝ) * P.real {ω | u n < X 0 ω} + ε / k by linarith)) k
    linarith

end ExtremeValueTheory
