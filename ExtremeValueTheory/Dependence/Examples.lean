/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.ExtremalIndex

/-!
# Examples of extremal indices

* **iid sequences** satisfy Leadbetter's conditions `D(uₙ)` and `D'(uₙ)` and have extremal
  index `1` [LLR, §3.4], [EKM, §4.4].
* **The moving maximum** `X t = max (Z t) (Z (t + 1))` of an iid sequence `Z` is stationary and
  has extremal index `1/2` [EKM, §8.1], [LLR, §3.7]: exceedances of high levels occur
  in pairs.

## Main results

* `ExtremeValueTheory.measureReal_maxLE_of_iIndepFun`: `P(max_{t ∈ S} X t ≤ u) = F(u) ^ #S`.
* `ExtremeValueTheory.conditionD_of_iIndepFun`, `ExtremeValueTheory.conditionD'_of_iIndepFun`.
* `ExtremeValueTheory.hasExtremalIndex_one_of_iIndepFun`.
* `ExtremeValueTheory.isStationary_movingMax`, `ExtremeValueTheory.hasExtremalIndex_movingMax`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-! ### iid sequences -/

section iid

omit [IsProbabilityMeasure P] in
/-- For an iid sequence, `P(max_{t ∈ S} X t ≤ u) = P(X 0 ≤ u) ^ #S`. -/
lemma measureReal_maxLE_of_iIndepFun (hind : iIndepFun X P)
    (hid : ∀ t, IdentDistrib (X t) (X 0) P P) (S : Finset ℕ) (u : ℝ) :
    P.real (maxLE X S u) = P.real {ω | X 0 ω ≤ u} ^ #S := by
  have e : maxLE X S u = ⋂ t ∈ S, X t ⁻¹' Set.Iic u := by ext; simp [maxLE]
  rw [e, Measure.real, hind.measure_inter_preimage_eq_mul S (fun _ _ ↦ measurableSet_Iic),
    ENNReal.toReal_prod]
  have : ∀ t, (P (X t ⁻¹' Set.Iic u)).toReal = P.real {ω | X 0 ω ≤ u} := by
    intro t
    rw [(hid t).measure_mem_eq measurableSet_Iic]
    rfl
  simp [this]

variable (hX : ∀ t, Measurable (X t)) (hind : iIndepFun X P)
  (hid : ∀ t, IdentDistrib (X t) (X 0) P P)
include hX hind hid

omit [IsProbabilityMeasure P] hX in
/-- iid sequences satisfy `D(uₙ)` for every level sequence, with gaps `lₙ = 1` and mixing
coefficients `αₙ = 0`. -/
theorem conditionD_of_iIndepFun (u : ℕ → ℝ) : ConditionD X P u := by
  refine ⟨fun _ ↦ 1, fun _ ↦ 0, ?_, tendsto_const_nhds, ?_⟩
  · simpa using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  · intro n A B _ _ hAB
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have := hAB a ha a hb
      simp at this
    simp only [measureReal_maxLE_of_iIndepFun hind hid, card_union_of_disjoint hdisj,
      pow_add, sub_self, abs_zero, le_refl]

omit [IsProbabilityMeasure P] hX in
/-- iid sequences satisfy `D'(uₙ)` whenever `n P(X 0 > uₙ)` converges. -/
theorem conditionD'_of_iIndepFun {u : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ)) :
    ConditionD' X P u := by
  intro ε hε
  set C := (|τ| + 1) ^ 2 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨⌈C / ε⌉₊ + 1, fun k hk ↦ ?_⟩
  have hk0 : (0 : ℝ) < k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (le_trans (Nat.le_add_left 1 _) hk)
    linarith
  have hkC : C / ε < k := by
    have h1 : C / ε ≤ ⌈C / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈C / ε⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  have hbd : ∀ᶠ n : ℕ in atTop, n * P.real {ω | u n < X 0 ω} ≤ |τ| + 1 :=
    hτ.eventually (ge_mem_nhds (by linarith [le_abs_self τ]))
  filter_upwards [hbd] with n hn
  set p := P.real {ω | u n < X 0 ω} with hp
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hpair : ∀ j ∈ Ico 1 (n / k), P.real {ω | u n < X 0 ω ∧ u n < X j ω} = p ^ 2 := by
    intro j hj
    have hj0 : (0 : ℕ) ≠ j := by simp at hj; omega
    have h := (hind.indepFun hj0).measure_inter_preimage_eq_mul (Set.Ioi (u n)) (Set.Ioi (u n))
      measurableSet_Ioi measurableSet_Ioi
    have hj' : P (X j ⁻¹' Set.Ioi (u n)) = P (X 0 ⁻¹' Set.Ioi (u n)) :=
      (hid j).measure_mem_eq measurableSet_Ioi
    rw [hj'] at h
    simp only [Measure.real, hp]
    rw [show {ω | u n < X 0 ω ∧ u n < X j ω} = X 0 ⁻¹' Set.Ioi (u n) ∩ X j ⁻¹' Set.Ioi (u n)
      from rfl, h, ENNReal.toReal_mul, sq]
    rfl
  rw [sum_congr rfl hpair, sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hr : ((n / k - 1 : ℕ) : ℝ) ≤ n / k :=
    (Nat.cast_le.2 (Nat.sub_le _ _)).trans Nat.cast_div_le
  have hnp0 : 0 ≤ n * p := mul_nonneg n.cast_nonneg hp0
  calc (n : ℝ) * (((n / k - 1 : ℕ) : ℝ) * p ^ 2) ≤ n * ((n / k) * p ^ 2) := by gcongr
    _ = (n * p) ^ 2 / k := by ring
    _ ≤ C / k := by
        gcongr
        rw [hC]
        exact pow_le_pow_left₀ hnp0 hn 2
    _ ≤ ε := by
        rw [div_le_iff₀ hk0]
        rw [div_lt_iff₀ hε] at hkC
        linarith

/-- **iid sequences have extremal index `1`**, via Leadbetter's theorem. -/
theorem hasExtremalIndex_one_of_iIndepFun : HasExtremalIndex X P 1 :=
  hasExtremalIndex_one (isStationary_of_iIndepFun hX hind hid) hX fun _ _ _ hu ↦
    ⟨conditionD_of_iIndepFun hind hid _, conditionD'_of_iIndepFun hind hid hu⟩

end iid

/-! ### The moving maximum -/

section movingMax

variable {Z : ℕ → Ω → ℝ} (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hid : ∀ t, IdentDistrib (Z t) (Z 0) P P)
include hZ hind hid

/-- The moving maximum `X t = max (Z t) (Z (t + 1))` of a stationary sequence is stationary. -/
theorem isStationary_movingMax :
    IsStationary (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P := by
  have h := (isStationary_of_iIndepFun hZ hind hid).factor hZ
    (f := fun z : ℕ → ℝ ↦ max (z 0) (z 1))
    ((measurable_pi_apply 0).max (measurable_pi_apply 1))
  convert h using 3 with t ω
  simp [add_comm]

/-- **The moving maximum of an iid sequence has extremal index `1/2`**: if
`X t = max (Z t) (Z (t + 1))` with `Z` iid, then `n P(X 0 > uₙ) → τ` implies
`P(M n ≤ uₙ) → exp (-τ / 2)`. -/
theorem hasExtremalIndex_movingMax :
    HasExtremalIndex (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P (1 / 2) := by
  refine ⟨⟨by norm_num, by norm_num⟩, fun τ hτ u hu ↦ ?_⟩
  set G : ℕ → ℝ := fun n ↦ P.real {ω | Z 0 ω ≤ u n} with hG
  have hG0 : ∀ n, 0 ≤ G n := fun n ↦ measureReal_nonneg
  -- `P(X 0 > u) = 1 - G ^ 2`
  have hsurv : ∀ n, P.real {ω | u n < max (Z 0 ω) (Z (0 + 1) ω)} = 1 - G n ^ 2 := by
    intro n
    have e : {ω | u n < max (Z 0 ω) (Z (0 + 1) ω)} = (maxLE Z (range 2) (u n))ᶜ := by
      ext ω; simp [maxLE, Finset.range_add_one, lt_max_iff]
      by_cases h1 : Z 1 ω ≤ u n
      · simp [h1, not_lt.2 h1]
      · simp [h1, not_le.1 h1]
    rw [e, probReal_compl_eq_one_sub (measurableSet_maxLE hZ _ _),
      measureReal_maxLE_of_iIndepFun hind hid, card_range]
  -- `P(M n ≤ u) = G ^ (n + 1)`
  have hmax : ∀ n, 0 < n → P.real {ω | partialMax (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) n ω
      ≤ u n} = G n ^ n * G n := by
    intro n hn
    rw [measureReal_partialMax_le hn, ← pow_succ, ← card_range (n + 1),
      ← measureReal_maxLE_of_iIndepFun hind hid]
    congr 1
    ext ω
    simp only [maxLE, mem_range, max_le_iff, Set.mem_ofPred_eq]
    constructor
    · intro h t ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | rfl
      · exact (h t h').1
      · exact (h (t - 1) (by omega)).2.trans_eq' (by rw [Nat.sub_add_cancel hn])
    · intro h t ht
      exact ⟨h t (by omega), h (t + 1) (by omega)⟩
  -- `n (1 - G) → τ / 2`
  have hu' : Tendsto (fun n : ℕ ↦ n * (1 - G n ^ 2)) atTop (𝓝 τ) :=
    hu.congr fun n ↦ by rw [hsurv]
  have hG1 : Tendsto G atTop (𝓝 1) := by
    have h2 : Tendsto (fun n ↦ G n ^ 2) atTop (𝓝 1) := by
      simpa using (tendsto_zero_of_tendsto_natCast_mul' hu').const_sub 1
    have := (Real.continuous_sqrt.tendsto 1).comp h2
    simp only [Real.sqrt_one] at this
    exact this.congr fun n ↦ by simp [Real.sqrt_sq (hG0 n)]
  have hZτ : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < Z 0 ω}) atTop (𝓝 (τ / 2)) := by
    have := hu'.div (hG1.const_add 1) (by norm_num)
    rw [show τ / (1 + 1) = τ / 2 by norm_num] at this
    refine this.congr fun n ↦ ?_
    show (n : ℝ) * (1 - G n ^ 2) / (1 + G n) = _
    have hc : P.real {ω | u n < Z 0 ω} = 1 - G n := by
      have : {ω | u n < Z 0 ω} = {ω | Z 0 ω ≤ u n}ᶜ := by ext; simp
      rw [this, probReal_compl_eq_one_sub (measurableSet_le (hZ 0) measurable_const)]
    rw [hc]
    have : 1 + G n ≠ 0 := by linarith [hG0 n]
    field_simp
    ring
  -- the iid sequence `Z` has extremal index `1`
  have hZmax := (hasExtremalIndex_one_of_iIndepFun hZ hind hid).2 (τ / 2) (by positivity) u hZτ
  have hGn : Tendsto (fun n ↦ G n ^ n) atTop (𝓝 (Real.exp (-(1 * (τ / 2))))) := by
    refine hZmax.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [measureReal_partialMax_le (by omega), measureReal_maxLE_of_iIndepFun hind hid,
      card_range]
  have := hGn.mul hG1
  rw [mul_one, show -(1 * (τ / 2)) = -(1 / 2 * τ) by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hmax n (by omega)]

end movingMax

end ExtremeValueTheory
