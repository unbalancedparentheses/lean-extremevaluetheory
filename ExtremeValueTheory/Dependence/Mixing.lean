/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Anticlustering
import ExtremeValueTheory.ForMathlib.Probability.Process.Mixing

/-!
# Mixing implies the block condition `𝒜(uₙ)`

We derive the block condition `ConditionA` (`P(M n ≤ uₙ) - P(M rₙ ≤ uₙ) ^ ⌊n / rₙ⌋ → 0`) of
`Dependence/Anticlustering.lean` from strong mixing with a rate, and in particular for
`m`-dependent sequences ([BS09, §4], [KS20, §7.5], [LLR, §3.3]).

## Main results, with the hypotheses each one uses

* `ExtremeValueTheory.abs_measureReal_maxLE_union_sub_le_alphaMixing`: for index sets
  `A, B ⊆ ℕ` with every element of `B` at least `l` above every element of `A`,
  `|P(max_{A ∪ B} X ≤ u) - P(max_A X ≤ u) P(max_B X ≤ u)| ≤ α(l)`, the strong mixing coefficient
  of `ProbabilityTheory.alphaMixing` (no stationarity).
* `ExtremeValueTheory.conditionA_of_forall_abs_le`: the block condition from a Leadbetter-type
  factorization bound `αₙ` at gaps `lₙ` (the hypothesis of `D(uₙ)`, but with a rate). Hypotheses:
  stationarity, `rₙ → ∞`, `rₙ / n → 0`, `lₙ / rₙ → 0`, `(n / rₙ) αₙ → 0` and `n P(X 0 > uₙ)`
  bounded. This upgrades the fixed-`k` block approximation `tendsto_measureReal_partialMax_sub_pow`
  to `kₙ = ⌊n / rₙ⌋ → ∞` blocks.
* `ExtremeValueTheory.conditionA_of_alphaMixing`: the block condition from strong mixing,
  `(n / rₙ) α(lₙ) → 0`, with the same remaining hypotheses ([BS09, §4], [KS20, §7.5]).
* `ExtremeValueTheory.conditionA_of_isMDependent`: `m`-dependent stationary sequences satisfy the
  block condition whenever `rₙ → ∞`, `rₙ / n → 0` and `n P(X 0 > uₙ)` is bounded.
* `ExtremeValueTheory.conditionD_of_isMDependent`: `m`-dependent sequences satisfy Leadbetter's
  `D(uₙ)` at every level sequence (no stationarity).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ### Block events and mixing coefficients -/

/-- `max_{t ∈ A} X t ≤ u` is measurable for any σ-algebra containing `σ(X t)`, `t ∈ A`. -/
theorem measurableSet_maxLE_of_comap_le {m' : MeasurableSpace Ω} {A : Finset ℕ}
    (h : ∀ t ∈ A, MeasurableSpace.comap (X t) inferInstance ≤ m') (u : ℝ) :
    MeasurableSet[m'] (maxLE X A u) := by
  have : maxLE X A u = ⋂ t ∈ (A : Set ℕ), X t ⁻¹' Set.Iic u := by ext; simp [maxLE]
  rw [this]
  exact MeasurableSet.biInter A.countable_toSet fun t ht =>
    h t ht _ ⟨Set.Iic u, measurableSet_Iic, rfl⟩

/-- **Mixing bound for block events**: if every element of `B` exceeds every element of `A` by
at least `l`, then `|P(max_{A ∪ B} X ≤ u) - P(max_A X ≤ u) P(max_B X ≤ u)| ≤ α(l)`.
No stationarity is used. -/
theorem abs_measureReal_maxLE_union_sub_le_alphaMixing [IsProbabilityMeasure P]
    {A B : Finset ℕ} {l : ℕ} (hAB : ∀ a ∈ A, ∀ b ∈ B, a + l ≤ b) (u : ℝ) :
    |P.real (maxLE X (A ∪ B) u) - P.real (maxLE X A u) * P.real (maxLE X B u)| ≤
      (alphaMixing X P l).toReal := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  set s := A.max' hA
  rw [maxLE_union]
  refine abs_measureReal_inter_sub_le_alphaMixing (s := s) (h := l)
    (measurableSet_maxLE_of_comap_le (fun t ht => comap_le_pastMeasurableSpace
      (A.le_max' t ht)) u)
    (measurableSet_maxLE_of_comap_le (fun t ht => comap_le_futureMeasurableSpace
      (hAB s (A.max'_mem hA) t ht)) u)

/-! ### The block condition from a factorization bound with a rate -/

/-- **The block condition from a factorization bound** ([LLR, §3.3], [BS09, §4]). Suppose the
probabilities of block events at distance `lₙ` inside `{0, …, n - 1}` factorize up to `αₙ` (the
bound of Leadbetter's `D(uₙ)`). If the sequence is stationary, `rₙ → ∞`, `rₙ / n → 0`,
`lₙ / rₙ → 0`, `(n / rₙ) αₙ → 0` and `n P(X 0 > uₙ)` is bounded, then
`P(M n ≤ uₙ) - P(M rₙ ≤ uₙ) ^ ⌊n / rₙ⌋ → 0`.

Compared with `tendsto_measureReal_partialMax_sub_pow` (a fixed number `k` of blocks), here the
number of blocks `kₙ = ⌊n / rₙ⌋` tends to infinity, which costs the rate `kₙ αₙ → 0`. -/
theorem conditionA_of_forall_abs_le [IsProbabilityMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {u : ℕ → ℝ} {r l : ℕ → ℕ} {α : ℕ → ℝ}
    (hD : ∀ n (A B : Finset ℕ), A ⊆ range n → B ⊆ range n → (∀ a ∈ A, ∀ b ∈ B, a + l n ≤ b) →
      |P.real (maxLE X (A ∪ B) (u n)) - P.real (maxLE X A (u n)) * P.real (maxLE X B (u n))|
        ≤ α n)
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlr : Tendsto (fun n => (l n : ℝ) / r n) atTop (𝓝 0))
    (hα : Tendsto (fun n : ℕ => (n : ℝ) / r n * α n) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n : ℕ in atTop, (n : ℝ) * P.real {ω | u n < X 0 ω} ≤ C) :
    ConditionA X P u r := by
  set p : ℕ → ℝ := fun n => P.real {ω | u n < X 0 ω}
  have hp0 : ∀ n, 0 ≤ p n := fun n => measureReal_nonneg
  have hα0 : ∀ n, 0 ≤ α n := fun n => by
    simpa using hD n ∅ ∅ (empty_subset _) (empty_subset _) (by simp)
  have hrinv : Tendsto (fun n => (1 : ℝ) / r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr)
  -- the bound
  set g : ℕ → ℝ := fun n => 2 * ((l n : ℝ) / r n) * C + C * (1 / r n) + (n : ℝ) / r n * α n +
    (r n : ℝ) / n * C
  have hg : Tendsto g atTop (𝓝 0) := by
    have := (((hlr.const_mul 2).mul_const C).add (hrinv.const_mul C)).add hα |>.add
      (hrn.mul_const C)
    simp only [mul_zero, zero_mul, add_zero] at this
    exact this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hC, hr.eventually_ge_atTop 1, hrn.eventually (gt_mem_nhds one_pos),
    eventually_gt_atTop 0] with n hCn hr1 hrn1 hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hrR : (0 : ℝ) < r n := by exact_mod_cast hr1
  have hrle : r n ≤ n := by
    have : (r n : ℝ) < n := by rwa [div_lt_one hn0'] at hrn1
    exact_mod_cast this.le
  set k := n / r n with hk
  have hk1 : 0 < k := Nat.div_pos hrle hr1
  have hkr : r n ≤ n / k := (Nat.le_div_iff_mul_le hk1).2 (by
    rw [mul_comm]; exact Nat.div_mul_le_self n (r n))
  -- the block estimate with `k` blocks of length `⌊n / k⌋`
  have hblock := hs.abs_measureReal_maxLE_range_sub_pow_le hX (u := u n) (α := α n) hk1 (hD n)
  -- replacing `⌊n / k⌋` by `rₙ`
  have hcov : range (n / k) ⊆ range (r n) ∪ Ico (r n) (n / k) := by
    intro t ht; rw [mem_range] at ht; rw [mem_union, mem_range, mem_Ico]; omega
  have hdiff := hs.abs_measureReal_maxLE_sub_le hX (range_subset_range.2 hkr) hcov (u n)
  rw [Nat.card_Ico] at hdiff
  have hpow : |P.real (maxLE X (range (n / k)) (u n)) ^ k - P.real (maxLE X (range (r n)) (u n)) ^ k|
      ≤ k * (((n / k - r n : ℕ) : ℝ) * p n) :=
    (abs_pow_sub_pow_le_of_mem_Icc (measureReal_maxLE_mem_Icc _ _)
      (measureReal_maxLE_mem_Icc _ _) k).trans (mul_le_mul_of_nonneg_left hdiff k.cast_nonneg)
  -- `k (⌊n / k⌋ - rₙ) ≤ rₙ`
  have hkk : (k : ℝ) * ((n / k - r n : ℕ) : ℝ) ≤ r n := by
    rw [Nat.cast_sub hkr, mul_sub]
    have h1 : ((n / k : ℕ) : ℝ) * k ≤ n := by exact_mod_cast Nat.div_mul_le_self n k
    have h2 : (n : ℝ) < k * r n + r n := by
      have := Nat.lt_div_mul_add (a := n) hr1
      rw [← hk] at this
      exact_mod_cast this
    nlinarith
  -- `k ≤ n / rₙ`
  have hkle : (k : ℝ) ≤ n / r n := Nat.cast_div_le
  have hkp : (k : ℝ) * p n ≤ C * (1 / r n) := by
    calc (k : ℝ) * p n ≤ n / r n * p n := mul_le_mul_of_nonneg_right hkle (hp0 n)
      _ = n * p n * (1 / r n) := by ring
      _ ≤ C * (1 / r n) := mul_le_mul_of_nonneg_right hCn (by positivity)
  have hklp : 2 * k * l n * p n ≤ 2 * ((l n : ℝ) / r n) * C := by
    calc 2 * k * l n * p n ≤ 2 * (n / r n) * l n * p n := by
          gcongr
      _ = 2 * ((l n : ℝ) / r n) * (n * p n) := by ring
      _ ≤ 2 * ((l n : ℝ) / r n) * C := mul_le_mul_of_nonneg_left hCn (by positivity)
  have hkα : (k : ℝ) * α n ≤ n / r n * α n := mul_le_mul_of_nonneg_right hkle (hα0 n)
  have hrp : (r n : ℝ) * p n ≤ (r n : ℝ) / n * C := by
    calc (r n : ℝ) * p n = (r n : ℝ) / n * (n * p n) := by field_simp
      _ ≤ (r n : ℝ) / n * C := mul_le_mul_of_nonneg_left hCn (by positivity)
  have hcorr : (k : ℝ) * (((n / k - r n : ℕ) : ℝ) * p n) ≤ r n * p n := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkk (hp0 n)
  rw [Real.norm_eq_abs, measureReal_partialMax_le hn0, measureReal_partialMax_le hr1]
  have htri := abs_sub_le (P.real (maxLE X (range n) (u n)))
    (P.real (maxLE X (range (n / k)) (u n)) ^ k) (P.real (maxLE X (range (r n)) (u n)) ^ k)
  have e : (2 * k * l n + k : ℝ) * p n + k * α n = 2 * k * l n * p n + k * p n + k * α n := by
    ring
  rw [e] at hblock
  dsimp only [g]
  linarith

/-- **Strong mixing implies the block condition** ([BS09, §4], [KS20, §7.5]): if `X` is stationary,
`rₙ → ∞`, `rₙ / n → 0`, `lₙ / rₙ → 0`, `(n / rₙ) α(lₙ) → 0` for the strong mixing coefficients
`α` of `X`, and `n P(X 0 > uₙ)` is bounded, then `𝒜(uₙ)` holds. -/
theorem conditionA_of_alphaMixing [IsProbabilityMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {u : ℕ → ℝ} {r l : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlr : Tendsto (fun n => (l n : ℝ) / r n) atTop (𝓝 0))
    (hα : Tendsto (fun n : ℕ => (n : ℝ) / r n * (alphaMixing X P (l n)).toReal) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n : ℕ in atTop, (n : ℝ) * P.real {ω | u n < X 0 ω} ≤ C) :
    ConditionA X P u r :=
  conditionA_of_forall_abs_le hs hX (fun n _ _ _ _ hAB =>
    abs_measureReal_maxLE_union_sub_le_alphaMixing hAB (u n)) hr hrn hlr hα hC

/-- **`m`-dependent sequences satisfy the block condition**: if `X` is stationary and
`m`-dependent, `rₙ → ∞`, `rₙ / n → 0` and `n P(X 0 > uₙ)` is bounded, then `𝒜(uₙ)` holds.
The gaps are `lₙ = m + 1`, at which the mixing coefficient vanishes. -/
theorem conditionA_of_isMDependent [IsProbabilityMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {m : ℕ} (hm : IsMDependent X m P) {u : ℕ → ℝ} {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n : ℕ in atTop, (n : ℝ) * P.real {ω | u n < X 0 ω} ≤ C) :
    ConditionA X P u r := by
  refine conditionA_of_alphaMixing (l := fun _ => m + 1) hs hX hr hrn ?_ ?_ hC
  · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr)
  · simp [hm.alphaMixing_eq_zero (Nat.lt_succ_self m)]

/-- **`m`-dependent sequences satisfy Leadbetter's `D(uₙ)`** at every level sequence, with
constant gaps `lₙ = m + 1` and vanishing coefficients (no stationarity). -/
theorem conditionD_of_isMDependent [IsProbabilityMeasure P] {m : ℕ} (hm : IsMDependent X m P)
    (u : ℕ → ℝ) : ConditionD X P u := by
  refine ⟨fun _ => m + 1, fun _ => 0, ?_, tendsto_const_nhds, fun n A B _ _ hAB => ?_⟩
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  · have := abs_measureReal_maxLE_union_sub_le_alphaMixing hAB (u n) (P := P) (X := X)
    rwa [hm.alphaMixing_eq_zero (Nat.lt_succ_self m), ENNReal.toReal_zero] at this

end ExtremeValueTheory
