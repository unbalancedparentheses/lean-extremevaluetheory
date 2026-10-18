/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Examples

/-!
# `D'(uₙ)` is necessary in Leadbetter's theorem

Leadbetter's theorem (`tendsto_measureReal_partialMax_le_exp`) assumes stationarity, the mixing
condition `D(uₙ)`, the anti-clustering condition `D'(uₙ)` and `n P(X_0 > uₙ) → τ`, and concludes
`P(M n ≤ uₙ) → e^(-τ)`. We show that `D'(uₙ)` cannot be dropped: the moving maximum
`X_t = max(Z_t, Z_{t+1})` of an iid sequence is stationary and satisfies `D(uₙ)` along *every*
level sequence (it is `1`-dependent), violates `D'(uₙ)` along every level sequence with
`n P(X_0 > uₙ) → τ > 0`, and has `P(M n ≤ uₙ) → e^(-τ/2) ≠ e^(-τ)`.

## Main results

* `maxLE_movingMax`: `{max_{t ∈ A} X_t ≤ u} = {max_{t ∈ A ∪ (A + 1)} Z_t ≤ u}`.
* `conditionD_movingMax` (`Z` iid; no level hypothesis): `D(uₙ)` with gaps `2` and coefficients
  `0`.
* `not_conditionD'_movingMax` (`Z` identically distributed, `n P(X_0 > uₙ) → τ > 0`): `D'(uₙ)` fails. Only the lag-one
  term `n P(X_0 > uₙ, X_1 > uₙ) ≥ n P(Z_1 > uₙ) ≥ n P(X_0 > uₙ) / 2` is used.
* `not_tendsto_exp_movingMax`: the conclusion of Leadbetter's theorem fails.
* `leadbetter_needs_conditionD'`: the packaged counterexample; with a continuous marginal of `Z`
  (`hasExceedanceLevels_movingMax`) the level sequences exist, so the counterexample is not
  vacuous.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℕ → Ω → ℝ}

/-- The block event of the moving maximum is a block event of the innovations. -/
theorem maxLE_movingMax (A : Finset ℕ) (u : ℝ) :
    maxLE (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) A u = maxLE Z (A ∪ A.image (· + 1)) u := by
  ext ω
  simp only [maxLE, Set.mem_ofPred_eq, max_le_iff, mem_union, mem_image]
  constructor
  · rintro h t (ht | ⟨s, hs, rfl⟩)
    · exact (h t ht).1
    · exact (h s hs).2
  · intro h t ht
    exact ⟨h t (Or.inl ht), h (t + 1) (Or.inr ⟨t, ht, rfl⟩)⟩

variable (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hid : ∀ t, IdentDistrib (Z t) (Z 0) P P)
include hind hid

omit [IsProbabilityMeasure P] in
/-- **The moving maximum satisfies `D(uₙ)`** along every level sequence: for index sets at
distance `≥ 2`, the innovation index sets `A ∪ (A + 1)` and `B ∪ (B + 1)` are disjoint, so the
block probabilities factorize exactly. -/
theorem conditionD_movingMax (u : ℕ → ℝ) :
    ConditionD (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P u := by
  refine ⟨fun _ ↦ 2, fun _ ↦ 0, ?_, tendsto_const_nhds, fun n A B _ _ hAB ↦ ?_⟩
  · simpa using (tendsto_const_nhds (x := (2 : ℝ))).div_atTop tendsto_natCast_atTop_atTop
  · simp only at hAB
    have hdisj : Disjoint (A ∪ A.image (· + 1)) (B ∪ B.image (· + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [mem_union, mem_image] at hx hy
      rcases hx with hx | ⟨a, ha, rfl⟩ <;> rcases hy with hy | ⟨b, hb, hb'⟩
      · have := hAB x hx x hy; omega
      · have := hAB x hx b hb; omega
      · have := hAB a ha _ hy; omega
      · have := hAB a ha b hb; omega
    have e : (A ∪ B) ∪ (A ∪ B).image (· + 1) =
        (A ∪ A.image (· + 1)) ∪ (B ∪ B.image (· + 1)) := by
      rw [image_union]; ac_rfl
    simp only [maxLE_movingMax, e, measureReal_maxLE_of_iIndepFun hind hid,
      card_union_of_disjoint hdisj, pow_add, sub_self, abs_zero, le_refl]

omit [IsProbabilityMeasure P] hind in
/-- `P(X_0 > u) ≤ 2 P(Z_1 > u)`. -/
theorem measureReal_lt_movingMax_le (u : ℝ) :
    P.real {ω | u < max (Z 0 ω) (Z (0 + 1) ω)} ≤ 2 * P.real {ω | u < Z 1 ω} := by
  have e : {ω | u < max (Z 0 ω) (Z (0 + 1) ω)} = Z 0 ⁻¹' Set.Ioi u ∪ Z 1 ⁻¹' Set.Ioi u := by
    ext ω; simp [lt_max_iff]
  have h01 : P.real (Z 0 ⁻¹' Set.Ioi u) = P.real (Z 1 ⁻¹' Set.Ioi u) := by
    simp only [measureReal_def, ((hid 1).measure_mem_eq measurableSet_Ioi).symm]
  rw [e]
  refine (measureReal_union_le _ _).trans (le_of_eq ?_)
  rw [h01, ← two_mul]
  rfl

omit hind in
/-- **The moving maximum violates `D'(uₙ)`** along every level sequence with
`n P(X_0 > uₙ) → τ > 0`: already the lag-one term `n P(X_0 > uₙ, X_1 > uₙ) ≥ n P(Z_1 > uₙ)` stays
above `τ / 3`. -/
theorem not_conditionD'_movingMax {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hu : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < max (Z 0 ω) (Z (0 + 1) ω)}) atTop (𝓝 τ)) :
    ¬ ConditionD' (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P u := by
  intro hD'
  obtain ⟨k₀, hk₀⟩ := hD' (τ / 4) (by positivity)
  set k := max k₀ 1
  have hk1 : 1 ≤ k := le_max_right _ _
  have hev := hk₀ k (le_max_left _ _)
  have hlow : ∀ᶠ n : ℕ in atTop, τ / 3 < n * P.real {ω | u n < Z 1 ω} := by
    filter_upwards [hu.eventually (lt_mem_nhds (show 2 * (τ / 3) < τ by linarith))] with n hn
    have := measureReal_lt_movingMax_le hid (P := P) (u n)
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith
  obtain ⟨n, hn1, hn2, hn3⟩ := (hev.and (hlow.and (eventually_ge_atTop (2 * k)))).exists
  have h1 : 1 ∈ Ico 1 (n / k) := by
    rw [mem_Ico]
    refine ⟨le_rfl, ?_⟩
    have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).2 (by omega : 2 * k ≤ n)
    omega
  have hterm : P.real {ω | u n < Z 1 ω} ≤
      ∑ j ∈ Ico 1 (n / k), P.real {ω | u n < max (Z 0 ω) (Z (0 + 1) ω) ∧
        u n < max (Z j ω) (Z (j + 1) ω)} := by
    refine le_trans ?_ (single_le_sum (f := fun j ↦ P.real {ω | u n < max (Z 0 ω) (Z (0 + 1) ω) ∧
        u n < max (Z j ω) (Z (j + 1) ω)}) (fun _ _ ↦ measureReal_nonneg) h1)
    exact measureReal_mono fun ω (hω : u n < Z 1 ω) ↦
      ⟨lt_max_of_lt_right hω, lt_max_of_lt_left hω⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have := mul_le_mul_of_nonneg_left hterm hn0
  linarith

include hZ in
omit hid in
/-- **The conclusion of Leadbetter's theorem fails for the moving maximum**:
`P(M n ≤ uₙ) → e^(-τ/2) ≠ e^(-τ)`. -/
theorem not_tendsto_exp_movingMax (hid : ∀ t, IdentDistrib (Z t) (Z 0) P P) {u : ℕ → ℝ} {τ : ℝ}
    (hτ0 : 0 < τ)
    (hu : Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < max (Z 0 ω) (Z (0 + 1) ω)}) atTop (𝓝 τ)) :
    ¬ Tendsto (fun n ↦ P.real {ω | partialMax (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) n ω ≤ u n})
      atTop (𝓝 (Real.exp (-τ))) := by
  intro h
  have h2 := (hasExtremalIndex_movingMax hZ hind hid).2 τ hτ0 u hu
  have := Real.exp_injective (tendsto_nhds_unique h2 h)
  linarith

include hZ in
omit hid in
/-- If `Z_0` has a continuous c.d.f., so does `X_0 = max(Z_0, Z_1)` (its c.d.f. is `F²`), and the
moving maximum admits level sequences `n P(X_0 > uₙ) → τ` for every `τ > 0`. -/
theorem hasExceedanceLevels_movingMax (hid : ∀ t, IdentDistrib (Z t) (Z 0) P P)
    (hcont : Continuous fun x ↦ P.real {ω | Z 0 ω ≤ x}) :
    HasExceedanceLevels (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P := by
  refine hasExceedanceLevels_of_continuous ((hZ 0).max (hZ 1)) ?_
  have e : (fun x ↦ P.real {ω | max (Z 0 ω) (Z (0 + 1) ω) ≤ x}) =
      fun x ↦ P.real {ω | Z 0 ω ≤ x} ^ 2 := by
    funext x
    have : {ω | max (Z 0 ω) (Z (0 + 1) ω) ≤ x} = maxLE Z (range 2) x := by
      ext ω; simp [maxLE, range_add_one, and_comm]
    rw [this, measureReal_maxLE_of_iIndepFun hind hid, card_range]
  rw [e]
  exact hcont.pow 2

include hZ in
omit hid in
/-- **`D'(uₙ)` is necessary in Leadbetter's theorem.** For the moving maximum of an iid sequence
`Z` with continuous marginal c.d.f., for every `τ > 0` there is a level sequence with
`n P(X_0 > uₙ) → τ` such that the sequence is stationary and satisfies `D(uₙ)`, but `D'(uₙ)`
fails and `P(M n ≤ uₙ) ↛ e^(-τ)`. So in `tendsto_measureReal_partialMax_le_exp` the hypothesis
`D'(uₙ)` cannot be removed. -/
theorem leadbetter_needs_conditionD' (hid : ∀ t, IdentDistrib (Z t) (Z 0) P P)
    (hcont : Continuous fun x ↦ P.real {ω | Z 0 ω ≤ x}) {τ : ℝ} (hτ0 : 0 < τ) :
    ∃ u : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < max (Z 0 ω) (Z (0 + 1) ω)}) atTop (𝓝 τ) ∧
      IsStationary (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P ∧
      ConditionD (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P u ∧
      ¬ ConditionD' (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) P u ∧
      ¬ Tendsto (fun n ↦ P.real {ω | partialMax (fun t ω ↦ max (Z t ω) (Z (t + 1) ω)) n ω ≤ u n})
        atTop (𝓝 (Real.exp (-τ))) := by
  obtain ⟨u, hu⟩ := hasExceedanceLevels_movingMax hZ hind hid hcont τ hτ0
  exact ⟨u, hu, isStationary_movingMax hZ hind hid, conditionD_movingMax hind hid u,
    not_conditionD'_movingMax hid hτ0 hu, not_tendsto_exp_movingMax hZ hind hid hτ0 hu⟩

end ExtremeValueTheory
