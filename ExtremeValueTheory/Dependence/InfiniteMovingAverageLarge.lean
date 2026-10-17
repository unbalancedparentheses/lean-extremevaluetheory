/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.InfiniteMovingAverage
import ExtremeValueTheory.HeavyTails.LinearProcessSeriesLarge

/-!
# The extremal index of an infinite moving average, all `α > 0`

This file removes the restriction `α < 1` of `Dependence/InfiniteMovingAverage.lean`. Let
`(Z_i)_{i ∈ ℤ}` be iid nonnegative random variables with `P(Z_0 > x)` regularly varying with
index `-α`, **any `α > 0`**, and let `ψ_j ≥ 0`, not all zero, with

  `∑_j ψ_j^δ < ∞` for some `0 < δ < α` with `δ < 1`.

Then `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` converges almost surely, and

* `tendsto_measureReal_process_div_of_lt_one`: `P(X_0 > x) / P(Z_0 > x) → ∑_j ψ_j^α`;
* `exists_measureReal_abs_sub_gt_le_of_lt_one`: the uniform remainder bound
  `P(|X_t - X^{(m)}_t| > y) ≤ K (∑_{j > m} ψ_j^δ) P(Z_0 > y)` for `m ≥ m₀`, `y ≥ x₀`;
* `hasExtremalIndex_of_lt_one`: `θ = (sup_j ψ_j)^α / ∑_j ψ_j^α`.

For `α < 1` the hypothesis `δ < 1` follows from `δ < α`, so these generalize the theorems of
`InfiniteMovingAverage.lean`. The only change in the proofs is the remainder bound, which now
comes from `LinearProcess.exists_measure_tsum_gt_le_of_lt_one` (weighted Hölder reduction to the
case `α < 1`, valid without moment or centering assumptions); `m₀` is chosen so that
`∑_{j > m} ψ_j^δ ≤ 1` for `m ≥ m₀`. The rest of the approximation argument (finite moving
averages via `MovingAverage.hasExtremalIndex`, i.e. through the main theorem `θ = ϑ`) is
unchanged.

The condition `δ < 1` is slightly stronger than the optimal `∑ ψ_j < ∞` of [EKM, Lemma A3.26] /
Mikosch–Samorodnitsky (2000) for `α > 1`; it holds for all geometrically decaying coefficients
(AR(1), causal ARMA) and for `ψ_j = O(j^{-r})` with `r > 1`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal

namespace ExtremeValueTheory

namespace InfiniteMovingAverage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {Z : ℤ → Ω → ℝ} {ψ : ℕ → ℝ} {α δ : ℝ}

/-- **Tail of the infinite moving average, all `α > 0`**:
`P(X_0 > x) / P(Z_0 > x) → ∑_j ψ_j^α` (`0 < δ < α`, `δ < 1`, `∑ ψ_j^δ < ∞`). -/
theorem tendsto_measureReal_process_div_of_lt_one (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) :
    Tendsto (fun x => P.real {ω | x < process ψ Z 0 ω} / P.real {ω | x < Z 0 ω}) atTop
      (𝓝 (∑' j, ψ j ^ α)) := by
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [setOf_lt_abs_eq hZ0] using hL
  have hp : Tendsto (fun x => P.real {ω | x < Z 0 ω} / P.real {ω | x < |Z 0 ω|}) atTop
      (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hL.1] with x hx
    rw [setOf_lt_abs_eq hZ0, div_self hx.ne']
  have hinj : Function.Injective fun i : ℕ => (0 : ℤ) - i := fun a b h => by
    simpa using h
  have h := LinearProcess.tendsto_measureReal_tsum_mul_div_of_lt_one
    (Z := fun i : ℕ => Z (0 - i)) (fun i => hZ _) (hZ 0) (hind.precomp hinj) (fun i => hident _)
    hδ hδα hδ1 hL' hp
    (summable_abs_rpow hψ0 hψ)
  simp only [setOf_lt_abs_eq hZ0] at h
  have hW : ∑' j, ψ j ^ α = ∑' j, LinearProcess.tailWeight α 1 (ψ j) := by
    refine tsum_congr fun j => ?_
    rcases (hψ0 j).eq_or_lt with h0 | hpos
    · rw [← h0, LinearProcess.tailWeight_zero, Real.zero_rpow (hδ.trans hδα).ne']
    · rw [LinearProcess.tailWeight_of_pos hpos, mul_one]
  rw [hW]
  exact h

/-- **Uniform remainder bound, all `α > 0`** (`0 < δ < α`, `δ < 1`): there are `K, x₀ > 0` and
`m₀` such that for all `m ≥ m₀`, `t ∈ ℤ` and `y ≥ x₀`,
`P(|X_t - X^{(m)}_t| > y) ≤ K (∑_{j > m} ψ_j^δ) P(Z_0 > y)`. Independence and moments are not
needed. -/
theorem exists_measureReal_abs_sub_gt_le_of_lt_one (hZ : ∀ i, Measurable (Z i))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) :
    ∃ K x₀ : ℝ, ∃ m₀ : ℕ, 0 < K ∧ 0 < x₀ ∧ ∀ m ≥ m₀, ∀ t : ℤ, ∀ y ≥ x₀,
      P.real {ω | y < |process ψ Z t ω - MovingAverage.process m ψ Z t ω|} ≤
        K * (∑' j, ψ (j + (m + 1)) ^ δ) * P.real {ω | y < Z 0 ω} := by
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [setOf_lt_abs_eq hZ0] using hL
  obtain ⟨K, x₀, hK, hx₀, hR⟩ :=
    LinearProcess.exists_measure_tsum_gt_le_of_lt_one (hZ 0) hδ hδα hδ1 hL'
  obtain ⟨m₀, hm₀⟩ := LinearProcess.exists_tsum_add_le_one ψ δ
  refine ⟨K, x₀, m₀, hK, hx₀, fun m hm t y hy => ?_⟩
  have hy0 : 0 ≤ y := hx₀.le.trans hy
  have h := hR (fun j => Z (t - ((j + (m + 1) : ℕ) : ℤ))) (fun j => hZ _) (fun j => hident _)
    (fun j => ψ (j + (m + 1)))
    ((summable_nat_add_iff (m + 1)).2 (summable_abs_rpow hψ0 hψ)) (hm₀ (m + 1) (by omega)) y hy
  simp only [abs_of_nonneg (hψ0 _), setOf_lt_abs_eq hZ0] at h
  have hsub : {ω | y < |process ψ Z t ω - MovingAverage.process m ψ Z t ω|} ⊆
      {ω | ENNReal.ofReal y <
        ∑' j, ENNReal.ofReal (ψ (j + (m + 1)) * |Z (t - ((j + (m + 1) : ℕ) : ℤ)) ω|)} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra hle
    push Not at hle
    have := (LinearProcess.abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z (t - j) ω)
      (m := m + 1) hy0 (by simpa only [abs_of_nonneg (hψ0 _)] using hle)).2
    exact absurd this (not_le.2 hω)
  have hT0 : 0 ≤ ∑' j, ψ (j + (m + 1)) ^ δ := tsum_nonneg fun j => Real.rpow_nonneg (hψ0 _) _
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (ENNReal.toReal_le_of_le_ofReal (by positivity) h)

/-- **The extremal index of an infinite moving average, all `α > 0`** ([DR85], [EKM, §8.1],
[KS20, Chapter 15]). Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative with `P(Z_0 > x)` regularly varying
with index `-α`, `α > 0`, let `0 < δ < α` with `δ < 1`, and let `ψ_j ≥ 0`, not all zero, with
`∑ ψ_j^δ < ∞`. Then
`X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` has extremal index `θ = (sup_j ψ_j)^α / ∑_j ψ_j^α`.

Proof by approximation with the `m`-dependent finite moving averages
(`MovingAverage.hasExtremalIndex`, derived through the main theorem `θ = ϑ`), using the uniform
remainder bound `exists_measureReal_abs_sub_gt_le_of_lt_one`. -/
theorem hasExtremalIndex_of_lt_one (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasExtremalIndex (fun n : ℕ => process ψ Z n) P ((⨆ j, ψ j) ^ α / ∑' j, ψ j ^ α) := by
  have hα : 0 < α := hδ.trans hδα
  have hS : Summable fun j => ψ j ^ α := summable_rpow hψ0 hδ hδα.le hψ
  obtain ⟨k, hk0, hk⟩ := exists_forall_le hψ0 hδ hψ hpos
  have hsup : (⨆ j, ψ j) = ψ k :=
    le_antisymm (ciSup_le hk) (le_ciSup (f := ψ) ⟨ψ k, by rintro _ ⟨j, rfl⟩; exact hk j⟩ k)
  rw [hsup]
  set W := ∑' j, ψ j ^ α with hW_def
  have hkα : 0 < ψ k ^ α := Real.rpow_pos_of_pos hk0 _
  have hkW : ψ k ^ α ≤ W := hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _
  have hW : 0 < W := hkα.trans_le hkW
  set ϑ := ψ k ^ α / W with hϑ
  refine ⟨⟨div_nonneg hkα.le hW.le, (div_le_one hW).2 hkW⟩, fun τ hτ u hu => ?_⟩
  set L : ℝ → ℝ := fun x => P.real {ω | x < Z 0 ω} with hL_def
  -- the finite moving averages
  have hfinIdx : ∀ m ≥ k, HasExtremalIndex (fun n : ℕ => MovingAverage.process m ψ Z n) P
      (ψ k ^ α / MovingAverage.weightSum m ψ α) := by
    intro m hm
    set ψm : ℕ → ℝ := fun j => if j ≤ m then ψ j else 0 with hψm_def
    have hψm0 : ∀ j, 0 ≤ ψm j := fun j => by
      simp only [hψm_def]; split_ifs
      · exact hψ0 j
      · exact le_rfl
    have hψmm : ∀ j, m < j → ψm j = 0 := fun j hj => by
      simp [hψm_def, show ¬ j ≤ m by omega]
    have hagree : ∀ i ∈ range (m + 1), ψm i = ψ i := fun i hi => by
      simp [hψm_def, show i ≤ m by simp only [Finset.mem_range] at hi; omega]
    have hproc : MovingAverage.process m ψm Z = MovingAverage.process m ψ Z := by
      funext t ω
      exact Finset.sum_congr rfl fun i hi => by rw [hagree i hi]
    have hWm : MovingAverage.weightSum m ψm α = MovingAverage.weightSum m ψ α :=
      Finset.sum_congr rfl fun i hi => by rw [hagree i hi]
    have hkm : k ∈ range (m + 1) := mem_range.2 (by omega)
    have hsupm : (range (m + 1)).sup' nonempty_range_add_one ψm = ψ k := by
      refine le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) ?_
      · rw [hagree j hj]; exact hk j
      · exact (hagree k hkm).symm.le.trans (Finset.le_sup' ψm hkm)
    have hWpos : 0 < MovingAverage.weightSum m ψm α := by
      rw [hWm]
      exact hkα.trans_le (Finset.single_le_sum (f := fun j => ψ j ^ α)
        (fun j _ => Real.rpow_nonneg (hψ0 j) _) hkm)
    have h := MovingAverage.hasExtremalIndex hZ hind hident hZ0 hα hL hψm0 hψmm hWpos
    rw [hsupm, show ∑ j ∈ range (m + 1), ψm j ^ α = MovingAverage.weightSum m ψm α from rfl,
      hWm, hproc] at h
    exact h
  -- levels
  simp only [Nat.cast_zero] at hu
  have hFXa : Antitone fun x => P.real {ω | x < process ψ Z 0 ω} := fun a b hab =>
    measureReal_mono (fun ω (h : b < _) => (show a < _ from lt_of_le_of_lt hab h))
  obtain ⟨hut, hs⟩ := tendsto_atTop_of_tendsto_natCast_mul hFXa (fun _ => measureReal_nonneg)
    hL.1 hW (tendsto_measureReal_process_div_of_lt_one hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ) hu
  -- the finite moving averages at the levels `c u_n`
  have hfin : ∀ m ≥ k, ∀ c : ℝ, 0 < c →
      Tendsto (fun n => P.real {ω | partialMax (fun n : ℕ => MovingAverage.process m ψ Z n) n ω ≤
        c * u n}) atTop (𝓝 (Real.exp (-(ϑ * τ * c ^ (-α))))) := by
    intro m hm c hc
    have hWm : 0 < MovingAverage.weightSum m ψ α :=
      hkα.trans_le (Finset.single_le_sum (f := fun j => ψ j ^ α)
        (fun j _ => Real.rpow_nonneg (hψ0 j) _) (mem_range.2 (by omega)))
    have hlev := tendsto_natCast_mul_comp_mul hL
      (MovingAverage.tendsto_measureReal_process_div (m := m) (ψ := ψ) hZ hind hident hZ0 hα hL
        hψ0) hut hs hc
    have hτ' : 0 < τ / W * (MovingAverage.weightSum m ψ α * c ^ (-α)) := by
      have := Real.rpow_pos_of_pos hc (-α)
      positivity
    have := (hfinIdx m hm).2 _ hτ' (fun n => c * u n) (by simpa only [Nat.cast_zero] using hlev)
    convert this using 3
    rw [hϑ]
    field_simp
  -- the remainder
  obtain ⟨K, x₀, m₀, hK, hx₀, hR⟩ :=
    exists_measureReal_abs_sub_gt_le_of_lt_one hZ hident hZ0 hδ hδα hδ1 hL hψ0 hψ
  set T : ℕ → ℝ := fun m => ∑' j, ψ (j + (m + 1)) ^ δ with hT_def
  have hT : Tendsto T atTop (𝓝 0) :=
    (tendsto_sum_nat_add fun j => ψ j ^ δ).comp (tendsto_add_atTop_nat 1)
  set Bd : ℕ → ℝ → ℕ → Set Ω := fun m ε n =>
    {ω | ∃ t < n, ε * u n < |process ψ Z t ω - MovingAverage.process m ψ Z t ω|} with hBd
  have hbad : ∀ m ≥ m₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      P.real (Bd m ε n) ≤ n * (K * T m * L (ε * u n)) := by
    intro m hm ε hε
    filter_upwards [(hut.const_mul_atTop hε).eventually (eventually_ge_atTop x₀)] with n hn
    have hsub : Bd m ε n ⊆ ⋃ t ∈ range n,
        {ω | ε * u n < |process ψ Z t ω - MovingAverage.process m ψ Z t ω|} := by
      rintro ω ⟨t, ht, h⟩
      exact mem_biUnion (mem_range.2 ht) h
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_biUnion_finset_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun (t : ℕ) _ => hR m hm (t : ℤ) _ hn).trans ?_
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have hbadlim : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => n * (K * T m * L (ε * u n)))
      atTop (𝓝 (K * T m * (τ / W * (1 * ε ^ (-α))))) := by
    intro m ε hε
    have hLL : Tendsto (fun x => L x / L x) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (by filter_upwards [hL.1] with x hx; rw [div_self hx.ne'])
    have := (tendsto_natCast_mul_comp_mul hL hLL hut hs hε).const_mul (K * T m)
    refine this.congr fun n => by ring
  have hbadsmall : ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D → ∃ m ≥ max k m₀,
      K * T m * (τ / W * (1 * ε ^ (-α))) < D := by
    intro ε hε D hD
    have : Tendsto (fun m => K * T m * (τ / W * (1 * ε ^ (-α)))) atTop
        (𝓝 (K * 0 * (τ / W * (1 * ε ^ (-α))))) := (hT.const_mul K).mul_const _
    rw [mul_zero, zero_mul] at this
    obtain ⟨m, h1, h2⟩ := ((this.eventually (gt_mem_nhds hD)).and
      (eventually_ge_atTop (max k m₀))).exists
    exact ⟨m, h2, h1⟩
  -- comparison of the maxima
  have hlow : ∀ m ε, 0 < ε → ∀ᶠ n in atTop,
      P.real {ω | partialMax (fun n : ℕ => MovingAverage.process m ψ Z n) n ω ≤ (1 - ε) * u n} ≤
        P.real {ω | partialMax (fun n : ℕ => process ψ Z n) n ω ≤ u n} + P.real (Bd m ε n) := by
    intro m ε hε
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans
      (measureReal_union_le _ _)
    by_cases hb : ω ∈ Bd m ε n
    · exact Or.inr hb
    · left
      simp only [hBd, mem_ofPred_eq, not_exists, not_and, not_lt] at hb
      simp only [mem_ofPred_eq, partialMax_le_iff hn] at hω ⊢
      intro t ht
      have h1 := hω t ht
      have h2 := (abs_le.1 (hb t ht)).2
      linarith
  have hup : ∀ m ε, 0 < ε → ∀ᶠ n in atTop,
      P.real {ω | partialMax (fun n : ℕ => process ψ Z n) n ω ≤ u n} ≤
        P.real {ω | partialMax (fun n : ℕ => MovingAverage.process m ψ Z n) n ω ≤ (1 + ε) * u n} +
          P.real (Bd m ε n) := by
    intro m ε hε
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans
      (measureReal_union_le _ _)
    by_cases hb : ω ∈ Bd m ε n
    · exact Or.inr hb
    · left
      simp only [hBd, mem_ofPred_eq, not_exists, not_and, not_lt] at hb
      simp only [mem_ofPred_eq, partialMax_le_iff hn] at hω ⊢
      intro t ht
      have h1 := hω t ht
      have h2 := (abs_le.1 (hb t ht)).1
      linarith
  -- the limit
  rw [tendsto_order]
  constructor
  · intro A hA
    set D := (Real.exp (-(ϑ * τ)) - A) / 2 with hD
    have hD0 : 0 < D := by rw [hD]; linarith
    have hg : ContinuousAt (fun ε : ℝ => Real.exp (-(ϑ * τ * (1 - ε) ^ (-α)))) 0 :=
      ((continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inl (by norm_num)))).neg).rexp
    obtain ⟨ε, hεA, hε0, hε1⟩ := ((((hg.eventually (lt_mem_nhds (show A + D < _ by
      simp only [sub_zero, Real.one_rpow, mul_one]; rw [hD]; linarith))).filter_mono
      nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT one_pos)).exists : ∃ ε : ℝ, _ ∧ ε ∈ Set.Ioo 0 1)
    obtain ⟨m, hm, hmD⟩ := hbadsmall ε hε0 D hD0
    have hc : (0 : ℝ) < 1 - ε := by linarith
    filter_upwards [(hfin m (le_of_max_le_left hm) _ hc).eventually (lt_mem_nhds hεA),
      (hbadlim m ε hε0).eventually (gt_mem_nhds hmD), hbad m (le_of_max_le_right hm) ε hε0,
      hlow m ε hε0] with n h1 h2 h3 h4
    linarith
  · intro B hB
    set D := (B - Real.exp (-(ϑ * τ))) / 2 with hD
    have hD0 : 0 < D := by rw [hD]; linarith
    have hg : ContinuousAt (fun ε : ℝ => Real.exp (-(ϑ * τ * (1 + ε) ^ (-α)))) 0 :=
      ((continuousAt_const.mul ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (by norm_num)))).neg).rexp
    obtain ⟨ε, hεB, hε0, hε1⟩ := ((((hg.eventually (gt_mem_nhds (show _ < B - D by
      simp only [add_zero, Real.one_rpow, mul_one]; rw [hD]; linarith))).filter_mono
      nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT one_pos)).exists : ∃ ε : ℝ, _ ∧ ε ∈ Set.Ioo 0 1)
    obtain ⟨m, hm, hmD⟩ := hbadsmall ε hε0 D hD0
    have hc : (0 : ℝ) < 1 + ε := by linarith
    filter_upwards [(hfin m (le_of_max_le_left hm) _ hc).eventually (gt_mem_nhds hεB),
      (hbadlim m ε hε0).eventually (gt_mem_nhds hmD), hbad m (le_of_max_le_right hm) ε hε0,
      hup m ε hε0] with n h1 h2 h3 h4
    linarith


end InfiniteMovingAverage

end ExtremeValueTheory
