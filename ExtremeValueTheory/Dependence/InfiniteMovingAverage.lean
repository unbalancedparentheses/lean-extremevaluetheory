/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MDependentExamples
import ExtremeValueTheory.HeavyTails.LinearProcessSeries

/-!
# The extremal index of an infinite moving average

Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative random variables with `P(Z_0 > x)` regularly varying with
index `-α`, and let `ψ_j ≥ 0`, `j ∈ ℕ`, be coefficients, not all zero, with `∑ ψ_j^δ < ∞` for
some `0 < δ < α < 1`. The infinite moving average

  `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}`

converges almost surely (`LinearProcess.ae_summable_mul`), and has extremal index

  `θ = sup_j ψ_j^α / ∑_j ψ_j^α`

([DR85], [EKM, §8.1], [KS20, Chapter 15]). We prove this by approximation with the finite moving
averages `X^{(m)}_t = ∑_{j ≤ m} ψ_j Z_{t-j}`, which are `m`-dependent and whose extremal index
`max_{j ≤ m} ψ_j^α / ∑_{j ≤ m} ψ_j^α` is `MovingAverage.hasExtremalIndex` (derived through the
main theorem `θ = ϑ`).

## Main results

* `InfiniteMovingAverage.tendsto_measureReal_process_div`:
  `P(X_0 > x) / P(Z_0 > x) → ∑_j ψ_j^α`.
* `InfiniteMovingAverage.exists_measureReal_abs_sub_gt_le`: the remainder bound
  `P(|X_t - X^{(m)}_t| > y) ≤ K (∑_{j > m} ψ_j^δ) P(Z_0 > y)`, uniformly in `t`, `m ≥ m₀` and
  `y ≥ x₀`.
* `InfiniteMovingAverage.hasExtremalIndex`: the extremal index of `X` is
  `(sup_j ψ_j)^α / ∑_j ψ_j^α`.
* The AR(1) process `X_t = φ X_{t-1} + Z_t`, `0 < φ < 1`, i.e. `ψ_j = φ^j`, has extremal
  index `1 - φ^α`: `AR1.hasExtremalIndex` in `Dependence/AR1.lean`.
* The spectral tail process `Θ_t = ψ_{J+t} / ψ_J` and `θ = ϑ`:
  `Dependence/InfiniteMovingAverageTailProcess.lean`.

## Hypotheses

The restriction `α < 1` is inherited from `LinearProcess.exists_measure_tsum_gt_le` (the uniform
remainder bound uses Karamata's theorem for the truncated first moment). The noise is nonnegative
and the coefficients are nonnegative, as for `MovingAverage.hasExtremalIndex`.

## Proof

Write `M_n`, `M^{(m)}_n` for the partial maxima, `u_n` a level sequence with
`n P(X_0 > u_n) → τ`, and `L(x) = P(Z_0 > x)`. Then `u_n → ∞` and `n L(u_n) → τ / ∑ψ^α`. For
`m` beyond an index `j*` where `sup ψ = ψ_{j*}` is attained, and `c > 0`,
`n P(X^{(m)}_0 > c u_n) → c^{-α} τ ∑_{j ≤ m} ψ_j^α / ∑ ψ^α`, so the finite theorem gives
`P(M^{(m)}_n ≤ c u_n) → exp(-ϑ τ c^{-α})`. On the complement of
`bad_n = {∃ t < n, |X_t - X^{(m)}_t| > ε u_n}`,

  `M^{(m)}_n ≤ (1 - ε) u_n ⟹ M_n ≤ u_n ⟹ M^{(m)}_n ≤ (1 + ε) u_n`,

and `P(bad_n) ≤ n K T_m L(ε u_n) → K T_m ε^{-α} τ / ∑ψ^α`, `T_m = ∑_{j > m} ψ_j^δ → 0`.
Choosing first `ε`, then `m`, the limit follows.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal

namespace ExtremeValueTheory

namespace InfiniteMovingAverage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The infinite moving average `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` (the `tsum` is `0` where the
series does not converge, a null event under the hypotheses of `LinearProcess.ae_summable_mul`). -/
noncomputable def process (ψ : ℕ → ℝ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  ∑' j : ℕ, ψ j * Z (t - j) ω

variable [IsProbabilityMeasure P] {Z : ℤ → Ω → ℝ} {ψ : ℕ → ℝ} {α δ : ℝ}

theorem setOf_lt_abs_eq (hZ0 : ∀ i ω, 0 ≤ Z i ω) (x : ℝ) :
    {ω | x < |Z 0 ω|} = {ω | x < Z 0 ω} := by
  ext ω; simp [abs_of_nonneg (hZ0 0 ω)]

theorem summable_abs_rpow (hψ0 : ∀ j, 0 ≤ ψ j) (hψ : Summable fun j => ψ j ^ δ) :
    Summable fun j => |ψ j| ^ δ := by
  simpa only [abs_of_nonneg (hψ0 _)] using hψ

/-- `∑ ψ_j^α < ∞` when `∑ ψ_j^δ < ∞`, `0 < δ ≤ α`. -/
theorem summable_rpow (hψ0 : ∀ j, 0 ≤ ψ j) (hδ : 0 < δ) (hδα : δ ≤ α)
    (hψ : Summable fun j => ψ j ^ δ) : Summable fun j => ψ j ^ α := by
  have := LinearProcess.summable_tailWeight (p := 1) hδ hδα zero_le_one le_rfl
    (summable_abs_rpow hψ0 hψ)
  refine this.congr fun j => ?_
  rcases (hψ0 j).eq_or_lt with h0 | hpos
  · rw [← h0, LinearProcess.tailWeight_zero, Real.zero_rpow (hδ.trans_le hδα).ne']
  · rw [LinearProcess.tailWeight_of_pos hpos, mul_one]

/-- **Tail of the infinite moving average**: `P(X_0 > x) / P(Z_0 > x) → ∑_j ψ_j^α`
(`0 < δ < α < 1`, `∑ ψ_j^δ < ∞`). -/
theorem tendsto_measureReal_process_div (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
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
  have h := LinearProcess.tendsto_measureReal_tsum_mul_div (Z := fun i : ℕ => Z (0 - i))
    (fun i => hZ _) (hZ 0) (hind.precomp hinj) (fun i => hident _) hδ hδα hα1 hL' hp
    (summable_abs_rpow hψ0 hψ)
  simp only [setOf_lt_abs_eq hZ0] at h
  have hW : ∑' j, ψ j ^ α = ∑' j, LinearProcess.tailWeight α 1 (ψ j) := by
    refine tsum_congr fun j => ?_
    rcases (hψ0 j).eq_or_lt with h0 | hpos
    · rw [← h0, LinearProcess.tailWeight_zero, Real.zero_rpow (hδ.trans hδα).ne']
    · rw [LinearProcess.tailWeight_of_pos hpos, mul_one]
  rw [hW]
  exact h

/-- **Uniform remainder bound** (`0 < δ < α < 1`): there are `K, x₀ > 0` and `m₀` such that for
all `m ≥ m₀`, `t ∈ ℤ` and `y ≥ x₀`,
`P(|X_t - X^{(m)}_t| > y) ≤ K (∑_{j > m} ψ_j^δ) P(Z_0 > y)`. Independence is not needed. -/
theorem exists_measureReal_abs_sub_gt_le (hZ : ∀ i, Measurable (Z i))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) :
    ∃ K x₀ : ℝ, ∃ m₀ : ℕ, 0 < K ∧ 0 < x₀ ∧ ∀ m ≥ m₀, ∀ t : ℤ, ∀ y ≥ x₀,
      P.real {ω | y < |process ψ Z t ω - MovingAverage.process m ψ Z t ω|} ≤
        K * (∑' j, ψ (j + (m + 1)) ^ δ) * P.real {ω | y < Z 0 ω} := by
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [setOf_lt_abs_eq hZ0] using hL
  obtain ⟨K, x₀, hK, hx₀, hR⟩ := LinearProcess.exists_measure_tsum_gt_le (hZ 0) hδα hα1 hL'
  obtain ⟨m₀, hm₀⟩ := LinearProcess.exists_abs_le_one hδ (summable_abs_rpow hψ0 hψ)
  refine ⟨K, x₀, m₀, hK, hx₀, fun m hm t y hy => ?_⟩
  have hy0 : 0 ≤ y := hx₀.le.trans hy
  have h := hR (fun j => Z (t - ((j + (m + 1) : ℕ) : ℤ))) (fun j => hZ _) (fun j => hident _)
    (fun j => ψ (j + (m + 1))) (fun j => hm₀ _ (by omega))
    ((summable_nat_add_iff (m + 1)).2 (summable_abs_rpow hψ0 hψ)) y hy
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

/-! ### Levels -/

omit [IsProbabilityMeasure P] in
/-- **Levels**: if `F / L → w`, `L` is regularly varying with index `-α`, `u_n → ∞`,
`n L(u_n) → s` and `c > 0`, then `n F(c u_n) → s (w c^{-α})`. -/
theorem tendsto_natCast_mul_comp_mul {F L : ℝ → ℝ} {w s c : ℝ} (hL : IsRegularlyVarying L (-α))
    (hF : Tendsto (fun x => F x / L x) atTop (𝓝 w)) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    (hs : Tendsto (fun n : ℕ => n * L (u n)) atTop (𝓝 s)) (hc : 0 < c) :
    Tendsto (fun n : ℕ => n * F (c * u n)) atTop (𝓝 (s * (w * c ^ (-α)))) := by
  have h := (LinearProcess.tendsto_comp_mul_div hL hF hc).comp hu
  refine (hs.mul h).congr' ?_
  filter_upwards [hu.eventually hL.1] with n hn
  have := hn.ne'
  simp only [Function.comp]
  field_simp

omit [IsProbabilityMeasure P] in
/-- If `n F(u_n) → τ`, `F / L → w > 0`, `F ≥ 0` antitone and `L > 0` eventually, then `u_n → ∞`
and `n L(u_n) → τ / w`. -/
theorem tendsto_atTop_of_tendsto_natCast_mul {F L : ℝ → ℝ} {w τ : ℝ} (hFa : Antitone F)
    (hF0 : ∀ x, 0 ≤ F x) (hL : ∀ᶠ x in atTop, 0 < L x) (hw : 0 < w)
    (hF : Tendsto (fun x => F x / L x) atTop (𝓝 w)) {u : ℕ → ℝ}
    (hu : Tendsto (fun n : ℕ => n * F (u n)) atTop (𝓝 τ)) :
    Tendsto u atTop atTop ∧ Tendsto (fun n : ℕ => n * L (u n)) atTop (𝓝 (τ / w)) := by
  have hpos : ∀ B, 0 < F B := by
    intro B
    obtain ⟨x, hx, hxB⟩ := ((hF.eventually (lt_mem_nhds hw)).and (eventually_ge_atTop B)).exists
    refine lt_of_lt_of_le ?_ (hFa hxB)
    rcases (hF0 x).eq_or_lt with h0 | h0
    · rw [← h0, zero_div] at hx; exact absurd hx (lt_irrefl _)
    · exact h0
  have hFu : Tendsto (fun n : ℕ => F (u n)) atTop (𝓝 0) := by
    have := hu.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hut : Tendsto u atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [hFu.eventually (gt_mem_nhds (hpos B))] with n hn
    by_contra h
    push Not at h
    exact absurd (hFa h.le) (not_le.2 hn)
  refine ⟨hut, (hu.div (hF.comp hut) hw.ne').congr' ?_⟩
  filter_upwards [hut.eventually hL] with n hn
  have h1 := hn.ne'
  have h2 := (hpos (u n)).ne'
  show (n : ℝ) * F (u n) / (F (u n) / L (u n)) = n * L (u n)
  field_simp

/-! ### The extremal index -/

/-- Under `∑ ψ_j^δ < ∞`, `ψ ≥ 0`, not all zero, the supremum of `ψ` is attained. -/
theorem exists_forall_le (hψ0 : ∀ j, 0 ≤ ψ j) (hδ : 0 < δ) (hψ : Summable fun j => ψ j ^ δ)
    (hpos : ∃ j, 0 < ψ j) : ∃ k, 0 < ψ k ∧ ∀ j, ψ j ≤ ψ k := by
  obtain ⟨j₀, hj₀⟩ := hpos
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hψ.tendsto_atTop_zero).eventually
    (gt_mem_nhds (Real.rpow_pos_of_pos hj₀ δ)))
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (range (N + j₀ + 1)) ψ
    ⟨j₀, mem_range.2 (by omega)⟩
  have hj₀k : ψ j₀ ≤ ψ k := hmax j₀ (mem_range.2 (by omega))
  refine ⟨k, hj₀.trans_le hj₀k, fun j => ?_⟩
  by_cases hj : j < N + j₀ + 1
  · exact hmax j (mem_range.2 hj)
  · have := hN j (by omega)
    rw [Real.rpow_lt_rpow_iff (hψ0 j) hj₀.le hδ] at this
    exact this.le.trans hj₀k

/-- **The extremal index of an infinite moving average** ([DR85], [EKM, §8.1], [KS20, Chapter
15]). Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative with `P(Z_0 > x)` regularly varying with index `-α`,
`0 < δ < α < 1`, and let `ψ_j ≥ 0`, not all zero, with `∑ ψ_j^δ < ∞`. Then
`X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` has extremal index `θ = (sup_j ψ_j)^α / ∑_j ψ_j^α`.

Proof by approximation with the `m`-dependent finite moving averages
(`MovingAverage.hasExtremalIndex`, derived through the main theorem `θ = ϑ`), using the uniform
remainder bound `exists_measureReal_abs_sub_gt_le`. -/
theorem hasExtremalIndex (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
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
    hL.1 hW (tendsto_measureReal_process_div hZ hind hident hZ0 hδ hδα hα1 hL hψ0 hψ) hu
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
    exists_measureReal_abs_sub_gt_le hZ hident hZ0 hδ hδα hα1 hL hψ0 hψ
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
