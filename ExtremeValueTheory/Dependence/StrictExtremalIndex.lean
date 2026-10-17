/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MDependentExamples
import ExtremeValueTheory.Dependence.InfiniteMovingAverageTailProcess
import ExtremeValueTheory.Dependence.AR1

/-!
# Exceedance levels for regularly varying tails and strict extremal indices

`HasExtremalIndex X P θ` quantifies over level sequences `uₙ` with `n P(X_0 > uₙ) → τ`; it is
vacuous at values `τ` attained by no such sequence. `HasExtremalIndexStrict` adds the existence of
such levels for every `τ > 0`, which makes `θ` unique (`HasExtremalIndexStrict.unique`).

For a regularly varying tail `F̄(x) = P(X_0 > x)` such levels always exist ([LLR, Theorem 1.7.13]):
`F̄(x-) / F̄(x) → 1`, so the quantile levels `uₙ ≈ inf {x : F̄(x) ≤ τ / n}` satisfy
`n F̄(uₙ) → τ`. We prove this without left limits: `F̄((1 - ε) uₙ) > τ / n ≥ F̄(uₙ)` and
`F̄((1 - ε) x) / F̄(x) → (1 - ε)^ρ`, which is close to `1` for small `ε`.

## Main results

* `hasExceedanceLevels_of_isRegularlyVarying`: a regularly varying marginal tail (any index)
  admits exceedance levels.
* `HasSpectralTailProcess.hasExceedanceLevels_abs`: hence `(|X_n|)` admits exceedance levels
  whenever `X` has a spectral tail process.
* Strict versions (`HasExtremalIndexStrict`, so `θ` is unique) of the extremal-index theorems:
  `HasSpectralTailProcess.hasExtremalIndex_abs_strict`,
  `HasSpectralTailProcess.hasExtremalIndex_of_isMDependent_strict`,
  `hasExtremalIndex_movingMax_of_isMDependent_strict`, `MovingAverage.hasExtremalIndex_strict`,
  `InfiniteMovingAverage.hasExtremalIndex_strict`, `AR1.hasExtremalIndex_strict`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace ExtremeValueTheory

section Levels

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- **Exceedance levels for a regularly varying tail** ([LLR, Theorem 1.7.13]): if
`x ↦ P(X_0 > x)` is regularly varying (of any index `ρ`), then for every `τ > 0` there are levels
`uₙ` with `n P(X_0 > uₙ) → τ`. -/
theorem hasExceedanceLevels_of_isRegularlyVarying (hX0 : Measurable (X 0)) {ρ : ℝ}
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < X 0 ω}) ρ) : HasExceedanceLevels X P := by
  classical
  set F : ℝ → ℝ := fun x => P.real {ω | x < X 0 ω} with hF
  have hanti : Antitone F := fun x y hxy =>
    measureReal_mono fun ω (hω : y < X 0 ω) => lt_of_le_of_lt hxy hω
  -- `F → 0` at `∞`
  have htop : Tendsto F atTop (𝓝 0) := by
    have hcdf : ∀ x, F x = 1 - cdf (P.map (X 0)) x := fun x => by
      rw [cdf_eq_real, map_measureReal_apply hX0 measurableSet_Iic]
      have : {ω | x < X 0 ω} = (X 0 ⁻¹' Iic x)ᶜ := by ext; simp
      rw [hF]
      simp only
      rw [this, probReal_compl_eq_one_sub (hX0 measurableSet_Iic)]
    have := (tendsto_cdf_atTop (P.map (X 0))).const_sub 1
    rw [sub_self] at this
    exact this.congr fun x => (hcdf x).symm
  -- `F > 0` everywhere
  have hpos : ∀ x, 0 < F x := by
    intro x
    obtain ⟨y, hxy, hy⟩ := ((eventually_ge_atTop x).and hRV.1).exists
    exact hy.trans_le (hanti hxy)
  intro τ hτ
  set S : ℕ → Set ℝ := fun n => {x | 0 ≤ x ∧ F x ≤ τ / n}
  have hSne : ∀ n : ℕ, 0 < n → (S n).Nonempty := by
    intro n hn
    have hτn : 0 < τ / n := div_pos hτ (by exact_mod_cast hn)
    obtain ⟨x, hx⟩ := (htop.eventually (ge_mem_nhds hτn)).exists
    exact ⟨max x 0, le_max_right _ _, (hanti (le_max_left _ _)).trans hx⟩
  have hSbdd : ∀ n, BddBelow (S n) := fun n => ⟨0, fun x hx => hx.1⟩
  set s : ℕ → ℝ := fun n => sInf (S n)
  have hchoose : ∀ n : ℕ, 0 < n → ∃ x ∈ S n, x < s n + 1 := fun n hn =>
    exists_lt_of_csInf_lt (hSne n hn) (lt_add_one _)
  set u : ℕ → ℝ := fun n => if hn : 0 < n then (hchoose n hn).choose else 0
  have huS : ∀ n : ℕ, 0 < n → u n ∈ S n := fun n hn => by
    simp only [u, hn, dite_true]; exact (hchoose n hn).choose_spec.1
  have hus : ∀ n : ℕ, 0 < n → u n < s n + 1 := fun n hn => by
    simp only [u, hn, dite_true]; exact (hchoose n hn).choose_spec.2
  -- below `s n`, the tail exceeds `τ / n`
  have hbelow : ∀ n : ℕ, ∀ y, 0 ≤ y → y < s n → τ / n < F y := by
    intro n y hy hys
    by_contra hc
    exact absurd (csInf_le (hSbdd n) ⟨hy, not_lt.1 hc⟩) (not_le.2 hys)
  -- `s n → ∞`
  have hs : Tendsto s atTop atTop := by
    rw [tendsto_atTop]
    intro C
    have h0 : Tendsto (fun n : ℕ => τ / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [h0.eventually (gt_mem_nhds (hpos C)), eventually_gt_atTop 0] with n hn hn0
    refine le_csInf (hSne n hn0) fun x hx => ?_
    by_contra hc
    exact absurd ((hanti (not_le.1 hc).le).trans hx.2) (not_le.2 hn)
  have hu : Tendsto u atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hs
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact csInf_le (hSbdd n) (huS n hn)
  have hupper : ∀ n : ℕ, 0 < n → n * F (u n) ≤ τ := fun n hn => by
    have := (huS n hn).2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn'] at this
    linarith
  refine ⟨u, tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩⟩
  · rcases le_or_gt a 0 with ha0 | ha0
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact ha0.trans_lt (mul_pos (by exact_mod_cast hn) (hpos _))
    -- choose `1 < c` with `a c < τ` and `t < 1` with `t ^ ρ < c`
    obtain ⟨c, hc1, hc⟩ := exists_between (show 1 < τ / a by rw [one_lt_div ha0]; exact ha)
    have hcont : Tendsto (fun t : ℝ => t ^ ρ) (𝓝 1) (𝓝 1) := by
      simpa using (Real.continuousAt_rpow_const 1 ρ (Or.inl one_ne_zero)).tendsto
    obtain ⟨t, htc, ht0, ht1⟩ := (((hcont.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hc1)).and (Ioo_mem_nhdsLT zero_lt_one)).exists
    have hratio := (hRV.2 t ht0).comp hu
    filter_upwards [hratio.eventually (gt_mem_nhds htc), hs.eventually_ge_atTop (t / (1 - t)),
      eventually_gt_atTop 0] with n hn hsn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hu0 : 0 ≤ u n := (huS n hn0).1
    have hts : t * u n < s n := by
      have h1t : 0 < 1 - t := by linarith
      have : t ≤ s n * (1 - t) := by rwa [div_le_iff₀ h1t] at hsn
      nlinarith [hus n hn0]
    have h1 := hbelow n (t * u n) (mul_nonneg ht0.le hu0) hts
    have h2 : F (t * u n) < c * F (u n) := by
      have := hn
      simp only [Function.comp] at this
      rwa [div_lt_iff₀ (hpos _)] at this
    have h3 : τ < n * (c * F (u n)) := by
      rw [div_lt_iff₀ hn'] at h1
      nlinarith
    have hac : a * c < τ := by rwa [lt_div_iff₀ ha0, mul_comm] at hc
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (hupper n hn).trans_lt hb

/-- A regularly varying marginal tail gives the strict extremal index from the extremal index. -/
theorem HasExtremalIndex.strict_of_isRegularlyVarying {θ : ℝ} (h : HasExtremalIndex X P θ)
    (hX0 : Measurable (X 0)) {ρ : ℝ}
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < X 0 ω}) ρ) :
    HasExtremalIndexStrict X P θ :=
  ⟨h, hasExceedanceLevels_of_isRegularlyVarying hX0 hRV⟩

end Levels

section TailProcess

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

omit [IsProbabilityMeasure Q] in
/-- A series with a spectral tail process has exceedance levels for `(|X_n|)_{n ∈ ℕ}`: its
marginal tail `P(|X_0| > x)` is regularly varying. -/
theorem HasSpectralTailProcess.hasExceedanceLevels_abs (h : HasSpectralTailProcess P X α Q Θ)
    (hX0 : Measurable (X 0)) : HasExceedanceLevels (fun k : ℕ => |X k|) P :=
  hasExceedanceLevels_of_isRegularlyVarying (X := fun k : ℕ => |X k|)
    (continuous_abs.measurable.comp hX0 :) (by simpa using h.1)

omit [IsProbabilityMeasure Q] in
/-- The nonnegative version of `HasSpectralTailProcess.hasExceedanceLevels_abs`. -/
theorem HasSpectralTailProcess.hasExceedanceLevels_of_nonneg
    (h : HasSpectralTailProcess P X α Q Θ) (hX0 : Measurable (X 0)) (hnn : ∀ ω, 0 ≤ X 0 ω) :
    HasExceedanceLevels (fun k : ℕ => X k) P :=
  hasExceedanceLevels_of_isRegularlyVarying (X := fun k : ℕ => X k) (by simpa using hX0)
    (by simpa [abs_of_nonneg (hnn _)] using h.1)

/-- **Strict form of `HasSpectralTailProcess.hasExtremalIndex_abs`**: `θ = ϑ` for `(|X_n|)`, and
`θ` is the unique extremal index. -/
theorem HasSpectralTailProcess.hasExtremalIndex_abs_strict (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hcond : ∀ τ > 0, ∀ u : ℕ → ℝ,
      Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ) →
        ForwardAntiClusteringAt P X u r ∧ ConditionA (fun k : ℕ => |X k|) P u r) :
    HasExtremalIndexStrict (fun k : ℕ => |X k|) P (candidateExtremalIndex Q Θ α).toReal :=
  ⟨h.hasExtremalIndex_abs hα hX hΘm hstat hr hrn hcond, h.hasExceedanceLevels_abs (hX 0)⟩

/-- **Strict form of `HasSpectralTailProcess.hasExtremalIndex_of_isMDependent`**. -/
theorem HasSpectralTailProcess.hasExtremalIndex_of_isMDependent_strict (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {m : ℕ}
    (hm : IsMDependent (fun n : ℕ => X n) m P) :
    HasExtremalIndexStrict (fun k : ℕ => |X k|) P (candidateExtremalIndex Q Θ α).toReal :=
  ⟨h.hasExtremalIndex_of_isMDependent hα hX hΘm hstat hm, h.hasExceedanceLevels_abs (hX 0)⟩

end TailProcess

section Examples

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℤ → Ω → ℝ} {α : ℝ}

/-- **Strict form of `hasExtremalIndex_movingMax_of_isMDependent`**: the moving maximum of iid
Pareto noise has the unique extremal index `1/2`. -/
theorem hasExtremalIndex_movingMax_of_isMDependent_strict (hα : 0 < α)
    (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω) :
    HasExtremalIndexStrict (fun n : ℕ => movingMax Z n) P 2⁻¹ :=
  ⟨hasExtremalIndex_movingMax_of_isMDependent hα hZ hind hlaw hpos,
    (hasSpectralTailProcess_movingMax hα hZ hind hlaw hpos).hasExceedanceLevels_of_nonneg
      ((hZ 0).max (hZ (0 + 1))) fun ω => (hpos 0 ω).trans (le_max_left _ _)⟩

/-- **Strict form of `MovingAverage.hasExtremalIndex`**. -/
theorem MovingAverage.hasExtremalIndex_strict {m : ℕ} {ψ : ℕ → ℝ} (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψm : ∀ j, m < j → ψ j = 0) (hW : 0 < MovingAverage.weightSum m ψ α) :
    HasExtremalIndexStrict (fun n : ℕ => MovingAverage.process m ψ Z n) P
      ((Finset.range (m + 1)).sup' Finset.nonempty_range_add_one ψ ^ α /
        ∑ j ∈ Finset.range (m + 1), ψ j ^ α) :=
  ⟨MovingAverage.hasExtremalIndex hZ hind hident hZ0 hα hL hψ0 hψm hW,
    (MovingAverage.exists_hasSpectralTailProcess_candidateExtremalIndex_eq hZ hind hident hZ0 hα
      hL hψ0 hψm hW).1.hasExceedanceLevels_of_nonneg (MovingAverage.measurable_process hZ 0)
      (MovingAverage.process_nonneg hψ0 hZ0 0)⟩

/-- **Strict form of `InfiniteMovingAverage.hasExtremalIndex`**. -/
theorem InfiniteMovingAverage.hasExtremalIndex_strict {ψ : ℕ → ℝ} {δ : ℝ}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasExtremalIndexStrict (fun n : ℕ => InfiniteMovingAverage.process ψ Z n) P
      ((⨆ j, ψ j) ^ α / ∑' j, ψ j ^ α) :=
  ⟨InfiniteMovingAverage.hasExtremalIndex hZ hind hident hZ0 hδ hδα hα1 hL hψ0 hψ hpos,
    (InfiniteMovingAverage.hasSpectralTailProcess hZ hind hident hZ0 hδ hδα hα1 hL hψ0 hψ
      hpos).hasExceedanceLevels_of_nonneg (InfiniteMovingAverage.measurable_process hZ 0)
      (InfiniteMovingAverage.process_nonneg hψ0 hZ0 0)⟩

/-- **Strict form of `AR1.hasExtremalIndex`**: the AR(1) process has the unique extremal index
`1 - φ^α`. -/
theorem AR1.hasExtremalIndex_strict {φ : ℝ} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hα1 : α < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    HasExtremalIndexStrict (fun n : ℕ => AR1.process φ Z n) P (1 - φ ^ α) := by
  have hδ : 0 < α / 2 := by positivity
  exact ⟨AR1.hasExtremalIndex hZ hind hident hZ0 hα hα1 hL hφ0 hφ1,
    (InfiniteMovingAverage.hasSpectralTailProcess (ψ := fun j => φ ^ j) hZ hind hident hZ0 hδ
      (by linarith) hα1 hL (fun j => pow_nonneg hφ0.le j) (AR1.summable_rpow hφ0 hφ1 hδ)
      ⟨0, by simp⟩).hasExceedanceLevels_of_nonneg
      (InfiniteMovingAverage.measurable_process hZ 0)
      (InfiniteMovingAverage.process_nonneg (fun j => pow_nonneg hφ0.le j) hZ0 0)⟩

end Examples

end ExtremeValueTheory
