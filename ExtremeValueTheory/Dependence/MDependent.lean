/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Mixing

/-!
# Anticlustering and the extremal index of `m`-dependent sequences

For an `m`-dependent stationary series, exceedances at lags `t > m` are independent of an
exceedance at time `0`, so
`P(|X_0| > u, max_{m < |t| ≤ r} |X_t| > u) ≤ (2 r + 1) P(|X_0| > u)^2`: anticlustering holds as
soon as `rₙ P(|X_0| > uₙ) → 0`. Together with the block condition for `m`-dependent sequences
(`conditionA_of_isMDependent`) the main theorem `HasSpectralTailProcess.hasExtremalIndex_abs`
applies, and the extremal index equals the candidate extremal index: `θ = ϑ`.

## Main results, with the hypotheses each one uses

* `ExtremeValueTheory.antiClusteringAt_of_indepFun`: anticlustering `AntiClusteringAt` along
  `uₙ` from stationarity, independence of `X_0` and `X_t` for `t > m`, `P(|X_0| > uₙ) → 0` and
  `rₙ P(|X_0| > uₙ) → 0`.
* `ExtremeValueTheory.antiClusteringAt_of_tendsto_mul`: the same with `n P(|X_0| > uₙ) → τ` and
  `rₙ / n → 0` in place of the last two hypotheses.
* `ExtremeValueTheory.antiClustering_of_indepFun`: the condition `AC(rₙ)` of [BS09, (4.1)] under
  `n P(|X_0| > aₙ x) → x^(-α)`-type hypotheses, namely `n P(|X_0| > aₙ x)` convergent for every
  `x > 0` and `rₙ / n → 0`.
* `ExtremeValueTheory.HasSpectralTailProcess.hasExtremalIndex_of_isMDependent`: an `m`-dependent
  stationary series with a spectral tail process has extremal index `ϑ` (`θ = ϑ`), for `|X|`.
* `ExtremeValueTheory.hasShiftInvariantWindows_slidingWindow`,
  `ExtremeValueTheory.isMDependent_slidingWindow`: sliding window functionals
  `X_t = F(Z_{t + d_1}, …, Z_{t + d_K})` of iid `ℤ`-indexed noise are stationary and
  `m`-dependent when the offsets lie in an interval of length `m`.
* `ExtremeValueTheory.hasExtremalIndex_movingMax_of_antiClustering`: the moving maximum
  `max(Z_t, Z_{t+1})` of iid Pareto noise has extremal index `1/2`, now derived through the main
  theorem (an independent second proof of `hasExtremalIndex_movingMax`).
* `ExtremeValueTheory.MovingAverage.hasExtremalIndex`: the finite moving average
  `∑_{i ≤ m} ψ_i Z_{t-i}` (nonnegative coefficients and iid nonnegative regularly varying noise)
  has extremal index `max_j ψ_j^α / ∑_j ψ_j^α` ([EKM, §8.1], [DR85]).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace ExtremeValueTheory

/-! ### Anticlustering for sequences independent at large lags -/

section AntiClustering

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℤ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- Under stationarity, joint exceedances at lags `|t| > m` factorize when `X_0` and `X_t` are
independent for `t > m`: `P(|X_0| > u, |X_t| > u) = P(|X_0| > u)^2`. -/
theorem measureReal_lt_abs_inter_of_indepFun (hX : ∀ t, Measurable (X t))
    (hstat : HasShiftInvariantWindows P X) {m : ℕ}
    (hind : ∀ t : ℤ, (m : ℤ) < t → IndepFun (X 0) (X t) P) {t : ℤ} (ht : (m : ℤ) < |t|)
    (u : ℝ) :
    P.real ({ω | u < |X 0 ω|} ∩ {ω | u < |X t ω|}) = P.real {ω | u < |X 0 ω|} ^ 2 := by
  have hS : MeasurableSet {x : ℝ | u < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  -- marginals
  have hmarg : ∀ s : ℤ, P.real {ω | u < |X s ω|} = P.real {ω | u < |X 0 ω|} := by
    intro s
    have := hstat.measure_preimage_comp hX (fun _ : Unit => (0 : ℤ)) s
      (B := {y : Unit → ℝ | u < |y ()|}) (hS.preimage (measurable_pi_apply ()))
    simp only [zero_add, Set.mem_ofPred_eq] at this
    simp only [measureReal_def, this]
  -- the positive-lag case
  have hpos : ∀ s : ℤ, (m : ℤ) < s →
      P.real ({ω | u < |X 0 ω|} ∩ {ω | u < |X s ω|}) = P.real {ω | u < |X 0 ω|} ^ 2 := by
    intro s hs
    have h := (hind s hs).measure_inter_preimage_eq_mul _ _ hS hS
    have e : {ω | u < |X 0 ω|} ∩ {ω | u < |X s ω|} =
        X 0 ⁻¹' {x | u < |x|} ∩ X s ⁻¹' {x | u < |x|} := rfl
    rw [e, measureReal_def, h, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]
    change P.real {ω | u < |X 0 ω|} * P.real {ω | u < |X s ω|} = _
    rw [hmarg s, sq]
  rcases le_or_gt 0 t with h0 | h0
  · exact hpos t (by rwa [abs_of_nonneg h0] at ht)
  · -- negative lags: shift by `-t`
    have hB : MeasurableSet {y : Fin 2 → ℝ | u < |y 0| ∧ u < |y 1|} :=
      (hS.preimage (measurable_pi_apply 0)).inter (hS.preimage (measurable_pi_apply 1))
    have := hstat.measure_preimage_comp hX ![0, t] (-t) hB
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add,
      add_neg_cancel, Set.mem_ofPred_eq] at this
    have e1 : {ω | u < |X 0 ω|} ∩ {ω | u < |X t ω|} = {ω | u < |X 0 ω| ∧ u < |X t ω|} := rfl
    rw [e1, measureReal_def, ← this]
    have e2 : {ω | u < |X (-t) ω| ∧ u < |X 0 ω|} =
        {ω | u < |X 0 ω|} ∩ {ω | u < |X (-t) ω|} := by
      ext ω; simp [and_comm]
    rw [e2, ← measureReal_def]
    exact hpos (-t) (by rw [abs_of_neg h0] at ht; exact ht)

/-- **Anticlustering for sequences independent at lags `> m`.** If `X` is stationary, `X_0` and
`X_t` are independent for every `t > m`, `P(|X_0| > uₙ) → 0` and `rₙ P(|X_0| > uₙ) → 0`, then
`AntiClusteringAt P X u r` holds (with `m + 1` as the lag cutoff, for every `ε`). -/
theorem antiClusteringAt_of_indepFun (hX : ∀ t, Measurable (X t))
    (hstat : HasShiftInvariantWindows P X) {m : ℕ}
    (hind : ∀ t : ℤ, (m : ℤ) < t → IndepFun (X 0) (X t) P) {u : ℕ → ℝ} {r : ℕ → ℕ}
    (hp : Tendsto (fun n => P.real {ω | u n < |X 0 ω|}) atTop (𝓝 0))
    (hrp : Tendsto (fun n => (r n : ℝ) * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 0)) :
    AntiClusteringAt P X u r := by
  intro ε hε
  refine ⟨m + 1, ?_⟩
  have hlim : Tendsto (fun n => (2 * (r n : ℝ) + 1) * P.real {ω | u n < |X 0 ω|}) atTop
      (𝓝 0) := by
    have := (hrp.const_mul 2).add hp
    simp only [mul_zero, add_zero] at this
    exact this.congr fun n => by ring
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  set p := P.real {ω | u n < |X 0 ω|}
  set R : ℤ := (r n : ℤ)
  set T : Finset ℤ := (Icc (-R) R).filter fun t => (m : ℤ) < |t|
  have hsub : {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, ((m + 1 : ℕ) : ℤ) ≤ |t| ∧ |t| ≤ r n ∧
      u n < |X t ω|} ⊆ ⋃ t ∈ T, ({ω | u n < |X 0 ω|} ∩ {ω | u n < |X t ω|}) := by
    rintro ω ⟨h0, t, h1, h2, h3⟩
    refine Set.mem_iUnion₂.2 ⟨t, ?_, h0, h3⟩
    rw [mem_filter, mem_Icc]
    push_cast at h1
    refine ⟨⟨?_, ?_⟩, by omega⟩ <;> cases abs_cases t <;> omega
  have hcard : (#T : ℝ) ≤ 2 * r n + 1 := by
    have : #T ≤ #(Icc (-R) R) := card_filter_le _ _
    rw [Int.card_Icc] at this
    have h' : (#T : ℤ) ≤ 2 * R + 1 := by
      have := Int.toNat_of_nonneg (show 0 ≤ R + 1 - -R by omega)
      omega
    have h'' : #T ≤ 2 * r n + 1 := by omega
    exact_mod_cast h''
  calc P.real _ ≤ P.real (⋃ t ∈ T, ({ω | u n < |X 0 ω|} ∩ {ω | u n < |X t ω|})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ t ∈ T, P.real ({ω | u n < |X 0 ω|} ∩ {ω | u n < |X t ω|}) :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ _t ∈ T, p ^ 2 := sum_congr rfl fun t ht =>
        measureReal_lt_abs_inter_of_indepFun hX hstat hind (mem_filter.1 ht).2 (u n)
    _ = #T * p * p := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ (2 * r n + 1) * p * p := by gcongr
    _ ≤ ε * p := by gcongr

/-- `n pₙ → τ` and `rₙ / n → 0` give `rₙ pₙ → 0`. -/
theorem tendsto_mul_of_tendsto_natCast_mul {p : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * p n) atTop (𝓝 τ)) {r : ℕ → ℕ}
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n => (r n : ℝ) * p n) atTop (𝓝 0) := by
  have := hrn.mul hτ
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Anticlustering along `uₙ` for sequences independent at lags `> m`, when
`n P(|X_0| > uₙ) → τ` and `rₙ / n → 0`. -/
theorem antiClusteringAt_of_tendsto_mul (hX : ∀ t, Measurable (X t))
    (hstat : HasShiftInvariantWindows P X) {m : ℕ}
    (hind : ∀ t : ℤ, (m : ℤ) < t → IndepFun (X 0) (X t) P) {u : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) {r : ℕ → ℕ}
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0)) : AntiClusteringAt P X u r :=
  antiClusteringAt_of_indepFun hX hstat hind (tendsto_zero_of_tendsto_natCast_mul' hτ)
    (tendsto_mul_of_tendsto_natCast_mul hτ hrn)

/-- **`AC(rₙ)` for sequences independent at lags `> m`** ([BS09, (4.1)]): if `X` is stationary,
`X_0` and `X_t` are independent for `t > m`, `rₙ / n → 0` and for every `x > 0` the sequence
`n P(|X_0| > aₙ x)` converges (as it does when `n P(|X_0| > aₙ) → 1` and the tail is regularly
varying), then `AntiClustering P X a r`. -/
theorem antiClustering_of_indepFun (hX : ∀ t, Measurable (X t))
    (hstat : HasShiftInvariantWindows P X) {m : ℕ}
    (hind : ∀ t : ℤ, (m : ℤ) < t → IndepFun (X 0) (X t) P) {a : ℕ → ℝ} {r : ℕ → ℕ}
    (ha : ∀ x : ℝ, 0 < x → ∃ τ : ℝ,
      Tendsto (fun n : ℕ => n * P.real {ω | a n * x < |X 0 ω|}) atTop (𝓝 τ))
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0)) : AntiClustering P X a r := by
  intro x hx
  obtain ⟨τ, hτ⟩ := ha x hx
  exact antiClusteringAt_of_tendsto_mul hX hstat hind hτ hrn

end AntiClustering

/-! ### The extremal index of `m`-dependent series -/

section ExtremalIndex

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

theorem tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * b, fun n hn => by
    rw [← Nat.sqrt_eq b]; exact Nat.sqrt_le_sqrt hn⟩

theorem tendsto_sqrt_div : Tendsto (fun n => (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => 1 / (Nat.sqrt n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp tendsto_sqrt_atTop)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hinv
  filter_upwards [tendsto_sqrt_atTop.eventually_ge_atTop 1] with n hn
  have hs : (0 : ℝ) < Nat.sqrt n := by exact_mod_cast hn
  have hle : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by exact_mod_cast Nat.sqrt_le n
  rw [div_le_div_iff₀ (by nlinarith) hs]
  nlinarith

/-- `|X|` restricted to `ℕ` is stationary for a stationary `ℤ`-indexed series. -/
theorem HasShiftInvariantWindows.isStationary_abs (hX : ∀ t, Measurable (X t))
    (hstat : HasShiftInvariantWindows P X) : IsStationary (fun k : ℕ => |X k|) P := by
  have := (hstat.isStationary_nat hX).factor (fun n => hX n)
    (f := fun z : ℕ → ℝ => |z 0|) (continuous_abs.measurable.comp (measurable_pi_apply 0))
  convert this using 3 with t ω
  simp

/-- **`θ = ϑ` for `m`-dependent series** ([BS09, §4], [KS20, §7.5]). Let `(X_t)_{t ∈ ℤ}` be
stationary with spectral tail process `Θ` and let its restriction `(X_n)_{n ∈ ℕ}` be `m`-dependent.
Then `(|X_n|)_{n ∈ ℕ}` has extremal index `ϑ`, the candidate extremal index of `Θ`.

Proof: the main theorem `HasSpectralTailProcess.hasExtremalIndex_abs` with block lengths
`rₙ = ⌊√n⌋`; anticlustering by `antiClusteringAt_of_tendsto_mul` (independence at lags `> m`),
the block condition by `conditionA_of_isMDependent` (applied to `|X|`, which is `m`-dependent). -/
theorem HasSpectralTailProcess.hasExtremalIndex_of_isMDependent (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {m : ℕ}
    (hm : IsMDependent (fun n : ℕ => X n) m P) :
    HasExtremalIndex (fun k : ℕ => |X k|) P (candidateExtremalIndex Q Θ α).toReal := by
  have hind : ∀ t : ℤ, (m : ℤ) < t → IndepFun (X 0) (X t) P := by
    intro t ht
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
    exact hm.indepFun (s := 0) (t := k) (by omega)
  have hmabs : IsMDependent (fun k : ℕ => |X k|) m P := by
    have := hm.comp continuous_abs.measurable
    exact this
  refine h.hasExtremalIndex_abs hα hX hΘm hstat tendsto_sqrt_atTop tendsto_sqrt_div
    fun τ _ u hu => ⟨(antiClusteringAt_of_tendsto_mul hX hstat hind hu tendsto_sqrt_div).forward,
      conditionA_of_isMDependent (hstat.isStationary_abs hX)
        (fun k => (continuous_abs.measurable.comp (hX k))) hmabs tendsto_sqrt_atTop
        tendsto_sqrt_div (C := τ + 1) ?_⟩
  filter_upwards [hu.eventually (gt_mem_nhds (lt_add_one τ))] with n hn
  exact hn.le

end ExtremalIndex

end ExtremeValueTheory
