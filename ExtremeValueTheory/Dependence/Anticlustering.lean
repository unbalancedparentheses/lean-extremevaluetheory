/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.StationaryWindows
import ExtremeValueTheory.Dependence.ExtremalIndex
import ExtremeValueTheory.Dependence.Anticlustering.BlockRatio

/-!
# Anticlustering and the extremal index

We link the candidate extremal index `ϑ = E[sup_{k ≥ 0} |Θ_k|^α - sup_{k ≥ 1} |Θ_k|^α]` of a
stationary regularly varying series ([KS20, §7.5], [Planinić–Soulier 2018]) with the block
extremal index `θ` of `Dependence/ExtremalIndex.lean`, following [BS09, §4] and [KS20, §6.1, §7.5].

Throughout, `|X|` is used: `M_r = max_{0 ≤ t < r} |X_t|`. For `X ≥ 0` this is the usual maximum.

## Main definitions

* `AntiClusteringAt P X u r`: anticlustering along a level sequence `uₙ` with block lengths `rₙ`,
  `lim_m limsup_n P(max_{m ≤ |t| ≤ rₙ} |X_t| > uₙ | |X_0| > uₙ) = 0`, in `ε`–`m` form.
* `ForwardAntiClusteringAt P X u r`: its forward half (`m ≤ t ≤ rₙ`); all results use only this.
* `AntiClustering P X a r`: the condition `AC(rₙ)` of [BS09, Condition 4.1], [KS20, §6.1]
  (`AntiClusteringAt` at every level `aₙ x`, `x > 0`).
* `ConditionA X P u r`: the block condition `P(M n ≤ uₙ) - P(M rₙ ≤ uₙ) ^ ⌊n / rₙ⌋ → 0`.

## Main results, with the hypotheses each one uses

* `HasSpectralTailProcess.tendsto_cond_forall_le`, `HasSpectralTailProcess.tendsto_cond_exists_lt`:
  conditional window probabilities converge to those of the tail process `Y = R Θ`
  (spectral tail process only).
* `HasSpectralTailProcess.tendsto_zero_of_forwardAntiClusteringAt`: forward anticlustering at a
  single level sequence `uₙ → ∞` with `rₙ → ∞` implies `Θ_t → 0` a.s. (no stationarity).
* `HasSpectralTailProcess.candidateExtremalIndex_pos_of_antiClustering`: `AC(rₙ)` with
  `n P(|X_0| > aₙ) → 1`, `rₙ → ∞` gives `Θ_t → 0` and `ϑ > 0` (stationarity for `ϑ > 0` only).
* `HasShiftInvariantWindows.measureReal_exists_lt_eq_sum`: the first-exceedance decomposition
  `P(M_r > x) = ∑_{k < r} P(|X_0| > x, max_{0 < t ≤ k} |X_t| ≤ x)` (stationarity only).
* `HasSpectralTailProcess.tendsto_blockRatio`: `P(M_{rₙ} > uₙ) / (rₙ P(|X_0| > uₙ)) → ϑ` under
  stationarity, `uₙ → ∞`, `rₙ → ∞` and forward anticlustering at `uₙ` (no `rₙ / n → 0`, no mixing).
* `HasSpectralTailProcess.tendsto_partialMax_abs`: adding `n P(|X_0| > uₙ) → τ`, `rₙ / n → 0`
  and `A(uₙ)`: `P(M n ≤ uₙ) → exp (-ϑ τ)`.
* `HasSpectralTailProcess.hasExtremalIndex_abs`,
  `HasSpectralTailProcess.hasExtremalIndex_of_nonneg`: the extremal index exists and equals
  `ϑ` ([BS09, §4], [KS20, §7.5]).
* `HasSpectralTailProcess.tendsto_partialMax_abs_of_antiClustering`: the same in the normalization
  `uₙ = aₙ x`: `P(M n ≤ aₙ x) → exp (-ϑ x^(-α))`.
* `HasSpectralTailProcess.le_candidateExtremalIndex_of_tendsto_blockRatio`: without
  anticlustering, every limit of the cluster ratio is `≤ ϑ`.
* `HasSpectralTailProcess.le_candidateExtremalIndex`: `θ ≤ ϑ` without anticlustering, assuming
  `A(uₙ)` along one level sequence with `n P(|X_0| > uₙ) → τ > 0`, `rₙ → ∞`, `rₙ / n → 0`.

## Remarks on the literature

* Only the forward half of anticlustering, at a single level sequence, is used anywhere. For
  `Θ_t → 0` the passage from level `1` to all levels uses the independent Pareto radius of
  `Y = R Θ`, so anticlustering at other levels `aₙ x` is not needed.
* The hypotheses of [KS20, Lemma 7.5.4] (`θ ≤ ϑ`) could not be checked against the text. The
  version proved here assumes the block condition `A(uₙ)` along one level sequence and no
  anticlustering; it is an upper bound for every limit of the cluster ratio, the lower bound being
  where anticlustering enters.

## File layout

This file holds the final part of the development and imports the others:

* `ExtremeValueTheory.Dependence.Anticlustering.Basic`: the anticlustering conditions, conditional
  window probabilities, and `Θ_t → 0` under forward anticlustering.
* `ExtremeValueTheory.Dependence.Anticlustering.BlockRatio`: the first-exceedance decomposition and
  the limit `ϑ` of the block exceedance ratio.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### The extremal index equals `ϑ` -/

/-- If `bₙ → 0` and `kₙ bₙ → c` then `(1 - bₙ) ^ kₙ → exp (-c)`. -/
theorem tendsto_one_sub_pow_exp_of_tendsto_mul {k : ℕ → ℕ} {b : ℕ → ℝ} {c : ℝ}
    (hb : Tendsto b atTop (𝓝 0)) (hkb : Tendsto (fun n => (k n : ℝ) * b n) atTop (𝓝 c)) :
    Tendsto (fun n => (1 - b n) ^ k n) atTop (𝓝 (Real.exp (-c))) := by
  have hlow : Tendsto (fun n => -((k n : ℝ) * b n) / (1 - b n)) atTop (𝓝 (-c)) := by
    have := hkb.neg.div (hb.const_sub 1) (by norm_num)
    rw [sub_zero, div_one] at this
    exact this
  have hlog : Tendsto (fun n => (k n : ℝ) * Real.log (1 - b n)) atTop (𝓝 (-c)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hkb.neg ?_ ?_
    · filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
      have hpos : 0 < 1 - b n := by linarith
      have := Real.one_sub_inv_le_log_of_pos hpos
      calc -((k n : ℝ) * b n) / (1 - b n) = (k n : ℝ) * (1 - (1 - b n)⁻¹) := by
            field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    · filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
      have hpos : 0 < 1 - b n := by linarith
      have := Real.log_le_sub_one_of_pos hpos
      calc (k n : ℝ) * Real.log (1 - b n) ≤ (k n : ℝ) * (1 - b n - 1) :=
            mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
        _ = -((k n : ℝ) * b n) := by ring
  refine ((Real.continuous_exp.tendsto _).comp hlog).congr' ?_
  filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
  simp only [Function.comp_apply]
  rw [Real.exp_nat_mul, Real.exp_log (by linarith)]

/-- If `rₙ / n → 0` and `rₙ > 0` eventually, then `⌊n / rₙ⌋ rₙ / n → 1`. -/
theorem tendsto_div_mul_div_self {r : ℕ → ℕ} (hr0 : ∀ᶠ n in atTop, 0 < r n)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n / r n : ℕ) : ℝ) * r n / n) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hrn.const_sub 1)
    tendsto_const_nhds ?_ ?_
  · filter_upwards [hr0, eventually_gt_atTop 0] with n hr hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h : n < n / r n * r n + r n := Nat.lt_div_mul_add hr
    have h' : (n : ℝ) < ((n / r n : ℕ) : ℝ) * r n + r n := by exact_mod_cast h
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn']
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_one hn']
    exact_mod_cast Nat.div_mul_le_self n (r n)

section ExtremalIndex

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- **Block condition** `A(uₙ)` (of Leadbetter / Davis–Hsing type, [BS09, §4], [KS20, §7.5]):
the maximum over `n` observations behaves like the maximum over `⌊n / rₙ⌋` independent blocks of
length `rₙ`: `P(M n ≤ uₙ) - P(M rₙ ≤ uₙ) ^ ⌊n / rₙ⌋ → 0`. It follows from strong mixing
conditions with suitable rates; here it is a hypothesis. -/
def ConditionA (X : ℕ → Ω → ℝ) (P : Measure Ω) (u : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  Tendsto (fun n => P.real {ω | partialMax X n ω ≤ u n} -
    P.real {ω | partialMax X (r n) ω ≤ u n} ^ (n / r n)) atTop (𝓝 0)

omit [IsProbabilityMeasure Q] in
/-- Regular variation makes `P(|X_0| > C)` positive for every level `C`. -/
theorem HasSpectralTailProcess.measureReal_lt_abs_pos (h : HasSpectralTailProcess P X α Q Θ)
    (C : ℝ) : 0 < P.real {ω | C < |X 0 ω|} := by
  obtain ⟨x, hxC, hx⟩ := ((eventually_ge_atTop C).and h.1.eventually_pos).exists
  exact hx.trans_le (measureReal_mono fun ω (hω : x < |X 0 ω|) => hxC.trans_lt hω)

/-- **Maxima under anticlustering** ([BS09, Proposition 4.2 and §4], [KS20, §7.5]): let
`(X_t)` be stationary with spectral tail process `Θ`, `n P(|X_0| > uₙ) → τ`, `rₙ → ∞`,
`rₙ / n → 0`, and assume the forward anticlustering bound and the block condition `A(uₙ)` for
`|X|`. Then `P(max_{0 ≤ t < n} |X_t| ≤ uₙ) → exp (-ϑ τ)`.

Hypotheses actually used: stationarity, the spectral tail process, `n P(|X_0| > uₙ) → τ`
(which forces `uₙ → ∞`), `rₙ → ∞`, `rₙ / n → 0`, forward anticlustering at the level sequence
`uₙ`, and `A(uₙ)`. -/
theorem HasSpectralTailProcess.tendsto_partialMax_abs (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (hstat : HasShiftInvariantWindows P X)
    (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hAC : ForwardAntiClusteringAt P X u r) (hA : ConditionA (fun k : ℕ => |X k|) P u r) :
    Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ u n}) atTop
      (𝓝 (Real.exp (-((candidateExtremalIndex Q Θ α).toReal * τ)))) := by
  set ϑ := (candidateExtremalIndex Q Θ α).toReal
  have hu := h.tendsto_atTop_of_tendsto_mul hτ
  have hratio := h.tendsto_blockRatio hα hX hΘm hstat hu hr hAC
  set p : ℕ → ℝ := fun n => P.real {ω | u n < |X 0 ω|}
  set b : ℕ → ℝ := fun n => P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|}
  have hp0 : ∀ n, 0 < p n := fun n => h.measureReal_lt_abs_pos _
  have hr0 : ∀ᶠ n in atTop, 0 < r n := hr.eventually_gt_atTop 0
  -- the block maximum
  have hpart : ∀ n, 0 < r n →
      P.real {ω | partialMax (fun k : ℕ => |X k|) (r n) ω ≤ u n} = 1 - b n := by
    intro n hn
    have hmeas : MeasurableSet {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} := by
      simp only [ofPred_exists, ofPred_and]
      exact MeasurableSet.iUnion fun t => (MeasurableSet.const _).inter
        (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX t)))
    rw [← probReal_compl_eq_one_sub hmeas]
    congr 1
    ext ω
    rw [mem_ofPred_eq, partialMax_le_iff hn, mem_compl_iff, mem_ofPred_eq]
    constructor
    · rintro hle ⟨t, ht, hlt⟩
      rw [Finset.mem_Ico] at ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
      exact absurd (hle k (by exact_mod_cast ht.2)) (not_le.2 hlt)
    · intro hne k hk
      by_contra hcon
      exact hne ⟨k, Finset.mem_Ico.2 ⟨by positivity, by exact_mod_cast hk⟩, not_le.1 hcon⟩
  -- `kₙ bₙ → ϑ τ` and `bₙ → 0`
  have hkr := tendsto_div_mul_div_self hr0 hrn
  have hrp : Tendsto (fun n => (r n : ℝ) / n * (n * p n)) atTop (𝓝 0) := by
    simpa using hrn.mul hτ
  have hb : Tendsto b atTop (𝓝 0) := by
    have := hratio.mul hrp
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [hr0, eventually_gt_atTop 0] with n hrpos hn
    have : (r n : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : P.real {ω | u n < |X 0 ω|} ≠ 0 := (hp0 n).ne'
    dsimp only [b, p]
    field_simp
  have hkb : Tendsto (fun n => ((n / r n : ℕ) : ℝ) * b n) atTop (𝓝 (ϑ * τ)) := by
    have := (hkr.mul hτ).mul hratio
    rw [one_mul, mul_comm τ] at this
    refine this.congr' ?_
    filter_upwards [hr0, eventually_gt_atTop 0] with n hrpos hn
    have : (r n : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : P.real {ω | u n < |X 0 ω|} ≠ 0 := (hp0 n).ne'
    dsimp only [b, p]
    field_simp
  have hpow := tendsto_one_sub_pow_exp_of_tendsto_mul hb hkb
  have := hA.add hpow
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [hr0] with n hn
  rw [hpart n hn]
  ring

/-- **The extremal index equals the candidate extremal index under anticlustering**
([BS09, Proposition 4.2 and §4], [KS20, §7.5]): if `(X_t)` is stationary with spectral tail
process `Θ`, `rₙ → ∞`, `rₙ / n → 0`, and for every level sequence with `n P(|X_0| > uₙ) → τ > 0`
the forward anticlustering bound and the block condition `A(uₙ)` hold, then `(|X_n|)_{n ∈ ℕ}`
has extremal index `ϑ`. -/
theorem HasSpectralTailProcess.hasExtremalIndex_abs (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (hstat : HasShiftInvariantWindows P X)
    (h : HasSpectralTailProcess P X α Q Θ) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hcond : ∀ τ > 0, ∀ u : ℕ → ℝ,
      Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ) →
        ForwardAntiClusteringAt P X u r ∧ ConditionA (fun k : ℕ => |X k|) P u r) :
    HasExtremalIndex (fun k : ℕ => |X k|) P (candidateExtremalIndex Q Θ α).toReal := by
  have h0 := h.ae_abs_eq_one hΘm (hX 0)
  refine ⟨⟨ENNReal.toReal_nonneg, ?_⟩, fun τ hτ u hu => ?_⟩
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top (candidateExtremalIndex_le_one hα.le h0)
  · have hu' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ) := by
      simpa using hu
    obtain ⟨hAC, hA⟩ := hcond τ hτ u hu'
    exact h.tendsto_partialMax_abs hα hX hΘm hstat hu' hr hrn hAC hA

/-- **Nonnegative series** ([BS09, §4], [KS20, §7.5]): the version of
`HasSpectralTailProcess.hasExtremalIndex_abs` for `X ≥ 0`, where `|X| = X`, directly in terms of
the block extremal index `HasExtremalIndex` of `(X_n)_{n ∈ ℕ}`. -/
theorem HasSpectralTailProcess.hasExtremalIndex_of_nonneg (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    (hnn : ∀ t ω, 0 ≤ X t ω) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hcond : ∀ τ > 0, ∀ u : ℕ → ℝ,
      Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ) →
        ForwardAntiClusteringAt P X u r ∧ ConditionA (fun k : ℕ => X k) P u r) :
    HasExtremalIndex (fun k : ℕ => X k) P (candidateExtremalIndex Q Θ α).toReal := by
  have habs : (fun k : ℕ => |X k|) = fun k : ℕ => X k :=
    funext fun k => abs_of_nonneg (show 0 ≤ X k from fun ω => hnn _ ω)
  have := h.hasExtremalIndex_abs hα hX hΘm hstat hr hrn fun τ hτ u hu => by
    have hu' : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ) := by
      simpa [abs_of_nonneg (hnn _ _)] using hu
    obtain ⟨h1, h2⟩ := hcond τ hτ u hu'
    exact ⟨h1, by rwa [ConditionA, habs]⟩
  rwa [habs] at this

/-- **The extremal index in the normalization of `AC(rₙ)`** ([BS09, §4], [KS20, §7.5]): if
`n P(|X_0| > aₙ) → 1`, `rₙ → ∞`, `rₙ / n → 0`, `AC(rₙ)` holds and the block condition
`A(aₙ x)` holds for every `x > 0`, then `P(max_{0 ≤ t < n} |X_t| ≤ aₙ x) → exp (-ϑ x^(-α))` for
every `x > 0`. Only the forward half of `AC(rₙ)` at the level `x` is used for the limit at `x`. -/
theorem HasSpectralTailProcess.tendsto_partialMax_abs_of_antiClustering (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {a : ℕ → ℝ} (ha : Tendsto (fun n : ℕ => n * P.real {ω | a n < |X 0 ω|}) atTop (𝓝 1))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hAC : AntiClustering P X a r)
    (hA : ∀ x : ℝ, 0 < x → ConditionA (fun k : ℕ => |X k|) P (fun n => a n * x) r)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ a n * x}) atTop
      (𝓝 (Real.exp (-((candidateExtremalIndex Q Θ α).toReal * x ^ (-α))))) := by
  have hainf := h.tendsto_atTop_of_tendsto_mul ha
  have hRV := (h.1.2 x hx).comp hainf
  have hτ : Tendsto (fun n : ℕ => n * P.real {ω | a n * x < |X 0 ω|}) atTop (𝓝 (x ^ (-α))) := by
    have := ha.mul hRV
    rw [one_mul] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, mul_comm x (a n)]
    have := h.measureReal_lt_abs_pos (a n)
    field_simp
  exact h.tendsto_partialMax_abs hα hX hΘm hstat hτ hr hrn (hAC x hx).forward (hA x hx)

end ExtremalIndex

/-! ### The cluster ratio -/

section ClusterRatio

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The *cluster ratio* `P(max_{0 ≤ t < rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ))`. -/
noncomputable def clusterRatio (P : Measure Ω) (X : ℤ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) :
    ℝ :=
  P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} / (r n * P.real {ω | u n < |X 0 ω|})

end ClusterRatio

/-! ### `θ ≤ ϑ` without anticlustering -/

section Inequality

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- **Upper bound for the cluster ratio without anticlustering**: for a stationary series with
spectral tail process `Θ`, `uₙ → ∞` and `rₙ → ∞`, every limit `L` of
`P(max_{0 ≤ t < rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ))` satisfies `L ≤ ϑ`.

The proof is the upper half of the squeeze in `tendsto_blockRatio`: the conditional
probabilities `q_k = P(max_{0 < t ≤ k} |X_t| ≤ uₙ | |X_0| > uₙ)` decrease in `k`, so the average
of `q_0, …, q_{rₙ - 1}` is at most `m / rₙ + q_m`, whose limit is `ϑ_m ↓ ϑ`. Anticlustering is
only needed for the matching lower bound. -/
theorem HasSpectralTailProcess.le_candidateExtremalIndex_of_tendsto_blockRatio (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {L : ℝ}
    (hL : Tendsto (fun n => P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} /
        (r n * P.real {ω | u n < |X 0 ω|})) atTop (𝓝 L)) :
    L ≤ (candidateExtremalIndex Q Θ α).toReal := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q
  have hs : ∀ x : ℝ, MeasurableSet {ω | x < |X 0 ω|} := fun x =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX 0))
  set S : ℕ → Set Ω := fun n => {ω | u n < |X 0 ω|}
  set D : ℕ → ℕ → Set Ω := fun n k =>
    {ω | u n < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) k, |X t ω| ≤ u n}
  set q : ℕ → ℕ → ℝ := fun n k => P.real (D n k) / P.real (S n)
  set θk : ℕ → ℝ := fun k => π.real {p | ∀ t ∈ Finset.Ioc (0 : ℤ) k, |p.1 * Θ t p.2| ≤ 1}
  have hq1 : ∀ n k, q n k ≤ 1 := fun n k =>
    div_le_one_of_le₀ (measureReal_mono fun ω hω => hω.1) measureReal_nonneg
  have hqanti : ∀ n m k, m ≤ k → q n k ≤ q n m := fun n m k hmk =>
    div_le_div_of_nonneg_right (measureReal_mono fun ω hω =>
      ⟨hω.1, fun t ht => hω.2 t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast hmk) ht)⟩)
      measureReal_nonneg
  have hratio : ∀ n, P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} /
      (r n * P.real {ω | u n < |X 0 ω|}) = (∑ k ∈ Finset.range (r n), q n k) / r n := by
    intro n
    rw [hstat.measureReal_exists_lt_eq_sum hX, div_mul_eq_div_div_swap, Finset.sum_div]
  have hqlim : ∀ k, Tendsto (fun n => q n k) atTop (𝓝 (θk k)) := by
    intro k
    have key := (h.tendsto_cond_forall_le hα hX hΘm (Finset.Ioc (0 : ℤ) k)).comp hu
    have key' := (ENNReal.tendsto_toReal (measure_ne_top π _)).comp key
    refine key'.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [cond_toReal_eq (hs _)]
    rfl
  have hθlim := tendsto_measureReal_forall_le_candidateExtremalIndex hα hΘm
    (h.ae_abs_eq_one hΘm (hX 0))
  have hm : ∀ m : ℕ, L ≤ θk m := by
    intro m
    have hmr : Tendsto (fun n => (m : ℝ) / r n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr)
    have := hmr.add (hqlim m)
    rw [zero_add] at this
    refine le_of_tendsto_of_tendsto hL this ?_
    filter_upwards [hr.eventually_ge_atTop (m + 1)] with n hn
    have hr0 : (0 : ℝ) < r n := by exact_mod_cast (show 0 < r n by omega)
    rw [hratio, div_le_iff₀ hr0]
    rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ r n by omega)]
    have h1 : ∑ k ∈ Finset.range m, q n k ≤ m := by
      calc _ ≤ ∑ _k ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun k _ => hq1 n k
        _ = m := by simp
    have h2 : ∑ k ∈ Finset.Ico m (r n), q n k ≤ r n * q n m := by
      calc _ ≤ ∑ _k ∈ Finset.Ico m (r n), q n m := Finset.sum_le_sum fun k hk =>
            hqanti n m k (Finset.mem_Ico.1 hk).1
        _ = (r n - m : ℕ) * q n m := by simp
        _ ≤ r n * q n m := by
            gcongr
            exact_mod_cast Nat.sub_le _ _
    calc _ ≤ (m : ℝ) + r n * q n m := add_le_add h1 h2
      _ = (m / r n + q n m) * r n := by field_simp
  exact ge_of_tendsto hθlim (Eventually.of_forall hm)

/-- **Under `A(uₙ)`, the maximum and the cluster ratio determine each other.** For a stationary
series with `P(|X_0| > x) > 0` for all `x`, `n P(|X_0| > uₙ) → τ > 0`, `rₙ → ∞`, `rₙ / n → 0` and
the block condition `A(uₙ)`: `P(M n ≤ uₙ) → exp (-θ τ)` iff the cluster ratio tends to `θ`.
(No tail process is used.) -/
theorem HasShiftInvariantWindows.tendsto_partialMax_iff_tendsto_clusterRatio
    {u : ℕ → ℝ} {r : ℕ → ℕ} (hX : ∀ t, Measurable (X t)) (hstat : HasShiftInvariantWindows P X)
    (hp0 : ∀ n, 0 < P.real {ω | u n < |X 0 ω|}) {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) (hτ0 : 0 < τ)
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) (θ : ℝ) :
    Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ u n}) atTop
        (𝓝 (Real.exp (-(θ * τ)))) ↔ Tendsto (clusterRatio P X u r) atTop (𝓝 θ) := by
  set p : ℕ → ℝ := fun n => P.real {ω | u n < |X 0 ω|}
  set b : ℕ → ℝ := fun n => P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|}
  set k : ℕ → ℕ := fun n => n / r n
  have hr0 : ∀ᶠ n in atTop, 0 < r n := hr.eventually_gt_atTop 0
  have hbr : ∀ n, b n ≤ r n * p n := by
    intro n
    simp only [b, hstat.measureReal_exists_lt_eq_sum hX]
    calc _ ≤ ∑ _k ∈ Finset.range (r n), p n :=
          Finset.sum_le_sum fun k _ => measureReal_mono fun ω hω => hω.1
      _ = r n * p n := by simp
  have hrp : Tendsto (fun n => (r n : ℝ) * p n) atTop (𝓝 0) := by
    have := hrn.mul hτ
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp only [p]
    field_simp
  have hb : Tendsto b atTop (𝓝 0) :=
    squeeze_zero (fun n => measureReal_nonneg) hbr hrp
  have hpart : ∀ n, 0 < r n →
      P.real {ω | partialMax (fun k : ℕ => |X k|) (r n) ω ≤ u n} = 1 - b n := by
    intro n hn
    have hmeas : MeasurableSet {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} := by
      simp only [ofPred_exists, ofPred_and]
      exact MeasurableSet.iUnion fun t => (MeasurableSet.const _).inter
        (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX t)))
    rw [← probReal_compl_eq_one_sub hmeas]
    congr 1
    ext ω
    rw [mem_ofPred_eq, partialMax_le_iff hn, mem_compl_iff, mem_ofPred_eq]
    constructor
    · rintro hle ⟨t, ht, hlt⟩
      rw [Finset.mem_Ico] at ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
      exact absurd (hle k (by exact_mod_cast ht.2)) (not_le.2 hlt)
    · intro hne k hk
      by_contra hcon
      exact hne ⟨k, Finset.mem_Ico.2 ⟨by positivity, by exact_mod_cast hk⟩, not_le.1 hcon⟩
  have hkr := tendsto_div_mul_div_self hr0 hrn
  -- `kₙ bₙ = (kₙ rₙ / n) (n pₙ) clusterRatio`
  have hfac : ∀ᶠ n in atTop, (k n : ℝ) * b n =
      ((n / r n : ℕ) : ℝ) * r n / n * (n * p n) * clusterRatio P X u r n := by
    filter_upwards [hr0, eventually_gt_atTop 0] with n hrpos hn
    have : (r n : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : P.real {ω | u n < |X 0 ω|} ≠ 0 := (hp0 n).ne'
    rw [clusterRatio]
    dsimp only [b, p, k]
    field_simp
  constructor
  · intro hθ
    have hpow : Tendsto (fun n => (1 - b n) ^ k n) atTop (𝓝 (Real.exp (-(θ * τ)))) := by
      have := hθ.sub hA
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [hr0] with n hn
      rw [hpart n hn]
      ring
    have hlog : Tendsto (fun n => (k n : ℝ) * Real.log (1 - b n)) atTop (𝓝 (-(θ * τ))) := by
      have := ((Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hpow)
      rw [Real.log_exp] at this
      refine this.congr' ?_
      filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
      simp only [Function.comp_apply, Real.log_pow]
    have hkb : Tendsto (fun n => (k n : ℝ) * b n) atTop (𝓝 (θ * τ)) := by
      have hlow : Tendsto (fun n => -((1 - b n) * ((k n : ℝ) * Real.log (1 - b n)))) atTop
          (𝓝 (θ * τ)) := by
        have := ((hb.const_sub 1).mul hlog).neg
        rwa [sub_zero, one_mul, neg_neg] at this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow (by simpa using hlog.neg) ?_ ?_
      · filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
        have hpos : 0 < 1 - b n := by linarith
        have h1 := Real.one_sub_inv_le_log_of_pos hpos
        have h2 : -b n ≤ (1 - b n) * Real.log (1 - b n) := by
          have := mul_le_mul_of_nonneg_left h1 hpos.le
          rwa [mul_sub, mul_one, mul_inv_cancel₀ hpos.ne', sub_sub_cancel_left] at this
        have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (k n))
        linarith
      · filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
        have hpos : 0 < 1 - b n := by linarith
        have h1 := Real.log_le_sub_one_of_pos hpos
        have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (k n))
        linarith
    have hden := hkr.mul hτ
    rw [one_mul] at hden
    have := hkb.div hden hτ0.ne'
    rw [mul_div_cancel_right₀ _ hτ0.ne'] at this
    refine this.congr' ?_
    filter_upwards [hfac, hden.eventually_ne hτ0.ne'] with n hn hne
    simp only [Pi.div_apply]
    rw [hn, mul_div_cancel_left₀ _ hne]
  · intro hθ
    have hkb : Tendsto (fun n => (k n : ℝ) * b n) atTop (𝓝 (θ * τ)) := by
      have := (hkr.mul hτ).mul hθ
      rw [one_mul, mul_comm τ] at this
      exact this.congr' (hfac.mono fun n hn => hn.symm)
    have hpow := tendsto_one_sub_pow_exp_of_tendsto_mul hb hkb
    have := hA.add hpow
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hr0] with n hn
    rw [hpart n hn]
    ring

/-- **The extremal index is at most the candidate extremal index** (`θ ≤ ϑ`, cf. [KS20, §7.5]).
Let `(X_t)` be stationary with spectral tail process `Θ`, `n P(|X_0| > uₙ) → τ > 0`, `rₙ → ∞`,
`rₙ / n → 0`, and assume the block condition `A(uₙ)` for `|X|`. If
`P(max_{0 ≤ t < n} |X_t| ≤ uₙ) → exp (-θ τ)`, then `θ ≤ ϑ`.

Hypotheses actually used: stationarity, the spectral tail process, `A(uₙ)` along a *single*
level sequence with `τ > 0`, `rₙ → ∞`, `rₙ / n → 0`. No anticlustering. (The hypotheses of
[KS20, Lemma 7.5.4] could not be checked against the text; this is the version proved here.) -/
theorem HasSpectralTailProcess.le_candidateExtremalIndex_of_tendsto (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {u : ℕ → ℝ} {τ : ℝ} (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ))
    (hτ0 : 0 < τ) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) {θ : ℝ}
    (hθ : Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ u n}) atTop
      (𝓝 (Real.exp (-(θ * τ))))) :
    θ ≤ (candidateExtremalIndex Q Θ α).toReal :=
  h.le_candidateExtremalIndex_of_tendsto_blockRatio hα hX hΘm hstat
    (h.tendsto_atTop_of_tendsto_mul hτ) hr
    ((hstat.tendsto_partialMax_iff_tendsto_clusterRatio hX (fun _ => h.measureReal_lt_abs_pos _)
      hτ hτ0 hr hrn hA θ).1 hθ)

/-- **`θ ≤ ϑ` for the block extremal index**: if `(|X_n|)` has extremal index `θ` and the block
condition `A(uₙ)` holds along one level sequence with `n P(|X_0| > uₙ) → τ > 0` (and `rₙ → ∞`,
`rₙ / n → 0`), then `θ ≤ ϑ`. No anticlustering is assumed. -/
theorem HasSpectralTailProcess.le_candidateExtremalIndex (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {θ : ℝ}
    (hθ : HasExtremalIndex (fun k : ℕ => |X k|) P θ)
    {u : ℕ → ℝ} {τ : ℝ} (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ))
    (hτ0 : 0 < τ) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) :
    θ ≤ (candidateExtremalIndex Q Θ α).toReal :=
  h.le_candidateExtremalIndex_of_tendsto hα hX hΘm hstat hτ hτ0 hr hrn hA
    (hθ.2 τ hτ0 u (by simpa using hτ))

end Inequality

end ExtremeValueTheory
