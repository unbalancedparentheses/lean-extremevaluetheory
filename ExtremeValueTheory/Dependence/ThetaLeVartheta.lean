/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Anticlustering
import ExtremeValueTheory.CDFBridge

/-!
# `θ ≤ ϑ` without mixing or anticlustering

For a stationary regularly varying series `(X_t)_{t ∈ ℤ}` with spectral tail process `Θ`, the
block extremal index `θ` of `(|X_n|)_{n ∈ ℕ}` (when it exists) is at most the candidate extremal
index `ϑ = P(sup_{k ≥ 1} |Y_k| ≤ 1)`, `Y = R Θ` ([KS20, Lemma 7.5.4]). Unlike
`HasSpectralTailProcess.le_candidateExtremalIndex` (in `Dependence/Anticlustering.lean`), no block
condition `A(uₙ)`, no block lengths `rₙ` and no anticlustering are assumed.

## Argument

1. *First-exceedance bound* (stationarity only). By the exact decomposition
   `P(M_n > u) = ∑_{k < n} P(|X_0| > u, max_{0 < t ≤ k} |X_t| ≤ u)`
   (`HasShiftInvariantWindows.measureReal_exists_lt_eq_sum`), whose terms decrease in `k` and are
   at most `P(|X_0| > u)`, for every `m ≤ n`:
   `P(M_n > u) ≤ m P(|X_0| > u) + n P(|X_0| > u, max_{0 < t ≤ m} |X_t| ≤ u)`.
2. Along levels with `n P(|X_0| > uₙ) → τ` and `P(M_n ≤ uₙ) → c`, letting `n → ∞` gives
   `1 - c ≤ τ ϑ_m`, `ϑ_m = P(max_{0 < t ≤ m} |Y_t| ≤ 1)`, and `m → ∞` gives `1 - c ≤ τ ϑ`.
3. With `c = exp (-θ τ)` and `1 - exp (-x) ≥ x / (1 + x)`: `θ ≤ ϑ + τ` for every `τ > 0` for
   which levels exist. Regular variation of `P(|X_0| > x)` provides levels for every `τ > 0`
   (`hasExceedanceLevels_of_isRegularlyVarying`), so `θ ≤ ϑ`.

## Main results

* `hasExceedanceLevels_of_isRegularlyVarying`: if `x ↦ P(X_0 > x)` is regularly varying (of any
  index), then for every `τ > 0` there are levels `uₙ` with `n P(X_0 > uₙ) → τ`
  (cf. [LLR, Theorem 1.7.13]: regular variation forces `P(X_0 ≥ x) / P(X_0 > x) → 1`).
* `HasSpectralTailProcess.hasExceedanceLevels_abs`: hence `(|X_n|)` admits exceedance levels.
* `HasSpectralTailProcess.one_sub_le_mul_candidateExtremalIndex`: `1 - c ≤ τ ϑ` (step 2).
* `HasSpectralTailProcess.le_candidateExtremalIndex'`: `θ ≤ ϑ`, assuming only `α > 0`,
  measurability of `X` and `Θ`, stationarity (`HasShiftInvariantWindows`), the spectral tail
  process and `HasExtremalIndex (|X|) P θ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Exceedance levels for regularly varying tails -/

section Levels

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Exceedance levels for regularly varying tails** (cf. [LLR, Theorem 1.7.13]): if the tail
`x ↦ P(X_0 > x)` is regularly varying with some index `ρ`, then for every `τ > 0` there is a level
sequence with `n P(X_0 > uₙ) → τ`. The levels are `uₙ = inf {x ≥ 0 | P(X_0 > x) ≤ τ / n}`: by
right continuity `n P(X_0 > uₙ) ≤ τ`, while for `λ > 1`,
`n P(X_0 > uₙ) ≥ τ P(X_0 > uₙ) / P(X_0 > uₙ / λ) → τ λ^ρ`. -/
theorem hasExceedanceLevels_of_isRegularlyVarying {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
    {ρ : ℝ} (hRV : IsRegularlyVarying (fun x => P.real {ω | x < X 0 ω}) ρ) :
    HasExceedanceLevels X P := by
  set g : ℝ → ℝ := fun x => P.real {ω | x < X 0 ω} with hg
  set μ := P.map (X 0)
  have hgcdf : ∀ x, g x = 1 - cdf μ x := fun x ↦ (one_sub_cdf_map_apply hX0.aemeasurable x).symm
  have hanti : Antitone g := fun x y hxy =>
    measureReal_mono fun ω (hω : y < X 0 ω) => lt_of_le_of_lt hxy hω
  have htop : Tendsto g atTop (𝓝 0) := by
    have := (tendsto_cdf_atTop μ).const_sub 1
    rw [sub_self] at this
    exact this.congr fun x => (hgcdf x).symm
  have hright : ∀ x, ContinuousWithinAt g (Ioi x) x := by
    intro x
    have := (continuousWithinAt_const (b := (1 : ℝ))).sub
      (((cdf μ).right_continuous x).mono Ioi_subset_Ici_self)
    exact this.congr (fun y _ => hgcdf y) (hgcdf x)
  have hpos : ∀ x, 0 < g x := by
    intro x
    obtain ⟨y, hxy, hy⟩ := ((eventually_ge_atTop x).and hRV.1).exists
    exact hy.trans_le (hanti hxy)
  intro τ hτ
  set S : ℕ → Set ℝ := fun n => {x | 0 ≤ x ∧ g x ≤ τ / n}
  set u : ℕ → ℝ := fun n => sInf (S n)
  refine ⟨u, ?_⟩
  have hSne : ∀ n : ℕ, 0 < n → (S n).Nonempty := by
    intro n hn
    have : 0 < τ / n := div_pos hτ (by exact_mod_cast hn)
    obtain ⟨x, hx0, hx⟩ :=
      ((eventually_ge_atTop 0).and (htop.eventually (ge_mem_nhds this))).exists
    exact ⟨x, hx0, hx⟩
  have hSbdd : ∀ n, BddBelow (S n) := fun n => ⟨0, fun x hx => hx.1⟩
  have hle : ∀ n : ℕ, 0 < n → g (u n) ≤ τ / n := by
    intro n hn
    refine le_of_tendsto (hright (u n)) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt (hSne n hn) hy
    exact (hanti hsy.le).trans hs.2
  have hgt : ∀ n : ℕ, ∀ y, 0 ≤ y → y < u n → τ / n < g y := by
    intro n y hy0 hyu
    by_contra hcon
    exact (csInf_le (hSbdd n) ⟨hy0, not_lt.1 hcon⟩).not_gt hyu
  have hu : Tendsto u atTop atTop := by
    rw [tendsto_atTop]
    intro C
    have hτn : Tendsto (fun n : ℕ => τ / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [hτn.eventually (gt_mem_nhds (hpos C)), eventually_gt_atTop 0] with n hn hn0
    by_contra hcon
    exact (hle n hn0).not_gt (hn.trans_le (hanti (not_le.1 hcon).le))
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hc : ContinuousAt (fun l : ℝ => τ * l ^ ρ) 1 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero))
    have h1 : a < τ * (1 : ℝ) ^ ρ := by rwa [Real.one_rpow, mul_one]
    obtain ⟨l, hl, hl1⟩ := (((hc.eventually (lt_mem_nhds h1)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (1 : ℝ) ∈ 𝓝[>] 1)).exists
    have hl1 : 1 < l := hl1
    have hl0 : 0 < l := one_pos.trans hl1
    have hv : Tendsto (fun n => u n / l) atTop atTop := hu.atTop_div_const hl0
    have hr := ((hRV.2 l hl0).comp hv).const_mul τ
    filter_upwards [hr.eventually (lt_mem_nhds hl), eventually_gt_atTop 0,
      hu.eventually_gt_atTop 0] with n hn hn0 hun
    show a < (n : ℝ) * g (u n)
    have hlu : l * (u n / l) = u n := by field_simp
    simp only [Function.comp_apply] at hn
    change a < τ * (g (l * (u n / l)) / g (u n / l)) at hn
    rw [hlu] at hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hq := (div_lt_iff₀ hnpos).1
      (hgt n (u n / l) (div_nonneg hun.le hl0.le) (div_lt_self hun hl1))
    have hgl := hpos (u n / l)
    have hgu := hpos (u n)
    calc a < τ * (g (u n) / g (u n / l)) := hn
      _ ≤ n * g (u n) := by
        rw [mul_div_assoc', div_le_iff₀ hgl]
        nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn0
    show (n : ℝ) * g (u n) < a
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    exact ((le_div_iff₀' hnpos).1 (hle n hn0)).trans_lt ha

end Levels

/-! ### `θ ≤ ϑ` -/

section Inequality

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

omit [IsProbabilityMeasure Q] in
/-- A series with a spectral tail process admits exceedance levels for `|X|`: the tail
`P(|X_0| > x)` is regularly varying. -/
theorem HasSpectralTailProcess.hasExceedanceLevels_abs (h : HasSpectralTailProcess P X α Q Θ)
    (hX : ∀ t, Measurable (X t)) : HasExceedanceLevels (fun k : ℕ => |X k|) P :=
  hasExceedanceLevels_of_isRegularlyVarying (X := fun k : ℕ => |X k|)
    (continuous_abs.measurable.comp (hX _)) h.1

/-- **The first-exceedance bound in the limit**: for a stationary series with spectral tail
process `Θ`, if `n P(|X_0| > uₙ) → τ` and `P(max_{0 ≤ t < n} |X_t| ≤ uₙ) → c`, then
`1 - c ≤ τ ϑ`. Uses only stationarity (through the first-exceedance decomposition) and the
spectral tail process: no mixing, no anticlustering, no block lengths. -/
theorem HasSpectralTailProcess.one_sub_le_mul_candidateExtremalIndex (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {u : ℕ → ℝ} {τ : ℝ} (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ))
    {c : ℝ}
    (hc : Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ u n}) atTop
      (𝓝 c)) :
    1 - c ≤ τ * (candidateExtremalIndex Q Θ α).toReal := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q
  have hu := h.tendsto_atTop_of_tendsto_mul hτ
  have hs : ∀ x : ℝ, MeasurableSet {ω | x < |X 0 ω|} := fun x =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX 0))
  set p : ℕ → ℝ := fun n => P.real {ω | u n < |X 0 ω|}
  set D : ℕ → ℕ → Set Ω := fun n k =>
    {ω | u n < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) k, |X t ω| ≤ u n}
  set b : ℕ → ℝ := fun n => P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) n, u n < |X t ω|}
  set θk : ℕ → ℝ := fun k => π.real {p | ∀ t ∈ Finset.Ioc (0 : ℤ) k, |p.1 * Θ t p.2| ≤ 1}
  have hp0 : ∀ n, 0 < p n := fun n => h.measureReal_lt_abs_pos _
  have hp : Tendsto p atTop (𝓝 0) := tendsto_zero_of_tendsto_natCast_mul' hτ
  -- the block maximum
  have hpart : ∀ n, 0 < n →
      P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ u n} = 1 - b n := by
    intro n hn
    have hmeas : MeasurableSet {ω | ∃ t ∈ Finset.Ico (0 : ℤ) n, u n < |X t ω|} := by
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
  have hb : Tendsto b atTop (𝓝 (1 - c)) := by
    have := hc.const_sub 1
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hpart n hn]
    ring
  -- step 1: the first-exceedance bound
  have hbound : ∀ m n, m ≤ n → b n ≤ m * p n + n * P.real (D n m) := by
    intro m n hmn
    simp only [b, hstat.measureReal_exists_lt_eq_sum hX]
    rw [← Finset.sum_range_add_sum_Ico _ hmn]
    have h1 : ∑ k ∈ Finset.range m, P.real (D n k) ≤ m * p n := by
      calc _ ≤ ∑ _k ∈ Finset.range m, p n :=
            Finset.sum_le_sum fun k _ => measureReal_mono fun ω hω => hω.1
        _ = m * p n := by simp
    have h2 : ∑ k ∈ Finset.Ico m n, P.real (D n k) ≤ n * P.real (D n m) := by
      calc _ ≤ ∑ _k ∈ Finset.Ico m n, P.real (D n m) := Finset.sum_le_sum fun k hk =>
            measureReal_mono fun ω hω => ⟨hω.1, fun t ht =>
              hω.2 t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast (Finset.mem_Ico.1 hk).1) ht)⟩
        _ = (n - m : ℕ) * P.real (D n m) := by simp
        _ ≤ n * P.real (D n m) := by
            gcongr
            exact_mod_cast Nat.sub_le _ _
    exact add_le_add h1 h2
  -- step 2: the conditional probabilities converge to the tail process
  have hqlim : ∀ k, Tendsto (fun n => P.real (D n k) / p n) atTop (𝓝 (θk k)) := by
    intro k
    have key := (h.tendsto_cond_forall_le hα hX hΘm (Finset.Ioc (0 : ℤ) k)).comp hu
    have key' := (ENNReal.tendsto_toReal (measure_ne_top π _)).comp key
    refine key'.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [cond_toReal_eq (hs _)]
    rfl
  have hm : ∀ m : ℕ, 1 - c ≤ τ * θk m := by
    intro m
    have hlim : Tendsto (fun n => m * p n + (n * p n) * (P.real (D n m) / p n)) atTop
        (𝓝 (m * 0 + τ * θk m)) :=
      (hp.const_mul _).add (hτ.mul (hqlim m))
    rw [mul_zero, zero_add] at hlim
    refine le_of_tendsto_of_tendsto hb hlim ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    refine (hbound m n hn).trans (le_of_eq ?_)
    have := (hp0 n).ne'
    field_simp
  -- step 3: `m → ∞`
  have hθlim := tendsto_measureReal_forall_le_candidateExtremalIndex hα hΘm
    (h.ae_abs_eq_one hΘm (hX 0))
  exact ge_of_tendsto' (hθlim.const_mul τ) hm

/-- **`θ ≤ ϑ` without mixing or anticlustering** ([KS20, Lemma 7.5.4]): if `(X_t)_{t ∈ ℤ}` is
stationary with spectral tail process `Θ` of index `α > 0` and `(|X_n|)_{n ∈ ℕ}` has extremal index
`θ`, then `θ ≤ ϑ = P(sup_{k ≥ 1} |Y_k| ≤ 1)`.

Hypotheses actually used: `α > 0`, measurability of `X_t` and `Θ_t`, stationarity
(`HasShiftInvariantWindows`, only through the first-exceedance decomposition), the spectral tail
process (regular variation of `P(|X_0| > x)` supplies levels with `n P(|X_0| > uₙ) → τ` for
every `τ > 0`), and `HasExtremalIndex (|X|) P θ`. No block condition `A(uₙ)`, no block lengths
`rₙ`, no anticlustering, no mixing. -/
theorem HasSpectralTailProcess.le_candidateExtremalIndex' (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {θ : ℝ}
    (hθ : HasExtremalIndex (fun k : ℕ => |X k|) P θ) :
    θ ≤ (candidateExtremalIndex Q Θ α).toReal := by
  set ϑ := (candidateExtremalIndex Q Θ α).toReal
  have hϑ1 : ϑ ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (candidateExtremalIndex_le_one hα.le (h.ae_abs_eq_one hΘm (hX 0)))
  have hϑ0 : 0 ≤ ϑ := ENNReal.toReal_nonneg
  obtain ⟨⟨hθ0, hθ1⟩, hθlim⟩ := hθ
  refine le_of_forall_pos_le_add fun τ hτ => ?_
  obtain ⟨u, hu⟩ := h.hasExceedanceLevels_abs hX τ hτ
  have h1 := h.one_sub_le_mul_candidateExtremalIndex hα hX hΘm hstat hu (hθlim τ hτ u hu)
  -- `1 - exp (-x) ≥ x / (1 + x)`
  set e := Real.exp (-(θ * τ))
  have hx : 0 ≤ θ * τ := mul_nonneg hθ0 hτ.le
  have he : e * (1 + θ * τ) ≤ 1 := by
    have h2 : 1 + θ * τ ≤ Real.exp (θ * τ) := by linarith [Real.add_one_le_exp (θ * τ)]
    have h3 : e * Real.exp (θ * τ) = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h4 : 0 ≤ e := (Real.exp_pos _).le
    nlinarith
  have h5 : θ * τ ≤ τ * ϑ * (1 + θ * τ) := by nlinarith
  have h6 : θ ≤ ϑ * (1 + θ * τ) := by
    have : τ * θ ≤ τ * (ϑ * (1 + θ * τ)) := by linarith
    exact le_of_mul_le_mul_left this hτ
  have h7 : ϑ * θ ≤ 1 := by nlinarith
  nlinarith

end Inequality

end ExtremeValueTheory
