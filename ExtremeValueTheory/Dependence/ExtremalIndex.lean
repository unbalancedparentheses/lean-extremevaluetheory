/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Leadbetter
import ExtremeValueTheory.SelfSimilarCDF
import ExtremeValueTheory.LimitRelationManipulation

/-!
# The extremal index

A stationary sequence `X` has *extremal index* `θ ∈ [0, 1]` if, whenever
`n P(X 0 > uₙ) → τ > 0`, the maxima satisfy `P(M n ≤ uₙ) → exp (-θ τ)` [LLR, §3.7],
[EKM, Definition 8.1.1]. For an iid sequence `θ = 1`; `θ < 1` measures clustering of extremes.

## Main definitions and results

* `ExtremeValueTheory.HasExtremalIndex X P θ`: `X` has extremal index `θ`.
* `ExtremeValueTheory.HasExtremalIndexStrict X P θ`: `X` has extremal index `θ` and every `τ > 0`
  is attained by a level sequence, as in [LLR, §3.7]; `HasExtremalIndexStrict.unique`.
* `ExtremeValueTheory.hasExtremalIndex_one`: Leadbetter's conditions `D(uₙ)` and `D'(uₙ)` at all
  levels with `n P(X 0 > uₙ) → τ > 0` give extremal index `1` [LLR, Theorem 3.4.1].
* `CumulativeDistributionFunction.IsExtremeValueDistr.continuous`: extreme value distributions
  are continuous.
* `ExtremeValueTheory.tendsto_measureReal_partialMax_le_pow`: if the marginal `F` of `X` is in the
  maximum domain of attraction of an extreme value distribution `H` with normalizations `Aₙ`, and
  `X` has extremal index `θ > 0`, then `P(M n ≤ Aₙ⁻¹ x) → H(x)^θ` for every `x`
  [LLR, §3.7], [EKM, §8.1].
* `ExtremeValueTheory.isExtremeValueDistr_pow`: `H^θ` is an extreme value distribution of the same
  type as `H`, i.e. `H^θ = A • H` for an affine `A` (max-stability).

## Remarks

We quantify over *all* level sequences with `n P(X 0 > uₙ) → τ`. For marginals with atoms such
sequences need not exist for every `τ`, in which case `HasExtremalIndex` is vacuous for that `τ`
(and `θ` need not be unique); the original definition [LLR, §3.7] also asks for the existence of
such a sequence for each `τ`. This stronger notion is `HasExtremalIndexStrict`
(= `HasExtremalIndex` plus `HasExceedanceLevels`); it determines `θ`
(`HasExtremalIndexStrict.unique`) and follows from `HasExtremalIndex` when the marginal c.d.f. is
continuous (`HasExtremalIndex.strict_of_continuous`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace CumulativeDistributionFunction

/-- **Extreme value distributions are continuous**: by the Fisher–Tippett–Gnedenko classification
they are affine images of the (continuous) standard Gumbel, Fréchet and Weibull laws. -/
theorem IsExtremeValueDistr.continuous {G : CumulativeDistributionFunction}
    (hG : G.IsExtremeValueDistr) : Continuous G := by
  have key : ∀ (A : AffineIncrEquiv) (S : CumulativeDistributionFunction), Continuous S →
      A • G = S → Continuous G := by
    intro A S hS hAG
    have e : (G : ℝ → ℝ) = fun x ↦ S (A.coefs.1 * x + A.coefs.2) := by
      funext x
      rw [← hAG, ← AffineIncrEquiv.apply_eq, mulAction_apply_eq_self_apply]
    rw [e]
    exact hS.comp (continuous_const.mul continuous_id |>.add continuous_const)
  rcases hG.classification with ⟨A, hA⟩ | ⟨A, ξ, hξ, hA⟩ | ⟨A, ξ, hξ, hA⟩
  · refine key A _ ?_ hA
    have : (standardGumbelCDF : ℝ → ℝ) = fun x ↦ Real.exp (-Real.exp (-x)) :=
      funext standardGumbelCDF_apply_eq
    rw [this]; fun_prop
  · exact key A _ (continuous_standardFrechetAux hξ) hA
  · refine key A _ ?_ hA
    have : (standardWeibullCDF hξ : ℝ → ℝ) = fun x ↦ Real.exp (-((max (-x) 0) ^ ξ)) :=
      funext (standardWeibullAux_eq hξ)
    rw [this]
    exact Real.continuous_exp.comp ((Real.continuous_rpow_const hξ.le).comp
      (continuous_neg.max continuous_const)).neg

end CumulativeDistributionFunction

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Extremal index** [LLR, §3.7], [EKM, Definition 8.1.1]: `θ ∈ [0, 1]` and for every `τ > 0`
and every level sequence `uₙ` with `n P(X 0 > uₙ) → τ`, `P(M n ≤ uₙ) → exp (-θ τ)`. -/
def HasExtremalIndex (X : ℕ → Ω → ℝ) (P : Measure Ω) (θ : ℝ) : Prop :=
  θ ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ τ > 0, ∀ u : ℕ → ℝ,
    Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ) →
      Tendsto (fun n ↦ P.real {ω | partialMax X n ω ≤ u n}) atTop (𝓝 (Real.exp (-(θ * τ))))

/-- The sequence `X` *admits exceedance levels* if for every `τ > 0` there is a level sequence
`uₙ` with `n P(X 0 > uₙ) → τ`. This holds for instance when the marginal c.d.f. of `X 0` is
continuous (`hasExceedanceLevels_of_continuous`); for marginals with atoms it may fail. -/
def HasExceedanceLevels (X : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ τ > 0, ∃ u : ℕ → ℝ, Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ)

/-- **Extremal index in the sense of [LLR, §3.7].** `HasExtremalIndex X P θ` together with the
existence, for every `τ > 0`, of levels `uₙ` with `n P(X 0 > uₙ) → τ`. Unlike
`HasExtremalIndex`, which is vacuous at the values of `τ` not attained by any level sequence, this
determines `θ` uniquely (`HasExtremalIndexStrict.unique`). -/
structure HasExtremalIndexStrict (X : ℕ → Ω → ℝ) (P : Measure Ω) (θ : ℝ) : Prop where
  /-- The limit relation defining the extremal index. -/
  hasExtremalIndex : HasExtremalIndex X P θ
  /-- Every `τ > 0` is attained by some level sequence. -/
  hasExceedanceLevels : HasExceedanceLevels X P

/-- **Uniqueness of the extremal index**: when exceedance levels exist, the extremal index is
unique. -/
theorem HasExtremalIndex.unique {θ θ' : ℝ} (h : HasExtremalIndex X P θ)
    (h' : HasExtremalIndex X P θ') (hl : HasExceedanceLevels X P) : θ = θ' := by
  obtain ⟨u, hu⟩ := hl 1 one_pos
  have := tendsto_nhds_unique (h.2 1 one_pos u hu) (h'.2 1 one_pos u hu)
  simpa using this

/-- **Uniqueness of the extremal index** in the sense of [LLR, §3.7]. -/
theorem HasExtremalIndexStrict.unique {θ θ' : ℝ} (h : HasExtremalIndexStrict X P θ)
    (h' : HasExtremalIndexStrict X P θ') : θ = θ' :=
  h.hasExtremalIndex.unique h'.hasExtremalIndex h.hasExceedanceLevels

/-- Exceedance levels exist when the marginal c.d.f. `x ↦ P(X 0 ≤ x)` is continuous: one can then
choose `uₙ` with `P(X 0 > uₙ) = τ / n` exactly for `n > τ`. -/
theorem hasExceedanceLevels_of_continuous [IsProbabilityMeasure P] (hX0 : Measurable (X 0))
    (hcont : Continuous fun x ↦ P.real {ω | X 0 ω ≤ x}) : HasExceedanceLevels X P := by
  set G : ℝ → ℝ := fun x ↦ P.real {ω | X 0 ω ≤ x} with hG
  have hGcdf : G = cdf (P.map (X 0)) := by
    funext x
    rw [cdf_eq_real, map_measureReal_apply hX0 measurableSet_Iic]
    rfl
  have hbot : Tendsto G atBot (𝓝 0) := hGcdf ▸ tendsto_cdf_atBot _
  have htop : Tendsto G atTop (𝓝 1) := hGcdf ▸ tendsto_cdf_atTop _
  have hsurv (v : ℝ) : P.real {ω | v < X 0 ω} = 1 - G v := by
    have : {ω | v < X 0 ω} = {ω | X 0 ω ≤ v}ᶜ := by ext; simp
    rw [this, probReal_compl_eq_one_sub (measurableSet_le hX0 measurable_const)]
  intro τ hτ
  have hrange (n : ℕ) (hn : τ < n) : 1 - τ / n ∈ Set.range G := by
    have hn0 : (0 : ℝ) < n := hτ.trans hn
    have h1 : 0 < 1 - τ / n := by rw [sub_pos, div_lt_one hn0]; exact hn
    have h2 : 1 - τ / n < 1 := by linarith [div_pos hτ hn0]
    refine mem_range_of_exists_le_of_exists_ge hcont ?_ ?_
    · obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds h1)).exists
      exact ⟨a, ha.le⟩
    · obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds h2)).exists
      exact ⟨b, hb.le⟩
  classical
  refine ⟨fun n ↦ if hn : τ < n then (hrange n hn).choose else 0, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt τ
  filter_upwards [eventually_ge_atTop N] with n hn
  have hτn : τ < n := hN.trans_le (by exact_mod_cast hn)
  simp only [hτn, dite_true]
  have hn0 : (n : ℝ) ≠ 0 := (hτ.trans hτn).ne'
  rw [hsurv, (hrange n hτn).choose_spec, sub_sub_cancel, mul_div_cancel₀ τ hn0]

/-- A sequence with extremal index `θ` and continuous marginal c.d.f. has extremal index `θ` in the
sense of [LLR, §3.7]. -/
theorem HasExtremalIndex.strict_of_continuous [IsProbabilityMeasure P] {θ : ℝ}
    (h : HasExtremalIndex X P θ) (hX0 : Measurable (X 0))
    (hcont : Continuous fun x ↦ P.real {ω | X 0 ω ≤ x}) : HasExtremalIndexStrict X P θ :=
  ⟨h, hasExceedanceLevels_of_continuous hX0 hcont⟩

/-- Under Leadbetter's conditions `D(uₙ)` and `D'(uₙ)` for all relevant level sequences, the
extremal index is `1` [LLR, Theorem 3.4.1], [EKM, Theorem 4.4.3]. -/
theorem hasExtremalIndex_one [IsProbabilityMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t))
    (hDD' : ∀ τ > 0, ∀ u : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ n * P.real {ω | u n < X 0 ω}) atTop (𝓝 τ) →
        ConditionD X P u ∧ ConditionD' X P u) :
    HasExtremalIndex X P 1 := by
  refine ⟨⟨zero_le_one, le_rfl⟩, fun τ hτ u hu ↦ ?_⟩
  rw [one_mul]
  exact tendsto_measureReal_partialMax_le_exp hs hX (hDD' τ hτ u hu).1 (hDD' τ hτ u hu).2 hu

/-- If `aₙ ∈ [0, 1]` and `aₙ ^ n → 1` then `n (1 - aₙ) → 0`. -/
lemma tendsto_natCast_mul_one_sub_of_tendsto_pow_one {a : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n)
    (h1 : ∀ n, a n ≤ 1) (h : Tendsto (fun n ↦ a n ^ n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ ↦ n * (1 - a n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n ↦ -Real.log (a n ^ n)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp h).neg
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    (Eventually.of_forall fun n ↦ mul_nonneg n.cast_nonneg (sub_nonneg.2 (h1 n))) ?_
  filter_upwards [h.eventually (lt_mem_nhds one_half_lt_one), eventually_ge_atTop 1] with n hn hn1
  have hapos : 0 < a n := by
    rcases (h0 n).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow (by omega)] at hn; norm_num at hn
  rw [Real.log_pow]
  have := Real.log_le_sub_one_of_pos hapos
  nlinarith [n.cast_nonneg (α := ℝ)]

/-- **Maxima of stationary sequences with an extremal index** [LLR, §3.7]: if the
marginal c.d.f. `F` of `X 0` is in the maximum domain of attraction of an extreme value
distribution `H` with normalizations `Aₙ` (that is, `F(Aₙ⁻¹ x) ^ n → H x`) and `X` has extremal
index `θ > 0`, then `P(M n ≤ Aₙ⁻¹ x) → H(x) ^ θ` for every `x`. -/
theorem tendsto_measureReal_partialMax_le_pow [IsProbabilityMeasure P] (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) {F H : CumulativeDistributionFunction}
    (hF : ∀ x, F x = P.real {ω | X 0 ω ≤ x}) (hH : H.IsExtremeValueDistr)
    (As : ℕ → AffineIncrEquiv) (hlim : ∀ x, Tendsto (fun n ↦ ((As n • F) x) ^ n) atTop (𝓝 (H x)))
    {θ : ℝ} (hθ : HasExtremalIndex X P θ) (hθ0 : 0 < θ) (x : ℝ) :
    Tendsto (fun n ↦ P.real {ω | partialMax X n ω ≤ (As n)⁻¹ x}) atTop (𝓝 (H.pow hθ0 x)) := by
  have hsurv : ∀ v : ℝ, P.real {ω | v < X 0 ω} = 1 - F v := by
    intro v
    have : {ω | v < X 0 ω} = {ω | X 0 ω ≤ v}ᶜ := by ext; simp
    rw [this, probReal_compl_eq_one_sub (measurableSet_le (hX 0) measurable_const), hF]
  simp only [CumulativeDistributionFunction.pow_apply_eq]
  -- the interior case `H x ∈ (0, 1)`
  have key : ∀ y, H y ∈ Set.Ioo 0 1 → Tendsto (fun n ↦ P.real {ω | partialMax X n ω ≤ (As n)⁻¹ y})
      atTop (𝓝 (H y ^ θ)) := by
    intro y hy
    have h3 := ((tfae_ev_limit_relation As hy).out 1 3).1
      (hlim y)
    have hτ : Tendsto (fun n : ℕ ↦ n * P.real {ω | (As n)⁻¹ y < X 0 ω}) atTop
        (𝓝 (-Real.log (H y))) := by
      refine h3.congr fun n ↦ ?_
      rw [hsurv, CumulativeDistributionFunction.mulAction_apply_eq]
    have hτ0 : 0 < -Real.log (H y) := neg_pos.2 (Real.log_neg hy.1 hy.2)
    have := hθ.2 _ hτ0 _ hτ
    rwa [show -(θ * -Real.log (H y)) = Real.log (H y) * θ by ring,
      ← Real.rpow_def_of_pos hy.1] at this
  have hmono : Monotone H := H.mono'
  rcases eq_or_lt_of_le (H.apply_nonneg x) with h0 | h0
  · -- `H x = 0`: compare with levels `y > x` where `H y` is small
    rw [← h0, Real.zero_rpow hθ0.ne']
    have hcont := hH.continuous
    rw [tendsto_order]
    refine ⟨fun a ha ↦ Eventually.of_forall fun n ↦ ha.trans_le measureReal_nonneg, fun b hb ↦ ?_⟩
    set c := min (1 / 2) (b ^ θ⁻¹ / 2) with hc
    have hbθ : 0 < b ^ θ⁻¹ := Real.rpow_pos_of_pos hb _
    have hc0 : 0 < c := lt_min one_half_pos (half_pos hbθ)
    have hc1 : c < 1 := (min_le_left _ _).trans_lt one_half_lt_one
    have hcb : c ^ θ < b := by
      have : c < b ^ θ⁻¹ := (min_le_right _ _).trans_lt (half_lt_self hbθ)
      calc c ^ θ < (b ^ θ⁻¹) ^ θ := Real.rpow_lt_rpow hc0.le this hθ0
        _ = b := Real.rpow_inv_rpow hb.le hθ0.ne'
    obtain ⟨z, hz⟩ := (H.tendsto_atTop.eventually (lt_mem_nhds hc1)).exists
    obtain ⟨y, hy⟩ : c ∈ Set.range H :=
      intermediate_value_univ x z hcont ⟨by rw [← h0]; exact hc0.le, hz.le⟩
    have hxy : x ≤ y := by
      by_contra hcon
      have := hmono (le_of_not_ge hcon)
      rw [hy, ← h0] at this
      linarith
    have hlimy := key y (by rw [hy]; exact ⟨hc0, hc1⟩)
    rw [hy] at hlimy
    filter_upwards [hlimy.eventually (gt_mem_nhds hcb)] with n hn
    refine lt_of_le_of_lt (measureReal_mono fun ω hω ↦ ?_) hn
    exact le_trans hω ((As n)⁻¹.mono hxy)
  rcases eq_or_lt_of_le (H.apply_le_one x) with h1 | h1
  · -- `H x = 1`: the union bound gives `P(M n ≤ uₙ) ≥ 1 - n P(X 0 > uₙ) → 1`
    rw [h1, Real.one_rpow]
    have hn0 := tendsto_natCast_mul_one_sub_of_tendsto_pow_one (a := fun n ↦ (As n • F) x)
      (fun n ↦ F.apply_nonneg _ |>.trans_eq' (by rfl)) (fun n ↦ (F.apply_le_one _))
      (by rw [← h1]; exact hlim x)
    have hlow : Tendsto (fun n : ℕ ↦ 1 - n * (1 - (As n • F) x)) atTop (𝓝 1) := by
      simpa using hn0.const_sub 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
      (Eventually.of_forall fun n ↦ measureReal_le_one)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [measureReal_partialMax_le (by omega)]
    have := (hs.measureReal_maxLE_range_bounds hX n ((As n)⁻¹ x)).1
    rw [hsurv] at this
    simpa [CumulativeDistributionFunction.mulAction_apply_eq] using this
  · exact key x ⟨h0, h1⟩

/-- The limit `H ^ θ` of the maxima of a stationary sequence with extremal index `θ > 0` is an
extreme value distribution of the same type as `H`: `H ^ θ = A • H` for some affine `A`
[LLR, §3.7]. -/
theorem isExtremeValueDistr_pow {H : CumulativeDistributionFunction}
    (hH : H.IsExtremeValueDistr) {θ : ℝ} (hθ0 : 0 < θ) :
    (H.pow hθ0).IsExtremeValueDistr ∧ ∃ A : AffineIncrEquiv, A • H = H.pow hθ0 := by
  obtain ⟨A, hA⟩ := CumulativeDistributionFunction.exists_smul_eq_pow_of_isExtremeValueDistr hH hθ0
  refine ⟨?_, A, hA⟩
  rw [← hA]
  exact hH.affineTransform H A

end ExtremeValueTheory
