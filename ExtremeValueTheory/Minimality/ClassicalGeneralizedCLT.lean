/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverseAsymmetric
import Mathlib.MeasureTheory.Function.Floor

/-!
# Minimality: the tail balance condition in the generalized central limit theorem

The asymmetric generalized central limit theorem
(`ExtremeValueTheory.tendsto_map_convPow_of_isRegularlyVarying_of_lt_one` and its `1 < α < 2`
and `α = 1` companions) assumes, besides regular variation of the two-sided tail
`G(x) = P(|X| > x)` with index `-α`, `0 < α < 2`, the *tail balance condition*
`P(X > x) / G(x) → p`. We show that this hypothesis is necessary, and that it is not implied by
regular variation of `G`.

* `not_tendsto_of_not_tailBalance`: by the converse GCLT
  (`GCLTConverse.exists_isRegularlyVarying_tailBalance_of_tendsto`), if `G` is regularly varying
  with index `-α`, `0 < α < 2`, and the tails are not balanced, then **no** normalization
  `(Sₙ - bₙ) / aₙ` converges in law to a non-degenerate limit.
* `signedPareto α`: the law of `±R` with `R ~ Pareto(1, α)`, where the sign is `+` when
  `⌈log R / L⌉` is odd (`L = log 4 / α`), i.e. the sign alternates on the geometric blocks
  `(4^{j/α}, 4^{(j+1)/α}]`. Then `P(|X| > x) = x^{-α}` for `x ≥ 1` is regularly varying, but
  `P(X > x) / P(|X| > x)` is `≥ 3/4` at `x = 4^{2k/α}` and `≤ 1/4` at `x = 4^{(2k+1)/α}`
  (`not_exists_tailBalance_signedPareto`).
* `signedPareto_gclt_counterexample`: for every `0 < α < 2`, `signedPareto α` satisfies all the
  hypotheses of the GCLT except tail balance, and for no `aₙ > 0`, `bₙ` and non-degenerate `ν`
  do the laws of `(Sₙ - bₙ) / aₙ` converge to `ν`.

## Summary

| hypothesis | status |
|---|---|
| tail balance `P(X > x) / G(x) → p` | necessary: `signedPareto_gclt_counterexample` |
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory.Minimality

open Subexp

/-- The regular variation index is unique. -/
theorem IsRegularlyVarying.index_unique {f : ℝ → ℝ} {ρ σ : ℝ} (hρ : IsRegularlyVarying f ρ)
    (hσ : IsRegularlyVarying f σ) : ρ = σ := by
  have h := tendsto_nhds_unique (hρ.2 2 two_pos) (hσ.2 2 two_pos)
  have := congrArg Real.log h
  rw [Real.log_rpow two_pos, Real.log_rpow two_pos] at this
  exact mul_right_cancel₀ (Real.log_pos one_lt_two).ne' this

/-- **Tail balance is necessary for the generalized CLT.** If `P(|X| > x)` is regularly varying
with index `-α`, `0 < α < 2`, and `P(X > x) / P(|X| > x)` has no limit, then for no `aₙ > 0`,
`bₙ` and non-degenerate `ν` do the laws of `(X₁ + ⋯ + Xₙ - bₙ) / aₙ` converge to `ν`. -/
theorem not_tendsto_of_not_tailBalance {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hnb : ¬ ∃ p, Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p))
    {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ}
    (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x) :
    ¬ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν) := by
  intro hconv
  obtain ⟨α', _, _, hU, hbal⟩ :=
    GCLTConverse.exists_isRegularlyVarying_tailBalance_of_tendsto ha hnd hconv
  have hU' := GCLTConverse.isRegularlyVarying_truncSecondMoment_of_absTail hα0 hα2 hRV
  have hαα : α' = α := by linarith [IsRegularlyVarying.index_unique hU hU']
  obtain ⟨-, -, p, -, -, hp⟩ := hbal (hαα ▸ hα2)
  exact hnb ⟨p, hp⟩

/-! ### The signed Pareto law -/

/-- The block length `L = log 4 / α` on the logarithmic scale. -/
noncomputable def blockLen (α : ℝ) : ℝ := Real.log 4 / α

/-- The sign pattern: `r ↦ r` if `⌈log r / L⌉` is odd, `r ↦ -r` otherwise. -/
noncomputable def signFlip (α : ℝ) (r : ℝ) : ℝ :=
  if Odd ⌈Real.log r / blockLen α⌉ then r else -r

theorem measurable_signFlip (α : ℝ) : Measurable (signFlip α) := by
  refine Measurable.ite ?_ measurable_id measurable_neg
  have hm : Measurable (fun r : ℝ => ⌈Real.log r / blockLen α⌉) :=
    (Int.measurable_ceil (R := ℝ)).comp (measurable_log.div_const _)
  exact hm (MeasurableSet.of_discrete (s := {n : ℤ | Odd n}))

/-- The signed Pareto law: `±R`, `R ~ Pareto(1, α)`, the sign alternating on geometric blocks. -/
noncomputable def signedPareto (α : ℝ) : Measure ℝ :=
  (paretoMeasure 1 α).map (signFlip α)

variable {α : ℝ}

theorem isProbabilityMeasure_signedPareto (hα0 : 0 < α) :
    IsProbabilityMeasure (signedPareto α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα0
  exact (Measure.isProbabilityMeasure_map_iff (measurable_signFlip α).aemeasurable).2 this

theorem abs_signFlip (r : ℝ) : |signFlip α r| = |r| := by
  unfold signFlip; split_ifs <;> simp

theorem pareto_ae_one_le : ∀ᵐ r ∂(paretoMeasure 1 α), 1 ≤ r := by
  rw [ae_iff]
  have : {r : ℝ | ¬ 1 ≤ r} = Iio 1 := by ext; simp
  rw [this]
  exact SymmPareto.pareto_Iio_one

theorem absTail_signedPareto (hα0 : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    absTail (signedPareto α) x = x ^ (-α) := by
  rw [absTail, measureReal_def, signedPareto,
    Measure.map_apply (measurable_signFlip α) (GCLT.measurableSet_abs_gt x)]
  have h : paretoMeasure 1 α (signFlip α ⁻¹' {y | x < |y|}) = paretoMeasure 1 α (Ioi x) := by
    refine measure_congr ?_
    filter_upwards [pareto_ae_one_le] with r hr
    have : |r| = r := abs_of_nonneg (by linarith)
    change (x < |signFlip α r|) = (x < r)
    rw [abs_signFlip, this]
  rw [h, SymmPareto.pareto_Ioi hα0 hx,
    ENNReal.toReal_ofReal (rpow_pos_of_pos (one_pos.trans_le hx) _).le]

theorem isRegularlyVarying_absTail_signedPareto (hα0 : 0 < α) :
    IsRegularlyVarying (absTail (signedPareto α)) (-α) :=
  (IsRegularlyVarying.rpow_id (-α)).congr (by
    filter_upwards [eventually_ge_atTop 1] with x hx using (absTail_signedPareto hα0 hx).symm)

theorem signedPareto_Ioi {x : ℝ} (hx : 1 ≤ x) :
    signedPareto α (Ioi x) =
      paretoMeasure 1 α (Ioi x ∩ {r | Odd ⌈Real.log r / blockLen α⌉}) := by
  rw [signedPareto, Measure.map_apply (measurable_signFlip α) measurableSet_Ioi]
  refine measure_congr ?_
  filter_upwards [pareto_ae_one_le] with r hr
  change (x < signFlip α r) = (x < r ∧ Odd ⌈Real.log r / blockLen α⌉)
  unfold signFlip
  split_ifs with h
  · simp [h]
  · simp only [h, and_false, eq_iff_iff, iff_false, not_lt]
    linarith

theorem blockLen_pos (hα0 : 0 < α) : 0 < blockLen α :=
  div_pos (Real.log_pos (by norm_num)) hα0

theorem rpow_exp_blockLen (hα0 : 0 < α) (t : ℝ) :
    exp (t * blockLen α) ^ (-α) = 4⁻¹ ^ t := by
  rw [← exp_mul, blockLen, rpow_def_of_pos (by norm_num : (0 : ℝ) < 4⁻¹), Real.log_inv]
  congr 1
  field_simp

theorem pareto_Ioc (hα0 : 0 < α) {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    paretoMeasure 1 α (Ioc s t) = ENNReal.ofReal (s ^ (-α) - t ^ (-α)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα0
  rw [← Ioi_sdiff_Ioi, measure_sdiff (Ioi_subset_Ioi hst) measurableSet_Ioi.nullMeasurableSet
    (measure_ne_top _ _), SymmPareto.pareto_Ioi hα0 hs,
    SymmPareto.pareto_Ioi hα0 (hs.trans hst), ENNReal.ofReal_sub _
    (rpow_pos_of_pos (one_pos.trans_le (hs.trans hst)) _).le]

/-- The right-tail ratio of `signedPareto α`. -/
noncomputable def balanceRatio (α : ℝ) (x : ℝ) : ℝ :=
  (signedPareto α).real (Ioi x) / absTail (signedPareto α) x

/-- At `x = exp (2k L)` the ratio is at least `3/4`. -/
theorem balanceRatio_even (hα0 : 0 < α) (k : ℕ) :
    3 / 4 ≤ balanceRatio α (exp ((2 * k) * blockLen α)) := by
  set x := exp ((2 * k) * blockLen α) with hx
  set y := exp ((2 * k + 1) * blockLen α) with hy
  have hL := blockLen_pos hα0
  have hx1 : 1 ≤ x := one_le_exp (by positivity)
  have hxy : x ≤ y := exp_le_exp.2 (by nlinarith)
  have hsub : Ioc x y ⊆ Ioi x ∩ {r | Odd ⌈Real.log r / blockLen α⌉} := by
    intro r ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hr0 : 0 < r := (exp_pos _).trans h1
    have e1 : (2 * k : ℝ) < Real.log r / blockLen α := by
      rw [lt_div_iff₀ hL, ← log_exp ((2 * k) * blockLen α)]
      exact log_lt_log (exp_pos _) h1
    have e2 : Real.log r / blockLen α ≤ 2 * k + 1 := by
      rw [div_le_iff₀ hL, ← log_exp ((2 * k + 1) * blockLen α)]
      exact log_le_log hr0 h2
    have : ⌈Real.log r / blockLen α⌉ = 2 * (k : ℤ) + 1 := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    simp only [mem_ofPred_eq, this]
    exact ⟨k, rfl⟩
  have hmeas : paretoMeasure 1 α (Ioc x y) ≤ signedPareto α (Ioi x) := by
    rw [signedPareto_Ioi hx1]; exact measure_mono hsub
  rw [pareto_Ioc hα0 hx1 hxy] at hmeas
  have := isProbabilityMeasure_paretoMeasure one_pos hα0
  have := isProbabilityMeasure_signedPareto hα0
  have hreal : x ^ (-α) - y ^ (-α) ≤ (signedPareto α).real (Ioi x) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hmeas
  have hx' : x ^ (-α) = 4⁻¹ ^ ((2 * k : ℝ)) := rpow_exp_blockLen hα0 _
  have hy' : y ^ (-α) = 4⁻¹ ^ ((2 * k : ℝ)) * 4⁻¹ := by
    rw [hy, rpow_exp_blockLen hα0, rpow_add (by norm_num), rpow_one]
  have hpos : 0 < x ^ (-α) := rpow_pos_of_pos (one_pos.trans_le hx1) _
  rw [balanceRatio, absTail_signedPareto hα0 hx1, le_div_iff₀ hpos]
  rw [hx', hy'] at hreal
  rw [hx']
  linarith

/-- At `x = exp ((2k + 1) L)` the ratio is at most `1/4`. -/
theorem balanceRatio_odd (hα0 : 0 < α) (k : ℕ) :
    balanceRatio α (exp ((2 * k + 1) * blockLen α)) ≤ 1 / 4 := by
  set x := exp ((2 * k + 1) * blockLen α) with hx
  set y := exp ((2 * k + 2) * blockLen α) with hy
  have hL := blockLen_pos hα0
  have hx1 : 1 ≤ x := one_le_exp (by positivity)
  have hy1 : 1 ≤ y := one_le_exp (by positivity)
  have hsub : Ioi x ∩ {r | Odd ⌈Real.log r / blockLen α⌉} ⊆ Ioi y := by
    intro r ⟨h1, h2⟩
    by_contra h3
    have h3 : r ≤ y := not_lt.1 h3
    have hr0 : 0 < r := (exp_pos _).trans h1
    have e1 : (2 * k + 1 : ℝ) < Real.log r / blockLen α := by
      rw [lt_div_iff₀ hL, ← log_exp ((2 * k + 1) * blockLen α)]
      exact log_lt_log (exp_pos _) h1
    have e2 : Real.log r / blockLen α ≤ 2 * k + 2 := by
      rw [div_le_iff₀ hL, ← log_exp ((2 * k + 2) * blockLen α)]
      exact log_le_log hr0 h3
    have : ⌈Real.log r / blockLen α⌉ = 2 * ((k : ℤ) + 1) := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    simp only [mem_ofPred_eq, this] at h2
    exact Int.not_odd_iff_even.2 (even_two_mul _) h2
  have hmeas : signedPareto α (Ioi x) ≤ paretoMeasure 1 α (Ioi y) := by
    rw [signedPareto_Ioi hx1]; exact measure_mono hsub
  rw [SymmPareto.pareto_Ioi hα0 hy1] at hmeas
  have := isProbabilityMeasure_signedPareto hα0
  have hreal : (signedPareto α).real (Ioi x) ≤ y ^ (-α) := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (rpow_pos_of_pos (one_pos.trans_le hy1) _).le hmeas
  have hx' : x ^ (-α) = 4⁻¹ ^ ((2 * k + 1 : ℝ)) := rpow_exp_blockLen hα0 _
  have hy' : y ^ (-α) = 4⁻¹ ^ ((2 * k + 1 : ℝ)) * 4⁻¹ := by
    rw [hy, rpow_exp_blockLen hα0, show (2 * k + 2 : ℝ) = (2 * k + 1) + 1 by ring,
      rpow_add (by norm_num), rpow_one]
  have hpos : 0 < x ^ (-α) := rpow_pos_of_pos (one_pos.trans_le hx1) _
  rw [balanceRatio, absTail_signedPareto hα0 hx1, div_le_iff₀ hpos]
  rw [hy'] at hreal
  rw [hx']
  linarith

/-- **The signed Pareto law has unbalanced tails**: `P(X > x) / P(|X| > x)` has no limit. -/
theorem not_exists_tailBalance_signedPareto (hα0 : 0 < α) :
    ¬ ∃ p, Tendsto (fun x => (signedPareto α).real (Ioi x) / absTail (signedPareto α) x) atTop
      (𝓝 p) := by
  rintro ⟨p, hp⟩
  have hL := blockLen_pos hα0
  have hseq : ∀ c : ℝ, Tendsto (fun k : ℕ => exp ((2 * k + c) * blockLen α)) atTop atTop := by
    intro c
    refine tendsto_exp_atTop.comp (Tendsto.atTop_mul_const hL ?_)
    exact tendsto_atTop_add_const_right _ c
      (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have h1 : 3 / 4 ≤ p := by
    refine ge_of_tendsto (hp.comp (hseq 0)) (Eventually.of_forall fun k => ?_)
    have := balanceRatio_even hα0 k
    simpa [balanceRatio] using this
  have h2 : p ≤ 1 / 4 := by
    refine le_of_tendsto (hp.comp (hseq 1)) (Eventually.of_forall fun k => ?_)
    exact balanceRatio_odd hα0 k
  linarith

/-- **The tail balance hypothesis of the generalized CLT cannot be dropped.** For every
`0 < α < 2`, the signed Pareto law has a two-sided tail `P(|X| > x) = x^{-α}` (`x ≥ 1`), regularly
varying with index `-α`, with `n P(|X| > n^{1/α}) → 1`; its tails are not balanced; and for no
normalization `aₙ > 0`, `bₙ` and non-degenerate `ν` do the laws of `(Sₙ - bₙ) / aₙ` converge
to `ν`. -/
theorem signedPareto_gclt_counterexample (hα0 : 0 < α) (hα2 : α < 2) :
    IsRegularlyVarying (absTail (signedPareto α)) (-α) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * absTail (signedPareto α) ((n : ℝ) ^ α⁻¹)) atTop (𝓝 1) ∧
      (¬ ∃ p, Tendsto (fun x => (signedPareto α).real (Ioi x) / absTail (signedPareto α) x)
        atTop (𝓝 p)) ∧
      ∀ (a b : ℕ → ℝ), (∀ n, 0 < a n) → ∀ ν : ProbabilityMeasure ℝ,
        (∀ x, (ν : Measure ℝ) ≠ Measure.dirac x) →
        ¬ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
          have := isProbabilityMeasure_signedPareto hα0
          ⟨(convPow (signedPareto α) n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩)
          atTop (𝓝 ν) := by
  have := isProbabilityMeasure_signedPareto hα0
  refine ⟨isRegularlyVarying_absTail_signedPareto hα0, ?_, not_exists_tailBalance_signedPareto hα0,
    fun a b ha ν hnd => not_tendsto_of_not_tailBalance hα0 hα2
      (isRegularlyVarying_absTail_signedPareto hα0) (not_exists_tailBalance_signedPareto hα0) ha
      hnd⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [absTail_signedPareto hα0 (one_le_rpow hn1 (inv_nonneg.2 hα0.le)), ← rpow_mul (by linarith),
    show α⁻¹ * -α = -1 by field_simp, rpow_neg_one, mul_inv_cancel₀ (by linarith)]

end ExtremeValueTheory.Minimality
