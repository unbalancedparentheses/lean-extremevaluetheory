/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.Gumbel

/-!
# Minimality: no atom at a finite right endpoint in the Gumbel von Mises theorem

`CumulativeDistributionFunction.isInMDAGumbel_of_vonMises_nhdsLT` (and the auxiliary-function
statement `tendsto_auxiliary_of_vonMises_nhdsLT`) assume, besides the von Mises condition
`(1 - F) F'' / (F')² → -1` as `t ↑ x_F`, that `F (t) → 1` as `t ↑ x_F`, i.e. that `F` has no atom
at the finite endpoint `x_F`. We show that this hypothesis cannot be dropped.

* `not_tendsto_pow_of_gap`: if the values of `F` avoid an interval `(c, 1)`, `c < 1`, then for no
  affine normalization does `F^n(aₙ x + bₙ)` converge to a limit value in `(0, 1)`. In particular
  such an `F` is in no max-domain of attraction (`not_isInMDAGumbel_of_gap`).
* `atomCDF`: `F (t) = 1 - e^{-t}` on `[0, 1)`, `F = 1` on `[1, ∞)` (an exponential law with all
  the mass beyond `1` moved to an atom at `1`).
* `atomCDF_vonMises_counterexample`: `atomCDF` satisfies every hypothesis of
  `isInMDAGumbel_of_vonMises_nhdsLT` with `z = 0`, `x_F = 1`, `F₁ = e^{-t}`, `F₂ = -e^{-t}`
  (indeed `(1 - F) F'' / (F')² = -1` exactly on `(0, 1)`) except `F (t) → 1` as `t ↑ 1`, and it
  is not in the Gumbel domain of attraction; moreover the auxiliary-function limit of
  `tendsto_auxiliary_of_vonMises_nhdsLT` fails at `x = 1`.

## Summary

| hypothesis | status |
|---|---|
| `F (t) → 1` as `t ↑ x_F` | necessary: `atomCDF_vonMises_counterexample` |
-/

open Filter Topology Set Real

namespace ExtremeValueTheory.Minimality

open CumulativeDistributionFunction

/-- If the values of `F` avoid `(c, 1)` with `c < 1`, then `F^n` evaluated along any affine
normalization cannot converge to a value in `(0, 1)`. -/
theorem not_tendsto_pow_of_gap (F : CumulativeDistributionFunction) {c : ℝ} (hc : c < 1)
    (hF : ∀ y, F y ≤ c ∨ F y = 1) (As : ℕ → AffineIncrEquiv) (x : ℝ) {g : ℝ} (hg0 : 0 < g)
    (hg1 : g < 1) : ¬ Tendsto (fun n : ℕ => ((As n • F) x) ^ n) atTop (𝓝 g) := by
  intro h
  set d := max c 0 with hd
  have hd1 : d < 1 := max_lt hc one_pos
  have hle : ∀ᶠ n : ℕ in atTop, ((As n • F) x) ^ n ≤ d ^ n := by
    filter_upwards [h.eventually (gt_mem_nhds hg1), eventually_ge_atTop 1] with n hn hn1
    rw [mulAction_apply_eq] at hn ⊢
    rcases hF ((As n)⁻¹ x) with h1 | h1
    · exact pow_le_pow_left₀ (F.apply_nonneg _) (h1.trans (le_max_left _ _)) n
    · rw [h1, one_pow] at hn
      exact absurd hn (lt_irrefl _)
  have h0 : Tendsto (fun n : ℕ => d ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_right _ _) hd1
  have := le_of_tendsto_of_tendsto h h0 hle
  linarith

/-- A c.d.f. whose values avoid `(c, 1)`, `c < 1`, is not in the Gumbel domain of attraction. -/
theorem not_isInMDAGumbel_of_gap (F : CumulativeDistributionFunction) {c : ℝ} (hc : c < 1)
    (hF : ∀ y, F y ≤ c ∨ F y = 1) : ¬ F.IsInMDAGumbel := by
  rintro ⟨As, hAs⟩
  have h := hAs 0
  rw [standardGumbelCDF_apply_eq] at h
  refine not_tendsto_pow_of_gap F hc hF As 0 (exp_pos _) ?_ h
  exact exp_lt_one_iff.2 (by simp)

/-- The exponential law with its mass beyond `1` moved to an atom at `1`:
`F t = max 0 (1 - e^{-t})` for `t < 1` and `F t = 1` for `t ≥ 1`. -/
noncomputable def atomCDF : CumulativeDistributionFunction where
  toFun t := if t < 1 then max 0 (1 - exp (-t)) else 1
  mono' := by
    intro s t hst
    simp only
    by_cases ht : t < 1
    · rw [ite_eq_left (hst.trans_lt ht), ite_eq_left ht]
      exact max_le_max le_rfl (by gcongr)
    · rw [ite_eq_right ht]
      split_ifs
      · exact max_le zero_le_one (by linarith [exp_pos (-s)])
      · exact le_rfl
  right_continuous' := by
    intro x
    by_cases hx : x < 1
    · have hc : ContinuousWithinAt (fun t : ℝ => max 0 (1 - exp (-t))) (Ici x) x :=
        (continuous_const.max (continuous_const.sub (continuous_exp.comp continuous_neg)))
          |>.continuousWithinAt
      refine hc.congr_of_eventuallyEq ?_ (ite_eq_left hx)
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with t ht
      exact ite_eq_left ht
    · refine (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq ?_ (ite_eq_right hx)
      filter_upwards [self_mem_nhdsWithin] with t (ht : x ≤ t)
      exact ite_eq_right fun h => hx (ht.trans_lt h)
  tendsto_atTop := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (ite_eq_right (not_lt.2 ht)).symm
  tendsto_atBot := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot 0] with t ht
    rw [ite_eq_left (by linarith)]
    refine (max_eq_left ?_).symm
    have := add_one_le_exp (-t)
    linarith

theorem atomCDF_of_lt {t : ℝ} (ht : t < 1) : atomCDF t = max 0 (1 - exp (-t)) := ite_eq_left ht

theorem atomCDF_of_ge {t : ℝ} (ht : 1 ≤ t) : atomCDF t = 1 := ite_eq_right (not_lt.2 ht)

theorem atomCDF_of_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : atomCDF t = 1 - exp (-t) := by
  rw [atomCDF_of_lt ht.2]
  refine max_eq_right ?_
  have : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith [ht.1])
  linarith

theorem atomCDF_le_of_lt {y : ℝ} (hy : y < 1) : atomCDF y ≤ 1 - exp (-1) := by
  rw [atomCDF_of_lt hy]
  refine max_le (by linarith [exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)]) ?_
  have : exp (-1) ≤ exp (-y) := exp_le_exp.2 (by linarith)
  linarith

theorem atomCDF_gap (y : ℝ) : atomCDF y ≤ 1 - exp (-1) ∨ atomCDF y = 1 := by
  by_cases hy : y < 1
  · exact Or.inl (atomCDF_le_of_lt hy)
  · exact Or.inr (atomCDF_of_ge (not_lt.1 hy))

/-- **The no-atom hypothesis of the finite-endpoint Gumbel von Mises theorem is necessary.**
`atomCDF` is twice differentiable on `(0, 1)` with `F' = e^{-t} > 0`, `F'' = -e^{-t}` and
`(1 - F) F'' / (F')² → -1` as `t ↑ 1`, but `F (t) ↛ 1` as `t ↑ 1` (there is an atom at `1`), and
the conclusion of `isInMDAGumbel_of_vonMises_nhdsLT` fails: `atomCDF` is not in the Gumbel
domain of attraction. The auxiliary-function limit of `tendsto_auxiliary_of_vonMises_nhdsLT`
also fails, at `x = 1`. -/
theorem atomCDF_vonMises_counterexample :
    (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt atomCDF (exp (-x)) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => exp (-t)) (-exp (-x)) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 0 < exp (-x)) ∧
      Tendsto (fun t => (1 - atomCDF t) * (-exp (-t)) / exp (-t) ^ 2) (𝓝[<] 1) (𝓝 (-1)) ∧
      ¬ Tendsto atomCDF (𝓝[<] 1) (𝓝 1) ∧
      ¬ atomCDF.IsInMDAGumbel ∧
      ¬ Tendsto (fun t => (1 - atomCDF (t + 1 * ((1 - atomCDF t) / exp (-t)))) /
        (1 - atomCDF t)) (𝓝[<] 1) (𝓝 (exp (-1))) := by
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  refine ⟨fun x hx => ?_, fun x _ => ?_, fun x _ => exp_pos _, ?_, ?_,
    not_isInMDAGumbel_of_gap atomCDF (by linarith [exp_pos (-1)]) atomCDF_gap, ?_⟩
  · have h : HasDerivAt (fun t => 1 - exp (-t)) (exp (-x)) x := by
      simpa using ((hasDerivAt_neg x).exp).const_sub 1
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact atomCDF_of_mem ht
  · simpa using (hasDerivAt_neg x).exp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with t ht
    rw [atomCDF_of_mem ht]
    have := (exp_pos (-t)).ne'
    field_simp
    ring
  · intro h
    have hle : ∀ᶠ t in 𝓝[<] (1 : ℝ), atomCDF t ≤ 1 - exp (-1) :=
      eventually_nhdsWithin_of_forall fun t (ht : t < 1) => atomCDF_le_of_lt ht
    have := le_of_tendsto h hle
    linarith [exp_pos (-1)]
  · -- for `t ∈ (0, 1)`, `t + 1 * f t = t + 1 > 1`, so the ratio is `0`
    intro h
    have h0 : Tendsto (fun t => (1 - atomCDF (t + 1 * ((1 - atomCDF t) / exp (-t)))) /
        (1 - atomCDF t)) (𝓝[<] 1) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with t ht
      have hf : (1 - atomCDF t) / exp (-t) = 1 := by
        rw [atomCDF_of_mem ht, sub_sub_cancel, div_self (exp_pos _).ne']
      rw [hf, one_mul, atomCDF_of_ge (by linarith [ht.1]), sub_self, zero_div]
    exact (exp_pos (-1)).ne' (tendsto_nhds_unique h h0)

end ExtremeValueTheory.Minimality
