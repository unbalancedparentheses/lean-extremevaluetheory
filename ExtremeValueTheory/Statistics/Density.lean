/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Densities from distribution functions

If the distribution function `F(x) = μ(-∞, x]` of a finite measure `μ` on `ℝ` is continuous and
differentiable with a nonnegative derivative `f` outside two exceptional points, then `μ` has
density `f` with respect to Lebesgue measure. The two exceptional points are where the
distribution functions of the generalized Pareto and generalized extreme value laws fail to be
differentiable: the endpoints of their supports.

## Main results

* `ExtremeValueTheory.intervalIntegral_eq_sub_of_hasDerivAt_off`: the fundamental theorem of
  calculus for a continuous `F` with a nonnegative derivative `f` outside two points; `f` is
  automatically interval integrable.
* `ExtremeValueTheory.eq_withDensity_of_hasDerivAt_off`: `μ = volume.withDensity f`.
* `ExtremeValueTheory.integral_eq_one_of_eq_withDensity`: a probability density integrates to `1`.
-/

open Filter Topology Set MeasureTheory

namespace ExtremeValueTheory

variable {F f : ℝ → ℝ}

private lemma ftc_piece {a b : ℝ} (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = F b - F a := by
  have hi : IntervalIntegrable f volume a b := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := F) (by rwa [uIcc_of_le hab])
      ?_ ?_
    · simpa [min_eq_left hab, max_eq_right hab] using hd
    · simpa [min_eq_left hab, max_eq_right hab] using hf
  exact ⟨hi, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd hi⟩

private lemma ftc_split {a m b : ℝ}
    (h1 : IntervalIntegrable f volume a m ∧ ∫ x in a..m, f x = F m - F a)
    (h2 : IntervalIntegrable f volume m b ∧ ∫ x in m..b, f x = F b - F m) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = F b - F a :=
  ⟨h1.1.trans h2.1, by
    rw [← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1, h1.2, h2.2]; ring⟩

private lemma ftc_one {a b c : ℝ} (hab : a ≤ b) (hF : Continuous F)
    (hd : ∀ x ∈ Ioo a b, x ≠ c → HasDerivAt F (f x) x) (hf : ∀ x, 0 ≤ f x) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = F b - F a := by
  by_cases hc : c ∈ Ioo a b
  · exact ftc_split
      (ftc_piece hc.1.le hF.continuousOn
        (fun x hx => hd x ⟨hx.1, hx.2.trans hc.2⟩ hx.2.ne) fun x _ => hf x)
      (ftc_piece hc.2.le hF.continuousOn
        (fun x hx => hd x ⟨hc.1.trans hx.1, hx.2⟩ hx.1.ne') fun x _ => hf x)
  · exact ftc_piece hab hF.continuousOn (fun x hx => hd x hx fun h => hc (h ▸ hx)) fun x _ => hf x

/-- **Fundamental theorem of calculus off two points.** If `F` is continuous and has a
nonnegative derivative `f` outside `{c₁, c₂}`, then `f` is interval integrable and
`∫_a^b f = F b - F a`. -/
theorem intervalIntegral_eq_sub_of_hasDerivAt_off {a b c₁ c₂ : ℝ} (hab : a ≤ b)
    (hF : Continuous F) (hd : ∀ x, x ≠ c₁ → x ≠ c₂ → HasDerivAt F (f x) x) (hf : ∀ x, 0 ≤ f x) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = F b - F a := by
  by_cases hc : c₁ ∈ Ioo a b
  · exact ftc_split (ftc_one hc.1.le hF (fun x hx h2 => hd x hx.2.ne h2) hf)
      (ftc_one hc.2.le hF (fun x hx h2 => hd x hx.1.ne' h2) hf)
  · exact ftc_one hab hF (fun x hx h2 => hd x (fun h => hc (h ▸ hx)) h2) hf

/-- **A distribution function with a derivative off two points has a density.** Let `μ` be a
finite measure on `ℝ` with `μ(-∞, x] = F(x)`, where `F` is continuous, `F → 0` at `-∞`, and
`F' = f ≥ 0` outside `{c₁, c₂}`. Then `μ = volume.withDensity f`. -/
theorem eq_withDensity_of_hasDerivAt_off {μ : Measure ℝ} [IsFiniteMeasure μ] {c₁ c₂ : ℝ}
    (hF : Continuous F) (hbot : Tendsto F atBot (𝓝 0))
    (hμ : ∀ x, μ (Iic x) = ENNReal.ofReal (F x))
    (hd : ∀ x, x ≠ c₁ → x ≠ c₂ → HasDerivAt F (f x) x) (hf : ∀ x, 0 ≤ f x) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  refine Measure.ext_of_Iic _ _ fun x => ?_
  set ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hIoc : ∀ n : ℕ, ν (Ioc (x - n) x) = ENNReal.ofReal (F x - F (x - n)) := by
    intro n
    have hle : x - n ≤ x := by linarith [n.cast_nonneg (α := ℝ)]
    have h := intervalIntegral_eq_sub_of_hasDerivAt_off hle hF hd hf
    rw [withDensity_apply _ measurableSet_Ioc, ← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 h.1) (ae_of_all _ fun _ => hf _),
      ← intervalIntegral.integral_of_le hle, h.2]
  have hmono : Monotone fun n : ℕ => Ioc (x - n) x := by
    intro m n hmn y hy
    exact ⟨lt_of_le_of_lt (by linarith [(Nat.cast_le (α := ℝ)).2 hmn]) hy.1, hy.2⟩
  have hU : (⋃ n : ℕ, Ioc (x - n) x) = Iic x := by
    ext y
    simp only [mem_iUnion, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨n, -, h⟩; exact h
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_gt (x - y)
      exact ⟨n, by linarith, h⟩
  have h1 := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU] at h1
  have hlim : Tendsto (fun n : ℕ => x - n) atTop atBot :=
    tendsto_atBot_add_const_left _ x (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (F x - F (x - n))) atTop
      (𝓝 (ENNReal.ofReal (F x))) := by
    have := (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_const_nhds (x := F x) |>.sub (hbot.comp hlim))
    simpa [Function.comp_def] using this
  rw [hμ]
  exact tendsto_nhds_unique h2 (h1.congr fun n => hIoc n)

/-- A probability density integrates to one. -/
theorem integral_eq_one_of_eq_withDensity {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) (hf : ∀ x, 0 ≤ f x)
    (hfm : AEStronglyMeasurable f volume) :
    Integrable f volume ∧ ∫ x, f x = 1 := by
  have hl : ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hμ, measure_univ]
  have hi : Integrable f volume := by
    refine ⟨hfm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hf), hl]
    exact ENNReal.one_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hfm, hl, ENNReal.toReal_one]

end ExtremeValueTheory
