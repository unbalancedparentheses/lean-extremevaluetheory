/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# A central limit theorem for triangular arrays with uniformly small summands

Let `U 0, U 1, …` be independent random elements of a measurable space `α`, all with law `μ`,
and for each `n` let `f n : α → ℝ` be a measurable function. If the `f n` are centered under
`μ`, bounded by constants `M n → 0`, and `n ∫ (f n) ^ 2 dμ → v`, then the row sums
`∑_{i < n} f n (U i)` converge in distribution to the centered Gaussian law with variance `v`.

This is the Lindeberg–Feller theorem for rows of i.i.d. summands under the (much stronger)
uniform smallness condition `sup |f n| → 0`, which makes Lindeberg's condition trivial. It covers
the "Poissonian" triangular arrays of tail empirical processes, where the summands are
`k^{-1/2} (1{U_i > 1 - (k/n) t} - (k/n) t)` with `k → ∞`, `k / n → 0`.

The proof goes through characteristic functions: the characteristic function of the row sum is
`φ_n(s) ^ n` with `φ_n(s) = ∫ exp (i s f n) dμ`, and the third-order Taylor bound
`|exp (i y) - (1 + i y - y ^ 2 / 2)| ≤ |y| ^ 3` for `|y| ≤ 1` gives
`n (φ_n(s) - 1) → - s ^ 2 v / 2`.

## Main statements

* `ProbabilityTheory.norm_cexp_mul_I_sub_le`: the third-order Taylor bound for `exp (i y)`.
* `ProbabilityTheory.tendsto_charFun_sum_range_of_bounded`: convergence of the characteristic
  functions of the row sums.
* `ProbabilityTheory.tendstoInDistribution_sum_range_of_bounded`: the row sums converge in
  distribution to `gaussianReal 0 v`.

## References

* [P. Billingsley, *Probability and Measure*][billingsley1995], Theorem 27.2.
-/

@[expose] public section

open MeasureTheory Filter Finset Topology Complex
open scoped ENNReal NNReal Real

namespace ProbabilityTheory

/-- Third-order Taylor bound for `exp (i y)`: `‖exp (i y) - (1 + i y - y ^ 2 / 2)‖ ≤ |y| ^ 3`
for `|y| ≤ 1`. -/
lemma norm_cexp_mul_I_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp (y * I) - (1 + y * I - (y : ℂ) ^ 2 / 2)‖ ≤ |y| ^ 3 := by
  have hn : ‖(y : ℂ) * I‖ = |y| := by simp
  have h := Complex.exp_bound (x := (y : ℂ) * I) (by rw [hn]; exact hy) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ range 3, ((y : ℂ) * I) ^ m / (m.factorial : ℂ) =
      1 + y * I - (y : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [mul_pow, Complex.I_sq, Nat.factorial]
    ring
  rw [hsum, hn] at h
  refine h.trans ?_
  have : (0 : ℝ) ≤ |y| ^ 3 := by positivity
  norm_num [Nat.factorial]
  nlinarith

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {P : Measure Ω} {μ : Measure α}

/-- The characteristic function of a row sum of i.i.d. summands is a power. -/
lemma charFun_map_sum_range_eq_pow {U : ℕ → Ω → α} (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = μ) {g : α → ℝ} (hg : Measurable g)
    (n : ℕ) (s : ℝ) :
    charFun (P.map (fun ω ↦ ∑ i ∈ range n, g (U i ω))) s = (charFun (μ.map g) s) ^ n := by
  have hind' : iIndepFun (fun i ω ↦ g (U i ω)) P := hind.comp (fun _ ↦ g) (fun _ ↦ hg)
  have := (hind'.restrict (range n)).charFun_map_fun_finsetSum_eq_prod
    (X := fun i ω ↦ g (U i ω)) (fun i _ ↦ (hg.comp (hU i)).aemeasurable)
  rw [this]
  have h (i : ℕ) : P.map (fun ω ↦ g (U i ω)) = μ.map g := by
    rw [← hlaw i, Measure.map_map hg (hU i)]
    rfl
  simp [h]

variable [IsProbabilityMeasure μ]

/-- **Central limit theorem for triangular arrays with uniformly small summands**
(characteristic functions). -/
theorem tendsto_charFun_sum_range_of_bounded {U : ℕ → Ω → α} (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = μ) {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n)) {M : ℕ → ℝ} (hM : Tendsto M atTop (𝓝 0))
    (hfM : ∀ n x, |f n x| ≤ M n) (hmean : ∀ᶠ n in atTop, ∫ x, f n x ∂μ = 0) {v : ℝ}
    (hvar : Tendsto (fun n : ℕ ↦ n * ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 v)) (s : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (fun ω ↦ ∑ i ∈ range n, f n (U i ω))) s) atTop
      (𝓝 (cexp (-((s : ℂ) ^ 2 * v / 2)))) := by
  simp_rw [charFun_map_sum_range_eq_pow hU hind hlaw (hf _)]
  -- integrability of the bounded functions involved
  have hintC (n : ℕ) {h : ℝ → ℂ} (hh : Continuous h) : Integrable (fun x ↦ h (f n x)) μ := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -|M n|) (b := |M n|)).exists_bound_of_continuousOn
      hh.continuousOn
    refine Integrable.of_bound (C := C) (hh.measurable.comp (hf n)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ hC _ ?_)
    exact abs_le.1 ((hfM n x).trans (le_abs_self _))
  have hintR (n : ℕ) {h : ℝ → ℝ} (hh : Continuous h) : Integrable (fun x ↦ h (f n x)) μ := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -|M n|) (b := |M n|)).exists_bound_of_continuousOn
      hh.continuousOn
    refine Integrable.of_bound (C := C) (hh.measurable.comp (hf n)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ hC _ ?_)
    exact abs_le.1 ((hfM n x).trans (le_abs_self _))
  set R : ℕ → ℂ := fun n ↦ ∫ x, (cexp (s * f n x * I) - (1 + s * f n x * I -
    ((s : ℂ) * f n x) ^ 2 / 2)) ∂μ with hR
  have hpoly (n : ℕ) : ∫ x, (1 + (s : ℂ) * f n x * I - ((s : ℂ) * f n x) ^ 2 / 2) ∂μ =
      1 + (s : ℂ) * I * ((∫ x, f n x ∂μ : ℝ) : ℂ) -
        (s : ℂ) ^ 2 / 2 * ((∫ x, f n x ^ 2 ∂μ : ℝ) : ℂ) := by
    have e : (fun x ↦ 1 + (s : ℂ) * f n x * I - ((s : ℂ) * f n x) ^ 2 / 2) =
        fun x ↦ (((1 - s ^ 2 / 2 * f n x ^ 2 : ℝ)) : ℂ) + (((s * f n x : ℝ)) : ℂ) * I := by
      ext x; push_cast; ring
    have i1 := hintC n (h := fun y ↦ (((1 - s ^ 2 / 2 * y ^ 2 : ℝ)) : ℂ)) (by fun_prop)
    have i2 := hintC n (h := fun y ↦ (((s * y : ℝ)) : ℂ) * I) (by fun_prop)
    have i3 := hintR n (h := fun y ↦ s ^ 2 / 2 * y ^ 2) (by fun_prop)
    beta_reduce at i1 i2 i3
    rw [e, integral_add i1 i2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_sub (integrable_const _) i3, integral_const_mul, integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    push_cast
    ring
  have hchar (n : ℕ) : charFun (μ.map (f n)) s =
      1 + (R n + (s : ℂ) * I * ((∫ x, f n x ∂μ : ℝ) : ℂ) -
        (s : ℂ) ^ 2 / 2 * ((∫ x, f n x ^ 2 ∂μ : ℝ) : ℂ)) := by
    rw [charFun_apply_real, integral_map (hf n).aemeasurable (by fun_prop), hR]
    dsimp only
    have i1 := hintC n (h := fun y ↦ cexp (s * y * I)) (by fun_prop)
    have i2 := hintC n (h := fun y ↦ 1 + (s : ℂ) * y * I - ((s : ℂ) * y) ^ 2 / 2) (by fun_prop)
    beta_reduce at i1 i2
    rw [integral_sub i1 i2, hpoly]
    ring
  -- the remainder is negligible
  have hRlim : Tendsto (fun n : ℕ ↦ (n : ℂ) * R n) atTop (𝓝 0) := by
    have hM' : ∀ᶠ n in atTop, |s| * |M n| ≤ 1 := by
      have : Tendsto (fun n ↦ |s| * |M n|) atTop (𝓝 (|s| * |0|)) :=
        (hM.abs).const_mul _
      simp only [abs_zero, mul_zero] at this
      exact this.eventually (ge_mem_nhds zero_lt_one)
    have hbound : ∀ᶠ n : ℕ in atTop,
        ‖(n : ℂ) * R n‖ ≤ |s| ^ 3 * |M n| * (n * ∫ x, f n x ^ 2 ∂μ) := by
      filter_upwards [hM'] with n hn
      rw [norm_mul, Complex.norm_natCast]
      have hRn : ‖R n‖ ≤ ∫ x, |s| ^ 3 * |M n| * f n x ^ 2 ∂μ := by
        refine norm_integral_le_of_norm_le ((hintR n (h := fun y ↦ y ^ 2)
          (by fun_prop)).const_mul _) (ae_of_all _ fun x ↦ ?_)
        have hfx : |f n x| ≤ |M n| := (hfM n x).trans (le_abs_self _)
        have hy : |s * f n x| ≤ 1 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left hfx (abs_nonneg _)).trans hn
        have h3 := norm_cexp_mul_I_sub_le hy
        push_cast at h3
        refine h3.trans ?_
        rw [abs_mul, mul_pow, show |f n x| ^ 3 = |f n x| * f n x ^ 2 by
          rw [pow_succ', ← sq_abs (f n x)]]
        have : |s| ^ 3 * (|f n x| * f n x ^ 2) ≤ |s| ^ 3 * (|M n| * f n x ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfx (sq_nonneg _))
            (by positivity)
        linarith
      rw [integral_const_mul] at hRn
      calc (n : ℝ) * ‖R n‖ ≤ n * (|s| ^ 3 * |M n| * ∫ x, f n x ^ 2 ∂μ) :=
            mul_le_mul_of_nonneg_left hRn (Nat.cast_nonneg _)
        _ = _ := by ring
    have hlim : Tendsto (fun n : ℕ ↦ |s| ^ 3 * |M n| * (n * ∫ x, f n x ^ 2 ∂μ)) atTop
        (𝓝 (|s| ^ 3 * |0| * v)) := ((hM.abs).const_mul _).mul hvar
    simp only [abs_zero, mul_zero, zero_mul] at hlim
    exact squeeze_zero_norm' hbound hlim
  have hvarC : Tendsto (fun n : ℕ ↦ (((n : ℝ) * ∫ x, f n x ^ 2 ∂μ : ℝ) : ℂ)) atTop (𝓝 (v : ℂ)) :=
    (continuous_ofReal.tendsto v).comp hvar
  have hmain : Tendsto (fun n : ℕ ↦ (n : ℂ) * R n -
      (s : ℂ) ^ 2 / 2 * (((n : ℝ) * ∫ x, f n x ^ 2 ∂μ : ℝ) : ℂ)) atTop
      (𝓝 (0 - (s : ℂ) ^ 2 / 2 * (v : ℂ))) :=
    hRlim.sub (hvarC.const_mul _)
  have hlim2 : Tendsto (fun n : ℕ ↦ (n : ℂ) * (R n + (s : ℂ) * I * ((∫ x, f n x ∂μ : ℝ) : ℂ) -
      (s : ℂ) ^ 2 / 2 * ((∫ x, f n x ^ 2 ∂μ : ℝ) : ℂ))) atTop (𝓝 (-((s : ℂ) ^ 2 * v / 2))) := by
    have e : -((s : ℂ) ^ 2 * v / 2) = 0 - (s : ℂ) ^ 2 / 2 * v := by ring
    rw [e]
    refine hmain.congr' ?_
    filter_upwards [hmean] with n hn
    rw [hn]
    push_cast
    ring
  exact (tendsto_one_add_pow_exp_of_tendsto hlim2).congr fun n ↦ by rw [hchar n]

/-- **Central limit theorem for triangular arrays with uniformly small summands**: if
`U 0, U 1, …` are i.i.d. with law `μ`, the `f n` are centered under `μ`, `|f n| ≤ M n → 0` and
`n ∫ (f n) ^ 2 dμ → v`, then `∑_{i < n} f n (U i)` converges in distribution to
`gaussianReal 0 v`. -/
theorem tendstoInDistribution_sum_range_of_bounded [IsProbabilityMeasure P] {U : ℕ → Ω → α}
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = μ)
    {f : ℕ → α → ℝ} (hf : ∀ n, Measurable (f n)) {M : ℕ → ℝ} (hM : Tendsto M atTop (𝓝 0))
    (hfM : ∀ n x, |f n x| ≤ M n) (hmean : ∀ᶠ n in atTop, ∫ x, f n x ∂μ = 0) {v : ℝ≥0}
    (hvar : Tendsto (fun n : ℕ ↦ n * ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 v)) :
    TendstoInDistribution (fun n ω ↦ ∑ i ∈ range n, f n (U i ω)) atTop id (fun _ ↦ P)
      (gaussianReal 0 v) := by
  refine .of_tendsto_charFun (fun n ↦ (Finset.measurable_sum _ fun i _ ↦
    (hf n).comp (hU i)).aemeasurable) aemeasurable_id fun s ↦ ?_
  rw [Measure.map_id, charFun_gaussianReal]
  convert tendsto_charFun_sum_range_of_bounded hU hind hlaw hf hM hfM hmean hvar s using 2
  simp only [ofReal_zero, mul_zero, zero_mul, zero_sub]
  ring_nf

end ProbabilityTheory
