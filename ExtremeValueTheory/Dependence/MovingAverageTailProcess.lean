/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MovingAverage
import ExtremeValueTheory.HeavyTails.LinearProcess

/-!
# The tail process of a finite moving average with nonnegative coefficients

Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative random variables with `P(Z_0 > x)` regularly varying with
index `-α`, `α > 0` (for instance Pareto), and let `ψ_0, …, ψ_m ≥ 0` be coefficients, not all
zero. The moving average `X_t = ∑_{i=0}^m ψ_i Z_{t-i}` has spectral tail process
`Θ_t = ψ_{J+t} / ψ_J` with `P(J = j) = ψ_j^α / ∑_i ψ_i^α` ([DR85], [KS20, §15.3],
[Meinguet–Segers 2010]); see `MovingAverage.spectral`, `MovingAverage.indexLaw`.

## Main results

* `MovingAverage.tendsto_measureReal_process_div`: `P(X_0 > x) / P(Z_0 > x) → ∑_j ψ_j^α`.
* `MovingAverage.hasSpectralTailProcess`: `HasSpectralTailProcess P X α (indexLaw m ψ α)
  (spectral m ψ)`.
* `MovingAverage.candidateExtremalIndex_eq`: hence the candidate extremal index of the moving
  average is `max_j ψ_j^α / ∑_j ψ_j^α`.

## Proof

Fix a window `S`, the finite set `I` of noise indices entering `X_t`, `t ∈ S ∪ {0}`, and a small
`η > 0`. Given `X_0 > x`, either two of the `Z_i`, `i ∈ I`, exceed `ηx` (probability
`O(P(Z > ηx)²) = o(P(X_0 > x))`), or exactly one does, namely `Z_{-j}` with `ψ_j > 0` (event
`G_j`). On `G_j ∩ {X_0 > x}`, `X_t / X_0` is within `O(η)` of `ψ_{j+t} / ψ_j`, and
`P(G_j ∩ {X_0 > x}) / P(X_0 > x)` lies asymptotically between `ψ_j^α / ∑ ψ^α` and
`(1 - η∑ψ)^{-α} ψ_j^α / ∑ ψ^α`, by independence and regular variation. Letting `η → 0` gives the
convergence of the conditional laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal

namespace ExtremeValueTheory

namespace MovingAverage

variable {m : ℕ} {ψ : ℕ → ℝ}

/-! ### Deterministic decomposition -/

section Deterministic

theorem sum_ite_coef (hψm : ∀ j, m < j → ψ j = 0) (j : ℕ) (t : ℤ) :
    ∑ i ∈ range (m + 1), (if t - i = -(j : ℤ) then ψ i else 0) = coef ψ (j + t) := by
  by_cases h : 0 ≤ (j : ℤ) + t
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
    have hiff : ∀ i : ℕ, (t - i = -(j : ℤ)) ↔ (k = i) := by intro i; omega
    simp_rw [hiff, Finset.sum_ite_eq, hk, coef_natCast]
    split_ifs with hkm
    · rfl
    · rw [hψm k (by simp only [Finset.mem_range] at hkm; omega)]
  · have hne : ∀ i : ℕ, ¬ (t - i = -(j : ℤ)) := by intro i; omega
    simp [hne, coef, h]

/-- Splitting off the contribution of `z_{-j}` to `∑_i ψ_i z_{t-i}`. -/
theorem sum_eq_coef_mul_add (hψm : ∀ j, m < j → ψ j = 0) (z : ℤ → ℝ) (j : ℕ) (t : ℤ) :
    ∑ i ∈ range (m + 1), ψ i * z (t - i) = coef ψ (j + t) * z (-(j : ℤ)) +
      ∑ i ∈ range (m + 1), (if t - i = -(j : ℤ) then 0 else ψ i * z (t - i)) := by
  rw [← sum_ite_coef hψm j t, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [h, add_zero]
  · rw [zero_mul, zero_add]

theorem rem_nonneg (hψ0 : ∀ j, 0 ≤ ψ j) {z : ℤ → ℝ} (j : ℕ) (t : ℤ)
    (hz : ∀ i ∈ range (m + 1), t - i ≠ -(j : ℤ) → 0 ≤ z (t - i)) :
    0 ≤ ∑ i ∈ range (m + 1), (if t - i = -(j : ℤ) then 0 else ψ i * z (t - i)) := by
  refine Finset.sum_nonneg fun i hi => ?_
  split_ifs with h
  · exact le_rfl
  · exact mul_nonneg (hψ0 i) (hz i hi h)

theorem rem_le (hψ0 : ∀ j, 0 ≤ ψ j) {z : ℤ → ℝ} {b : ℝ} (hb : 0 ≤ b) (j : ℕ) (t : ℤ)
    (hz : ∀ i ∈ range (m + 1), t - i ≠ -(j : ℤ) → z (t - i) ≤ b) :
    ∑ i ∈ range (m + 1), (if t - i = -(j : ℤ) then 0 else ψ i * z (t - i)) ≤
      b * ∑ i ∈ range (m + 1), ψ i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  split_ifs with h
  · exact mul_nonneg hb (hψ0 i)
  · rw [mul_comm b]; exact mul_le_mul_of_nonneg_left (hz i hi h) (hψ0 i)

/-- **Coverage**: if `∑_i ψ_i z_{-i} > x ≥ b ∑ ψ`, then either exactly one relevant coordinate
`z_{-j}` with `ψ_j > 0` exceeds `b` (all other coordinates of `I` being `≤ b`), or two coordinates
of `I` exceed `b`. -/
theorem coverage (hψ0 : ∀ j, 0 ≤ ψ j) {I : Finset ℤ} (hI : ∀ j ∈ range (m + 1), -(j : ℤ) ∈ I)
    {z : ℤ → ℝ} {b x : ℝ} (hb : b * ∑ i ∈ range (m + 1), ψ i ≤ x)
    (hx : x < ∑ i ∈ range (m + 1), ψ i * z (-(i : ℤ))) :
    (∃ j ∈ range (m + 1), 0 < ψ j ∧ b < z (-(j : ℤ)) ∧ ∀ i ∈ I, i ≠ -(j : ℤ) → z i ≤ b) ∨
      (∃ i ∈ I, ∃ i' ∈ I, i ≠ i' ∧ b < z i ∧ b < z i') := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hle : ∀ j ∈ range (m + 1), ψ j * z (-(j : ℤ)) ≤ b * ψ j := by
    intro j hj
    rcases (hψ0 j).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    by_cases hzj : z (-(j : ℤ)) ≤ b
    · rw [mul_comm b]; exact mul_le_mul_of_nonneg_left hzj (hψ0 j)
    · push Not at hzj
      obtain ⟨i, hi, hij, hzi⟩ := h1 j hj hpos hzj
      exact absurd (h2 i hi _ (hI j hj) hij hzi) (not_le.2 hzj)
  have := Finset.sum_le_sum hle
  rw [← Finset.mul_sum] at this
  linarith

/-- **Approximation of the ratios**: if `z_{-j}` is the only coordinate exceeding `b` among those
entering `X_0` and `X_t`, and `X_0 > x > 0`, then
`|X_t / X_0 - ψ_{j+t} / ψ_j| ≤ b ∑ψ (ψ_j + ψ_{j+t}) / (ψ_j x)`. -/
theorem abs_div_sub_le (hψ0 : ∀ j, 0 ≤ ψ j) (hψm : ∀ j, m < j → ψ j = 0) {z : ℤ → ℝ}
    {b x : ℝ} (hb : 0 ≤ b) (hx : 0 < x) {j : ℕ} (hj : 0 < ψ j) (t : ℤ)
    (hz : ∀ s ∈ ({0, t} : Finset ℤ), ∀ i ∈ range (m + 1), s - i ≠ -(j : ℤ) →
      0 ≤ z (s - i) ∧ z (s - i) ≤ b)
    (hX : x < ∑ i ∈ range (m + 1), ψ i * z (0 - i)) :
    |(∑ i ∈ range (m + 1), ψ i * z (t - i)) / (∑ i ∈ range (m + 1), ψ i * z (0 - i)) -
        coef ψ (j + t) / ψ j| ≤
      b * (∑ i ∈ range (m + 1), ψ i) * (ψ j + coef ψ (j + t)) / (ψ j * x) := by
  set σ := ∑ i ∈ range (m + 1), ψ i
  set c := coef ψ (j + t)
  have hc : 0 ≤ c := by
    simp only [c, coef]; split_ifs
    · exact hψ0 _
    · exact le_rfl
  have h0 := sum_eq_coef_mul_add hψm z j 0
  have ht := sum_eq_coef_mul_add hψm z j t
  rw [add_zero, coef_natCast] at h0
  set R0 := ∑ i ∈ range (m + 1), (if (0 : ℤ) - i = -(j : ℤ) then 0 else ψ i * z (0 - i))
  set Rt := ∑ i ∈ range (m + 1), (if t - i = -(j : ℤ) then 0 else ψ i * z (t - i))
  have hR0 : 0 ≤ R0 ∧ R0 ≤ b * σ :=
    ⟨rem_nonneg hψ0 j 0 fun i hi h => (hz 0 (by simp) i hi h).1,
      rem_le hψ0 hb j 0 fun i hi h => (hz 0 (by simp) i hi h).2⟩
  have hRt : 0 ≤ Rt ∧ Rt ≤ b * σ :=
    ⟨rem_nonneg hψ0 j t fun i hi h => (hz t (by simp) i hi h).1,
      rem_le hψ0 hb j t fun i hi h => (hz t (by simp) i hi h).2⟩
  set X0 := ∑ i ∈ range (m + 1), ψ i * z (0 - i)
  set Xt := ∑ i ∈ range (m + 1), ψ i * z (t - i)
  have hX0 : 0 < X0 := hx.trans hX
  have key : Xt / X0 - c / ψ j = (ψ j * Rt - c * R0) / (ψ j * X0) := by
    rw [div_sub_div _ _ hX0.ne' hj.ne', ht, h0]
    congr 1
    · ring
    · ring
  rw [key, abs_div, abs_of_pos (mul_pos hj hX0)]
  have hnum : |ψ j * Rt - c * R0| ≤ b * σ * (ψ j + c) := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hR0.2 hc, mul_nonneg hj.le hRt.1]
    · nlinarith [mul_le_mul_of_nonneg_left hRt.2 hj.le, mul_nonneg hc hR0.1]
  have hσ : 0 ≤ b * σ * (ψ j + c) := by
    have : 0 ≤ σ := Finset.sum_nonneg fun i _ => hψ0 i
    positivity
  calc |ψ j * Rt - c * R0| / (ψ j * X0) ≤ b * σ * (ψ j + c) / (ψ j * X0) :=
        div_le_div_of_nonneg_right hnum (mul_pos hj hX0).le
    _ ≤ b * σ * (ψ j + c) / (ψ j * x) :=
        div_le_div_of_nonneg_left hσ (mul_pos hj hx) (mul_le_mul_of_nonneg_left hX.le hj.le)

end Deterministic

end MovingAverage

end ExtremeValueTheory
