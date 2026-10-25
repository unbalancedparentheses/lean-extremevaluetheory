/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.InfiniteMovingAverageTailProcess

/-!
# The extremal index of the AR(1) process

For `0 < φ < 1` and iid nonnegative noise `(Z_t)_{t ∈ ℤ}` with `P(Z_0 > x)` regularly varying with
index `-α`, **any `α > 0`**, the stationary AR(1) process `X_t = φ X_{t-1} + Z_t` is the infinite
moving average `X_t = ∑_{j ≥ 0} φ^j Z_{t-j}`. Its extremal index is

  `θ = 1 - φ^α`

([EKM, §8.1], [Chernick 1981], [KS20, Chapter 15]), the case `ψ_j = φ^j` of
`InfiniteMovingAverage.hasExtremalIndex_of_summable_rpow`: `sup_j φ^{jα} = 1` and
`∑_j φ^{jα} = 1 / (1 - φ^α)`. The geometric coefficients satisfy `∑_j φ^{jδ} < ∞` for every
`δ > 0`, in particular for `δ = min(α, 1) / 2 < min(α, 1)`. No moment or centering assumption on
the noise is needed (the noise is nonnegative, and the series converges absolutely).

## Main results

* `AR1.process_eq`: the series `∑_j φ^j Z_{t-j}` satisfies the AR(1) recursion wherever the series
  at time `t - 1` converges; `AR1.ae_process_eq_of_pos`: almost surely, for all `t`.
* `AR1.hasExtremalIndex_of_pos`: `θ = 1 - φ^α` for all `α > 0`.
* `AR1.hasSpectralTailProcess_of_pos`: the spectral tail process is `Θ_t = φ^t` for `t ≥ -J`
  (`Θ_t = ψ_{J+t} / ψ_J`, `P(J = j) = (1 - φ^α) φ^{jα}`).
* `AR1.ae_process_eq`, `AR1.hasExtremalIndex`: the special case `α < 1`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace ExtremeValueTheory

namespace AR1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z : ℤ → Ω → ℝ} {φ α : ℝ}

/-- The AR(1) process `X_t = ∑_{j ≥ 0} φ^j Z_{t-j}`. -/
noncomputable abbrev process (φ : ℝ) (Z : ℤ → Ω → ℝ) : ℤ → Ω → ℝ :=
  InfiniteMovingAverage.process (fun j => φ ^ j) Z

/-- **The AR(1) recursion** `X_t = φ X_{t-1} + Z_t`, wherever the series defining `X_{t-1}`
converges. -/
theorem process_eq {t : ℤ} {ω : Ω} (h : Summable fun j : ℕ => φ ^ j * Z (t - 1 - j) ω) :
    process φ Z t ω = φ * process φ Z (t - 1) ω + Z t ω := by
  have hs : Summable fun j : ℕ => φ ^ (j + 1) * Z (t - ((j + 1 : ℕ) : ℤ)) ω := by
    refine (h.mul_left φ).congr fun j => ?_
    rw [pow_succ, show t - ((j + 1 : ℕ) : ℤ) = t - 1 - j by push_cast; ring]
    ring
  have hs' : Summable fun j : ℕ => φ ^ j * Z (t - j) ω := (summable_nat_add_iff 1).1 hs
  simp only [process, InfiniteMovingAverage.process]
  rw [hs'.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  rw [add_comm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t - ((j + 1 : ℕ) : ℤ) = t - 1 - j by push_cast; ring]
  ring

theorem rpow_pow_eq (hφ0 : 0 < φ) (δ : ℝ) (j : ℕ) : (φ ^ j) ^ δ = (φ ^ δ) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hφ0.le, mul_comm, Real.rpow_mul hφ0.le,
    Real.rpow_natCast]

theorem summable_rpow (hφ0 : 0 < φ) (hφ1 : φ < 1) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j : ℕ => (φ ^ j) ^ δ := by
  simp only [rpow_pow_eq hφ0]
  exact summable_geometric_of_lt_one (Real.rpow_nonneg hφ0.le _)
    (Real.rpow_lt_one hφ0.le hφ1 hδ)

/-- The exponent `δ = min(α, 1) / 2` used for the summability of the AR(1) coefficients. -/
theorem half_min_bounds (hα : 0 < α) :
    0 < min α 1 / 2 ∧ min α 1 / 2 < α ∧ min α 1 / 2 < 1 := by
  have h0 : 0 < min α 1 := lt_min hα one_pos
  refine ⟨by positivity, ?_, ?_⟩
  · linarith [min_le_left α 1]
  · linarith [min_le_right α 1]

variable [IsProbabilityMeasure P]

/-- **The AR(1) recursion holds almost surely, all `α > 0`**: for identically distributed
nonnegative noise (independence is not needed) with `P(Z_0 > x)` regularly varying with index
`-α`, `α > 0`, and `0 < φ < 1`, almost surely `X_t = φ X_{t-1} + Z_t` for all `t ∈ ℤ`. -/
theorem ae_process_eq_of_pos (hZ : ∀ i, Measurable (Z i))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hφ0 : 0 < φ)
    (hφ1 : φ < 1) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, process φ Z t ω = φ * process φ Z (t - 1) ω + Z t ω := by
  obtain ⟨hδ, hδα, hδ1⟩ := half_min_bounds hα
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [InfiniteMovingAverage.setOf_lt_abs_eq hZ0] using hL
  rw [ae_all_iff]
  intro t
  have h := LinearProcess.ae_summable_mul_of_summable_rpow (Z := fun j : ℕ => Z (t - 1 - j))
    (fun j => hZ _) (hZ 0) (fun j => hident _) hδ hδα hδ1 hL' (ψ := fun j => φ ^ j)
    (by simpa only [abs_of_nonneg (pow_nonneg hφ0.le _)] using summable_rpow hφ0 hφ1 hδ)
  filter_upwards [h] with ω hω
  exact process_eq hω

/-- **The extremal index of the AR(1) process, all `α > 0`** ([EKM, §8.1], [Chernick 1981],
[KS20, Chapter 15]): for `0 < φ < 1` and iid nonnegative noise with `P(Z_0 > x)` regularly
varying with index `-α`, `α > 0`, the process `X_t = ∑_{j ≥ 0} φ^j Z_{t-j}` (the stationary
solution of `X_t = φ X_{t-1} + Z_t`, `ae_process_eq_of_pos`) has extremal index `1 - φ^α`. -/
theorem hasExtremalIndex_of_pos (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    HasExtremalIndex (fun n : ℕ => process φ Z n) P (1 - φ ^ α) := by
  obtain ⟨hδ, hδα, hδ1⟩ := half_min_bounds hα
  have h := InfiniteMovingAverage.hasExtremalIndex_of_summable_rpow (ψ := fun j => φ ^ j) hZ hind hident
    hZ0 hδ hδα hδ1 hL (fun j => pow_nonneg hφ0.le j) (summable_rpow hφ0 hφ1 hδ) ⟨0, by simp⟩
  have hsup : (⨆ j : ℕ, φ ^ j) = 1 := by
    refine le_antisymm (ciSup_le fun j => pow_le_one₀ hφ0.le hφ1.le) ?_
    exact (pow_zero φ).symm.le.trans
      (le_ciSup (f := fun j : ℕ => φ ^ j) ⟨1, by
        rintro _ ⟨j, rfl⟩; exact pow_le_one₀ hφ0.le hφ1.le⟩ 0)
  have hφα : φ ^ α < 1 := Real.rpow_lt_one hφ0.le hφ1 hα
  have hsum : ∑' j : ℕ, (φ ^ j) ^ α = (1 - φ ^ α)⁻¹ := by
    simp only [rpow_pow_eq hφ0]
    exact tsum_geometric_of_lt_one (Real.rpow_nonneg hφ0.le _) hφα
  rw [hsup, hsum, Real.one_rpow, one_div, inv_inv] at h
  exact h

/-- **The spectral tail process of the AR(1) process, all `α > 0`** ([KS20, §15.3]): under the
hypotheses of `hasExtremalIndex_of_pos`, `X` has spectral tail process `Θ_t = φ^{J+t} / φ^J`
(for `J + t ≥ 0`, else `0`), `P(J = j) = φ^{jα} / ∑_i φ^{iα}`. -/
theorem hasSpectralTailProcess_of_pos (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    HasSpectralTailProcess P (process φ Z) α
      (InfiniteMovingAverage.indexLaw (fun j => φ ^ j) α)
      (InfiniteMovingAverage.spectral fun j => φ ^ j) := by
  obtain ⟨hδ, hδα, hδ1⟩ := half_min_bounds hα
  exact InfiniteMovingAverage.hasSpectralTailProcess_of_summable_rpow (ψ := fun j => φ ^ j) hZ hind
    hident hZ0 hδ hδα hδ1 hL (fun j => pow_nonneg hφ0.le j) (summable_rpow hφ0 hφ1 hδ) ⟨0, by simp⟩

/-- **The AR(1) recursion holds almost surely**: under the hypotheses of the extremal index
theorem, almost surely `X_t = φ X_{t-1} + Z_t` for all `t ∈ ℤ`. A special case of
`ae_process_eq_of_pos`. -/
theorem ae_process_eq (hZ : ∀ i, Measurable (Z i)) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (hZ0 : ∀ i ω, 0 ≤ Z i ω) {δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) (_hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hφ0 : 0 < φ)
    (hφ1 : φ < 1) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, process φ Z t ω = φ * process φ Z (t - 1) ω + Z t ω :=
  ae_process_eq_of_pos hZ hident hZ0 (hδ.trans hδα) hL hφ0 hφ1

/-- **The extremal index of the AR(1) process** ([EKM, §8.1], [Chernick 1981], [KS20, Chapter
15]): for `0 < φ < 1` and iid nonnegative noise with `P(Z_0 > x)` regularly varying with index
`-α`, `0 < α < 1`, the process `X_t = ∑_{j ≥ 0} φ^j Z_{t-j}` (the stationary solution of
`X_t = φ X_{t-1} + Z_t`, `ae_process_eq`) has extremal index `1 - φ^α`. The case `α < 1` of
`hasExtremalIndex_of_pos`. -/
theorem hasExtremalIndex (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (_hα1 : α < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    HasExtremalIndex (fun n : ℕ => process φ Z n) P (1 - φ ^ α) :=
  hasExtremalIndex_of_pos hZ hind hident hZ0 hα hL hφ0 hφ1

end AR1

end ExtremeValueTheory
