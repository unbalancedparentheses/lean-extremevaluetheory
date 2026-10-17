/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TailProcess

/-!
# The spectral tail process of a finite moving average

Let `X_t = ∑_{j=0}^m ψ_j Z_{t-j}` be a moving average of order `m` with nonnegative coefficients
`ψ_j ≥ 0` (not all zero) and iid nonnegative noise with regularly varying tail of index `-α`. Its
spectral tail process is ([DR85], [KS20, Example 5.2.10 and §15.3], [Meinguet–Segers 2010])

  `Θ_t = ψ_{J+t} / ψ_J`,

where `J ∈ {0, …, m}` is a random index with `P(J = j) = ψ_j^α / ∑_i ψ_i^α`: given a large value
of `X_0`, one noise variable `Z_{-J}` is large ("single big jump"), and `J = j` with probability
proportional to the tail weight `ψ_j^α` of `ψ_j Z_{-j}`.

Here we define this candidate spectral tail process and compute its candidate extremal index

  `ϑ = max_j ψ_j^α / ∑_j ψ_j^α`,

the classical extremal index of the moving average ([EKM, §8.1], [DR85], [Leadbetter, Lindgren,
Rootzén, §3.8]). The identification of `Θ` as the spectral tail process of `X`, i.e.
`HasSpectralTailProcess P X α Q Θ`, is `MovingAverage.hasSpectralTailProcess` in
`Dependence/MovingAverageTailProcess.lean`.

## Main definitions

* `MovingAverage.coef ψ k`: the coefficient `ψ_k` for `k ∈ ℤ`, zero for `k < 0`.
* `MovingAverage.weightSum m ψ α = ∑_{j ≤ m} ψ_j^α`.
* `MovingAverage.indexLaw m ψ α`: the law of `J` on `Fin (m + 1)`.
* `MovingAverage.spectral m ψ t j = ψ_{j + t} / ψ_j`.

## Main results

* `MovingAverage.candidateExtremalIndex_spectral`: `ϑ = max_j ψ_j^α / ∑_j ψ_j^α`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal

namespace ExtremeValueTheory

namespace MovingAverage

/-- The coefficient `ψ_k` for `k ∈ ℤ`, zero for negative `k`. -/
noncomputable def coef (ψ : ℕ → ℝ) (k : ℤ) : ℝ := if 0 ≤ k then ψ k.toNat else 0

@[simp] theorem coef_natCast (ψ : ℕ → ℝ) (n : ℕ) : coef ψ n = ψ n := by simp [coef]

/-- `∑_{j ≤ m} ψ_j^α`. -/
noncomputable def weightSum (m : ℕ) (ψ : ℕ → ℝ) (α : ℝ) : ℝ :=
  ∑ j ∈ range (m + 1), ψ j ^ α

/-- The law of the index `J` of the big jump: `P(J = j) = ψ_j^α / ∑_i ψ_i^α`. -/
noncomputable def indexLaw (m : ℕ) (ψ : ℕ → ℝ) (α : ℝ) : Measure (Fin (m + 1)) :=
  ∑ j : Fin (m + 1), ENNReal.ofReal (ψ j ^ α / weightSum m ψ α) • Measure.dirac j

/-- The spectral tail process `Θ_t = ψ_{J + t} / ψ_J` of the moving average, on the index
space `Fin (m + 1)` of `J`. -/
noncomputable def spectral (m : ℕ) (ψ : ℕ → ℝ) (t : ℤ) (j : Fin (m + 1)) : ℝ :=
  coef ψ ((j : ℕ) + t) / ψ j

variable {m : ℕ} {ψ : ℕ → ℝ} {α : ℝ}

theorem indexLaw_isProbabilityMeasure (hψ0 : ∀ j, 0 ≤ ψ j) (hS : 0 < weightSum m ψ α) :
    IsProbabilityMeasure (indexLaw m ψ α) := by
  constructor
  simp only [indexLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (Real.rpow_nonneg (hψ0 _) _) hS.le,
    ← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun j => ψ j ^ α), ← weightSum,
    div_self hS.ne', ENNReal.ofReal_one]

/-- The running maximum `M_n = max_{k ≥ n} ψ_k` (the coefficients vanish beyond `m`). -/
noncomputable def runMax (m : ℕ) (ψ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (range (m + 1)).sup' nonempty_range_add_one fun k => ψ (n + k)

theorem exists_runMax_eq (n : ℕ) : ∃ k, runMax m ψ n = ψ (n + k) := by
  obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' nonempty_range_add_one fun k => ψ (n + k)
  exact ⟨k, hk⟩

section runMax

variable (hψ0 : ∀ j, 0 ≤ ψ j) (hψm : ∀ j, m < j → ψ j = 0)
include hψ0 hψm

theorem le_runMax (n k : ℕ) : ψ (n + k) ≤ runMax m ψ n := by
  by_cases hk : k ≤ m
  · exact le_sup' (fun k => ψ (n + k)) (mem_range.2 (by omega))
  · rw [hψm _ (by omega)]
    exact (hψ0 (n + 0)).trans (le_sup' (fun k => ψ (n + k)) (mem_range.2 (by omega)))

theorem runMax_nonneg (n : ℕ) : 0 ≤ runMax m ψ n :=
  (hψ0 (n + 0)).trans (le_runMax hψ0 hψm n 0)

theorem runMax_succ_le (n : ℕ) : runMax m ψ (n + 1) ≤ runMax m ψ n := by
  obtain ⟨k, hk⟩ := exists_runMax_eq (m := m) (ψ := ψ) (n + 1)
  rw [hk, show n + 1 + k = n + (k + 1) by ring]
  exact le_runMax hψ0 hψm n _

theorem runMax_eq_of_eq_zero {n : ℕ} (hn : ψ n = 0) : runMax m ψ n = runMax m ψ (n + 1) := by
  refine le_antisymm ?_ (runMax_succ_le hψ0 hψm n)
  obtain ⟨k, hk⟩ := exists_runMax_eq (m := m) (ψ := ψ) n
  rw [hk]
  rcases k with _ | k
  · rw [add_zero, hn]; exact runMax_nonneg hψ0 hψm _
  · rw [show n + (k + 1) = n + 1 + k by ring]; exact le_runMax hψ0 hψm _ _

omit hψ0 in
theorem runMax_eq_zero : runMax m ψ (m + 1) = 0 := by
  obtain ⟨k, hk⟩ := exists_runMax_eq (m := m) (ψ := ψ) (m + 1)
  rw [hk, hψm _ (by omega)]

/-- The supremum `sup_{k ≥ 0} ψ_{n+k} / c` in `[0, ∞]`. -/
theorem iSup_ofReal_div (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ⨆ k : ℕ, ENNReal.ofReal (ψ (n + k) / c) = ENNReal.ofReal (runMax m ψ n / c) := by
  refine le_antisymm (iSup_le fun k => ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (le_runMax hψ0 hψm n k) hc.le)) ?_
  obtain ⟨k, hk⟩ := exists_runMax_eq (m := m) (ψ := ψ) n
  rw [hk]
  exact le_iSup (fun k => ENNReal.ofReal (ψ (n + k) / c)) k

end runMax

/-- **Candidate extremal index of a finite moving average** ([EKM, §8.1], [DR85],
[KS20, §15.3]): for nonnegative coefficients `ψ_0, …, ψ_m` (not all zero) and `α > 0`, the
spectral tail process `Θ_t = ψ_{J+t} / ψ_J` with `P(J = j) ∝ ψ_j^α` has candidate extremal
index `ϑ = max_j ψ_j^α / ∑_j ψ_j^α`. -/
theorem candidateExtremalIndex_spectral (hα : 0 < α) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψm : ∀ j, m < j → ψ j = 0) (hS : 0 < weightSum m ψ α) :
    candidateExtremalIndex (indexLaw m ψ α) (spectral m ψ) α =
      ENNReal.ofReal ((range (m + 1)).sup' nonempty_range_add_one ψ ^ α / weightSum m ψ α) := by
  set S := weightSum m ψ α
  have hM0 : ∀ n, 0 ≤ runMax m ψ n := runMax_nonneg hψ0 hψm
  have hMs : ∀ n, runMax m ψ (n + 1) ≤ runMax m ψ n := runMax_succ_le hψ0 hψm
  -- the value of the integrand at `j`, weighted
  have hterm : ∀ j : Fin (m + 1),
      ENNReal.ofReal (ψ j ^ α / S) *
        ((⨆ k : ℕ, ENNReal.ofReal |spectral m ψ k j|) ^ α -
          (⨆ k : ℕ, ENNReal.ofReal |spectral m ψ (k + 1) j|) ^ α) =
      ENNReal.ofReal ((runMax m ψ j ^ α - runMax m ψ (j + 1) ^ α) / S) := by
    intro j
    rcases (hψ0 j).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow hα.ne', zero_div, ENNReal.ofReal_zero, zero_mul,
        runMax_eq_of_eq_zero hψ0 hψm h0.symm, sub_self, zero_div, ENNReal.ofReal_zero]
    have h1 : ∀ k : ℕ, |spectral m ψ k j| = ψ ((j : ℕ) + k) / ψ j := fun k => by
      rw [spectral, show ((j : ℕ) : ℤ) + (k : ℤ) = (((j : ℕ) + k : ℕ) : ℤ) by push_cast; ring,
        coef_natCast, abs_of_nonneg (div_nonneg (hψ0 _) hpos.le)]
    have h2 : ∀ k : ℕ, |spectral m ψ (k + 1) j| = ψ ((j : ℕ) + 1 + k) / ψ j := fun k => by
      rw [spectral, show ((j : ℕ) : ℤ) + ((k : ℤ) + 1) = (((j : ℕ) + 1 + k : ℕ) : ℤ) by
        push_cast; ring, coef_natCast, abs_of_nonneg (div_nonneg (hψ0 _) hpos.le)]
    simp only [h1, h2]
    rw [iSup_ofReal_div hψ0 hψm _ hpos, iSup_ofReal_div hψ0 hψm _ hpos,
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hM0 _) hpos.le) hα.le,
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hM0 _) hpos.le) hα.le,
      ← ENNReal.ofReal_sub _ (Real.rpow_nonneg (div_nonneg (hM0 _) hpos.le) _),
      ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (hψ0 _) _) hS.le)]
    congr 1
    rw [Real.div_rpow (hM0 _) hpos.le, Real.div_rpow (hM0 _) hpos.le]
    have : 0 < ψ j ^ α := Real.rpow_pos_of_pos hpos _
    field_simp
  rw [candidateExtremalIndex, indexLaw, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  refine (Finset.sum_congr rfl fun j _ => hterm j).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg
      (sub_nonneg.2 (Real.rpow_le_rpow (hM0 _) (hMs _) hα.le)) hS.le,
    Fin.sum_univ_eq_sum_range (fun j => (runMax m ψ j ^ α - runMax m ψ (j + 1) ^ α) / S), ← Finset.sum_div,
    Finset.sum_range_sub' (fun j => runMax m ψ j ^ α), runMax_eq_zero hψm,
    Real.zero_rpow hα.ne', sub_zero]
  congr 2
  -- `M 0 = max_j ψ_j`
  simp only [runMax, zero_add]
