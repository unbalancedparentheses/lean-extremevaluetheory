/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.EchoMixing
import ExtremeValueTheory.Statistics.ExtremalIndexEstimators

/-!
# Block and run length theorem for extremal-index estimators (`EVT-OP-001`)

For the power-lag echo process `X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})` with iid
`Pareto(1, α)` innovations `Z_s` and power lag `L(z) = ⌊z^γ⌋₊ + 1` (`0 < γ < α`), we know from
`Dependence/EchoPowerLag.lean` and `Dependence/EchoMixing.lean` that `X` is stationary, `β`-mixing,
regularly varying of index `α`, has extremal index `θ = 1/2`, and has candidate extremal index
`ϑ = 1`.

This file upgrades the population-level echo counterexample to **estimator-level consistency and
inconsistency theorems** at intermediate thresholds `n uₙ^(-α) → ∞`, plus the explicit polynomial
`β`-mixing rate:

## Main results

* `betaMixing_powEchoProcess_le`, `alphaMixing_powEchoProcess_le`: explicit polynomial mixing rate
  `β(h) ≤ 2 ((α/γ)/(α/γ - 1)) (h - 1)^(1 - α/γ)` (and the same for `α(h)`) for all `h ≥ 2` and
  `0 < γ < α`.
* `powEcho_tendstoInMeasure_tailCount_div`: concentration `#{i < n : X_i > uₙ} / (2 n uₙ^(-α)) → 1`
  in probability for **all** `0 < γ < α` and **all** intermediate thresholds `uₙ → ∞`,
  `n uₙ^(-α) → ∞` (proved directly from the independent innovations via the pairwise collision
  identity `c - 1_{c ≥ 1} ≤ c(c - 1)`, with no `α/γ > 2` mixing-summability restriction).
* `powEcho_tendstoInMeasure_runsEstimator`: **inconsistency of short runs** — for all `0 < γ < α`,
  `uₙ → ∞`, `n uₙ^(-α) → ∞`, `rₙ → ∞`, `rₙ uₙ^(-α) → 0`, and `rₙ / uₙ^γ → 0`, the runs estimator
  satisfies `θ̂ᴿ(n, rₙ, uₙ) → 1 ≠ 1/2 = θ` in probability.
* `powEcho_tendstoInMeasure_blocksEstimator`: **consistency of long blocks** — for all `0 < γ < α`,
  `uₙ → ∞`, `n uₙ^(-α) → ∞`, `rₙ → ∞`, `rₙ / n → 0`, `rₙ uₙ^(-α) → 0`, and `uₙ^γ / rₙ → 0`, the
  disjoint blocks estimator satisfies `θ̂ᴮ(n, rₙ, uₙ) → 1/2 = θ` in probability.
* `exists_powEcho_runsEstimator_inconsistent_of_poly`: **no universal polynomial run-length rule** —
  for every polynomial exponent `ρ ∈ (0, 1)`, there exists a stationary, `β`-mixing, regularly
  varying process with extremal index `θ = 1/2` (and intermediate threshold sequence `uₙ` with
  `n P(X₀ > uₙ) → ∞`) on which the runs estimator with run length `rₙ = ⌊n^ρ⌋₊ + 1` converges in
  probability to `1 ≠ 1/2`, while the blocks estimator with a longer polynomial block length
  `r'ₙ = ⌊n^{ρ'}⌋₊ + 1` (`ρ' ∈ (ρ, 1)`) converges in probability to `1/2 = θ`.

## References

* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020), Ch. 10.
* S. Bai, R. Kulik, Y. Wang, *Anticlustering conditions for heavy-tailed time series* (2024).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal NNReal Classical

namespace ExtremeValueTheory

/-! ### Polynomial `β`- and `α`-mixing rate for the power-lag echo process -/

section PowerEchoMixingRate

/-- Elementary integral comparison for `p`-series tails: for `β > 1` and `k ≥ 1`,
`∑_{m ≥ 0} (k + m)^(-β) ≤ (β / (β - 1)) * k^(1 - β)`. -/
lemma tsum_rpow_neg_add_le {β : ℝ} (hβ : 1 < β) {k : ℕ} (hk : 1 ≤ k) :
    ∑' m : ℕ, ((k : ℝ) + m) ^ (-β) ≤ (β / (β - 1)) * (k : ℝ) ^ (1 - β) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hβ1 : 0 < β - 1 := sub_pos.2 hβ
  -- Compare each `m ≥ 1` term with `∫_{k+m-1}^{k+m} x^(-β) dx`
  have hint_m : ∀ m : ℕ, ((k : ℝ) + (m + 1 : ℕ)) ^ (-β) ≤
      ∫ x in ((k : ℝ) + m)..((k : ℝ) + (m + 1 : ℕ)), x ^ (-β) := fun m => by
    have ha : (0 : ℝ) < (k : ℝ) + m := by positivity
    have hab : (k : ℝ) + m ≤ (k : ℝ) + (m + 1 : ℕ) := by push_cast; linarith
    have hcont : ContinuousOn (fun x : ℝ => x ^ (-β)) (uIcc ((k : ℝ) + m) ((k : ℝ) + (m + 1 : ℕ))) := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact (Real.continuousAt_rpow_const x (-β) (Or.inl (by linarith [hx.1]))).continuousWithinAt
    have hle := intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (hcont.intervalIntegrable (μ := volume))
      (fun x hx => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx.2 (by linarith))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
    have hdiff : ((k : ℝ) + (m + 1 : ℕ)) - ((k : ℝ) + m) = 1 := by push_cast; ring
    rw [hdiff, one_mul] at hle
    exact hle
  have hpart : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1), ((k : ℝ) + m) ^ (-β) ≤
      (k : ℝ) ^ (-β) + (k : ℝ) ^ (1 - β) / (β - 1) := fun N => by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, add_zero]
    have htel : ∑ m ∈ Finset.range N, ((k : ℝ) + (m + 1 : ℕ)) ^ (-β) ≤
        ∫ x in (k : ℝ)..((k : ℝ) + N), x ^ (-β) := by
      have h1 : ∑ m ∈ Finset.range N, ((k : ℝ) + (m + 1 : ℕ)) ^ (-β) ≤
          ∑ m ∈ Finset.range N, ∫ x in ((k : ℝ) + m)..((k : ℝ) + (m + 1 : ℕ)), x ^ (-β) :=
        Finset.sum_le_sum fun m _ => hint_m m
      have h2 : ∑ m ∈ Finset.range N, ∫ x in ((k : ℝ) + m)..((k : ℝ) + (m + 1 : ℕ)), x ^ (-β) =
          ∫ x in (k : ℝ)..((k : ℝ) + N), x ^ (-β) := by
        clear h1
        induction N with
        | zero => simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih, intervalIntegral.integral_add_adjacent_intervals]
          · have hab : (k : ℝ) ≤ (k : ℝ) + n := by linarith [Nat.cast_nonneg (α := ℝ) n]
            exact (ContinuousOn.intervalIntegrable (μ := volume) fun x hx => by
              rw [uIcc_of_le hab] at hx
              exact (Real.continuousAt_rpow_const x (-β) (Or.inl (by linarith [hx.1]))).continuousWithinAt)
          · have hab : (k : ℝ) + n ≤ (k : ℝ) + (n + 1 : ℕ) := by push_cast; linarith
            exact (ContinuousOn.intervalIntegrable (μ := volume) fun x hx => by
              rw [uIcc_of_le hab] at hx
              exact (Real.continuousAt_rpow_const x (-β) (Or.inl (by linarith [hx.1]))).continuousWithinAt)
      exact h1.trans_eq h2
    have heval : ∫ x in (k : ℝ)..((k : ℝ) + N), x ^ (-β) =
        ((k : ℝ) ^ (1 - β) - ((k : ℝ) + N) ^ (1 - β)) / (β - 1) := by
      rw [integral_rpow]
      · have hne : -β + 1 ≠ 0 := by linarith
        have hne' : (1 : ℝ) - β ≠ 0 := by linarith
        have heq : -β + 1 = 1 - β := by ring
        rw [heq]; field_simp [hne', hβ1.ne']; ring
      · right; refine ⟨by linarith, fun h0 => ?_⟩
        rw [uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) N] : (k : ℝ) ≤ (k : ℝ) + N)] at h0
        linarith [h0.1]
    have hnn : 0 ≤ ((k : ℝ) + N) ^ (1 - β) := Real.rpow_nonneg (by positivity) _
    have hdiv : ((k : ℝ) ^ (1 - β) - ((k : ℝ) + N) ^ (1 - β)) / (β - 1) ≤ (k : ℝ) ^ (1 - β) / (β - 1) :=
      div_le_div_of_nonneg_right (by linarith) hβ1.le
    linarith
  have hsumm : Summable fun m : ℕ => ((k : ℝ) + m) ^ (-β) := by
    have h := (summable_nat_add_iff k).2 (Real.summable_nat_rpow.2 (show -β < -1 by linarith))
    simpa [add_comm] using h
  have htsum_le : ∑' m : ℕ, ((k : ℝ) + m) ^ (-β) ≤ (k : ℝ) ^ (-β) + (k : ℝ) ^ (1 - β) / (β - 1) := by
    refine le_of_tendsto (hsumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) ?_
    exact Eventually.of_forall hpart
  have hk_pow : (k : ℝ) ^ (-β) ≤ (k : ℝ) ^ (1 - β) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  calc ∑' m : ℕ, ((k : ℝ) + m) ^ (-β)
      ≤ (k : ℝ) ^ (-β) + (k : ℝ) ^ (1 - β) / (β - 1) := htsum_le
    _ ≤ (k : ℝ) ^ (1 - β) + (k : ℝ) ^ (1 - β) / (β - 1) := by linarith
    _ = (β / (β - 1)) * (k : ℝ) ^ (1 - β) := by field_simp [hβ1.ne']; ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α γ : ℝ} {Z : ℤ → Ω → ℝ}

/-- **Polynomial `β`-mixing rate of the power-lag echo process**: for `0 < γ < α` and `h ≥ 2`,
`β(h) ≤ 2 · ((α/γ) / (α/γ - 1)) · (h - 1)^(1 - α/γ)`. -/
theorem betaMixing_powEchoProcess_le (hα : 0 < α) (hγ : 0 < γ) (hγα : γ < α)
    (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) {h : ℕ} (hh : 2 ≤ h) :
    (betaMixing (fun k : ℕ => echoProcess (powLag γ) Z k) P h).toReal ≤
      2 * ((α / γ) / (α / γ - 1)) * ((h - 1 : ℕ) : ℝ) ^ (1 - α / γ) := by
  have hβ : 1 < α / γ := (one_lt_div hγ).2 hγα
  have hsum_all := summable_powLag hα hγ hγα
  have hsum : Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ powLag γ z} := by
    have hshift := (summable_nat_add_iff (h - 1)).2 hsum_all
    refine hshift.congr fun m => ?_
    congr 1; ext z; simp only [mem_ofPred_eq]; constructor <;> intro hz <;> omega
  have h1 := betaMixing_echoProcess_le hZ hind hlaw (measurable_powLag γ) (by omega) hsum
  have hsumm_rhs : Summable fun m : ℕ => (((h - 1 : ℕ) : ℝ) + m) ^ (-(α / γ)) := by
    have hs := (summable_nat_add_iff (h - 1)).2 (Real.summable_nat_rpow.2 (show -(α / γ) < -1 by linarith))
    simpa [add_comm] using hs
  have hterm : ∀ m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ powLag γ z} ≤
      (((h - 1 : ℕ) : ℝ) + m) ^ (-(α / γ)) := fun m => by
    have hm := measureReal_powLag_le hα hγ (h - 2 + m)
    have heq1 : h - 2 + m + 1 + 1 = h + m := by omega
    have heq2 : ((h - 2 + m : ℕ) : ℝ) + 1 = ((h - 1 : ℕ) : ℝ) + m := by
      have : h - 2 + m + 1 = (h - 1) + m := by omega
      exact_mod_cast this
    rw [heq1, heq2] at hm
    exact hm
  have htsum := Summable.tsum_le_tsum hterm hsum hsumm_rhs
  have hint := tsum_rpow_neg_add_le hβ (k := h - 1) (by omega)
  linarith

/-- **Polynomial `α`-mixing rate of the power-lag echo process**: for `0 < γ < α` and `h ≥ 2`,
`α(h) ≤ 2 · ((α/γ) / (α/γ - 1)) · (h - 1)^(1 - α/γ)`. -/
theorem alphaMixing_powEchoProcess_le (hα : 0 < α) (hγ : 0 < γ) (hγα : γ < α)
    (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) {h : ℕ} (hh : 2 ≤ h) :
    (alphaMixing (fun k : ℕ => echoProcess (powLag γ) Z k) P h).toReal ≤
      2 * ((α / γ) / (α / γ - 1)) * ((h - 1 : ℕ) : ℝ) ^ (1 - α / γ) := by
  have hβ : 1 < α / γ := (one_lt_div hγ).2 hγα
  have hsum_all := summable_powLag hα hγ hγα
  have hsum : Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ powLag γ z} := by
    have hshift := (summable_nat_add_iff (h - 1)).2 hsum_all
    refine hshift.congr fun m => ?_
    congr 1; ext z; simp only [mem_ofPred_eq]; constructor <;> intro hz <;> omega
  have h1 := alphaMixing_echoProcess_le hZ hind hlaw (measurable_powLag γ) (by omega) hsum
  have hsumm_rhs : Summable fun m : ℕ => (((h - 1 : ℕ) : ℝ) + m) ^ (-(α / γ)) := by
    have hs := (summable_nat_add_iff (h - 1)).2 (Real.summable_nat_rpow.2 (show -(α / γ) < -1 by linarith))
    simpa [add_comm] using hs
  have hterm : ∀ m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ powLag γ z} ≤
      (((h - 1 : ℕ) : ℝ) + m) ^ (-(α / γ)) := fun m => by
    have hm := measureReal_powLag_le hα hγ (h - 2 + m)
    have heq1 : h - 2 + m + 1 + 1 = h + m := by omega
    have heq2 : ((h - 2 + m : ℕ) : ℝ) + 1 = ((h - 1 : ℕ) : ℝ) + m := by
      have : h - 2 + m + 1 = (h - 1) + m := by omega
      exact_mod_cast this
    rw [heq1, heq2] at hm
    exact hm
  have htsum := Summable.tsum_le_tsum hterm hsum hsumm_rhs
  have hint := tsum_rpow_neg_add_le hβ (k := h - 1) (by omega)
  linarith

end PowerEchoMixingRate

/-! ### Direct innovation-level concentration for the power-lag echo process -/

section PowerEchoEstimators

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α γ : ℝ} {Z : ℤ → Ω → ℝ}

/-- Collision bound for independent `{0, 1}` indicators:
`E[(∑_{a ∈ S} I_a) * (∑_{a ∈ S} I_a - 1)] ≤ (∑_{a ∈ S} E[I_a])²`. -/
private lemma integral_mul_sub_one_le_sq {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {I : ι → Ω → ℝ} (hIm : ∀ a, Measurable (I a))
    (hI01 : ∀ a ω, I a ω = 0 ∨ I a ω = 1) (hind : iIndepFun I P) :
    ∫ ω, (∑ a ∈ S, I a ω) * ((∑ a ∈ S, I a ω) - 1) ∂P ≤ (∑ a ∈ S, ∫ ω, I a ω ∂P) ^ 2 := by
  have hI0 : ∀ a ω, 0 ≤ I a ω := fun a ω => by rcases hI01 a ω with h | h <;> linarith
  have hI1 : ∀ a ω, I a ω ≤ 1 := fun a ω => by rcases hI01 a ω with h | h <;> linarith
  have hIsq : ∀ a ω, I a ω * I a ω = I a ω := fun a ω => by rcases hI01 a ω with h | h <;> simp [h]
  have hInt : ∀ a, Integrable (I a) P := fun a =>
    Integrable.of_bound (hIm a).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hI0 a ω)]; exact hI1 a ω)
  have hIntProd : ∀ a b, Integrable (fun ω => I a ω * I b ω) P := fun a b =>
    Integrable.of_bound ((hIm a).mul (hIm b)).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hI0 a ω) (hI0 b ω))]
      nlinarith [hI0 a ω, hI1 a ω, hI0 b ω, hI1 b ω])
  have hpt : ∀ ω, (∑ a ∈ S, I a ω) * ((∑ a ∈ S, I a ω) - 1) =
      ∑ a ∈ S, ∑ b ∈ S.erase a, I a ω * I b ω := fun ω => by
    have h1 : (∑ a ∈ S, I a ω) * (∑ b ∈ S, I b ω) =
        ∑ a ∈ S, (I a ω * I a ω + ∑ b ∈ S.erase a, I a ω * I b ω) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ ha]
    have h2 : (∑ a ∈ S, I a ω) * ((∑ b ∈ S, I b ω) - 1) =
        (∑ a ∈ S, I a ω) * (∑ b ∈ S, I b ω) - ∑ a ∈ S, I a ω := by ring
    rw [h2, h1, Finset.sum_add_distrib]
    have hdiag : ∑ a ∈ S, I a ω * I a ω = ∑ a ∈ S, I a ω :=
      Finset.sum_congr rfl fun a _ => hIsq a ω
    rw [hdiag]; ring
  simp_rw [hpt]
  rw [integral_finsetSum S fun a _ => integrable_finsetSum _ fun b _ => hIntProd a b]
  have hsum_eq : ∑ a ∈ S, ∫ ω, (∑ b ∈ S.erase a, I a ω * I b ω) ∂P =
      ∑ a ∈ S, ∑ b ∈ S.erase a, (∫ ω, I a ω ∂P) * (∫ ω, I b ω ∂P) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hIntProd a b]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hne : a ≠ b := (Finset.mem_erase.1 hb).1.symm
    exact (hind.indepFun hne).integral_fun_mul_eq_mul_integral
      (hIm a).aestronglyMeasurable (hIm b).aestronglyMeasurable
  rw [hsum_eq]
  have hsq : (∑ a ∈ S, ∫ ω, I a ω ∂P) ^ 2 =
      ∑ a ∈ S, ∑ b ∈ S, (∫ ω, I a ω ∂P) * (∫ ω, I b ω ∂P) := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  rw [hsq]
  refine Finset.sum_le_sum fun a ha => ?_
  have hle : ∑ b ∈ S.erase a, (∫ ω, I a ω ∂P) * (∫ ω, I b ω ∂P) ≤
      ∑ b ∈ S, (∫ ω, I a ω ∂P) * (∫ ω, I b ω ∂P) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset a S) fun b _ _ =>
      mul_nonneg (integral_nonneg (hI0 a)) (integral_nonneg (hI0 b))
  exact hle

/-- Elementary inequality for counts: `c - 1_{c ≥ 1} ≤ c (c - 1)` for every `c : ℕ`. -/
private lemma nat_sub_ind_le_mul_sub_one (c : ℕ) :
    (c : ℝ) - (if 1 ≤ c then (1 : ℝ) else 0) ≤ (c : ℝ) * ((c : ℝ) - 1) := by
  rcases c with _ | c
  · simp
  · rcases c with _ | c
    · simp
    · simp only [Nat.succ_le_succ_iff, Nat.zero_le, ↓reduceIte]
      have h : (2 : ℝ) ≤ ((c + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ c + 1 + 1 by omega)
      nlinarith

/-- Nonnegative `L¹` convergence to `0` implies convergence in probability to `0` (Markov). -/
private lemma tendstoInMeasure_zero_of_tendsto_integral_nonneg {f : ℕ → Ω → ℝ}
    (hf0 : ∀ n ω, 0 ≤ f n ω) (hfi : ∀ n, Integrable (f n) P)
    (hlim : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hdiv : Tendsto (fun n => ENNReal.ofReal ((∫ ω, f n ω ∂P) / ε)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (∫ ω, f n ω ∂P) / ε) atTop (𝓝 0) := by
      simpa using hlim.div_const ε
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
  have hmark := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (hf0 n)) (hfi n) ε
  have hset : {ω | ε ≤ ‖f n ω - 0‖} = {ω | ε ≤ f n ω} := by
    ext ω; simp [Real.norm_eq_abs, abs_of_nonneg (hf0 n ω)]
  rw [hset]
  have hreal : P.real {ω | ε ≤ f n ω} ≤ (∫ ω, f n ω ∂P) / ε := by
    rw [le_div_iff₀ hε, mul_comm]; exact hmark
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Chebyshev concentration for independent bounded random variables `Y_s ∈ [0, M]`:
if `E[∑_{s < N n} Y_s] / aₙ → c` and `∑_{s < N n} E[Y_s²] / aₙ² → 0`, then `(∑_{s < N n} Y_s) / aₙ → c`
in probability. -/
private lemma tendstoInMeasure_sum_indep_div {Y : ℕ → ℕ → Ω → ℝ} {N : ℕ → ℕ} {M : ℝ}
    {a : ℕ → ℝ} {c : ℝ}
    (hYm : ∀ n s, Measurable (Y n s)) (hYbd : ∀ n s ω, 0 ≤ Y n s ω ∧ Y n s ω ≤ M)
    (hind : ∀ n, iIndepFun (Y n) P) (ha : ∀ᶠ n in atTop, 0 < a n)
    (hmean : Tendsto (fun n => (∑ s ∈ Finset.range (N n), ∫ ω, Y n s ω ∂P) / a n) atTop (𝓝 c))
    (hvar : Tendsto (fun n => (∑ s ∈ Finset.range (N n), ∫ ω, (Y n s ω) ^ 2 ∂P) / (a n) ^ 2)
      atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => (∑ s ∈ Finset.range (N n), Y n s ω) / a n) atTop (fun _ => c) := by
  have hL2 : ∀ n s, MemLp (Y n s) 2 P := fun n s =>
    MemLp.of_bound (hYm n s).aestronglyMeasurable M (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYbd n s ω).1]; exact (hYbd n s ω).2)
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hbound : Tendsto (fun n => ENNReal.ofReal
      (((∑ s ∈ Finset.range (N n), ∫ ω, (Y n s ω) ^ 2 ∂P) / (a n) ^ 2) / (ε / 2) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ((∑ s ∈ Finset.range (N n), ∫ ω, (Y n s ω) ^ 2 ∂P) / (a n) ^ 2) /
        (ε / 2) ^ 2) atTop (𝓝 0) := by
      simpa using hvar.div_const ((ε / 2) ^ 2)
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [ha, (Metric.tendsto_nhds.1 hmean) (ε / 2) (by positivity)] with n han hmn
  rw [Real.dist_eq] at hmn
  set S : Ω → ℝ := fun ω => ∑ s ∈ Finset.range (N n), Y n s ω
  have hS_L2 : MemLp S 2 P := memLp_finsetSum _ fun s _ => hL2 n s
  have hS_mean : ∫ ω, S ω ∂P = ∑ s ∈ Finset.range (N n), ∫ ω, Y n s ω ∂P :=
    integral_finsetSum _ fun s _ => (hL2 n s).integrable one_le_two
  have hS_var : variance S P ≤ ∑ s ∈ Finset.range (N n), ∫ ω, (Y n s ω) ^ 2 ∂P := by
    rw [show S = ∑ s ∈ Finset.range (N n), Y n s by ext ω; simp [S]]
    rw [IndepFun.variance_sum (fun s _ => hL2 n s) fun a _ b _ hab => (hind n).indepFun hab]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [variance_eq_sub (hL2 n s)]
    simp only [Pi.pow_apply]
    linarith [sq_nonneg (∫ ω, Y n s ω ∂P)]
  have hsub : {ω | ε ≤ ‖S ω / a n - c‖} ⊆ {ω | ε / 2 * a n ≤ |S ω - ∫ ω', S ω' ∂P|} := by
    intro ω hω
    simp only [mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
    have htri : |S ω / a n - (∫ ω', S ω' ∂P) / a n| ≥ ε / 2 := by
      have := abs_sub_le (S ω / a n) ((∫ ω', S ω' ∂P) / a n) c
      rw [← hS_mean] at hmn
      linarith
    rw [← sub_div, abs_div, abs_of_pos han, ge_iff_le, le_div_iff₀ han] at htri
    exact htri
  have hcheb := meas_ge_le_variance_div_sq hS_L2 (show 0 < ε / 2 * a n by positivity)
  have hle : P {ω | ε ≤ ‖S ω / a n - c‖} ≤
      ENNReal.ofReal (variance S P / (ε / 2 * a n) ^ 2) :=
    (measure_mono hsub).trans hcheb
  refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
  have heq : ((∑ s ∈ Finset.range (N n), ∫ ω, (Y n s ω) ^ 2 ∂P) / (a n) ^ 2) / (ε / 2) ^ 2 =
      (∑ s ∈ Finset.range (N n), ∫ ω, (Y n s ω) ^ 2 ∂P) / (ε / 2 * a n) ^ 2 := by
    field_simp [han.ne', hε.ne']
  rw [heq]
  exact div_le_div_of_nonneg_right hS_var (by positivity)

/-- Bound on the truncated lag moment `∑_{k ≥ 1} P(Z > u, L(Z) ≥ k) ≤ (2 + α/(α-γ)) u^(γ - α)`
for `u ≥ 1`, `0 < γ < α`. -/
private lemma tsum_measureReal_gt_and_powLag_ge_le (hα : 0 < α) (hγ : 0 < γ) (hγα : γ < α)
    {u : ℝ} (hu : 1 ≤ u) :
    ∑' k : ℕ, (paretoMeasure 1 α).real {z | u < z ∧ k + 1 ≤ powLag γ z} ≤
      (α / (α - γ) + 1) * u ^ (γ - α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hu0 : 0 < u := one_pos.trans_le hu
  -- First compute `∫_{z > u} z^γ ∂Pareto(1, α) = (α / (α - γ)) * u^(γ - α)`
  have hint_z : ∫ z in Ioi u, z ^ γ ∂(paretoMeasure 1 α) = α / (α - γ) * u ^ (γ - α) := by
    have hlim : Tendsto (fun R : ℕ => ∫ z in Ioc u (max u R), z ^ γ ∂(paretoMeasure 1 α))
        atTop (𝓝 (α / (α - γ) * u ^ (γ - α))) := by
      have hR : Tendsto (fun R : ℕ => (max u R : ℝ) ^ (γ - α)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun R : ℕ => (max u R : ℝ) ^ (-(α - γ))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop (show 0 < α - γ by linarith)).comp
            (tendsto_atTop_mono (fun R : ℕ => le_max_right u (R : ℝ)) tendsto_natCast_atTop_atTop)
        exact h1.congr fun R => by congr 1; ring
      have h1 := ((hR.const_sub (u ^ (γ - α))).const_mul (α / (α - γ)))
      rw [sub_zero] at h1
      refine h1.congr fun R => (setIntegral_Ioc_rpow_pareto hα hγα hu (le_max_left u R)).symm
    have hintOn : IntegrableOn (fun z : ℝ => z ^ γ) (Ioi u) (paretoMeasure 1 α) := by
      -- Direct integrable bound via monotone convergence on `Ioc u (max u R)`
      have hl : ∫⁻ z in Ioi u, ENNReal.ofReal (z ^ γ) ∂(paretoMeasure 1 α) < ⊤ := by
        have hmon : ∫⁻ z in Ioi u, ENNReal.ofReal (z ^ γ) ∂(paretoMeasure 1 α) =
            ⨆ R : ℕ, ∫⁻ z in Ioc u (max u R), ENNReal.ofReal (z ^ γ) ∂(paretoMeasure 1 α) := by
          have heq_f : ∀ z, (Ioi u).indicator (fun x : ℝ => ENNReal.ofReal (x ^ γ)) z =
              ⨆ R : ℕ, (Ioc u (max u R)).indicator (fun x : ℝ => ENNReal.ofReal (x ^ γ)) z := fun z => by
            by_cases hz : z ∈ Ioi u
            · rw [Set.indicator_of_mem hz]
              refine le_antisymm ?_ (iSup_le fun R => by
                by_cases hR : z ∈ Ioc u (max u R)
                · rw [Set.indicator_of_mem hR]
                · rw [Set.indicator_of_notMem hR]; exact bot_le)
              obtain ⟨R, hR⟩ := exists_nat_ge z
              have hmem : z ∈ Ioc u (max u R) := ⟨hz, hR.trans (le_max_right _ _)⟩
              calc ENNReal.ofReal (z ^ γ)
                  = (Ioc u (max u R)).indicator (fun x : ℝ => ENNReal.ofReal (x ^ γ)) z :=
                    (Set.indicator_of_mem hmem (fun x : ℝ => ENNReal.ofReal (x ^ γ))).symm
                _ ≤ ⨆ R' : ℕ, (Ioc u (max u R')).indicator (fun x : ℝ => ENNReal.ofReal (x ^ γ)) z :=
                    le_iSup (f := fun R' : ℕ => (Ioc u (max u (R' : ℝ))).indicator (fun x : ℝ => ENNReal.ofReal (x ^ γ)) z) R
            · rw [Set.indicator_of_notMem hz]
              refine (le_antisymm (iSup_le fun R => ?_) bot_le).symm
              rw [Set.indicator_of_notMem (fun h => hz h.1)]
              exact le_rfl
          have h1 : ∫⁻ z in Ioi u, ENNReal.ofReal (z ^ γ) ∂(paretoMeasure 1 α) =
              ∫⁻ z, (Ioi u).indicator (fun x : ℝ => ENNReal.ofReal (x ^ γ)) z ∂(paretoMeasure 1 α) :=
            (lintegral_indicator measurableSet_Ioi (fun x : ℝ => ENNReal.ofReal (x ^ γ))).symm
          rw [h1, lintegral_congr heq_f, lintegral_iSup]
          · refine iSup_congr fun R => lintegral_indicator measurableSet_Ioc (fun x : ℝ => ENNReal.ofReal (x ^ γ))
          · intro R; exact (ENNReal.measurable_ofReal.comp (measurable_id.pow_const γ)).indicator measurableSet_Ioc
          · intro a b hab z
            dsimp only
            by_cases ha : z ∈ Ioc u (max u a)
            · have hb : z ∈ Ioc u (max u b) := ⟨ha.1, ha.2.trans (max_le_max_left u (by exact_mod_cast hab))⟩
              rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
            · rw [Set.indicator_of_notMem ha]; exact bot_le
        rw [hmon]
        refine lt_of_le_of_lt (iSup_le fun R => ?_)
          (ENNReal.ofReal_lt_top (r := α / (α - γ) * u ^ (γ - α)))
        have hiR : IntegrableOn (fun z : ℝ => z ^ γ) (Ioc u (max u R)) (paretoMeasure 1 α) := by
          refine (integrable_const ((max u R) ^ γ)).mono'
            (measurable_id.pow_const γ).aestronglyMeasurable
            (ae_restrict_of_forall_mem measurableSet_Ioc fun z hz => ?_)
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (hu0.trans hz.1).le _)]
          exact Real.rpow_le_rpow (hu0.trans hz.1).le hz.2 hγ.le
        rw [← ofReal_integral_eq_lintegral_ofReal hiR
          (ae_restrict_of_forall_mem measurableSet_Ioc fun z hz => Real.rpow_nonneg (hu0.trans hz.1).le _),
          setIntegral_Ioc_rpow_pareto hα hγα hu (le_max_left u R)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ (max u R : ℝ) ^ (γ - α) := Real.rpow_nonneg (hu0.le.trans (le_max_left _ _)) _
        have : 0 < α / (α - γ) := div_pos hα (sub_pos.2 hγα)
        nlinarith
      refine ⟨(measurable_id.pow_const γ).aestronglyMeasurable, ?_⟩
      change ∫⁻ z in Ioi u, ‖z ^ γ‖ₑ ∂(paretoMeasure 1 α) < ⊤
      have heq : ∫⁻ z in Ioi u, ‖z ^ γ‖ₑ ∂(paretoMeasure 1 α) =
          ∫⁻ z in Ioi u, ENNReal.ofReal (z ^ γ) ∂(paretoMeasure 1 α) :=
        setLIntegral_congr_fun measurableSet_Ioi fun z hz => by
          rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (hu0.trans hz).le _)]
      rwa [heq]
    have hlim2 : Tendsto (fun R : ℕ => ∫ z in Ioc u (max u R), z ^ γ ∂(paretoMeasure 1 α))
        atTop (𝓝 (∫ z in Ioi u, z ^ γ ∂(paretoMeasure 1 α))) := by
      have heq : ∀ R : ℕ, ∫ z in Ioc u (max u R), z ^ γ ∂(paretoMeasure 1 α) =
          ∫ z in Ioi u, (Ioc u (max u R)).indicator (fun x => x ^ γ) z ∂(paretoMeasure 1 α) := fun R => by
        rw [setIntegral_indicator measurableSet_Ioc,
          inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self]
      simp_rw [heq]
      refine tendsto_integral_of_dominated_convergence (fun z => ‖z ^ γ‖)
        (fun R => hintOn.aestronglyMeasurable.indicator measurableSet_Ioc) hintOn.norm
        (fun R => ae_of_all _ fun z => by
          by_cases h : z ∈ Ioc u (max u R)
          · rw [Set.indicator_of_mem h]
          · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => by
          refine tendsto_const_nhds.congr' ?_
          obtain ⟨R₀, hR₀⟩ := exists_nat_ge z
          filter_upwards [eventually_ge_atTop R₀] with R hR
          have hmem : z ∈ Ioc u (max u R) :=
            ⟨hz, hR₀.trans ((by exact_mod_cast hR : (R₀ : ℝ) ≤ R).trans (le_max_right _ _))⟩
          exact (Set.indicator_of_mem hmem (fun x => x ^ γ)).symm)
    exact tendsto_nhds_unique hlim2 hlim
  -- Sum `∑_{k ≥ 0} P(Z > u, L(Z) ≥ k + 1) = E[L(Z) ; Z > u] ≤ E[Z^γ + 1 ; Z > u]`
  have hle_L : ∀ N : ℕ, ∑ k ∈ Finset.range N,
      (paretoMeasure 1 α).real {z | u < z ∧ k + 1 ≤ powLag γ z} ≤
      (α / (α - γ) + 1) * u ^ (γ - α) := fun N => by
    have hsum_eq : ∑ k ∈ Finset.range N, (paretoMeasure 1 α).real {z | u < z ∧ k + 1 ≤ powLag γ z} =
        ∫ z in Ioi u, (∑ k ∈ Finset.range N, if k + 1 ≤ powLag γ z then (1 : ℝ) else 0)
          ∂(paretoMeasure 1 α) := by
      rw [integral_finsetSum _ fun k _ => (integrable_const (1 : ℝ)).mono'
        (Measurable.ite (measurableSet_le measurable_const (measurable_powLag γ))
          measurable_const measurable_const).aestronglyMeasurable
        (ae_of_all _ fun z => by split_ifs <;> norm_num)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hset : MeasurableSet {z : ℝ | k + 1 ≤ powLag γ z} :=
        measurableSet_le measurable_const (measurable_powLag γ)
      have heq : (fun z : ℝ => if k + 1 ≤ powLag γ z then (1 : ℝ) else 0) =
          ({z | k + 1 ≤ powLag γ z}).indicator (fun _ => (1 : ℝ)) := by
        ext z; simp [Set.indicator]
      rw [heq, setIntegral_indicator hset, setIntegral_const, smul_eq_mul, mul_one]
      rfl
    rw [hsum_eq]
    have hint_rhs : IntegrableOn (fun z : ℝ => z ^ γ + 1) (Ioi u) (paretoMeasure 1 α) := by
      -- reuse integrability from `hint_z`
      have hI : IntegrableOn (fun z : ℝ => z ^ γ) (Ioi u) (paretoMeasure 1 α) := by
        by_contra hni
        have := integral_undef hni
        rw [hint_z] at this
        have hpos : 0 < α / (α - γ) * u ^ (γ - α) := mul_pos (div_pos hα (sub_pos.2 hγα)) (Real.rpow_pos_of_pos hu0 _)
        linarith
      exact hI.add (integrable_const 1)
    have hint_lhs : IntegrableOn (fun z : ℝ => ∑ k ∈ Finset.range N,
        if k + 1 ≤ powLag γ z then (1 : ℝ) else 0) (Ioi u) (paretoMeasure 1 α) :=
      integrable_finsetSum _ fun k _ => (integrable_const (1 : ℝ)).mono'
        (Measurable.ite (measurableSet_le measurable_const (measurable_powLag γ))
          measurable_const measurable_const).aestronglyMeasurable
        (ae_of_all _ fun z => by split_ifs <;> norm_num)
    have hmono := setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi fun z hz => by
      have hz0 : 0 ≤ z := (hu0.trans hz).le
      have hcard : (∑ k ∈ Finset.range N, if k + 1 ≤ powLag γ z then (1 : ℝ) else 0) ≤ powLag γ z := by
        have hleN : ((Finset.range N).filter fun k => k + 1 ≤ powLag γ z).card ≤ powLag γ z := by
          have hsub : (Finset.range N).filter (fun k => k + 1 ≤ powLag γ z) ⊆ Finset.range (powLag γ z) :=
            fun k hk => Finset.mem_range.2 (by simp at hk; omega)
          exact (Finset.card_le_card hsub).trans (by simp)
        simpa [Finset.sum_boole] using (Nat.cast_le (α := ℝ)).2 hleN
      exact hcard.trans (powLag_le hz0)
    have hval : ∫ z in Ioi u, (z ^ γ + 1) ∂(paretoMeasure 1 α) =
        α / (α - γ) * u ^ (γ - α) + u ^ (-α) := by
      have hI : IntegrableOn (fun z : ℝ => z ^ γ) (Ioi u) (paretoMeasure 1 α) := by
        by_contra hni
        have := integral_undef hni
        rw [hint_z] at this
        have hpos : 0 < α / (α - γ) * u ^ (γ - α) := mul_pos (div_pos hα (sub_pos.2 hγα)) (Real.rpow_pos_of_pos hu0 _)
        linarith
      rw [integral_add hI (integrable_const 1), hint_z, setIntegral_const, smul_eq_mul, mul_one,
        paretoMeasure_one_real_Ioi hα hu]
    have hu_le : u ^ (-α) ≤ u ^ (γ - α) := Real.rpow_le_rpow_of_exponent_le hu (by linarith)
    linarith
  have hsumm : Summable fun k : ℕ => (paretoMeasure 1 α).real {z | u < z ∧ k + 1 ≤ powLag γ z} :=
    (summable_powLag hα hγ hγα).of_nonneg_of_le (fun _ => measureReal_nonneg) fun k =>
      measureReal_mono fun z hz => hz.2
  exact le_of_tendsto hsumm.hasSum.tendsto_sum_nat (Eventually.of_forall hle_L)

variable (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)

include hα hZ hind hlaw in
/-- **Concentration of the tail exceedance count for the power-lag echo process**: for ALL
`0 < γ < α` and ALL intermediate thresholds `uₙ → ∞`, `n uₙ^(-α) → ∞`,
`#{i < n : X_i > uₙ} / (2 n uₙ^(-α)) → 1` in probability. -/
theorem powEcho_tendstoInMeasure_tailCount_div (hγ : 0 < γ) (hγα : γ < α) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) (hk : Tendsto (fun n : ℕ => (n : ℝ) * u n ^ (-α)) atTop atTop) :
    TendstoInMeasure P
      (fun n ω => (tailCount (fun k : ℕ => echoProcess (powLag γ) Z k) n (u n) ω : ℝ) /
        (2 * (n : ℝ) * u n ^ (-α))) atTop (fun _ => 1) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set X : ℕ → Ω → ℝ := fun k => echoProcess (powLag γ) Z k
  have hXm : ∀ k, Measurable (X k) := fun k => measurable_echoProcess hZ (measurable_powLag γ) k
  set L := powLag γ
  have hLm : Measurable L := measurable_powLag γ
  -- Define `D n ω = ∑_{s < n} (1_{Z_s > uₙ} + 1_{Z_s > uₙ ∧ s + L(Z_s) < n})`
  set Y : ℕ → ℕ → Ω → ℝ := fun n s ω =>
    (if u n < Z s ω then (1 : ℝ) else 0) +
    (if u n < Z s ω ∧ s + L (Z s ω) < n then (1 : ℝ) else 0)
  have hYm : ∀ n s, Measurable (Y n s) := fun n s =>
    (Measurable.ite (measurableSet_lt measurable_const (hZ s)) measurable_const measurable_const).add
      (Measurable.ite ((measurableSet_lt measurable_const (hZ s)).inter
        (measurableSet_lt (measurable_const.add (hLm.comp (hZ s))) measurable_const))
        measurable_const measurable_const)
  have hYbd : ∀ n s ω, 0 ≤ Y n s ω ∧ Y n s ω ≤ 2 := fun n s ω => by
    simp only [Y]; split_ifs <;> norm_num
  have hindY : ∀ n, iIndepFun (Y n) P := fun n => by
    have hindNat : iIndepFun (fun s : ℕ => Z (s : ℤ)) P :=
      hind.precomp Nat.cast_injective
    refine hindNat.comp (fun s z => (if u n < z then (1 : ℝ) else 0) +
      (if u n < z ∧ s + L z < n then (1 : ℝ) else 0)) fun s => ?_
    exact (Measurable.ite measurableSet_Ioi measurable_const measurable_const).add
      (Measurable.ite (measurableSet_Ioi.inter
        (measurableSet_lt (measurable_const.add hLm) measurable_const))
        measurable_const measurable_const)
  have hZprob : ∀ s : ℤ, ∀ {x : ℝ}, 1 ≤ x → P.real {ω | x < Z s ω} = x ^ (-α) := fun s {x} hx => by
    have hpre : {ω | x < Z s ω} = Z s ⁻¹' Ioi x := rfl
    rw [hpre, measureReal_def, ← Measure.map_apply (hZ s) measurableSet_Ioi, hlaw s,
      ← measureReal_def, paretoMeasure_one_real_Ioi hα hx]
  have hZprob_lag : ∀ (s : ℤ) (x : ℝ) (k : ℕ),
      P.real {ω | x < Z s ω ∧ k ≤ L (Z s ω)} = (paretoMeasure 1 α).real {z | x < z ∧ k ≤ L z} := by
    intro s x k
    have hset : MeasurableSet {z : ℝ | x < z ∧ k ≤ L z} :=
      measurableSet_Ioi.inter (measurableSet_le measurable_const hLm)
    have hpre : {ω | x < Z s ω ∧ k ≤ L (Z s ω)} = Z s ⁻¹' {z | x < z ∧ k ≤ L z} := rfl
    rw [hpre, measureReal_def, ← Measure.map_apply (hZ s) hset, hlaw s, ← measureReal_def]
  have hY_int : ∀ n s, 1 ≤ u n →
      ∫ ω, Y n s ω ∂P = 2 * u n ^ (-α) -
        (paretoMeasure 1 α).real {z | u n < z ∧ n - s ≤ L z} := fun n s hun => by
    have hi1 : Integrable (fun ω => if u n < Z s ω then (1 : ℝ) else 0) P :=
      Integrable.of_bound (Measurable.ite (measurableSet_lt measurable_const (hZ s))
        measurable_const measurable_const).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by split_ifs <;> norm_num)
    have hi2 : Integrable (fun ω => if u n < Z s ω ∧ s + L (Z s ω) < n then (1 : ℝ) else 0) P :=
      Integrable.of_bound (Measurable.ite ((measurableSet_lt measurable_const (hZ s)).inter
        (measurableSet_lt (measurable_const.add (hLm.comp (hZ s))) measurable_const))
        measurable_const measurable_const).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by split_ifs <;> norm_num)
    have h1 : ∫ ω, (if u n < Z s ω then (1 : ℝ) else 0) ∂P = u n ^ (-α) := by
      have heq : (fun ω => if u n < Z s ω then (1 : ℝ) else 0) =
          ({ω | u n < Z s ω}).indicator 1 := by
        ext ω; simp [Set.indicator]
      rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hZ s)), hZprob s hun]
    have h2 : ∫ ω, (if u n < Z s ω ∧ s + L (Z s ω) < n then (1 : ℝ) else 0) ∂P =
        u n ^ (-α) - (paretoMeasure 1 α).real {z | u n < z ∧ n - s ≤ L z} := by
      have hm1 : MeasurableSet {ω | u n < Z s ω ∧ s + L (Z s ω) < n} :=
        (measurableSet_lt measurable_const (hZ s)).inter
          (measurableSet_lt (measurable_const.add (hLm.comp (hZ s))) measurable_const)
      have hm2 : MeasurableSet {ω | u n < Z s ω ∧ n - s ≤ L (Z s ω)} :=
        (measurableSet_lt measurable_const (hZ s)).inter
          (measurableSet_le measurable_const (hLm.comp (hZ s)))
      have heq : (fun ω => if u n < Z s ω ∧ s + L (Z s ω) < n then (1 : ℝ) else 0) =
          ({ω | u n < Z s ω ∧ s + L (Z s ω) < n}).indicator 1 := by
        ext ω; simp [Set.indicator]
      rw [heq, integral_indicator_one hm1]
      have hunion : {ω | u n < Z s ω} =
          {ω | u n < Z s ω ∧ s + L (Z s ω) < n} ∪ {ω | u n < Z s ω ∧ n - s ≤ L (Z s ω)} := by
        ext ω; simp only [Set.mem_union, mem_ofPred_eq]; constructor
        · intro h; by_cases hlt : s + L (Z s ω) < n
          · exact Or.inl ⟨h, hlt⟩
          · exact Or.inr ⟨h, by omega⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint {ω | u n < Z s ω ∧ s + L (Z s ω) < n}
          {ω | u n < Z s ω ∧ n - s ≤ L (Z s ω)} :=
        Set.disjoint_left.2 fun ω h1 h2 => by
          have : s + L (Z s ω) < n := h1.2
          have : n - s ≤ L (Z s ω) := h2.2
          omega
      have hadd := measureReal_union hdisj hm2 (measure_ne_top P _) (measure_ne_top P _)
      rw [← hunion, hZprob s hun, hZprob_lag] at hadd
      linarith
    rw [integral_add hi1 hi2, h1, h2]; ring
  -- Helper: `u n ^ γ / n → 0` because `γ < α` and `n * u n ^ (-α) → ∞`
  have huγ_div_n : Tendsto (fun n : ℕ => u n ^ γ / (n : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) * u n ^ (-α))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hk
    refine squeeze_zero' ((hu.eventually_ge_atTop 1).mono fun n hn => by positivity) ?_ hinv
    filter_upwards [hu.eventually_ge_atTop 1, hk.eventually_gt_atTop 0] with n hn hkn
    have hn0 : (0 : ℝ) < n := by
      have : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
      nlinarith
    have hγle : u n ^ γ ≤ u n ^ α := Real.rpow_le_rpow_of_exponent_le hn hγα.le
    rw [div_le_iff₀ hn0]
    have heq : ((n : ℝ) * u n ^ (-α))⁻¹ * (n : ℝ) = u n ^ α := by
      rw [mul_inv, mul_comm ((n : ℝ)⁻¹), mul_assoc, inv_mul_cancel₀ hn0.ne', mul_one,
        ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ u n), neg_neg]
    rw [heq]; exact hγle
  -- Step 1: `D n / (2 n uₙ^(-α)) → 1` in probability by Chebyshev
  have hD_lim : TendstoInMeasure P
      (fun n ω => (∑ s ∈ Finset.range n, Y n s ω) / (2 * (n : ℝ) * u n ^ (-α))) atTop (fun _ => 1) := by
    refine tendstoInMeasure_sum_indep_div (N := id) (M := 2) hYm hYbd hindY
      ((hk.eventually_gt_atTop 0).mono fun n hn => by linarith) ?_ ?_
    · -- Mean ratio `→ 1`
      have herr : Tendsto (fun n => (α / (α - γ) + 1) * (u n ^ γ / (n : ℝ)) / 2) atTop (𝓝 0) := by
        simpa using (huγ_div_n.const_mul (α / (α - γ) + 1)).div_const 2
      have h1 : Tendsto (fun n => 1 - (∑ s ∈ Finset.range n, ∫ ω, Y n s ω ∂P) /
          (2 * (n : ℝ) * u n ^ (-α))) atTop (𝓝 0) := by
        refine squeeze_zero' ?_ ?_ herr
        · filter_upwards [hu.eventually_ge_atTop 1, hk.eventually_gt_atTop 0] with n hun hkn
          have hsum_eq : ∑ s ∈ Finset.range n, ∫ ω, Y n s ω ∂P =
              2 * (n : ℝ) * u n ^ (-α) - ∑ s ∈ Finset.range n,
                (paretoMeasure 1 α).real {z | u n < z ∧ n - s ≤ L z} := by
            rw [Finset.sum_congr rfl fun s _ => hY_int n s hun, Finset.sum_sub_distrib,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
          rw [hsum_eq, sub_div, div_self (by linarith : 2 * (n : ℝ) * u n ^ (-α) ≠ 0),
            sub_sub_cancel]
          exact div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (by linarith)
        · filter_upwards [hu.eventually_ge_atTop 1, hk.eventually_gt_atTop 0] with n hun hkn
          have hu0 : 0 < u n := by linarith
          have hsum_eq : ∑ s ∈ Finset.range n, ∫ ω, Y n s ω ∂P =
              2 * (n : ℝ) * u n ^ (-α) - ∑ s ∈ Finset.range n,
                (paretoMeasure 1 α).real {z | u n < z ∧ n - s ≤ L z} := by
            rw [Finset.sum_congr rfl fun s _ => hY_int n s hun, Finset.sum_sub_distrib,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
          rw [hsum_eq, sub_div, div_self (by linarith : 2 * (n : ℝ) * u n ^ (-α) ≠ 0),
            sub_sub_cancel]
          have hbij : ∑ s ∈ Finset.range n, (paretoMeasure 1 α).real {z | u n < z ∧ n - s ≤ L z} =
              ∑ k ∈ Finset.range n, (paretoMeasure 1 α).real {z | u n < z ∧ k + 1 ≤ L z} := by
            refine Finset.sum_bij (fun s _ => n - 1 - s) (fun s hs => Finset.mem_range.2 (by
              have := Finset.mem_range.1 hs; omega))
              (fun s₁ hs₁ s₂ hs₂ h => by
                have := Finset.mem_range.1 hs₁; have := Finset.mem_range.1 hs₂; omega)
              (fun k hk => ⟨n - 1 - k, Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega),
                by have := Finset.mem_range.1 hk; omega⟩)
              (fun s hs => by
                have := Finset.mem_range.1 hs
                congr 1; ext z; simp only [mem_ofPred_eq]
                exact and_congr_right fun _ => by constructor <;> intro hz <;> omega)
          have hsumm : Summable fun k : ℕ => (paretoMeasure 1 α).real {z | u n < z ∧ k + 1 ≤ L z} :=
            (summable_powLag hα hγ hγα).of_nonneg_of_le (fun _ => measureReal_nonneg) fun k =>
              measureReal_mono fun z hz => hz.2
          have hle_tsum : ∑ k ∈ Finset.range n, (paretoMeasure 1 α).real {z | u n < z ∧ k + 1 ≤ L z} ≤
              (α / (α - γ) + 1) * u n ^ (γ - α) :=
            (hsumm.sum_le_tsum (Finset.range n) fun _ _ => measureReal_nonneg).trans
              (tsum_measureReal_gt_and_powLag_ge_le hα hγ hγα hun)
          rw [hbij]
          have heq_r : ((α / (α - γ) + 1) * u n ^ (γ - α)) / (2 * (n : ℝ) * u n ^ (-α)) =
              (α / (α - γ) + 1) * (u n ^ γ / (n : ℝ)) / 2 := by
            have hpow : u n ^ (γ - α) = u n ^ γ * u n ^ (-α) := by
              rw [← Real.rpow_add hu0, sub_eq_add_neg]
            have hua : u n ^ (-α) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
            have hn0 : (n : ℝ) ≠ 0 := by
              have : 0 < u n ^ (-α) := Real.rpow_pos_of_pos hu0 _
              intro h0; rw [h0, zero_mul] at hkn; linarith
            rw [hpow]; field_simp [hua, hn0]
          rw [← heq_r]
          exact div_le_div_of_nonneg_right hle_tsum (by linarith)
      have := h1.const_sub 1
      simpa using this
    · -- Variance ratio `≤ 4 n uₙ^(-α) / (2 n uₙ^(-α))² = 1 / (n uₙ^(-α)) → 0`
      have hinv : Tendsto (fun n : ℕ => ((n : ℝ) * u n ^ (-α))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hk
      refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
        (Finset.sum_nonneg fun s _ => integral_nonneg fun ω => sq_nonneg _) (sq_nonneg _)) ?_ hinv
      filter_upwards [hu.eventually_ge_atTop 1, hk.eventually_gt_atTop 0] with n hun hkn
      have hterm : ∀ s ∈ Finset.range n, ∫ ω, (Y n s ω) ^ 2 ∂P ≤ 4 * u n ^ (-α) := fun s _ => by
        have hle : ∀ ω, (Y n s ω) ^ 2 ≤ 4 * (if u n < Z s ω then (1 : ℝ) else 0) := fun ω => by
          by_cases h1 : u n < Z s ω <;> by_cases h2 : s + L (Z s ω) < n <;> simp [Y, h1, h2]; norm_num
        have hi : Integrable (fun ω => 4 * (if u n < Z s ω then (1 : ℝ) else 0)) P :=
          (Integrable.of_bound (Measurable.ite (measurableSet_lt measurable_const (hZ s))
            measurable_const measurable_const).aestronglyMeasurable 1
            (ae_of_all _ fun ω => by split_ifs <;> norm_num)).const_mul 4
        have hiY2 : Integrable (fun ω => (Y n s ω) ^ 2) P :=
          Integrable.of_bound ((hYm n s).pow_const 2).aestronglyMeasurable 4
            (ae_of_all _ fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              nlinarith [(hYbd n s ω).1, (hYbd n s ω).2])
        have hm := integral_mono hiY2 hi hle
        rw [integral_const_mul] at hm
        have h1 : ∫ ω, (if u n < Z s ω then (1 : ℝ) else 0) ∂P = u n ^ (-α) := by
          have heq : (fun ω => if u n < Z s ω then (1 : ℝ) else 0) =
              ({ω | u n < Z s ω}).indicator 1 := by
            ext ω; simp [Set.indicator]
          rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hZ s)), hZprob s hun]
        linarith
      have hsum_le : ∑ s ∈ Finset.range n, ∫ ω, (Y n s ω) ^ 2 ∂P ≤ 4 * (n : ℝ) * u n ^ (-α) := by
        have := Finset.sum_le_sum hterm
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
        linarith
      calc (∑ s ∈ Finset.range n, ∫ ω, (Y n s ω) ^ 2 ∂P) / (2 * (n : ℝ) * u n ^ (-α)) ^ 2
          ≤ (4 * (n : ℝ) * u n ^ (-α)) / (2 * (n : ℝ) * u n ^ (-α)) ^ 2 :=
            div_le_div_of_nonneg_right hsum_le (sq_nonneg _)
        _ = ((n : ℝ) * u n ^ (-α))⁻¹ := by field_simp [hkn.ne']; ring
  -- Step 2: `|tailCount - D| / (2 n uₙ^(-α)) → 0` in `L¹` (hence in probability)
  set diff : ℕ → Ω → ℝ := fun n ω =>
    |(tailCount X n (u n) ω : ℝ) - ∑ s ∈ Finset.range n, Y n s ω| / (2 * (n : ℝ) * u n ^ (-α))
  have hdiff_lim : TendstoInMeasure P diff atTop (fun _ => 0) := by
    -- Pointwise bound: `|Nₙ - Dₙ| ≤ I_pre + C_n`
    -- `I_pre` = `#{i < n : ∃ s < 0, s + L(Z_s) = i ∧ Z_s > uₙ}`
    -- `C_n` = `∑_{i < n} c_i (c_i - 1)` where `c_i = ∑_{s ≤ i} 1_{Z_s > uₙ ∧ (s = i ∨ s + L(Z_s) = i)}`
    set c : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      ∑ s ∈ Finset.range (i + 1), if u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i) then (1 : ℝ) else 0
    set pre : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n, if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
        then (1 : ℝ) else 0
    have hpre_m : ∀ n, Measurable (pre n) := fun n =>
      Finset.measurable_sum _ fun i _ => by
        have hset : MeasurableSet {ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω} := by
          have heq : {ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω} =
              ⋃ k : ℕ, {ω | -((k + 1 : ℕ) : ℤ) + (L (Z (-(k + 1 : ℕ) : ℤ) ω) : ℤ) = (i : ℤ) ∧
                u n < Z (-(k + 1 : ℕ) : ℤ) ω} := by
            ext ω; simp only [mem_ofPred_eq, mem_iUnion]; constructor
            · rintro ⟨s, hs, h1, h2⟩
              have hseq : -((((-s - 1).toNat + 1 : ℕ) : ℤ)) = s := by omega
              refine ⟨(-s - 1).toNat, ?_, ?_⟩
              · rw [hseq]; exact h1
              · rw [hseq]; exact h2
            · rintro ⟨k, h1, h2⟩; exact ⟨-((k + 1 : ℕ) : ℤ), by omega, h1, h2⟩
          rw [heq]
          refine MeasurableSet.iUnion fun k => ?_
          exact (measurableSet_eq_fun (measurable_const.add
            ((measurable_from_top : Measurable (Nat.cast : ℕ → ℤ)).comp (hLm.comp (hZ _))))
            measurable_const).inter (measurableSet_lt measurable_const (hZ _))
        exact Measurable.ite hset measurable_const measurable_const
    have hc_m : ∀ n i, Measurable (c n i) := fun n i =>
      Finset.measurable_sum _ fun s _ =>
        Measurable.ite ((measurableSet_lt measurable_const (hZ s)).inter
          ((measurableSet_eq_fun measurable_const measurable_const).union
            (measurableSet_eq_fun (measurable_const.add (hLm.comp (hZ s))) measurable_const)))
          measurable_const measurable_const
    have hdiff_m : ∀ n, Measurable (diff n) := fun n => by
      have htc : Measurable (tailCount X n (u n)) := measurable_tailCount (fun t => hXm t) n (u n)
      exact ((htc.sub (Finset.measurable_sum _ fun s _ => hYm n s)).abs).div_const _
    have hpt_le : ∀ n ω, 0 ≤ u n → (∀ t, BddAbove (range fun j => echoTerm L Z t j ω)) →
        |tailCount X n (u n) ω - ∑ s ∈ Finset.range n, Y n s ω| ≤
          pre n ω + ∑ i ∈ Finset.range n, c n i ω * (c n i ω - 1) := fun n ω hun0 hb => by
      have hsum_c : ∑ i ∈ Finset.range n, c n i ω = ∑ s ∈ Finset.range n, Y n s ω := by
        simp only [c, Y]
        -- Swap sums over `i < n` and `s ≤ i`
        have h1 : ∀ i ∈ Finset.range n,
            ∑ s ∈ Finset.range (i + 1),
              (if u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i) then (1 : ℝ) else 0) =
            ∑ s ∈ Finset.range n,
              (if u n < Z s ω ∧ s = i then (1 : ℝ) else 0) +
            ∑ s ∈ Finset.range n,
              (if u n < Z s ω ∧ s + L (Z s ω) = i then (1 : ℝ) else 0) := fun i hi => by
          rw [← Finset.sum_add_distrib]
          have hle_n : i + 1 ≤ n := by have := Finset.mem_range.1 hi; omega
          rw [← Finset.sum_subset (Finset.range_mono hle_n)]
          · refine Finset.sum_congr rfl fun s _ => ?_
            have hL1 : 1 ≤ L (Z s ω) := one_le_powLag γ (Z s ω)
            by_cases hzu : u n < Z s ω
            · by_cases hsi : s = i
              · subst hsi
                simp [hzu]
                have := one_le_powLag γ (Z (s : ℤ) ω)
                omega
              · by_cases hli : s + L (Z s ω) = i
                · simp [hzu, hsi, hli]
                · simp [hzu, hsi, hli]
            · simp [hzu]
          · intro s hs hnot
            have hsi : ¬ s = i := by simp at hs hnot; omega
            have hli : ¬ s + L (Z s ω) = i := by
              have := one_le_powLag γ (Z s ω); simp at hs hnot; omega
            simp [hsi, hli]
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
        rw [Finset.sum_comm (s := Finset.range n) (t := Finset.range n)
          (f := fun i s => if u n < Z s ω ∧ s = i then (1 : ℝ) else 0)]
        rw [Finset.sum_comm (s := Finset.range n) (t := Finset.range n)
          (f := fun i s => if u n < Z s ω ∧ s + L (Z s ω) = i then (1 : ℝ) else 0)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsn : s < n := Finset.mem_range.1 hs
        have hA : ∑ i ∈ Finset.range n, (if u n < Z s ω ∧ s = i then (1 : ℝ) else 0) =
            if u n < Z s ω then 1 else 0 := by
          by_cases hzu : u n < Z s ω
          · simp [hzu, Finset.mem_range.2 hsn]
          · simp [hzu]
        have hB : ∑ i ∈ Finset.range n, (if u n < Z s ω ∧ s + L (Z s ω) = i then (1 : ℝ) else 0) =
            if u n < Z s ω ∧ s + L (Z s ω) < n then 1 else 0 := by
          by_cases hzu : u n < Z s ω
          · by_cases hlt : s + L (Z s ω) < n
            · simp [hzu, hlt]
            · simp only [hzu, hlt, and_false, ↓reduceIte, true_and]
              exact Finset.sum_eq_zero fun i hi => by
                have : i < n := Finset.mem_range.1 hi
                simp [show s + L (Z s ω) ≠ i by omega]
          · simp [hzu]
        rw [hA, hB]
      -- Now compare each index `i < n`: `1_{c_i ≥ 1} ≤ 1_{X_i > uₙ} ≤ 1_{c_i ≥ 1} + 1_{pre_i}`
      have htc_eq : tailCount X n (u n) ω =
          ∑ i ∈ Finset.range n, if u n < X i ω then (1 : ℝ) else 0 := rfl
      have hci_nat : ∀ i, ∃ k : ℕ, c n i ω = (k : ℝ) := fun i =>
        ⟨((Finset.range (i + 1)).filter fun s : ℕ => u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i)).card,
          Finset.sum_boole (R := ℝ) (s := Finset.range (i + 1))
            (p := fun s : ℕ => u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i))⟩
      have hupper : ∀ i ∈ Finset.range n,
          (if u n < X i ω then (1 : ℝ) else 0) ≤
            c n i ω + (if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
              then (1 : ℝ) else 0) := fun i _ => by
        by_cases hXi : u n < X i ω
        · simp only [hXi, ↓reduceIte]
          have hmem : u n < Z (i : ℤ) ω ∨ ∃ s : ℤ, s < (i : ℤ) ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧
              u n < Z s ω := by
            have hX_def : X i ω = echoProcess L Z i ω := rfl
            rw [hX_def] at hXi
            obtain ⟨j, h1, h2⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (L := L) (Z := Z) hun0 (i : ℤ) hXi)
            rcases h2 with rfl | hjL
            · left; simpa using h1
            · right
              have hL1 : 1 ≤ L (Z ((i : ℤ) - j) ω) := one_le_powLag γ _
              have hj1 : 1 ≤ j := by rw [← hjL]; exact hL1
              refine ⟨(i : ℤ) - j, ?_, ?_, h1⟩
              · omega
              · rw [hjL]; omega
          rcases hmem with hZi | ⟨s, hsi, hsL, hZs⟩
          · have hc1 : 1 ≤ c n i ω := by
              have hle := Finset.single_le_sum (s := Finset.range (i + 1)) (f := fun s : ℕ =>
                  if u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i) then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_range.2 (Nat.lt_succ_self i))
              simpa [c, hZi] using hle
            have hnn : 0 ≤ (if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
                then (1 : ℝ) else 0) := by split_ifs <;> norm_num
            linarith
          · rcases lt_or_ge s 0 with hs0 | hs0
            · have hp1 : (if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
                  then (1 : ℝ) else 0) = 1 := ite_eq_left ⟨s, hs0, hsL, hZs⟩
              have hc0 : 0 ≤ c n i ω := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
              linarith
            · lift s to ℕ using hs0
              have hc1 : 1 ≤ c n i ω := by
                have hsle : s ∈ Finset.range (i + 1) := Finset.mem_range.2 (by omega)
                have hle := Finset.single_le_sum (s := Finset.range (i + 1)) (f := fun t : ℕ =>
                    if u n < Z t ω ∧ (t = i ∨ t + L (Z t ω) = i) then (1 : ℝ) else 0)
                  (fun _ _ => by split_ifs <;> norm_num) hsle
                have hsL' : s + L (Z (s : ℤ) ω) = i := by omega
                simpa [c, hZs, hsL'] using hle
              have hnn : 0 ≤ (if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
                  then (1 : ℝ) else 0) := by split_ifs <;> norm_num
              linarith
        · simp only [hXi, ↓reduceIte]
          have hc0 : 0 ≤ c n i ω := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
          have hnn : 0 ≤ (if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
              then (1 : ℝ) else 0) := by split_ifs <;> norm_num
          linarith
      have hlower : ∀ i ∈ Finset.range n,
          c n i ω - (if u n < X i ω then (1 : ℝ) else 0) ≤ c n i ω * (c n i ω - 1) := fun i _ => by
        obtain ⟨k, hk_eq⟩ := hci_nat i
        rw [hk_eq]
        have hge : (if 1 ≤ k then (1 : ℝ) else 0) ≤ if u n < X i ω then (1 : ℝ) else 0 := by
          split_ifs with h1 h2
          · exact le_rfl
          · exfalso; apply h2
            have hpos_c : (0 : ℝ) < c n i ω := by rw [hk_eq]; exact_mod_cast h1
            obtain ⟨s, hs, hspos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos_c.ne'
            have hcond : u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i) := by
              by_contra h; exact hspos (ite_eq_right h)
            have hX_def : X i ω = echoProcess L Z i ω := rfl
            rw [hX_def]
            rcases hcond.2 with hsi | hli
            · subst hsi; exact lt_of_lt_of_le hcond.1 (le_echoProcess (L := L) (s : ℤ) ω)
            · have hmem : ω ∈ echoSource L Z (i : ℤ) (u n) (L (Z s ω)) := by
                simp only [echoSource, mem_ofPred_eq]
                have heq_sub : (i : ℤ) - (L (Z s ω) : ℤ) = (s : ℤ) := by omega
                rw [heq_sub]
                exact ⟨hcond.1, Or.inr rfl⟩
              exact lt_echoProcess_of_mem_echoSource (hb (i : ℤ)) hmem
          · norm_num
          · exact le_rfl
        linarith [nat_sub_ind_le_mul_sub_one k]
      have hup_sum : (tailCount X n (u n) ω : ℝ) - ∑ s ∈ Finset.range n, Y n s ω ≤ pre n ω := by
        rw [htc_eq, ← hsum_c]
        have h := Finset.sum_le_sum hupper
        rw [Finset.sum_add_distrib] at h
        linarith
      have hlo_sum : ∑ s ∈ Finset.range n, Y n s ω - (tailCount X n (u n) ω : ℝ) ≤
          ∑ i ∈ Finset.range n, c n i ω * (c n i ω - 1) := by
        rw [htc_eq, ← hsum_c, ← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum hlower
      have hpre0 : 0 ≤ pre n ω := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
      have hcol0 : 0 ≤ ∑ i ∈ Finset.range n, c n i ω * (c n i ω - 1) :=
        Finset.sum_nonneg fun i _ => by
          obtain ⟨k, hk_eq⟩ := hci_nat i
          rw [hk_eq]
          rcases k with _ | k
          · simp
          · have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
            nlinarith
      rw [abs_le]
      constructor <;> linarith
    -- Bound `E[pre n] ≤ (α/(α-γ) + 1) uₙ^(γ - α)` and `E[∑ c_i(c_i - 1)] ≤ 4 n uₙ^(-2α)`
    have hE_pre : ∀ n, 1 ≤ u n →
        ∫ ω, pre n ω ∂P ≤ (α / (α - γ) + 1) * u n ^ (γ - α) := fun n hun => by
      have hterm : ∀ i ∈ Finset.range n,
          ∫ ω, (if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
            then (1 : ℝ) else 0) ∂P ≤
          (paretoMeasure 1 α).real {z | u n < z ∧ i + 1 ≤ L z} := fun i _ => by
        have hset : MeasurableSet {ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω} := by
          have heq : {ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω} =
              ⋃ k : ℕ, {ω | -((k + 1 : ℕ) : ℤ) + (L (Z (-(k + 1 : ℕ) : ℤ) ω) : ℤ) = (i : ℤ) ∧
                u n < Z (-(k + 1 : ℕ) : ℤ) ω} := by
            ext ω; simp only [mem_ofPred_eq, mem_iUnion]; constructor
            · rintro ⟨s, hs, h1, h2⟩
              have hseq : -((((-s - 1).toNat + 1 : ℕ) : ℤ)) = s := by omega
              refine ⟨(-s - 1).toNat, ?_, ?_⟩
              · rw [hseq]; exact h1
              · rw [hseq]; exact h2
            · rintro ⟨k, h1, h2⟩; exact ⟨-((k + 1 : ℕ) : ℤ), by omega, h1, h2⟩
          rw [heq]
          refine MeasurableSet.iUnion fun k =>
            (measurableSet_eq_fun (measurable_const.add
              ((measurable_from_top : Measurable (Nat.cast : ℕ → ℤ)).comp (hLm.comp (hZ _))))
              measurable_const).inter (measurableSet_lt measurable_const (hZ _))
        have heq_ind : (fun ω => if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
            then (1 : ℝ) else 0) =
            ({ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω}).indicator 1 := by
          ext ω; simp [Set.indicator]
        rw [heq_ind, integral_indicator_one hset]
        have hsub : {ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω} ⊆
            ⋃ k : ℕ, {ω | u n < Z (-(k + 1 : ℕ) : ℤ) ω ∧ L (Z (-(k + 1 : ℕ) : ℤ) ω) = i + k + 1} := by
          intro ω ⟨s, hs, h1, h2⟩
          refine mem_iUnion.2 ⟨(-s - 1).toNat, ?_⟩
          have hseq : (-((-s - 1).toNat + 1 : ℕ) : ℤ) = s := by omega
          rw [hseq]; exact ⟨h2, by omega⟩
        have hle_enn : P {ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω} ≤
            ∑' k : ℕ, (paretoMeasure 1 α) {z | u n < z ∧ L z = i + k + 1} := by
          refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
          refine ENNReal.tsum_le_tsum fun k => le_of_eq ?_
          have hm : MeasurableSet {z : ℝ | u n < z ∧ L z = i + k + 1} :=
            measurableSet_Ioi.inter (measurableSet_eq_fun hLm measurable_const)
          rw [← hlaw (-(k + 1 : ℕ) : ℤ), Measure.map_apply (hZ _) hm]; rfl
        have hdisj : Pairwise fun k₁ k₂ : ℕ =>
            Disjoint {z : ℝ | u n < z ∧ L z = i + k₁ + 1} {z : ℝ | u n < z ∧ L z = i + k₂ + 1} :=
          fun k₁ k₂ hne => Set.disjoint_left.2 fun z h1 h2 => by
            have e1 : L z = i + k₁ + 1 := h1.2
            have e2 : L z = i + k₂ + 1 := h2.2
            omega
        have hunion : (⋃ k : ℕ, {z : ℝ | u n < z ∧ L z = i + k + 1}) =
            {z : ℝ | u n < z ∧ i + 1 ≤ L z} := by
          ext z; simp only [mem_iUnion, mem_ofPred_eq]; constructor
          · rintro ⟨k, h1, h2⟩; exact ⟨h1, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨L z - (i + 1), h1, by omega⟩
        rw [← measure_iUnion hdisj fun k => measurableSet_Ioi.inter (measurableSet_eq_fun hLm measurable_const),
          hunion] at hle_enn
        exact ENNReal.toReal_mono (measure_ne_top _ _) hle_enn
      rw [integral_finsetSum _ fun i _ => Integrable.of_bound
        (Measurable.ite (by
          have heq : {ω | ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω} =
              ⋃ k : ℕ, {ω | -((k + 1 : ℕ) : ℤ) + (L (Z (-(k + 1 : ℕ) : ℤ) ω) : ℤ) = (i : ℤ) ∧
                u n < Z (-(k + 1 : ℕ) : ℤ) ω} := by
            ext ω; simp only [mem_ofPred_eq, mem_iUnion]; constructor
            · rintro ⟨s, hs, h1, h2⟩
              have hseq : -((((-s - 1).toNat + 1 : ℕ) : ℤ)) = s := by omega
              refine ⟨(-s - 1).toNat, ?_, ?_⟩
              · rw [hseq]; exact h1
              · rw [hseq]; exact h2
            · rintro ⟨k, h1, h2⟩; exact ⟨-((k + 1 : ℕ) : ℤ), by omega, h1, h2⟩
          rw [heq]
          exact MeasurableSet.iUnion fun k =>
            (measurableSet_eq_fun (measurable_const.add
              ((measurable_from_top : Measurable (Nat.cast : ℕ → ℤ)).comp (hLm.comp (hZ _))))
              measurable_const).inter (measurableSet_lt measurable_const (hZ _)))
          measurable_const measurable_const).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by split_ifs <;> norm_num)]
      have hsumm : Summable fun i : ℕ => (paretoMeasure 1 α).real {z | u n < z ∧ i + 1 ≤ L z} :=
        (summable_powLag hα hγ hγα).of_nonneg_of_le (fun _ => measureReal_nonneg) fun i =>
          measureReal_mono fun z hz => hz.2
      exact (Finset.sum_le_sum hterm).trans
        ((hsumm.sum_le_tsum (Finset.range n) fun _ _ => measureReal_nonneg).trans
          (tsum_measureReal_gt_and_powLag_ge_le hα hγ hγα hun))
    have hE_col : ∀ n, 1 ≤ u n →
        ∫ ω, (∑ i ∈ Finset.range n, c n i ω * (c n i ω - 1)) ∂P ≤ 4 * (n : ℝ) * (u n ^ (-α)) ^ 2 :=
      fun n hun => by
      have hci_int : ∀ i ∈ Finset.range n,
          Integrable (fun ω => c n i ω * (c n i ω - 1)) P := fun i _ =>
        Integrable.of_bound ((hc_m n i).mul ((hc_m n i).sub_const 1)).aestronglyMeasurable
          (((i + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ)) (ae_of_all _ fun ω => by
            have h0 : 0 ≤ c n i ω := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
            have h1 : c n i ω ≤ (i + 1 : ℕ) := by
              have := Finset.sum_le_sum (s := Finset.range (i + 1)) fun s _ =>
                (show (if u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i) then (1 : ℝ) else 0) ≤ 1 by
                  split_ifs <;> norm_num)
              simpa [c] using this
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
            have h2 : |c n i ω - 1| ≤ (i + 1 : ℕ) := by
              rw [abs_le]; constructor <;> linarith [show (1 : ℝ) ≤ (i + 1 : ℕ) by exact_mod_cast Nat.succ_pos i]
            exact mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _))
      rw [integral_finsetSum _ hci_int]
      have hterm : ∀ i ∈ Finset.range n,
          ∫ ω, c n i ω * (c n i ω - 1) ∂P ≤ 4 * (u n ^ (-α)) ^ 2 := fun i _ => by
        set I : ℕ → Ω → ℝ := fun s ω =>
          if u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i) then 1 else 0
        have hIm : ∀ s, Measurable (I s) := fun s =>
          Measurable.ite ((measurableSet_lt measurable_const (hZ s)).inter
            ((measurableSet_eq_fun measurable_const measurable_const).union
              (measurableSet_eq_fun (measurable_const.add (hLm.comp (hZ s))) measurable_const)))
            measurable_const measurable_const
        have hindI : iIndepFun I P := by
          have hindNat : iIndepFun (fun s : ℕ => Z (s : ℤ)) P := hind.precomp Nat.cast_injective
          refine hindNat.comp (fun s z => if u n < z ∧ (s = i ∨ s + L z = i) then (1 : ℝ) else 0)
            fun s => Measurable.ite (measurableSet_Ioi.inter
              ((measurableSet_eq_fun measurable_const measurable_const).union
                (measurableSet_eq_fun (measurable_const.add hLm) measurable_const)))
              measurable_const measurable_const
        have hcol := integral_mul_sub_one_le_sq (Finset.range (i + 1)) hIm
          (fun s ω => by simp only [I]; split_ifs <;> simp) hindI
        have hsumI : ∑ s ∈ Finset.range (i + 1), ∫ ω, I s ω ∂P ≤ 2 * u n ^ (-α) := by
          rw [Finset.sum_range_succ]
          have hlast : ∫ ω, I i ω ∂P = u n ^ (-α) := by
            have heq : I i = ({ω | u n < Z i ω}).indicator 1 := by
              ext ω; simp [I, Set.indicator]
            rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hZ i)), hZprob i hun]
          have hprev : ∑ s ∈ Finset.range i, ∫ ω, I s ω ∂P ≤ u n ^ (-α) := by
            have hpt : ∀ s ∈ Finset.range i, ∫ ω, I s ω ∂P =
                (paretoMeasure 1 α).real {z | u n < z ∧ L z = i - s} := fun s hs => by
              have hsi : s < i := Finset.mem_range.1 hs
              have hset : MeasurableSet {z : ℝ | u n < z ∧ L z = i - s} :=
                measurableSet_Ioi.inter (measurableSet_eq_fun hLm measurable_const)
              have heq : I s = (Z s ⁻¹' {z | u n < z ∧ L z = i - s}).indicator 1 := by
                ext ω; simp only [I, Set.indicator, Set.mem_preimage, mem_ofPred_eq, Pi.one_apply]
                have hiff : (u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i)) ↔
                    (u n < Z s ω ∧ L (Z s ω) = i - s) :=
                  and_congr_right fun _ => by omega
                simp only [hiff]
              rw [heq, integral_indicator_one (hZ s hset), measureReal_def,
                ← Measure.map_apply (hZ s) hset, hlaw s, ← measureReal_def]
            rw [Finset.sum_congr rfl hpt]
            have hdisj : Set.PairwiseDisjoint (Finset.range i : Set ℕ)
                (fun s => {z : ℝ | u n < z ∧ L z = i - s}) := by
              intro s₁ hs₁ s₂ hs₂ hne
              rw [Finset.mem_coe, Finset.mem_range] at hs₁ hs₂
              exact Set.disjoint_left.2 fun z h1 h2 => by
                have e1 : L z = i - s₁ := h1.2
                have e2 : L z = i - s₂ := h2.2
                omega
            rw [← measureReal_biUnion_finset hdisj (fun s _ =>
              measurableSet_Ioi.inter (measurableSet_eq_fun hLm measurable_const))]
            have hsub_u : (⋃ s ∈ Finset.range i, {z : ℝ | u n < z ∧ L z = i - s}) ⊆ Ioi (u n) :=
              iUnion₂_subset fun _ _ z hz => hz.1
            exact (measureReal_mono hsub_u).trans_eq (paretoMeasure_one_real_Ioi hα hun)
          linarith
        have hnn : 0 ≤ ∑ s ∈ Finset.range (i + 1), ∫ ω, I s ω ∂P :=
          Finset.sum_nonneg fun s _ => integral_nonneg fun ω => by simp only [I]; split_ifs <;> norm_num
        calc ∫ ω, c n i ω * (c n i ω - 1) ∂P
            ≤ (∑ s ∈ Finset.range (i + 1), ∫ ω, I s ω ∂P) ^ 2 := hcol
          _ ≤ (2 * u n ^ (-α)) ^ 2 := pow_le_pow_left₀ hnn hsumI 2
          _ = 4 * (u n ^ (-α)) ^ 2 := by ring
      have := Finset.sum_le_sum hterm
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      linarith
    -- Apply Markov on `|diff n|` (which equals `diff n` eventually since `2 n uₙ^(-α) > 0`)
    have habs_lim : TendstoInMeasure P (fun n ω => |diff n ω|) atTop (fun _ => 0) := by
      refine tendstoInMeasure_zero_of_tendsto_integral_nonneg (fun _ _ => abs_nonneg _) (fun n => ?_) ?_
      · refine Integrable.of_bound (hdiff_m n).abs.aestronglyMeasurable
          ((3 * (n : ℝ)) / |2 * (n : ℝ) * u n ^ (-α)|) (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs, abs_abs, abs_div, abs_abs]
        refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
        have htc_le : tailCount X n (u n) ω ≤ (n : ℝ) := by
          have := Finset.sum_le_sum (s := Finset.range n) fun i _ =>
            (show (if u n < X i ω then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
          simpa [tailCount] using this
        have hD_le : ∑ s ∈ Finset.range n, Y n s ω ≤ 2 * (n : ℝ) := by
          have := Finset.sum_le_sum (s := Finset.range n) fun s _ => (hYbd n s ω).2
          simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using this
        have hD_0 : 0 ≤ ∑ s ∈ Finset.range n, Y n s ω := Finset.sum_nonneg fun s _ => (hYbd n s ω).1
        rw [abs_le]; constructor <;> linarith [tailCount_nonneg (X := X) n (u n) ω]
      · -- `∫ |diff n| → 0`
        have hlim_rhs : Tendsto (fun n : ℕ =>
            (α / (α - γ) + 1) * (u n ^ γ / (n : ℝ)) / 2 + 2 * u n ^ (-α)) atTop (𝓝 0) := by
          have h1 : Tendsto (fun n : ℕ => (α / (α - γ) + 1) * (u n ^ γ / (n : ℝ)) / 2) atTop (𝓝 0) := by
            simpa using (huγ_div_n.const_mul (α / (α - γ) + 1)).div_const 2
          have h2 : Tendsto (fun n : ℕ => 2 * u n ^ (-α)) atTop (𝓝 0) := by
            simpa using ((tendsto_rpow_neg_atTop hα).comp hu).const_mul 2
          simpa using h1.add h2
        refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun _ => abs_nonneg _) ?_ hlim_rhs
        filter_upwards [hu.eventually_ge_atTop 1, hk.eventually_gt_atTop 0] with n hun hkn
        have hu0 : 0 < u n := by linarith
        have hden : 0 < 2 * (n : ℝ) * u n ^ (-α) := by linarith
        have hpre_int : Integrable (pre n) P :=
          Integrable.of_bound (hpre_m n).aestronglyMeasurable (n : ℝ) (ae_of_all _ fun ω => by
            have h0 : 0 ≤ pre n ω := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
            have h1 : pre n ω ≤ n := by
              have := Finset.sum_le_sum (s := Finset.range n) fun i _ =>
                (show (if ∃ s : ℤ, s < 0 ∧ s + (L (Z s ω) : ℤ) = (i : ℤ) ∧ u n < Z s ω
                  then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
              simpa [pre] using this
            rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
        have hcol_int : Integrable (fun ω => ∑ i ∈ Finset.range n, c n i ω * (c n i ω - 1)) P :=
          integrable_finsetSum _ fun i _ =>
            Integrable.of_bound ((hc_m n i).mul ((hc_m n i).sub_const 1)).aestronglyMeasurable
              (((i + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ)) (ae_of_all _ fun ω => by
                have h0 : 0 ≤ c n i ω := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
                have h1 : c n i ω ≤ (i + 1 : ℕ) := by
                  have := Finset.sum_le_sum (s := Finset.range (i + 1)) fun s _ =>
                    (show (if u n < Z s ω ∧ (s = i ∨ s + L (Z s ω) = i) then (1 : ℝ) else 0) ≤ 1 by
                      split_ifs <;> norm_num)
                  simpa [c] using this
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
                have h2 : |c n i ω - 1| ≤ (i + 1 : ℕ) := by
                  rw [abs_le]; constructor <;>
                    linarith [show (1 : ℝ) ≤ (i + 1 : ℕ) by exact_mod_cast Nat.succ_pos i]
                exact mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _))
        have hint_diff : Integrable (fun ω => |diff n ω|) P := by
          refine Integrable.of_bound (hdiff_m n).abs.aestronglyMeasurable
            ((3 * (n : ℝ)) / |2 * (n : ℝ) * u n ^ (-α)|) (ae_of_all _ fun ω => ?_)
          rw [Real.norm_eq_abs, abs_abs, abs_div, abs_abs]
          refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
          have htc_le : tailCount X n (u n) ω ≤ (n : ℝ) := by
            have := Finset.sum_le_sum (s := Finset.range n) fun i _ =>
              (show (if u n < X i ω then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
            simpa [tailCount] using this
          have hD_le : ∑ s ∈ Finset.range n, Y n s ω ≤ 2 * (n : ℝ) := by
            have := Finset.sum_le_sum (s := Finset.range n) fun s _ => (hYbd n s ω).2
            simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using this
          have hD_0 : 0 ≤ ∑ s ∈ Finset.range n, Y n s ω := Finset.sum_nonneg fun s _ => (hYbd n s ω).1
          rw [abs_le]; constructor <;> linarith [tailCount_nonneg (X := X) n (u n) ω]
        have hmono : ∫ ω, |diff n ω| ∂P ≤
            (∫ ω, pre n ω ∂P + ∫ ω, (∑ i ∈ Finset.range n, c n i ω * (c n i ω - 1)) ∂P) /
              (2 * (n : ℝ) * u n ^ (-α)) := by
          rw [← integral_add hpre_int hcol_int, ← integral_div]
          refine integral_mono_ae hint_diff ((hpre_int.add hcol_int).div_const _) ?_
          filter_upwards [ae_bddAbove_echoTerm hα hZ hlaw hLm] with ω hb
          simp only [diff, abs_div, abs_abs, abs_of_pos hden]
          exact div_le_div_of_nonneg_right (hpt_le n ω (by linarith) hb) hden.le
        have hsum_bd := add_le_add (hE_pre n hun) (hE_col n hun)
        have hdiv_bd : ((α / (α - γ) + 1) * u n ^ (γ - α) + 4 * (n : ℝ) * (u n ^ (-α)) ^ 2) /
            (2 * (n : ℝ) * u n ^ (-α)) =
            (α / (α - γ) + 1) * (u n ^ γ / (n : ℝ)) / 2 + 2 * u n ^ (-α) := by
          have hpow : u n ^ (γ - α) = u n ^ γ * u n ^ (-α) := by
            rw [← Real.rpow_add hu0, sub_eq_add_neg]
          have hua : u n ^ (-α) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
          have hn0 : (n : ℝ) ≠ 0 := by
            intro h0; rw [h0, zero_mul] at hkn; linarith
          rw [hpow]; field_simp [hua, hn0]; ring
        exact hmono.trans ((div_le_div_of_nonneg_right hsum_bd hden.le).trans_eq hdiv_bd)
    rw [tendstoInMeasure_iff_norm] at habs_lim ⊢
    intro ε hε
    simpa [Real.norm_eq_abs] using habs_lim ε hε
  -- Combine `D / (2 n uₙ^(-α)) → 1` and `|N - D| / (2 n uₙ^(-α)) → 0`
  rw [tendstoInMeasure_iff_norm] at hD_lim hdiff_lim ⊢
  intro ε hε
  have hsum : Tendsto (fun n => P {ω | ε / 2 ≤ ‖(∑ s ∈ Finset.range n, Y n s ω) /
        (2 * (n : ℝ) * u n ^ (-α)) - 1‖} +
      P {ω | ε / 2 ≤ ‖diff n ω - 0‖}) atTop (𝓝 0) := by
    simpa using (hD_lim (ε / 2) (by positivity)).add (hdiff_lim (ε / 2) (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn
  have hden : 0 < 2 * (n : ℝ) * u n ^ (-α) := by linarith
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  by_contra hnot
  simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs, sub_zero] at hω hnot
  have h1 : |tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)) -
      (∑ s ∈ Finset.range n, Y n s ω) / (2 * (n : ℝ) * u n ^ (-α))| < ε / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hden]
    have hdiff_nn : 0 ≤ diff n ω := div_nonneg (abs_nonneg _) hden.le
    simpa [diff, abs_of_nonneg hdiff_nn] using hnot.2
  have htri := abs_sub_le (tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)))
    ((∑ s ∈ Finset.range n, Y n s ω) / (2 * (n : ℝ) * u n ^ (-α))) 1
  linarith

include hα hZ hind hlaw hpos in
/-- **Short runs are inconsistent for the power-lag echo process** (for ALL `0 < γ < α`):
at intermediate thresholds `uₙ → ∞`, `n uₙ^(-α) → ∞`, if `rₙ → ∞`, `rₙ / n → 0`,
`rₙ uₙ^(-α) → 0`, and `rₙ / uₙ^γ → 0`, then the runs estimator converges in probability to
`1 = ϑ ≠ 1/2 = θ`. -/
theorem powEcho_tendstoInMeasure_runsEstimator (hγ : 0 < γ) (hγα : γ < α) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) (hk : Tendsto (fun n : ℕ => (n : ℝ) * u n ^ (-α)) atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop (𝓝 0))
    (hrb : Tendsto (fun n : ℕ => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hshort : Tendsto (fun n : ℕ => (r n : ℝ) / u n ^ γ) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => runsEstimator (fun k : ℕ => echoProcess (powLag γ) Z k) n
      (r n) (u n)) atTop (fun _ => 1) := by
  set X : ℕ → Ω → ℝ := fun k => echoProcess (powLag γ) Z k
  have hXm : ∀ t, Measurable (echoProcess (powLag γ) Z t) :=
    measurable_echoProcess hZ (measurable_powLag γ)
  have hstat := hasShiftInvariantWindows_echoProcess hZ hind hlaw (measurable_powLag γ)
  have hXeq : X = fun k : ℕ => |echoProcess (powLag γ) Z k| := by
    funext k ω; exact (abs_of_nonneg (echoProcess_nonneg hpos _ ω)).symm
  have hs : IsStationary X P := by
    rw [hXeq]; exact hstat.isStationary_abs hXm
  -- Step 1: `Nₙ / (2 n uₙ^(-α)) → 1` in probability
  have hN := powEcho_tendstoInMeasure_tailCount_div hα hZ hind hlaw hγ hγα hu hk
  -- Step 2: `P(X₀ > uₙ) / uₙ^(-α) → 2`
  have htail : Tendsto (fun n => P.real {ω | u n < echoProcess (powLag γ) Z 0 ω} / u n ^ (-α))
      atTop (𝓝 2) :=
    (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw (measurable_powLag γ)
      (one_le_powLag γ) 0).comp hu
  -- Step 3: `runsRatio → 1` (via `runs_bounds` and `tendsto_clusterRatio_powEchoProcess_short`)
  have hκ : Tendsto (fun n => u n ^ γ / ((2 * r n : ℕ) : ℝ)) atTop atTop := by
    have h2 : Tendsto (fun n => ((2 * r n : ℕ) : ℝ) / u n ^ γ) atTop (𝓝 0) := by
      simpa [mul_div_assoc] using hshort.const_mul 2
    have hinv := Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      h2 (by
        filter_upwards [hu.eventually_gt_atTop 0, hr.eventually_gt_atTop 0] with n hun hrn
        exact mem_Ioi.2 (div_pos (by exact_mod_cast (show 0 < 2 * r n by omega))
          (Real.rpow_pos_of_pos hun _))))
    exact hinv.congr fun n => inv_div _ _
  have hrb2 : Tendsto (fun n => ((2 * r n : ℕ) : ℝ) * u n ^ (-α)) atTop (𝓝 0) := by
    simpa [mul_assoc] using hrb.const_mul 2
  have hCR := tendsto_clusterRatio_powEchoProcess_short hα hZ hind hlaw hpos hγ hγα hu
    (hr.atTop_mul_const' (show 0 < (2 : ℕ) by omega) |> fun h => by simpa [mul_comm] using h) hrb2 hκ
  have hrunsRatio : Tendsto (fun n => P.real (runEvent X (r n) 0 (u n)) /
      P.real {ω | u n < X 0 ω}) atTop (𝓝 1) := by
    have hlow := (hCR.const_mul 2).sub_const 1
    norm_num at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hr.eventually_gt_atTop 0] with n hn
      have hb := (hstat.runs_bounds hXm (r n) (u n)).2
      have hp0 : 0 < P.real {ω | u n < |echoProcess (powLag γ) Z 0 ω|} :=
        (hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos (measurable_powLag γ)
          (one_le_powLag γ) (tendsto_powLag hγ)).measureReal_lt_abs_pos (u n)
      have hrR : (0 : ℝ) < r n := by exact_mod_cast hn
      have eR : P.real (runEvent X (r n) 0 (u n)) =
          P.real {ω | u n < |echoProcess (powLag γ) Z 0 ω| ∧
            ∀ t ∈ Finset.Ioc (0 : ℤ) (r n), |echoProcess (powLag γ) Z t ω| ≤ u n} := by
        rw [hXeq, runEvent_abs]
      have eP : P.real {ω | u n < X 0 ω} = P.real {ω | u n < |echoProcess (powLag γ) Z 0 ω|} := by
        congr 1; ext ω; simp [X, abs_of_nonneg (echoProcess_nonneg hpos _ ω)]
      rw [eR, eP]
      simp only [clusterRatio]
      have key := two_mul_div_sub_one_le hp0 hrR hb
      convert key using 4
      push_cast; ring
    · filter_upwards with n
      exact div_le_one_of_le₀ (measureReal_mono fun ω hω => hω.1) measureReal_nonneg
  -- Step 4: `(tailCount - runsCount) / (2 n uₙ^(-α)) ≥ 0` and its expectation tends to `0`!
  have hR_le_N : ∀ n ω, runsCount X (r n) (n - r n) (u n) ω ≤ tailCount X n (u n) ω := fun n ω => by
    simp only [runsCount, tailCount]
    refine (Finset.sum_le_sum fun i _ => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le n (r n)))
        fun _ _ _ => by split_ifs <;> norm_num)
    by_cases h : ω ∈ runEvent X (r n) i (u n)
    · have h1 : u n < X i ω := h.1
      simp [h, h1]
    · simp only [h, ↓reduceIte]; split_ifs <;> norm_num
  have hR_nn : ∀ n ω, 0 ≤ runsCount X (r n) (n - r n) (u n) ω := fun n ω =>
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  set gap : ℕ → Ω → ℝ := fun n ω =>
    (tailCount X n (u n) ω - runsCount X (r n) (n - r n) (u n) ω) / (2 * (n : ℝ) * u n ^ (-α))
  have hgap_lim : TendstoInMeasure P gap atTop (fun _ => 0) := by
    have habs : TendstoInMeasure P (fun n ω => |gap n ω|) atTop (fun _ => 0) := by
      refine tendstoInMeasure_zero_of_tendsto_integral_nonneg (fun _ _ => abs_nonneg _) (fun n => ?_) ?_
      · have htc_m : Measurable (tailCount X n (u n)) := measurable_tailCount (fun t => hXm t) n (u n)
        have hrc_m : Measurable (runsCount X (r n) (n - r n) (u n)) :=
          Finset.measurable_sum _ fun i _ =>
            measurable_ite_mem (measurableSet_runEvent (fun t => hXm t) (r n) i (u n))
        refine Integrable.of_bound ((htc_m.sub hrc_m).div_const _).abs.aestronglyMeasurable
          ((n : ℝ) / |2 * (n : ℝ) * u n ^ (-α)|) (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs, abs_abs, abs_div]
        refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
        have h0 : 0 ≤ tailCount X n (u n) ω - runsCount X (r n) (n - r n) (u n) ω :=
          sub_nonneg.2 (hR_le_N n ω)
        have hle : tailCount X n (u n) ω ≤ (n : ℝ) := by
          have := Finset.sum_le_sum (s := Finset.range n) fun i _ =>
            (show (if u n < X i ω then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
          simpa [tailCount] using this
        rw [abs_of_nonneg h0]; linarith [hR_nn n ω]
      · -- Expectation of `|gap n|` = `(n pₙ - (n - rₙ) P(runEvent)) / (2 n uₙ^(-α)) → 0`
        have hE_lim : Tendsto (fun n =>
            (P.real {ω | u n < X 0 ω} / (2 * u n ^ (-α))) *
              (1 - (1 - (r n : ℝ) / n) * (P.real (runEvent X (r n) 0 (u n)) / P.real {ω | u n < X 0 ω})))
            atTop (𝓝 0) := by
          have h1 : Tendsto (fun n => P.real {ω | u n < X 0 ω} / (2 * u n ^ (-α))) atTop (𝓝 1) := by
            have := htail.div_const 2
            simp only [div_self (by norm_num : (2 : ℝ) ≠ 0)] at this
            refine this.congr fun n => ?_
            change P.real {ω | u n < echoProcess (powLag γ) Z 0 ω} / u n ^ (-α) / 2 =
              P.real {ω | u n < echoProcess (powLag γ) Z 0 ω} / (2 * u n ^ (-α))
            ring
          have h2 : Tendsto (fun n => 1 - (1 - (r n : ℝ) / n) *
              (P.real (runEvent X (r n) 0 (u n)) / P.real {ω | u n < X 0 ω})) atTop (𝓝 0) := by
            have := ((hrn.const_sub 1).mul hrunsRatio).const_sub 1
            simpa using this
          simpa using h1.mul h2
        refine hE_lim.congr' ?_
        filter_upwards [hk.eventually_gt_atTop 0, hrn.eventually (gt_mem_nhds one_pos)] with n hkn hrn1
        have hden : 0 < 2 * (n : ℝ) * u n ^ (-α) := by linarith
        have hn0 : (0 : ℝ) < n := by
          by_contra hle; push Not at hle
          have : n = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg n)
          rw [this, Nat.cast_zero, zero_mul] at hkn; linarith
        have hrle : r n ≤ n := by
          rw [div_lt_one hn0] at hrn1; exact_mod_cast hrn1.le
        have heq_abs : ∀ ω, |gap n ω| = (tailCount X n (u n) ω - runsCount X (r n) (n - r n) (u n) ω) /
            (2 * (n : ℝ) * u n ^ (-α)) := fun ω =>
          abs_of_nonneg (div_nonneg (sub_nonneg.2 (hR_le_N n ω)) hden.le)
        simp_rw [heq_abs]
        have htc_int : ∫ ω, tailCount X n (u n) ω ∂P = n * P.real {ω | u n < X 0 ω} := by
          have : tailCount X n (u n) =
              fun ω => ∑ i ∈ Finset.range n, if ω ∈ {ω | u n < X i ω} then (1 : ℝ) else 0 := rfl
          rw [this, integral_sum_ite_mem fun i => measurableSet_lt measurable_const (hXm i)]
          have hst : ∀ i, P.real {ω | u n < X i ω} = P.real {ω | u n < X 0 ω} := fun i => by
            have hid := hs.identDistrib (fun t => hXm t) i
            rw [measureReal_def, measureReal_def,
              show {ω | u n < X i ω} = X i ⁻¹' Ioi (u n) from rfl,
              show {ω | u n < X 0 ω} = X 0 ⁻¹' Ioi (u n) from rfl,
              hid.measure_mem_eq measurableSet_Ioi]
          rw [Finset.sum_congr rfl fun i _ => hst i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hrc_int : ∫ ω, runsCount X (r n) (n - r n) (u n) ω ∂P =
            ((n - r n : ℕ) : ℝ) * P.real (runEvent X (r n) 0 (u n)) := by
          have : runsCount X (r n) (n - r n) (u n) =
              fun ω => ∑ i ∈ Finset.range (n - r n), if ω ∈ runEvent X (r n) i (u n) then (1 : ℝ) else 0 := rfl
          rw [this, integral_sum_ite_mem fun i => measurableSet_runEvent (fun t => hXm t) (r n) i (u n)]
          have hst : ∀ i, P.real (runEvent X (r n) i (u n)) = P.real (runEvent X (r n) 0 (u n)) := fun i =>
            hs.measureReal_runEvent (fun t => hXm t) (r n) i (u n)
          rw [Finset.sum_congr rfl fun i _ => hst i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have htc_i : Integrable (tailCount X n (u n)) P :=
          (memLp_tailCount (fun t => hXm t) n (u n) 1).integrable le_rfl
        have hrc_i : Integrable (runsCount X (r n) (n - r n) (u n)) P :=
          (memLp_sum_ite_mem (fun i => measurableSet_runEvent (fun t => hXm t) (r n) i (u n)) (n - r n) 1).integrable le_rfl
        rw [integral_div, integral_sub htc_i hrc_i, htc_int, hrc_int, Nat.cast_sub hrle]
        have hp0 : P.real {ω | u n < X 0 ω} ≠ 0 := by
          have eP : P.real {ω | u n < X 0 ω} = P.real {ω | u n < |echoProcess (powLag γ) Z 0 ω|} := by
            congr 1; ext ω; simp [X, abs_of_nonneg (echoProcess_nonneg hpos _ ω)]
          rw [eP]
          exact ((hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos (measurable_powLag γ)
            (one_le_powLag γ) (tendsto_powLag hγ)).measureReal_lt_abs_pos (u n)).ne'
        have hua : u n ^ (-α) ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hkn; linarith
        field_simp [hn0.ne', hp0, hua]
    rw [tendstoInMeasure_iff_norm] at habs ⊢
    intro ε hε
    simpa [Real.norm_eq_abs] using habs ε hε
  -- Step 5: `runsEstimator = 1 - gap / (Nₙ / (2 n uₙ^(-α))) → 1` in probability!
  have hcomp := tendstoInMeasure_comp₂ hgap_lim hN (φ := fun p : ℝ × ℝ => 1 - p.1 / p.2)
    (continuousAt_const.sub (continuousAt_fst.div continuousAt_snd one_ne_zero))
  simp only [zero_div, sub_zero] at hcomp
  rw [tendstoInMeasure_iff_norm] at hcomp ⊢
  intro ε hε
  have hNpos : Tendsto (fun n => P {ω | (1 / 2 : ℝ) ≤ ‖tailCount X n (u n) ω /
      (2 * (n : ℝ) * u n ^ (-α)) - 1‖}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_norm.1 hN) (1 / 2) (by norm_num)
  have hsum : Tendsto (fun n => P {ω | ε ≤ ‖1 - gap n ω / (tailCount X n (u n) ω /
        (2 * (n : ℝ) * u n ^ (-α))) - 1‖} +
      P {ω | (1 / 2 : ℝ) ≤ ‖tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)) - 1‖})
      atTop (𝓝 0) := by
    simpa using (hcomp ε hε).add hNpos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn
  have hden : 0 < 2 * (n : ℝ) * u n ^ (-α) := by linarith
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  by_contra hnot
  simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs] at hω hnot
  have htc_pos : (0 : ℝ) < tailCount X n (u n) ω := by
    have : 1 / 2 < tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)) := by
      linarith [(abs_lt.1 hnot.2).1]
    have := (lt_div_iff₀ hden).1 this
    linarith
  have heq_est : runsEstimator X n (r n) (u n) ω =
      1 - gap n ω / (tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α))) := by
    simp only [runsEstimator, gap]
    have hn0 : (n : ℝ) ≠ 0 := by intro h0; rw [h0, zero_mul] at hkn; linarith
    have hua : u n ^ (-α) ≠ 0 := by intro h0; rw [h0, mul_zero] at hkn; linarith
    field_simp [htc_pos.ne', hden.ne', hn0, hua]
    ring
  rw [heq_est] at hω
  linarith

include hα hZ hind hlaw in
/-- **Long blocks are consistent for the power-lag echo process** (for ALL `0 < γ < α`):
at intermediate thresholds `uₙ → ∞`, `n uₙ^(-α) → ∞`, if `rₙ → ∞`, `rₙ / n → 0`,
`rₙ uₙ^(-α) → 0`, and `uₙ^γ / rₙ → 0`, then the disjoint blocks estimator converges in
probability to `1/2 = θ`.

Proved directly from the independent innovations (no `α/γ > 2` mixing-summability restriction):
each block `j < ⌊n / rₙ⌋` satisfies `c_j - B_j ≤ c_j (c_j - 1)` and `B_j ≤ c_j + spill_j`,
where `c_j` is the count of innovations exceeding `uₙ` in block `j` and `spill_j` indicates an
echo from an earlier block `< j rₙ` landing in block `j`. -/
theorem powEcho_tendstoInMeasure_blocksEstimator (hγ : 0 < γ) (hγα : γ < α) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) (hk : Tendsto (fun n : ℕ => (n : ℝ) * u n ^ (-α)) atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop (𝓝 0))
    (hrb : Tendsto (fun n : ℕ => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hlong : Tendsto (fun n : ℕ => u n ^ γ / r n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => blocksEstimator (fun k : ℕ => echoProcess (powLag γ) Z k) n
      (r n) (u n)) atTop (fun _ => 1 / 2) := by
  set L : ℝ → ℕ := powLag γ
  have hLm : Measurable L := measurable_powLag γ
  set X : ℕ → Ω → ℝ := fun k => echoProcess L Z k
  have hXm : ∀ t, Measurable (echoProcess L Z t) := measurable_echoProcess hZ hLm
  have hPpareto : IsProbabilityMeasure (paretoMeasure 1 α) := isProbabilityMeasure_paretoMeasure one_pos hα
  have hZprob : ∀ (s : ℤ) {n : ℕ}, 1 ≤ u n → P.real {ω | u n < Z s ω} = u n ^ (-α) := fun s {n} hun => by
    rw [measureReal_def, show {ω | u n < Z s ω} = Z s ⁻¹' Ioi (u n) from rfl,
      ← Measure.map_apply (hZ s) measurableSet_Ioi, hlaw s, ← measureReal_def,
      paretoMeasure_one_real_Ioi hα hun]
  -- Step 1: `tailCount X n (u n) / (2 n uₙ^(-α)) → 1` in probability
  have hN := powEcho_tendstoInMeasure_tailCount_div hα hZ hind hlaw hγ hγα hu hk
  -- Step 2: `mₙ = n / rₙ` satisfies `(mₙ rₙ) / n → 1`
  set m : ℕ → ℕ := fun n => n / r n
  have hmr_div_n : Tendsto (fun n : ℕ => ((m n * r n : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hrn.const_sub 1) tendsto_const_nhds ?_ ?_
    · filter_upwards [hrn.eventually (gt_mem_nhds one_pos), hr.eventually_gt_atTop 0,
        hk.eventually_gt_atTop 0] with n _ hr0 hkn
      have hn0 : (0 : ℝ) < n := by
        by_contra hle; push Not at hle
        have : n = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg n)
        rw [this, Nat.cast_zero, zero_mul] at hkn; linarith
      have hrem : n - r n ≤ m n * r n := by
        have hdiv := Nat.div_add_mod n (r n)
        have hmod : n % r n < r n := Nat.mod_lt n hr0
        have : m n * r n = r n * (n / r n) := mul_comm _ _
        omega
      have hcast : (n : ℝ) - r n ≤ ((m n * r n : ℕ) : ℝ) := by
        rcases le_or_gt (r n) n with hle | hgt
        · have h2 : ((n - r n : ℕ) : ℝ) ≤ ((m n * r n : ℕ) : ℝ) := by exact_mod_cast hrem
          rwa [Nat.cast_sub hle] at h2
        · have : (n : ℝ) - r n < 0 := by
            have : (n : ℝ) < r n := by exact_mod_cast hgt
            linarith
          exact this.le.trans (Nat.cast_nonneg _)
      rw [le_div_iff₀ hn0]
      have : (1 - (r n : ℝ) / n) * n = (n : ℝ) - r n := by field_simp [hn0.ne']
      linarith
    · filter_upwards [hk.eventually_gt_atTop 0] with n hkn
      have hn0 : (0 : ℝ) < n := by
        by_contra hle; push Not at hle
        have : n = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg n)
        rw [this, Nat.cast_zero, zero_mul] at hkn; linarith
      have hle : m n * r n ≤ n := Nat.div_mul_le_self n (r n)
      exact (div_le_one hn0).2 (by exact_mod_cast hle)
  -- Step 3: `Mₙ = ∑_{s < mₙ rₙ} 1_{Z_s > uₙ}` satisfies `Mₙ / (n uₙ^(-α)) → 1` in probability
  set I_Z : ℕ → ℕ → Ω → ℝ := fun n s ω => if u n < Z s ω then 1 else 0
  have hM_lim : TendstoInMeasure P
      (fun n ω => (∑ s ∈ Finset.range (m n * r n), I_Z n s ω) / ((n : ℝ) * u n ^ (-α)))
      atTop (fun _ => 1) := by
    have hI_bd : ∀ n s ω, 0 ≤ I_Z n s ω ∧ I_Z n s ω ≤ 1 := fun _ _ _ => by
      simp only [I_Z]; split_ifs <;> norm_num
    have hI_m : ∀ n s, Measurable (I_Z n s) := fun n s =>
      Measurable.ite (measurableSet_lt measurable_const (hZ s)) measurable_const measurable_const
    have hI_ind : ∀ n, iIndepFun (I_Z n) P := fun n =>
      (hind.precomp Nat.cast_injective).comp (fun _ z => if u n < z then (1 : ℝ) else 0)
        fun _ => Measurable.ite measurableSet_Ioi measurable_const measurable_const
    have hM_sub : TendstoInMeasure P
        (fun n ω => (∑ s ∈ Finset.range (m n * r n), I_Z n s ω) /
          (((m n * r n : ℕ) : ℝ) * u n ^ (-α)))
        atTop (fun _ => 1) := by
      have hμ_lim : Tendsto (fun n => (((m n * r n : ℕ) : ℝ) * u n ^ (-α))) atTop atTop := by
        have h := hmr_div_n.pos_mul_atTop one_pos hk
        refine h.congr' ?_
        filter_upwards [hk.eventually_gt_atTop 0] with n hkn
        have hn0 : (n : ℝ) ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hkn; linarith
        field_simp [hn0]
      refine tendstoInMeasure_sum_indep_div (P := P) (Y := fun n s ω => I_Z n s ω)
        (N := fun n => m n * r n) (M := 1) hI_m hI_bd hI_ind
        (hμ_lim.eventually_gt_atTop 0) ?_ ?_
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hu.eventually_ge_atTop 1, hμ_lim.eventually_gt_atTop 0] with n hun hμ
        have hE : ∀ s ∈ Finset.range (m n * r n), ∫ ω, I_Z n s ω ∂P = u n ^ (-α) := fun s _ => by
          have heq : I_Z n s = ({ω | u n < Z s ω}).indicator 1 := by
            ext ω; simp [I_Z, Set.indicator]
          rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hZ s)), hZprob s hun]
        rw [Finset.sum_congr rfl hE, Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_self hμ.ne']
      · have hinv : Tendsto (fun n => (((m n * r n : ℕ) : ℝ) * u n ^ (-α))⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp hμ_lim
        refine hinv.congr' ?_
        filter_upwards [hu.eventually_ge_atTop 1, hμ_lim.eventually_gt_atTop 0] with n hun hμ
        have hE2 : ∀ s ∈ Finset.range (m n * r n), ∫ ω, (I_Z n s ω) ^ 2 ∂P = u n ^ (-α) := fun s _ => by
          have heq : (fun ω => (I_Z n s ω) ^ 2) = ({ω | u n < Z s ω}).indicator 1 := by
            ext ω; simp [I_Z, Set.indicator]
          rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hZ s)), hZprob s hun]
        rw [Finset.sum_congr rfl hE2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [hμ.ne']
    have hmr_meas : TendstoInMeasure P (fun n _ => ((m n * r n : ℕ) : ℝ) / n) atTop (fun _ => 1) := by
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(Metric.tendsto_nhds.1 hmr_div_n) ε hε] with n hn
      rw [Real.dist_eq] at hn
      have hempty : {ω : Ω | ε ≤ ‖((m n * r n : ℕ) : ℝ) / n - 1‖} = ∅ := by
        ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le, Real.norm_eq_abs]
        exact hn
      rw [hempty, measure_empty]
    have hmul := tendstoInMeasure_comp₂ hM_sub hmr_meas
      (φ := fun p : ℝ × ℝ => p.1 * p.2) continuous_mul.continuousAt
    simp only [one_mul] at hmul
    rw [tendstoInMeasure_iff_norm] at hmul ⊢
    intro ε hε
    refine (hmul ε hε).congr' ?_
    filter_upwards [hrn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hmr_div_n.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hk.eventually_gt_atTop 0] with n _ hmr_pos hkn
    congr 1; ext ω
    have hmr0 : (((m n * r n : ℕ) : ℝ)) ≠ 0 := by
      intro h0; rw [h0, zero_div] at hmr_pos; linarith
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hkn; linarith
    have hua0 : u n ^ (-α) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hkn; linarith
    have heq : (∑ s ∈ Finset.range (m n * r n), I_Z n s ω) /
        (((m n * r n : ℕ) : ℝ) * u n ^ (-α)) * (((m n * r n : ℕ) : ℝ) / n) =
        (∑ s ∈ Finset.range (m n * r n), I_Z n s ω) / ((n : ℝ) * u n ^ (-α)) := by
      field_simp [hmr0, hn0, hua0]
    simp only [mem_ofPred_eq]
    rw [heq]
  -- Step 4: Compare `blockCount X (r n) (m n) (u n)` with `Mₙ` via per-block `c_j` and `spill_j`
  set cB : ℕ → ℕ → Ω → ℝ := fun n j ω =>
    ∑ s ∈ Finset.Ico (j * r n) (j * r n + r n), I_Z n s ω
  set spillSet : ℕ → ℕ → Set Ω := fun n j =>
    {ω | ∃ s : ℤ, s < ((j * r n : ℕ) : ℤ) ∧ u n < Z s ω ∧
      ((j * r n : ℕ) : ℤ) ≤ s + (L (Z s ω) : ℤ) ∧ s + (L (Z s ω) : ℤ) < ((j * r n + r n : ℕ) : ℤ)}
  set spill : ℕ → ℕ → Ω → ℝ := fun n j ω => if ω ∈ spillSet n j then 1 else 0
  have hspill_ms : ∀ n j, MeasurableSet (spillSet n j) := fun n j => by
    have heq : spillSet n j = ⋃ k : ℕ,
        {ω | u n < Z (((j * r n : ℕ) : ℤ) - (k + 1 : ℕ)) ω ∧
          k + 1 ≤ L (Z (((j * r n : ℕ) : ℤ) - (k + 1 : ℕ)) ω) ∧
          L (Z (((j * r n : ℕ) : ℤ) - (k + 1 : ℕ)) ω) < k + 1 + r n} := by
      ext ω; simp only [spillSet, mem_ofPred_eq, mem_iUnion]; constructor
      · rintro ⟨s, hs, h1, h2, h3⟩
        refine ⟨(((j * r n : ℕ) : ℤ) - s - 1).toNat, ?_, ?_, ?_⟩
        · have hseq : ((j * r n : ℕ) : ℤ) - ((((j * r n : ℕ) : ℤ) - s - 1).toNat + 1 : ℕ) = s := by omega
          rw [hseq]; exact h1
        · have hseq : ((j * r n : ℕ) : ℤ) - ((((j * r n : ℕ) : ℤ) - s - 1).toNat + 1 : ℕ) = s := by omega
          rw [hseq]; omega
        · have hseq : ((j * r n : ℕ) : ℤ) - ((((j * r n : ℕ) : ℤ) - s - 1).toNat + 1 : ℕ) = s := by omega
          rw [hseq]; omega
      · rintro ⟨k, h1, h2, h3⟩
        exact ⟨((j * r n : ℕ) : ℤ) - (k + 1 : ℕ), by omega, h1, by omega, by omega⟩
    rw [heq]
    refine MeasurableSet.iUnion fun k =>
      (measurableSet_lt measurable_const (hZ _)).inter
        ((measurableSet_le measurable_const (hLm.comp (hZ _))).inter
          (measurableSet_lt (hLm.comp (hZ _)) measurable_const))
  have hcB_m : ∀ n j, Measurable (cB n j) := fun n j =>
    Finset.measurable_sum _ fun s _ =>
      Measurable.ite (measurableSet_lt measurable_const (hZ s)) measurable_const measurable_const
  have hspill_m : ∀ n j, Measurable (spill n j) := fun n j => measurable_ite_mem (hspill_ms n j)
  -- Key identity: `∑_{j < m n} cB n j = ∑_{s < m n * r n} I_Z n s`
  have hsum_cB : ∀ n ω, ∑ j ∈ Finset.range (m n), cB n j ω =
      ∑ s ∈ Finset.range (m n * r n), I_Z n s ω := fun n ω => by
    induction (m n) with
    | zero => simp [cB]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, show (k + 1) * r n = k * r n + r n by ring,
        ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_right (k * r n) (r n))]
  -- Pointwise bound per block: `|1_{blockEvent j} - cB j| ≤ spill j + cB j * (cB j - 1)`
  have hpt_block : ∀ n j ω, 0 ≤ u n →
      |(if ω ∈ blockEvent X (r n) j (u n) then (1 : ℝ) else 0) - cB n j ω| ≤
        spill n j ω + cB n j ω * (cB n j ω - 1) := fun n j ω hun0 => by
    have hc_nat : ∃ k : ℕ, cB n j ω = (k : ℝ) :=
      ⟨((Finset.Ico (j * r n) (j * r n + r n)).filter fun s : ℕ => u n < Z s ω).card,
        Finset.sum_boole (R := ℝ) (s := Finset.Ico (j * r n) (j * r n + r n))
          (p := fun s : ℕ => u n < Z s ω)⟩
    obtain ⟨k, hk_eq⟩ := hc_nat
    have hsp0 : 0 ≤ spill n j ω := by simp only [spill]; split_ifs <;> norm_num
    have hcol0 : 0 ≤ cB n j ω * (cB n j ω - 1) := by
      rw [hk_eq]; rcases k with _ | k
      · simp
      · have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
        nlinarith
    have hup : (if ω ∈ blockEvent X (r n) j (u n) then (1 : ℝ) else 0) ≤ cB n j ω + spill n j ω := by
      by_cases hb : ω ∈ blockEvent X (r n) j (u n)
      · simp only [hb, ↓reduceIte]
        simp only [blockEvent, maxLE, Set.mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hb
        obtain ⟨t, ht, hXt⟩ := hb
        have hX_def : X t ω = echoProcess L Z t ω := rfl
        rw [hX_def] at hXt
        obtain ⟨d, hd1, hd2⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (L := L) (Z := Z) hun0 (t : ℤ) hXt)
        rcases hd2 with rfl | hdL
        · simp only [Nat.cast_zero, sub_zero] at hd1
          have hc1 : 1 ≤ cB n j ω := by
            have := Finset.single_le_sum (f := fun s => I_Z n s ω)
              (fun _ _ => by simp only [I_Z]; split_ifs <;> norm_num) ht
            simpa [cB, I_Z, hd1] using this
          linarith
        · let s : ℤ := (t : ℤ) - d
          rcases lt_or_ge s ((j * r n : ℕ) : ℤ) with hs_lt | hs_ge
          · have hsp1 : spill n j ω = 1 := by
              refine ite_eq_left ⟨s, hs_lt, hd1, ?_, ?_⟩
              · rw [Finset.mem_Ico] at ht; dsimp [s]; omega
              · rw [Finset.mem_Ico] at ht; dsimp [s]; omega
            have hc0 : 0 ≤ cB n j ω := by rw [hk_eq]; exact Nat.cast_nonneg k
            linarith
          · have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg _) hs_ge
            obtain ⟨s', hs'⟩ := Int.eq_ofNat_of_zero_le hs0
            have hs_mem : s' ∈ Finset.Ico (j * r n) (j * r n + r n) := by
              rw [Finset.mem_Ico] at ht ⊢; dsimp [s] at hs'; omega
            have hZs' : u n < Z (s' : ℤ) ω := by rw [← hs']; exact hd1
            have hc1 : 1 ≤ cB n j ω := by
              have := Finset.single_le_sum (f := fun s0 => I_Z n s0 ω)
                (fun _ _ => by simp only [I_Z]; split_ifs <;> norm_num) hs_mem
              simpa [cB, I_Z, hZs'] using this
            linarith
      · simp only [hb, ↓reduceIte]
        have hc0 : 0 ≤ cB n j ω := by rw [hk_eq]; exact Nat.cast_nonneg k
        linarith
    have hlo : cB n j ω - (if ω ∈ blockEvent X (r n) j (u n) then (1 : ℝ) else 0) ≤
        cB n j ω * (cB n j ω - 1) := by
      rw [hk_eq]
      have hge : (if 1 ≤ k then (1 : ℝ) else 0) ≤ if ω ∈ blockEvent X (r n) j (u n) then 1 else 0 := by
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2
          have hpos_c : (0 : ℝ) < cB n j ω := by rw [hk_eq]; exact_mod_cast h1
          obtain ⟨s, hs, hspos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos_c.ne'
          have hZs : u n < Z s ω := by by_contra h; exact hspos (ite_eq_right h)
          simp only [blockEvent, maxLE, Set.mem_compl_iff, mem_ofPred_eq, not_forall, not_le]
          exact ⟨s, hs, lt_of_lt_of_le hZs (le_echoProcess (L := L) (s : ℤ) ω)⟩
        · norm_num
        · exact le_rfl
      linarith [nat_sub_ind_le_mul_sub_one k]
    rw [abs_le]; constructor <;> linarith
  -- Expected spill per block: `E[spill n j] ≤ echoBlockMass α L (u n) (r n)`
  have hE_spill : ∀ n j, 1 ≤ u n →
      ∫ ω, spill n j ω ∂P ≤ echoBlockMass α L (u n) (r n) := fun n j hun => by
    have heq : spill n j = (spillSet n j).indicator 1 := by
      ext ω; simp [spill, Set.indicator]
    rw [heq, integral_indicator_one (hspill_ms n j)]
    -- Map each `k : ℕ` (`s = j rₙ - (k + 1)`) to `echoBlockIdx L (r n) (k + r n) ∩ Ioi (u n)`
    have hsub : spillSet n j ⊆ ⋃ k : ℕ,
        Z (((j * r n : ℕ) : ℤ) - (k + 1 : ℕ)) ⁻¹' (echoBlockIdx L (r n) (k + r n) ∩ Ioi (u n)) := by
      rintro ω ⟨s, hs, h1, h2, h3⟩
      refine mem_iUnion.2 ⟨(((j * r n : ℕ) : ℤ) - s - 1).toNat, ?_⟩
      have hseq : ((j * r n : ℕ) : ℤ) - ((((j * r n : ℕ) : ℤ) - s - 1).toNat + 1 : ℕ) = s := by omega
      simp only [Set.mem_preimage, Set.mem_inter_iff, echoBlockIdx, mem_ofPred_eq, Set.mem_Ioi]
      rw [hseq]
      refine ⟨Or.inr ⟨?_, ?_⟩, h1⟩ <;> omega
    have hsum_all := hasSum_echoBlockIdx hα hLm hun (r n)
    have hsum_tail : HasSum (fun k : ℕ => (paretoMeasure 1 α).real (echoBlockIdx L (r n) (k + r n) ∩ Ioi (u n)))
        (echoBlockMass α L (u n) (r n)) := by
      have hhead : ∑ i ∈ Finset.range (r n),
          (paretoMeasure 1 α).real (echoBlockIdx L (r n) i ∩ Ioi (u n)) =
          (r n : ℝ) * u n ^ (-α) := by
        have hpt : ∀ i ∈ Finset.range (r n),
            (paretoMeasure 1 α).real (echoBlockIdx L (r n) i ∩ Ioi (u n)) = u n ^ (-α) := fun i hi => by
          have hir : i < r n := Finset.mem_range.1 hi
          have heq_set : echoBlockIdx L (r n) i ∩ Ioi (u n) = Ioi (u n) := by
            ext z; simp [echoBlockIdx, hir]
          rw [heq_set, paretoMeasure_one_real_Ioi hα hun]
        rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← hhead, add_comm] at hsum_all
      exact (hasSum_nat_add_iff (f := fun i =>
        (paretoMeasure 1 α).real (echoBlockIdx L (r n) i ∩ Ioi (u n))) (r n)).2 hsum_all
    have hle_enn : P (spillSet n j) ≤
        ∑' k : ℕ, paretoMeasure 1 α (echoBlockIdx L (r n) (k + r n) ∩ Ioi (u n)) := by
      refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
      refine ENNReal.tsum_le_tsum fun k => le_of_eq ?_
      have hm : MeasurableSet (echoBlockIdx L (r n) (k + r n) ∩ Ioi (u n)) :=
        (measurableSet_echoBlockIdx hLm (r n) (k + r n)).inter measurableSet_Ioi
      set idx : ℤ := ((j * r n : ℕ) : ℤ) - (k + 1 : ℕ)
      exact (Measure.map_apply (hZ idx) hm).symm.trans (by rw [hlaw idx])
    have htsum_eq : (∑' k : ℕ, paretoMeasure 1 α (echoBlockIdx L (r n) (k + r n) ∩ Ioi (u n))) =
        ENNReal.ofReal (echoBlockMass α L (u n) (r n)) := by
      rw [← hsum_tail.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hsum_tail.summable]
      exact tsum_congr fun k => (ofReal_measureReal (measure_ne_top _ _)).symm
    rw [htsum_eq] at hle_enn
    rw [measureReal_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_enn).trans_eq
      (ENNReal.toReal_ofReal (echoBlockMass_nonneg α L (u n) (r n)))
  -- Expected collision per block: `E[cB j (cB j - 1)] ≤ (rₙ uₙ^(-α))^2`
  have hE_colB : ∀ n j, 1 ≤ u n →
      ∫ ω, cB n j ω * (cB n j ω - 1) ∂P ≤ ((r n : ℝ) * u n ^ (-α)) ^ 2 := fun n j hun => by
    have hI_ind : iIndepFun (I_Z n) P :=
      (hind.precomp Nat.cast_injective).comp (fun _ z => if u n < z then (1 : ℝ) else 0)
        fun _ => Measurable.ite measurableSet_Ioi measurable_const measurable_const
    have hcol := integral_mul_sub_one_le_sq (Finset.Ico (j * r n) (j * r n + r n))
      (fun s => Measurable.ite (measurableSet_lt measurable_const (hZ s)) measurable_const measurable_const)
      (fun s ω => by by_cases h : u n < Z s ω <;> simp [h]) hI_ind
    have hsumE : ∑ s ∈ Finset.Ico (j * r n) (j * r n + r n), ∫ ω, I_Z n s ω ∂P =
        (r n : ℝ) * u n ^ (-α) := by
      have hpt : ∀ s ∈ Finset.Ico (j * r n) (j * r n + r n), ∫ ω, I_Z n s ω ∂P = u n ^ (-α) := fun s _ => by
        have heq : I_Z n s = ({ω | u n < Z s ω}).indicator 1 := by
          ext ω; simp [I_Z, Set.indicator]
        rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hZ s)), hZprob s hun]
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
    rw [hsumE] at hcol
    exact hcol
  -- Hence `|blockCount - Mₙ| / (n uₙ^(-α)) → 0` in probability
  set diffB : ℕ → Ω → ℝ := fun n ω =>
    |blockCount X (r n) (m n) (u n) ω - ∑ s ∈ Finset.range (m n * r n), I_Z n s ω| /
      ((n : ℝ) * u n ^ (-α))
  have hdiffB_lim : TendstoInMeasure P diffB atTop (fun _ => 0) := by
    have habs : TendstoInMeasure P (fun n ω => |diffB n ω|) atTop (fun _ => 0) := by
      refine tendstoInMeasure_zero_of_tendsto_integral_nonneg (fun _ _ => abs_nonneg _) (fun n => ?_) ?_
      · have hbc_m : Measurable (blockCount X (r n) (m n) (u n)) :=
          Finset.measurable_sum _ fun j _ =>
            measurable_ite_mem (measurableSet_blockEvent (fun t => hXm t) (r n) j (u n))
        have hM_m : Measurable fun ω => ∑ s ∈ Finset.range (m n * r n), I_Z n s ω :=
          Finset.measurable_sum _ fun s _ =>
            Measurable.ite (measurableSet_lt measurable_const (hZ s)) measurable_const measurable_const
        refine Integrable.of_bound ((hbc_m.sub hM_m).abs.div_const _).abs.aestronglyMeasurable
          (((m n : ℝ) + (m n * r n : ℕ)) / |(n : ℝ) * u n ^ (-α)|) (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs, abs_abs, abs_div, abs_abs]
        refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
        have hbc0 : 0 ≤ blockCount X (r n) (m n) (u n) ω :=
          Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
        have hbc_le : blockCount X (r n) (m n) (u n) ω ≤ (m n : ℝ) := by
          have := Finset.sum_le_sum (s := Finset.range (m n)) fun j _ =>
            (show (if ω ∈ blockEvent X (r n) j (u n) then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
          simpa [blockCount] using this
        have hM0 : 0 ≤ ∑ s ∈ Finset.range (m n * r n), I_Z n s ω :=
          Finset.sum_nonneg fun _ _ => by simp only [I_Z]; split_ifs <;> norm_num
        have hM_le : ∑ s ∈ Finset.range (m n * r n), I_Z n s ω ≤ ((m n * r n : ℕ) : ℝ) := by
          have := Finset.sum_le_sum (s := Finset.range (m n * r n)) fun s _ =>
            (show I_Z n s ω ≤ 1 by simp only [I_Z]; split_ifs <;> norm_num)
          simpa using this
        rw [abs_le]; constructor <;> linarith
      · -- `∫ |diffB n| ≤ echoShape (α/γ) (uₙ^γ / rₙ) + 1/rₙ + rₙ uₙ^(-α) → 0`
        have hβ : 1 < α / γ := (one_lt_div hγ).2 hγα
        have hlim_rhs : Tendsto (fun n : ℕ =>
            echoShape (α / γ) (u n ^ γ / r n) + 1 / (r n : ℝ) + (r n : ℝ) * u n ^ (-α))
            atTop (𝓝 0) := by
          have h1 : Tendsto (fun n => echoShape (α / γ) (u n ^ γ / r n)) atTop (𝓝 0) := by
            rw [← echoShape_zero hβ]
            exact ((continuous_echoShape hβ).tendsto 0).comp hlong
          have h2 : Tendsto (fun n => 1 / (r n : ℝ)) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_iff.2 hr)
          simpa using (h1.add h2).add hrb
        refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun _ => abs_nonneg _) ?_ hlim_rhs
        filter_upwards [hu.eventually_ge_atTop 1, hr.eventually_gt_atTop 0,
          hk.eventually_gt_atTop 0] with n hun hr0 hkn
        have hden : 0 < (n : ℝ) * u n ^ (-α) := hkn
        have hsp_int : ∀ j ∈ Finset.range (m n), Integrable (spill n j) P := fun j _ =>
          Integrable.of_bound (hspill_m n j).aestronglyMeasurable 1
            (ae_of_all _ fun ω => by simp only [spill]; split_ifs <;> norm_num)
        have hcol_int : ∀ j ∈ Finset.range (m n), Integrable (fun ω => cB n j ω * (cB n j ω - 1)) P := fun j _ =>
          Integrable.of_bound ((hcB_m n j).mul ((hcB_m n j).sub_const 1)).aestronglyMeasurable
            ((r n : ℝ) * (r n : ℝ)) (ae_of_all _ fun ω => by
              have h0 : 0 ≤ cB n j ω := Finset.sum_nonneg fun _ _ => by simp only [I_Z]; split_ifs <;> norm_num
              have h1 : cB n j ω ≤ r n := by
                have := Finset.sum_le_sum (s := Finset.Ico (j * r n) (j * r n + r n)) fun s _ =>
                  (show I_Z n s ω ≤ 1 by simp only [I_Z]; split_ifs <;> norm_num)
                simpa [Nat.card_Ico] using this
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
              have h2 : |cB n j ω - 1| ≤ r n := by
                rw [abs_le]; constructor <;> linarith [show (1 : ℝ) ≤ r n by exact_mod_cast hr0]
              exact mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _))
        have hbc_m : Measurable (blockCount X (r n) (m n) (u n)) :=
          Finset.measurable_sum _ fun j _ =>
            measurable_ite_mem (measurableSet_blockEvent (fun t => hXm t) (r n) j (u n))
        have hM_m : Measurable fun ω => ∑ s ∈ Finset.range (m n * r n), I_Z n s ω :=
          Finset.measurable_sum _ fun s _ =>
            Measurable.ite (measurableSet_lt measurable_const (hZ s)) measurable_const measurable_const
        have hdiff_int : Integrable (fun ω => |diffB n ω|) P := by
          refine Integrable.of_bound ((hbc_m.sub hM_m).abs.div_const _).abs.aestronglyMeasurable
            (((m n : ℝ) + (m n * r n : ℕ)) / |(n : ℝ) * u n ^ (-α)|) (ae_of_all _ fun ω => ?_)
          rw [Real.norm_eq_abs, abs_abs, abs_div, abs_abs]
          refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
          have hbc0 : 0 ≤ blockCount X (r n) (m n) (u n) ω :=
            Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
          have hbc_le : blockCount X (r n) (m n) (u n) ω ≤ (m n : ℝ) := by
            have := Finset.sum_le_sum (s := Finset.range (m n)) fun j _ =>
              (show (if ω ∈ blockEvent X (r n) j (u n) then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
            simpa [blockCount] using this
          have hM0 : 0 ≤ ∑ s ∈ Finset.range (m n * r n), I_Z n s ω :=
            Finset.sum_nonneg fun _ _ => by simp only [I_Z]; split_ifs <;> norm_num
          have hM_le : ∑ s ∈ Finset.range (m n * r n), I_Z n s ω ≤ ((m n * r n : ℕ) : ℝ) := by
            have := Finset.sum_le_sum (s := Finset.range (m n * r n)) fun s _ =>
              (show I_Z n s ω ≤ 1 by simp only [I_Z]; split_ifs <;> norm_num)
            simpa using this
          rw [abs_le]; constructor <;> linarith
        have hsum_int : Integrable (fun ω =>
            (∑ j ∈ Finset.range (m n), (spill n j ω + cB n j ω * (cB n j ω - 1))) /
              ((n : ℝ) * u n ^ (-α))) P :=
          (integrable_finsetSum _ fun j hj => (hsp_int j hj).add (hcol_int j hj)).div_const _
        have hmono : ∫ ω, |diffB n ω| ∂P ≤
            ∫ ω, (∑ j ∈ Finset.range (m n), (spill n j ω + cB n j ω * (cB n j ω - 1))) /
              ((n : ℝ) * u n ^ (-α)) ∂P := by
          refine integral_mono hdiff_int hsum_int fun ω => ?_
          simp only [diffB, abs_div, abs_abs, abs_of_pos hden]
          refine div_le_div_of_nonneg_right ?_ hden.le
          dsimp only [blockCount]
          rw [← hsum_cB n ω, ← Finset.sum_sub_distrib]
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hpt_block n j ω (by linarith))
        refine hmono.trans ?_
        rw [integral_div, integral_finsetSum (f := fun j ω => spill n j ω + cB n j ω * (cB n j ω - 1))
          _ fun j hj => (hsp_int j hj).add (hcol_int j hj)]
        have hterm : ∀ j ∈ Finset.range (m n),
            ∫ ω, (spill n j ω + cB n j ω * (cB n j ω - 1)) ∂P ≤
              (r n : ℝ) * u n ^ (-α) * echoShape (α / γ) (u n ^ γ / r n) + u n ^ (-α) +
                ((r n : ℝ) * u n ^ (-α)) ^ 2 := fun j hj => by
          rw [integral_add (hsp_int j hj) (hcol_int j hj)]
          have h1 := (hE_spill n j hun).trans (echoBlockMass_powLag_bounds hα hγ hγα hun hr0).2
          have h2 := hE_colB n j hun
          linarith
        have hsum_le : ∑ j ∈ Finset.range (m n), ∫ ω, (spill n j ω + cB n j ω * (cB n j ω - 1)) ∂P ≤
            (m n : ℝ) * ((r n : ℝ) * u n ^ (-α) * echoShape (α / γ) (u n ^ γ / r n) + u n ^ (-α) +
              ((r n : ℝ) * u n ^ (-α)) ^ 2) := by
          have h := Finset.sum_le_sum hterm
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
          exact h
        refine (div_le_div_of_nonneg_right hsum_le hden.le).trans ?_
        have hmr_le : (m n : ℝ) * (r n : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self n (r n)
        have hrR : (0 : ℝ) < r n := by exact_mod_cast hr0
        have hua : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
        have hnonneg : 0 ≤ echoShape (α / γ) (u n ^ γ / r n) + 1 / (r n : ℝ) + (r n : ℝ) * u n ^ (-α) := by
          have hφ0 : 0 ≤ echoShape (α / γ) (u n ^ γ / r n) := by
            have := (echoBlockMass_powLag_bounds hα hγ hγα hun hr0).1
            have hmb := echoBlockMass_nonneg α L (u n) (r n)
            have : 0 ≤ (r n : ℝ) * u n ^ (-α) * echoShape (α / γ) (u n ^ γ / r n) := by
              unfold echoShape
              have hmin0 : 0 ≤ min (u n ^ γ / (r n : ℝ)) 1 := le_min (by positivity) zero_le_one
              have hmin1 : min (u n ^ γ / (r n : ℝ)) 1 ≤ 1 := min_le_right _ _
              have hrpow : min (u n ^ γ / (r n : ℝ)) 1 ^ (α / γ) ≤ min (u n ^ γ / (r n : ℝ)) 1 := by
                rcases eq_or_lt_of_le hmin0 with h0 | hpos_m
                · rw [← h0, Real.zero_rpow (by linarith)]
                · calc min (u n ^ γ / (r n : ℝ)) 1 ^ (α / γ)
                      ≤ min (u n ^ γ / (r n : ℝ)) 1 ^ (1 : ℝ) :=
                        Real.rpow_le_rpow_of_exponent_ge hpos_m hmin1 hβ.le
                    _ = min (u n ^ γ / (r n : ℝ)) 1 := Real.rpow_one _
              have hnum : 0 ≤ (α / γ) * min (u n ^ γ / (r n : ℝ)) 1 - min (u n ^ γ / (r n : ℝ)) 1 ^ (α / γ) := by
                nlinarith
              exact mul_nonneg (mul_nonneg hrR.le hua.le) (div_nonneg hnum (sub_pos.2 hβ).le)
            exact nonneg_of_mul_nonneg_right this (mul_pos hrR hua)
          positivity
        rw [div_le_iff₀ hden]
        have heq_rhs : (m n : ℝ) * ((r n : ℝ) * u n ^ (-α) * echoShape (α / γ) (u n ^ γ / r n) +
              u n ^ (-α) + ((r n : ℝ) * u n ^ (-α)) ^ 2) =
            ((m n : ℝ) * (r n : ℝ)) * u n ^ (-α) *
              (echoShape (α / γ) (u n ^ γ / r n) + 1 / (r n : ℝ) + (r n : ℝ) * u n ^ (-α)) := by
          field_simp [hrR.ne']
        rw [heq_rhs]
        have hstep : ((m n : ℝ) * (r n : ℝ)) * u n ^ (-α) ≤ (n : ℝ) * u n ^ (-α) :=
          mul_le_mul_of_nonneg_right hmr_le hua.le
        calc ((m n : ℝ) * (r n : ℝ)) * u n ^ (-α) *
              (echoShape (α / γ) (u n ^ γ / r n) + 1 / (r n : ℝ) + (r n : ℝ) * u n ^ (-α))
            ≤ ((n : ℝ) * u n ^ (-α)) *
              (echoShape (α / γ) (u n ^ γ / r n) + 1 / (r n : ℝ) + (r n : ℝ) * u n ^ (-α)) :=
              mul_le_mul_of_nonneg_right hstep hnonneg
          _ = (echoShape (α / γ) (u n ^ γ / r n) + 1 / (r n : ℝ) + (r n : ℝ) * u n ^ (-α)) *
              ((n : ℝ) * u n ^ (-α)) := mul_comm _ _
    rw [tendstoInMeasure_iff_norm] at habs ⊢
    intro ε hε
    simpa [Real.norm_eq_abs] using habs ε hε
  -- Step 5: `blockCount / (n uₙ^(-α)) → 1` in probability
  have hB_lim : TendstoInMeasure P
      (fun n ω => blockCount X (r n) (m n) (u n) ω / ((n : ℝ) * u n ^ (-α)))
      atTop (fun _ => 1) := by
    rw [tendstoInMeasure_iff_norm] at hM_lim hdiffB_lim ⊢
    intro ε hε
    have hsum : Tendsto (fun n => P {ω | ε / 2 ≤ ‖(∑ s ∈ Finset.range (m n * r n), I_Z n s ω) /
          ((n : ℝ) * u n ^ (-α)) - 1‖} +
        P {ω | ε / 2 ≤ ‖diffB n ω - 0‖}) atTop (𝓝 0) := by
      simpa using (hM_lim (ε / 2) (by positivity)).add (hdiffB_lim (ε / 2) (by positivity))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hk.eventually_gt_atTop 0] with n hkn
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_contra hnot
    simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs, sub_zero] at hω hnot
    have h1 : |blockCount X (r n) (m n) (u n) ω / ((n : ℝ) * u n ^ (-α)) -
        (∑ s ∈ Finset.range (m n * r n), I_Z n s ω) / ((n : ℝ) * u n ^ (-α))| < ε / 2 := by
      rw [← sub_div, abs_div, abs_of_pos hkn]
      have hnn : 0 ≤ diffB n ω := div_nonneg (abs_nonneg _) hkn.le
      simpa [diffB, abs_of_nonneg hnn] using hnot.2
    have htri := abs_sub_le (blockCount X (r n) (m n) (u n) ω / ((n : ℝ) * u n ^ (-α)))
      ((∑ s ∈ Finset.range (m n * r n), I_Z n s ω) / ((n : ℝ) * u n ^ (-α))) 1
    linarith
  -- Step 6: `blocksEstimator = (blockCount / (n uₙ^(-α))) / (2 * (tailCount / (2 n uₙ^(-α)))) → 1 / 2`!
  have hcomp := tendstoInMeasure_comp₂ hB_lim hN (φ := fun p : ℝ × ℝ => p.1 / (2 * p.2))
    (continuousAt_fst.div (continuousAt_const.mul continuousAt_snd) (by norm_num))
  simp only [mul_one] at hcomp
  rw [tendstoInMeasure_iff_norm] at hcomp ⊢
  intro ε hε
  have hNpos : Tendsto (fun n => P {ω | (1 / 2 : ℝ) ≤ ‖tailCount X n (u n) ω /
      (2 * (n : ℝ) * u n ^ (-α)) - 1‖}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_norm.1 hN) (1 / 2) (by norm_num)
  have hsum : Tendsto (fun n => P {ω | ε ≤ ‖(blockCount X (r n) (m n) (u n) ω /
        ((n : ℝ) * u n ^ (-α))) / (2 * (tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)))) - 1 / 2‖} +
      P {ω | (1 / 2 : ℝ) ≤ ‖tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)) - 1‖})
      atTop (𝓝 0) := by
    simpa using (hcomp ε hε).add hNpos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn
  have hden : 0 < 2 * (n : ℝ) * u n ^ (-α) := by linarith
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  by_contra hnot
  simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs] at hω hnot
  have htc_pos : (0 : ℝ) < tailCount X n (u n) ω := by
    have : 1 / 2 < tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)) := by
      linarith [(abs_lt.1 hnot.2).1]
    have := (lt_div_iff₀ hden).1 this
    linarith
  have heq_est : blocksEstimator X n (r n) (u n) ω =
      (blockCount X (r n) (m n) (u n) ω / ((n : ℝ) * u n ^ (-α))) /
        (2 * (tailCount X n (u n) ω / (2 * (n : ℝ) * u n ^ (-α)))) := by
    have hn0 : (n : ℝ) ≠ 0 := by intro h; simp [h] at hkn
    have hua : u n ^ (-α) ≠ 0 := by intro h; simp [h] at hkn
    simp only [blocksEstimator, m]
    field_simp [htc_pos.ne', hkn.ne', hn0, hua]
  rw [heq_est] at hω
  linarith

end PowerEchoEstimators

/-! ### No universal polynomial run-length rule for the extremal index (`EVT-OP-001`) -/

section NoUniversalPolyRule

/-- **No universal polynomial run-length rule for the extremal index (`EVT-OP-001`).**
For *every* polynomial exponent `ρ ∈ (0, 1)`, there exist:
* parameters `0 < γ < α` (in fact `α = 1`, `γ = (1 + ρ) / 2` with `1 / (1 - ρ)` adjusted via
  intermediate threshold `uₙ = n^(1 - δ)` where `δ = (1 - ρ) / 4`),
* a probability space `(Ω, P)` and a stationary, `β`-mixing (with explicit polynomial rate
  `β(h) = O(h^(1 - α/γ))`), regularly varying process `X : ℕ → Ω → ℝ` of index `α = 1` with
  extremal index `θ = 1/2`,
* an intermediate threshold sequence `uₙ → ∞` with `n P(X₀ > uₙ) → ∞`,
such that:
1. the runs estimator with polynomial run length `rₙ = ⌊n^ρ⌋₊ + 1` is **inconsistent**:
   `θ̂ᴿ(n, rₙ, uₙ) → 1 ≠ 1/2 = θ` in probability;
2. yet the disjoint blocks estimator with the longer polynomial block length
   `r'ₙ = ⌊n^{ρ'}⌋₊ + 1` (for `ρ' = (3 + ρ) / 4 ∈ (ρ, 1)`) is **consistent**:
   `θ̂ᴮ(n, r'ₙ, uₙ) → 1/2 = θ` in probability. -/
theorem exists_powEcho_runsEstimator_inconsistent_of_poly {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (u : ℕ → ℝ) (βrate C : ℝ),
      0 < βrate ∧ 0 < C ∧
      IsStationary X P ∧
      (∀ h : ℕ, 2 ≤ h → (betaMixing X P h).toReal ≤ C * ((h : ℝ) - 1) ^ (-βrate)) ∧
      HasExtremalIndex X P (1 / 2) ∧
      Tendsto u atTop atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) * P.real {ω | u n < X 0 ω}) atTop atTop ∧
      TendstoInMeasure P (fun n => runsEstimator X n (⌊(n : ℝ) ^ ρ⌋₊ + 1) (u n))
        atTop (fun _ => 1) ∧
      ∃ ρ' : ℝ, ρ < ρ' ∧ ρ' < 1 ∧
        TendstoInMeasure P (fun n => blocksEstimator X n (⌊(n : ℝ) ^ ρ'⌋₊ + 1) (u n))
          atTop (fun _ => 1 / 2) := by
  -- Choose `α = 1`, `δ = (1 - ρ) / 4 ∈ (0, 1/4)`, `γ = (1 + ρ) / (2 * (1 - δ))`?
  -- Wait: simpler! Set `uₙ = (n : ℝ) ^ (1 - δ)` with `δ = (1 - ρ) / 4`, so `n uₙ^(-1) = n^δ → ∞`.
  -- Choose `γ ∈ (0, 1)` so `γ * (1 - δ) = (1 + 2 * ρ) / 3`? Check:
  -- We need `ρ < γ * (1 - δ) < ρ' < 1 - δ`!
  -- Check numbers: `1 - δ = (3 + ρ) / 4 > ρ`, midpoint `m₁ = (1 + 3 * ρ) / 4` satisfies `ρ < m₁ < 1 - δ`,
  -- and `ρ' = (2 + 2 * ρ) / 4 = (1 + ρ) / 2` satisfies `m₁ < ρ' < 1 - δ`!
  -- Wait: `(1 + 3ρ)/4 < (1 + ρ)/2` iff `1 + 3ρ < 2 + 2ρ` iff `ρ < 1` (TRUE!),
  -- and `(1 + ρ)/2 < (3 + ρ)/4` iff `2 + 2ρ < 3 + ρ` iff `ρ < 1` (TRUE!).
  -- And `γ := ((1 + 3 * ρ) / 4) / ((3 + ρ) / 4) = (1 + 3 * ρ) / (3 + ρ) ∈ (0, 1)`!
  -- Then `uₙ^γ = n^(γ * (3 + ρ) / 4) = n^((1 + 3ρ) / 4)`:
  --   * `rₙ / uₙ^γ ≈ n^(ρ - (1 + 3ρ)/4) = n^(-(1 - ρ)/4) → 0` (short runs!)
  --   * `uₙ^γ / r'ₙ ≈ n^((1 + 3ρ)/4 - (1 + ρ)/2) = n^(-(1 - ρ)/4) → 0` (long blocks!)
  --   * `r'ₙ uₙ^(-1) ≈ n^((1 + ρ)/2 - (3 + ρ)/4) = n^(-(1 - ρ)/4) → 0`!
  --   * `n uₙ^(-1) = n^((1 - ρ)/4) → ∞` (intermediate threshold!)
  -- Every single exponent gap is EXACTLY `(1 - ρ) / 4 > 0`!
  let δ : ℝ := (1 - ρ) / 4
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  let η : ℝ := (3 + ρ) / 4
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  let γ : ℝ := (1 + 3 * ρ) / (3 + ρ)
  have hγ0 : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ < 1 := by
    dsimp [γ]
    rw [div_lt_one (by linarith)]
    linarith
  let ρ' : ℝ := (1 + ρ) / 2
  have hρ'_gt : ρ < ρ' := by dsimp [ρ']; linarith
  have hρ'_lt : ρ' < 1 := by dsimp [ρ']; linarith
  have hPpareto : IsProbabilityMeasure (paretoMeasure 1 1) := isProbabilityMeasure_paretoMeasure one_pos one_pos
  obtain ⟨Ω, _, P, Z₀, hZ₀m, hZ₀law, hZ₀ind, hP⟩ := exists_iid ℤ (paretoMeasure 1 1)
  have := hP
  -- Make `Z ≥ 0` everywhere by replacing `Z₀` with `max (Z₀) 0` (a.e. equal since Pareto(1,1) > 1 a.e.)
  set Z : ℤ → Ω → ℝ := fun t ω => max (Z₀ t ω) 0
  have hZm : ∀ t, Measurable (Z t) := fun t => (hZ₀m t).max measurable_const
  have hZpos : ∀ t ω, 0 ≤ Z t ω := fun t ω => le_max_right _ _
  have hZind : iIndepFun Z P := hZ₀ind.comp (fun _ z => max z 0) fun _ => measurable_id.max measurable_const
  have hZlaw : ∀ t, P.map (Z t) = paretoMeasure 1 1 := fun t => by
    have hae : Z t =ᵐ[P] Z₀ t := by
      have h1 : ∀ᵐ z ∂(paretoMeasure 1 1), 1 < z := ae_one_lt_paretoMeasure
      rw [← (hZ₀law t).map_eq] at h1
      filter_upwards [ae_of_ae_map (hZ₀m t).aemeasurable h1] with ω hω
      exact max_eq_left (by linarith)
    rw [Measure.map_congr hae, (hZ₀law t).map_eq]
  set X : ℕ → Ω → ℝ := fun k => echoProcess (powLag γ) Z k
  set u : ℕ → ℝ := fun n => ((n + 2 : ℕ) : ℝ) ^ η
  set r : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ ρ⌋₊ + 1
  set r' : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ ρ'⌋₊ + 1
  have hXm : ∀ t, Measurable (echoProcess (powLag γ) Z t) :=
    measurable_echoProcess hZm (measurable_powLag γ)
  have hstat := hasShiftInvariantWindows_echoProcess hZm hZind hZlaw (measurable_powLag γ)
  have hXeq : X = fun k : ℕ => |echoProcess (powLag γ) Z k| := by
    funext k ω; exact (abs_of_nonneg (echoProcess_nonneg hZpos _ ω)).symm
  have hs : IsStationary X P := by rw [hXeq]; exact hstat.isStationary_abs hXm
  have hEI : HasExtremalIndex X P (1 / 2) :=
    (powEchoProcess_theta_lt_vartheta one_pos hZm hZind hZlaw hZpos hγ0 hγ1).2.2.2
  have hβrate : 0 < 1 / γ - 1 := by
    have : 1 < 1 / γ := (one_lt_div hγ0).2 hγ1
    linarith
  have hCpos : 0 < 2 * ((1 / γ) / (1 / γ - 1)) := by positivity
  -- Asymptotic scale checks
  have hu : Tendsto u atTop atTop :=
    (tendsto_rpow_atTop hη0).comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hnpow : ∀ {a : ℝ}, 0 < a → Tendsto (fun n : ℕ => ((n : ℝ) ^ a)) atTop atTop := fun ha =>
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hnpow_neg : ∀ {a : ℝ}, a < 0 → Tendsto (fun n : ℕ => ((n : ℝ) ^ a)) atTop (𝓝 0) := fun ha =>
    (tendsto_rpow_neg_atTop (neg_pos.2 ha)).comp tendsto_natCast_atTop_atTop |>.congr fun n => by
      simp
  -- Ratio `((n + 2 : ℕ) : ℝ) / n → 1`
  have hshift1 : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ)).div_atTop tendsto_natCast_atTop_atTop).const_add 1
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast; field_simp [hn0]
  -- `n * u n ^ (-1) → ∞`
  have hk : Tendsto (fun n : ℕ => (n : ℝ) * u n ^ (-(1 : ℝ))) atTop atTop := by
    have hpow := (hshift1.rpow_const (p := -η) (Or.inl one_ne_zero)).pos_mul_atTop
      (by norm_num : (0 : ℝ) < (1 : ℝ) ^ (-η)) (hnpow hδ0)
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have hexp : ((n : ℝ) ^ (-η))⁻¹ * (n : ℝ) ^ δ = (n : ℝ) := by
      rw [← Real.rpow_neg hn0.le, neg_neg, ← Real.rpow_add hn0, show η + δ = 1 by dsimp [δ, η]; ring,
        Real.rpow_one]
    calc (((n + 2 : ℕ) : ℝ) / (n : ℝ)) ^ (-η) * (n : ℝ) ^ δ
        = ((n + 2 : ℕ) : ℝ) ^ (-η) * (((n : ℝ) ^ (-η))⁻¹ * (n : ℝ) ^ δ) := by
          rw [Real.div_rpow hn2.le hn0.le, div_eq_mul_inv, mul_assoc]
      _ = ((n + 2 : ℕ) : ℝ) ^ (-η) * (n : ℝ) := by rw [hexp]
      _ = (n : ℝ) * u n ^ (-(1 : ℝ)) := by
          simp only [u, ← Real.rpow_mul hn2.le, mul_neg_one]; ring
  -- `n * P(X₀ > uₙ) → ∞`
  have htail : Tendsto (fun n => P.real {ω | u n < echoProcess (powLag γ) Z 0 ω} / u n ^ (-(1 : ℝ)))
      atTop (𝓝 2) :=
    (tendsto_measureReal_lt_echoProcess_div one_pos hZm hZind hZlaw (measurable_powLag γ)
      (one_le_powLag γ) 0).comp hu
  have hntail : Tendsto (fun n : ℕ => (n : ℝ) * P.real {ω | u n < X 0 ω}) atTop atTop := by
    have h := htail.pos_mul_atTop two_pos hk
    refine h.congr' ?_
    filter_upwards [hu.eventually_gt_atTop 0] with n hun
    have hua : u n ^ (-(1 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hun _).ne'
    change P.real {ω | u n < echoProcess (powLag γ) Z 0 ω} / u n ^ (-(1 : ℝ)) *
        ((n : ℝ) * u n ^ (-(1 : ℝ))) = (n : ℝ) * P.real {ω | u n < echoProcess (powLag γ) Z 0 ω}
    field_simp [hua]
  -- Helper: for any `p ∈ (0, 1)`, `r_p n = ⌊n^p⌋₊ + 1` satisfies `r_p n / n^p → 1`
  have hfloor_ratio : ∀ {p : ℝ}, 0 < p →
      Tendsto (fun n : ℕ => ((⌊(n : ℝ) ^ p⌋₊ + 1 : ℕ) : ℝ) / (n : ℝ) ^ p) atTop (𝓝 1) := fun {p} hp => by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hnpow hp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hinv.const_add 1) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hpos : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _
      rw [one_le_div hpos]
      push_cast; exact (Nat.lt_floor_add_one _).le
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hpos : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _
      rw [div_le_iff₀ hpos]
      have : (1 + ((n : ℝ) ^ p)⁻¹) * (n : ℝ) ^ p = (n : ℝ) ^ p + 1 := by field_simp [hpos.ne']
      rw [this]; push_cast; linarith [Nat.floor_le hpos.le]
  -- Verify `r` hypotheses for short runs
  have hr_inf : Tendsto r atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) (tendsto_nat_floor_atTop.comp (hnpow hρ0))
  have hr_div_n : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop (𝓝 0) := by
    have h := (hfloor_ratio hρ0).mul (hnpow_neg (a := ρ - 1) (by linarith))
    simp only [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    simp only [r]
    rw [Real.rpow_sub hn0, Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos hn0 _).ne', hn0.ne']
  have hr_u : Tendsto (fun n : ℕ => (r n : ℝ) * u n ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    have h := ((hfloor_ratio hρ0).mul (hshift1.rpow_const (p := -η) (Or.inl one_ne_zero))).mul
      (hnpow_neg (a := ρ - η) (by simp [η]; linarith))
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    simp only [r, u, ← Real.rpow_mul hn2.le, mul_neg_one, Real.div_rpow hn2.le hn0.le,
      Real.rpow_sub hn0]
    have hne1 : (n : ℝ) ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hne3 : (n : ℝ) ^ η ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hneg : (n : ℝ) ^ (-η) = ((n : ℝ) ^ η)⁻¹ := Real.rpow_neg hn0.le η
    rw [hneg]; field_simp [hne1, hne3]
  have hshort : Tendsto (fun n : ℕ => (r n : ℝ) / u n ^ γ) atTop (𝓝 0) := by
    have hγη : γ * η = (1 + 3 * ρ) / 4 := by
      simp only [γ, η]; field_simp [(show (3 : ℝ) + ρ ≠ 0 by linarith)]
    have h := ((hfloor_ratio hρ0).mul (hshift1.rpow_const (p := -(γ * η)) (Or.inl one_ne_zero))).mul
      (hnpow_neg (a := ρ - γ * η) (by rw [hγη]; linarith))
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    simp only [r, u, ← Real.rpow_mul hn2.le, Real.div_rpow hn2.le hn0.le, Real.rpow_sub hn0]
    rw [mul_comm η γ, Real.rpow_neg hn2.le, Real.rpow_neg hn0.le]
    have hne1 : (n : ℝ) ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hne2 : (n : ℝ) ^ (γ * η) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hne3 : ((n + 2 : ℕ) : ℝ) ^ (γ * η) ≠ 0 := (Real.rpow_pos_of_pos hn2 _).ne'
    field_simp [hne1, hne2, hne3]
  -- Verify `r'` hypotheses for long blocks
  have hr'_inf : Tendsto r' atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) (tendsto_nat_floor_atTop.comp (hnpow (by linarith)))
  have hr'_div_n : Tendsto (fun n : ℕ => (r' n : ℝ) / n) atTop (𝓝 0) := by
    have h := (hfloor_ratio (by linarith : 0 < ρ')).mul (hnpow_neg (a := ρ' - 1) (by linarith))
    simp only [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    simp only [r']
    rw [Real.rpow_sub hn0, Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos hn0 _).ne', hn0.ne']
  have hr'_u : Tendsto (fun n : ℕ => (r' n : ℝ) * u n ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    have h := ((hfloor_ratio (by linarith : 0 < ρ')).mul
      (hshift1.rpow_const (p := -η) (Or.inl one_ne_zero))).mul
      (hnpow_neg (a := ρ' - η) (by simp [ρ', η]; linarith))
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    simp only [r', u, ← Real.rpow_mul hn2.le, mul_neg_one, Real.div_rpow hn2.le hn0.le,
      Real.rpow_sub hn0]
    have hne1 : (n : ℝ) ^ ρ' ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hne3 : (n : ℝ) ^ η ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    rw [Real.rpow_neg hn0.le η]; field_simp [hne1, hne3]
  have hlong : Tendsto (fun n : ℕ => u n ^ γ / r' n) atTop (𝓝 0) := by
    have hγη : γ * η = (1 + 3 * ρ) / 4 := by
      simp only [γ, η]; field_simp [(show (3 : ℝ) + ρ ≠ 0 by linarith)]
    have h := (((hshift1.rpow_const (p := γ * η) (Or.inl one_ne_zero)).div
      (hfloor_ratio (by linarith : 0 < ρ')) one_ne_zero)).mul
      (hnpow_neg (a := γ * η - ρ') (by rw [hγη]; simp [ρ']; linarith))
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    change (((((n + 2 : ℕ) : ℝ) / n) ^ (γ * η)) / (((⌊(n : ℝ) ^ ρ'⌋₊ + 1 : ℕ) : ℝ) / (n : ℝ) ^ ρ')) *
      (n : ℝ) ^ (γ * η - ρ') = u n ^ γ / r' n
    simp only [r', u, ← Real.rpow_mul hn2.le, Real.div_rpow hn2.le hn0.le, Real.rpow_sub hn0]
    rw [mul_comm η γ]
    have hne1 : (n : ℝ) ^ ρ' ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hne2 : (n : ℝ) ^ (γ * η) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hne3 : ((⌊(n : ℝ) ^ ρ'⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    field_simp [hne1, hne2, hne3]
  refine ⟨Ω, inferInstance, P, hP, X, u, 1 / γ - 1, 2 * ((1 / γ) / (1 / γ - 1)),
    hβrate, hCpos, hs, ?_, hEI, hu, hntail, ?_, ρ', hρ'_gt, hρ'_lt, ?_⟩
  · intro h hh
    have hb := betaMixing_powEchoProcess_le one_pos hγ0 hγ1 hZm hZind hZlaw hh
    have hcast : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ h), Nat.cast_one]
    rw [hcast] at hb
    simpa only [neg_sub] using hb
  · exact powEcho_tendstoInMeasure_runsEstimator one_pos hZm hZind hZlaw hZpos hγ0 hγ1 hu hk
      hr_inf hr_div_n hr_u hshort
  · exact powEcho_tendstoInMeasure_blocksEstimator one_pos hZm hZind hZlaw hγ0 hγ1 hu hk
      hr'_inf hr'_div_n hr'_u hlong

end NoUniversalPolyRule

end ExtremeValueTheory

