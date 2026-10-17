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

/-! ### Probabilistic estimates -/

section Probabilistic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The moving average `X_t = ∑_{i=0}^m ψ_i Z_{t-i}`. -/
noncomputable def process (m : ℕ) (ψ : ℕ → ℝ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  ∑ i ∈ range (m + 1), ψ i * Z (t - i) ω

theorem measurable_process {Z : ℤ → Ω → ℝ} (hZ : ∀ i, Measurable (Z i)) (t : ℤ) :
    Measurable (process m ψ Z t) :=
  Finset.measurable_sum _ fun _ _ => (hZ _).const_mul _

theorem process_nonneg (hψ0 : ∀ j, 0 ≤ ψ j) {Z : ℤ → Ω → ℝ} (hZ0 : ∀ i ω, 0 ≤ Z i ω) (t : ℤ)
    (ω : Ω) : 0 ≤ process m ψ Z t ω :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hψ0 i) (hZ0 _ ω)

/-- If `F / L → c > 0` and `L` is regularly varying with index `ρ`, so is `F`. -/
theorem isRegularlyVarying_of_tendsto_div {F L : ℝ → ℝ} {ρ c : ℝ} (hL : IsRegularlyVarying L ρ)
    (hc : 0 < c) (hF : Tendsto (fun x => F x / L x) atTop (𝓝 c)) : IsRegularlyVarying F ρ := by
  have hFpos : ∀ᶠ x in atTop, 0 < F x := by
    filter_upwards [hF.eventually (lt_mem_nhds hc), hL.1] with x hx hLx
    exact (div_pos_iff_of_pos_right hLx).1 hx
  refine ⟨hFpos, fun t ht => ?_⟩
  have htx : Tendsto (fun x : ℝ => t * x) atTop atTop := tendsto_id.const_mul_atTop ht
  have h := ((hF.comp htx).mul (hL.2 t ht)).div hF hc.ne'
  rw [mul_div_cancel_left₀ _ hc.ne'] at h
  refine h.congr' ?_
  filter_upwards [hFpos, hL.1, htx.eventually hL.1] with x hFx hLx hLtx
  simp only [Function.comp, Pi.div_apply]
  field_simp

variable [IsProbabilityMeasure P] {Z : ℤ → Ω → ℝ} {α : ℝ}

/-- **Tail of `X_0`**: `P(X_0 > x) / P(Z_0 > x) → ∑_{j ≤ m} ψ_j^α`. -/
theorem tendsto_measureReal_process_div (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j) :
    Tendsto (fun x => P.real {ω | x < process m ψ Z 0 ω} / P.real {ω | x < Z 0 ω}) atTop
      (𝓝 (weightSum m ψ α)) := by
  have habs : ∀ x, {ω | x < |Z 0 ω|} = {ω | x < Z 0 ω} := fun x => by
    ext ω; simp [abs_of_nonneg (hZ0 0 ω)]
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [habs] using hL
  have hp : Tendsto (fun x => P.real {ω | x < Z 0 ω} / P.real {ω | x < |Z 0 ω|}) atTop
      (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hL.1] with x hx
    rw [habs, div_self hx.ne']
  have hinj : Function.Injective fun i : ℕ => (0 : ℤ) - i := fun a b h => by
    simpa using h
  have h := LinearProcess.tendsto_measureReal_sum_mul_div (Z := fun i : ℕ => Z (0 - i))
    (fun i => hZ _) (hZ 0) (hind.precomp hinj) (fun i => hident _) hL' hp ψ (range (m + 1))
  simp only [habs] at h
  have hW : weightSum m ψ α = ∑ j ∈ range (m + 1), LinearProcess.tailWeight α 1 (ψ j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases (hψ0 j).eq_or_lt with h0 | hpos
    · rw [← h0, LinearProcess.tailWeight_zero, Real.zero_rpow hα.ne']
    · rw [LinearProcess.tailWeight_of_pos hpos, mul_one]
  rw [hW]
  exact h

/-- **Product formula**: `P(Z_{i₀} > a, Z_i ≤ b for i ∈ I \ {i₀}) = F̄(a) (1 - F̄(b))^{#I - 1}`. -/
theorem measureReal_gt_and_forall_le (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) {I : Finset ℤ} {i₀ : ℤ} (hi₀ : i₀ ∈ I)
    (a b : ℝ) :
    P.real {ω | a < Z i₀ ω ∧ ∀ i ∈ I, i ≠ i₀ → Z i ω ≤ b} =
      P.real {ω | a < Z 0 ω} * (1 - P.real {ω | b < Z 0 ω}) ^ (I.card - 1) := by
  classical
  set s : ℤ → Set ℝ := fun i => if i = i₀ then Ioi a else Iic b with hs
  have hsm : ∀ i ∈ I, MeasurableSet (s i) := fun i _ => by
    simp only [hs]; split_ifs
    · exact measurableSet_Ioi
    · exact measurableSet_Iic
  have hset : {ω | a < Z i₀ ω ∧ ∀ i ∈ I, i ≠ i₀ → Z i ω ≤ b} = ⋂ i ∈ I, Z i ⁻¹' s i := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Set.mem_preimage, hs]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      split_ifs with h
      · subst h; exact h1
      · exact h2 i hi h
    · intro h
      refine ⟨by simpa using h i₀ hi₀, fun i hi hne => ?_⟩
      simpa [hne] using h i hi
  have hle : ∀ i, P.real (Z i ⁻¹' Iic b) = 1 - P.real {ω | b < Z 0 ω} := fun i => by
    rw [measureReal_def, (hident i).measure_mem_eq measurableSet_Iic, ← measureReal_def,
      ← probReal_compl_eq_one_sub (measurableSet_lt measurable_const (hZ 0))]
    congr 1; ext ω; simp
  rw [hset, measureReal_def, hind.measure_inter_preimage_eq_mul I hsm, ENNReal.toReal_prod,
    ← Finset.mul_prod_erase I _ hi₀]
  congr 1
  · simp only [hs, ite_true]
    rw [ (hident i₀).measure_mem_eq measurableSet_Ioi]
    rfl
  · rw [← Finset.card_erase_of_mem hi₀, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [hs, Finset.ne_of_mem_erase hi, ite_false]
    exact hle i

/-- **Two large values**: `P(two coordinates of I exceed b) ≤ (#I)² F̄(b)²`. -/
theorem measureReal_two_gt_le (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (I : Finset ℤ) (b : ℝ) :
    P.real {ω | ∃ i ∈ I, ∃ i' ∈ I, i ≠ i' ∧ b < Z i ω ∧ b < Z i' ω} ≤
      (I.card : ℝ) ^ 2 * P.real {ω | b < Z 0 ω} ^ 2 := by
  classical
  have hsub : {ω | ∃ i ∈ I, ∃ i' ∈ I, i ≠ i' ∧ b < Z i ω ∧ b < Z i' ω} ⊆
      ⋃ p ∈ (I ×ˢ I).filter (fun p => p.1 ≠ p.2), (Z p.1 ⁻¹' Ioi b ∩ Z p.2 ⁻¹' Ioi b) := by
    rintro ω ⟨i, hi, i', hi', hne, h1, h2⟩
    simp only [mem_iUnion, Finset.mem_filter, Finset.mem_product]
    exact ⟨(i, i'), ⟨⟨hi, hi'⟩, hne⟩, h1, h2⟩
  have hpair : ∀ p ∈ (I ×ˢ I).filter (fun p => p.1 ≠ p.2),
      P.real (Z p.1 ⁻¹' Ioi b ∩ Z p.2 ⁻¹' Ioi b) = P.real {ω | b < Z 0 ω} ^ 2 := by
    intro p hp
    have hne := (Finset.mem_filter.1 hp).2
    rw [measureReal_def, (hind.indepFun hne).measure_inter_preimage_eq_mul _ _ measurableSet_Ioi
      measurableSet_Ioi, (hident p.1).measure_mem_eq measurableSet_Ioi,
      (hident p.2).measure_mem_eq measurableSet_Ioi, ENNReal.toReal_mul, sq]
    rfl
  calc _ ≤ P.real (⋃ p ∈ (I ×ˢ I).filter (fun p => p.1 ≠ p.2),
        (Z p.1 ⁻¹' Ioi b ∩ Z p.2 ⁻¹' Ioi b)) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ p ∈ (I ×ˢ I).filter (fun p => p.1 ≠ p.2),
        P.real (Z p.1 ⁻¹' Ioi b ∩ Z p.2 ⁻¹' Ioi b) := measureReal_biUnion_finset_le _ _
    _ = ((I ×ˢ I).filter (fun p => p.1 ≠ p.2)).card * P.real {ω | b < Z 0 ω} ^ 2 := by
        rw [Finset.sum_congr rfl hpair, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (I.card : ℝ) ^ 2 * P.real {ω | b < Z 0 ω} ^ 2 := by
        gcongr
        calc (((I ×ˢ I).filter (fun p => p.1 ≠ p.2)).card : ℝ) ≤ ((I ×ˢ I).card : ℝ) := by
              exact_mod_cast Finset.card_filter_le _ _
          _ = (I.card : ℝ) ^ 2 := by rw [Finset.card_product]; push_cast; ring

end Probabilistic

/-! ### Single big jump events -/

section Events

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The noise indices `t - i`, `t ∈ S ∪ {0}`, `i ≤ m`, entering `X_t` for `t` in the window. -/
def window (m : ℕ) (S : Finset ℤ) : Finset ℤ :=
  (insert 0 S).biUnion fun t => (range (m + 1)).image fun i : ℕ => t - i

theorem sub_mem_window {S : Finset ℤ} {t : ℤ} (ht : t ∈ insert 0 S) {i : ℕ}
    (hi : i ∈ range (m + 1)) : t - i ∈ window m S :=
  Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image.2 ⟨i, hi, rfl⟩⟩

theorem neg_mem_window (S : Finset ℤ) {j : ℕ} (hj : j ∈ range (m + 1)) :
    -(j : ℤ) ∈ window m S := by
  simpa using sub_mem_window (S := S) (Finset.mem_insert_self 0 S) hj

/-- `Z_{-j} > a` while all other noise variables of the window are `≤ b`. -/
def bigJump (I : Finset ℤ) (Z : ℤ → Ω → ℝ) (j : ℕ) (a b : ℝ) : Set Ω :=
  {ω | a < Z (-(j : ℤ)) ω ∧ ∀ i ∈ I, i ≠ -(j : ℤ) → Z i ω ≤ b}

/-- Two noise variables of the window exceed `b`. -/
def twoBig (I : Finset ℤ) (Z : ℤ → Ω → ℝ) (b : ℝ) : Set Ω :=
  {ω | ∃ i ∈ I, ∃ i' ∈ I, i ≠ i' ∧ b < Z i ω ∧ b < Z i' ω}

variable {Z : ℤ → Ω → ℝ}

theorem measurableSet_bigJump (hZ : ∀ i, Measurable (Z i)) (I : Finset ℤ) (j : ℕ) (a b : ℝ) :
    MeasurableSet (bigJump I Z j a b) := by
  have h1 : MeasurableSet {ω | a < Z (-(j : ℤ)) ω} := measurableSet_lt measurable_const (hZ _)
  have h2 : MeasurableSet {ω | ∀ i ∈ I, i ≠ -(j : ℤ) → Z i ω ≤ b} := by
    have : {ω | ∀ i ∈ I, i ≠ -(j : ℤ) → Z i ω ≤ b} =
        ⋂ i ∈ (I.filter fun i => i ≠ -(j : ℤ)), {ω | Z i ω ≤ b} := by
      ext ω; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun i _ => measurableSet_le (hZ i) measurable_const
  exact h1.inter h2

theorem bigJump_disjoint {I : Finset ℤ} {j j' : ℕ} (hj : -(j : ℤ) ∈ I) (hjj' : j ≠ j') (b : ℝ) :
    Disjoint (bigJump I Z j b b) (bigJump I Z j' b b) := by
  rw [Set.disjoint_left]
  rintro ω ⟨h1, -⟩ ⟨-, h2⟩
  exact absurd (h2 _ hj (by omega)) (not_le.2 h1)

variable [IsProbabilityMeasure P]

theorem measureReal_bigJump (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) {I : Finset ℤ} {j : ℕ} (hj : -(j : ℤ) ∈ I)
    (a b : ℝ) :
    P.real (bigJump I Z j a b) =
      P.real {ω | a < Z 0 ω} * (1 - P.real {ω | b < Z 0 ω}) ^ (I.card - 1) :=
  measureReal_gt_and_forall_le hZ hind hident hj a b

end Events

section Inclusions

variable {Ω : Type*} {Z : ℤ → Ω → ℝ} {S : Finset ℤ}
variable (hψ0 : ∀ j, 0 ≤ ψ j) (hψm : ∀ j, m < j → ψ j = 0) (hZ0 : ∀ i ω, 0 ≤ Z i ω)
include hψ0 hψm hZ0

omit hψm in
/-- `Z_{-j} > x / ψ_j` (and the rest small) forces `X_0 > x` and the big jump event. -/
theorem bigJump_subset {j : ℕ} (hjm : j ∈ range (m + 1)) (hj : 0 < ψ j) {η x : ℝ}
    (hη : η * ψ j ≤ 1) (hx : 0 < x) :
    bigJump (window m S) Z j ((ψ j)⁻¹ * x) (η * x) ⊆
      {ω | x < |process m ψ Z 0 ω|} ∩ bigJump (window m S) Z j (η * x) (η * x) := by
  rintro ω ⟨h1, h2⟩
  refine ⟨?_, ?_, h2⟩
  · rw [mem_ofPred_eq, abs_of_nonneg (process_nonneg hψ0 hZ0 0 ω)]
    have hle : ψ j * Z (0 - j) ω ≤ process m ψ Z 0 ω :=
      Finset.single_le_sum (f := fun i => ψ i * Z (0 - i) ω)
        (fun i _ => mul_nonneg (hψ0 i) (hZ0 _ ω)) hjm
    rw [zero_sub] at hle
    have : x < ψ j * Z (-(j : ℤ)) ω := by
      rw [inv_mul_lt_iff₀ hj] at h1; exact h1
    linarith
  · have : η * x ≤ (ψ j)⁻¹ * x := by
      rw [← div_eq_inv_mul, le_div_iff₀ hj]
      nlinarith
    exact this.trans_lt h1

/-- On `X_0 > x` and the big jump event, `Z_{-j} > (1 - η∑ψ) x / ψ_j`. -/
theorem inter_bigJump_subset {j : ℕ} (hj : 0 < ψ j) {η x : ℝ}
    (hη : 0 ≤ η) (hx : 0 < x) :
    {ω | x < |process m ψ Z 0 ω|} ∩ bigJump (window m S) Z j (η * x) (η * x) ⊆
      bigJump (window m S) Z j
        (((ψ j)⁻¹ * (1 - η * ∑ i ∈ range (m + 1), ψ i)) * x) (η * x) := by
  rintro ω ⟨hX, -, h2⟩
  refine ⟨?_, h2⟩
  rw [mem_ofPred_eq, abs_of_nonneg (process_nonneg hψ0 hZ0 0 ω)] at hX
  have hdec := sum_eq_coef_mul_add hψm (fun i => Z i ω) j 0
  rw [add_zero, coef_natCast] at hdec
  have hR := rem_le hψ0 (z := fun i => Z i ω) (by positivity : 0 ≤ η * x) j 0
    fun i hi h => h2 _ (sub_mem_window (Finset.mem_insert_self 0 S) hi) h
  change x < ∑ i ∈ range (m + 1), ψ i * Z (0 - i) ω at hX
  rw [mul_assoc, inv_mul_lt_iff₀ hj]
  nlinarith

/-- On `X_0 > x` and the big jump event, `X_t / X_0` is close to `ψ_{j+t} / ψ_j`. -/
theorem abs_ratio_sub_le {j : ℕ} (hj : 0 < ψ j) {η x : ℝ} (hη : 0 ≤ η) (hx : 0 < x)
    {ω : Ω} (hω : ω ∈ {ω | x < |process m ψ Z 0 ω|} ∩ bigJump (window m S) Z j (η * x) (η * x))
    {t : ℤ} (ht : t ∈ S) :
    |process m ψ Z t ω / |process m ψ Z 0 ω| - coef ψ (j + t) / ψ j| ≤
      η * (∑ i ∈ range (m + 1), ψ i) * (ψ j + coef ψ (j + t)) / ψ j := by
  obtain ⟨hX, -, h2⟩ := hω
  change x < |process m ψ Z 0 ω| at hX
  rw [abs_of_nonneg (process_nonneg hψ0 hZ0 0 ω)] at hX ⊢
  have h := abs_div_sub_le hψ0 hψm (z := fun i => Z i ω) (by positivity : 0 ≤ η * x) hx hj t
    (fun s hs i hi hne => ⟨hZ0 _ ω, h2 _ (sub_mem_window (by
      rcases Finset.mem_insert.1 hs with h | h
      · rw [h]; exact Finset.mem_insert_self 0 S
      · rw [Finset.mem_singleton.1 h]; exact Finset.mem_insert_of_mem ht) hi) hne⟩) hX
  refine h.trans (le_of_eq ?_)
  field_simp

omit hψm in
/-- **Coverage**: `{X_0 > x}` is covered by the big jump events and the double exceedances. -/
theorem subset_iUnion_bigJump_union {η x : ℝ}
    (hη : η * ∑ i ∈ range (m + 1), ψ i ≤ 1) (hx : 0 < x) :
    {ω | x < |process m ψ Z 0 ω|} ⊆
      (⋃ j ∈ (range (m + 1)).filter (fun j => 0 < ψ j),
        bigJump (window m S) Z j (η * x) (η * x)) ∪ twoBig (window m S) Z (η * x) := by
  intro ω hω
  rw [mem_ofPred_eq, abs_of_nonneg (process_nonneg hψ0 hZ0 0 ω)] at hω
  change x < ∑ i ∈ range (m + 1), ψ i * Z (0 - i) ω at hω
  simp only [zero_sub] at hω
  rcases coverage hψ0 (I := window m S) (z := fun i => Z i ω) (fun j hj => neg_mem_window S hj)
    (b := η * x) (by nlinarith) hω with ⟨j, hj, hpos, h1, h2⟩ | h
  · left
    simp only [mem_iUnion, Finset.mem_filter]
    exact ⟨j, ⟨hj, hpos⟩, h1, h2⟩
  · exact Or.inr h

end Inclusions

end MovingAverage

end ExtremeValueTheory
