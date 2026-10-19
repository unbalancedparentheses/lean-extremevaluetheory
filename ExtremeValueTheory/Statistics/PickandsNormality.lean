/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.TailEmpiricalProcessRV
import ExtremeValueTheory.Statistics.MomentNormality
import ExtremeValueTheory.ForMathlib.Probability.DeltaMethod

/-!
# Asymptotic normality of the Pickands estimator
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Intermediate order statistics and the tail empirical process -/

section TailOrderStat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The normalized intermediate uniform order statistic `(n/k) (1 - U_{(j+1)})`. -/
noncomputable def tailTime (U : ℕ → Ω → ℝ) (n k j : ℕ) (ω : Ω) : ℝ :=
  (1 - orderStat (fun i : Fin n => U i ω) j) / (k / n)

/-- Below the normalized order statistic `T = (n/k)(1 - U_{(j+1)})` the count of exceedances is
at most `j`: `√k W_n(t) ≤ j - k t`. -/
theorem sqrt_mul_tailEmpiricalProcess_le_of_lt_tailTime {U : ℕ → Ω → ℝ} {ω : Ω} {n k j : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hjn : j < n) {t : ℝ} (ht : t < tailTime U n k j ω) :
    √(k : ℝ) * tailEmpiricalProcess U n k t ω ≤ j - k * t := by
  have hp : (0 : ℝ) < k / n := by positivity
  rw [sqrt_mul_tailEmpiricalProcess U n hk t ω]
  have := sum_range_indicator_le_of_lt (U := U) (ω := ω) (k := k) hjn (t := t)
    (by rw [tailTime, lt_div_iff₀ hp] at ht; linarith)
  linarith

/-- Above the normalized order statistic the count of exceedances is at least `j + 1`:
`√k W_n(t) ≥ j + 1 - k t`. -/
theorem le_sqrt_mul_tailEmpiricalProcess_of_tailTime_le {U : ℕ → Ω → ℝ} {ω : Ω} {n k j : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hjn : j < n) {t : ℝ} (ht : tailTime U n k j ω ≤ t) :
    (j : ℝ) + 1 - k * t ≤ √(k : ℝ) * tailEmpiricalProcess U n k t ω := by
  have hp : (0 : ℝ) < k / n := by positivity
  rw [sqrt_mul_tailEmpiricalProcess U n hk t ω]
  have := le_sum_range_indicator_of_le (U := U) (ω := ω) (k := k) hjn (t := t)
    (by rw [tailTime, div_le_iff₀ hp] at ht; linarith)
  linarith

/-- Deterministic core of the representation of intermediate order statistics: if `W_n` is close
to `W_n(m)` on the window `m + [-(M + ε), M + ε] / √k` and `|W_n(m)| < M`, then
`|√k (m - T) - W_n(m)| < ε` for `T = (n/k)(1 - U_{(mk+1)})`. -/
theorem abs_sqrt_mul_sub_tailTime_sub_lt {U : ℕ → Ω → ℝ} {ω : Ω} {n k m : ℕ} (hk : 0 < k)
    (hn : 0 < n) (hjn : m * k < n) {ε M : ℝ} (hε : 0 < ε)
    (hw : |tailEmpiricalProcess U n k m ω| < M)
    (hwin : ∀ c : ℝ, |c| ≤ M + ε → |tailEmpiricalProcess U n k (m + c / √(k : ℝ)) ω -
      tailEmpiricalProcess U n k m ω| ≤ ε / 2) :
    |√(k : ℝ) * ((m : ℝ) - tailTime U n k (m * k) ω) - tailEmpiricalProcess U n k m ω| < ε := by
  set s := √(k : ℝ) with hs
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : 0 < s := Real.sqrt_pos.2 hk'
  have hss : s * s = k := Real.mul_self_sqrt hk'.le
  set T := tailTime U n k (m * k) ω with hT
  set w := tailEmpiricalProcess U n k m ω with hw'
  rw [abs_lt] at hw
  have hkt : ∀ c : ℝ, (k : ℝ) * (m + c / s) = k * m + s * c := by
    intro c
    rw [← hss]
    field_simp
  have hprod : s * (T - m) = -(s * (m - T)) := by ring
  rw [abs_lt]
  constructor
  · by_contra hneg
    push Not at hneg
    have hTm : -w + ε ≤ s * (T - m) := by linarith
    have htT : (m : ℝ) + (-w + 3 * ε / 4) / s < T := by
      have : (-w + 3 * ε / 4) / s < T - m := by
        rw [div_lt_iff₀ hs0, mul_comm]; linarith
      linarith
    have h1 := sqrt_mul_tailEmpiricalProcess_le_of_lt_tailTime hk hn hjn htT
    push_cast at h1
    rw [hkt] at h1
    have e : (m : ℝ) * k - (k * m + s * (-w + 3 * ε / 4)) = s * (w - 3 * ε / 4) := by ring
    rw [e] at h1
    have hWt := le_of_mul_le_mul_left h1 hs0
    have hwt := hwin (-w + 3 * ε / 4) (by rw [abs_le]; constructor <;> linarith)
    rw [abs_le] at hwt
    linarith [hwt.1]
  · by_contra hpos
    push Not at hpos
    have hTm : s * (T - m) ≤ -w - ε := by linarith
    have hTt : T ≤ (m : ℝ) + (-w - ε / 2) / s := by
      have : T - m ≤ (-w - ε / 2) / s := by
        rw [le_div_iff₀ hs0, mul_comm]; linarith
      linarith
    have h1 := le_sqrt_mul_tailEmpiricalProcess_of_tailTime_le hk hn hjn hTt
    push_cast at h1
    rw [hkt] at h1
    have e : (m : ℝ) * k + 1 - (k * m + s * (-w - ε / 2)) = s * (w + ε / 2) + 1 := by ring
    rw [e] at h1
    have h2 : s * (w + ε / 2) < s * tailEmpiricalProcess U n k (m + (-w - ε / 2) / s) ω := by
      linarith
    have hWt := lt_of_mul_lt_mul_left h2 hs0.le
    have hwt := hwin (-w - ε / 2) (by rw [abs_le]; constructor <;> linarith)
    rw [abs_le] at hwt
    linarith [hwt.2]

variable [IsProbabilityMeasure P] {U : ℕ → Ω → ℝ} {k : ℕ → ℕ}

/-- **Bahadur–Kiefer-type representation of intermediate uniform order statistics** ([dHF,
Theorem 2.4.8], at fixed times): for iid uniform `U_i`, an intermediate sequence `k` and an
integer `m ≥ 1`, `√k (m - (n/k)(1 - U_{(mk+1)})) - W_n(m) → 0` in probability. -/
theorem tendstoInMeasure_sqrt_mul_sub_tailTime (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) :
    TendstoInMeasure P (fun n ω => √(k n : ℝ) * ((m : ℝ) - tailTime U n (k n) (m * k n) ω) -
      tailEmpiricalProcess U n (k n) m ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hsR : Tendsto (fun n => √(k n : ℝ)) atTop atTop := tendsto_sqrt_atTop.comp hkR
  set S : ℕ → Set Ω := fun n => {ω | ε ≤ dist (√(k n : ℝ) * ((m : ℝ) -
    tailTime U n (k n) (m * k n) ω) - tailEmpiricalProcess U n (k n) m ω) 0} with hSdef
  -- it suffices to bound the real probabilities
  suffices key : ∀ δ > 0, ∀ᶠ n in atTop, P.real (S n) ≤ δ by
    have hreal : Tendsto (fun n => P.real (S n)) atTop (𝓝 0) := by
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
        lt_of_lt_of_le ha measureReal_nonneg, fun a ha => ?_⟩
      filter_upwards [key (a / 2) (half_pos ha)] with n hn
      linarith
    have := ENNReal.tendsto_ofReal hreal
    rw [ENNReal.ofReal_zero] at this
    refine this.congr fun n => ?_
    rw [ofReal_measureReal]
  intro δ hδ
  set M : ℝ := 2 * m / δ + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have : 0 ≤ 2 * m / δ := by positivity
                         linarith
  have hM0 : 0 < M := by linarith
  have hmM : (m : ℝ) / M ^ 2 ≤ δ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : M ≤ M ^ 2 := by nlinarith
    have h2 : 2 * m / δ ≤ M := by linarith
    have h3 : (m : ℝ) ≤ δ / 2 * M := by
      rw [div_le_iff₀ hδ] at h2; linarith
    nlinarith
  set lam : ℝ := ε / 8 with hlam
  have hlam0 : 0 < lam := by positivity
  set R : ℝ := M + ε with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (2 * R / lam) (by norm_num : (1 : ℝ) < 2)
  have hq' : 2 * R / 2 ^ q ≤ lam := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hlam0] at hq
    linarith
  -- the oscillation bound tends to zero
  have hosc : Tendsto (fun n => 8 ^ 4 / lam ^ 4 * (84 * (2 * R / √(k n : ℝ)) ^ 2 +
      2 ^ (q + 2) * (2 * R / √(k n : ℝ)) / k n)) atTop (𝓝 (8 ^ 4 / lam ^ 4 * (84 * 0 ^ 2 +
      2 ^ (q + 2) * 0 * 0))) := by
    have h1 : Tendsto (fun n => 2 * R / √(k n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsR
    have h2 : Tendsto (fun n => ((k n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
    refine tendsto_const_nhds.mul ((tendsto_const_nhds.mul (h1.pow 2)).add
      ((tendsto_const_nhds.mul h1).mul h2) |>.congr fun n => ?_)
    simp only [div_eq_mul_inv]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    at hosc
  have hlev : Tendsto (fun n => (k n : ℝ) / n * (m + R / √(k n : ℝ))) atTop (𝓝 (0 * (m + 0))) :=
    hkn.mul (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hsR))
  rw [zero_mul] at hlev
  have hkm : ∀ᶠ n in atTop, m * k n < n := by
    have := hkn.const_mul (m : ℝ)
    rw [mul_zero] at this
    filter_upwards [this.eventually (gt_mem_nhds one_pos),
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0] with n h1 h2
    rw [← mul_div_assoc, div_lt_one h2] at h1
    exact_mod_cast h1
  filter_upwards [hosc.eventually (ge_mem_nhds (half_pos hδ)), hlev.eventually (ge_mem_nhds
    one_pos), hk.eventually_gt_atTop 0, hsR.eventually_ge_atTop (R / m), hkm,
    eventually_gt_atTop 0] with n hosc_n hlev_n hk0 hsk hjn hn0
  set s : ℝ := √(k n : ℝ) with hs
  have hk' : (0 : ℝ) < k n := by exact_mod_cast hk0
  have hs0 : 0 < s := Real.sqrt_pos.2 hk'
  have hss : s * s = k n := Real.mul_self_sqrt hk'.le
  set W : ℝ → Ω → ℝ := fun t ω => tailEmpiricalProcess U n (k n) t ω with hW
  set a : ℝ := m - R / s with ha
  set L : ℝ := 2 * R / s with hL
  have hRs : R / s ≤ m := by rw [div_le_iff₀ hs0]; rw [div_le_iff₀ hm'] at hsk; linarith
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have haL : a + L = m + R / s := by rw [ha, hL]; ring
  have hL0 : 0 < L := by positivity
  have hp : (k n : ℝ) / n * (a + L) ≤ 1 := by rw [haL]; exact hlev_n
  have hpm : (k n : ℝ) / n * m ≤ 1 := by
    refine le_trans ?_ hp
    gcongr
    rw [haL]; linarith [div_nonneg hR0.le hs0.le]
  have hqL : √(k n : ℝ) * (L / 2 ^ q) ≤ lam := by
    have e : s * (L / 2 ^ q) = 2 * R / 2 ^ q := by rw [hL]; field_simp
    rw [← hs, e]; exact hq'
  have hosc' := measureReal_exists_abs_tailEmpiricalProcess_sub_gt_le hU hind hlaw
    (n := n) (k := k n) hn0.ne' ha0 hL0 hp hlam0 q hqL
  have hcheb := measureReal_le_abs_tailEmpiricalProcess_le hU hind hlaw (n := n) (k := k n)
    hn0 hk0 hm'.le hpm hM0
  -- the inclusion
  have hsub : S n ⊆ {ω | M ≤ |W m ω|} ∪ {ω | ∃ u ∈ Set.Icc a (a + L),
      2 * lam < |W u ω - W a ω|} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_exists, not_and, not_lt] at hcon
    obtain ⟨hwM, hosc⟩ := hcon
    have hwin : ∀ c : ℝ, |c| ≤ M + ε →
        |W (m + c / √(k n : ℝ)) ω - W m ω| ≤ ε / 2 := by
      intro c hc
      have hcs : |c / s| ≤ R / s := by
        rw [abs_div, abs_of_pos hs0]; exact div_le_div_of_nonneg_right hc hs0.le
      rw [abs_le] at hcs
      have hRs0 : 0 ≤ R / s := div_nonneg hR0.le hs0.le
      have hu' : (m : ℝ) + c / s ∈ Set.Icc a (a + L) :=
        ⟨by rw [ha]; linarith, by rw [haL]; linarith⟩
      have hm'' : (m : ℝ) ∈ Set.Icc a (a + L) := ⟨by rw [ha]; linarith, by rw [haL]; linarith⟩
      have h1 := hosc _ hu'
      have h2 := hosc (m : ℝ) hm''
      calc |W (m + c / s) ω - W m ω| = |(W (m + c / s) ω - W a ω) - (W m ω - W a ω)| := by
            ring_nf
        _ ≤ |W (m + c / s) ω - W a ω| + |W m ω - W a ω| := abs_sub _ _
        _ ≤ ε / 2 := by rw [hlam] at h1 h2; linarith
    have := abs_sqrt_mul_sub_tailTime_sub_lt hk0 hn0 hjn hε hwM hwin
    simp only [hSdef, mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
    linarith
  calc P.real (S n) ≤ P.real ({ω | M ≤ |W m ω|} ∪ {ω | ∃ u ∈ Set.Icc a (a + L),
        2 * lam < |W u ω - W a ω|}) := measureReal_mono hsub
    _ ≤ P.real {ω | M ≤ |W m ω|} + P.real {ω | ∃ u ∈ Set.Icc a (a + L),
        2 * lam < |W u ω - W a ω|} := measureReal_union_le _ _
    _ ≤ m / M ^ 2 + δ / 2 := add_le_add hcheb (hosc'.trans (by rw [hL]; exact hosc_n))
    _ ≤ δ := by linarith

end TailOrderStat

end ExtremeValueTheory
