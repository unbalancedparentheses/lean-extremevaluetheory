/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.TailEmpiricalProcessRV
import ExtremeValueTheory.Statistics.MomentNormality
import ExtremeValueTheory.ForMathlib.Probability.DeltaMethod
import ExtremeValueTheory.RegularVariation.Extended

/-!
# Asymptotic normality of the Pickands estimator
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

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

/-! ### Joint convergence of finitely many intermediate order statistics -/

section Joint

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Convergence in probability to `0` in `ℝ^ι` follows from convergence of the coordinates. -/
theorem tendstoInMeasure_euclideanSpace_zero {ι : Type*} [Fintype ι]
    {f : ℕ → Ω → EuclideanSpace ℝ ι}
    (h : ∀ i, TendstoInMeasure P (fun n ω => f n ω i) atTop (fun _ => 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set c : ℝ := (Fintype.card ι : ℝ) + 1 with hc
  have hc1 : 1 ≤ c := by rw [hc]; linarith [(Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)]
  have hη : 0 < ε / c := by positivity
  have hi := fun i => (tendstoInMeasure_iff_norm.1 (h i)) (ε / c) hη
  have hsum := tendsto_finset_sum (Finset.univ : Finset ι) fun i _ => hi i
  simp only [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) fun n => ?_
  refine (measure_mono fun ω hω => ?_).trans (measure_iUnion_fintype_le P _)
  simp only [mem_iUnion, mem_ofPred_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  have hsq : ‖f n ω‖ ^ 2 < ε ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, f n ω i ^ 2 ≤ ∑ _i : ι, (ε / c) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hcon i
          rw [Real.norm_eq_abs] at this
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this.le 2
      _ = (Fintype.card ι : ℝ) * (ε / c) ^ 2 := by simp
      _ < ε ^ 2 := by
          rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
          have : (Fintype.card ι : ℝ) < c ^ 2 := by rw [hc]; nlinarith
          have hε2 : 0 < ε ^ 2 := by positivity
          nlinarith [mul_lt_mul_of_pos_right this hε2]
  have := lt_of_pow_lt_pow_left₀ 2 hε.le hsq
  linarith

variable {U : ℕ → Ω → ℝ} {k : ℕ → ℕ}

theorem measurable_tailTime (hU : ∀ i, Measurable (U i)) (n k j : ℕ) :
    Measurable (tailTime U n k j) :=
  ((measurable_const.sub (measurable_orderStat (X := fun i : Fin n => U i)
    (fun i => hU i) j)).div_const _)

/-- **Joint asymptotic normality of intermediate uniform order statistics** ([dHF, Theorem 2.4.8]
at finitely many times): for integers `τ_i ≥ 1`, the vector
`(√k (τ_i - (n/k)(1 - U_{(τ_i k + 1)})))_i` converges in distribution to the centered Gaussian
vector with covariance `min τ_i τ_j` (Brownian motion at the times `τ_i`). -/
theorem tendstoInDistribution_sqrt_smul_tailTime (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℕ) (hτ : ∀ i, 0 < τ i) :
    TendstoInDistribution (fun n ω => √(k n : ℝ) •
        (WithLp.toLp 2 (fun i => -tailTime U n (k n) (τ i * k n) ω) -
          WithLp.toLp 2 (fun i => -(τ i : ℝ)) : EuclideanSpace ℝ ι))
      atTop id (fun _ => P) (multivariateGaussian 0 (brownianCovMatrix fun i => (τ i : ℝ≥0))) := by
  have hfdd := tendstoInDistribution_tailEmpiricalProcess_comp hU hind hlaw hk hkn
    (fun i => (τ i : ℝ≥0))
  have hV := hfdd.continuous_comp (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))
  have hV' : TendstoInDistribution (fun n => WithLp.toLp 2 ∘ fun ω (i : ι) =>
      tailEmpiricalProcess U n (k n) (τ i : ℝ≥0) ω) atTop
      (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (fun _ => P)
      (multivariateGaussian 0 (brownianCovMatrix fun i => (τ i : ℝ≥0))) := by
    refine ⟨hV.forall_aemeasurable, aemeasurable_id, ?_⟩
    have e : (⟨(multivariateGaussian 0 (brownianCovMatrix fun i => (τ i : ℝ≥0))).map id,
        inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ ι)) =
        ⟨(brownianFdd fun i => (τ i : ℝ≥0)).map (WithLp.toLp 2 ∘ id), inferInstance⟩ := by
      refine Subtype.ext ?_
      change _ = Measure.map _ (Measure.map WithLp.ofLp _)
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [e]
    exact hV.tendsto
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ id hV' ?_ (fun n => ?_)
  · refine tendstoInMeasure_euclideanSpace_zero fun i => ?_
    have hB := tendstoInMeasure_sqrt_mul_sub_tailTime hU hind hlaw hk hkn (hτ i)
    refine tendstoInMeasure_of_eventuallyEq hB (Eventually.of_forall fun n ω => ?_)
    simp only [Pi.sub_apply, Function.comp_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, NNReal.coe_natCast]
    ring
  · have hm : Measurable (fun ω => (WithLp.toLp 2
        (fun i => -tailTime U n (k n) (τ i * k n) ω) : EuclideanSpace ℝ ι)) :=
      (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2
        fun i => (measurable_tailTime hU n (k n) _).neg)
    exact ((measurable_const (a := √(k n : ℝ))).smul (hm.sub_const _)).aemeasurable

end Joint

/-! ### Second-order extended regular variation -/

section SecondOrder

/-- The limit function of second-order extended regular variation ([dHF, Theorem 2.3.3]),
`H_{γ,ρ}(x) = ∫_1^x s^{γ-1} ∫_1^s u^{ρ-1} du ds = ∫_1^x s^{γ-1} h_ρ(s) ds`. For `ρ < 0` and
`γ, γ + ρ ≠ 0` this is `(1/ρ) ((x^{γ+ρ} - 1)/(γ+ρ) - (x^γ - 1)/γ)`. -/
noncomputable def extSecondOrderLimit (γ ρ x : ℝ) : ℝ :=
  ∫ s in (1 : ℝ)..x, s ^ (γ - 1) * boxCox ρ s

/-- **Second-order extended regular variation** ([dHF, Definition 2.3.1 and Theorem 2.3.3]),
in the locally uniform form of [dHF, Theorem 2.3.9 / Remark B.3.? ]: `a > 0` eventually, `A` has
eventually constant sign, `A(t) → 0`, `|A|` is regularly varying with index `ρ ≤ 0`, and

  `((U(xt) - U(t)) / a(t) - D_γ(x)) / A(t) → H_{γ,ρ}(x)`

locally uniformly in `x ∈ (0, ∞)`. -/
structure IsExtSecondOrderRegularlyVarying (U : ℝ → ℝ) (γ ρ : ℝ) (a A : ℝ → ℝ) : Prop where
  eventually_pos : ∀ᶠ t in atTop, 0 < a t
  nonpos : ρ ≤ 0
  tendsto_zero : Tendsto A atTop (𝓝 0)
  sign : (∀ᶠ t in atTop, 0 < A t) ∨ (∀ᶠ t in atTop, A t < 0)
  isRegularlyVarying_abs : IsRegularlyVarying (fun t => |A t|) ρ
  tendstoLocallyUniformlyOn : TendstoLocallyUniformlyOn
    (fun t x => ((U (x * t) - U t) / a t - extRVLimit γ x) / A t) (extSecondOrderLimit γ ρ)
    atTop (Ioi 0)

theorem continuousOn_rpow_mul_boxCox (γ ρ : ℝ) :
    ContinuousOn (fun s : ℝ => s ^ (γ - 1) * boxCox ρ s) (Ioi 0) := by
  refine ContinuousOn.mul (fun s hs => (continuousAt_rpow_const _ _
    (Or.inl (ne_of_gt hs))).continuousWithinAt) ?_
  unfold boxCox
  split_ifs with h
  · exact continuousOn_log.mono fun s hs => ne_of_gt hs
  · exact ((continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt hs)).sub
      continuousOn_const).div_const _

theorem continuousAt_extSecondOrderLimit (γ ρ : ℝ) {c : ℝ} (hc : 0 < c) :
    ContinuousAt (extSecondOrderLimit γ ρ) c := by
  have hcont := continuousOn_rpow_mul_boxCox γ ρ
  have hsub : Set.uIcc (1 : ℝ) c ⊆ Ioi 0 := fun s hs => by
    rcases Set.mem_uIcc.1 hs with h | h <;> simp only [mem_Ioi] <;> linarith [h.1]
  have hii : IntervalIntegrable (fun s : ℝ => s ^ (γ - 1) * boxCox ρ s) volume 1 c :=
    (hcont.mono hsub).intervalIntegrable
  exact (intervalIntegral.integral_hasDerivAt_right hii
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi c hc)
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hc))).continuousAt

end SecondOrder

/-! ### The Pickands map and its gradient -/

section PickandsMap

theorem hasDerivAt_extRVLimit (γ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (extRVLimit γ) (x ^ (γ - 1)) x := by
  by_cases hγ : γ = 0
  · subst hγ
    have : extRVLimit 0 = Real.log := funext extRVLimit_zero_left
    rw [this, zero_sub, rpow_neg_one]
    exact hasDerivAt_log hx.ne'
  · have : extRVLimit γ = fun y => (y ^ γ - 1) / γ := funext (extRVLimit_of_ne hγ)
    rw [this]
    have h := ((hasDerivAt_rpow_const (p := γ) (Or.inl hx.ne')).sub_const 1).div_const γ
    convert h using 1
    field_simp

theorem hasDerivAt_extRVLimit_four_div (γ : ℝ) {y : ℝ} (hy : y < 0) :
    HasDerivAt (fun y => extRVLimit γ (4 / -y)) ((4 / -y) ^ (γ - 1) * (4 / y ^ 2)) y := by
  have h1 : HasDerivAt (fun y : ℝ => -4 * y⁻¹) (-4 * -(y ^ 2)⁻¹) y :=
    (hasDerivAt_inv hy.ne).const_mul (-4)
  have e : (fun y : ℝ => -4 * y⁻¹) = fun y => 4 / -y := by
    funext y; rw [div_neg, div_eq_mul_inv]; ring
  rw [e] at h1
  have hpos : 0 < 4 / -y := div_pos (by norm_num) (by linarith)
  have h2 := (hasDerivAt_extRVLimit γ hpos).comp y h1
  refine h2.congr_deriv ?_
  congr 1
  field_simp

/-- The Pickands statistic as a function of the normalized order statistics:
`ψ(y) = log (D_γ(4/(-y₀)) - D_γ(4/(-y₁))) - log (D_γ(4/(-y₁)) - D_γ(4/(-y₂)))`. With
`y_i = -(n/k)(1 - U_{(τ_i k + 1)})`, `τ = (1, 2, 4)`, this is `log 2 ×` the Pickands estimator of
an exact generalized Pareto sample. -/
noncomputable def pickandsMap (γ : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.log (extRVLimit γ (4 / -y 0) - extRVLimit γ (4 / -y 1)) -
    Real.log (extRVLimit γ (4 / -y 1) - extRVLimit γ (4 / -y 2))

/-- The times `1, 2, 4` of the Pickands estimator. -/
def pickandsTimes : Fin 3 → ℕ := ![1, 2, 4]

/-- The centering point `(-1, -2, -4)`. -/
noncomputable def pickandsCenter : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => -(pickandsTimes i : ℝ))

/-- The gradient of `pickandsMap γ` at `pickandsCenter`. -/
noncomputable def pickandsGrad (γ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 ^ γ / extRVLimit γ 2, -(1 + 2 ^ γ) / (2 * extRVLimit γ 2),
    1 / (4 * extRVLimit γ 2)]

theorem extRVLimit_four (γ : ℝ) :
    extRVLimit γ 4 - extRVLimit γ 2 = 2 ^ γ * extRVLimit γ 2 := by
  have h := extRVLimit_mul (γ := γ) (x := 2) (y := 2) two_pos two_pos
  norm_num at h
  linarith

theorem pickandsMap_center (γ : ℝ) : pickandsMap γ pickandsCenter = γ * Real.log 2 := by
  have hd : 0 < extRVLimit γ 2 := extRVLimit_pos one_lt_two
  simp only [pickandsMap, pickandsCenter, pickandsTimes, WithLp.ofLp_toLp]
  norm_num
  rw [extRVLimit_one, sub_zero, extRVLimit_four, Real.log_mul (by positivity) hd.ne',
    Real.log_rpow two_pos]
  ring

theorem hasGradientAt_pickandsMap (γ : ℝ) :
    HasGradientAt (pickandsMap γ) (pickandsGrad γ) pickandsCenter := by
  set D := extRVLimit γ with hD
  have hd : 0 < D 2 := extRVLimit_pos one_lt_two
  have hv0 : pickandsCenter 0 = -1 := by simp [pickandsCenter, pickandsTimes]
  have hv1 : pickandsCenter 1 = -2 := by simp [pickandsCenter, pickandsTimes]
  have hv2 : pickandsCenter 2 = -4 := by simp [pickandsCenter, pickandsTimes]
  have hc : ∀ i, pickandsCenter i < 0 := by
    intro i; fin_cases i <;> simp [pickandsCenter, pickandsTimes]
  have hu : ∀ i, HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 3) => D (4 / -v i))
      (((4 / -pickandsCenter i) ^ (γ - 1) * (4 / pickandsCenter i ^ 2)) •
        EuclideanSpace.proj (𝕜 := ℝ) i) pickandsCenter := fun i =>
    (hasDerivAt_extRVLimit_four_div γ (hc i)).comp_hasFDerivAt
      (f := (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin 3) → ℝ))
      pickandsCenter (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have hN : D (4 / -pickandsCenter 0) - D (4 / -pickandsCenter 1) = 2 ^ γ * D 2 := by
    rw [hv0, hv1]; norm_num; exact extRVLimit_four γ
  have hN' : D (4 / -pickandsCenter 1) - D (4 / -pickandsCenter 2) = D 2 := by
    rw [hv1, hv2]; norm_num [hD, extRVLimit_one]
  have h2γ : (0 : ℝ) < 2 ^ γ := by positivity
  have hF := ((hu 0).sub (hu 1)).log (by simp only [Pi.sub_apply]; rw [hN]; positivity) |>.sub
    (((hu 1).sub (hu 2)).log (by simp only [Pi.sub_apply]; rw [hN']; positivity))
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hF.congr_fderiv ?_
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_three,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    RCLike.inner_apply, conj_trivial, pickandsGrad, Pi.sub_apply]
  rw [hN, hN', hv0, hv1, hv2]
  simp only [EuclideanSpace.proj, PiLp.proj_apply]
  have e4 : (4 : ℝ) ^ (γ - 1) = 2 ^ γ * 2 ^ γ / 4 := by
    rw [rpow_sub_one (by norm_num), show (4 : ℝ) = 2 * 2 by norm_num,
      mul_rpow (by norm_num) (by norm_num)]
  have e2 : (2 : ℝ) ^ (γ - 1) = 2 ^ γ / 2 := rpow_sub_one (by norm_num) _
  simp only [hD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num
  rw [e4, e2]
  field_simp
  ring

/-- The asymptotic variance `aᵀ S a` of the Pickands map, `S = (min (τ_i, τ_j))`. -/
theorem pickandsGrad_quadForm (γ : ℝ) :
    (pickandsGrad γ) ⬝ᵥ (brownianCovMatrix fun i => (pickandsTimes i : ℝ≥0)) *ᵥ
      (pickandsGrad γ) = (2 * (2 ^ γ) ^ 2 + 1) / (4 * extRVLimit γ 2 ^ 2) := by
  have hd : 0 < extRVLimit γ 2 := extRVLimit_pos one_lt_two
  simp only [dotProduct, Matrix.mulVec, brownianCovMatrix, Fin.sum_univ_three, pickandsGrad,
    pickandsTimes, Matrix.of_apply, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num
  field_simp
  ring

end PickandsMap

end ExtremeValueTheory
