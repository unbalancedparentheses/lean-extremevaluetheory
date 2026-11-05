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
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => hi i
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

/-- **Second-order extended regular variation** ([dHF, Definition 2.3.1]): `a > 0` and
`A ≠ 0` eventually, `A(t) → 0`, and

  `((U(xt) - U(t)) / a(t) - D_γ(x)) / A(t) → H_{γ,ρ}(x)`

locally uniformly in `x ∈ (0, ∞)`.

[dHF, Definition 2.3.1] asks for pointwise convergence for each `x > 0` and for `A` of eventually
constant sign; the convergence is then locally uniform on `(0, ∞)` (see [dHF, §2.3 and
Appendix B.3]), and `|A|` is regularly varying with index
`ρ ≤ 0` ([dHF, Theorem 2.3.3]). Here the locally uniform convergence is part of the hypothesis
(that implication is not formalized), while the sign condition and the conclusions of
[dHF, Theorem 2.3.3] are not needed and not assumed. -/
structure IsExtSecondOrderRegularlyVarying (U : ℝ → ℝ) (γ ρ : ℝ) (a A : ℝ → ℝ) : Prop where
  eventually_pos : ∀ᶠ t in atTop, 0 < a t
  tendsto_zero : Tendsto A atTop (𝓝 0)
  eventually_ne_zero : ∀ᶠ t in atTop, A t ≠ 0
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

/-! ### The second-order remainder of the Pickands statistic -/

section Remainder

/-- `|log (1 + z) - z| ≤ 2 z²` for `|z| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) - z| ≤ 2 * z ^ 2 := by
  rw [abs_le] at hz
  have h1 : 0 < 1 + z := by linarith
  have hu := Real.log_le_sub_one_of_pos h1
  have hl := Real.one_sub_inv_le_log_of_pos h1
  have e : 1 - (1 + z)⁻¹ = z - z ^ 2 / (1 + z) := by field_simp; ring
  have hq : z ^ 2 / (1 + z) ≤ 2 * z ^ 2 := by
    rw [div_le_iff₀ h1]; nlinarith [sq_nonneg z]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z]

/-- `log (1 + A u) / A → u₀` as `A → 0` with `A ≠ 0`, and `u → u₀`. -/
theorem tendsto_log_one_add_mul_div {α : Type*} {l : Filter α} {A u : α → ℝ} {u₀ : ℝ}
    (hA : Tendsto A l (𝓝 0)) (hA0 : ∀ᶠ p in l, A p ≠ 0) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun p => Real.log (1 + A p * u p) / A p) l (𝓝 u₀) := by
  have hAu : Tendsto (fun p => |A p * u p|) l (𝓝 0) := by
    have := (hA.mul hu).abs
    simpa using this
  have hr : Tendsto (fun p => 2 * |A p| * u p ^ 2) l (𝓝 0) := by
    have := (hA.abs.const_mul 2).mul (hu.pow 2)
    simpa using this
  have hd : Tendsto (fun p => Real.log (1 + A p * u p) / A p - u p) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hr
    filter_upwards [hA0, hAu.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with p hp hsmall
    have hpos : 0 < |A p| := abs_pos.2 hp
    have e : Real.log (1 + A p * u p) / A p - u p =
        (Real.log (1 + A p * u p) - A p * u p) / A p := by field_simp
    rw [Real.norm_eq_abs, e, abs_div, div_le_iff₀ hpos]
    calc |Real.log (1 + A p * u p) - A p * u p| ≤ 2 * (A p * u p) ^ 2 :=
          abs_log_one_add_sub_le hsmall
      _ = 2 * |A p| * u p ^ 2 * |A p| := by rw [mul_pow, ← sq_abs (A p)]; ring
  simpa using hd.add hu

/-- Locally uniform convergence along a reparametrized filter, evaluated at a moving point. -/
theorem tendsto_comp_of_tendstoLocallyUniformlyOn {β : Type*} {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    {s : Set ℝ} (h : TendstoLocallyUniformlyOn F f atTop s) {l : Filter β} {φ g : β → ℝ}
    (hφ : Tendsto φ l atTop) {x : ℝ} (hx : x ∈ s) (hf : ContinuousWithinAt f s x)
    (hg : Tendsto g l (𝓝[s] x)) : Tendsto (fun b => F (φ b) (g b)) l (𝓝 (f x)) := by
  have h' : TendstoLocallyUniformlyOn (fun b => F (φ b)) f l s := fun u hu y hy => by
    obtain ⟨t, ht, hev⟩ := h u hu y hy
    exact ⟨t, ht, hφ.eventually hev⟩
  exact h'.tendsto_comp hf hx hg

theorem strictMonoOn_extRVLimit (γ : ℝ) : StrictMonoOn (extRVLimit γ) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (hasDerivAt_extRVLimit γ hx).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_extRVLimit γ hx).deriv]
  exact rpow_pos_of_pos hx _

/-- The log-ratio of spacings of `U` at the points `x_i t`, `x_i = 1/(-y_i)`:
`log ((U(x₀t) - U(x₁t)) / (U(x₁t) - U(x₂t)))`. With `t = n/k` and `y_i = -(n/k)(1 - U_{(τ_i k+1)})`
this is `log 2 ×` the Pickands estimator of the sample `U(1/(1 - U_i))`. -/
noncomputable def pickandsLog (U : ℝ → ℝ) (t : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.log ((U ((-y 0)⁻¹ * t) - U ((-y 1)⁻¹ * t)) / (U ((-y 1)⁻¹ * t) - U ((-y 2)⁻¹ * t)))

/-- The asymptotic bias factor of the Pickands estimator ([dHF, Theorem 3.3.5]):
`b = (log 2)⁻¹ ((H(1) - H(1/2)) / (D(1) - D(1/2)) - (H(1/2) - H(1/4)) / (D(1/2) - D(1/4)))`,
with `D = D_γ` and `H = H_{γ,ρ}`. -/
noncomputable def pickandsBias (γ ρ : ℝ) : ℝ :=
  ((extSecondOrderLimit γ ρ 1 - extSecondOrderLimit γ ρ (1 / 2)) /
      (extRVLimit γ 1 - extRVLimit γ (1 / 2)) -
    (extSecondOrderLimit γ ρ (1 / 2) - extSecondOrderLimit γ ρ (1 / 4)) /
      (extRVLimit γ (1 / 2) - extRVLimit γ (1 / 4))) / Real.log 2

/-- **The second-order remainder of the Pickands statistic.** Under second-order extended regular
variation, `(pickandsLog U t y - pickandsMap γ y) / A(t) → b log 2` as `t → ∞` and `y` tends to
the centering point `(-1, -2, -4)`. -/
theorem tendsto_pickandsLog_sub_div {U : ℝ → ℝ} {γ ρ : ℝ} {a A : ℝ → ℝ}
    (h2 : IsExtSecondOrderRegularlyVarying U γ ρ a A) :
    Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (pickandsLog U p.1 p.2 - pickandsMap γ p.2) / A p.1)
      (atTop ×ˢ 𝓝 pickandsCenter) (𝓝 (pickandsBias γ ρ * Real.log 2)) := by
  set l : Filter (ℝ × EuclideanSpace ℝ (Fin 3)) := atTop ×ˢ 𝓝 pickandsCenter with hl
  set D := extRVLimit γ with hD
  set H := extSecondOrderLimit γ ρ with hH
  set F : ℝ → ℝ → ℝ := fun t x => ((U (x * t) - U t) / a t - D x) / A t with hF
  have hfst : Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => p.1) l atTop := tendsto_fst
  have hsnd : Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => p.2) l (𝓝 pickandsCenter) :=
    tendsto_snd
  have hτ : ∀ i, (0 : ℝ) < pickandsTimes i := by intro i; fin_cases i <;> simp [pickandsTimes]
  have hxlim : ∀ i, Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => (-p.2 i)⁻¹) l
      (𝓝 ((pickandsTimes i : ℝ)⁻¹)) := by
    intro i
    have hc : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y i := by fun_prop
    have h1 := (hc.tendsto _).comp hsnd
    have := h1.neg.inv₀ (by simp [pickandsCenter, (hτ i).ne'])
    simpa [pickandsCenter] using this
  have hxpos : ∀ i, ∀ᶠ p in l, 0 < (-p.2 i)⁻¹ := fun i =>
    (hxlim i).eventually (lt_mem_nhds (inv_pos.2 (hτ i)))
  have hFl : ∀ i, Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => F p.1 (-p.2 i)⁻¹) l
      (𝓝 (H (pickandsTimes i : ℝ)⁻¹)) := fun i =>
    tendsto_comp_of_tendstoLocallyUniformlyOn h2.tendstoLocallyUniformlyOn hfst
      (inv_pos.2 (hτ i))
      (continuousAt_extSecondOrderLimit γ ρ (inv_pos.2 (hτ i))).continuousWithinAt
      (tendsto_nhdsWithin_iff.2 ⟨hxlim i, hxpos i⟩)
  have hDl : ∀ i, Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => D (-p.2 i)⁻¹) l
      (𝓝 (D (pickandsTimes i : ℝ)⁻¹)) := fun i =>
    (hasDerivAt_extRVLimit γ (inv_pos.2 (hτ i))).continuousAt.tendsto.comp (hxlim i)
  have hmono := strictMonoOn_extRVLimit γ
  have hd01 : 0 < D (pickandsTimes 0 : ℝ)⁻¹ - D (pickandsTimes 1 : ℝ)⁻¹ := by
    have := hmono (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 by norm_num)
      (by norm_num)
    simp only [pickandsTimes]; norm_num; linarith
  have hd12 : 0 < D (pickandsTimes 1 : ℝ)⁻¹ - D (pickandsTimes 2 : ℝ)⁻¹ := by
    have := hmono (show (0 : ℝ) < 1 / 4 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
      (by norm_num)
    simp only [pickandsTimes]; norm_num; linarith
  set u : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
    (F p.1 (-p.2 0)⁻¹ - F p.1 (-p.2 1)⁻¹) / (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) with hu
  set u' : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
    (F p.1 (-p.2 1)⁻¹ - F p.1 (-p.2 2)⁻¹) / (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) with hu'
  have hul : Tendsto u l (𝓝 ((H (pickandsTimes 0 : ℝ)⁻¹ - H (pickandsTimes 1 : ℝ)⁻¹) /
      (D (pickandsTimes 0 : ℝ)⁻¹ - D (pickandsTimes 1 : ℝ)⁻¹))) :=
    ((hFl 0).sub (hFl 1)).div ((hDl 0).sub (hDl 1)) hd01.ne'
  have hul' : Tendsto u' l (𝓝 ((H (pickandsTimes 1 : ℝ)⁻¹ - H (pickandsTimes 2 : ℝ)⁻¹) /
      (D (pickandsTimes 1 : ℝ)⁻¹ - D (pickandsTimes 2 : ℝ)⁻¹))) :=
    ((hFl 1).sub (hFl 2)).div ((hDl 1).sub (hDl 2)) hd12.ne'
  have hA : Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => A p.1) l (𝓝 0) :=
    h2.tendsto_zero.comp hfst
  have hA0 := hfst.eventually h2.eventually_ne_zero
  have ha0 := hfst.eventually h2.eventually_pos
  have hlim := (tendsto_log_one_add_mul_div hA hA0 hul).sub
    (tendsto_log_one_add_mul_div hA hA0 hul')
  have hp01 := ((hDl 0).sub (hDl 1)).eventually (lt_mem_nhds hd01)
  have hp12 := ((hDl 1).sub (hDl 2)).eventually (lt_mem_nhds hd12)
  have h1u : ∀ᶠ p in l, 0 < 1 + A p.1 * u p := by
    have : Tendsto (fun p => 1 + A p.1 * u p) l (𝓝 (1 + 0 * _)) :=
      tendsto_const_nhds.add (hA.mul hul)
    rw [zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds one_pos)
  have h1u' : ∀ᶠ p in l, 0 < 1 + A p.1 * u' p := by
    have : Tendsto (fun p => 1 + A p.1 * u' p) l (𝓝 (1 + 0 * _)) :=
      tendsto_const_nhds.add (hA.mul hul')
    rw [zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds one_pos)
  have hval : (H (pickandsTimes 0 : ℝ)⁻¹ - H (pickandsTimes 1 : ℝ)⁻¹) /
        (D (pickandsTimes 0 : ℝ)⁻¹ - D (pickandsTimes 1 : ℝ)⁻¹) -
      (H (pickandsTimes 1 : ℝ)⁻¹ - H (pickandsTimes 2 : ℝ)⁻¹) /
        (D (pickandsTimes 1 : ℝ)⁻¹ - D (pickandsTimes 2 : ℝ)⁻¹) =
      pickandsBias γ ρ * Real.log 2 := by
    have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    simp only [pickandsBias, pickandsTimes, hD, hH]
    norm_num
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [hA0, ha0, hp01, hp12, h1u, h1u', hxpos 0, hxpos 1, hxpos 2]
    with p hA0 ha0 hp01 hp12 h1u h1u' hx0 hx1 hx2
  have hUi : ∀ i, U ((-p.2 i)⁻¹ * p.1) =
      U p.1 + a p.1 * (D (-p.2 i)⁻¹ + A p.1 * F p.1 (-p.2 i)⁻¹) := by
    intro i
    simp only [hF]
    field_simp
    ring
  have eN : U ((-p.2 0)⁻¹ * p.1) - U ((-p.2 1)⁻¹ * p.1) =
      a p.1 * (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) * (1 + A p.1 * u p) := by
    rw [hUi 0, hUi 1]
    simp only [hu]
    have hne := hp01.ne'
    generalize D (-p.2 0)⁻¹ = d0 at hne ⊢
    generalize D (-p.2 1)⁻¹ = d1 at hne ⊢
    rw [sub_ne_zero] at hne
    field_simp
    ring
  have eN' : U ((-p.2 1)⁻¹ * p.1) - U ((-p.2 2)⁻¹ * p.1) =
      a p.1 * (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) * (1 + A p.1 * u' p) := by
    rw [hUi 1, hUi 2]
    simp only [hu']
    have hne := hp12.ne'
    generalize D (-p.2 1)⁻¹ = d0 at hne ⊢
    generalize D (-p.2 2)⁻¹ = d1 at hne ⊢
    rw [sub_ne_zero] at hne
    field_simp
    ring
  have e4 : ∀ i, 0 < (-p.2 i)⁻¹ →
      D (4 / -p.2 i) = D 4 + 4 ^ γ * D (-p.2 i)⁻¹ := by
    intro i hi
    rw [div_eq_mul_inv]
    exact extRVLimit_mul (by norm_num) hi
  have h4 : (0 : ℝ) < 4 ^ γ := by positivity
  have hM : pickandsMap γ p.2 = Real.log (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) -
      Real.log (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) := by
    simp only [pickandsMap]
    rw [← hD, e4 0 hx0, e4 1 hx1, e4 2 hx2]
    rw [show D 4 + 4 ^ γ * D (-p.2 0)⁻¹ - (D 4 + 4 ^ γ * D (-p.2 1)⁻¹) =
      4 ^ γ * (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) by ring,
      show D 4 + 4 ^ γ * D (-p.2 1)⁻¹ - (D 4 + 4 ^ γ * D (-p.2 2)⁻¹) =
      4 ^ γ * (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) by ring,
      Real.log_mul h4.ne' hp01.ne', Real.log_mul h4.ne' hp12.ne']
    ring
  have hL : pickandsLog U p.1 p.2 = Real.log (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) +
      Real.log (1 + A p.1 * u p) - (Real.log (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) +
      Real.log (1 + A p.1 * u' p)) := by
    simp only [pickandsLog]
    rw [eN, eN', Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) h1u.ne', Real.log_mul (by positivity) h1u'.ne',
      Real.log_mul ha0.ne' hp01.ne', Real.log_mul ha0.ne' hp12.ne']
    ring
  rw [hL, hM]
  field_simp
  ring

end Remainder

/-! ### Convergence in probability through a joint limit -/

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If `G(s, y) → g₀` as `s → l_s` and `y → c`, `t_n → l_s` deterministically and `Y_n → c` in
probability, then `G(t_n, Y_n) → g₀` in probability. -/
theorem TendstoInMeasure.comp_prod_of_tendsto {E β : Type*} [PseudoMetricSpace E]
    {lt : Filter β} {G : β × E → ℝ} {c : E} {g₀ : ℝ} (hG : Tendsto G (lt ×ˢ 𝓝 c) (𝓝 g₀))
    {t : ℕ → β} (ht : Tendsto t atTop lt) {Y : ℕ → Ω → E}
    (hY : TendstoInMeasure P Y atTop (fun _ => c)) :
    TendstoInMeasure P (fun n ω => G (t n, Y n ω)) atTop (fun _ => g₀) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  obtain ⟨S, hS, B, hB, hSB⟩ := mem_prod_iff.1 (hG (Metric.ball_mem_nhds g₀ hε))
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.1 hB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hY δ hδ)
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [ht hS] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have hmem := hSB (show (t n, Y n ω) ∈ S ×ˢ B from ⟨hn, hδB (Metric.mem_ball.2 hcon)⟩)
  simp only [mem_preimage, Metric.mem_ball] at hmem
  linarith

end Prob

/-! ### Asymptotic normality of the Pickands estimator -/

section Normality

theorem measurable_extRVLimit (γ : ℝ) : Measurable (extRVLimit γ) := by
  by_cases hγ : γ = 0
  · rw [show extRVLimit γ = Real.log from funext fun x => by simp [extRVLimit, hγ]]
    exact measurable_log
  · rw [show extRVLimit γ = fun x => (x ^ γ - 1) / γ from funext (extRVLimit_of_ne hγ)]
    fun_prop

theorem measurable_pickandsMap (γ : ℝ) : Measurable (pickandsMap γ) := by
  have := measurable_extRVLimit γ
  unfold pickandsMap
  fun_prop

theorem measurable_pickandsLog {U : ℝ → ℝ} (hU : Measurable U) (t : ℝ) :
    Measurable (pickandsLog U t) := by
  unfold pickandsLog
  fun_prop

theorem measurable_pickands_pi (n k : ℕ) : Measurable fun y : Fin n → ℝ => pickands y k :=
  ((((measurable_orderStat_pi k).sub (measurable_orderStat_pi (2 * k))).div
    ((measurable_orderStat_pi (2 * k)).sub (measurable_orderStat_pi (4 * k)))).log).div_const _

/-- The asymptotic variance of the Pickands estimator,
`(2 · 2^{2γ} + 1) / (4 D_γ(2)² (log 2)²)`; see `pickandsVariance_of_ne` and
`pickandsVariance_zero` for the closed forms of [dHF, Theorem 3.3.5]. -/
noncomputable def pickandsVariance (γ : ℝ) : ℝ :=
  (2 * (2 ^ γ) ^ 2 + 1) / (4 * extRVLimit γ 2 ^ 2 * Real.log 2 ^ 2)

/-- For `γ ≠ 0` the asymptotic variance of the Pickands estimator is
`γ² (2^{2γ+1} + 1) / (2 (2^γ - 1) log 2)²` ([dHF, Theorem 3.3.5]). -/
theorem pickandsVariance_of_ne {γ : ℝ} (hγ : γ ≠ 0) :
    pickandsVariance γ = γ ^ 2 * (2 ^ (2 * γ + 1) + 1) / (2 * (2 ^ γ - 1) * Real.log 2) ^ 2 := by
  have hd := extRVLimit_pos (γ := γ) one_lt_two
  rw [extRVLimit_of_ne hγ] at hd
  have h1 : (2 : ℝ) ^ γ - 1 ≠ 0 := by
    intro h; rw [h, zero_div] at hd; exact lt_irrefl _ hd
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [pickandsVariance, extRVLimit_of_ne hγ, rpow_add two_pos, rpow_one,
    show 2 * γ = γ + γ by ring, rpow_add two_pos]
  field_simp
  ring

/-- For `γ = 0` the asymptotic variance of the Pickands estimator is `3 / (4 (log 2)⁴)`
([dHF, Theorem 3.3.5]). -/
theorem pickandsVariance_zero : pickandsVariance 0 = 3 / (4 * Real.log 2 ^ 4) := by
  rw [pickandsVariance, extRVLimit_zero_left]
  norm_num
  ring

theorem pickandsVariance_nonneg (γ : ℝ) : 0 ≤ pickandsVariance γ := by
  unfold pickandsVariance; positivity

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [IsProbabilityMeasure P] in
/-- A uniform random variable lies in the open interval `(0, 1)` almost surely. -/
theorem ae_mem_Ioo_of_map_eq_uniform {V : Ω → ℝ} (hV : Measurable V)
    (hlaw : P.map V = volume.restrict (Set.Icc 0 1)) : P {ω | V ω ∉ Ioo (0 : ℝ) 1} = 0 := by
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := compl_mem_ae_iff.2 (measure_singleton 1)
  have h : ∀ᵐ x ∂(P.map V), x ∈ Ioo (0 : ℝ) 1 := by
    rw [hlaw]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h0,
      ae_restrict_of_ae h1] with x hx hx0 hx1
    exact ⟨lt_of_le_of_ne hx.1 hx0.symm, lt_of_le_of_ne hx.2 hx1⟩
  exact ae_of_ae_map hV.aemeasurable h

/-- **Asymptotic normality of the Pickands estimator, uniform representation.** Let the `V_i`
be iid uniform on `[0, 1]`, let `U` be measurable and
nondecreasing on `(1, ∞)` and of second-order extended regular variation with indices `γ`, `ρ`
and auxiliary functions `a`, `A`. If `k → ∞`, `k/n → 0` and `√k A(n/k) → λ`, then the Pickands
estimator `γ̂_P` of the sample `U(1/(1 - V_i))` satisfies
`√k (γ̂_P - γ) ⇒ N(λ b_{γ,ρ}, σ²_γ)` (`pickandsBias`, `pickandsVariance`). -/
theorem tendstoInDistribution_pickands_uniform {V : ℕ → Ω → ℝ} (hV : ∀ i, Measurable (V i))
    (hind : iIndepFun V P) (hlaw : ∀ i, P.map (V i) = volume.restrict (Set.Icc 0 1))
    {U : ℝ → ℝ} (hUm : MonotoneOn U (Ioi 1))
    (hUmeas : Measurable U) {γ ρ lam : ℝ} {a A : ℝ → ℝ}
    (h2 : IsExtSecondOrderRegularlyVarying U γ ρ a A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal (lam * pickandsBias γ ρ) (pickandsVariance γ).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) *
        (pickands (fun i : Fin n => U (1 / (1 - V i ω))) (k n) - γ)) atTop Z (fun _ => P) P' := by
  set S := brownianCovMatrix fun i => (pickandsTimes i : ℝ≥0) with hS
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
    WithLp.toLp 2 (fun i => -tailTime V n (k n) (pickandsTimes i * k n) ω) with hY
  have hτ : ∀ i, 0 < pickandsTimes i := by intro i; fin_cases i <;> simp [pickandsTimes]
  have hT := tendstoInDistribution_sqrt_smul_tailTime hV hind hlaw hk hkn pickandsTimes hτ
  have hsk : Tendsto (fun n => √(k n : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hk)
  have hYm : ∀ n, Measurable (Y n) := fun n => (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.2 fun i => (measurable_tailTime hV n (k n) _).neg)
  set v0 : ℝ := pickandsGrad γ ⬝ᵥ S *ᵥ pickandsGrad γ with hv0
  have hDM := hT.delta_method_gaussian (θh := Y) (θ := pickandsCenter)
    (posSemidef_brownianCovMatrix _) HasLaw.id hsk (hasGradientAt_pickandsMap γ)
    (fun n => ((measurable_pickandsMap γ).comp (hYm n)).aemeasurable)
    (HasLaw.id (μ := gaussianReal 0 v0.toNNReal))
  have hY0 := hT.tendstoInMeasure_of_smul hsk
  have hYc : TendstoInMeasure P Y atTop (fun _ => pickandsCenter) := by
    rw [tendstoInMeasure_iff_dist] at hY0 ⊢
    intro ε hε
    simpa [dist_eq_norm, hY, pickandsCenter] using hY0 ε hε
  have ht : Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  have hG := TendstoInMeasure.comp_prod_of_tendsto (tendsto_pickandsLog_sub_div h2) ht hYc
  have hB := TendstoInMeasure.mul' (tendstoInMeasure_const_of_tendsto (P := P) hlam) hG rfl
  have hBm : ∀ n, AEMeasurable (fun ω => √(k n : ℝ) * A (n / k n) *
      ((pickandsLog U (n / k n) (Y n ω) - pickandsMap γ (Y n ω)) / A (n / k n))) P := fun n =>
    (measurable_const.mul ((((measurable_pickandsLog hUmeas _).comp (hYm n)).sub
      ((measurable_pickandsMap γ).comp (hYm n))).div_const _)).aemeasurable
  have hC := hDM.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun q : ℝ × ℝ => (Real.log 2)⁻¹ * (q.1 + q.2)) (by fun_prop) hB hBm
  refine (tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ ?_).congr_limit
    hZ.aemeasurable ?_
  · have h4 : ∀ᶠ n in atTop, 4 * k n < n := by
      have := hkn.const_mul (4 : ℝ)
      rw [mul_zero] at this
      filter_upwards [this.eventually (gt_mem_nhds one_pos),
        (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0] with n h1 h2
      rw [← mul_div_assoc, div_lt_one h2] at h1
      exact_mod_cast h1
    have hg : MonotoneOn (fun v : ℝ => U (1 / (1 - v))) (Ioo 0 1) := by
      intro v hv w hw hvw
      have hv1 : 0 < 1 - v := sub_pos.2 hv.2
      have hw1 : 0 < 1 - w := sub_pos.2 hw.2
      refine hUm ?_ ?_ (one_div_le_one_div_of_le hw1 (by linarith))
      · simp only [mem_Ioi]; rw [lt_one_div one_pos hv1]; linarith [hv.1]
      · simp only [mem_Ioi]; rw [lt_one_div one_pos hw1]; linarith [hw.1]
    have hzero : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
      tendstoInMeasure_const_of_tendsto tendsto_const_nhds
    refine hzero.congr_of_measure_ne ?_
    have hnull : ∀ n : ℕ, P {ω | ∃ i : Fin n, V i ω ∉ Ioo (0 : ℝ) 1} = 0 := fun n => by
      have : {ω | ∃ i : Fin n, V i ω ∉ Ioo (0 : ℝ) 1} = ⋃ i : Fin n, {ω | V i ω ∉ Ioo (0 : ℝ) 1} := by
        ext; simp
      rw [this]
      exact measure_iUnion_null fun i => ae_mem_Ioo_of_map_eq_uniform (hV i) (hlaw i)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hk.eventually_gt_atTop 0, h4, ht.eventually h2.eventually_ne_zero,
      eventually_gt_atTop 0] with n hk0 hn4 hA0 hn0
    refine (measure_mono_null (fun ω hω => ?_) (hnull n)).symm
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra hcon
    push Not at hcon
    apply hω
    have hV01 : ∀ i : Fin n, V i ω ∈ Ioo (0 : ℝ) 1 := hcon
    have hk0' : (0 : ℝ) < k n := by exact_mod_cast hk0
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hkk : (k n : ℝ) / n * (n / k n) = 1 := by field_simp
    have hos : ∀ j < n, orderStat (fun i : Fin n => U (1 / (1 - V i ω))) j =
        U ((tailTime V n (k n) j ω)⁻¹ * (n / k n)) := by
      intro j hj
      rw [show (fun i : Fin n => U (1 / (1 - V i ω))) =
        (fun v : ℝ => U (1 / (1 - v))) ∘ (fun i : Fin n => V i ω) from rfl,
        orderStat_comp_monotoneOn hg hV01 hj, tailTime, inv_div,
        div_mul_eq_mul_div, hkk]
    have key : pickands (fun i : Fin n => U (1 / (1 - V i ω))) (k n) =
        pickandsLog U (n / k n) (Y n ω) / Real.log 2 := by
      rw [pickands, hos (k n) (by omega), hos (2 * k n) (by omega), hos (4 * k n) (by omega)]
      simp [pickandsLog, hY, pickandsTimes]
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    simp only [Pi.sub_apply]
    rw [key, pickandsMap_center]
    field_simp
    ring
  · intro n
    exact (measurable_const.mul (((measurable_pickands_pi n (k n)).comp (measurable_pi_iff.2
      fun i => hUmeas.comp (measurable_const.div (measurable_const.sub (hV i))))).sub_const
        _)).aemeasurable
  · rw [hZ.map_eq]
    have hv0nn : 0 ≤ v0 := by rw [hv0, hS, pickandsGrad_quadForm]; positivity
    rw [show (fun ω : ℝ => (Real.log 2)⁻¹ * ((id ω, lam * (pickandsBias γ ρ * Real.log 2)).1 +
        (id ω, lam * (pickandsBias γ ρ * Real.log 2)).2)) = (fun x => (Real.log 2)⁻¹ * x) ∘
        (fun x => x + lam * (pickandsBias γ ρ * Real.log 2)) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_add_const,
      gaussianReal_map_const_mul]
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    congr 1
    · field_simp; ring
    · apply NNReal.eq
      rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hv0nn,
        Real.coe_toNNReal _ (pickandsVariance_nonneg γ), hv0, hS, pickandsGrad_quadForm,
        pickandsVariance]
      field_simp

/-- The image of the standard exponential law under `x ↦ 1 - e^{-x}` is the uniform law. -/
theorem map_one_sub_exp_neg_expMeasure :
    (expMeasure 1).map (fun x => 1 - exp (-x)) = volume.restrict (Set.Icc 0 1) := by
  have hm : Measurable fun x : ℝ => 1 - exp (-x) := by fun_prop
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Icc 0 1)) := ⟨by simp⟩
  refine Measure.ext_of_Iic _ _ fun s => ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge s 0 with hs | hs
  · have e : Iic s ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, _⟩; linarith
    rw [e, measure_empty]
    refine measure_mono_null (t := Iic 0) (fun x hx => ?_) ?_
    · simp only [mem_preimage, mem_Iic] at hx ⊢
      by_contra hx0
      have : exp (-x) < 1 := by
        rw [← exp_zero]; exact exp_lt_exp.2 (by linarith [not_le.1 hx0])
      linarith
    · have h0 := expMeasure_Iic (le_refl (0 : ℝ))
      simpa using h0
  rcases lt_or_ge s 1 with hs1 | hs1
  · have h1s : 0 < 1 - s := by linarith
    have e1 : (fun x : ℝ => 1 - exp (-x)) ⁻¹' Iic s = Iic (-log (1 - s)) := by
      ext x
      simp only [mem_preimage, mem_Iic]
      rw [show (1 - exp (-x) ≤ s) ↔ 1 - s ≤ exp (-x) by constructor <;> intro h <;> linarith,
        ← log_le_iff_le_exp h1s]
      constructor <;> intro h <;> linarith
    have e2 : Iic s ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 s := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    have hl : 0 ≤ -log (1 - s) := by
      have := log_nonpos h1s.le (by linarith)
      linarith
    rw [e1, e2, expMeasure_Iic hl, neg_neg, exp_log h1s, Real.volume_Icc]
    congr 1
    ring
  · have e1 : (fun x : ℝ => 1 - exp (-x)) ⁻¹' Iic s = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      linarith [exp_pos (-x)]
    have e2 : Iic s ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by linarith [h.2], h⟩
    rw [e1, e2, measure_univ, Real.volume_Icc]
    norm_num

/-- **Asymptotic normality of the Pickands estimator on the exponential scale**: the statement of
`tendstoInDistribution_pickands_uniform` for the samples `U(e^{E_i})`, `E_i` iid standard
exponential. -/
theorem tendstoInDistribution_pickands_comp_exp {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {U : ℝ → ℝ}
    (hUm : MonotoneOn U (Ioi 1)) (hUmeas : Measurable U) {γ ρ lam : ℝ} {a A : ℝ → ℝ}
    (h2 : IsExtSecondOrderRegularlyVarying U γ ρ a A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal (lam * pickandsBias γ ρ) (pickandsVariance γ).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) *
        (pickands (fun i : Fin n => U (exp (E i ω))) (k n) - γ)) atTop Z (fun _ => P) P' := by
  have hm : Measurable fun x : ℝ => 1 - exp (-x) := by fun_prop
  have hlaw : ∀ i, P.map (fun ω => 1 - exp (-E i ω)) = volume.restrict (Set.Icc 0 1) := fun i => by
    rw [← map_one_sub_exp_neg_expMeasure, ← (hE i).map_eq, Measure.map_map hm (hEm i)]
    rfl
  have h := tendstoInDistribution_pickands_uniform (V := fun i ω => 1 - exp (-E i ω))
    (fun i => hm.comp (hEm i)) (hind.comp (fun _ x => 1 - exp (-x)) fun _ => hm) hlaw hUm hUmeas
    h2 hk hkn hlam hZ
  have e : ∀ x : ℝ, 1 / (1 - (1 - exp (-x))) = exp x := fun x => by
    rw [sub_sub_cancel, exp_neg, one_div, inv_inv]
  simpa only [e] using h

/-- **Asymptotic normality of the Pickands estimator** (Pickands 1975; Dekkers and de Haan 1989,
Theorem 2.3; [dHF, Theorem 3.3.5]). Let `X_0, X_1, …` be iid real random variables whose tail
quantile function `U(t) = F^←(1 - 1/t)` satisfies the second-order condition
`IsExtSecondOrderRegularlyVarying U γ ρ a A` for some `γ ∈ ℝ`, `ρ`. If `k = k(n) → ∞`, `k / n → 0`
and `√k A(n / k) → λ`, then the estimator
`γ̂_P = (log 2)⁻¹ log ((X_{(k+1)} - X_{(2k+1)}) / (X_{(2k+1)} - X_{(4k+1)}))` satisfies

  `√k (γ̂_P - γ) ⇒ N(λ b_{γ,ρ}, σ²_γ)`,

with `b_{γ,ρ} = pickandsBias γ ρ` (`pickandsBias_of_ne`, `pickandsBias_zero_right`) and
`σ²_γ = pickandsVariance γ`, which is `γ² (2^{2γ+1} + 1) / (2 (2^γ - 1) log 2)²` for `γ ≠ 0` and
`3 / (4 (log 2)⁴)` for `γ = 0` (`pickandsVariance_of_ne`, `pickandsVariance_zero`).

Two points of comparison with the source:

* The second-order condition is assumed with locally uniform convergence in `x`; [dHF] states it
  pointwise and deduces uniformity. See `IsExtSecondOrderRegularlyVarying`. That deduction is not
  formalized, so this hypothesis is formally stronger than the textbook's.
* `k` is the **smallest** of the three indices, and it is both the index in `√k` and the point
  `n / k` at which `A` is evaluated, as in Dekkers and de Haan. See the module docstring for the
  translation if the largest index is called `k`. -/
theorem tendstoInDistribution_pickands {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ}
    {a A : ℝ → ℝ}
    (h2 : IsExtSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ a A)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal (lam * pickandsBias γ ρ) (pickandsVariance γ).toNNReal) P') :
    TendstoInDistribution (fun n ω =>
        √(k n : ℝ) * (pickands (fun i : Fin n => X i ω) (k n) - γ))
      atTop Z (fun _ => P) P' := by
  obtain ⟨Ω₀, _, P₀, E, hEm, hE, hind, hP₀⟩ := exists_iid ℕ (expMeasure 1)
  have hUm := measurable_survivalQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  have hUmono := monotoneOn_survivalQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  have hB := tendstoInDistribution_pickands_comp_exp hEm hE hind hUmono hUm h2 hk hkn hlam hZ
  refine hB.of_map_eq (fun n => ?_) (Eventually.of_forall fun n => ?_)
  · exact (measurable_const.mul (((measurable_pickands_pi n (k n)).comp
      (measurable_pi_iff.2 fun i => hX i)).sub_const _)).aemeasurable
  exact map_statistic_eq_map_statistic_comp_exp hX hindep hident hE hind n
    (measurable_const.mul ((measurable_pickands_pi n (k n)).sub_const _))

/-- **Asymptotic normality of the Pickands estimator without bias**: if `√k A(n / k) → 0`, then
`√k (γ̂_P - γ) ⇒ N(0, σ²_γ)`. -/
theorem tendstoInDistribution_pickands_of_tendsto_zero {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ : ℝ} {a A : ℝ → ℝ}
    (h2 : IsExtSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ a A)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hA : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 0)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (pickandsVariance γ).toNNReal) P') :
    TendstoInDistribution (fun n ω =>
        √(k n : ℝ) * (pickands (fun i : Fin n => X i ω) (k n) - γ))
      atTop Z (fun _ => P) P' :=
  tendstoInDistribution_pickands hX hindep hident h2 hk hkn hA (by rwa [zero_mul])

/-- `H_{γ,ρ} = (D_{γ+ρ} - D_γ) / ρ` on `(0, ∞)` for `ρ ≠ 0`. -/
theorem extSecondOrderLimit_of_ne {γ ρ : ℝ} (hρ : ρ ≠ 0) {x : ℝ} (hx : 0 < x) :
    extSecondOrderLimit γ ρ x = (extRVLimit (γ + ρ) x - extRVLimit γ x) / ρ := by
  have hsub : Set.uIcc (1 : ℝ) x ⊆ Ioi 0 := fun s hs => by
    rcases Set.mem_uIcc.1 hs with h | h <;> simp only [mem_Ioi] <;> linarith [h.1]
  have hd : ∀ s ∈ Set.uIcc (1 : ℝ) x, HasDerivAt (fun s => (extRVLimit (γ + ρ) s -
      extRVLimit γ s) / ρ) (s ^ (γ - 1) * boxCox ρ s) s := fun s hs => by
    have hs0 : 0 < s := hsub hs
    refine (((hasDerivAt_extRVLimit (γ + ρ) hs0).sub (hasDerivAt_extRVLimit γ hs0)).div_const
      ρ).congr_deriv ?_
    have hb : boxCox ρ s = (s ^ ρ - 1) / ρ := by simp [boxCox, hρ]
    rw [hb, show γ + ρ - 1 = (γ - 1) + ρ by ring, rpow_add hs0]
    ring
  have hii : IntervalIntegrable (fun s : ℝ => s ^ (γ - 1) * boxCox ρ s) volume 1 x :=
    ((continuousOn_rpow_mul_boxCox γ ρ).mono hsub).intervalIntegrable
  rw [extSecondOrderLimit, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii, extRVLimit_one,
    extRVLimit_one]
  ring

/-- Spacing of `D_γ` at `1, 1/2`. -/
theorem extRVLimit_one_sub_half (γ : ℝ) :
    extRVLimit γ 1 - extRVLimit γ (1 / 2) = (2 : ℝ) ^ (-γ) * extRVLimit γ 2 := by
  have h := extRVLimit_mul (γ := γ) (x := 1 / 2) (y := 2) (by norm_num) two_pos
  rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num] at h
  rw [h, rpow_neg two_pos.le, one_div, inv_rpow two_pos.le]
  ring

/-- Spacing of `D_γ` at `1/2, 1/4`. -/
theorem extRVLimit_half_sub_quarter (γ : ℝ) :
    extRVLimit γ (1 / 2) - extRVLimit γ (1 / 4) = ((2 : ℝ) ^ (-γ)) ^ 2 * extRVLimit γ 2 := by
  have h := extRVLimit_mul (γ := γ) (x := 1 / 4) (y := 2) (by norm_num) two_pos
  rw [show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num] at h
  have e : ((1 : ℝ) / 4) ^ γ = ((2 : ℝ) ^ (-γ)) ^ 2 := by
    rw [show (1 : ℝ) / 4 = 2⁻¹ * 2⁻¹ by norm_num, mul_rpow (by norm_num) (by norm_num),
      inv_rpow two_pos.le, rpow_neg two_pos.le]
    ring
  rw [h, e]
  ring

/-- **Closed form of the Pickands bias**, `ρ ≠ 0`:
`b_{γ,ρ} = D_{γ+ρ}(2) / D_γ(2) · 2^{-ρ} (1 - 2^{-ρ}) / (ρ log 2)`. -/
theorem pickandsBias_of_ne (γ : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    pickandsBias γ ρ = extRVLimit (γ + ρ) 2 / extRVLimit γ 2 *
      ((2 : ℝ) ^ (-ρ) * (1 - (2 : ℝ) ^ (-ρ))) / (ρ * Real.log 2) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hD : extRVLimit γ 2 ≠ 0 := (extRVLimit_pos one_lt_two).ne'
  have hp : (2 : ℝ) ^ (-γ) ≠ 0 := (rpow_pos_of_pos two_pos _).ne'
  have e : (2 : ℝ) ^ (-(γ + ρ)) = 2 ^ (-γ) * 2 ^ (-ρ) := by
    rw [neg_add, rpow_add two_pos]
  unfold pickandsBias
  rw [extSecondOrderLimit_of_ne hρ one_pos, extSecondOrderLimit_of_ne hρ (by norm_num),
    extSecondOrderLimit_of_ne hρ (by norm_num), extRVLimit_one_sub_half γ,
    extRVLimit_half_sub_quarter γ,
    show (extRVLimit (γ + ρ) 1 - extRVLimit γ 1) / ρ - (extRVLimit (γ + ρ) (1 / 2) -
      extRVLimit γ (1 / 2)) / ρ = ((extRVLimit (γ + ρ) 1 - extRVLimit (γ + ρ) (1 / 2)) -
      (extRVLimit γ 1 - extRVLimit γ (1 / 2))) / ρ by ring,
    show (extRVLimit (γ + ρ) (1 / 2) - extRVLimit γ (1 / 2)) / ρ - (extRVLimit (γ + ρ) (1 / 4) -
      extRVLimit γ (1 / 4)) / ρ = ((extRVLimit (γ + ρ) (1 / 2) - extRVLimit (γ + ρ) (1 / 4)) -
      (extRVLimit γ (1 / 2) - extRVLimit γ (1 / 4))) / ρ by ring,
    extRVLimit_one_sub_half γ, extRVLimit_one_sub_half (γ + ρ), extRVLimit_half_sub_quarter γ,
    extRVLimit_half_sub_quarter (γ + ρ), e]
  field_simp
  ring

/-- `H_{γ,ρ}` is exact for the model `U = D_γ + c D_{γ+ρ}`, which is therefore of second-order
extended regular variation, with `a(t) = t^γ (1 + c t^ρ)` and `A(t) = ρ c t^ρ / (1 + c t^ρ)`. This
is the standard example with a nontrivial second-order term; it covers all `γ ∈ ℝ`, `ρ < 0`. -/
theorem isExtSecondOrderRegularlyVarying_add_extRVLimit {γ ρ c : ℝ} (hρ : ρ < 0) (hc : 0 < c)
    {U : ℝ → ℝ} (hU : ∀ t, 0 < t → U t = extRVLimit γ t + c * extRVLimit (γ + ρ) t) :
    IsExtSecondOrderRegularlyVarying U γ ρ (fun t => t ^ γ * (1 + c * t ^ ρ))
      (fun t => ρ * (c * t ^ ρ) / (1 + c * t ^ ρ)) := by
  have hto : Tendsto (fun t : ℝ => c * t ^ ρ) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -ρ) (by linarith)).const_mul c
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with t ht
    positivity
  · have : Tendsto (fun t : ℝ => ρ * (c * t ^ ρ) / (1 + c * t ^ ρ)) atTop
        (𝓝 (ρ * 0 / (1 + 0))) :=
      (hto.const_mul ρ).div (tendsto_const_nhds.add hto) (by norm_num)
    rwa [mul_zero, zero_div] at this
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have : 0 < c * t ^ ρ := by positivity
    exact (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hρ this) (by linarith)).ne
  · rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    refine ⟨Ioi 0, self_mem_nhdsWithin, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with t ht y hy
    have hy0 : 0 < y := hy
    have hw : 0 < c * t ^ ρ := by positivity
    have htγ : 0 < t ^ γ := by positivity
    have key : ((U (y * t) - U t) / (t ^ γ * (1 + c * t ^ ρ)) - extRVLimit γ y) /
        (ρ * (c * t ^ ρ) / (1 + c * t ^ ρ)) = extSecondOrderLimit γ ρ y := by
      rw [extSecondOrderLimit_of_ne hρ.ne hy0, hU _ (mul_pos hy0 ht), hU _ ht, mul_comm y t,
        extRVLimit_mul ht hy0, extRVLimit_mul ht hy0, rpow_add ht]
      have h1w : 1 + c * t ^ ρ ≠ 0 := by positivity
      have h2 : t ^ ρ ≠ 0 := by positivity
      field_simp
      ring
    rw [key, dist_self]
    exact hε

end Normality

end ExtremeValueTheory
