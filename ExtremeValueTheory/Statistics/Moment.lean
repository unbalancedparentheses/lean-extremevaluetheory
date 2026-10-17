/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Pickands
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Log-moments of the top order statistics and the moment estimator

For the descending order statistics `X_{(1)} ≥ ⋯ ≥ X_{(n)}` of a sample and `j ≥ 1`, the
`j`-th **log-moment** of the top `k + 1` order statistics is

  `M^{(j)}_{k,n} = (1/k) ∑_{i<k} (log X_{(i+1)} - log X_{(k+1)}) ^ j`,

so that `M^{(1)}` is the Hill estimator. The **moment estimator** of Dekkers, Einmahl and
de Haan is

  `γ̂_M = M^{(1)} + 1 - (1/2) (1 - (M^{(1)})² / M^{(2)})⁻¹`

(A. L. M. Dekkers, J. H. J. Einmahl and L. de Haan, *A moment estimator for the index of an
extreme-value distribution*, Ann. Statist. 17 (1989); de Haan and Ferreira, *Extreme Value
Theory: An Introduction*, Springer 2006, §3.5 [dHF]).

## Main results

* `ExtremeValueTheory.tendstoInMeasure_logMoment`: if the survival function of the iid `X_i`
  is regularly varying with index `-α`, `α > 0`, and `k → ∞`, `k / n → 0`, then
  `M^{(j)}_{k,n} → j! / α ^ j` in probability, for every `j ≥ 1`. For `j = 1` this is the weak
  consistency of the Hill estimator (`tendstoInMeasure_hill`).
* `ExtremeValueTheory.tendstoInMeasure_momentEstimator`: **weak consistency of the moment
  estimator in the heavy-tailed case** ([dHF, §3.5] restricted to `γ > 0`):
  `γ̂_M → 1 / α` in probability.
* `ExtremeValueTheory.tendstoInMeasure_momentEstimator_of_isInMDAGEV` and
  `ExtremeValueTheory.tendstoInMeasure_hill_of_isInMDAGEV`: the same in the language of domains
  of attraction, for `F ∈ MDA(H_ξ)`, `ξ > 0`.
* `ExtremeValueTheory.tendstoInMeasure_momentEstimator_pareto`: the exact Pareto case.

The consistency of the moment estimator for every `ξ ∈ ℝ` (with positive right endpoint), which
needs the extended regular variation of `log U`, is proved in
`ExtremeValueTheory.Statistics.MomentGeneral`
(`tendstoInMeasure_momentEstimator_of_isInMDAGEV'`).

## Proof

The argument is the tail empirical process argument used for the Hill estimator
(`ExtremeValueTheory.Statistics.Hill`), with the log-excess `log⁺ (X / s)` replaced by its
`j`-th power. The layer cake formula gives
`E log⁺ (X / s) ^ j = j ∫_0^∞ u ^ (j - 1) F̄(s e^u) du`, and by dominated convergence with the
Potter bounds `E log⁺ (X / s) ^ j / F̄(s) → j ∫_0^∞ u ^ (j - 1) e^{-α u} du = j! / α ^ j`.
The moment estimator is a continuous function of `(M^{(1)}, M^{(2)})` at `(1/α, 2/α²)`, where it
takes the value `1/α + 1 - (1/2) (1 - 1/2)⁻¹ = 1/α`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

/-! ### Definitions -/

section Deterministic

variable {n : ℕ}

/-- The `j`-th **log-moment** of the top `k + 1` order statistics of the sample `x`:
`M^{(j)}_{k,n} = (1/k) ∑_{i<k} (log X_{(i+1)} - log X_{(k+1)}) ^ j`. -/
noncomputable def logMoment (x : Fin n → ℝ) (k j : ℕ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i ∈ range k, (Real.log (orderStat x i) - Real.log (orderStat x k)) ^ j

/-- The first log-moment is the Hill estimator. -/
theorem logMoment_one (x : Fin n → ℝ) (k : ℕ) : logMoment x k 1 = hill x k := by
  simp [logMoment, hill]

/-- The **moment estimator** of Dekkers, Einmahl and de Haan:
`γ̂_M = M^{(1)} + 1 - (1/2) (1 - (M^{(1)})² / M^{(2)})⁻¹`. -/
noncomputable def momentEstimator (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  logMoment x k 1 + 1 - 1 / 2 * (1 - logMoment x k 1 ^ 2 / logMoment x k 2)⁻¹

/-- The log-moments as averages of powers of log-excesses over the random threshold
`X_{(k+1)} > 0`: `M^{(j)}_{k,n} = (1/k) ∑_i log⁺ (X_i / X_{(k+1)}) ^ j` for `j ≠ 0`. -/
theorem logMoment_eq_sum_logExcess (x : Fin n → ℝ) {k j : ℕ} (hj : j ≠ 0) (hk : k < n)
    (ht : 0 < orderStat x k) :
    logMoment x k j = (k : ℝ)⁻¹ * ∑ i, logExcess (orderStat x k) (x i) ^ j := by
  rw [logMoment, ← sum_orderStat x (fun y => logExcess (orderStat x k) y ^ j),
    ← Finset.sum_range_add_sum_Ico _ hk.le]
  congr 1
  rw [Finset.sum_eq_zero (s := Ico k n), add_zero]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [logExcess_of_ge ht (orderStat_anti x (mem_range.1 hi).le hk)]
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [logExcess_of_le ht (orderStat_anti x hi.1 hi.2), zero_pow hj]

end Deterministic

/-! ### Moments of the log-excess over a high threshold -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}

theorem integrableOn_rpow_mul_exp_neg {q b : ℝ} (hq : -1 < q) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ q * Real.exp (-b * u)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := q) (p := 1) hq one_pos hb
  simpa using this

/-- Bound on the `p`-th moment of the log-excess over a high threshold, from the Potter-type
bound `F̄(s e^u) ≤ 2 F̄(s) e^{-α u / 2}`. -/
theorem lintegral_logExcess_rpow_le (hY : Measurable Y) {α : ℝ} (hα : 0 < α) {s : ℝ}
    (hs : 0 < s)
    (hb : ∀ u : ℝ, 0 ≤ u →
      survival P Y (s * Real.exp u) ≤ 2 * survival P Y s * Real.exp (-(α / 2) * u))
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (logExcess s (Y ω) ^ p) ∂P ≤
      ENNReal.ofReal (2 * p * (∫ u in Ioi 0, u ^ (p - 1) * Real.exp (-(α / 2) * u)) *
        survival P Y s) := by
  have hp0 : 0 < p := by linarith
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul P
    (Eventually.of_forall fun ω => logExcess_nonneg hs (Y ω))
    ((measurable_logExcess s).comp hY).aemeasurable hp0
  rw [h]
  have hI := integrableOn_rpow_mul_exp_neg (q := p - 1) (by linarith) (half_pos hα)
  have hFs := survival_nonneg (P := P) (Y := Y) s
  calc ENNReal.ofReal p * ∫⁻ t in Ioi 0, P {a | t < logExcess s (Y a)} *
        ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0,
          ENNReal.ofReal (2 * survival P Y s * (t ^ (p - 1) * Real.exp (-(α / 2) * t))) := by
        gcongr 1
        refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
        rw [Set.mem_Ioi] at ht
        rw [setOf_lt_logExcess hs ht, ← ENNReal.ofReal_toReal (measure_ne_top P _),
          ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        have := hb t ht.le
        have ht' : 0 ≤ t ^ (p - 1) := rpow_nonneg ht.le _
        change survival P Y (s * Real.exp t) * t ^ (p - 1) ≤ _
        nlinarith
    _ = ENNReal.ofReal p * ENNReal.ofReal (2 * survival P Y s *
          ∫ u in Ioi 0, u ^ (p - 1) * Real.exp (-(α / 2) * u)) := by
        rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hI.const_mul _)]
        refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
        have : 0 < t := ht
        positivity
    _ = _ := by
        rw [← ENNReal.ofReal_mul hp0.le]
        congr 1; ring

/-- The layer cake formula for the `p`-th moment of the log-excess:
`E log⁺ (Y / s) ^ p = p ∫_0^∞ u ^ (p - 1) F̄(s e^u) du`. -/
theorem integral_logExcess_rpow (hY : Measurable Y) {s : ℝ} (hs : 0 < s) {p : ℝ} (hp : 0 < p)
    (hint : IntegrableOn (fun t => t ^ (p - 1) * survival P Y (s * Real.exp t)) (Ioi 0)) :
    ∫ ω, logExcess s (Y ω) ^ p ∂P =
      p * ∫ t in Ioi 0, t ^ (p - 1) * survival P Y (s * Real.exp t) := by
  have hm : AEStronglyMeasurable (fun ω => logExcess s (Y ω) ^ p) P :=
    (((measurable_logExcess s).comp hY).pow_const p).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun ω => rpow_nonneg (logExcess_nonneg hs _) _) hm,
    lintegral_rpow_eq_lintegral_meas_lt_mul P
      (Eventually.of_forall fun ω => logExcess_nonneg hs (Y ω))
      ((measurable_logExcess s).comp hY).aemeasurable hp]
  have hI : ∫⁻ t in Ioi 0, P {a | t < logExcess s (Y a)} * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (∫ t in Ioi 0, t ^ (p - 1) * survival P Y (s * Real.exp t)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : 0 < t := ht
      rw [setOf_lt_logExcess hs ht', ENNReal.ofReal_mul (rpow_nonneg ht'.le _), mul_comm]
      congr 1
      exact (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht' : 0 < t := ht
      exact mul_nonneg (rpow_nonneg ht'.le _) (survival_nonneg _)
  rw [hI, ← ENNReal.ofReal_mul hp.le, ENNReal.toReal_ofReal]
  refine mul_nonneg hp.le (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  have ht' : 0 < t := ht
  exact mul_nonneg (rpow_nonneg ht'.le _) (survival_nonneg _)

/-- The `p`-th moment of the log-excess over a high threshold `s`, divided by `F̄(s)`, tends to
`Γ(p + 1) / α ^ p` as `s → ∞`, for a survival function regularly varying with index `-α`. -/
theorem tendsto_integral_logExcess_rpow_div (hY : Measurable Y) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (survival P Y) (-α)) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun s => (∫ ω, logExcess s (Y ω) ^ p ∂P) / survival P Y s) atTop
      (𝓝 (Real.Gamma (p + 1) / α ^ p)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨x₀, hx₀, hb⟩ := exists_survival_exp_le hα hRV
  have hFpos := survival_pos hRV
  have hI2 := integrableOn_rpow_mul_exp_neg (q := p - 1) (by linarith) (half_pos hα)
  have hmeas : ∀ s, 0 ≤ s →
      Measurable fun t : ℝ => t ^ (p - 1) * survival P Y (s * Real.exp t) := by
    intro s hs
    refine (measurable_id.pow_const _).mul (Antitone.measurable ?_)
    exact (survival_anti Y).comp_monotone fun u v huv =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 huv) hs
  have hint : ∀ s ≥ x₀,
      IntegrableOn (fun t => t ^ (p - 1) * survival P Y (s * Real.exp t)) (Ioi 0) := by
    intro s hs
    refine Integrable.mono' (hI2.const_mul (2 * survival P Y s))
      (hmeas s (hx₀.le.trans hs)).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht' : 0 < t := ht
    have htp : 0 ≤ t ^ (p - 1) := rpow_nonneg ht'.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htp (survival_nonneg _))]
    have := hb s hs t ht'.le
    nlinarith
  have hlimval : Real.Gamma (p + 1) / α ^ p =
      p * ∫ t in Ioi 0, t ^ (p - 1) * Real.exp (-α * t) := by
    have := integral_rpow_mul_exp_neg_mul_Ioi hp0 hα
    simp_rw [neg_mul]
    rw [this, Real.Gamma_add_one hp0.ne', Real.div_rpow zero_le_one hα.le, Real.one_rpow]
    ring
  rw [hlimval]
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (l := atTop) (F := fun s t => t ^ (p - 1) * survival P Y (s * Real.exp t) / survival P Y s)
    (f := fun t => t ^ (p - 1) * Real.exp (-α * t))
    (fun t => 2 * (t ^ (p - 1) * Real.exp (-(α / 2) * t))) ?_ ?_ ?_ ?_
  · refine (key.const_mul p).congr' ?_
    filter_upwards [eventually_ge_atTop x₀] with s hs
    rw [integral_logExcess_rpow hY (hx₀.trans_le hs) hp0 (hint s hs), integral_div, mul_div_assoc]
  · filter_upwards [eventually_gt_atTop 0] with s hs
    exact ((hmeas s hs.le).div_const _).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop x₀] with s hs
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht' : 0 < t := ht
    have htp : 0 ≤ t ^ (p - 1) := rpow_nonneg ht'.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg htp (survival_nonneg _))
      (survival_nonneg _)), div_le_iff₀ (hFpos s)]
    have := hb s hs t ht'.le
    nlinarith
  · exact hI2.const_mul 2
  · refine Eventually.of_forall fun t => ?_
    have h := hRV.tendsto (Real.exp_pos t)
    rw [← Real.exp_mul, show t * -α = -α * t by ring] at h
    refine (h.const_mul (t ^ (p - 1))).congr fun s => ?_
    rw [mul_comm (Real.exp t) s, mul_div_assoc]

/-- For thresholds `s ≥ x₀`, the `j`-th power of the log-excess is square integrable, with
`E[log⁺(Y/s) ^ (2j)] ≤ C F̄(s)`. -/
theorem exists_memLp_logExcess_pow (hY : Measurable Y) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (survival P Y) (-α)) {j : ℕ} (hj : j ≠ 0) :
    ∃ x₀ C : ℝ, 0 < x₀ ∧ ∀ s ≥ x₀, MemLp (fun ω => logExcess s (Y ω) ^ j) 2 P ∧
      ∫ ω, (logExcess s (Y ω) ^ j) ^ 2 ∂P ≤ C * survival P Y s := by
  obtain ⟨x₀, hx₀, hb⟩ := exists_survival_exp_le hα hRV
  set q : ℝ := ((2 * j : ℕ) : ℝ) with hq
  have hq1 : 1 ≤ q := by
    rw [hq]
    have : 1 ≤ 2 * j := by omega
    exact_mod_cast this
  refine ⟨x₀, 2 * q * ∫ u in Ioi 0, u ^ (q - 1) * Real.exp (-(α / 2) * u), hx₀, fun s hs => ?_⟩
  have hs0 : 0 < s := hx₀.trans_le hs
  have heq : ∀ ω, (logExcess s (Y ω) ^ j) ^ 2 = logExcess s (Y ω) ^ q := by
    intro ω
    rw [hq, rpow_natCast, ← pow_mul, mul_comm]
  have hm : AEStronglyMeasurable (fun ω => logExcess s (Y ω) ^ j) P :=
    (((measurable_logExcess s).comp hY).pow_const j).aestronglyMeasurable
  have hL := lintegral_logExcess_rpow_le hY hα hs0 (hb s hs) hq1
  simp_rw [← heq] at hL
  refine ⟨(memLp_two_iff_integrable_sq hm).2 ⟨hm.pow 2, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    exact hL.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
      (hm.pow 2)]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hL).trans ?_
    rw [ENNReal.toReal_ofReal]
    have : 0 ≤ ∫ u in Ioi 0, u ^ (q - 1) * Real.exp (-(α / 2) * u) :=
      setIntegral_nonneg measurableSet_Ioi fun u hu => by
        have : 0 < u := hu
        positivity
    have := survival_nonneg (P := P) (Y := Y) s
    have : 0 < q := by linarith
    positivity

end Tail

/-! ### Deterministic thresholds -/

section Threshold

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}

/-- For a regularly varying survival function and an intermediate sequence `k`, there are
deterministic thresholds `t_n → ∞` with `n F̄(c t_n) / k_n → c ^ (-α)` for every `c > 0`. -/
theorem exists_threshold_of_isRegularlyVarying (hY : Measurable Y) {α : ℝ}
    (hRV : IsRegularlyVarying (survival P Y) (-α)) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧ ∀ c : ℝ, 0 < c →
      Tendsto (fun n => n * survival P Y (c * t n) / k n) atTop (𝓝 (c ^ (-α))) := by
  set F := survival P Y with hF_def
  have hFanti : Antitone F := survival_anti Y
  have hFpos : ∀ x, 0 < F x := survival_pos hRV
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have hppos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < k n / n := by
    filter_upwards [hkpos, hnpos] with n h1 h2; positivity
  set t : ℕ → ℝ := fun n => sInf {x | F x ≤ (k n : ℝ) / n} with ht_def
  have hspec : ∀ M, ∀ᶠ n in atTop, F (t n) ≤ (k n : ℝ) / n ∧
      (∀ x < t n, (k n : ℝ) / n < F x) ∧ M ≤ t n := by
    intro M
    filter_upwards [hppos, hkn.eventually (gt_mem_nhds (hFpos M))] with n h1 h2
    exact threshold_spec hFanti (continuousWithinAt_survival hY) (tendsto_survival_atTop hY)
      h1 h2
  have htinf : Tendsto t atTop atTop :=
    tendsto_atTop.2 fun M => (hspec M).mono fun n h => h.2.2
  have hr : Tendsto (fun n => n * F (t n) / k n) atTop (𝓝 1) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have hcont : Tendsto (fun c : ℝ => c ^ (-α)) (𝓝 1) (𝓝 1) := by
        have := Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)
        simpa using this.tendsto
      obtain ⟨c, hca, hc1⟩ := (((hcont.eventually (lt_mem_nhds ha)).filter_mono
        nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
      have hc0 : (0 : ℝ) < c := zero_lt_one.trans hc1
      have hlim := (hRV.tendsto hc0).comp (htinf.atTop_div_const hc0)
      filter_upwards [hlim.eventually (lt_mem_nhds hca), hspec 1, hkpos, hnpos] with n h1 h2 h3 h4
      simp only [Function.comp_apply, mul_div_cancel₀ _ hc0.ne'] at h1
      have htn : 0 < t n := one_pos.trans_le h2.2.2
      have hlt : (k n : ℝ) / n < F (t n / c) := h2.2.1 _ (div_lt_self htn hc1)
      refine h1.trans_le ?_
      rw [div_le_div_iff₀ (hFpos _) h3]
      rw [div_lt_iff₀ h4] at hlt
      nlinarith [hFpos (t n)]
    · filter_upwards [hspec 0, hkpos, hnpos] with n h1 h2 h3
      refine lt_of_le_of_lt ?_ ha
      rw [div_le_one h2]
      have := h1.1
      rw [le_div_iff₀ h3] at this
      linarith
  refine ⟨t, htinf, fun c hc => ?_⟩
  have h := ((hRV.tendsto hc).comp htinf).mul hr
  rw [mul_one] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  field_simp [(hFpos (t n)).ne']

end Threshold

/-! ### Convergence in probability and continuous maps -/

section ContinuousMapping

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Continuous mapping theorem** for convergence in probability to constants, in two
variables: if `f_n → a` and `g_n → b` in probability and `φ` is continuous at `(a, b)`, then
`φ (f_n, g_n) → φ (a, b)` in probability. -/
theorem tendstoInMeasure_comp₂ {ι : Type*} {l : Filter ι} {f g : ι → Ω → ℝ} {a b : ℝ}
    (hf : TendstoInMeasure P f l (fun _ => a)) (hg : TendstoInMeasure P g l (fun _ => b))
    {φ : ℝ × ℝ → ℝ} (hφ : ContinuousAt φ (a, b)) :
    TendstoInMeasure P (fun i ω => φ (f i ω, g i ω)) l (fun _ => φ (a, b)) := by
  rw [tendstoInMeasure_iff_dist] at hf hg ⊢
  intro ε hε
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hφ ε hε
  have h := (hf η hη).add (hg η hη)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun i => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
  have hd : dist (f i ω, g i ω) (a, b) < η := by
    rw [Prod.dist_eq]
    exact max_lt hcon.1 hcon.2
  exact absurd hω (not_le.2 (hball hd))

end ContinuousMapping

/-! ### Weak consistency -/

section Consistency

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Weak consistency of the log-moments** ([dHF, §3.5], in the case
`γ > 0`). Let `X_0, X_1, …` be iid with survival function `F̄ x = P(X_0 > x)` regularly varying
with index `-α`, `α > 0`, and let `k(n) → ∞`, `k(n) / n → 0`. Then for every `j ≥ 1`,
`M^{(j)}_{k(n),n} → j! / α ^ j` in probability. -/
theorem tendstoInMeasure_logMoment {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    {j : ℕ} (hj : j ≠ 0) :
    TendstoInMeasure P (fun n ω => logMoment (fun i : Fin n => X i ω) (k n) j) atTop
      (fun _ => (j.factorial : ℝ) / α ^ j) := by
  set F := survival P (X 0) with hF_def
  change IsRegularlyVarying F (-α) at hRV
  have hFpos : ∀ x, 0 < F x := survival_pos hRV
  obtain ⟨t, htinf, hcount⟩ := exists_threshold_of_isRegularlyVarying (hX 0) hRV hk hkn
  set L : ℝ := (j.factorial : ℝ) / α ^ j with hL_def
  have hL : 0 < L := by positivity
  have hmean : Tendsto (fun s => (∫ ω, logExcess s (X 0 ω) ^ j ∂P) / F s) atTop (𝓝 L) := by
    have h := tendsto_integral_logExcess_rpow_div (hX 0) hα hRV (p := (j : ℝ))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj)
    rw [Real.Gamma_nat_eq_factorial, rpow_natCast] at h
    simpa only [rpow_natCast] using h
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkinv : Tendsto (fun n => ((k n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  -- the two weak laws of large numbers
  have hWcount : ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |(exceedCount (fun i : Fin n => X i ω) (c * t n) : ℝ) / k n - c ^ (-α)|}) atTop (𝓝 0) :=
    fun c hc δ hδ => tendsto_measure_abs_exceedCount_div_sub hX hindep hident hk (hcount c hc) hδ
  obtain ⟨x₀, C, hx₀, hL2⟩ := exists_memLp_logExcess_pow (hX 0) hα hRV hj
  have hWlog : ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |(∑ i ∈ range n, logExcess (c * t n) (X i ω) ^ j) / k n - L * c ^ (-α)|})
      atTop (𝓝 0) := by
    intro c hc δ hδ
    have hct : Tendsto (fun n => c * t n) atTop atTop := htinf.const_mul_atTop hc
    have hev : ∀ᶠ n in atTop, x₀ ≤ c * t n := hct.eventually_ge_atTop x₀
    refine tendsto_measure_abs_sum_div_sub hindep hident
      (g := fun n y => logExcess (c * t n) y ^ j)
      (fun n => (measurable_logExcess _).pow_const _) hkpos
      (hev.mono fun n hn => (hL2 _ hn).1) ?_ ?_ hδ
    · have h := (hmean.comp hct).mul (hcount c hc)
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, ← hF_def]
      field_simp [(hFpos (c * t n)).ne']
    · have hb := ((hcount c hc).mul hkinv).const_mul C
      rw [mul_zero, mul_zero] at hb
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
      · refine Eventually.of_forall fun n => ?_
        have : 0 ≤ ∫ ω, (logExcess (c * t n) (X 0 ω) ^ j) ^ 2 ∂P :=
          integral_nonneg fun ω => sq_nonneg _
        positivity
      · filter_upwards [hev, hkpos] with n hn hkn'
        have h := (hL2 _ hn).2
        rw [div_le_iff₀ (by positivity)]
        calc (n : ℝ) * ∫ ω, (logExcess (c * t n) (X 0 ω) ^ j) ^ 2 ∂P
            ≤ n * (C * F (c * t n)) := by gcongr
          _ = C * (n * F (c * t n) / k n * (k n : ℝ)⁻¹) * (k n : ℝ) ^ 2 := by
            field_simp
  -- choice of the constants `c₁ < 1 < c₂`
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hcont : Tendsto (fun c : ℝ => c ^ (-α)) (𝓝 1) (𝓝 1) := by
    have := Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)
    simpa using this.tendsto
  have hθ : 0 < ε / (2 * L) := by positivity
  obtain ⟨c₂, hc₂a, hc₂1⟩ := (((hcont.eventually (lt_mem_nhds (show 1 - ε / (2 * L) < 1 by
    linarith))).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
  have e₁ : ∀ᶠ c in 𝓝[<] (1 : ℝ), c ^ (-α) < 1 + ε / (2 * L) :=
    (hcont.eventually (gt_mem_nhds (show 1 < 1 + ε / (2 * L) by linarith))).filter_mono
      nhdsWithin_le_nhds
  have e₁' : ∀ᶠ c in 𝓝[<] (1 : ℝ), c ∈ Iio (1 : ℝ) := self_mem_nhdsWithin
  have e₁'' : ∀ᶠ c in 𝓝[<] (1 : ℝ), c ∈ Ioi (0 : ℝ) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))
  obtain ⟨c₁, hc₁a, hc₁1, hc₁0⟩ := (e₁.and (e₁'.and e₁'')).exists
  simp only [Set.mem_Ioi, Set.mem_Iio] at hc₂1 hc₁1 hc₁0
  have hc₂0 : 0 < c₂ := zero_lt_one.trans hc₂1
  have hδ₂ : 0 < 1 - c₂ ^ (-α) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg hc₂1 (neg_lt_zero.2 hα); linarith
  have hδ₁ : 0 < c₁ ^ (-α) - 1 := by
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hc₁0 hc₁1 (neg_lt_zero.2 hα); linarith
  have hm₂ : L - ε / 2 < L * c₂ ^ (-α) := by
    have : L * (1 - ε / (2 * L)) < L * c₂ ^ (-α) := mul_lt_mul_of_pos_left hc₂a hL
    have e : L * (1 - ε / (2 * L)) = L - ε / 2 := by field_simp
    linarith
  have hm₁ : L * c₁ ^ (-α) < L + ε / 2 := by
    have : L * c₁ ^ (-α) < L * (1 + ε / (2 * L)) := mul_lt_mul_of_pos_left hc₁a hL
    have e : L * (1 + ε / (2 * L)) = L + ε / 2 := by field_simp
    linarith
  have hlim := (((hWcount c₂ hc₂0 _ hδ₂).add (hWcount c₁ hc₁0 _ hδ₁)).add
    (hWlog c₂ hc₂0 _ (half_pos hε))).add (hWlog c₁ hc₁0 _ (half_pos hε))
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  have hkn' : ∀ᶠ n : ℕ in atTop, k n < n := by
    filter_upwards [hkn.eventually (gt_mem_nhds one_pos), hnpos] with n h1 h2
    rw [div_lt_one h2] at h1
    exact_mod_cast h1
  have htpos : ∀ᶠ n in atTop, 0 < t n := htinf.eventually_gt_atTop 0
  filter_upwards [hkn', hkpos, htpos] with n hkn hkpos' htn
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add_left
    ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)) _))
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_le] at hcon
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
  set x : Fin n → ℝ := fun i => X i ω with hx
  have hS : ∀ a, ∑ i, logExcess a (x i) ^ j = ∑ i ∈ range n, logExcess a (X i ω) ^ j :=
    fun a => Fin.sum_univ_eq_sum_range (fun i => logExcess a (X i ω) ^ j) n
  -- localisation of the random threshold `X_{(k+1)}`
  have hT2 : orderStat x (k n) ≤ c₂ * t n := by
    rw [orderStat_le_iff x hkn]
    have := (abs_lt.1 h1).2
    have h' : (exceedCount x (c₂ * t n) : ℝ) / k n < 1 := by linarith
    rw [div_lt_one hkpos'] at h'
    exact_mod_cast h'.le
  have hT1 : c₁ * t n < orderStat x (k n) := by
    rw [lt_orderStat_iff x hkn]
    have := (abs_lt.1 h2).1
    have h' : 1 < (exceedCount x (c₁ * t n) : ℝ) / k n := by linarith
    rw [one_lt_div hkpos'] at h'
    exact_mod_cast h'
  have hc₁t : 0 < c₁ * t n := mul_pos hc₁0 htn
  have hT0 : 0 < orderStat x (k n) := hc₁t.trans hT1
  rw [logMoment_eq_sum_logExcess x hj hkn hT0, ← div_eq_inv_mul] at hω
  have hlo : (∑ i ∈ range n, logExcess (c₂ * t n) (X i ω) ^ j) / k n ≤
      (∑ i, logExcess (orderStat x (k n)) (x i) ^ j) / k n := by
    rw [hS]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (logExcess_nonneg (hT0.trans_le hT2) _)
        (logExcess_anti hT0 hT2 _) j) hkpos'.le
  have hhi : (∑ i, logExcess (orderStat x (k n)) (x i) ^ j) / k n ≤
      (∑ i ∈ range n, logExcess (c₁ * t n) (X i ω) ^ j) / k n := by
    rw [hS]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (logExcess_nonneg hT0 _) (logExcess_anti hc₁t hT1.le _) j) hkpos'.le
  have e3 := (abs_lt.1 h3).1
  have e4 := (abs_lt.1 h4).2
  have : |(∑ i, logExcess (orderStat x (k n)) (x i) ^ j) / k n - L| < ε := by
    rw [abs_lt]; constructor <;> linarith
  linarith

/-- **Weak consistency of the moment estimator, heavy-tailed case** (Dekkers, Einmahl and
de Haan 1989; [dHF, §3.5] for `γ > 0`). Let `X_0, X_1, …` be iid with survival
function regularly varying with index `-α`, `α > 0`, and let `k(n) → ∞`, `k(n) / n → 0`. Then
the moment estimator converges in probability to `γ = 1 / α`. -/
theorem tendstoInMeasure_momentEstimator {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => momentEstimator (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  have h1 := tendstoInMeasure_logMoment hX hindep hident hα hRV hk hkn one_ne_zero
  have h2 := tendstoInMeasure_logMoment hX hindep hident hα hRV hk hkn two_ne_zero
  set a : ℝ := ((Nat.factorial 1 : ℕ) : ℝ) / α ^ 1 with ha
  set b : ℝ := ((Nat.factorial 2 : ℕ) : ℝ) / α ^ 2 with hb
  have ha' : a = 1 / α := by rw [ha]; simp
  have hb' : b = 2 / α ^ 2 := by rw [hb]; simp [Nat.factorial]
  set φ : ℝ × ℝ → ℝ := fun p => p.1 + 1 - 1 / 2 * (1 - p.1 ^ 2 / p.2)⁻¹ with hφ_def
  have hb0 : b ≠ 0 := by rw [hb']; positivity
  have hhalf : 1 - a ^ 2 / b = 1 / 2 := by
    rw [ha', hb']
    field_simp
    ring
  have hcont : ContinuousAt φ (a, b) := by
    refine (continuousAt_fst.add continuousAt_const).sub (continuousAt_const.mul
      ((continuousAt_const.sub ((continuousAt_fst.pow 2).div continuousAt_snd hb0)).inv₀ ?_))
    change 1 - a ^ 2 / b ≠ 0
    rw [hhalf]
    norm_num
  have hval : φ (a, b) = 1 / α := by
    simp only [hφ_def]
    rw [hhalf, ha']
    norm_num
  have := tendstoInMeasure_comp₂ h1 h2 hcont
  rw [hval] at this
  exact this

/-- **Weak consistency of the moment estimator, exact Pareto case.** If the `X_i` are iid
`Pareto(α)`, `P(X_0 > x) = x ^ (-α)` for `x ≥ 1`, and `k(n) → ∞`, `k(n) / n → 0`, then the
moment estimator converges in probability to `1 / α`. -/
theorem tendstoInMeasure_momentEstimator_pareto {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => momentEstimator (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) :=
  tendstoInMeasure_momentEstimator hX hindep hident hα ((IsRegularlyVarying.rpow_id (-α)).congr
    ((eventually_ge_atTop 1).mono fun x hx => (hPar x hx).symm)) hk hkn

/-- In the Fréchet domain of attraction, the tail of the c.d.f. of `X_0` is regularly varying,
in the form used by the Hill and moment estimators. -/
theorem isRegularlyVarying_tail_of_isInMDAGEV {X : Ω → ℝ} (hX : Measurable X)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | X ω ≤ x}).toReal)
    {ξ : ℝ} (hξ : 0 < ξ) (hMDA : F.IsInMDAGEV ξ) :
    IsRegularlyVarying (fun x => (P {ω | x < X ω}).toReal) (-(1 / ξ)) := by
  have hFr : F.IsInMDAFrechet (one_div_pos.2 hξ) := by
    simpa [CumulativeDistributionFunction.IsInMDAGEV, hξ] using hMDA
  have h := (F.isInMDAFrechet_iff (one_div_pos.2 hξ)).1 hFr
  refine h.congr (Eventually.of_forall fun a => ?_)
  have hc : {ω | a < X ω} = {ω | X ω ≤ a}ᶜ := by ext ω; simp
  simp only
  rw [hc, prob_compl_eq_one_sub (measurableSet_le hX measurable_const),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, hF]

/-- **Weak consistency of the Hill estimator in domain of attraction form**: if the c.d.f. of the
iid `X_i` is in `MDA(H_ξ)` with `ξ > 0`, and `k(n) → ∞`, `k(n) / n → 0`, then the Hill
estimator converges in probability to `ξ`. -/
theorem tendstoInMeasure_hill_of_isInMDAGEV {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | X 0 ω ≤ x}).toReal)
    {ξ : ℝ} (hξ : 0 < ξ) (hMDA : F.IsInMDAGEV ξ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop (fun _ => ξ) := by
  have h := tendstoInMeasure_hill hX hindep hident (one_div_pos.2 hξ)
    (isRegularlyVarying_tail_of_isInMDAGEV (hX 0) hF hξ hMDA) hk hkn
  rwa [one_div_one_div] at h

/-- **Weak consistency of the moment estimator in domain of attraction form**, Fréchet case: if
the c.d.f. of the iid `X_i` is in `MDA(H_ξ)` with `ξ > 0`, and `k(n) → ∞`, `k(n) / n → 0`, then
the moment estimator converges in probability to `ξ`. -/
theorem tendstoInMeasure_momentEstimator_of_isInMDAGEV {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | X 0 ω ≤ x}).toReal)
    {ξ : ℝ} (hξ : 0 < ξ) (hMDA : F.IsInMDAGEV ξ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => momentEstimator (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => ξ) := by
  have h := tendstoInMeasure_momentEstimator hX hindep hident (one_div_pos.2 hξ)
    (isRegularlyVarying_tail_of_isInMDAGEV (hX 0) hF hξ hMDA) hk hkn
  rwa [one_div_one_div] at h

end Consistency

end ExtremeValueTheory
