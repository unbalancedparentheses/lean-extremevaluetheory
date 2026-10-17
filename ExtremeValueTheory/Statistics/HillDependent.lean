/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Hill
import ExtremeValueTheory.ForMathlib.Probability.Process.Mixing
import Mathlib.Probability.Moments.Covariance

/-!
# Consistency of the Hill estimator for dependent sequences

The iid proof of `tendstoInMeasure_hill` used independence only through Chebyshev's inequality
applied to two functionals of the sample: the exceedance count `#{i < n | X_i > c u_n}` and the
log-excess sum `∑_{i<n} log⁺ (X_i / (c u_n))`. Here we show that **only the exceedance counts
matter**: the log-excess sum is sandwiched, deterministically, between Riemann sums of exceedance
counts over the geometric grid `c u_n ρ^j` (`sum_le_logExcess`, `logExcess_le_sum`), up to a
remainder whose *mean* (no dependence needed) is small. Hence Hill consistency follows from
consistency of the **tail empirical measure** `(1/k) ∑_{i<n} 1{X_i > x u_n} → x^{-α}`, which in
turn follows from `Var(∑_{i<n} 1{X_i > u_n}) = o(k_n²)` by Chebyshev (Resnick and Stărică,
*Consistency of Hill's estimator for dependent data*, J. Appl. Probab. 32 (1995); Rootzén,
Leadbetter and de Haan, *On the distribution of tail array sums for strongly mixing stationary
sequences*, Ann. Appl. Probab. 8 (1998); Kulik and Soulier, *Heavy-Tailed Time Series*, 2020,
Ch. 9).

## Main results

* `ExtremeValueTheory.tailCount`: the exceedance count `∑_{i<n} 1{X_i > u}`.
* `ExtremeValueTheory.tendsto_measure_abs_tailCount_div_sub`: Chebyshev for exceedance counts
  with identically distributed marginals and `Var / b_n² → 0`.
* `ExtremeValueTheory.tendstoInMeasure_hill_of_variance`: **Hill consistency under a variance
  condition on exceedance counts.** Hypotheses: identically distributed marginals, regularly
  varying marginal tail with index `-α`, `k → ∞`, `k/n → 0`, and
  `Var(∑_{i<n} 1{X_i > u_n}) / k_n² → 0` along every `u_n → ∞` with `n F̄(u_n)/k_n → c > 0`.
  No independence, stationarity or mixing assumption beyond that.
* `ExtremeValueTheory.variance_tailCount_le_of_isMDependent`: for an `m`-dependent sequence with
  identical marginals, `Var(∑_{i<n} 1{X_i > u}) ≤ (2m+1) n F̄(u)`.
* `ExtremeValueTheory.tendstoInMeasure_hill_of_isMDependent`: **Hill consistency for
  `m`-dependent sequences** with identical marginals (no stationarity needed).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

/-! ### Exceedance counts -/

section TailCount

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The exceedance count `∑_{i<n} 1{X_i > u}` of the first `n` observations over the level `u`
(as a real-valued random variable). -/
noncomputable def tailCount (X : ℕ → Ω → ℝ) (n : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, if u < X i ω then (1 : ℝ) else 0

theorem measurable_ite_lt {Y : Ω → ℝ} (hY : Measurable Y) (u : ℝ) :
    Measurable fun ω => if u < Y ω then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_lt measurable_const hY) measurable_const measurable_const

theorem memLp_ite_lt [IsFiniteMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) (u : ℝ)
    (p : ENNReal) : MemLp (fun ω => if u < Y ω then (1 : ℝ) else 0) p P :=
  MemLp.of_bound (measurable_ite_lt hY u).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by split_ifs <;> norm_num)

theorem integral_ite_lt' {Y : Ω → ℝ} (hY : Measurable Y) (u : ℝ) :
    ∫ ω, (if u < Y ω then (1 : ℝ) else 0) ∂P = survival P Y u := by
  have : (fun ω => if u < Y ω then (1 : ℝ) else 0) = {ω | u < Y ω}.indicator 1 := by
    ext ω; simp [Set.indicator]
  rw [this, integral_indicator_one (measurableSet_lt measurable_const hY), measureReal_def]
  rfl

variable {X : ℕ → Ω → ℝ}

theorem measurable_tailCount (hX : ∀ i, Measurable (X i)) (n : ℕ) (u : ℝ) :
    Measurable (tailCount X n u) :=
  Finset.measurable_fun_sum _ fun i _ => measurable_ite_lt (hX i) u

theorem memLp_tailCount [IsFiniteMeasure P] (hX : ∀ i, Measurable (X i)) (n : ℕ) (u : ℝ)
    (p : ENNReal) : MemLp (tailCount X n u) p P :=
  memLp_finsetSum _ fun i _ => memLp_ite_lt (hX i) u p

omit [MeasurableSpace Ω] in
theorem tailCount_nonneg (n : ℕ) (u : ℝ) (ω : Ω) : 0 ≤ tailCount X n u ω :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

/-- With identically distributed marginals, `E[∑_{i<n} 1{X_i > u}] = n F̄(u)`. -/
theorem integral_tailCount [IsFiniteMeasure P] (hX : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) (u : ℝ) :
    ∫ ω, tailCount X n u ω ∂P = n * survival P (X 0) u := by
  unfold tailCount
  rw [integral_finsetSum _ fun i _ => (memLp_ite_lt (hX i) u 1).integrable le_rfl]
  have : ∀ i, ∫ ω, (if u < X i ω then (1 : ℝ) else 0) ∂P = survival P (X 0) u := by
    intro i
    rw [integral_ite_lt' (hX i)]
    have h := ((hident i).comp (measurable_ite_lt measurable_id u)).integral_eq
    simp only [Function.comp_def, id] at h
    rw [← integral_ite_lt' (hX 0), ← h, integral_ite_lt' (hX i)]
  simp [this]

/-- **Chebyshev for exceedance counts.** If the marginals are identically distributed,
`n F̄(u_n) / b_n → c` and `Var(∑_{i<n} 1{X_i > u_n}) / b_n² → 0`, then
`(1/b_n) ∑_{i<n} 1{X_i > u_n} → c` in probability. No dependence assumption is made beyond the
variance condition. -/
theorem tendsto_measure_abs_tailCount_div_sub [IsProbabilityMeasure P]
    (hX : ∀ i, Measurable (X i)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {u b : ℕ → ℝ} {c : ℝ} (hb : ∀ᶠ n in atTop, 0 < b n)
    (hmean : Tendsto (fun n : ℕ => n * survival P (X 0) (u n) / b n) atTop (𝓝 c))
    (hvar : Tendsto (fun n => variance (tailCount X n (u n)) P / b n ^ 2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |tailCount X n (u n) ω / b n - c|}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (4 / ε ^ 2 *
      (variance (tailCount X n (u n)) P / b n ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using hvar.const_mul (4 / ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  have hmean' := (Metric.tendsto_nhds.1 hmean) (ε / 2) (half_pos hε)
  filter_upwards [hb, hmean'] with n hbn hmn
  set T := tailCount X n (u n) with hT
  have hET : P[T] = n * survival P (X 0) (u n) := integral_tailCount hX hident n (u n)
  rw [Real.dist_eq] at hmn
  have hsub : {ω | ε ≤ |T ω / b n - c|} ⊆ {ω | ε * b n / 2 ≤ |T ω - P[T]|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [hET]
    have h1 : T ω / b n - c = (T ω - n * survival P (X 0) (u n)) / b n +
        (n * survival P (X 0) (u n) / b n - c) := by
      field_simp; ring
    rw [h1] at hω
    have h2 := (abs_add_le _ _).trans' hω
    rw [abs_div, abs_of_pos hbn] at h2
    have h3 : ε / 2 ≤ |T ω - n * survival P (X 0) (u n)| / b n := by linarith
    rw [le_div_iff₀ hbn] at h3
    linarith
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_variance_div_sq (memLp_tailCount hX n (u n) 2) (by positivity)).trans ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp; ring

end TailCount

/-! ### Deterministic Riemann-sum sandwich for the log-excess -/

section Sandwich

theorem logExcess_le_step {s ρ : ℝ} (hs : 0 < s) (hρ : 1 ≤ ρ) (y : ℝ) :
    logExcess s y ≤ Real.log ρ * (if s < y then 1 else 0) + logExcess (s * ρ) y := by
  have hsρ : s ≤ s * ρ := le_mul_of_one_le_right hs.le hρ
  have hsρ0 : 0 < s * ρ := hs.trans_le hsρ
  rcases le_or_gt y s with h | h
  · rw [logExcess_of_le hs h, logExcess_of_le hsρ0 (h.trans hsρ)]
    simp [not_lt.2 h]
  simp only [h, ↓reduceIte, mul_one]
  rcases le_or_gt y (s * ρ) with h' | h'
  · rw [logExcess_of_le hsρ0 h', logExcess_of_ge hs h.le, add_zero]
    have := Real.log_le_log (hs.trans h) h'
    rw [Real.log_mul hs.ne' (zero_lt_one.trans_le hρ).ne'] at this
    linarith
  · rw [logExcess_of_ge hs h.le, logExcess_of_ge hsρ0 h'.le,
      Real.log_mul hs.ne' (zero_lt_one.trans_le hρ).ne']
    linarith

theorem step_le_logExcess {s ρ : ℝ} (hs : 0 < s) (hρ : 1 ≤ ρ) (y : ℝ) :
    Real.log ρ * (if s * ρ < y then 1 else 0) + logExcess (s * ρ) y ≤ logExcess s y := by
  have hsρ : s ≤ s * ρ := le_mul_of_one_le_right hs.le hρ
  have hsρ0 : 0 < s * ρ := hs.trans_le hsρ
  rcases le_or_gt y (s * ρ) with h | h
  · rw [logExcess_of_le hsρ0 h]
    simpa [not_lt.2 h] using logExcess_nonneg hs y
  · simp only [h, ↓reduceIte, mul_one]
    rw [logExcess_of_ge hsρ0 h.le, logExcess_of_ge hs (hsρ.trans h.le),
      Real.log_mul hs.ne' (zero_lt_one.trans_le hρ).ne']
    linarith

/-- Upper Riemann sum: `log⁺(y/s) ≤ log ρ ∑_{j<J} 1{y > s ρ^j} + log⁺(y/(s ρ^J))`. -/
theorem logExcess_le_sum {ρ : ℝ} (hρ : 1 ≤ ρ) (J : ℕ) :
    ∀ {s : ℝ}, 0 < s → ∀ y : ℝ, logExcess s y ≤
      Real.log ρ * (∑ j ∈ range J, if s * ρ ^ j < y then (1 : ℝ) else 0) +
        logExcess (s * ρ ^ J) y := by
  induction J with
  | zero => intro s hs y; simp
  | succ J ih =>
    intro s hs y
    have hsρ0 : 0 < s * ρ := mul_pos hs (zero_lt_one.trans_le hρ)
    have h1 := logExcess_le_step hs hρ y
    have h2 := ih hsρ0 y
    rw [Finset.sum_range_succ', pow_zero, mul_one, mul_add]
    have e : ∀ j : ℕ, s * ρ ^ (j + 1) = s * ρ * ρ ^ j := fun j => by ring
    simp only [e]
    linarith

/-- Lower Riemann sum: `log ρ ∑_{j<J} 1{y > s ρ^{j+1}} ≤ log⁺(y/s)`. -/
theorem sum_le_logExcess {ρ : ℝ} (hρ : 1 ≤ ρ) (J : ℕ) :
    ∀ {s : ℝ}, 0 < s → ∀ y : ℝ,
      Real.log ρ * (∑ j ∈ range J, if s * ρ ^ (j + 1) < y then (1 : ℝ) else 0) ≤
        logExcess s y := by
  induction J with
  | zero => intro s hs y; simpa using logExcess_nonneg hs y
  | succ J ih =>
    intro s hs y
    have hsρ0 : 0 < s * ρ := mul_pos hs (zero_lt_one.trans_le hρ)
    have h1 := step_le_logExcess hs hρ y
    have h2 := ih hsρ0 y
    rw [Finset.sum_range_succ', zero_add, pow_one, mul_add]
    have e : ∀ j : ℕ, s * ρ ^ (j + 1 + 1) = s * ρ * ρ ^ (j + 1) := fun j => by ring
    simp only [e]
    linarith

end Sandwich

/-! ### Deterministic thresholds -/

section Threshold

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For a regularly varying survival function and an intermediate sequence `k`, there are
deterministic thresholds `t_n → ∞` with `n F̄(c t_n) / k_n → c^{-α}` for every `c > 0`. -/
theorem exists_threshold {Y : Ω → ℝ} (hY : Measurable Y) {α : ℝ}
    (hRV : IsRegularlyVarying (survival P Y) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
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

end ExtremeValueTheory
