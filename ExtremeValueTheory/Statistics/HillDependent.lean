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

/-! ### Hill consistency from the tail empirical measure -/

section Consistency

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] in
/-- Summed lower Riemann sandwich. -/
theorem sum_tailCount_le_sum_logExcess (X : ℕ → Ω → ℝ) {ρ s : ℝ} (hρ : 1 ≤ ρ) (hs : 0 < s)
    (J n : ℕ) (ω : Ω) :
    Real.log ρ * ∑ j ∈ range J, tailCount X n (s * ρ ^ (j + 1)) ω ≤
      ∑ i ∈ range n, logExcess s (X i ω) := by
  unfold tailCount
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => sum_le_logExcess hρ J hs (X i ω)

omit [MeasurableSpace Ω] in
/-- Summed upper Riemann sandwich. -/
theorem sum_logExcess_le_sum_tailCount (X : ℕ → Ω → ℝ) {ρ s : ℝ} (hρ : 1 ≤ ρ) (hs : 0 < s)
    (J n : ℕ) (ω : Ω) :
    ∑ i ∈ range n, logExcess s (X i ω) ≤
      Real.log ρ * ∑ j ∈ range J, tailCount X n (s * ρ ^ j) ω +
        ∑ i ∈ range n, logExcess (s * ρ ^ J) (X i ω) := by
  unfold tailCount
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => logExcess_le_sum hρ J hs (X i ω)

/-- Geometric Riemann sums of `u ↦ e^{-α u}` with mesh `log ρ`. -/
theorem geom_riemann_bounds {α ρ : ℝ} (hα : 0 < α) (hρ : 1 < ρ) (J : ℕ) :
    1 / α * (1 - (ρ ^ (-α)) ^ J) ≤ Real.log ρ * ∑ j ∈ range J, (ρ ^ (-α)) ^ j ∧
      Real.log ρ * ∑ j ∈ range J, (ρ ^ (-α)) ^ j ≤ 1 / α + Real.log ρ := by
  set q := ρ ^ (-α) with hq
  set ℓ := Real.log ρ with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos hρ
  have hqexp : q = Real.exp (-(α * ℓ)) := by
    simp only [hq, hℓ, Real.rpow_def_of_pos (zero_lt_one.trans hρ)]; ring_nf
  have hq0 : 0 < q := by rw [hqexp]; exact Real.exp_pos _
  have h1 : 1 - q ≤ α * ℓ := by
    have := Real.add_one_le_exp (-(α * ℓ)); rw [← hqexp] at this; linarith
  have h2 : α * ℓ * q ≤ 1 - q := by
    have h := Real.add_one_le_exp (α * ℓ)
    have e : Real.exp (α * ℓ) * q = 1 := by rw [hqexp, ← Real.exp_add]; simp
    nlinarith
  set S := ∑ j ∈ range J, q ^ j with hS
  have hgeom : S * (1 - q) = 1 - q ^ J := by
    have := geom_sum_mul q J
    rw [← hS] at this; linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => (pow_pos hq0 j).le
  have hqJ : 0 ≤ q ^ J := (pow_pos hq0 J).le
  constructor
  · rw [← hgeom, div_mul_eq_mul_div, one_mul, div_le_iff₀ hα]
    nlinarith
  · have e1 : S ≤ 1 + q * S := by nlinarith
    have e2 : α * ℓ * S ≤ α * ℓ * (1 + q * S) := mul_le_mul_of_nonneg_left e1 (by positivity)
    have e3 : α * ℓ * q * S ≤ (1 - q) * S := mul_le_mul_of_nonneg_right h2 hS0
    rw [div_add' _ _ _ hα.ne', le_div_iff₀ hα]
    nlinarith

/-- **Hill consistency under a variance condition on exceedance counts.** Let `X_0, X_1, …` be
identically distributed (no independence or stationarity is assumed) with survival function
`F̄(x) = P(X_0 > x)` regularly varying with index `-α`, `α > 0`, and let `k(n) → ∞`,
`k(n)/n → 0`. Assume the **variance condition**: along every sequence of levels `u_n → ∞` with
`n F̄(u_n) / k_n → c > 0`, `Var(∑_{i<n} 1{X_i > u_n}) / k_n² → 0`. Then the Hill estimator
`H_{k(n),n}` converges in probability to `1/α`.

The variance condition is exactly what makes the tail empirical measure
`(1/k) ∑_{i<n} 1{X_i > x u_n}` consistent; the log-excess functional is then handled by a
deterministic Riemann-sum sandwich plus Markov's inequality for the remainder, which needs only
the marginal law. -/
theorem tendstoInMeasure_hill_of_variance {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hvar : ∀ (u : ℕ → ℝ) (c : ℝ), 0 < c → Tendsto u atTop atTop →
      Tendsto (fun n => n * (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 c) →
      Tendsto (fun n => variance (tailCount X n (u n)) P / (k n : ℝ) ^ 2) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  set F := survival P (X 0) with hF_def
  change IsRegularlyVarying F (-α) at hRV
  obtain ⟨t, htinf, hcount⟩ := exists_threshold (hX 0) hRV hk hkn
  have hFpos : ∀ x, 0 < F x := survival_pos hRV
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  -- consistency of the tail empirical measure
  have hW : ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |tailCount X n (c * t n) ω / k n - c ^ (-α)|}) atTop (𝓝 0) := fun c hc δ hδ =>
    tendsto_measure_abs_tailCount_div_sub hX hident hkpos (hcount c hc)
      (hvar _ _ (Real.rpow_pos_of_pos hc _) (htinf.const_mul_atTop hc) (hcount c hc)) hδ
  -- Markov's inequality for the log-excess remainder
  obtain ⟨x₀, C, hx₀, hL2⟩ := exists_memLp_logExcess (hX 0) hα hRV
  have hR : ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, 1 / α * c ^ (-α) / δ < θ →
      ∀ᶠ n in atTop, P {ω | δ ≤ (∑ i ∈ range n, logExcess (c * t n) (X i ω)) / k n} ≤
        ENNReal.ofReal θ := by
    intro c hc δ hδ θ hθ
    have hct : Tendsto (fun n => c * t n) atTop atTop := htinf.const_mul_atTop hc
    have hmean : Tendsto (fun n => n * (∫ ω, logExcess (c * t n) (X 0 ω) ∂P) / k n) atTop
        (𝓝 (1 / α * c ^ (-α))) := by
      have h := ((tendsto_integral_logExcess_div (hX 0) hα hRV).comp hct).mul (hcount c hc)
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, ← hF_def]
      field_simp [(hFpos (c * t n)).ne']
    have hθ' : 1 / α * c ^ (-α) < θ * δ := by rwa [div_lt_iff₀ hδ] at hθ
    filter_upwards [hmean.eventually (gt_mem_nhds hθ'), hct.eventually_ge_atTop x₀, hkpos]
      with n hn hxn hkn'
    have hI : ∀ i, Integrable (fun ω => logExcess (c * t n) (X i ω)) P := fun i =>
      (((hident i).comp (measurable_logExcess (c * t n))).memLp_iff.2
        (hL2 _ hxn).1).integrable one_le_two
    have hEi : ∀ i, ∫ ω, logExcess (c * t n) (X i ω) ∂P =
        ∫ ω, logExcess (c * t n) (X 0 ω) ∂P := fun i =>
      ((hident i).comp (measurable_logExcess (c * t n))).integral_eq
    set Z : Ω → ℝ := fun ω => (∑ i ∈ range n, logExcess (c * t n) (X i ω)) / k n with hZ
    have hZint : Integrable Z P := (integrable_finsetSum _ fun i _ => hI i).div_const _
    have hEZ : ∫ ω, Z ω ∂P = n * (∫ ω, logExcess (c * t n) (X 0 ω) ∂P) / k n := by
      rw [hZ, integral_div, integral_finsetSum _ fun i _ => hI i]
      simp [hEi]
    have hM := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω =>
      div_nonneg (Finset.sum_nonneg fun i _ => logExcess_nonneg (hx₀.trans_le hxn) _)
        hkn'.le) hZint δ
    rw [hEZ] at hM
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have : δ * P.real {ω | δ ≤ Z ω} < θ * δ := hM.trans_lt hn
    exact (lt_of_mul_lt_mul_left (this.trans_eq (mul_comm θ δ)) hδ.le).le
  -- choice of the mesh `ρ`
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨θ, hθ0, hθpos, hθη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hθ : 0 < θ := by
    rcases hθ0.lt_or_eq with h | h
    · exact h
    · rw [← h, ENNReal.ofReal_zero] at hθpos; exact absurd hθpos (lt_irrefl _)
  set a := 1 / α with ha
  have ha0 : 0 < a := by positivity
  have hf : Tendsto (fun ρ : ℝ => ρ ^ α * (Real.log ρ + a) - a) (𝓝 1) (𝓝 0) := by
    have h1 : ContinuousAt (fun ρ : ℝ => ρ ^ α * (Real.log ρ + a) - a) 1 :=
      ((Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)).mul
        ((Real.continuousAt_log one_ne_zero).add continuousAt_const)).sub continuousAt_const
    simpa using h1.tendsto
  have hg : Tendsto (fun ρ : ℝ => a * (1 - (ρ ^ (-α)) ^ 2)) (𝓝 1) (𝓝 0) := by
    have h1 : ContinuousAt (fun ρ : ℝ => a * (1 - (ρ ^ (-α)) ^ 2)) 1 :=
      continuousAt_const.mul (continuousAt_const.sub
        ((Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)).pow 2))
    simpa using h1.tendsto
  obtain ⟨ρ, ⟨hfρ, hgρ⟩, hρ1⟩ := ((((hf.eventually (gt_mem_nhds (half_pos hε))).and
    (hg.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity)))).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
  change 1 < ρ at hρ1
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ1
  set ℓ := Real.log ρ with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos hρ1
  set q := ρ ^ (-α) with hq
  set r := ρ ^ α with hr
  have hq0 : 0 < q := Real.rpow_pos_of_pos hρ0 _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hρ1 (neg_lt_zero.2 hα)
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ0 _
  have hrq : r * q = 1 := by
    rw [hr, hq, Real.rpow_neg hρ0.le, mul_inv_cancel₀ hr0.ne']
  have hr1 : 1 < r := Real.one_lt_rpow hρ1 hα
  have hpow : ∀ m : ℕ, (ρ ^ m) ^ (-α) = q ^ m := fun m => (Real.rpow_pow_comm hρ0.le _ m).symm
  have hinv : (ρ⁻¹) ^ (-α) = r := by
    rw [Real.inv_rpow hρ0.le, Real.rpow_neg hρ0.le, inv_inv]
  have hc3 : ∀ j : ℕ, (ρ * ρ ^ (j + 1)) ^ (-α) = q ^ 2 * q ^ j := fun j => by
    rw [← pow_succ', hpow, ← pow_add]; ring_nf
  have hc4 : ∀ j : ℕ, (ρ⁻¹ * ρ ^ j) ^ (-α) = r * q ^ j := fun j => by
    rw [Real.mul_rpow (inv_nonneg.2 hρ0.le) (pow_nonneg hρ0.le j), hinv, hpow]
  -- choice of the truncation level `J`
  set δ' := ε / 8 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  obtain ⟨J, hJ1, hJ2⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 4 / a by positivity))).and
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).eventually
    (gt_mem_nhds (show (0 : ℝ) < θ / 2 * δ' / (a * r) by positivity)))).exists
  set δ := ε / (8 * (ℓ * J + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hℓJδ : ℓ * J * δ < ε / 8 := by
    rw [hδ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨hG1, hG2⟩ := geom_riemann_bounds hα hρ1 J
  rw [← hq, ← hℓ] at hG1 hG2
  -- the bad events
  set c₂ : ℕ → ℝ := fun j => ρ * ρ ^ (j + 1) with hc₂
  set c₁ : ℕ → ℝ := fun j => ρ⁻¹ * ρ ^ j with hc₁
  have hc₂0 : ∀ j, 0 < c₂ j := fun j => by positivity
  have hc₁0 : ∀ j, 0 < c₁ j := fun j => by positivity
  set A : ℕ → Set Ω := fun n =>
    ({ω | 1 - q ≤ |tailCount X n (ρ * t n) ω / k n - ρ ^ (-α)|} ∪
      {ω | r - 1 ≤ |tailCount X n (ρ⁻¹ * t n) ω / k n - ρ⁻¹ ^ (-α)|}) ∪
    ((⋃ j ∈ range J, {ω | δ ≤ |tailCount X n (c₂ j * t n) ω / k n - c₂ j ^ (-α)|}) ∪
      ⋃ j ∈ range J, {ω | δ ≤ |tailCount X n (c₁ j * t n) ω / k n - c₁ j ^ (-α)|}) with hA
  have hAlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    have hlim := ((hW ρ hρ0 (1 - q) (by linarith)).add (hW ρ⁻¹ (inv_pos.2 hρ0) (r - 1) (by linarith))).add
      ((tendsto_finsetSum (range J) fun j _ => hW (c₂ j) (hc₂0 j) δ hδ0).add
        (tendsto_finsetSum (range J) fun j _ => hW (c₁ j) (hc₁0 j) δ hδ0))
    simp only [add_zero, Finset.sum_const_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
    refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans le_rfl)
      ((measure_union_le _ _).trans (add_le_add (measure_biUnion_finset_le _ _)
        (measure_biUnion_finset_le _ _))))
  have hRJ := hR (c₁ J) (hc₁0 J) δ' hδ'0 (θ / 2) (by
    rw [hc₁, hc4, div_lt_iff₀ hδ'0]
    rw [lt_div_iff₀ (by positivity)] at hJ2
    linarith)
  have hkn' : ∀ᶠ n : ℕ in atTop, k n < n := by
    filter_upwards [hkn.eventually (gt_mem_nhds one_pos), hnpos] with n h1 h2
    rw [div_lt_one h2] at h1
    exact_mod_cast h1
  have htpos : ∀ᶠ n in atTop, 0 < t n := htinf.eventually_gt_atTop 0
  filter_upwards [hAlim.eventually (ge_mem_nhds (show (0 : ENNReal) < ENNReal.ofReal (θ / 2) by
    simpa using half_pos hθ)), hRJ, hkn', hkpos, htpos] with n hAn hRn hkn hkpos' htn
  refine le_trans ?_ hθη.le
  rw [show ENNReal.ofReal θ = ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf]
  refine (measure_mono ?_).trans ((measure_union_le (A n) _).trans (add_le_add hAn hRn))
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω
  by_contra hcon
  simp only [hA, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
    not_le, Finset.mem_range] at hcon
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hcon
  set x : Fin n → ℝ := fun i => X i ω with hx
  have hN : ∀ a, (exceedCount x a : ℝ) = tailCount X n a ω := by
    intro a
    rw [exceedCount_eq_sum]
    exact Fin.sum_univ_eq_sum_range (fun i => if a < X i ω then (1 : ℝ) else 0) n
  have hS : ∀ a, ∑ i, logExcess a (x i) = ∑ i ∈ range n, logExcess a (X i ω) := fun a =>
    Fin.sum_univ_eq_sum_range (fun i => logExcess a (X i ω)) n
  -- localisation of the random threshold `X_{(k+1)}`
  have hT2 : orderStat x (k n) ≤ ρ * t n := by
    rw [orderStat_le_iff x hkn]
    have := (abs_lt.1 h1).2
    rw [← hq, ← hN] at this
    have h' : (exceedCount x (ρ * t n) : ℝ) / k n < 1 := by linarith
    rw [div_lt_one hkpos'] at h'
    exact_mod_cast h'.le
  have hT1 : ρ⁻¹ * t n < orderStat x (k n) := by
    rw [lt_orderStat_iff x hkn]
    have := (abs_lt.1 h2).1
    rw [hinv, ← hN] at this
    have h' : 1 < (exceedCount x (ρ⁻¹ * t n) : ℝ) / k n := by linarith
    rw [one_lt_div hkpos'] at h'
    exact_mod_cast h'
  have hs1 : 0 < ρ⁻¹ * t n := by positivity
  have hs2 : 0 < ρ * t n := by positivity
  have hT0 : 0 < orderStat x (k n) := hs1.trans hT1
  rw [hill_eq_sum_logExcess x hkn hT0, ← div_eq_inv_mul, hS] at hω
  have hlo : (∑ i ∈ range n, logExcess (ρ * t n) (X i ω)) / k n ≤
      (∑ i ∈ range n, logExcess (orderStat x (k n)) (X i ω)) / k n :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => logExcess_anti hT0 hT2 _)
      hkpos'.le
  have hhi : (∑ i ∈ range n, logExcess (orderStat x (k n)) (X i ω)) / k n ≤
      (∑ i ∈ range n, logExcess (ρ⁻¹ * t n) (X i ω)) / k n :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => logExcess_anti hs1 hT1.le _)
      hkpos'.le
  -- lower Riemann sum
  have hL := sum_tailCount_le_sum_logExcess X hρ1.le hs2 J n ω
  have hL' : ℓ * ∑ j ∈ range J, (q ^ 2 * q ^ j - δ) ≤
      (∑ i ∈ range n, logExcess (ρ * t n) (X i ω)) / k n := by
    rw [le_div_iff₀ hkpos']
    refine le_trans ?_ hL
    rw [mul_assoc, Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hℓ0.le
    have := (abs_lt.1 (h3 j (Finset.mem_range.1 hj))).1
    rw [hc₂, hc3] at this
    have e : ρ * t n * ρ ^ (j + 1) = ρ * ρ ^ (j + 1) * t n := by ring
    rw [e]
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hkpos'] at this
    linarith
  -- upper Riemann sum
  have hU := sum_logExcess_le_sum_tailCount X hρ1.le hs1 J n ω
  have hU' : (∑ i ∈ range n, logExcess (ρ⁻¹ * t n) (X i ω)) / k n ≤
      ℓ * ∑ j ∈ range J, (r * q ^ j + δ) + δ' := by
    have hR5 : (∑ i ∈ range n, logExcess (ρ⁻¹ * t n * ρ ^ J) (X i ω)) / k n < δ' := by
      have e : ρ⁻¹ * t n * ρ ^ J = c₁ J * t n := by rw [hc₁]; ring
      rw [e]; exact h5
    rw [div_le_iff₀ hkpos']
    rw [div_lt_iff₀ hkpos'] at hR5
    refine hU.trans ?_
    have hsum : ℓ * ∑ j ∈ range J, tailCount X n (ρ⁻¹ * t n * ρ ^ j) ω ≤
        ℓ * ∑ j ∈ range J, (r * q ^ j + δ) * k n := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hℓ0.le
      have := (abs_lt.1 (h4 j (Finset.mem_range.1 hj))).2
      rw [hc₁, hc4] at this
      have e : ρ⁻¹ * t n * ρ ^ j = ρ⁻¹ * ρ ^ j * t n := by ring
      rw [e]
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hkpos'] at this
      linarith
    rw [← Finset.sum_mul] at hsum
    linarith
  -- conclusion
  have hsum2 : ℓ * ∑ j ∈ range J, (q ^ 2 * q ^ j - δ) =
      q ^ 2 * (ℓ * ∑ j ∈ range J, q ^ j) - ℓ * J * δ := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp; ring
  have hsum1 : ℓ * ∑ j ∈ range J, (r * q ^ j + δ) =
      r * (ℓ * ∑ j ∈ range J, q ^ j) + ℓ * J * δ := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
  rw [hsum2] at hL'
  rw [hsum1] at hU'
  have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hfρ' : r * (ℓ + a) - a < ε / 2 := hfρ
  have hgρ' : a * (1 - q ^ 2) < ε / 4 := hgρ
  have hJ1' : a * q ^ J < ε / 4 := by rwa [lt_div_iff₀ ha0, mul_comm] at hJ1
  have hup : r * (ℓ * ∑ j ∈ range J, q ^ j) ≤ r * (a + ℓ) :=
    mul_le_mul_of_nonneg_left hG2 hr0.le
  have hdown : q ^ 2 * (a * (1 - q ^ J)) ≤ q ^ 2 * (ℓ * ∑ j ∈ range J, q ^ j) :=
    mul_le_mul_of_nonneg_left hG1 (by positivity)
  have hqq : q ^ 2 * (a * q ^ J) ≤ a * q ^ J :=
    mul_le_of_le_one_left (by positivity) hq2
  have := abs_lt.2 (⟨by linarith, by linarith⟩ :
    -ε < (∑ i ∈ range n, logExcess (orderStat x (k n)) (X i ω)) / k n - a ∧
      (∑ i ∈ range n, logExcess (orderStat x (k n)) (X i ω)) / k n - a < ε)
  linarith

end Consistency

end ExtremeValueTheory
