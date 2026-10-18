/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Hill
import ExtremeValueTheory.ForMathlib.Probability.Process.Mixing
import Mathlib.Probability.Moments.Covariance
import ExtremeValueTheory.ForMathlib.Probability.Process.Stationary

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
* `ExtremeValueTheory.variance_tailCount_le_of_isStationary`: for a stationary sequence and any
  block length `r`, `Var(∑_{i<n} 1{X_i > u}) ≤ n (F̄(u) + 2 ∑_{1≤h≤r} P(X_0 > u, X_h > u) +
  2 ∑_{r<h<n} α(h))`.
* `ExtremeValueTheory.tendstoInMeasure_hill_of_alphaMixing`: **Hill consistency for stationary
  strongly mixing sequences** under the cluster condition
  `(1/k_n) ∑_{1≤h≤r_n} P(X_h > u_n | X_0 > u_n) → 0` and the mixing condition
  `(n/k_n²) ∑_{r_n<h<n} α(h) → 0`; `tendstoInMeasure_hill_of_alphaMixing_rate` replaces the latter
  by `(n/k_n)² α(r_n + 1) → 0`.

## Hypotheses used at each step

* Chebyshev step (`tendsto_measure_abs_tailCount_div_sub`): measurability, identical marginals
  (for the mean), the variance condition.
* Riemann sandwich (`sum_le_logExcess`, `logExcess_le_sum`): deterministic.
* Remainder (Markov): identical marginals, regular variation (Potter bounds via
  `tendsto_integral_logExcess_div`).
* Thresholds `t_n` (`exists_threshold`): regular variation, right-continuity of `F̄`, `k → ∞`,
  `k/n → 0`.
* `m`-dependence enters only through `variance_tailCount_le_of_isMDependent` (covariances vanish
  beyond lag `m`; lags `≤ m` are bounded by `F̄(u)` since the indicators are nonnegative).
* Strong mixing enters only through `variance_tailCount_le_of_isStationary`: stationarity makes
  `P(X_i > u, X_{i+h} > u)` depend on `h` only, joint exceedances bound covariances at lags
  `≤ r`, and `|Cov(1_A, 1_B)| ≤ α(h)` at lags `> r`.
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

/-- **Chebyshev's weak law along a sequence.** If `E[S_n] / b_n → c` and `Var(S_n) / b_n² → 0`,
then `S_n / b_n → c` in probability. No independence is assumed. -/
theorem tendsto_measure_abs_div_sub_of_variance [IsProbabilityMeasure P] {S : ℕ → Ω → ℝ}
    (hS : ∀ n, MemLp (S n) 2 P) {b : ℕ → ℝ} {c : ℝ} (hb : ∀ᶠ n in atTop, 0 < b n)
    (hmean : Tendsto (fun n => P[S n] / b n) atTop (𝓝 c))
    (hvar : Tendsto (fun n => variance (S n) P / b n ^ 2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |S n ω / b n - c|}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (4 / ε ^ 2 *
      (variance (S n) P / b n ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using hvar.const_mul (4 / ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  have hmean' := (Metric.tendsto_nhds.1 hmean) (ε / 2) (half_pos hε)
  filter_upwards [hb, hmean'] with n hbn hmn
  set T := S n with hT
  rw [Real.dist_eq] at hmn
  have hsub : {ω | ε ≤ |T ω / b n - c|} ⊆ {ω | ε * b n / 2 ≤ |T ω - P[T]|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have h1 : T ω / b n - c = (T ω - P[T]) / b n + (P[T] / b n - c) := by
      field_simp; ring
    rw [h1] at hω
    have h2 := (abs_add_le _ _).trans' hω
    rw [abs_div, abs_of_pos hbn] at h2
    have h3 : ε / 2 ≤ |T ω - P[T]| / b n := by linarith
    rw [le_div_iff₀ hbn] at h3
    linarith
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_variance_div_sq (hS n) (by positivity)).trans ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp; ring

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
    Tendsto (fun n => P {ω | ε ≤ |tailCount X n (u n) ω / b n - c|}) atTop (𝓝 0) :=
  tendsto_measure_abs_div_sub_of_variance (fun n => memLp_tailCount hX n (u n) 2) hb
    (hmean.congr fun n => by rw [integral_tailCount hX hident n (u n)]) hvar hε

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
      Tendsto (fun n => n * survival P Y (c * t n) / k n) atTop (𝓝 (c ^ (-α))) :=
  exists_threshold_of_isRegularlyVarying hY hRV hk hkn

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

/-! ### `m`-dependent sequences -/

section MDependent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For nonnegative square-integrable `Y, Z`, `cov(Y, Z) ≤ (E Y² + E Z²) / 2`. -/
theorem covariance_le_of_nonneg {Y Z : Ω → ℝ} (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hZ0 : ∀ ω, 0 ≤ Z ω) :
    cov[Y, Z; P] ≤ (∫ ω, Y ω ^ 2 ∂P + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
  rw [covariance_eq_sub hY hZ]
  have hYZ : Integrable (Y * Z) P := hY.integrable_mul hZ
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := hY.integrable_sq
  have hZ2 : Integrable (fun ω => Z ω ^ 2) P := hZ.integrable_sq
  have h1 : P[Y * Z] ≤ ∫ ω, (Y ω ^ 2 + Z ω ^ 2) / 2 ∂P :=
    integral_mono hYZ ((hY2.add hZ2).div_const 2) fun ω => by
      simp only [Pi.mul_apply]; nlinarith [sq_nonneg (Y ω - Z ω)]
  rw [integral_div, integral_add hY2 hZ2] at h1
  have h2 : 0 ≤ P[Y] * P[Z] := mul_nonneg (integral_nonneg hY0) (integral_nonneg hZ0)
  linarith

/-- **Variance of sums of an `m`-dependent sequence.** If `X` is `m`-dependent with identically
distributed marginals and `g ≥ 0` with `g(X_0) ∈ L²`, then
`Var(∑_{i<n} g(X_i)) ≤ (2m+1) n E[g(X_0)²]`. -/
theorem variance_sum_le_of_isMDependent {X : ℕ → Ω → ℝ} {m : ℕ}
    (hdep : IsMDependent X m P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {g : ℝ → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hL2 : MemLp (fun ω => g (X 0 ω)) 2 P) (n : ℕ) :
    variance (fun ω => ∑ i ∈ range n, g (X i ω)) P ≤
      (2 * m + 1) * n * ∫ ω, g (X 0 ω) ^ 2 ∂P := by
  set Y : ℕ → Ω → ℝ := fun i ω => g (X i ω) with hY
  have hYid : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i => by
    simpa [hY, Function.comp_def] using (hident i).comp hg
  have hYL2 : ∀ i, MemLp (Y i) 2 P := fun i => (hYid i).memLp_iff.2 hL2
  have hY2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂P = ∫ ω, g (X 0 ω) ^ 2 ∂P := fun i => by
    have := ((hYid i).comp (measurable_id.pow_const 2)).integral_eq
    simpa [hY, Function.comp_def] using this
  set M := ∫ ω, g (X 0 ω) ^ 2 ∂P with hM
  have hM0 : 0 ≤ M := integral_nonneg fun ω => sq_nonneg _
  have hcov : ∀ i j, cov[Y i, Y j; P] ≤ if i ≤ j + m ∧ j ≤ i + m then M else 0 := by
    intro i j
    split_ifs with h
    · have := covariance_le_of_nonneg (hYL2 i) (hYL2 j) (fun ω => hg0 _) (fun ω => hg0 _)
      rw [hY2, hY2] at this
      linarith
    · rw [not_and_or, not_le, not_le] at h
      refine le_of_eq ?_
      rcases h with h | h
      · rw [covariance_comm]
        exact ((hdep.indepFun h).comp hg hg).covariance_eq_zero (hYL2 j) (hYL2 i)
      · exact ((hdep.indepFun h).comp hg hg).covariance_eq_zero (hYL2 i) (hYL2 j)
  rw [variance_fun_sum' fun i _ => hYL2 i]
  have hrow : ∀ i, ∑ j ∈ range n, cov[Y i, Y j; P] ≤ (2 * m + 1) * M := by
    intro i
    refine (Finset.sum_le_sum fun j _ => hcov i j).trans ?_
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hM0
    have hsub : (range n).filter (fun j => i ≤ j + m ∧ j ≤ i + m) ⊆ Icc (i - m) (i + m) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      omega
    have hc := (Finset.card_le_card hsub).trans_eq (Nat.card_Icc _ _)
    have : i + m + 1 - (i - m) ≤ 2 * m + 1 := by omega
    exact_mod_cast hc.trans this
  calc ∑ i ∈ range n, ∑ j ∈ range n, cov[Y i, Y j; P]
      ≤ ∑ i ∈ range n, (2 * m + 1) * M := Finset.sum_le_sum fun i _ => hrow i
    _ = (2 * m + 1) * n * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **Exceedance counts of `m`-dependent sequences:**
`Var(∑_{i<n} 1{X_i > u}) ≤ (2m+1) n F̄(u)`. -/
theorem variance_tailCount_le_of_isMDependent {X : ℕ → Ω → ℝ} {m : ℕ}
    (hX : ∀ i, Measurable (X i)) (hdep : IsMDependent X m P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) (u : ℝ) :
    variance (tailCount X n u) P ≤ (2 * m + 1) * n * survival P (X 0) u := by
  have h := variance_sum_le_of_isMDependent hdep hident (g := fun x => if u < x then 1 else 0)
    (measurable_ite_lt measurable_id u) (fun x => by split_ifs <;> norm_num)
    (memLp_ite_lt (hX 0) u 2) n
  have hsq : (fun ω => (if u < X 0 ω then (1 : ℝ) else 0) ^ 2) =
      fun ω => if u < X 0 ω then (1 : ℝ) else 0 := by
    ext ω; split_ifs <;> norm_num
  rw [hsq, integral_ite_lt' (hX 0)] at h
  exact h

/-- **Weak consistency of the Hill estimator for `m`-dependent sequences.** Let `X_0, X_1, …` be
an `m`-dependent sequence (for some fixed `m`) with identically distributed marginals (no further
stationarity is needed), whose survival function `F̄(x) = P(X_0 > x)` is regularly varying with
index `-α`, `α > 0`, and let `k(n) → ∞`, `k(n)/n → 0`. Then `H_{k(n),n} → 1/α` in probability.

The `m = 0` case contains (pairwise-independent) iid sequences; the hypotheses used are
`IsMDependent X m P` only through `variance_tailCount_le_of_isMDependent`. -/
theorem tendstoInMeasure_hill_of_isMDependent {X : ℕ → Ω → ℝ} {m : ℕ}
    (hX : ∀ i, Measurable (X i)) (hdep : IsMDependent X m P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  refine tendstoInMeasure_hill_of_variance hX hident hα hRV hk hkn fun u c _ _ hmean => ?_
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkinv : Tendsto (fun n => ((k n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
  have hb := (hmean.mul hkinv).const_mul (2 * (m : ℝ) + 1)
  rw [mul_zero, mul_zero] at hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun n => by have := variance_nonneg (tailCount X n (u n)) P; positivity)
    ?_
  filter_upwards [hkR.eventually_gt_atTop 0] with n hkn'
  have h := variance_tailCount_le_of_isMDependent hX hdep hident n (u n)
  calc variance (tailCount X n (u n)) P / (k n : ℝ) ^ 2
      ≤ (2 * m + 1) * n * survival P (X 0) (u n) / (k n : ℝ) ^ 2 := by gcongr
    _ = (2 * m + 1) * (n * (P {ω | u n < X 0 ω}).toReal / k n * (k n : ℝ)⁻¹) := by
      rw [survival]; field_simp

end MDependent

/-! ### Strongly mixing stationary sequences with a cluster condition -/

section Mixing

/-- A double sum over `i, j < n` of a function of the lag `|i - j|` is at most
`n (b 0 + 2 ∑_{1 ≤ h < n} b h)`. -/
theorem sum_sum_dist_le {b : ℕ → ℝ} (hb : ∀ h, 0 ≤ b h) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, b (i - j + (j - i)) ≤
      n * (b 0 + 2 * ∑ h ∈ Ico 1 n, b h) := by
  have hrow : ∀ i ∈ range n, ∑ j ∈ range n, b (i - j + (j - i)) ≤
      b 0 + 2 * ∑ h ∈ Ico 1 n, b h := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsplit : ∑ j ∈ range n, b (i - j + (j - i)) =
        ∑ j ∈ (range n).filter (· < i), b (i - j) + ∑ j ∈ (range n).filter (· = i), b 0 +
          ∑ j ∈ (range n).filter (i < ·), b (j - i) := by
      rw [← Finset.sum_filter_add_sum_filter_not (range n) (· < i),
        ← Finset.sum_filter_add_sum_filter_not ((range n).filter fun j => ¬ j < i) (· = i),
        Finset.filter_filter, Finset.filter_filter, add_assoc]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_filter] at hj
        congr 1; omega
      congr 1
      · refine Finset.sum_congr (by ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega)
          fun j hj => ?_
        rw [Finset.mem_filter] at hj
        rw [hj.2]; simp
      · refine Finset.sum_congr (by ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega)
          fun j hj => ?_
        rw [Finset.mem_filter] at hj
        congr 1; omega
    have h1 : ∑ j ∈ (range n).filter (· < i), b (i - j) ≤ ∑ h ∈ Ico 1 n, b h := by
      rw [← Finset.sum_image (g := fun j => i - j) (fun x hx y hy hxy => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hy hxy; omega)]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) fun h _ _ => hb h
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hh
      obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hh
      simp only [Finset.mem_Ico]; omega
    have h2 : ∑ j ∈ (range n).filter (i < ·), b (j - i) ≤ ∑ h ∈ Ico 1 n, b h := by
      rw [← Finset.sum_image (g := fun j => j - i) (fun x hx y hy hxy => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hy hxy; omega)]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) fun h _ _ => hb h
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hh
      obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hh
      simp only [Finset.mem_Ico]; omega
    have h3 : ∑ j ∈ (range n).filter (· = i), b 0 = b 0 := by
      have : (range n).filter (· = i) = {i} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
      rw [this, Finset.sum_singleton]
    rw [hsplit, h3]
    linarith
  refine (Finset.sum_le_sum hrow).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

open scoped Classical in
/-- The covariance of the indicators of two events: `cov(1_A, 1_B) = P(A ∩ B) - P(A) P(B)`. -/
theorem covariance_ite_mem {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[fun ω => if ω ∈ A then (1 : ℝ) else 0, fun ω => if ω ∈ B then (1 : ℝ) else 0; P] =
      P.real (A ∩ B) - P.real A * P.real B := by
  have hi : ∀ {C : Set Ω}, (fun ω => if ω ∈ C then (1 : ℝ) else 0) = C.indicator 1 := by
    intro C; ext ω; simp [Set.indicator]
  have hL : ∀ {C : Set Ω}, MeasurableSet C → MemLp (C.indicator (1 : Ω → ℝ)) 2 P :=
    fun hC => (memLp_const (1 : ℝ)).indicator hC.nullMeasurableSet
  rw [hi, hi, covariance_eq_sub (hL hA) (hL hB)]
  have e : A.indicator (1 : Ω → ℝ) * B.indicator 1 = (A ∩ B).indicator 1 := by
    ext ω
    simp only [Pi.mul_apply, Set.indicator, Set.mem_inter_iff, Pi.one_apply]
    split_ifs <;> simp_all
  rw [e, integral_indicator_one (hA.inter hB), integral_indicator_one hA,
    integral_indicator_one hB]

/-- The covariance of two exceedance indicators. -/
theorem covariance_ite_lt {Y Z : Ω → ℝ} (hY : Measurable Y) (hZ : Measurable Z) (u : ℝ) :
    cov[fun ω => if u < Y ω then (1 : ℝ) else 0, fun ω => if u < Z ω then (1 : ℝ) else 0; P] =
      P.real ({ω | u < Y ω} ∩ {ω | u < Z ω}) - P.real {ω | u < Y ω} * P.real {ω | u < Z ω} :=
  covariance_ite_mem (A := {ω | u < Y ω}) (B := {ω | u < Z ω})
    (measurableSet_lt measurable_const hY) (measurableSet_lt measurable_const hZ)

/-- **Variance of exceedance counts of a stationary strongly mixing sequence.** For every
`r`, `Var(∑_{i<n} 1{X_i > u}) ≤ n (F̄(u) + 2 ∑_{1 ≤ h ≤ r} P(X_0 > u, X_h > u) +
2 ∑_{r < h < n} α(h))`: lags up to `r` are controlled by the joint exceedance probabilities
(the cluster part), longer lags by the strong mixing coefficients. -/
theorem variance_tailCount_le_of_isStationary {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hstat : IsStationary X P) (n r : ℕ) (u : ℝ) :
    variance (tailCount X n u) P ≤ n * (survival P (X 0) u +
      2 * ∑ h ∈ Icc 1 r, P.real {ω | u < X 0 ω ∧ u < X h ω} +
      2 * ∑ h ∈ Ico (r + 1) n, (alphaMixing X P h).toReal) := by
  set Y : ℕ → Ω → ℝ := fun i ω => if u < X i ω then 1 else 0 with hY
  set p : ℕ → ℝ := fun h => P.real {ω | u < X 0 ω ∧ u < X h ω} with hp
  set b : ℕ → ℝ := fun h => if h = 0 then survival P (X 0) u else if h ≤ r then p h
    else (alphaMixing X P h).toReal with hb
  have hb0 : ∀ h, 0 ≤ b h := fun h => by
    simp only [hb]; split_ifs
    · exact survival_nonneg _
    · exact measureReal_nonneg
    · exact ENNReal.toReal_nonneg
  have hident := fun i => hstat.identDistrib hX i
  -- the joint exceedance probabilities are shift invariant
  have hpair : ∀ i h, P.real ({ω | u < X i ω} ∩ {ω | u < X (i + h) ω}) = p h := by
    intro i h
    have hC : MeasurableSet {x : ℕ → ℝ | u < x 0 ∧ u < x h} :=
      (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
        (measurableSet_lt measurable_const (measurable_pi_apply h))
    have := hstat.measureReal_preimage_shift hX i hC
    have e1 : {ω | u < X i ω} ∩ {ω | u < X (i + h) ω} =
        (fun ω (t : ℕ) => X (t + i) ω) ⁻¹' {x : ℕ → ℝ | u < x 0 ∧ u < x h} := by
      ext ω; simp [add_comm h i]
    have e2 : {ω | u < X 0 ω ∧ u < X h ω} =
        (fun ω (t : ℕ) => X t ω) ⁻¹' {x : ℕ → ℝ | u < x 0 ∧ u < x h} := by
      ext ω; simp
    show _ = P.real {ω | u < X 0 ω ∧ u < X h ω}
    rw [e1, this, ← e2]
  -- covariance bound for `i ≤ j`
  have hcov' : ∀ i h, cov[Y i, Y (i + h); P] ≤ b h := by
    intro i h
    rw [hY, covariance_ite_lt (hX i) (hX (i + h)) u]
    simp only [hb]
    split_ifs with h0 hr
    · subst h0
      simp only [add_zero, Set.inter_self]
      have := mul_nonneg (measureReal_nonneg (μ := P) (s := {ω | u < X i ω}))
        (measureReal_nonneg (μ := P) (s := {ω | u < X i ω}))
      have e : P.real {ω | u < X i ω} = survival P (X 0) u := by
        show (P {ω | u < X i ω}).toReal = (P {ω | u < X 0 ω}).toReal
        congr 1
        exact (hident i).measure_mem_eq measurableSet_Ioi
      linarith
    · rw [hpair]
      have := mul_nonneg (measureReal_nonneg (μ := P) (s := {ω | u < X i ω}))
        (measureReal_nonneg (μ := P) (s := {ω | u < X (i + h) ω}))
      linarith
    · refine (le_abs_self _).trans ?_
      refine abs_measureReal_inter_sub_le_alphaMixing (s := i) ?_ ?_
      · exact comap_le_pastMeasurableSpace le_rfl _ ⟨Ioi u, measurableSet_Ioi, rfl⟩
      · exact comap_le_futureMeasurableSpace le_rfl _ ⟨Ioi u, measurableSet_Ioi, rfl⟩
  have hcov : ∀ i j, cov[Y i, Y j; P] ≤ b (i - j + (j - i)) := by
    intro i j
    rcases le_total i j with hij | hij
    · obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [show i - (i + h) + (i + h - i) = h by omega]
      exact hcov' i h
    · obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [covariance_comm, show j + h - j + (j - (j + h)) = h by omega]
      exact hcov' j h
  have hYL2 : ∀ i, MemLp (Y i) 2 P := fun i => memLp_ite_lt (hX i) u 2
  have hV : variance (tailCount X n u) P = ∑ i ∈ range n, ∑ j ∈ range n, cov[Y i, Y j; P] :=
    variance_fun_sum' fun i _ => hYL2 i
  rw [hV]
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcov i j).trans
    ((sum_sum_dist_le hb0 n).trans ?_)
  have hbs : ∑ h ∈ Ico 1 n, b h ≤ ∑ h ∈ Icc 1 r, p h +
      ∑ h ∈ Ico (r + 1) n, (alphaMixing X P h).toReal := by
    have e : ∀ h ∈ Finset.Ico 1 n, b h = if h ≤ r then p h else (alphaMixing X P h).toReal := by
      intro h hh
      rw [Finset.mem_Ico] at hh
      have h0 : h ≠ 0 := by omega
      simp only [hb, h0, ↓reduceIte]
    rw [Finset.sum_congr rfl e, Finset.sum_ite]
    gcongr
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hh ⊢; omega
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Ico] at hh ⊢; omega
  have hb00 : b 0 = survival P (X 0) u := by simp [hb]
  rw [hb00]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- **Weak consistency of the Hill estimator for stationary strongly mixing sequences**
(Resnick and Stărică 1995; Rootzén, Leadbetter and de Haan 1998). Let `X` be a stationary
sequence whose marginal survival function `F̄` is regularly varying with index `-α`, `α > 0`,
let `k(n) → ∞`, `k(n)/n → 0`, and let `r(n)` be a sequence of block lengths such that

* (**cluster condition**) along every `u_n → ∞` with `n F̄(u_n) / k_n → c > 0`,
  `(1/k_n) ∑_{1 ≤ h ≤ r_n} P(X_h > u_n | X_0 > u_n) → 0` (in particular, this holds whenever the
  anticlustering-type sums `∑_{1 ≤ h ≤ r_n} P(X_h > u_n | X_0 > u_n)` stay bounded);
* (**mixing condition**) `(n / k_n²) ∑_{r_n < h < n} α(h) → 0`.

Then `H_{k(n),n} → 1/α` in probability. -/
theorem tendstoInMeasure_hill_of_alphaMixing {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hstat : IsStationary X P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (r : ℕ → ℕ)
    (hclus : ∀ (u : ℕ → ℝ) (c : ℝ), 0 < c → Tendsto u atTop atTop →
      Tendsto (fun n => n * (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 c) →
      Tendsto (fun n => (∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
        (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) / (k n : ℝ) ^ 2 *
      ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P h).toReal) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  have hident := fun i => hstat.identDistrib hX i
  refine tendstoInMeasure_hill_of_variance hX hident hα hRV hk hkn fun u c hc hu hmean => ?_
  have hFpos : ∀ x, 0 < (P {ω | x < X 0 ω}).toReal := survival_pos hRV
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkinv : Tendsto (fun n => ((k n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
  have hb := ((hmean.mul hkinv).add ((hmean.mul (hclus u c hc hu hmean)).const_mul 2)).add
    (hmix.const_mul 2)
  simp only [mul_zero, add_zero] at hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun n => by have := variance_nonneg (tailCount X n (u n)) P; positivity)
    ?_
  filter_upwards [hkR.eventually_gt_atTop 0] with n hkn'
  have h := variance_tailCount_le_of_isStationary hX hstat n (r n) (u n)
  have hF := hFpos (u n)
  calc variance (tailCount X n (u n)) P / (k n : ℝ) ^ 2
      ≤ n * (survival P (X 0) (u n) +
          2 * ∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} +
          2 * ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P h).toReal) / (k n : ℝ) ^ 2 := by gcongr
    _ = _ := by rw [survival]; field_simp

omit [IsProbabilityMeasure P] in
/-- The strong mixing coefficients of a process are antitone in the lag. -/
theorem alphaMixing_anti {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E) :
    Antitone (alphaMixing X P) := fun h h' hh =>
  iSup_mono fun _ => strongMixingCoeff_mono le_rfl (futureMeasurableSpace_anti (by omega))

/-- **Hill consistency under strong mixing, with a simple rate.** As
`tendstoInMeasure_hill_of_alphaMixing`, with the mixing condition replaced by the sufficient
`(n / k_n)² α(r_n + 1) → 0`. -/
theorem tendstoInMeasure_hill_of_alphaMixing_rate {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hstat : IsStationary X P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (r : ℕ → ℕ)
    (hclus : ∀ (u : ℕ → ℝ) (c : ℝ), 0 < c → Tendsto u atTop atTop →
      Tendsto (fun n => n * (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 c) →
      Tendsto (fun n => (∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
        (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => ((n : ℝ) / k n) ^ 2 *
      (alphaMixing X P (r n + 1)).toReal) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  refine tendstoInMeasure_hill_of_alphaMixing hX hstat hα hRV hk hkn r hclus ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmix
    (Eventually.of_forall fun n => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)) (Eventually.of_forall fun n => ?_)
  have hs : ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P h).toReal ≤
      n * (alphaMixing X P (r n + 1)).toReal := by
    calc ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P h).toReal
        ≤ ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P (r n + 1)).toReal :=
          Finset.sum_le_sum fun h hh => ENNReal.toReal_mono (alphaMixing_ne_top _)
            (alphaMixing_anti X (Finset.mem_Ico.1 hh).1)
      _ ≤ n * (alphaMixing X P (r n + 1)).toReal := by
          rw [sum_const, nsmul_eq_mul, Nat.card_Ico]
          gcongr
          exact Nat.sub_le _ _
  calc (n : ℝ) / (k n : ℝ) ^ 2 * ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P h).toReal
      ≤ (n : ℝ) / (k n : ℝ) ^ 2 * (n * (alphaMixing X P (r n + 1)).toReal) := by gcongr
    _ = ((n : ℝ) / k n) ^ 2 * (alphaMixing X P (r n + 1)).toReal := by ring

end Mixing

end ExtremeValueTheory
