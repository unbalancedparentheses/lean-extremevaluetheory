/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.OrderStatistics
import ExtremeValueTheory.RegularVariation.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Hill estimator and its weak consistency

Let `X_{(1)} ≥ X_{(2)} ≥ ⋯ ≥ X_{(n)}` be the descending order statistics of a sample
`X_0, …, X_{n-1}`. The **Hill estimator** of the extreme value index `γ = 1 / α` based on the top
`k + 1` order statistics is

  `H_{k,n} = (1/k) ∑_{i<k} (log X_{(i+1)} - log X_{(k+1)})`.

## Main results

* `ExtremeValueTheory.hill`: the Hill estimator.
* `ExtremeValueTheory.hill_eq_sum_logExcess`: `H_{k,n} = (1/k) ∑_i log⁺ (X_i / X_{(k+1)})`.
* `ExtremeValueTheory.tendstoInMeasure_hill`: **weak consistency** (de Haan and Ferreira,
  *Extreme Value Theory: An Introduction*, Springer 2006, Theorem 3.2.2; Mason, *Laws of large
  numbers for sums of extreme values*, Ann. Probab. 10 (1982)): if the `X_i` are iid with
  survival function `F̄` regularly varying with index `-α`, `α > 0`, and `k = k(n) → ∞`,
  `k / n → 0`, then `H_{k(n),n} → 1 / α` in probability.
* `ExtremeValueTheory.tendstoInMeasure_hill_pareto`: the exact Pareto case.

## Proof

Rather than the Rényi representation of exponential spacings used in de Haan–Ferreira, we use
the (equivalent, and in the spirit of Mason 1982) *tail empirical process* argument, which
only needs Chebyshev's inequality:

1. Deterministically, `H_{k,n} = (1/k) ∑_i log⁺ (X_i / X_{(k+1)})`, and
   `s ↦ ∑_i log⁺ (X_i / s)` is antitone (`hill_eq_sum_logExcess`, `logExcess_anti`).
2. Choose deterministic thresholds `u_n = inf {x | F̄ x ≤ k/n}`; right-continuity of `F̄` and
   regular variation give `n F̄(u_n) / k → 1` and hence `n F̄(c u_n) / k → c ^ (-α)`.
3. For fixed `c > 0`, by Chebyshev (`tendsto_measure_abs_sum_div_sub`):
   * `#{i | X_i > c u_n} / k → c ^ (-α)` in probability (the count is binomial);
   * `(1/k) ∑_i log⁺ (X_i / (c u_n)) → c ^ (-α) / α` in probability. The mean is computed via
     the layer cake formula, `E log⁺ (X / s) = ∫_0^∞ F̄(s e^u) du`, and
     `∫_0^∞ F̄(s e^u) / F̄(s) du → ∫_0^∞ e^{-α u} du = 1/α` by dominated convergence with the
     Potter bounds; the second moment is `O(F̄(s))` by the same bounds.
4. By the duality `X_{(k+1)} > a ↔ #{i | X_i > a} ≥ k + 1`, step 3 gives
   `c₁ u_n < X_{(k+1)} ≤ c₂ u_n` with probability → 1 for any `c₁ < 1 < c₂`, and then
   monotonicity sandwiches `H_{k,n}` between the averages at `c₂ u_n` and `c₁ u_n`, which are
   close to `c₂^{-α}/α` and `c₁^{-α}/α`; letting `c₁, c₂ → 1` concludes.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

/-! ### Deterministic part -/

section Deterministic

variable {n : ℕ}

/-- The **Hill estimator** based on the top `k + 1` order statistics of the sample `x`:
`H_{k,n} = (1/k) ∑_{i<k} (log X_{(i+1)} - log X_{(k+1)})`
(recall that `orderStat x i = X_{(i+1)}`). -/
noncomputable def hill (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i ∈ range k, (Real.log (orderStat x i) - Real.log (orderStat x k))

/-- The log-excess `log⁺ (y / t) = log (max y t / t)` of `y` over the threshold `t`. -/
noncomputable def logExcess (t y : ℝ) : ℝ :=
  Real.log (max y t / t)

theorem logExcess_nonneg {t : ℝ} (ht : 0 < t) (y : ℝ) : 0 ≤ logExcess t y :=
  Real.log_nonneg ((one_le_div ht).2 (le_max_right _ _))

theorem logExcess_of_le {t y : ℝ} (ht : 0 < t) (hy : y ≤ t) : logExcess t y = 0 := by
  simp [logExcess, max_eq_right hy, div_self ht.ne']

theorem logExcess_of_ge {t y : ℝ} (ht : 0 < t) (hy : t ≤ y) :
    logExcess t y = Real.log y - Real.log t := by
  rw [logExcess, max_eq_left hy, Real.log_div (ht.trans_le hy).ne' ht.ne']

/-- The log-excess is antitone in the threshold. -/
theorem logExcess_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (y : ℝ) :
    logExcess t y ≤ logExcess s y := by
  have ht : 0 < t := hs.trans_le hst
  refine Real.log_le_log (div_pos (ht.trans_le (le_max_right _ _)) ht) ?_
  rw [div_le_div_iff₀ ht hs]
  rcases le_total y s with h1 | h1
  · rw [max_eq_right (h1.trans hst), max_eq_right h1]; nlinarith
  rcases le_total y t with h2 | h2
  · rw [max_eq_right h2, max_eq_left h1]; nlinarith
  · rw [max_eq_left h2, max_eq_left h1]; nlinarith

theorem measurable_logExcess (t : ℝ) : Measurable (logExcess t) :=
  ((measurable_id.max measurable_const).div_const t).log

/-- The Hill estimator as an average of log-excesses over the random threshold `X_{(k+1)}`:
if `X_{(k+1)} > 0` then `H_{k,n} = (1/k) ∑_i log⁺ (X_i / X_{(k+1)})`. -/
theorem hill_eq_sum_logExcess (x : Fin n → ℝ) {k : ℕ} (hk : k < n) (ht : 0 < orderStat x k) :
    hill x k = (k : ℝ)⁻¹ * ∑ i, logExcess (orderStat x k) (x i) := by
  rw [hill, ← sum_orderStat x (logExcess (orderStat x k)),
    ← Finset.sum_range_add_sum_Ico _ hk.le]
  congr 1
  rw [Finset.sum_eq_zero (s := Ico k n), add_zero]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [logExcess_of_ge ht (orderStat_anti x (mem_range.1 hi).le hk)]
  · intro j hj
    rw [Finset.mem_Ico] at hj
    exact logExcess_of_le ht (orderStat_anti x hj.1 hj.2)

end Deterministic

/-! ### A weak law of large numbers for triangular arrays, via Chebyshev -/

section WLLN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A weak law of large numbers for row sums `∑_{i<n} g_n(X_i)` of functions of an iid sequence,
normalized by `b_n`, proved by Chebyshev's inequality. Only pairwise independence is used. -/
theorem tendsto_measure_abs_sum_div_sub {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {g : ℕ → ℝ → ℝ} (hg : ∀ n, Measurable (g n))
    {b : ℕ → ℝ} (hb : ∀ᶠ n in atTop, 0 < b n)
    (hL2 : ∀ᶠ n in atTop, MemLp (fun ω => g n (X 0 ω)) 2 P) {m : ℝ}
    (hmean : Tendsto (fun n : ℕ => n * P[fun ω => g n (X 0 ω)] / b n) atTop (𝓝 m))
    (hvar : Tendsto (fun n : ℕ => n * P[fun ω => g n (X 0 ω) ^ 2] / b n ^ 2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |(∑ i ∈ range n, g n (X i ω)) / b n - m|}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (4 / ε ^ 2 *
      (n * P[fun ω => g n (X 0 ω) ^ 2] / b n ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using hvar.const_mul (4 / ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  have hmean' := (Metric.tendsto_nhds.1 hmean) (ε / 2) (half_pos hε)
  filter_upwards [hb, hL2, hmean'] with n hbn hL2n hmn
  set Y : ℕ → Ω → ℝ := fun i ω => g n (X i ω) with hY
  have hYId : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i => by
    have := (hident i).comp (hg n)
    simpa [hY, Function.comp_def] using this
  have hYL2 : ∀ i, MemLp (Y i) 2 P := fun i => (hYId i).memLp_iff.2 hL2n
  have hYind : ∀ i j, i ≠ j → IndepFun (Y i) (Y j) P := fun i j hij =>
    (hindep.indepFun hij).comp (hg n) (hg n)
  set T : Ω → ℝ := ∑ i ∈ range n, Y i with hT
  have hTfun : ∀ ω, T ω = ∑ i ∈ range n, g n (X i ω) := fun ω => by
    simp [hT, hY, Finset.sum_apply]
  have hTL2 : MemLp T 2 P := memLp_finsetSum' _ fun i _ => hYL2 i
  have hET : P[T] = (n : ℝ) * P[Y 0] := by
    have : ∫ ω, T ω ∂P = ∑ i ∈ range n, ∫ ω, Y i ω ∂P := by
      simp only [hT, Finset.sum_apply]
      exact integral_finsetSum _ fun i _ => (hYL2 i).integrable one_le_two
    rw [this, Finset.sum_congr rfl fun i _ => (hYId i).integral_eq, sum_const, card_range,
      nsmul_eq_mul]
  have hVT : variance T P ≤ n * P[fun ω => g n (X 0 ω) ^ 2] := by
    rw [hT, IndepFun.variance_sum (fun i _ => hYL2 i)
      (fun i _ j _ hij => hYind i j hij)]
    rw [Finset.sum_congr rfl fun i _ => (hYId i).variance_eq, sum_const, card_range,
      nsmul_eq_mul]
    gcongr
    exact variance_le_expectation_sq (hYL2 0).aestronglyMeasurable
  rw [Real.dist_eq] at hmn
  have hEY : P[Y 0] = ∫ ω, g n (X 0 ω) ∂P := rfl
  rw [hEY] at hET
  have hsub : {ω | ε ≤ |(∑ i ∈ range n, g n (X i ω)) / b n - m|} ⊆
      {ω | ε * b n / 2 ≤ |T ω - P[T]|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [hTfun, hET]
    have h1 : (∑ i ∈ range n, g n (X i ω)) / b n - m =
        ((∑ i ∈ range n, g n (X i ω)) - n * ∫ ω, g n (X 0 ω) ∂P) / b n +
          (n * (∫ ω, g n (X 0 ω) ∂P) / b n - m) := by
      field_simp; ring
    rw [h1] at hω
    have h2 := (abs_add_le _ _).trans' hω
    rw [abs_div, abs_of_pos hbn] at h2
    have h3 : ε / 2 ≤ |∑ i ∈ range n, g n (X i ω) - n * ∫ ω, g n (X 0 ω) ∂P| / b n := by
      linarith
    rw [le_div_iff₀ hbn] at h3
    linarith
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_variance_div_sq hTL2 (by positivity)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  calc variance T P ≤ n * P[fun ω => g n (X 0 ω) ^ 2] := hVT
    _ = _ := by field_simp; ring

end WLLN

/-! ### Tail integrals of a regularly varying survival function -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The survival function `x ↦ P(Y > x)` of a real random variable. -/
noncomputable def survival (P : Measure Ω) (Y : Ω → ℝ) (x : ℝ) : ℝ :=
  (P {ω | x < Y ω}).toReal

variable {Y : Ω → ℝ}

theorem survival_anti (Y : Ω → ℝ) : Antitone (survival P Y) := by
  intro a b hab
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
  exact lt_of_le_of_lt hab hω

omit [IsProbabilityMeasure P] in
theorem survival_nonneg (x : ℝ) : 0 ≤ survival P Y x := ENNReal.toReal_nonneg

theorem survival_pos {α : ℝ} (hRV : IsRegularlyVarying (survival P Y) (-α)) (t : ℝ) :
    0 < survival P Y t := by
  obtain ⟨s, hs, hts⟩ := (hRV.eventually_pos.and (eventually_ge_atTop t)).exists
  exact hs.trans_le (survival_anti Y hts)

theorem survival_eq_one_sub_cdf (hY : Measurable Y) (x : ℝ) :
    survival P Y x = 1 - cdf (P.map Y) x := by
  rw [cdf_eq_real, map_measureReal_apply hY measurableSet_Iic, survival,
    ← probReal_compl_eq_one_sub (hY measurableSet_Iic), measureReal_def]
  congr 2
  ext ω
  simp

theorem continuousWithinAt_survival (hY : Measurable Y) (x : ℝ) :
    ContinuousWithinAt (survival P Y) (Ici x) x := by
  have h := ((cdf (P.map Y)).right_continuous x).const_sub 1
  exact ContinuousWithinAt.congr h (fun y _ => survival_eq_one_sub_cdf hY y)
    (survival_eq_one_sub_cdf hY x)

theorem tendsto_survival_atTop (hY : Measurable Y) :
    Tendsto (survival P Y) atTop (𝓝 0) := by
  have h := (tendsto_cdf_atTop (μ := P.map Y)).const_sub 1
  rw [sub_self] at h
  exact h.congr fun y => (survival_eq_one_sub_cdf (P := P) hY y).symm

omit [MeasurableSpace Ω] in
theorem setOf_lt_logExcess {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    {ω | u < logExcess s (Y ω)} = {ω | s * Real.exp u < Y ω} := by
  ext ω
  simp only [mem_ofPred_eq, logExcess]
  rw [Real.lt_log_iff_exp_lt (div_pos (hs.trans_le (le_max_right _ _)) hs), lt_div_iff₀ hs,
    mul_comm, lt_max_iff]
  have : ¬ s * Real.exp u < s := by
    have := Real.one_lt_exp_iff.2 hu
    nlinarith
  tauto

/-- A consequence of the Potter bounds: the survival function decays at least like
`exp (-(α/2) u)` along `s * exp u`, uniformly in large `s`. -/
theorem exists_survival_exp_le {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (survival P Y) (-α)) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ s ≥ x₀, ∀ u : ℝ, 0 ≤ u →
      survival P Y (s * Real.exp u) ≤ 2 * survival P Y s * Real.exp (-(α / 2) * u) := by
  obtain ⟨x₀, hx₀, hpos, hb⟩ := hRV.potter_bound (a := 0) (Or.inr ((survival_anti (P := P) Y).antitoneOn _))
    (half_pos hα) one_lt_two
  refine ⟨x₀, hx₀, fun s hs u hu => ?_⟩
  have hs0 : 0 < s := hx₀.trans_le hs
  have hsu : x₀ ≤ s * Real.exp u := hs.trans (le_mul_of_one_le_right hs0.le (Real.one_le_exp hu))
  have h := hb s hs _ hsu
  rw [mul_div_cancel_left₀ _ hs0.ne', div_le_iff₀ (hpos s hs)] at h
  have hmax : max (Real.exp u ^ (-α + α / 2)) (Real.exp u ^ (-α - α / 2)) =
      Real.exp (-(α / 2) * u) := by
    rw [max_eq_left (Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hu) (by linarith)),
      ← Real.exp_mul]
    congr 1; ring
  rw [hmax] at h
  linarith

omit [IsProbabilityMeasure P] in
theorem integral_logExcess {s : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω => logExcess s (Y ω)) P) :
    ∫ ω, logExcess s (Y ω) ∂P = ∫ u in Ioi 0, survival P Y (s * Real.exp u) := by
  rw [hint.integral_eq_integral_meas_lt (Eventually.of_forall fun ω => logExcess_nonneg hs _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [setOf_lt_logExcess hs hu]
  rfl

theorem integrableOn_mul_exp_neg {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-b * u)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) one_pos hb
  simpa using this

/-- Second moment bound for the log-excess over a high threshold. -/
theorem lintegral_logExcess_sq_le (hY : Measurable Y) {α : ℝ} (hα : 0 < α) {x₀ s : ℝ}
    (hx₀ : 0 < x₀) (hs : x₀ ≤ s)
    (hb : ∀ u : ℝ, 0 ≤ u →
      survival P Y (s * Real.exp u) ≤ 2 * survival P Y s * Real.exp (-(α / 2) * u)) :
    ∫⁻ ω, ENNReal.ofReal (logExcess s (Y ω) ^ 2) ∂P ≤
      ENNReal.ofReal (4 * (∫ u in Ioi 0, u * Real.exp (-(α / 2) * u)) * survival P Y s) := by
  have hs0 : 0 < s := hx₀.trans_le hs
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul P
    (Eventually.of_forall fun ω => logExcess_nonneg hs0 (Y ω))
    ((measurable_logExcess s).comp hY).aemeasurable two_pos
  simp only [Real.rpow_two] at h
  rw [h]
  have hI := integrableOn_mul_exp_neg (half_pos hα)
  have hFs := survival_nonneg (P := P) (Y := Y) s
  calc ENNReal.ofReal 2 * ∫⁻ t in Ioi 0, P {a | t < logExcess s (Y a)} *
        ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
      ≤ ENNReal.ofReal 2 * ∫⁻ t in Ioi 0,
          ENNReal.ofReal (2 * survival P Y s * (t * Real.exp (-(α / 2) * t))) := by
        gcongr 1
        refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
        rw [Set.mem_Ioi] at ht
        rw [setOf_lt_logExcess hs0 ht, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
          ← ENNReal.ofReal_toReal (measure_ne_top P _), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        have := hb t ht.le
        change survival P Y (s * Real.exp t) * t ≤ _
        nlinarith
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (2 * survival P Y s *
          ∫ u in Ioi 0, u * Real.exp (-(α / 2) * u)) := by
        rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hI.const_mul _)]
        refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
        have : 0 < t := ht
        positivity
    _ = _ := by
        rw [← ENNReal.ofReal_mul zero_le_two]
        congr 1; ring

theorem integral_exp_neg_mul_Ioi {α : ℝ} (hα : 0 < α) :
    ∫ u in Ioi 0, Real.exp (-α * u) = 1 / α := by
  rw [integral_exp_mul_Ioi (neg_lt_zero.2 hα) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]

/-- The mean log-excess over a high threshold `s`, divided by the tail probability `F̄(s)`,
tends to `1 / α` as `s → ∞`: this is the integrated form of regular variation used by the
Hill estimator. -/
theorem tendsto_integral_logExcess_div (hY : Measurable Y) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (survival P Y) (-α)) :
    Tendsto (fun s => (∫ ω, logExcess s (Y ω) ∂P) / survival P Y s) atTop (𝓝 (1 / α)) := by
  obtain ⟨x₀, hx₀, hb⟩ := exists_survival_exp_le hα hRV
  have hFpos := survival_pos hRV
  -- integrability of the log-excess for large thresholds
  have hint : ∀ s ≥ x₀, Integrable (fun ω => logExcess s (Y ω)) P := by
    intro s hs
    have hm : AEStronglyMeasurable (fun ω => logExcess s (Y ω)) P :=
      ((measurable_logExcess s).comp hY).aestronglyMeasurable
    refine ((memLp_two_iff_integrable_sq hm).2 ⟨hm.pow 2, ?_⟩).integrable one_le_two
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    exact (lintegral_logExcess_sq_le hY hα hx₀ hs (hb s hs)).trans_lt ENNReal.ofReal_lt_top
  rw [← integral_exp_neg_mul_Ioi hα]
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (l := atTop) (F := fun s u => survival P Y (s * Real.exp u) / survival P Y s)
    (f := fun u => Real.exp (-α * u)) (fun u => 2 * Real.exp (-(α / 2) * u)) ?_ ?_ ?_ ?_
  · refine key.congr' ?_
    filter_upwards [eventually_ge_atTop x₀] with s hs
    rw [integral_logExcess (hx₀.trans_le hs) (hint s hs), integral_div]
  · filter_upwards [eventually_gt_atTop 0] with s hs
    refine ((Antitone.measurable (f := fun u => survival P Y (s * Real.exp u)) ?_).div_const
      _).aestronglyMeasurable
    exact (survival_anti Y).comp_monotone fun u v huv =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 huv) hs.le
  · filter_upwards [eventually_ge_atTop x₀] with s hs
    refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (survival_nonneg _) (survival_nonneg _)),
      div_le_iff₀ (hFpos s)]
    have := hb s hs u (le_of_lt hu)
    linarith
  · exact (exp_neg_integrableOn_Ioi 0 (half_pos hα)).const_mul 2
  · refine Eventually.of_forall fun u => ?_
    have h := hRV.tendsto (Real.exp_pos u)
    rw [← Real.exp_mul, show u * -α = -α * u by ring] at h
    exact h.congr fun s => by rw [mul_comm]

/-- For thresholds `s ≥ x₀`, the log-excess is square integrable, with
`E[log⁺(Y/s)²] ≤ C F̄(s)`. -/
theorem exists_memLp_logExcess (hY : Measurable Y) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (survival P Y) (-α)) :
    ∃ x₀ C : ℝ, 0 < x₀ ∧ ∀ s ≥ x₀, MemLp (fun ω => logExcess s (Y ω)) 2 P ∧
      ∫ ω, logExcess s (Y ω) ^ 2 ∂P ≤ C * survival P Y s := by
  obtain ⟨x₀, hx₀, hb⟩ := exists_survival_exp_le hα hRV
  refine ⟨x₀, 4 * ∫ u in Ioi 0, u * Real.exp (-(α / 2) * u), hx₀, fun s hs => ?_⟩
  have hm : AEStronglyMeasurable (fun ω => logExcess s (Y ω)) P :=
    ((measurable_logExcess s).comp hY).aestronglyMeasurable
  have hL := lintegral_logExcess_sq_le hY hα hx₀ hs (hb s hs)
  refine ⟨(memLp_two_iff_integrable_sq hm).2 ⟨hm.pow 2, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    exact hL.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
      (hm.pow 2)]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hL).trans ?_
    rw [ENNReal.toReal_ofReal]
    have : 0 ≤ ∫ u in Ioi 0, u * Real.exp (-(α / 2) * u) :=
      setIntegral_nonneg measurableSet_Ioi fun u hu => by
        have : 0 < u := hu
        positivity
    have := survival_nonneg (P := P) (Y := Y) s
    positivity

end Tail

/-! ### The deterministic threshold `u_n` with `n F̄(u_n) / k_n → 1` -/

section Threshold

/-- The generalized inverse `sInf {x | F x ≤ p}` of a right-continuous antitone function. -/
theorem threshold_spec {F : ℝ → ℝ} (hF : Antitone F) (hrc : ∀ x, ContinuousWithinAt F (Ici x) x)
    (h0 : Tendsto F atTop (𝓝 0)) {p M : ℝ} (hp : 0 < p) (hM : p < F M) :
    F (sInf {x | F x ≤ p}) ≤ p ∧ (∀ x < sInf {x | F x ≤ p}, p < F x) ∧
      M ≤ sInf {x | F x ≤ p} := by
  set S := {x | F x ≤ p} with hS
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := (h0.eventually (gt_mem_nhds hp)).exists
    exact ⟨x, hx.le⟩
  have hlow : ∀ x ∈ S, M < x := by
    intro x hx
    by_contra h
    exact absurd ((hF (not_lt.1 h)).trans hx) (not_le.2 hM)
  have hbdd : BddBelow S := ⟨M, fun x hx => (hlow x hx).le⟩
  refine ⟨?_, fun x hx => ?_, le_csInf hne fun x hx => (hlow x hx).le⟩
  · have hle : ∀ x ∈ Ioi (sInf S), F x ≤ p := by
      intro x hx
      obtain ⟨y, hyS, hyx⟩ := exists_lt_of_csInf_lt hne hx
      exact (hF hyx.le).trans hyS
    have hc := (hrc (sInf S)).mono Ioi_subset_Ici_self
    exact le_of_tendsto hc (eventually_nhdsWithin_of_forall hle)
  · have := notMem_of_lt_csInf hx hbdd
    simpa [hS] using this

end Threshold

/-! ### Weak consistency of the Hill estimator -/

section Consistency

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private lemma integral_ite_lt (X : Ω → ℝ) (hX : Measurable X) (a : ℝ) :
    ∫ ω, (if a < X ω then (1 : ℝ) else 0) ∂P = survival P X a := by
  have : (fun ω => if a < X ω then (1 : ℝ) else 0) = {ω | a < X ω}.indicator 1 := by
    ext ω; simp [Set.indicator]
  rw [this, integral_indicator_one (measurableSet_lt measurable_const hX), measureReal_def]
  rfl

/-- **Weak consistency of the Hill estimator** (de Haan and Ferreira, *Extreme Value Theory:
An Introduction*, 2006, Theorem 3.2.2; Mason 1982). Let `X_0, X_1, …` be iid real random
variables whose survival function `F̄ x = P(X_0 > x)` is regularly varying with index `-α`,
`α > 0`, and let `k = k(n)` be an intermediate sequence: `k(n) → ∞` and `k(n) / n → 0`. Then the
Hill estimator `H_{k(n),n}` built from `X_0, …, X_{n-1}` converges in probability to `1 / α`. -/
theorem tendstoInMeasure_hill {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  set F := survival P (X 0) with hF_def
  change IsRegularlyVarying F (-α) at hRV
  have hFanti : Antitone F := survival_anti (X 0)
  have hFpos : ∀ x, 0 < F x := survival_pos hRV
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkinv : Tendsto (fun n => ((k n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have hppos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < k n / n := by
    filter_upwards [hkpos, hnpos] with n h1 h2; positivity
  -- the deterministic thresholds
  set t : ℕ → ℝ := fun n => sInf {x | F x ≤ (k n : ℝ) / n} with ht_def
  have hspec : ∀ M, ∀ᶠ n in atTop, F (t n) ≤ (k n : ℝ) / n ∧
      (∀ x < t n, (k n : ℝ) / n < F x) ∧ M ≤ t n := by
    intro M
    filter_upwards [hppos, hkn.eventually (gt_mem_nhds (hFpos M))] with n h1 h2
    exact threshold_spec hFanti (continuousWithinAt_survival (hX 0)) (tendsto_survival_atTop (hX 0))
      h1 h2
  have htinf : Tendsto t atTop atTop :=
    tendsto_atTop.2 fun M => (hspec M).mono fun n h => h.2.2
  -- `n F̄(t_n) / k_n → 1`
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
  have hcount : ∀ c : ℝ, 0 < c → Tendsto (fun n => n * F (c * t n) / k n) atTop (𝓝 (c ^ (-α))) := by
    intro c hc
    have h := ((hRV.tendsto hc).comp htinf).mul hr
    rw [mul_one] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    field_simp [(hFpos (t n)).ne']
  -- the two weak laws of large numbers
  have hWcount : ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |(∑ i ∈ range n, (if c * t n < X i ω then (1 : ℝ) else 0)) / k n - c ^ (-α)|})
      atTop (𝓝 0) := by
    intro c hc δ hδ
    have hsq : ∀ n ω, (if c * t n < X 0 ω then (1 : ℝ) else 0) ^ 2 =
        if c * t n < X 0 ω then (1 : ℝ) else 0 := by
      intro n ω; split_ifs <;> norm_num
    refine tendsto_measure_abs_sum_div_sub hindep hident
      (g := fun n x => if c * t n < x then (1 : ℝ) else 0)
      (fun n => Measurable.ite (measurableSet_lt measurable_const measurable_id)
        measurable_const measurable_const) hkpos (Eventually.of_forall fun n => ?_) ?_ ?_ hδ
    · refine MemLp.of_bound ?_ 1 (Eventually.of_forall fun ω => ?_)
      · exact (Measurable.ite (measurableSet_lt measurable_const (hX 0)) measurable_const
          measurable_const).aestronglyMeasurable
      · split_ifs <;> norm_num
    · refine (hcount c hc).congr fun n => ?_
      simp only
      rw [integral_ite_lt (X 0) (hX 0)]
    · have h := (hcount c hc).mul hkinv
      rw [mul_zero] at h
      refine h.congr fun n => ?_
      simp only [hsq]
      rw [integral_ite_lt (X 0) (hX 0), ← hF_def]
      field_simp
  obtain ⟨x₀, C, hx₀, hL2⟩ := exists_memLp_logExcess (hX 0) hα hRV
  have hWlog : ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |(∑ i ∈ range n, logExcess (c * t n) (X i ω)) / k n - 1 / α * c ^ (-α)|})
      atTop (𝓝 0) := by
    intro c hc δ hδ
    have hct : Tendsto (fun n => c * t n) atTop atTop := htinf.const_mul_atTop hc
    have hev : ∀ᶠ n in atTop, x₀ ≤ c * t n := hct.eventually_ge_atTop x₀
    refine tendsto_measure_abs_sum_div_sub hindep hident (g := fun n => logExcess (c * t n))
      (fun n => measurable_logExcess _) hkpos (hev.mono fun n hn => (hL2 _ hn).1) ?_ ?_ hδ
    · have h := ((tendsto_integral_logExcess_div (hX 0) hα hRV).comp hct).mul (hcount c hc)
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, ← hF_def]
      field_simp [(hFpos (c * t n)).ne']
    · have hb := ((hcount c hc).mul hkinv).const_mul C
      rw [mul_zero, mul_zero] at hb
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
      · refine Eventually.of_forall fun n => ?_
        have : 0 ≤ ∫ ω, logExcess (c * t n) (X 0 ω) ^ 2 ∂P :=
          integral_nonneg fun ω => sq_nonneg _
        positivity
      · filter_upwards [hev, hkpos] with n hn hkn'
        have h := (hL2 _ hn).2
        rw [div_le_iff₀ (by positivity)]
        calc (n : ℝ) * ∫ ω, logExcess (c * t n) (X 0 ω) ^ 2 ∂P
            ≤ n * (C * F (c * t n)) := by gcongr
          _ = C * (n * F (c * t n) / k n * (k n : ℝ)⁻¹) * (k n : ℝ) ^ 2 := by
            field_simp
  -- choice of the constants `c₁ < 1 < c₂`
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hcont : Tendsto (fun c : ℝ => c ^ (-α)) (𝓝 1) (𝓝 1) := by
    have := Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)
    simpa using this.tendsto
  have hαε : 0 < α * ε / 2 := by positivity
  obtain ⟨c₂, hc₂a, hc₂1⟩ := (((hcont.eventually (lt_mem_nhds (show 1 - α * ε / 2 < 1 by
    linarith))).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
  have e₁ : ∀ᶠ c in 𝓝[<] (1 : ℝ), c ^ (-α) < 1 + α * ε / 2 :=
    (hcont.eventually (gt_mem_nhds (show 1 < 1 + α * ε / 2 by linarith))).filter_mono
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
  have hm₂ : 1 / α - ε / 2 < 1 / α * c₂ ^ (-α) := by
    have : 1 / α * (1 - α * ε / 2) < 1 / α * c₂ ^ (-α) :=
      mul_lt_mul_of_pos_left hc₂a (by positivity)
    have e : 1 / α * (1 - α * ε / 2) = 1 / α - ε / 2 := by field_simp
    linarith
  have hm₁ : 1 / α * c₁ ^ (-α) < 1 / α + ε / 2 := by
    have : 1 / α * c₁ ^ (-α) < 1 / α * (1 + α * ε / 2) :=
      mul_lt_mul_of_pos_left hc₁a (by positivity)
    have e : 1 / α * (1 + α * ε / 2) = 1 / α + ε / 2 := by field_simp
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
  filter_upwards [hkn', hkpos, hspec 1] with n hkn hkpos' hsp
  have htn : 0 < t n := one_pos.trans_le hsp.2.2
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add_left
    ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)) _))
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_le] at hcon
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
  set x : Fin n → ℝ := fun i => X i ω with hx
  have hN : ∀ a, (exceedCount x a : ℝ) = ∑ i ∈ range n, if a < X i ω then (1 : ℝ) else 0 := by
    intro a
    rw [exceedCount_eq_sum]
    exact Fin.sum_univ_eq_sum_range (fun i => if a < X i ω then (1 : ℝ) else 0) n
  have hS : ∀ a, ∑ i, logExcess a (x i) = ∑ i ∈ range n, logExcess a (X i ω) := fun a =>
    Fin.sum_univ_eq_sum_range (fun i => logExcess a (X i ω)) n
  -- localisation of the random threshold `X_{(k+1)}`
  have hT2 : orderStat x (k n) ≤ c₂ * t n := by
    rw [orderStat_le_iff x hkn]
    have := (abs_lt.1 h1).2
    rw [← hN] at this
    have h' : (exceedCount x (c₂ * t n) : ℝ) / k n < 1 := by linarith
    rw [div_lt_one hkpos'] at h'
    exact_mod_cast h'.le
  have hT1 : c₁ * t n < orderStat x (k n) := by
    rw [lt_orderStat_iff x hkn]
    have := (abs_lt.1 h2).1
    rw [← hN] at this
    have h' : 1 < (exceedCount x (c₁ * t n) : ℝ) / k n := by linarith
    rw [one_lt_div hkpos'] at h'
    exact_mod_cast h'
  have hc₁t : 0 < c₁ * t n := mul_pos hc₁0 htn
  have hT0 : 0 < orderStat x (k n) := hc₁t.trans hT1
  rw [hill_eq_sum_logExcess x hkn hT0, ← div_eq_inv_mul] at hω
  have hlo : (∑ i ∈ range n, logExcess (c₂ * t n) (X i ω)) / k n ≤
      (∑ i, logExcess (orderStat x (k n)) (x i)) / k n := by
    rw [← hS]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun i _ => logExcess_anti hT0 hT2 _) hkpos'.le
  have hhi : (∑ i, logExcess (orderStat x (k n)) (x i)) / k n ≤
      (∑ i ∈ range n, logExcess (c₁ * t n) (X i ω)) / k n := by
    rw [← hS]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun i _ => logExcess_anti hc₁t hT1.le _) hkpos'.le
  have e3 := (abs_lt.1 h3).1
  have e4 := (abs_lt.1 h4).2
  have : |(∑ i, logExcess (orderStat x (k n)) (x i)) / k n - 1 / α| < ε := by
    rw [abs_lt]; constructor <;> linarith
  linarith

/-- **Weak consistency of the Hill estimator, exact Pareto case.** If `X_0, X_1, …` are iid
`Pareto(α)` random variables, `P(X_0 > x) = x ^ (-α)` for `x ≥ 1`, and `k(n) → ∞`,
`k(n) / n → 0`, then `H_{k(n),n} → 1 / α` in probability. -/
theorem tendstoInMeasure_hill_pareto {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) :=
  tendstoInMeasure_hill hX hindep hident hα ((IsRegularlyVarying.rpow_id (-α)).congr
    ((eventually_ge_atTop 1).mono fun x hx => (hPar x hx).symm)) hk hkn

end Consistency

end ExtremeValueTheory
