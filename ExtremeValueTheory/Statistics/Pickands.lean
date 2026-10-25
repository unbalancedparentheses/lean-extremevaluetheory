/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Hill
import ExtremeValueTheory.PeaksOverThreshold.Converse

/-!
# The Pickands estimator and its weak consistency

Let `X_{(1)} ≥ X_{(2)} ≥ ⋯ ≥ X_{(n)}` be the descending order statistics of a sample
`X_0, …, X_{n-1}` (recall `orderStat x j = X_{(j+1)}`). The **Pickands estimator** of the extreme
value index `ξ ∈ ℝ` is

  `ξ̂_{k,n} = (log 2)⁻¹ log ((X_{(k+1)} - X_{(2k+1)}) / (X_{(2k+1)} - X_{(4k+1)}))`

(J. Pickands III, *Statistical inference using extreme order statistics*, Ann. Statist. 3
(1975); de Haan and Ferreira, *Extreme Value Theory: An Introduction*, Springer 2006, §3.3
[dHF]; Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events*, Springer 1997,
§6.4.2 [EKM]). In the notation of [dHF] these are `X_{n-k,n}`, `X_{n-2k,n}`, `X_{n-4k,n}`.

## Main results

* `ExtremeValueTheory.pickands`: the Pickands estimator.
* `ExtremeValueTheory.tendstoInMeasure_pickands`: **weak consistency** ([EKM, Theorem 6.4.1],
  [dHF, §3.3]): if the `X_i` are iid with c.d.f. `F ∈ MDA(H_ξ)` for some `ξ ∈ ℝ`, and
  `k = k(n) → ∞`, `k / n → 0`, then `ξ̂_{k(n),n} → ξ` in probability.
* `ExtremeValueTheory.tendstoInMeasure_pickands_exponential`: the standard exponential case
  (`ξ = 0`), showing that the hypotheses are satisfiable.

## Proof

Instead of the quantile form of the domain of attraction condition, we use the
Pickands–Balkema–de Haan theorem (`exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV'`):
there is `β > 0` with `F̄ (u + β(u) x) / F̄ u → Ḡ_{ξ,1}(x)` uniformly in `x ≥ 0` as `u ↑ x_F`.

1. Let `u_n = sInf {y | F̄ y ≤ 8 k / n}`. Since `F ∈ MDA(H_ξ)` has no relative jumps at its
   quantiles (`tendsto_quantile_of_tendstoUniformlyOn_excessSurvival`), `n F̄(u_n) / k → 8`, and
   therefore `n F̄(u_n + β(u_n) x) / k → 8 Ḡ(x)` for every `x ≥ 0`.
2. By Chebyshev, the number of exceedances of `u_n + β(u_n) x`, divided by `k`, converges in
   probability to `8 Ḡ(x)` (`tendsto_measure_abs_exceedCount_div_sub`).
3. By the duality `X_{(j+1)} > a ↔ #{i | X_i > a} ≥ j + 1`, for `m ∈ {1, 2, 4}` the normalized
   order statistic `(X_{(mk+1)} - u_n) / β(u_n)` converges in probability to
   `x_m = Λ_ξ(m / 8)`, the point with `8 Ḡ(x_m) = m`.
4. The scale `β(u_n)` and the location `u_n` cancel in the Pickands ratio, and
   `(x_1 - x_2) / (x_2 - x_4) = 2 ^ ξ`; the continuous mapping theorem concludes.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

/-! ### Definition -/

/-- The **Pickands estimator** based on the top `4k + 1` order statistics of the sample `x`:
`(log 2)⁻¹ log ((X_{(k+1)} - X_{(2k+1)}) / (X_{(2k+1)} - X_{(4k+1)}))`
(recall that `orderStat x j = X_{(j+1)}`). -/
noncomputable def pickands {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  Real.log ((orderStat x k - orderStat x (2 * k)) / (orderStat x (2 * k) - orderStat x (4 * k))) /
    Real.log 2

/-! ### The inverse of the GPD survival function -/

section GPDInv

variable {ξ : ℝ}

theorem gpdSurvivalInv_nonneg {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) : 0 ≤ gpdSurvivalInv ξ v := by
  rcases hv1.lt_or_eq with h | h
  · rw [← gpdSurvivalInv_one (ξ := ξ)]
    exact (gpdSurvivalInv_lt_gpdSurvivalInv hv h).le
  · rw [h, gpdSurvivalInv_one]

/-- To the right of `Λ_ξ v`, the GPD survival function is `< v`. -/
theorem gpdSurvival'_lt_of_gpdSurvivalInv_lt {v y : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hy : gpdSurvivalInv ξ v < y) : gpdSurvivalAll ξ 1 y < v := by
  have h0 := gpdSurvivalInv_nonneg (ξ := ξ) hv hv1
  have hle : gpdSurvivalAll ξ 1 y ≤ v := by
    have := gpdSurvivalAll_antitoneOn (ξ := ξ) one_pos (mem_Ici.2 h0) (mem_Ici.2 (h0.trans hy.le))
      hy.le
    rwa [gpdSurvivalAll_gpdSurvivalInv hv] at this
  refine hle.lt_of_ne fun heq => ?_
  have := gpdSurvivalInv_gpdSurvivalAll (ξ := ξ) (x := y) (by rw [heq]; exact hv)
  rw [heq] at this
  exact hy.ne this

/-- To the left of `Λ_ξ v` (on `[0, ∞)`), the GPD survival function is `> v`. -/
theorem lt_gpdSurvival'_of_lt_gpdSurvivalInv {v y : ℝ} (hv : 0 < v) (hy0 : 0 ≤ y)
    (hy : y < gpdSurvivalInv ξ v) : v < gpdSurvivalAll ξ 1 y := by
  have hle : v ≤ gpdSurvivalAll ξ 1 y := by
    have := gpdSurvivalAll_antitoneOn (ξ := ξ) one_pos (mem_Ici.2 hy0)
      (mem_Ici.2 (hy0.trans hy.le)) hy.le
    rwa [gpdSurvivalAll_gpdSurvivalInv hv] at this
  refine hle.lt_of_ne fun heq => ?_
  have := gpdSurvivalInv_gpdSurvivalAll (ξ := ξ) (x := y) (by rw [← heq]; exact hv)
  rw [← heq] at this
  exact hy.ne this.symm

/-- The Pickands ratio of the limit points: with `x_m = Λ_ξ(m/8)`,
`(x_1 - x_2) / (x_2 - x_4) = 2 ^ ξ`. -/
theorem gpdSurvivalInv_pickands_ratio :
    (gpdSurvivalInv ξ (1 / 8) - gpdSurvivalInv ξ (2 / 8)) /
      (gpdSurvivalInv ξ (2 / 8) - gpdSurvivalInv ξ (4 / 8)) = (2 : ℝ) ^ ξ := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [gpdSurvivalInv, ↓reduceIte, rpow_zero]
    have h8 : Real.log (1 / 8) = -3 * Real.log 2 := by
      rw [show (1 / 8 : ℝ) = (2 ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have h4 : Real.log (2 / 8) = -2 * Real.log 2 := by
      rw [show (2 / 8 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have h2 : Real.log (4 / 8) = -1 * Real.log 2 := by
      rw [show (4 / 8 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]; ring
    rw [h8, h4, h2]
    have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp
    ring
  · simp only [gpdSurvivalInv, hξ, ↓reduceIte]
    set t : ℝ := (2 : ℝ) ^ ξ with ht
    have hpow : ∀ j : ℕ, ((1 / 2 : ℝ) ^ j) ^ (-ξ) = t ^ j := by
      intro j
      rw [one_div, inv_pow, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
        ht, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    have e1 : (1 / 8 : ℝ) ^ (-ξ) = t ^ 3 := by rw [← hpow 3]; norm_num
    have e2 : (2 / 8 : ℝ) ^ (-ξ) = t ^ 2 := by rw [← hpow 2]; norm_num
    have e4 : (4 / 8 : ℝ) ^ (-ξ) = t ^ 1 := by rw [← hpow 1]; norm_num
    rw [e1, e2, e4]
    have ht0 : 0 < t := rpow_pos_of_pos two_pos ξ
    have ht1 : t ≠ 1 := by
      intro h
      have := congrArg Real.log h
      rw [ht, Real.log_rpow two_pos, Real.log_one] at this
      rcases mul_eq_zero.1 this with h' | h'
      · exact hξ h'
      · exact (Real.log_pos one_lt_two).ne' h'
    have hd : t ^ 2 - t ^ 1 ≠ 0 := by
      have : t ^ 2 - t ^ 1 = t * (t - 1) := by ring
      rw [this]
      exact mul_ne_zero ht0.ne' (sub_ne_zero.2 ht1)
    have hd' : (t ^ 2 - 1) / ξ - (t ^ 1 - 1) / ξ ≠ 0 := by
      rw [div_sub_div_same, show t ^ 2 - 1 - (t ^ 1 - 1) = t ^ 2 - t ^ 1 by ring]
      exact div_ne_zero hd hξ
    rw [div_eq_iff hd']
    field_simp
    ring

end GPDInv

/-! ### A weak law of large numbers for exceedance counts -/

section Count

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private lemma integral_ite_lt' (X : Ω → ℝ) (hX : Measurable X) (a : ℝ) :
    ∫ ω, (if a < X ω then (1 : ℝ) else 0) ∂P = (P {ω | a < X ω}).toReal := by
  have : (fun ω => if a < X ω then (1 : ℝ) else 0) = {ω | a < X ω}.indicator 1 := by
    ext ω; simp [Set.indicator]
  rw [this, integral_indicator_one (measurableSet_lt measurable_const hX), measureReal_def]

/-- **Exceedance counts over moving thresholds.** If the `X_i` are iid and the deterministic
thresholds `a_n` satisfy `n P(X_0 > a_n) / k_n → c` with `k_n → ∞`, then the number of
exceedances `#{i < n | X_i > a_n}`, divided by `k_n`, converges in probability to `c`. -/
theorem tendsto_measure_abs_exceedCount_div_sub {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) {a : ℕ → ℝ} {c : ℝ}
    (hc : Tendsto (fun n : ℕ => n * (P {ω | a n < X 0 ω}).toReal / k n) atTop (𝓝 c))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ ≤ |(exceedCount (fun i : Fin n => X i ω) (a n) : ℝ) / k n - c|})
      atTop (𝓝 0) := by
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkinv : Tendsto (fun n => ((k n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hN : ∀ n ω, (exceedCount (fun i : Fin n => X i ω) (a n) : ℝ) =
      ∑ i ∈ range n, if a n < X i ω then (1 : ℝ) else 0 := by
    intro n ω
    rw [exceedCount_eq_sum]
    exact Fin.sum_univ_eq_sum_range (fun i => if a n < X i ω then (1 : ℝ) else 0) n
  simp_rw [hN]
  have hsq : ∀ n ω, (if a n < X 0 ω then (1 : ℝ) else 0) ^ 2 =
      if a n < X 0 ω then (1 : ℝ) else 0 := by
    intro n ω; split_ifs <;> norm_num
  refine tendsto_measure_abs_sum_div_sub hindep hident
    (g := fun n x => if a n < x then (1 : ℝ) else 0)
    (fun n => Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const) hkpos (Eventually.of_forall fun n => ?_) ?_ ?_ hδ
  · refine MemLp.of_bound ?_ 1 (Eventually.of_forall fun ω => ?_)
    · exact (Measurable.ite (measurableSet_lt measurable_const (hX 0)) measurable_const
        measurable_const).aestronglyMeasurable
    · split_ifs <;> norm_num
  · refine hc.congr fun n => ?_
    simp only
    rw [integral_ite_lt' (X 0) (hX 0)]
  · have h := hc.mul hkinv
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [hsq]
    rw [integral_ite_lt' (X 0) (hX 0)]
    field_simp

end Count

/-! ### Localization of the order statistics -/

section Consistency

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Localization of an intermediate order statistic.** Suppose the deterministic thresholds
`u_n + b_n x` satisfy `n P(X_0 > u_n + b_n x) / k_n → G x` for `x ≥ 0`. If `0 ≤ x`, `0 ≤ y`,
`G y < m < G x`, then with probability tending to one the normalized order statistic
`(X_{(mk+1)} - u_n) / b_n` lies in `(x, y]`. -/
theorem tendsto_measure_not_mem_orderStat {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) {m : ℕ} (hmk : ∀ᶠ n in atTop, m * k n < n) {u b : ℕ → ℝ}
    (hb : ∀ᶠ n in atTop, 0 < b n) {G : ℝ → ℝ}
    (hlim : ∀ x, 0 ≤ x → Tendsto (fun n : ℕ => n * (P {ω | u n + b n * x < X 0 ω}).toReal / k n)
      atTop (𝓝 (G x)))
    {x y : ℝ} (hx0 : 0 ≤ x) (hx : (m : ℝ) < G x) (hy0 : 0 ≤ y) (hy : G y < m) :
    Tendsto (fun n => P {ω | ¬ (x < (orderStat (fun i : Fin n => X i ω) (m * k n) - u n) / b n ∧
      (orderStat (fun i : Fin n => X i ω) (m * k n) - u n) / b n ≤ y)}) atTop (𝓝 0) := by
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have h1 := tendsto_measure_abs_exceedCount_div_sub hX hindep hident hk (hlim x hx0)
    (sub_pos.2 hx)
  have h2 := tendsto_measure_abs_exceedCount_div_sub hX hindep hident hk (hlim y hy0)
    (sub_pos.2 hy)
  have h := h1.add h2
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hmk, hb, hkpos] with n hn hbn hkn
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
  obtain ⟨e1, e2⟩ := hcon
  apply hω
  set z := fun i : Fin n => X i ω with hz
  constructor
  · rw [lt_div_iff₀ hbn]
    have hlt : u n + b n * x < orderStat z (m * k n) := by
      rw [lt_orderStat_iff z hn]
      have := (abs_lt.1 e1).1
      have h' : (m : ℝ) < (exceedCount z (u n + b n * x) : ℝ) / k n := by linarith
      rw [lt_div_iff₀ hkn] at h'
      have : ((m * k n : ℕ) : ℝ) < exceedCount z (u n + b n * x) := by push_cast; linarith
      exact_mod_cast this
    linarith
  · rw [div_le_iff₀ hbn]
    have hle : orderStat z (m * k n) ≤ u n + b n * y := by
      rw [orderStat_le_iff z hn]
      have := (abs_lt.1 e2).2
      have h' : (exceedCount z (u n + b n * y) : ℝ) / k n < m := by linarith
      rw [div_lt_iff₀ hkn] at h'
      have : (exceedCount z (u n + b n * y) : ℝ) < ((m * k n : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this.le
    linarith

/-! ### Weak consistency of the Pickands estimator -/

/-- **Weak consistency of the Pickands estimator** ([EKM, Theorem 6.4.1], [dHF, §3.3]; Pickands
1975). Let `X_0, X_1, …` be iid real random variables whose c.d.f. `F` is in the maximum domain
of attraction of the generalized extreme value distribution `H_ξ`, for some `ξ ∈ ℝ`, and let
`k = k(n)` be an intermediate sequence: `k(n) → ∞` and `k(n) / n → 0`. Then the Pickands
estimator `ξ̂_{k(n),n}` built from `X_0, …, X_{n-1}` converges in probability to `ξ`. -/
theorem tendstoInMeasure_pickands {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | X 0 ω ≤ x}).toReal)
    {ξ : ℝ} (hMDA : F.IsInMDAGEV ξ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => pickands (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => ξ) := by
  have hFbar : ∀ a, 1 - F a = (P {ω | a < X 0 ω}).toReal := by
    intro a
    have hc : {ω | a < X 0 ω} = {ω | X 0 ω ≤ a}ᶜ := by ext ω; simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_le (hX 0) measurable_const),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, hF]
  obtain ⟨β, hβ, hU⟩ := F.exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV' hMDA
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  -- the deterministic thresholds `u_n = q(8 k / n)`
  set lam : ℕ → ℝ := fun n => 8 * (k n : ℝ) / n with hlam_def
  have hlam : Tendsto lam atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hkn.const_mul 8
      rw [mul_zero] at this
      exact this.congr fun n => by simp only [hlam_def]; ring
    · filter_upwards [hkpos, hnpos] with n h1 h2
      show 0 < 8 * (k n : ℝ) / n
      positivity
  set u : ℕ → ℝ := fun n => sInf {y | 1 - F y ≤ lam n} with hu_def
  have hq := CumulativeDistributionFunction.tendsto_quantile_of_tendstoUniformlyOn_excessSurvival
    hβ hU hlam
  have hu : Tendsto u atTop F.upperEndpointFilter := hq.1
  have hJ : Tendsto (fun n => (1 - F (u n)) / lam n) atTop (𝓝 1) := hq.2.1
  have hβn : ∀ᶠ n in atTop, 0 < β (u n) := hu.eventually hβ
  -- `n F̄(u_n + β(u_n) x) / k_n → 8 Ḡ(x)`
  have hlim : ∀ x, 0 ≤ x → Tendsto (fun n : ℕ =>
      n * (P {ω | u n + β (u n) * x < X 0 ω}).toReal / k n) atTop
      (𝓝 (8 * gpdSurvivalAll ξ 1 x)) := by
    intro x hx
    have h1 := (hU.tendsto_at (mem_Ici.2 hx)).comp hu
    have h2 := (hJ.mul h1).const_mul 8
    rw [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [hu.eventually F.eventually_tail_pos_upperEndpointFilter, hkpos, hnpos]
      with n h3 h4 h5
    simp only [Function.comp_apply, excessSurvival, hlam_def]
    rw [← hFbar]
    field_simp
  have hmk : ∀ m : ℕ, ∀ᶠ n in atTop, m * k n < n := by
    intro m
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    filter_upwards [hkn.eventually (gt_mem_nhds hm), hnpos] with n h1 h2
    rw [div_lt_div_iff₀ h2 (by positivity)] at h1
    have : ((m * k n : ℕ) : ℝ) < n := by
      push_cast
      have : (0 : ℝ) ≤ k n := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast this
  -- localization of `(X_{(mk+1)} - u_n) / β(u_n)` around `Λ_ξ(m/8)`
  have hloc : ∀ v : ℝ, 0 < v → v < 1 → ∀ m : ℕ, (m : ℝ) = 8 * v → ∀ η : ℝ, 0 < η →
      Tendsto (fun n => P {ω | ¬ (gpdSurvivalInv ξ v - η <
        (orderStat (fun i : Fin n => X i ω) (m * k n) - u n) / β (u n) ∧
        (orderStat (fun i : Fin n => X i ω) (m * k n) - u n) / β (u n) ≤
          gpdSurvivalInv ξ v + η)}) atTop (𝓝 0) := by
    intro v hv hv1 m hm η hη
    have hΛ : 0 < gpdSurvivalInv ξ v := by
      have := gpdSurvivalInv_lt_gpdSurvivalInv (ξ := ξ) hv hv1
      rwa [gpdSurvivalInv_one] at this
    set x := gpdSurvivalInv ξ v - min η (gpdSurvivalInv ξ v / 2) with hx_def
    have hmin1 := min_le_left η (gpdSurvivalInv ξ v / 2)
    have hmin2 := min_le_right η (gpdSurvivalInv ξ v / 2)
    have hmin0 : 0 < min η (gpdSurvivalInv ξ v / 2) := lt_min hη (by linarith)
    have hx0 : 0 ≤ x := by rw [hx_def]; linarith
    have hGx := lt_gpdSurvival'_of_lt_gpdSurvivalInv (ξ := ξ) hv hx0 (by rw [hx_def]; linarith)
    have hGy := gpdSurvival'_lt_of_gpdSurvivalInv_lt (ξ := ξ) (y := gpdSurvivalInv ξ v + η) hv
      hv1.le (by linarith)
    have h := tendsto_measure_not_mem_orderStat hX hindep hident hk (hmk m) hβn
      (G := fun x => 8 * gpdSurvivalAll ξ 1 x) hlim hx0 (by rw [hm]; linarith)
      (y := gpdSurvivalInv ξ v + η) (by linarith) (by rw [hm]; linarith)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    intro hc
    apply hω
    exact ⟨by linarith [hc.1], hc.2⟩
  -- the continuous mapping step
  set x₁ := gpdSurvivalInv ξ (1 / 8) with hx₁
  set x₂ := gpdSurvivalInv ξ (2 / 8) with hx₂
  set x₄ := gpdSurvivalInv ξ (4 / 8) with hx₄
  have hratio : (x₁ - x₂) / (x₂ - x₄) = (2 : ℝ) ^ ξ := gpdSurvivalInv_pickands_ratio
  have h24 : x₂ - x₄ ≠ 0 :=
    (sub_pos.2 (gpdSurvivalInv_lt_gpdSurvivalInv (ξ := ξ) (by norm_num) (by norm_num))).ne'
  set φ : ℝ × ℝ × ℝ → ℝ := fun p => Real.log ((p.1 - p.2.1) / (p.2.1 - p.2.2)) / Real.log 2
    with hφ_def
  have hφ : φ (x₁, x₂, x₄) = ξ := by
    simp only [hφ_def]
    rw [hratio, Real.log_rpow two_pos]
    have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp
  have hcont : ContinuousAt φ (x₁, x₂, x₄) := by
    refine ContinuousAt.div_const (ContinuousAt.log (ContinuousAt.div (by fun_prop) (by fun_prop)
      (by simpa using h24)) ?_) _
    change (x₁ - x₂) / (x₂ - x₄) ≠ 0
    rw [hratio]
    exact (rpow_pos_of_pos two_pos ξ).ne'
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hcont ε hε
  have L₁ := hloc (1 / 8) (by norm_num) (by norm_num) 1 (by norm_num) (η / 2) (half_pos hη)
  have L₂ := hloc (2 / 8) (by norm_num) (by norm_num) 2 (by norm_num) (η / 2) (half_pos hη)
  have L₄ := hloc (4 / 8) (by norm_num) (by norm_num) 4 (by norm_num) (η / 2) (half_pos hη)
  simp only [one_mul] at L₁
  have hlim := (L₁.add L₂).add L₄
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hβn] with n hbn
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans
    (add_le_add_left (measure_union_le _ _) _))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
  obtain ⟨⟨c₁, c₂⟩, c₄⟩ := hcon
  set z := fun i : Fin n => X i ω with hz
  set Z₁ := (orderStat z (k n) - u n) / β (u n)
  set Z₂ := (orderStat z (2 * k n) - u n) / β (u n)
  set Z₄ := (orderStat z (4 * k n) - u n) / β (u n)
  have hdist : dist (Z₁, Z₂, Z₄) (x₁, x₂, x₄) < η := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_lt (abs_lt.2 ⟨by linarith [c₁.1], by linarith [c₁.2]⟩)
      (max_lt (abs_lt.2 ⟨by linarith [c₂.1], by linarith [c₂.2]⟩)
        (abs_lt.2 ⟨by linarith [c₄.1], by linarith [c₄.2]⟩))
  have hval : pickands z (k n) = φ (Z₁, Z₂, Z₄) := by
    simp only [pickands, hφ_def]
    congr 2
    have hb := hbn.ne'
    rw [show Z₁ - Z₂ = (orderStat z (k n) - orderStat z (2 * k n)) / β (u n) by ring,
      show Z₂ - Z₄ = (orderStat z (2 * k n) - orderStat z (4 * k n)) / β (u n) by ring,
      div_div_div_cancel_right₀ hb]
  have := hball hdist
  rw [hφ, ← hval] at this
  exact absurd hω (not_le.2 this)

/-- **Weak consistency of the Pickands estimator, exponential case.** If `X_0, X_1, …` are iid
standard exponential random variables (in the Gumbel domain of attraction, `ξ = 0`) and
`k(n) → ∞`, `k(n) / n → 0`, then the Pickands estimator converges in probability to `0`. -/
theorem tendstoInMeasure_pickands_exponential {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hF : ∀ x, CumulativeDistributionFunction.standardExponentialCDF x =
      (P {ω | X 0 ω ≤ x}).toReal) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => pickands (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 0) :=
  tendstoInMeasure_pickands hX hindep hident hF
    (by simpa [CumulativeDistributionFunction.IsInMDAGEV] using
      CumulativeDistributionFunction.isInMDAGumbel_standardExponentialCDF) hk hkn

end Consistency

end ExtremeValueTheory
