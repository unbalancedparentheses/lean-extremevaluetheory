/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ExtremeQuantile
import ExtremeValueTheory.Statistics.HillNormality
import ExtremeValueTheory.ForMathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Extreme quantile estimation under second-order regular variation

Let `X_0, X_1, …` be iid with tail quantile function `U(t) = F̄^←(1/t)` of second-order regular
variation (`ExtremeValueTheory.IsSecondOrderRegularlyVarying`) with first-order index `γ > 0`,
second-order index `ρ < 0` and auxiliary function `A`, and let `k → ∞`, `k / n → 0`,
`√k A(n/k) → λ ∈ ℝ`. For `p_n > 0` write `d_n = k / (n p_n)` for the extrapolation factor.
We discharge the two hypotheses of the reduction theorems of
`ExtremeValueTheory.Statistics.ExtremeQuantile` (a `√k`-rate for the Hill estimator and the
deterministic extrapolation bias) and obtain the consistency and asymptotic normality of the
Weissman estimator `x̂_p = X_{(k+1)} d_n^{γ̂}` far beyond the sample range ([dHF, §4.3]), and
the consistency of the tail probability estimator ([dHF, §4.4]).

## Main results

* `isBoundedInProbability_of_tendstoInDistribution`: convergence in distribution implies
  tightness (via `MeasureTheory.TendstoInDistribution.exists_measure_le_abs_le`).
* `isRegularlyVarying_of_isRegularlyVarying_survivalQuantile`: if `U` is regularly varying with
  index `γ > 0`, the survival function is regularly varying with index `-1/γ`.
* `survivalQuantile_survival_eq_tailQuantile`, `tailQuantile_eq_survivalQuantile`:
  `U(t) = x_{1/t}`.
* `IsSecondOrderRegularlyVarying.tendsto_div_mul_rpow`: `U(d t) / (U(t) d^γ) → 1` uniformly in
  `d ≥ 1` (using the uniform bound `IsSecondOrderRegularlyVarying.exists_bound_of_neg`).
* `tendstoInMeasure_weissman_div_of_secondOrder`: `x̂_{p_n} / x_{p_n} → 1` in probability if
  `d_n ≥ 1` eventually and `log d_n / √k → 0`.
* `tendstoInMeasure_tailProbEstimator_div_of_secondOrder`: `p̂(y_n) / F̄(y_n) → 1` in
  probability if `x_{k/n} ≤ y_n` eventually and `log (y_n / x_{k/n}) / √k → 0`.
* `isBoundedInProbability_log_orderStat`: `√k (log X_{(k+1)} - log U(n/k)) = O_P(1)`, from
  `isBoundedInProbability_orderStat_sub_log` (`√k (E_{(k+1)} - log(n/k)) = O_P(1)` for
  exponentials, by Chebyshev's inequality for exceedance counts) and the quantile transform.
* `tendstoInDistribution_weissman`: if moreover `d_n → ∞`,
  `(√k / log d_n) (x̂_{p_n} / x_{p_n} - 1) ⇒ N(λ / (1 - ρ), γ²)`.

## Proof of the asymptotic normality

`log (x̂_p / x_p) = (log X_{(k+1)} - log U(n/k)) + (γ̂ - γ) log d_n - r_n` with the deterministic
remainder `r_n = log U(d_n n/k) - log U(n/k) - γ log d_n = O(A(n/k))`. Multiplying by
`√k / log d_n`, the first term is `O_P(1) / log d_n → 0`, the last is `O(1) / log d_n → 0`, and
the middle one is the Hill CLT. The delta method for `exp` (`expSlope`) concludes; the event
`X_{(k+1)} ≤ 0`, where the logarithmic decomposition fails, has vanishing probability.

## References

* [dHF] L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*, Springer, 2006.
* I. Weissman, *Estimation of parameters and large quantiles based on the k largest
  observations*, JASA 73 (1978).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### Tightness from convergence in distribution -/

section Tightness

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- A sequence of real random variables converging in distribution is bounded in probability. -/
theorem isBoundedInProbability_of_tendstoInDistribution {Z : ℕ → Ω → ℝ} {W : Ω' → ℝ}
    (h : TendstoInDistribution Z atTop W (fun _ => P) P') : IsBoundedInProbability P Z := by
  intro ε hε
  obtain ⟨M, hM⟩ := h.exists_measure_le_abs_le hε
  exact ⟨M, hM.mono fun n hn =>
    (measure_mono fun ω hω => (show M < |Z n ω| from hω).le).trans hn⟩

end Tightness

/-! ### First-order consequences of second-order regular variation -/

/-- Second-order regular variation implies (first-order) regular variation. -/
theorem IsSecondOrderRegularlyVarying.isRegularlyVarying {U A : ℝ → ℝ} {γ ρ : ℝ}
    (h : IsSecondOrderRegularlyVarying U γ ρ A) : IsRegularlyVarying U γ := by
  refine ⟨h.eventually_pos, fun x hx => ?_⟩
  have := ((h.tendsto x hx).mul h.tendsto_zero).add_const (x ^ γ)
  rw [mul_zero, zero_add] at this
  refine this.congr' ?_
  filter_upwards [h.eventually_ne_zero] with t ht
  rw [div_mul_cancel₀ _ ht]
  ring

section Inversion

variable {F : ℝ → ℝ}

/-- A regularly varying function with positive index is unbounded. -/
theorem IsRegularlyVarying.exists_lt {U : ℝ → ℝ} {γ : ℝ} (hU : IsRegularlyVarying U γ)
    (hγ : 0 < γ) (z T : ℝ) : ∃ t, T < t ∧ z < U t := by
  set c : ℝ := (1 + 2 ^ γ) / 2 with hc
  have h2 : 1 < (2 : ℝ) ^ γ := one_lt_rpow one_lt_two hγ
  have hc1 : 1 < c := by rw [hc]; linarith
  have hc2 : c < 2 ^ γ := by rw [hc]; linarith
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (((hU.tendsto two_pos).eventually (lt_mem_nhds hc2)).and
    (hU.eventually_pos.and (eventually_gt_atTop (max T 0))))
  have hT0 : max T 0 < max t₀ (max T 0 + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  set s := max t₀ (max T 0 + 1) with hs
  have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hT0
  have hiter : ∀ m : ℕ, c ^ m * U s ≤ U (2 ^ m * s) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hm : t₀ ≤ 2 ^ m * s :=
        (le_max_left _ _).trans (le_mul_of_one_le_left hs0.le (one_le_pow₀ one_le_two))
      obtain ⟨h1, h2, -⟩ := ht₀ _ hm
      rw [lt_div_iff₀ h2] at h1
      rw [pow_succ, pow_succ, mul_assoc (2 ^ m) 2 s, mul_comm (2 : ℝ) s, ← mul_assoc,
        mul_comm _ (2 : ℝ)]
      nlinarith
  have hUs : 0 < U s := (ht₀ s (le_max_left _ _)).2.1
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hc1).eventually_gt_atTop
    (z / U s)).exists
  refine ⟨2 ^ m * s, ?_, ?_⟩
  · have := le_mul_of_one_le_left hs0.le (one_le_pow₀ (one_le_two : (1 : ℝ) ≤ 2) (n := m))
    have : T < s := lt_of_le_of_lt (le_max_left _ _) hT0
    linarith
  · rw [div_lt_iff₀ hUs] at hm
    linarith [hiter m]

/-- **Inversion of regular variation**: if the tail quantile function `U = F̄^←(1/·)` of a
survival function `F̄` is regularly varying with index `γ > 0`, then `F̄` is regularly varying
with index `-1/γ` ([BGT, Theorem 1.5.12]; [dHF, Corollary 1.2.10]). -/
theorem isRegularlyVarying_of_isRegularlyVarying_survivalQuantile (hF : Antitone F)
    (hrc : ∀ x, ContinuousWithinAt F (Ici x) x) (h0 : Tendsto F atTop (𝓝 0))
    (h1 : Tendsto F atBot (𝓝 1)) {γ : ℝ} (hγ : 0 < γ)
    (hU : IsRegularlyVarying (survivalQuantile F) γ) : IsRegularlyVarying F (-(1 / γ)) := by
  set U := survivalQuantile F with hUdef
  have hGal : ∀ {t : ℝ}, 1 < t → ∀ x, U t ≤ x ↔ F x ≤ t⁻¹ := fun ht x =>
    tailQuantile_le_iff hF hrc h0 h1 ht x
  -- `F` is positive
  have hFpos : ∀ z, 0 < F z := by
    intro z
    by_contra hz
    obtain ⟨t, ht, hzt⟩ := hU.exists_lt hγ z 1
    have : U t ≤ z := (hGal ht z).2 ((not_lt.1 hz).trans (inv_pos.2 (one_pos.trans ht)).le)
    linarith
  refine ⟨Eventually.of_forall hFpos, fun c hc => ?_⟩
  set T : ℝ → ℝ := fun y => (F y)⁻¹ with hT
  have hTlim : Tendsto T atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall hFpos⟩)
  have hT1 : ∀ᶠ y in atTop, 1 < T y := hTlim.eventually_gt_atTop 1
  have hTinv : ∀ y, (T y)⁻¹ = F y := fun y => inv_inv _
  -- the two Galois facts
  have hUle : ∀ y, 1 < T y → U (T y) ≤ y := fun y hy => (hGal hy y).2 (hTinv y).ge
  have hlt : ∀ y, 1 < T y → ∀ v, 1 < v → y < U (v * T y) := by
    intro y hy v hv
    by_contra hcon
    have h' := (hGal (one_lt_mul_of_lt_of_le hv hy.le) y).1 (not_lt.1 hcon)
    have hTpos : 0 < T y := one_pos.trans hy
    rw [mul_inv, ← hTinv y] at h'
    have : v⁻¹ * (T y)⁻¹ < (T y)⁻¹ :=
      mul_lt_of_lt_one_left (inv_pos.2 hTpos) (inv_lt_one_of_one_lt₀ hv)
    linarith
  set q : ℝ := c ^ (1 / γ) with hq
  have hq0 : 0 < q := rpow_pos_of_pos hc _
  have hqγ : q ^ γ = c := by
    rw [hq, ← rpow_mul hc.le, one_div, inv_mul_cancel₀ hγ.ne', rpow_one]
  have hL : c ^ (-(1 / γ)) = q⁻¹ := by rw [rpow_neg hc.le]
  rw [hL]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b' hb' => ?_⟩
  · rcases le_or_gt a 0 with ha0 | ha0
    · exact Eventually.of_forall fun y => lt_of_le_of_lt ha0 (div_pos (hFpos _) (hFpos _))
    have hai : q < a⁻¹ := by
      rw [lt_inv_comm₀ hq0 ha0]; exact ha
    set v : ℝ := (1 + a⁻¹ / q) / 2 with hv
    have hq1 : 1 < a⁻¹ / q := by rw [one_lt_div hq0]; exact hai
    have hv1 : 1 < v := by rw [hv]; linarith
    have hvq : v * q < a⁻¹ := by
      have : v < a⁻¹ / q := by rw [hv]; linarith
      rwa [lt_div_iff₀ hq0] at this
    have hgap : 0 < (a⁻¹) ^ γ - c * v ^ γ := by
      rw [← hqγ, ← mul_rpow hq0.le (by linarith), sub_pos, mul_comm]
      exact rpow_lt_rpow (by positivity) hvq hγ
    have hlim := (hU.tendsto (inv_pos.2 ha0)).sub
      ((hU.tendsto (by linarith : (0 : ℝ) < v)).const_mul c)
    have hev : ∀ᶠ t in atTop, c * U (v * t) < U (a⁻¹ * t) ∧ 1 < a⁻¹ * t := by
      filter_upwards [hlim.eventually (lt_mem_nhds hgap), hU.eventually_pos,
        (tendsto_id.const_mul_atTop (inv_pos.2 ha0)).eventually_gt_atTop 1] with t h1 h2 h3
      refine ⟨?_, h3⟩
      rw [mul_div_assoc', div_sub_div_same, lt_div_iff₀ h2, zero_mul, sub_pos] at h1
      exact h1
    filter_upwards [hTlim.eventually hev, hT1] with y ⟨h1, h2⟩ hy
    have h3 : c * y < c * U (v * T y) := mul_lt_mul_of_pos_left (hlt y hy v hv1) hc
    have h4 : ¬ U (a⁻¹ * T y) ≤ c * y := by linarith
    rw [hGal h2, mul_inv, inv_inv, hTinv y, not_le] at h4
    rwa [lt_div_iff₀ (hFpos y)]
  · obtain ⟨b, hb, hbb'⟩ := exists_between hb'
    have hb0 : 0 < b := (inv_pos.2 hq0).trans hb
    have hbi : b⁻¹ < q := by rw [inv_lt_comm₀ hb0 hq0]; exact hb
    have hgap : (b⁻¹) ^ γ < c := by
      rw [← hqγ]; exact rpow_lt_rpow (by positivity) hbi hγ
    have hev : ∀ᶠ t in atTop, U (b⁻¹ * t) < c * U t ∧ 1 < b⁻¹ * t := by
      filter_upwards [(hU.tendsto (inv_pos.2 hb0)).eventually (gt_mem_nhds hgap),
        hU.eventually_pos,
        (tendsto_id.const_mul_atTop (inv_pos.2 hb0)).eventually_gt_atTop 1] with t h1 h2 h3
      exact ⟨by rwa [div_lt_iff₀ h2] at h1, h3⟩
    filter_upwards [hTlim.eventually hev, hT1] with y ⟨h1, h2⟩ hy
    have h3 : U (b⁻¹ * T y) ≤ c * y :=
      h1.le.trans (mul_le_mul_of_nonneg_left (hUle y hy) hc.le)
    rw [hGal h2, mul_inv, inv_inv, hTinv y] at h3
    exact lt_of_le_of_lt (by rwa [div_le_iff₀ (hFpos y)]) hbb'

end Inversion

/-! ### Quantile extrapolation under second-order regular variation -/

section Bias

/-- **Second-order quantile extrapolation** ([dHF, §4.3]): if `U` is of
second-order regular variation with `ρ < 0`, `t → ∞` and `d ≥ 1`, then
`U(d t) / (U(t) d^γ) → 1`, uniformly in the extrapolation factor `d`, which may tend to
infinity at any rate. -/
theorem IsSecondOrderRegularlyVarying.tendsto_div_mul_rpow {U A : ℝ → ℝ} {γ ρ : ℝ}
    (h : IsSecondOrderRegularlyVarying U γ ρ A) (hU : Measurable U) (hρ : ρ < 0)
    {ι : Type*} {l : Filter ι} {t d : ι → ℝ} (ht : Tendsto t l atTop)
    (hd : ∀ᶠ i in l, 1 ≤ d i) :
    Tendsto (fun i => U (d i * t i) / (U (t i) * d i ^ γ)) l (𝓝 1) := by
  obtain ⟨A', hA'm, h', -⟩ := h.exists_measurable hU
  obtain ⟨C, t₀, -, hC⟩ := h'.exists_bound_of_neg hU hA'm hρ
  set r : ι → ℝ := fun i => log (U (d i * t i)) - log (U (t i)) - γ * log (d i) with hr
  have hr0 : Tendsto r l (𝓝 0) := by
    have hb : Tendsto (fun i => C * |A' (t i)|) l (𝓝 0) := by
      have := ((h'.tendsto_zero.comp ht).abs).const_mul C
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [ht.eventually_ge_atTop t₀, hd] with i h1 h2
    exact hC (t i) h1 (d i) h2
  have hdt : Tendsto (fun i => d i * t i) l atTop := by
    refine tendsto_atTop_mono' l ?_ ht
    filter_upwards [hd, ht.eventually_ge_atTop 0] with i h1 h2
    exact le_mul_of_one_le_left h2 h1
  have := (continuous_exp.tendsto 0).comp hr0
  rw [exp_zero] at this
  refine this.congr' ?_
  filter_upwards [ht.eventually h.eventually_pos, hdt.eventually h.eventually_pos, hd]
    with i h1 h2 h3
  have h3' : 0 < d i := one_pos.trans_le h3
  simp only [Function.comp_apply, hr]
  rw [exp_sub, exp_sub, exp_log h1, exp_log h2, rpow_def_of_pos h3', mul_comm (log (d i)),
    div_div]

end Bias

section Quantile

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}

/-- The two tail quantile functions agree: `U(t) = x_{1/t}` for `t > 1`. -/
theorem survivalQuantile_survival_eq_tailQuantile {t : ℝ} (ht : 1 < t) :
    survivalQuantile (survival P Y) t = tailQuantile P Y t⁻¹ := by
  simp [survivalQuantile, ht, tailQuantile]

/-- The two tail quantile functions agree: `x_p = U(1/p)` for `0 < p < 1`. -/
theorem tailQuantile_eq_survivalQuantile {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    tailQuantile P Y p = survivalQuantile (survival P Y) p⁻¹ := by
  rw [survivalQuantile_survival_eq_tailQuantile ((one_lt_inv₀ hp0).2 hp1), inv_inv]

end Quantile

/-! ### Consistency of the Weissman estimator -/

section Weissman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Under second-order regular variation of the tail quantile function with `γ > 0`, the
survival function is regularly varying with index `-1/γ`. -/
theorem IsSecondOrderRegularlyVarying.isRegularlyVarying_survival {Y : Ω → ℝ}
    (hY : Measurable Y) {γ ρ : ℝ} {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P Y)) γ ρ A) :
    IsRegularlyVarying (survival P Y) (-(1 / γ)) :=
  isRegularlyVarying_of_isRegularlyVarying_survivalQuantile (survival_anti (P := P) Y)
    (continuousWithinAt_survival (P := P) hY) (tendsto_survival_atTop (P := P) hY)
    (tendsto_survival_atBot (P := P) hY) hγ h2.isRegularlyVarying

/-- **The Hill estimator is `√k`-tight** under the conditions of its central limit theorem:
`√k (H_{k,n} - γ) = O_P(1)`. -/
theorem isBoundedInProbability_hill {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) :
    IsBoundedInProbability P
      (fun n ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - γ)) :=
  isBoundedInProbability_of_tendstoInDistribution
    (tendstoInDistribution_hill hX hindep hident hγ h2 hk hkn hlam HasLaw.id)

/-- **The extrapolation bias of the Weissman estimator vanishes** under second-order regular
variation with `ρ < 0` ([dHF, §4.3]): if `k → ∞`, `k / n → 0` and the
extrapolation factor `d_n = k / (n p_n)` is eventually `≥ 1`, then
`x_{p_n} / (x_{k/n} d_n^γ) → 1`. -/
theorem tendsto_tailQuantile_div_of_secondOrder {Y : Ω → ℝ} (hY : Measurable Y) {γ ρ : ℝ}
    {A : ℝ → ℝ} (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P Y)) γ ρ A)
    (hρ : ρ < 0) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) {p : ℕ → ℝ}
    (hp0 : ∀ᶠ n in atTop, 0 < p n) (hd : ∀ᶠ n in atTop, 1 ≤ (k n : ℝ) / (n * p n)) :
    Tendsto (fun n => tailQuantile P Y (p n) /
      (tailQuantile P Y ((k n : ℝ) / n) * ((k n : ℝ) / (n * p n)) ^ γ)) atTop (𝓝 1) := by
  have hUm := measurable_tailQuantile (survival_anti (P := P) Y)
    (continuousWithinAt_survival (P := P) hY) (tendsto_survival_atTop (P := P) hY)
    (tendsto_survival_atBot (P := P) hY)
  have h := h2.tendsto_div_mul_rpow hUm hρ (tendsto_div_atTop_of_tendsto hk hkn) hd
  refine h.congr' ?_
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  filter_upwards [hkR.eventually_gt_atTop 0,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0,
    hkn.eventually (gt_mem_nhds one_pos), hp0, hd] with n hk0 hn0 hkn1 hpn hdn
  have hr0 : 0 < (k n : ℝ) / n := div_pos hk0 hn0
  have hpk : p n ≤ (k n : ℝ) / n := by
    rw [le_div_iff₀ (mul_pos hn0 hpn)] at hdn
    rw [le_div_iff₀ hn0]
    linarith
  have hp1 : p n < 1 := hpk.trans_lt hkn1
  rw [tailQuantile_eq_survivalQuantile hpn hp1, tailQuantile_eq_survivalQuantile hr0 hkn1]
  congr 3
  · field_simp
  · rw [inv_div]

/-- **Consistency of the Weissman estimator for extreme quantiles** ([dHF, §4.3],
consistency part; Weissman 1978). Let `X_0, X_1, …` be iid with tail quantile function
`U(t) = F̄^←(1/t)` of second-order regular variation with `γ > 0`, `ρ < 0` and auxiliary function
`A`. If `k → ∞`, `k / n → 0`, `√k A(n/k) → λ` (finite), and the extrapolation factor
`d_n = k / (n p_n)` satisfies `d_n ≥ 1` eventually and `log d_n / √k → 0`, then

  `x̂_{p_n} / x_{p_n} → 1` in probability,

where `x̂_p = X_{(k+1)} d_n^{γ̂}` is the Weissman estimator. This covers quantiles far beyond the
sample range, e.g. `n p_n → c ∈ [0, ∞)` with `log n = o(√k)`. -/
theorem tendstoInMeasure_weissman_div_of_secondOrder {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ} {A : ℝ → ℝ} (hγ : 0 < γ)
    (hρ : ρ < 0)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {p : ℕ → ℝ}
    (hp0 : ∀ᶠ n in atTop, 0 < p n) (hd1 : ∀ᶠ n in atTop, 1 ≤ (k n : ℝ) / (n * p n))
    (hd : Tendsto (fun n => Real.log ((k n : ℝ) / (n * p n)) / √(k n : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => weissman (fun i : Fin n => X i ω) (k n) (p n) /
      tailQuantile P (X 0) (p n)) atTop (fun _ => 1) := by
  have hα : 0 < 1 / γ := one_div_pos.2 hγ
  have hRV := h2.isRegularlyVarying_survival (hX 0) hγ
  have hrate := isBoundedInProbability_hill hX hindep hident hγ h2 hk hkn hlam
  have hbias := tendsto_tailQuantile_div_of_secondOrder (hX 0) h2 hρ hk hkn hp0 hd1
  rw [← one_div_one_div γ] at hrate hbias
  exact tendstoInMeasure_weissman_div_of_isBoundedInProbability hX hindep hident hα hRV hk hkn
    hp0 hrate hd hbias

end Weissman

/-! ### Consistency of the tail probability estimator -/

section TailProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The extrapolation bias of the tail probability estimator, reduction form**: under
second-order regular variation with `γ > 0`, if `k → ∞`, `k / n → 0`, the levels `y_n` are
eventually beyond the intermediate quantile, `x_{k/n} ≤ y_n`, and the quantile extrapolation
`U(D_n n/k) / (U(n/k) D_n^γ) → 1` holds along the factors `D_n ≥ 1` with
`D_n n/k = 1 / F̄(y_n)`, then `(k / n) (y_n / x_{k/n})^{-1/γ} / F̄(y_n) → 1`. -/
theorem tendsto_tailProb_div_of_extrapolation {Y : Ω → ℝ} (hY : Measurable Y) {γ ρ : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P Y)) γ ρ A)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) {y : ℕ → ℝ}
    (hy : ∀ᶠ n in atTop, tailQuantile P Y ((k n : ℝ) / n) ≤ y n)
    (hext : ∀ D : ℕ → ℝ, (∀ᶠ n in atTop, 1 ≤ D n) →
      (∀ᶠ n in atTop, D n * ((n : ℝ) / k n) = (survival P Y (y n))⁻¹) →
      Tendsto (fun n => survivalQuantile (survival P Y) (D n * ((n : ℝ) / k n)) /
        (survivalQuantile (survival P Y) ((n : ℝ) / k n) * D n ^ γ)) atTop (𝓝 1)) :
    Tendsto (fun n => (k n : ℝ) / n * (y n / tailQuantile P Y ((k n : ℝ) / n)) ^ (-(1 / γ)) /
      survival P Y (y n)) atTop (𝓝 1) := by
  set F := survival P Y with hFdef
  set U := survivalQuantile F with hUdef
  have hF := survival_anti (P := P) Y
  have hrc := continuousWithinAt_survival (P := P) hY
  have hF0 := tendsto_survival_atTop (P := P) hY
  have hF1 := tendsto_survival_atBot (P := P) hY
  have hGal : ∀ {t : ℝ}, 1 < t → ∀ x, U t ≤ x ↔ F x ≤ t⁻¹ := fun ht x =>
    tailQuantile_le_iff hF hrc hF0 hF1 ht x
  have hUm := measurable_tailQuantile hF hrc hF0 hF1
  have hRV := h2.isRegularlyVarying_survival hY hγ
  have hFpos : ∀ z, 0 < F z := survival_pos hRV
  have hU1 := h2.isRegularlyVarying
  set s : ℕ → ℝ := fun n => (n : ℝ) / k n with hs
  have hslim : Tendsto s atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  set τ : ℕ → ℝ := fun n => (F (y n))⁻¹ with hτ
  set D : ℕ → ℝ := fun n => τ n / s n with hD
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  -- eventually: `x_{k/n} = U(s_n)`, `s_n ≤ τ_n`, hence `D_n ≥ 1`
  have hev : ∀ᶠ n in atTop, 1 < s n ∧ tailQuantile P Y ((k n : ℝ) / n) = U (s n) ∧
      s n ≤ τ n ∧ 0 < U (s n) := by
    filter_upwards [hkR.eventually_gt_atTop 0,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0,
      hkn.eventually (gt_mem_nhds one_pos), hy, hslim.eventually_gt_atTop 1,
      hslim.eventually h2.eventually_pos] with n hk0 hn0 hkn1 hyn hs1 hUs
    have hq : tailQuantile P Y ((k n : ℝ) / n) = U (s n) := by
      rw [tailQuantile_eq_survivalQuantile (div_pos hk0 hn0) hkn1, inv_div]
    refine ⟨hs1, hq, ?_, hUs⟩
    rw [hq] at hyn
    have := (hGal hs1 (y n)).1 hyn
    have hs0 : 0 < s n := one_pos.trans hs1
    rw [hτ]
    exact (le_inv_comm₀ (hFpos _) hs0).1 this
  have hτlim : Tendsto τ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hslim
    filter_upwards [hev] with n hn
    exact hn.2.2.1
  have hD1 : ∀ᶠ n in atTop, 1 ≤ D n := by
    filter_upwards [hev] with n hn
    rw [hD, le_div_iff₀ (one_pos.trans hn.1), one_mul]
    exact hn.2.2.1
  -- the bias of the quantile extrapolation
  have hb : Tendsto (fun n => U (D n * s n) / (U (s n) * D n ^ γ)) atTop (𝓝 1) := by
    refine hext D hD1 ?_
    filter_upwards [hev] with n hn
    exact div_mul_cancel₀ _ (one_pos.trans hn.1).ne'
  -- `y_n / U(τ_n) → 1`
  have hyU : Tendsto (fun n => y n / U (τ n)) atTop (𝓝 1) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb1 => ?_⟩
    · filter_upwards [hτlim.eventually_gt_atTop 1, hτlim.eventually h2.eventually_pos]
        with n h1 h3
      refine ha.trans_le ?_
      rw [one_le_div h3]
      exact (hGal h1 (y n)).2 (by rw [hτ, inv_inv])
    · set v : ℝ := b ^ (1 / (2 * γ)) with hv
      have hv1 : 1 < v := one_lt_rpow hb1 (by positivity)
      have hvγ : v ^ γ < b := by
        rw [hv, ← rpow_mul (by linarith), show 1 / (2 * γ) * γ = 1 / 2 by field_simp]
        exact rpow_lt_self_of_one_lt hb1 (by norm_num)
      filter_upwards [hτlim.eventually_gt_atTop 1, hτlim.eventually h2.eventually_pos,
        hτlim.eventually ((hU1.tendsto (one_pos.trans hv1)).eventually (gt_mem_nhds hvγ))]
        with n h1 h3 h4
      refine lt_of_le_of_lt ?_ h4
      refine div_le_div_of_nonneg_right ?_ h3.le
      by_contra hcon
      have h5 := (hGal (one_lt_mul_of_lt_of_le hv1 h1.le) (y n)).1 (not_le.1 hcon).le
      have hτ0 : 0 < τ n := one_pos.trans h1
      rw [mul_inv] at h5
      have : v⁻¹ * (τ n)⁻¹ < (τ n)⁻¹ :=
        mul_lt_of_lt_one_left (inv_pos.2 hτ0) (inv_lt_one_of_one_lt₀ hv1)
      rw [hτ, inv_inv] at this h5
      linarith
  have hW := ((hb.inv₀ one_ne_zero).mul (hyU.inv₀ one_ne_zero))
  rw [inv_one, mul_one] at hW
  have hcont : Tendsto (fun w : ℝ => w ^ (1 / γ)) (𝓝 1) (𝓝 1) := by
    have := Real.continuousAt_rpow_const 1 (1 / γ) (Or.inl one_ne_zero)
    simpa using this.tendsto
  refine (hcont.comp hW).congr' ?_
  filter_upwards [hev, hτlim.eventually h2.eventually_pos] with n ⟨hs1, hq, hsτ, hUs⟩ hUτ
  have hs0 : 0 < s n := one_pos.trans hs1
  have hτ0 : 0 < τ n := hs0.trans_le hsτ
  have hD0 : 0 < D n := div_pos hτ0 hs0
  have hDs : D n * s n = τ n := div_mul_cancel₀ _ hs0.ne'
  have hyn : 0 < y n := by
    have : U (τ n) ≤ y n := (hGal (hs1.trans_le hsτ) (y n)).2 (by rw [hτ, inv_inv])
    linarith
  have hkn' : (k n : ℝ) / n = (s n)⁻¹ := by rw [hs, inv_div]
  have hFy : F (y n) = (τ n)⁻¹ := by rw [hτ, inv_inv]
  simp only [Function.comp_apply]
  rw [hq, hkn', hFy, hDs]
  have e1 : ((U (τ n) / (U (s n) * D n ^ γ))⁻¹ * (y n / U (τ n))⁻¹) =
      D n ^ γ * (y n / U (s n))⁻¹ := by
    field_simp
  rw [e1, mul_rpow (rpow_pos_of_pos hD0 _).le (inv_nonneg.2 (div_pos hyn hUs).le),
    ← rpow_mul hD0.le, mul_one_div_cancel hγ.ne', rpow_one, inv_rpow (div_pos hyn hUs).le,
    ← rpow_neg (div_pos hyn hUs).le, show (s n)⁻¹ * (y n / U (s n)) ^ (-(1 / γ)) / (τ n)⁻¹ =
      τ n / s n * (y n / U (s n)) ^ (-(1 / γ)) by field_simp]

/-- **The extrapolation bias of the tail probability estimator vanishes** under second-order
regular variation with `γ > 0`, `ρ < 0` ([dHF, §4.4]): if `k → ∞`,
`k / n → 0` and the levels `y_n` are eventually beyond the intermediate quantile,
`x_{k/n} ≤ y_n`, then `(k / n) (y_n / x_{k/n})^{-1/γ} / F̄(y_n) → 1`. -/
theorem tendsto_tailProb_div_of_secondOrder {Y : Ω → ℝ} (hY : Measurable Y) {γ ρ : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P Y)) γ ρ A)
    (hρ : ρ < 0) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) {y : ℕ → ℝ}
    (hy : ∀ᶠ n in atTop, tailQuantile P Y ((k n : ℝ) / n) ≤ y n) :
    Tendsto (fun n => (k n : ℝ) / n * (y n / tailQuantile P Y ((k n : ℝ) / n)) ^ (-(1 / γ)) /
      survival P Y (y n)) atTop (𝓝 1) := by
  have hUm := measurable_tailQuantile (survival_anti (P := P) Y)
    (continuousWithinAt_survival (P := P) hY) (tendsto_survival_atTop (P := P) hY)
    (tendsto_survival_atBot (P := P) hY)
  exact tendsto_tailProb_div_of_extrapolation hY hγ h2 hk hkn hy fun D hD1 _ =>
    h2.tendsto_div_mul_rpow hUm hρ (tendsto_div_atTop_of_tendsto hk hkn) hD1

/-- **Consistency of the tail probability estimator far in the tail** ([dHF, §4.4],
consistency part). Let `X_0, X_1, …` be iid with tail quantile function of second-order regular
variation with `γ > 0`, `ρ < 0` and auxiliary function `A`. If `k → ∞`, `k / n → 0`,
`√k A(n/k) → λ`, and the levels `y_n` satisfy `x_{k/n} ≤ y_n` eventually and
`log (y_n / x_{k/n}) / √k → 0`, then `p̂(y_n) / P(X > y_n) → 1` in probability. -/
theorem tendstoInMeasure_tailProbEstimator_div_of_secondOrder {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ} {A : ℝ → ℝ} (hγ : 0 < γ)
    (hρ : ρ < 0)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {y : ℕ → ℝ}
    (hy : ∀ᶠ n in atTop, tailQuantile P (X 0) ((k n : ℝ) / n) ≤ y n)
    (he : Tendsto (fun n => Real.log (y n / tailQuantile P (X 0) ((k n : ℝ) / n)) /
      √(k n : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => tailProbEstimator (fun i : Fin n => X i ω) (k n) (y n) /
      (P {ω | y n < X 0 ω}).toReal) atTop (fun _ => 1) := by
  have hα : 0 < 1 / γ := one_div_pos.2 hγ
  have hRV := h2.isRegularlyVarying_survival (hX 0) hγ
  have hrate := isBoundedInProbability_hill hX hindep hident hγ h2 hk hkn hlam
  have hbias := tendsto_tailProb_div_of_secondOrder (hX 0) hγ h2 hρ hk hkn hy
  rw [← one_div_one_div γ] at hrate
  have hy0 : ∀ᶠ n in atTop, 0 < y n := by
    filter_upwards [hy, (tendsto_div_atTop_of_tendsto hk hkn).eventually h2.eventually_pos,
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hk).eventually_gt_atTop 0,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0,
      hkn.eventually (gt_mem_nhds one_pos)] with n h1 h3 hk0 hn0 hkn1
    have hk0' : (0 : ℝ) < k n := hk0
    rw [tailQuantile_eq_survivalQuantile (div_pos hk0' hn0) hkn1, inv_div] at h1
    exact h3.trans_le h1
  exact tendstoInMeasure_tailProbEstimator_div_of_isBoundedInProbability hX hindep hident hα hRV
    hk hkn hy0 hrate he hbias

end TailProbability

/-! ### The `√k`-rate of the intermediate exponential order statistic -/

section ExpOrderStat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Chebyshev's inequality for exceedance counts**: with `q = P(X_0 > a)`,
`P(c ≤ |#{i < n | X_i > a} - n q|) ≤ n q / c²`. -/
theorem measure_le_abs_exceedCount_sub_le {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) (a : ℝ)
    {c : ℝ} (hc : 0 < c) :
    P {ω | c ≤ |(exceedCount (fun i : Fin n => X i ω) a : ℝ) - n * (P {ω | a < X 0 ω}).toReal|}
      ≤ ENNReal.ofReal (n * (P {ω | a < X 0 ω}).toReal / c ^ 2) := by
  set g : ℝ → ℝ := fun x => if a < x then (1 : ℝ) else 0 with hg
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const
  set Y : ℕ → Ω → ℝ := fun i ω => g (X i ω) with hY
  have hYId : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i => by
    have := (hident i).comp hgm
    simpa [hY, Function.comp_def] using this
  have hL2 : MemLp (Y 0) 2 P := by
    refine MemLp.of_bound (hgm.comp (hX 0)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    simp only [hY, hg]
    split_ifs <;> norm_num
  have hYL2 : ∀ i, MemLp (Y i) 2 P := fun i => (hYId i).memLp_iff.2 hL2
  have hYind : ∀ i j, i ≠ j → IndepFun (Y i) (Y j) P := fun i j hij =>
    (hindep.indepFun hij).comp hgm hgm
  have hint : P[Y 0] = (P {ω | a < X 0 ω}).toReal := by
    have : Y 0 = {ω | a < X 0 ω}.indicator 1 := by
      ext ω; simp [hY, hg, Set.indicator]
    rw [this, integral_indicator_one (measurableSet_lt measurable_const (hX 0)), measureReal_def]
  have hsq : P[Y 0 ^ 2] = (P {ω | a < X 0 ω}).toReal := by
    rw [← hint]
    congr 1
    ext ω
    simp only [Pi.pow_apply, hY, hg]
    split_ifs <;> norm_num
  set T : Ω → ℝ := ∑ i ∈ Finset.range n, Y i with hT
  have hTfun : ∀ ω, T ω = exceedCount (fun i : Fin n => X i ω) a := by
    intro ω
    rw [exceedCount_eq_sum]
    simp only [hT, Finset.sum_apply, hY, hg]
    exact (Fin.sum_univ_eq_sum_range (fun i => if a < X i ω then (1 : ℝ) else 0) n).symm
  have hTL2 : MemLp T 2 P := memLp_finsetSum' _ fun i _ => hYL2 i
  have hET : P[T] = n * (P {ω | a < X 0 ω}).toReal := by
    have : ∫ ω, T ω ∂P = ∑ i ∈ Finset.range n, ∫ ω, Y i ω ∂P := by
      simp only [hT, Finset.sum_apply]
      exact integral_finsetSum _ fun i _ => (hYL2 i).integrable one_le_two
    rw [this, Finset.sum_congr rfl fun i _ => (hYId i).integral_eq, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, hint]
  have hVT : variance T P ≤ n * (P {ω | a < X 0 ω}).toReal := by
    rw [hT, IndepFun.variance_sum (fun i _ => hYL2 i) (fun i _ j _ hij => hYind i j hij)]
    rw [Finset.sum_congr rfl fun i _ => (hYId i).variance_eq, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← hsq]
    gcongr
    exact variance_le_expectation_sq hL2.aestronglyMeasurable
  have hsub : {ω | c ≤ |(exceedCount (fun i : Fin n => X i ω) a : ℝ) -
      n * (P {ω | a < X 0 ω}).toReal|} = {ω | c ≤ |T ω - P[T]|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [hET, hTfun]
  rw [hsub]
  refine (meas_ge_le_variance_div_sq hTL2 hc).trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

/-- **The intermediate exponential order statistic at rate `√k`**: if the `E_i` are iid standard
exponential, `k → ∞` and `k / n → 0`, then `√k (E_{(k+1)} - log(n/k))` is bounded in
probability. -/
theorem isBoundedInProbability_orderStat_sub_log {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    IsBoundedInProbability P (fun n ω =>
      √(k n : ℝ) * (orderStat (fun i : Fin n => E i ω) (k n) - log (n / k n))) := by
  have hident : ∀ i, IdentDistrib (E i) (E 0) P P := fun i =>
    ⟨(hE i).aemeasurable, (hE 0).aemeasurable, by rw [(hE i).map_eq, (hE 0).map_eq]⟩
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, htop ▸ le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' htop, ENNReal.ofReal_toReal_le⟩
  set M : ℝ := 7 / η + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; linarith [div_pos (by norm_num : (0 : ℝ) < 7) hη0]
  have hM0 : 0 < M := one_pos.trans_le hM1
  have hM2 : 7 / M ^ 2 ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    have : 7 / η < M := by rw [hM]; linarith
    rw [div_lt_iff₀ hη0] at this
    nlinarith
  refine ⟨M, ?_⟩
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hnk := tendsto_div_atTop_of_tendsto hk hkn
  filter_upwards [hkR.eventually_ge_atTop (M ^ 2), eventually_lt_of_tendsto_div hkn,
    (tendsto_log_atTop.comp hnk).eventually_ge_atTop 1, hkR.eventually_gt_atTop 0]
    with n hkM hkn' hlog hk0
  simp only [Function.comp_apply] at hlog
  set s₀ := log (n / k n) with hs₀
  have hsk : 0 < √(k n : ℝ) := sqrt_pos.2 hk0
  set x := M / √(k n : ℝ) with hx
  have hx0 : 0 < x := div_pos hM0 hsk
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hsk]
    calc M = √(M ^ 2) := (sqrt_sq hM0.le).symm
      _ ≤ √(k n : ℝ) := sqrt_le_sqrt hkM
  have hkx : (k n : ℝ) * x ^ 2 = M ^ 2 := by
    rw [hx, div_pow, sq_sqrt hk0.le]; field_simp
  have hn0 : (0 : ℝ) < n := by
    have : (k n : ℝ) < n := by exact_mod_cast hkn'
    linarith
  have hexp_s₀ : exp (-s₀) = k n / n := by
    rw [hs₀, exp_neg, exp_log (div_pos hn0 hk0), inv_div]
  -- the two thresholds and their exceedance probabilities
  set a₁ := s₀ + x with ha₁
  set a₂ := s₀ - x with ha₂
  have hq₁ : (P {ω | a₁ < E 0 ω}).toReal = k n / n * exp (-x) := by
    rw [measure_lt_expMeasure_of_hasLaw (hE 0) (by rw [ha₁]; linarith),
      ENNReal.toReal_ofReal (exp_pos _).le, ha₁, neg_add, exp_add, hexp_s₀]
  have hq₂ : (P {ω | a₂ < E 0 ω}).toReal = k n / n * exp x := by
    rw [measure_lt_expMeasure_of_hasLaw (hE 0) (by rw [ha₂]; linarith),
      ENNReal.toReal_ofReal (exp_pos _).le, ha₂, neg_sub, sub_eq_add_neg, exp_add, hexp_s₀,
      mul_comm]
  set c₁ := (k n : ℝ) * (1 - exp (-x)) with hc₁
  set c₂ := (k n : ℝ) * (exp x - 1) with hc₂
  have he1 : x / 2 ≤ 1 - exp (-x) := by
    have h1 : 1 + x ≤ exp x := by linarith [add_one_le_exp x]
    have h2 : exp (-x) ≤ 1 / (1 + x) := by
      rw [exp_neg, one_div]; exact inv_anti₀ (by linarith) h1
    have h3 : 1 / (1 + x) ≤ 1 - x / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have he2 : x ≤ exp x - 1 := by linarith [add_one_le_exp x]
  have hc₁0 : 0 < c₁ := mul_pos hk0 (by linarith)
  have hc₂0 : 0 < c₂ := mul_pos hk0 (by linarith)
  have hb₁ := measure_le_abs_exceedCount_sub_le hEm hind hident n a₁ hc₁0
  have hb₂ := measure_le_abs_exceedCount_sub_le hEm hind hident n a₂ hc₂0
  rw [hq₁] at hb₁
  rw [hq₂] at hb₂
  have hnq : ∀ y, (n : ℝ) * (k n / n * y) = k n * y := fun y => by field_simp
  rw [hnq] at hb₁ hb₂
  -- the event inclusion
  refine (measure_mono (t := {ω | c₁ ≤ |(exceedCount (fun i : Fin n => E i ω) a₁ : ℝ) -
      k n * exp (-x)|} ∪ {ω | c₂ ≤ |(exceedCount (fun i : Fin n => E i ω) a₂ : ℝ) -
      k n * exp x|}) ?_).trans ((measure_union_le _ _).trans ?_)
  · intro ω hω
    simp only [mem_ofPred_eq] at hω
    set z := fun i : Fin n => E i ω with hz
    rw [abs_mul, abs_of_pos hsk, ← div_lt_iff₀' hsk, ← hx] at hω
    rcases lt_abs.1 hω with h | h
    · left
      have hlt : a₁ < orderStat z (k n) := by rw [ha₁]; linarith
      rw [lt_orderStat_iff z hkn'] at hlt
      have hN : (k n : ℝ) + 1 ≤ exceedCount z a₁ := by exact_mod_cast hlt
      simp only [mem_ofPred_eq]
      refine le_trans ?_ (le_abs_self _)
      rw [hc₁]
      linarith
    · right
      have hle : orderStat z (k n) ≤ a₂ := by rw [ha₂]; linarith
      rw [orderStat_le_iff z hkn'] at hle
      have hN : (exceedCount z a₂ : ℝ) ≤ k n := by exact_mod_cast hle
      simp only [mem_ofPred_eq]
      refine le_trans ?_ (neg_le_abs _)
      rw [hc₂]
      linarith
  · refine (add_le_add hb₁ hb₂).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine (ENNReal.ofReal_le_ofReal ?_).trans hηε
    refine le_trans ?_ hM2
    have hex1 : exp (-x) ≤ 1 := exp_le_one_iff.2 (by linarith)
    have hex2 : exp x ≤ 3 := by
      have := exp_le_exp.2 hx1
      linarith [exp_one_lt_d9]
    have hk2 : (k n : ℝ) * x ^ 2 > 0 := by positivity
    have t1 : (k n : ℝ) * exp (-x) / c₁ ^ 2 ≤ 4 / M ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), ← hkx, hc₁]
      have : (k n : ℝ) * (x / 2) ≤ k n * (1 - exp (-x)) := by gcongr
      have h0 : 0 ≤ (k n : ℝ) * (x / 2) := by positivity
      have := mul_le_mul this this h0 (by linarith)
      nlinarith
    have t2 : (k n : ℝ) * exp x / c₂ ^ 2 ≤ 3 / M ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), ← hkx, hc₂]
      have : (k n : ℝ) * x ≤ k n * (exp x - 1) := by gcongr
      have h0 : 0 ≤ (k n : ℝ) * x := by positivity
      have := mul_le_mul this this h0 (by nlinarith)
      nlinarith
    calc _ ≤ 4 / M ^ 2 + 3 / M ^ 2 := add_le_add t1 t2
      _ = 7 / M ^ 2 := by ring

end ExpOrderStat

/-! ### The `√k`-rate of the intermediate order statistic -/

/-- **Two-sided uniform bound for second-order regular variation with `ρ < 0`**: there are `C`
and `t₀ > 0` with `|log U(xt) - log U(t) - γ log x| ≤ C |A(t)|` for `t ≥ t₀`, `x ≥ e⁻¹`. -/
theorem IsSecondOrderRegularlyVarying.exists_bound_of_neg' {U A : ℝ → ℝ} {γ ρ : ℝ}
    (h : IsSecondOrderRegularlyVarying U γ ρ A) (hU : Measurable U) (hA : Measurable A)
    (hρ : ρ < 0) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t ≥ t₀, ∀ x ≥ exp (-1),
      |log (U (x * t)) - log (U t) - γ * log x| ≤ C * |A t| := by
  obtain ⟨C₁, t₁, ht₁, hC₁⟩ := h.exists_bound_of_neg hU hA hρ
  obtain ⟨x₀, hx₀, hApos, hP⟩ :=
    h.isRegularlyVarying_abs.potter_bound_of_measurable (continuous_abs.measurable.comp hA)
      one_pos one_lt_two
  set K : ℝ := 2 * exp (|ρ| + 1) with hK
  refine ⟨|C₁| * (1 + K), exp 1 * max t₁ x₀, by positivity, fun t ht x hx => ?_⟩
  have hm0 : 0 < max t₁ x₀ := lt_max_of_lt_left ht₁
  have ht0 : 0 < t := (by positivity : (0 : ℝ) < exp 1 * max t₁ x₀).trans_le ht
  have htm : max t₁ x₀ ≤ t := le_trans (le_mul_of_one_le_left hm0.le (one_le_exp one_pos.le)) ht
  have hK1 : 0 ≤ K := by positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · refine (hC₁ t ((le_max_left _ _).trans htm) x hx1).trans ?_
    have : C₁ ≤ |C₁| * (1 + K) := (le_abs_self C₁).trans (le_mul_of_one_le_right (abs_nonneg _)
      (by linarith))
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  · have hx0 : 0 < x := (exp_pos _).trans_le hx
    have hxt : max t₁ x₀ ≤ x * t := by
      have : exp (-1) * (exp 1 * max t₁ x₀) ≤ x * t :=
        mul_le_mul hx ht (by positivity) hx0.le
      rwa [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul] at this
    have h1 := hC₁ (x * t) ((le_max_left _ _).trans hxt) x⁻¹ (one_le_inv₀ hx0 |>.2 hx1.le)
    rw [← mul_assoc, inv_mul_cancel₀ hx0.ne', one_mul, log_inv] at h1
    -- Potter: `|A(xt)| ≤ K |A(t)|`
    have hpot := hP t ((le_max_right _ _).trans htm) (x * t) ((le_max_right _ _).trans hxt)
    rw [mul_div_cancel_right₀ _ ht0.ne', div_le_iff₀ (hApos t ((le_max_right _ _).trans htm))]
      at hpot
    have hlogx1 : -1 ≤ log x := by
      rw [← log_exp (-1)]; exact log_le_log (exp_pos _) hx
    have hlogx : -1 ≤ log x ∧ log x ≤ 0 := ⟨hlogx1, log_nonpos hx0.le hx1.le⟩
    have hb : ∀ r : ℝ, |r| ≤ |ρ| + 1 → x ^ r ≤ exp (|ρ| + 1) := by
      intro r hr'
      rw [rpow_def_of_pos hx0]
      refine exp_le_exp.2 ?_
      have : |log x * r| ≤ |ρ| + 1 := by
        rw [abs_mul]
        have : |log x| ≤ 1 := abs_le.2 ⟨hlogx.1, by linarith [hlogx.2]⟩
        calc |log x| * |r| ≤ 1 * (|ρ| + 1) := mul_le_mul this hr' (abs_nonneg _) zero_le_one
          _ = |ρ| + 1 := one_mul _
      exact (le_abs_self _).trans this
    have hmax : max (x ^ (ρ + 1)) (x ^ (ρ - 1)) ≤ exp (|ρ| + 1) :=
      max_le (hb _ ((abs_add_le _ _).trans (by simp))) (hb _ ((abs_sub _ _).trans (by simp)))
    have hAxt : |A (x * t)| ≤ K * |A t| := by
      calc |A (x * t)| ≤ 2 * max (x ^ (ρ + 1)) (x ^ (ρ - 1)) * |A t| := hpot
        _ ≤ 2 * exp (|ρ| + 1) * |A t| := by gcongr
    have e : log (U (x * t)) - log (U t) - γ * log x =
        -(log (U t) - log (U (x * t)) - γ * -log x) := by ring
    rw [e, abs_neg]
    calc _ ≤ C₁ * |A (x * t)| := h1
      _ ≤ |C₁| * |A (x * t)| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      _ ≤ |C₁| * (K * |A t|) := mul_le_mul_of_nonneg_left hAxt (abs_nonneg _)
      _ = |C₁| * K * |A t| := by ring
      _ ≤ |C₁| * (1 + K) * |A t| := by gcongr; linarith

/-- **Local two-sided uniform bound for second-order regular variation** (any `ρ ≤ 0`): there are
`C` and `t₀ > 0` with `|log U(xt) - log U(t) - γ log x| ≤ C |A(t)|` for `t ≥ t₀` and
`x ∈ [e⁻¹, e]`. -/
theorem IsSecondOrderRegularlyVarying.exists_bound_Icc {U A : ℝ → ℝ} {γ ρ : ℝ}
    (h : IsSecondOrderRegularlyVarying U γ ρ A) (hU : Measurable U) (hA : Measurable A) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t ≥ t₀, ∀ x ∈ Icc (exp (-1)) (exp 1),
      |log (U (x * t)) - log (U t) - γ * log x| ≤ C * |A t| := by
  obtain ⟨C₁, t₁, ht₁, hC₁⟩ := h.exists_bound hU hA one_pos
  obtain ⟨x₀, hx₀, hApos, hP⟩ :=
    h.isRegularlyVarying_abs.potter_bound_of_measurable (continuous_abs.measurable.comp hA)
      one_pos one_lt_two
  set K : ℝ := 2 * exp (|ρ| + 1) with hK
  refine ⟨|C₁| * exp 1 * (1 + K), exp 1 * max t₁ x₀, by positivity, fun t ht x hx => ?_⟩
  have hm0 : 0 < max t₁ x₀ := lt_max_of_lt_left ht₁
  have ht0 : 0 < t := (by positivity : (0 : ℝ) < exp 1 * max t₁ x₀).trans_le ht
  have htm : max t₁ x₀ ≤ t := le_trans (le_mul_of_one_le_left hm0.le (one_le_exp one_pos.le)) ht
  have hK1 : 0 ≤ K := by positivity
  have hx0 : 0 < x := (exp_pos _).trans_le hx.1
  rcases le_or_gt 1 x with hx1 | hx1
  · refine (hC₁ t ((le_max_left _ _).trans htm) x hx1).trans ?_
    rw [rpow_one]
    calc C₁ * |A t| * x ≤ |C₁| * |A t| * exp 1 := by
          gcongr
          · exact le_abs_self _
          · exact hx.2
      _ = |C₁| * exp 1 * 1 * |A t| := by ring
      _ ≤ |C₁| * exp 1 * (1 + K) * |A t| := by gcongr; linarith
  · have hxt : max t₁ x₀ ≤ x * t := by
      have : exp (-1) * (exp 1 * max t₁ x₀) ≤ x * t :=
        mul_le_mul hx.1 ht (by positivity) hx0.le
      rwa [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul] at this
    have h1 := hC₁ (x * t) ((le_max_left _ _).trans hxt) x⁻¹ (one_le_inv₀ hx0 |>.2 hx1.le)
    rw [← mul_assoc, inv_mul_cancel₀ hx0.ne', one_mul, log_inv, rpow_one] at h1
    have hxinv : x⁻¹ ≤ exp 1 := by
      rw [inv_le_comm₀ hx0 (exp_pos _), ← exp_neg]; exact hx.1
    -- Potter: `|A(xt)| ≤ K |A(t)|`
    have hpot := hP t ((le_max_right _ _).trans htm) (x * t) ((le_max_right _ _).trans hxt)
    rw [mul_div_cancel_right₀ _ ht0.ne', div_le_iff₀ (hApos t ((le_max_right _ _).trans htm))]
      at hpot
    have hlogx1 : -1 ≤ log x := by
      rw [← log_exp (-1)]; exact log_le_log (exp_pos _) hx.1
    have hlogx : -1 ≤ log x ∧ log x ≤ 0 := ⟨hlogx1, log_nonpos hx0.le hx1.le⟩
    have hb : ∀ r : ℝ, |r| ≤ |ρ| + 1 → x ^ r ≤ exp (|ρ| + 1) := by
      intro r hr'
      rw [rpow_def_of_pos hx0]
      refine exp_le_exp.2 ?_
      have : |log x * r| ≤ |ρ| + 1 := by
        rw [abs_mul]
        have : |log x| ≤ 1 := abs_le.2 ⟨hlogx.1, by linarith [hlogx.2]⟩
        calc |log x| * |r| ≤ 1 * (|ρ| + 1) := mul_le_mul this hr' (abs_nonneg _) zero_le_one
          _ = |ρ| + 1 := one_mul _
      exact (le_abs_self _).trans this
    have hmax : max (x ^ (ρ + 1)) (x ^ (ρ - 1)) ≤ exp (|ρ| + 1) :=
      max_le (hb _ ((abs_add_le _ _).trans (by simp))) (hb _ ((abs_sub _ _).trans (by simp)))
    have hAxt : |A (x * t)| ≤ K * |A t| := by
      calc |A (x * t)| ≤ 2 * max (x ^ (ρ + 1)) (x ^ (ρ - 1)) * |A t| := hpot
        _ ≤ 2 * exp (|ρ| + 1) * |A t| := by gcongr
    have e : log (U (x * t)) - log (U t) - γ * log x =
        -(log (U t) - log (U (x * t)) - γ * -log x) := by ring
    rw [e, abs_neg]
    calc _ ≤ C₁ * |A (x * t)| * x⁻¹ := h1
      _ ≤ |C₁| * (K * |A t|) * exp 1 := by
          gcongr
          exact le_abs_self _
      _ = |C₁| * exp 1 * K * |A t| := by ring
      _ ≤ |C₁| * exp 1 * (1 + K) * |A t| := by gcongr; linarith

section IntermediateOrderStat

variable {Ω Ω₀ : Type*} {mΩ : MeasurableSpace Ω} {mΩ₀ : MeasurableSpace Ω₀}
  {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

/-- **The intermediate order statistic at rate `√k`, on the exponential scale**: if the `E_i`
are iid standard exponential and `U` is monotone on `(1, ∞)` and of second-order regular
variation (any `ρ ≤ 0`), `k → ∞`, `k / n → 0` and `√k A(n/k) → λ`, then
`√k (log U(e^{E})_{(k+1)} - log U(n/k))` is bounded in probability. -/
theorem isBoundedInProbability_log_orderStat_comp_exp {E : ℕ → Ω₀ → ℝ}
    (hEm : ∀ i, Measurable (E i)) (hE : ∀ i, HasLaw (E i) (expMeasure 1) P₀)
    (hind : iIndepFun E P₀) {U A : ℝ → ℝ} {γ ρ lam : ℝ} (hU : Measurable U)
    (hUm : MonotoneOn U (Ioi 1)) (h2 : IsSecondOrderRegularlyVarying U γ ρ A)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) :
    IsBoundedInProbability P₀ (fun n ω => √(k n : ℝ) *
      (log (orderStat (fun i : Fin n => U (exp (E i ω))) (k n)) - log (U (n / k n)))) := by
  obtain ⟨B, hBm, h2B, hBA⟩ := h2.exists_measurable hU
  have hnk := tendsto_div_atTop_of_tendsto hk hkn
  have hlamB : Tendsto (fun n => √(k n : ℝ) * B (n / k n)) atTop (𝓝 lam) := by
    have := hlam.mul (hBA.comp hnk)
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hnk.eventually h2.eventually_ne_zero] with n hn
    simp only [Function.comp_apply]
    field_simp
  obtain ⟨C, t₀, ht₀, hC⟩ := h2B.exists_bound_Icc hU hBm
  have hT := isBoundedInProbability_orderStat_sub_log hEm hE hind hk hkn
  have hnull : P₀ (⋃ i, {ω | E i ω ≤ 0}) = 0 := by
    refine measure_iUnion_null fun i => ?_
    have : {ω | E i ω ≤ 0} = E i ⁻¹' Iic 0 := rfl
    rw [this, ← Measure.map_apply (hEm i) measurableSet_Iic, (hE i).map_eq, expMeasure_Iic le_rfl]
    simp
  intro ε hε
  obtain ⟨M', hM'⟩ := hT ε hε
  set M₁ := max M' 0 with hM₁
  refine ⟨|γ| * M₁ + |C| * (|lam| + 1), ?_⟩
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  filter_upwards [hM', hnk.eventually_ge_atTop t₀, eventually_lt_of_tendsto_div hkn,
    hkR.eventually_ge_atTop (M₁ ^ 2), hkR.eventually_gt_atTop 0,
    hlamB.abs.eventually (gt_mem_nhds (lt_add_one |lam|))] with n hn hnt hkn' hkM hk0 hlamn
  refine le_trans (measure_mono_ae ?_) hn
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
  intro hω'
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hω
  change |γ| * M₁ + |C| * (|lam| + 1) < _ at hω'
  by_contra hcon
  rw [not_lt] at hcon
  set e := orderStat (fun i : Fin n => E i ω) (k n) with he
  set s₀ := log (n / k n) with hs₀
  have hn0 : (0 : ℝ) < n / k n := ht₀.trans_le hnt
  have hsk : 0 < √(k n : ℝ) := sqrt_pos.2 hk0
  -- `|e - s₀| ≤ M₁ / √k ≤ 1`
  have hes : |e - s₀| ≤ M₁ / √(k n : ℝ) := by
    rw [le_div_iff₀ hsk, mul_comm]
    rw [abs_mul, abs_of_pos hsk] at hcon
    exact hcon.trans (le_max_left _ _)
  have hM1k : M₁ / √(k n : ℝ) ≤ 1 := by
    rw [div_le_one hsk]
    calc M₁ = √(M₁ ^ 2) := (sqrt_sq (le_max_right _ _)).symm
      _ ≤ √(k n : ℝ) := sqrt_le_sqrt hkM
  -- order statistics commute with `U ∘ exp`
  have hmono : MonotoneOn (fun x => U (exp x)) (Ioi 0) := fun a ha b hb hab =>
    hUm (one_lt_exp_iff.2 ha) (one_lt_exp_iff.2 hb) (exp_le_exp.2 hab)
  have hcomm := orderStat_comp_monotoneOn hmono (y := fun i : Fin n => E i ω)
    (fun i => hω i) hkn'
  simp only [Function.comp_def] at hcomm
  rw [hcomm] at hω'
  set x := exp (e - s₀) with hx
  have hx1 : exp (-1) ≤ x := exp_le_exp.2 (by linarith [(abs_le.1 (hes.trans hM1k)).1])
  have hxt : exp e = x * (n / k n) := by
    rw [hx, exp_sub, hs₀, exp_log hn0, div_mul_cancel₀ _ hn0.ne']
  have hx2 : x ≤ exp 1 := exp_le_exp.2 (by linarith [(abs_le.1 (hes.trans hM1k)).2])
  have hbd := hC (n / k n) hnt x ⟨hx1, hx2⟩
  rw [← hxt, hx, log_exp] at hbd
  have key : |log (U (exp e)) - log (U (n / k n))| ≤
      |γ| * (M₁ / √(k n : ℝ)) + |C| * |B (n / k n)| := by
    have h1 : |log (U (exp e)) - log (U (n / k n))| ≤
        |γ * (e - s₀)| + |log (U (exp e)) - log (U (n / k n)) - γ * (e - s₀)| := by
      have := abs_add_le (γ * (e - s₀)) (log (U (exp e)) - log (U (n / k n)) - γ * (e - s₀))
      rwa [add_sub_cancel] at this
    refine h1.trans (add_le_add ?_ (hbd.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (abs_nonneg _))))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hes (abs_nonneg _)
  rw [abs_mul, abs_of_pos hsk] at hω'
  have h3 := mul_le_mul_of_nonneg_left key hsk.le
  have h4 : √(k n : ℝ) * (|γ| * (M₁ / √(k n : ℝ)) + |C| * |B (n / k n)|) =
      |γ| * M₁ + |C| * |√(k n : ℝ) * B (n / k n)| := by
    rw [abs_mul, abs_of_pos hsk]; field_simp
  rw [h4] at h3
  have h5 : |C| * |√(k n : ℝ) * B (n / k n)| ≤ |C| * (|lam| + 1) :=
    mul_le_mul_of_nonneg_left hlamn.le (abs_nonneg _)
  linarith

omit [IsProbabilityMeasure P₀] in
/-- **The quantile transform for samples**: the law of any measurable statistic of the iid
sample `(X_i)_{i<n}` equals the law of the same statistic of `(U(e^{E_i}))_{i<n}`, where the
`E_i` are iid standard exponential and `U` is the tail quantile function of `X_0`. -/
theorem map_statistic_eq_map_statistic_comp_exp {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {E : ℕ → Ω₀ → ℝ}
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P₀) (hind : iIndepFun E P₀) (n : ℕ)
    {S : (Fin n → ℝ) → ℝ} (hS : Measurable S) :
    P.map (fun ω => S (fun i => X i ω)) =
      P₀.map (fun ω => S (fun i => survivalQuantile (survival P (X 0)) (exp (E i ω)))) := by
  set U := survivalQuantile (survival P (X 0)) with hUdef
  have hUm := measurable_tailQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  have hV : Measurable fun e => U (exp e) := hUm.comp measurable_exp
  have hlawX : HasLaw (fun ω (i : Fin n) => X i ω)
      (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => U (exp e)) P := by
    refine (hindep.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective).hasLaw_pi
      (fun i => ⟨(hX i).aemeasurable, ?_⟩)
    rw [(hident i).map_eq]
    exact map_eq_expMeasure_map_tailQuantile (hX 0)
  have e1 : P.map (fun ω => S (fun i => X i ω)) =
      (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => U (exp e)).map S :=
    ((hasLaw_map hS.aemeasurable).comp hlawX).map_eq
  have hT : Measurable fun y : Fin n → ℝ => S (fun i => U (exp (y i))) :=
    hS.comp (measurable_pi_iff.2 fun i => hV.comp (measurable_pi_apply i))
  have e2 : P₀.map (fun ω => S (fun i => U (exp (E i ω)))) =
      (Measure.pi fun _ : Fin n => expMeasure 1).map
        (fun y : Fin n → ℝ => S (fun i => U (exp (y i)))) :=
    map_comp_vec_of_iid hE hind hT
  rw [e1, e2, ← Measure.pi_map_pi (fun _ => hV.aemeasurable), Measure.map_map hS (by fun_prop)]
  rfl

/-- **The intermediate order statistic at rate `√k`** ([dHF, Theorem 2.4.1]): under
second-order regular variation of the tail quantile function (any `ρ ≤ 0`), `k → ∞`,
`k / n → 0` and `√k A(n/k) → λ`, `√k (log X_{(k+1)} - log U(n/k))` is bounded in
probability. -/
theorem isBoundedInProbability_log_orderStat {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ}
    {A : ℝ → ℝ}
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) :
    IsBoundedInProbability P (fun n ω => √(k n : ℝ) *
      (log (orderStat (fun i : Fin n => X i ω) (k n)) -
        log (survivalQuantile (survival P (X 0)) (n / k n)))) := by
  obtain ⟨Ω₀, _, P₀, E, hEm, hE, hind, hP₀⟩ := exists_iid ℕ (expMeasure 1)
  set U := survivalQuantile (survival P (X 0)) with hUdef
  have hUm := measurable_tailQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  have hUmono := monotoneOn_tailQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  have hB := isBoundedInProbability_log_orderStat_comp_exp hEm hE hind hUm hUmono h2 hk hkn
    hlam
  intro ε hε
  obtain ⟨M, hM⟩ := hB ε hε
  refine ⟨M, hM.mono fun n hn => ?_⟩
  set S : (Fin n → ℝ) → ℝ := fun y => √(k n : ℝ) * (log (orderStat y (k n)) - log (U (n / k n)))
    with hS
  have hSm : Measurable S :=
    measurable_const.mul ((measurable_orderStat_pi (k n)).log.sub measurable_const)
  have hmeas : MeasurableSet {y : ℝ | M < |y|} := measurableSet_lt measurable_const
    continuous_abs.measurable
  have e := map_statistic_eq_map_statistic_comp_exp hX hindep hident hE hind n hSm
  have e' := congrArg (fun μ : Measure ℝ => μ {y : ℝ | M < |y|}) e
  have m1 : Measurable fun ω => S (fun i : Fin n => X i ω) :=
    hSm.comp (measurable_pi_iff.2 fun i => hX i)
  have m2 : Measurable fun ω => S (fun i : Fin n => U (exp (E i ω))) :=
    hSm.comp (measurable_pi_iff.2 fun i => (hUm.comp measurable_exp).comp (hEm i))
  rw [Measure.map_apply m1 hmeas, Measure.map_apply m2 hmeas] at e'
  change P {ω | M < |S (fun i => X i ω)|} ≤ ε
  rw [show {ω | M < |S (fun i => X i ω)|} = (fun ω => S (fun i => X i ω)) ⁻¹' {y | M < |y|}
    from rfl, e']
  exact hn

end IntermediateOrderStat

/-! ### Asymptotic normality of the Weissman estimator -/

section Aux

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Slutsky-type lemma, random version**: if `Z_n` is bounded in probability and `Y_n → 0` in
probability, then `Y_n Z_n → 0` in probability. -/
theorem tendstoInMeasure_mul_zero_of_isBoundedInProbability' {Z Y : ℕ → Ω → ℝ}
    (hZ : IsBoundedInProbability P Z) (hY : TendstoInMeasure P Y atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => Y n ω * Z n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨M, hM⟩ := hZ (ε / 2) hε2
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hY' := (ENNReal.tendsto_nhds_zero.1 (hY (δ / M') (by positivity))) (ε / 2) hε2
  filter_upwards [hM, hY'] with n h1 h2
  refine (measure_mono (t := {ω | M < |Z n ω|} ∪ {ω | δ / M' ≤ dist (Y n ω) 0}) ?_).trans
    ((measure_union_le _ _).trans ((add_le_add h1 h2).trans (ENNReal.add_halves ε).le))
  intro ω hω
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨hz, hy⟩ := hcon
  have h3 : |Y n ω| * |Z n ω| ≤ |Y n ω| * M' :=
    mul_le_mul_of_nonneg_left (hz.trans (le_max_left _ _)) (abs_nonneg _)
  rw [lt_div_iff₀ hM'pos] at hy
  linarith

end Aux

/-- The difference quotient `(e^y - 1) / y` of the exponential at `0`, extended by `1` at `0`. -/
noncomputable def expSlope (y : ℝ) : ℝ := if y = 0 then 1 else (exp y - 1) / y

theorem expSlope_zero : expSlope 0 = 1 := by simp [expSlope]

theorem continuousAt_expSlope : ContinuousAt expSlope 0 := by
  rw [← continuousWithinAt_compl_self]
  have h := hasDerivAt_iff_tendsto_slope_zero.1 (Real.hasDerivAt_exp 0)
  rw [exp_zero] at h
  rw [ContinuousWithinAt, expSlope_zero]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [mem_compl_iff, mem_singleton_iff] at hy
  simp only [expSlope, hy, ↓reduceIte, zero_add, smul_eq_mul]
  ring

theorem measurable_expSlope : Measurable expSlope := by
  unfold expSlope
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((measurable_exp.sub_const 1).div measurable_id)

theorem mul_expSlope_mul {h : ℝ} (hh : h ≠ 0) (g : ℝ) :
    g * expSlope (h * g) = (exp (h * g) - 1) / h := by
  by_cases hg : g = 0
  · simp [hg]
  · have : h * g ≠ 0 := mul_ne_zero hh hg
    simp only [expSlope, this, ↓reduceIte]
    field_simp

section Normality

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Asymptotic normality of the Weissman estimator** ([dHF, §4.3]). Let
`X_0, X_1, …` be iid with tail quantile function `U` of second-order regular variation with
`γ > 0`, `ρ < 0` and auxiliary function `A`. If `k → ∞`, `k / n → 0`, `√k A(n/k) → λ`, and the
extrapolation factor `d_n = k / (n p_n)` satisfies `d_n → ∞` and `log d_n / √k → 0`, then

  `(√k / log d_n) (x̂_{p_n} / x_{p_n} - 1) ⇒ N(λ / (1 - ρ), γ²)`. -/
theorem tendstoInDistribution_weissman {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ) (hρ : ρ < 0)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {p : ℕ → ℝ}
    (hp0 : ∀ᶠ n in atTop, 0 < p n) (hd : Tendsto (fun n => (k n : ℝ) / (n * p n)) atTop atTop)
    (hdk : Tendsto (fun n => Real.log ((k n : ℝ) / (n * p n)) / √(k n : ℝ)) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal (lam / (1 - ρ)) (γ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) / Real.log ((k n : ℝ) / (n * p n)) *
      (weissman (fun i : Fin n => X i ω) (k n) (p n) / tailQuantile P (X 0) (p n) - 1))
      atTop Z (fun _ => P) P' := by
  set U := survivalQuantile (survival P (X 0)) with hUdef
  have hUm := measurable_tailQuantile (survival_anti (P := P) (X 0))
    (continuousWithinAt_survival (P := P) (hX 0)) (tendsto_survival_atTop (P := P) (hX 0))
    (tendsto_survival_atBot (P := P) (hX 0))
  set d : ℕ → ℝ := fun n => (k n : ℝ) / (n * p n) with hd_def
  set ℓ : ℕ → ℝ := fun n => Real.log (d n) with hℓ_def
  set h : ℕ → ℝ := fun n => ℓ n / √(k n : ℝ) with hh_def
  set t : ℕ → ℝ := fun n => (n : ℝ) / k n with ht_def
  have hnk : Tendsto t atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  -- a measurable auxiliary function and the deterministic bias
  obtain ⟨B, hBm, h2B, hBA⟩ := h2.exists_measurable hUm
  have hlamB : Tendsto (fun n => √(k n : ℝ) * B (t n)) atTop (𝓝 lam) := by
    have := hlam.mul (hBA.comp hnk)
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hnk.eventually h2.eventually_ne_zero] with n hn
    simp only [Function.comp_apply, ht_def] at hn ⊢
    field_simp
  obtain ⟨C, t₀, -, hC⟩ := h2B.exists_bound_of_neg hUm hBm hρ
  set r : ℕ → ℝ := fun n => log (U (d n * t n)) - log (U (t n)) - γ * log (d n) with hr_def
  have hℓ : Tendsto ℓ atTop atTop := tendsto_log_atTop.comp hd
  have hℓinv : Tendsto (fun n => (ℓ n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hℓ
  have hrdet : Tendsto (fun n => √(k n : ℝ) * r n / ℓ n) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => |C| * (|lam| + 1) * (ℓ n)⁻¹) atTop (𝓝 0) := by
      simpa using hℓinv.const_mul (|C| * (|lam| + 1))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hnk.eventually_ge_atTop t₀, hd.eventually_ge_atTop 1,
      hℓ.eventually_gt_atTop 0, hkR.eventually_gt_atTop 0,
      hlamB.abs.eventually (gt_mem_nhds (lt_add_one |lam|))] with n h1 h3 hℓ0 hk0 hlamn
    have hb1 := hC (t n) h1 (d n) h3
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hℓ0, abs_of_pos (sqrt_pos.2 hk0),
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hℓ0.le)
    calc √(k n : ℝ) * |r n| ≤ √(k n : ℝ) * (C * |B (t n)|) := by gcongr
      _ ≤ |C| * |√(k n : ℝ) * B (t n)| := by
          rw [abs_mul, abs_of_pos (sqrt_pos.2 hk0),
            show √(k n : ℝ) * (C * |B (t n)|) = C * (√(k n : ℝ) * |B (t n)|) by ring]
          exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (|lam| + 1) := mul_le_mul_of_nonneg_left hlamn.le (abs_nonneg _)
  -- the random terms
  have hW := tendstoInDistribution_hill hX hindep hident hγ h2 hk hkn hlam hZ
  have hV := isBoundedInProbability_log_orderStat hX hindep hident h2 hk hkn hlam
  have hOS : ∀ n, Measurable fun ω => orderStat (fun i : Fin n => X i ω) (k n) := fun n =>
    measurable_orderStat (fun i => hX i) _
  have hH : ∀ n, Measurable fun ω => hill (fun i : Fin n => X i ω) (k n) := fun n =>
    (measurable_hill_pi n (k n)).comp (measurable_pi_iff.2 fun i => hX i)
  set W : ℕ → Ω → ℝ := fun n ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - γ)
    with hW_def
  set V : ℕ → Ω → ℝ := fun n ω => √(k n : ℝ) *
    (log (orderStat (fun i : Fin n => X i ω) (k n)) - log (U (t n))) with hV_def
  set Y : ℕ → Ω → ℝ := fun n ω => (ℓ n)⁻¹ * V n ω - √(k n : ℝ) * r n / ℓ n with hY_def
  have hY : TendstoInMeasure P Y atTop (fun _ => 0) := by
    have h1 := tendstoInMeasure_mul_zero_of_isBoundedInProbability hV hℓinv
    have h2' := tendstoInMeasure_const_of_tendsto (P := P) hrdet
    have := tendstoInMeasure_comp₂ h1 h2' (φ := fun q => q.1 - q.2) (by fun_prop)
    simp only [sub_self] at this
    exact this
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (measurable_const.mul (measurable_const.mul ((hOS n).log.sub measurable_const))).sub
      measurable_const
  have hZ0 : (fun ω => Z ω + 0) = Z := by funext ω; simp
  set G : ℕ → Ω → ℝ := fun n => W n + Y n with hG_def
  have hG : TendstoInDistribution G atTop Z (fun _ => P) P' := by
    have := hW.add_of_tendstoInMeasure_const hY fun n => (hYm n).aemeasurable
    rwa [hZ0] at this
  have hGm : ∀ n, Measurable (G n) := fun n =>
    (measurable_const.mul ((hH n).sub measurable_const)).add (hYm n)
  have hGt := isBoundedInProbability_of_tendstoInDistribution hG
  have hhG : TendstoInMeasure P (fun n ω => h n * G n ω) atTop (fun _ => 0) :=
    tendstoInMeasure_mul_zero_of_isBoundedInProbability hGt hdk
  have hφ := tendstoInMeasure_comp hhG (φ := fun y => expSlope y - 1)
    (continuousAt_expSlope.sub continuousAt_const)
  simp only [expSlope_zero, sub_self] at hφ
  have hY2 := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hGt hφ
  have hY2m : ∀ n, Measurable fun ω => (expSlope (h n * G n ω) - 1) * G n ω := fun n =>
    ((measurable_expSlope.comp (measurable_const.mul (hGm n))).sub_const 1).mul (hGm n)
  set T' : ℕ → Ω → ℝ := fun n => G n + fun ω => (expSlope (h n * G n ω) - 1) * G n ω
    with hT'_def
  have hT' : TendstoInDistribution T' atTop Z (fun _ => P) P' := by
    have := hG.add_of_tendstoInMeasure_const hY2 fun n => (hY2m n).aemeasurable
    rwa [hZ0] at this
  have hT'm : ∀ n, Measurable (T' n) := fun n => (hGm n).add (hY2m n)
  set T : ℕ → Ω → ℝ := fun n ω => √(k n : ℝ) / Real.log ((k n : ℝ) / (n * p n)) *
    (weissman (fun i : Fin n => X i ω) (k n) (p n) / tailQuantile P (X 0) (p n) - 1) with hT_def
  have hTm : ∀ n, Measurable (T n) := by
    intro n
    have h1 := hOS n
    have h3 := hH n
    simp only [hT_def, weissman]
    fun_prop
  -- the event `X_{(k+1)} ≤ 0` is asymptotically negligible
  have hRV := h2.isRegularlyVarying_survival (hX 0) hγ
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have hr0 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < k n / n := by
    filter_upwards [hkpos, hnpos] with n h1 h2; positivity
  obtain ⟨hs, -⟩ := tendsto_tailQuantile (hX 0) hRV hr0 hkn
  have hbad : Tendsto (fun n => P {ω | orderStat (fun i : Fin n => X i ω) (k n) ≤ 0}) atTop
      (𝓝 0) := by
    have hloc := tendstoInMeasure_orderStat_div_tailQuantile hX hindep hident
      (one_div_pos.2 hγ) hRV hk hkn
    rw [tendstoInMeasure_iff_dist] at hloc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hloc 1 one_pos)
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hs.eventually_gt_atTop 0] with n hsn
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq, Real.dist_eq] at hω ⊢
    have : orderStat (fun i : Fin n => X i ω) (k n) / tailQuantile P (X 0) ((k n : ℝ) / n) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hω hsn.le
    rw [abs_sub_comm]
    exact (le_abs_self _).trans' (by linarith)
  have hdt : Tendsto (fun n => d n * t n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hnk
    filter_upwards [hd.eventually_ge_atTop 1, hnk.eventually_ge_atTop 0] with n h1 h3
    exact le_mul_of_one_le_left h3 h1
  have hD : TendstoInMeasure P (fun n ω => T n ω - T' n ω) atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr_of_measure_ne (g := fun _ _ => 0)
      (tendstoInMeasure_const_of_tendsto tendsto_const_nhds) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hkpos, hnpos, hp0, hkn.eventually (gt_mem_nhds one_pos),
      hd.eventually_gt_atTop 1, hnk.eventually h2.eventually_pos,
      hdt.eventually h2.eventually_pos] with n hk0 hn0 hpn hkn1 hd1 hUt hUdt
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra ho
    rw [not_le] at ho
    apply hω
    set o := orderStat (fun i : Fin n => X i ω) (k n) with ho_def
    set g := hill (fun i : Fin n => X i ω) (k n) with hg_def
    have hd0 : 0 < d n := one_pos.trans hd1
    have hℓ0 : 0 < ℓ n := log_pos hd1
    have hsk : 0 < √(k n : ℝ) := sqrt_pos.2 hk0
    have hh0 : h n ≠ 0 := (div_pos hℓ0 hsk).ne'
    -- the extreme quantile is `U(d t)`
    have hpk : p n ≤ (k n : ℝ) / n := by
      have := hd1.le
      simp only [hd_def] at this
      rw [le_div_iff₀ (mul_pos hn0 hpn)] at this
      rw [le_div_iff₀ hn0]
      linarith
    have hxp : tailQuantile P (X 0) (p n) = U (d n * t n) := by
      rw [tailQuantile_eq_survivalQuantile hpn (hpk.trans_lt hkn1)]
      congr 1
      simp only [hd_def, ht_def]
      field_simp
    have key : h n * G n ω = log o + log (d n) * g - log (U (d n * t n)) := by
      have hℓ0' : log (d n) ≠ 0 := hℓ0.ne'
      simp only [hG_def, hW_def, hY_def, hV_def, hr_def, hh_def, Pi.add_apply, hℓ_def]
      field_simp
      ring
    have hw : weissman (fun i : Fin n => X i ω) (k n) (p n) / tailQuantile P (X 0) (p n) =
        exp (h n * G n ω) := by
      rw [key, exp_sub, exp_add, exp_log ho, exp_log hUdt, hxp, weissman,
        rpow_def_of_pos hd0]
    have hT'e : T' n ω = (exp (h n * G n ω) - 1) / h n := by
      rw [← mul_expSlope_mul hh0]
      simp only [hT'_def, Pi.add_apply]
      ring
    simp only [hT_def]
    rw [hw, hT'e, sub_eq_zero]
    simp only [hh_def, hℓ_def, hd_def]
    field_simp
  have hfinal := hT'.add_of_tendstoInMeasure_const hD fun n => ((hTm n).sub (hT'm n)).aemeasurable
  rw [hZ0] at hfinal
  have e : (fun n => T' n + fun ω => T n ω - T' n ω) = T := by
    funext n ω
    simp
  rw [e] at hfinal
  exact hfinal

end Normality

end ExtremeValueTheory
