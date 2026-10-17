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
    have hlim := (hU.tendsto (inv_pos.2 ha0)).sub ((hU.tendsto (by linarith : (0 : ℝ) < v)).const_mul c)
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

/-- **Second-order quantile extrapolation** ([dHF, proof of Theorem 4.3.1]): if `U` is of
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
variation with `ρ < 0` ([dHF, proof of Theorem 4.3.1]): if `k → ∞`, `k / n → 0` and the
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

/-- **Consistency of the Weissman estimator for extreme quantiles** ([dHF, Theorem 4.3.1],
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

end ExtremeValueTheory
