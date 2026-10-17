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

end ExtremeValueTheory
