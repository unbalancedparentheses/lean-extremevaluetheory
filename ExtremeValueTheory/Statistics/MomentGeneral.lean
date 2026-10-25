/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Moment
import ExtremeValueTheory.DomainOfAttraction.Quantile

/-!
# Consistency of the moment estimator for every extreme value index

The moment estimator of Dekkers, Einmahl and de Haan,

  `γ̂_M = M^{(1)} + 1 - (1/2) (1 - (M^{(1)})² / M^{(2)})⁻¹`,

with the log-moments `M^{(j)} = (1/k) ∑_{i<k} (log X_{(i+1)} - log X_{(k+1)}) ^ j`
(`ExtremeValueTheory.momentEstimator`, `ExtremeValueTheory.logMoment`), is consistent for every
`γ ∈ ℝ` provided the right endpoint `x_F = U(∞)` is positive ([dHF, Theorem 3.5.2]; A. L. M.
Dekkers, J. H. J. Einmahl and L. de Haan, Ann. Statist. 17 (1989)).

## Main results

* `ExtremeValueTheory.gpdMoment_one`, `gpdMoment_two`: the moments of the generalized Pareto
  distribution with shape `ρ ≤ 0`: `1 / (1 - ρ)` and `2 / ((1 - ρ) (1 - 2ρ))`.
* `ExtremeValueTheory.tendstoInMeasure_logMoment_of_isInMDAGEV`: if `F ∈ MDA(H_γ)` and
  `x_F > 0`, then with the auxiliary function `a` of the extended regular variation of `U`
  (`CumulativeDistributionFunction.isExtendedRegularlyVarying_tailQuantile`),
  `M^{(1)} U(n/k) / a(n/k) → 1 / (1 - γ₋)` and
  `M^{(2)} (U(n/k) / a(n/k))² → 2 / ((1 - γ₋)(1 - 2γ₋))` in probability, where `γ₋ = min γ 0`
  ([dHF, Lemma 3.5.1 and the proof of Theorem 3.5.2]).
* `ExtremeValueTheory.tendstoInMeasure_momentEstimator_of_isInMDAGEV'`: **weak consistency of
  the moment estimator for every `γ ∈ ℝ`** ([dHF, Theorem 3.5.2]).

## Proof

Let `U` be the tail quantile function, `q = a / U` and `t = n / k`. By [dHF, Lemma 3.5.1]
(`IsExtendedRegularlyVarying.log`), `log U` is extended regularly varying with index
`ρ = γ₋ ≤ 0` and auxiliary function `q`, which gives `t F̄(exp (log U(t) + q(t) x)) → Ḡ_ρ(x)`
(`tendsto_mul_one_sub_exp_log_tailQuantile`) with a Potter-type domination
(`exists_mul_one_sub_exp_log_tailQuantile_le`).

1. At the deterministic threshold `U(t)`, the layer cake formula and dominated convergence give
   `t E[(log⁺ (X / U(t)) / q(t)) ^ p] → p ∫_0^∞ z ^ (p - 1) Ḡ_ρ(z) dz`, and a weak law of large
   numbers gives `(1/k) ∑_i (log⁺ (X_i / U(t)) / q(t)) ^ j → μ_j` in probability.
2. The random threshold `X_{(k+1)}` lies between `exp (log U(t) ∓ q(t) η)` with probability
   tending to one (exceedance counts), and the log-excess is `1`-Lipschitz in the logarithm of
   the threshold, so replacing `U(t)` by `X_{(k+1)}` changes the normalized log-moments by
   `O(η)`.
3. Finally `q(t) → γ₊ = max γ 0`, so `M^{(1)} → γ₊ μ₁` and `(M^{(1)})² / M^{(2)} → μ₁² / μ₂`,
   and the moment estimator tends to `γ₊ / (1 - γ₋) + γ₋ = γ`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

/-! ### The generalized Pareto distribution with non-positive shape -/

section GPD

variable {ρ : ℝ}

theorem continuous_gpdSurvival_of_nonpos (hρ : ρ ≤ 0) : Continuous (gpdSurvival ρ 1) := by
  rcases hρ.lt_or_eq with hρ' | hρ'
  · have : gpdSurvival ρ 1 = fun x => (max (1 + ρ * x) 0) ^ (-(1 / ρ)) := by
      funext x; exact gpdSurvival_one_of_ne hρ'.ne x
    rw [this]
    have hp : 0 < -(1 / ρ) := by
      have : 1 / ρ < 0 := one_div_neg.2 hρ'
      linarith
    exact (continuous_const.add (continuous_const.mul continuous_id)).max continuous_const
      |>.rpow_const fun _ => Or.inr hp.le
  · subst hρ'
    have : gpdSurvival 0 1 = fun x => Real.exp (-x / 1) := by
      funext x; exact gpdSurvival_of_eq_zero 1 x
    rw [this]
    fun_prop

theorem one_lt_gpdSurvival_of_neg (hρ : ρ ≤ 0) {x : ℝ} (hx : x < 0) :
    1 < gpdSurvival ρ 1 x := by
  rcases hρ.lt_or_eq with hρ' | hρ'
  · rw [gpdSurvival_one_of_ne hρ'.ne]
    have hb : 1 < 1 + ρ * x := by nlinarith
    rw [max_eq_left (by linarith)]
    exact one_lt_rpow hb (by have : 1 / ρ < 0 := one_div_neg.2 hρ'; linarith)
  · subst hρ'
    rw [gpdSurvival_of_eq_zero, div_one]
    exact Real.one_lt_exp_iff.2 (by linarith)

/-- The `p`-th moment `p ∫_0^∞ z ^ (p - 1) Ḡ_{ρ,1}(z) dz` of the generalized Pareto
distribution with shape `ρ` (layer cake form). -/
noncomputable def gpdMoment (ρ p : ℝ) : ℝ :=
  p * ∫ z in Ioi 0, z ^ (p - 1) * gpdSurvival ρ 1 z

/-- For `ρ < 0` the integrand of `gpdMoment` vanishes beyond the right endpoint `-1/ρ`. -/
private lemma integral_Ioi_eq_intervalIntegral (hρ : ρ < 0) (g : ℝ → ℝ) :
    ∫ z in Ioi 0, g z * gpdSurvival ρ 1 z = ∫ z in (0 : ℝ)..(-1 / ρ), g z * (1 + ρ * z) ^ (-(1 / ρ)) := by
  have he : 0 < -1 / ρ := div_pos_of_neg_of_neg (by norm_num) hρ
  have hp : 0 < -(1 / ρ) := by
    have : 1 / ρ < 0 := one_div_neg.2 hρ
    linarith
  rw [intervalIntegral.integral_of_le he.le,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
    rw [gpdSurvival_one_of_ne hρ.ne, max_eq_left]
    have := hz.2
    rw [le_div_iff_of_neg hρ] at this
    linarith
  · intro z hz
    have h1 : -1 / ρ < z := by
      by_contra h
      exact hz.2 ⟨hz.1, not_lt.1 h⟩
    rw [div_lt_iff_of_neg hρ] at h1
    rw [gpdSurvival_one_of_ne hρ.ne, max_eq_right (by linarith), zero_rpow hp.ne', mul_zero]

theorem gpdMoment_one (hρ : ρ ≤ 0) : gpdMoment ρ 1 = 1 / (1 - ρ) := by
  rcases hρ.lt_or_eq with hρ' | hρ'
  · rw [gpdMoment, one_mul]
    have := integral_Ioi_eq_intervalIntegral hρ' (fun z => z ^ ((1 : ℝ) - 1))
    simp only [sub_self, rpow_zero, one_mul] at this ⊢
    rw [this]
    have hρ0 : ρ ≠ 0 := hρ'.ne
    have h1ρ : 1 - ρ ≠ 0 := by linarith
    set a := 1 - 1 / ρ with ha
    have ha0 : 0 < a := by
      have : 1 / ρ < 0 := one_div_neg.2 hρ'
      rw [ha]; linarith
    have hρ1 : ρ - 1 ≠ 0 := by linarith
    have hF : ∀ z ∈ Ioo (0 : ℝ) (-1 / ρ), HasDerivAt (fun z => (1 + ρ * z) ^ a / (ρ - 1))
        ((1 + ρ * z) ^ (-(1 / ρ))) z := by
      intro z hz
      have hb : 0 < 1 + ρ * z := by
        have := hz.2
        rw [lt_div_iff_of_neg hρ'] at this
        linarith
      have h1 : HasDerivAt (fun z => 1 + ρ * z) ρ z := by
        simpa using ((hasDerivAt_id z).const_mul ρ).const_add 1
      have h2 := (h1.rpow_const (p := a) (Or.inl hb.ne')).div_const (ρ - 1)
      refine h2.congr_deriv ?_
      rw [show a - 1 = -(1 / ρ) by rw [ha]; ring]
      field_simp
      rw [ha]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (div_pos_of_neg_of_neg (by norm_num) hρ').le ?_ hF ?_]
    · have : 1 + ρ * (-1 / ρ) = 0 := by field_simp; ring
      rw [this, zero_rpow ha0.ne', mul_zero, add_zero, one_rpow]
      field_simp
      ring
    · exact (Continuous.div_const (Continuous.rpow_const (f := fun z : ℝ => 1 + ρ * z)
        (by fun_prop) fun _ => Or.inr ha0.le) _).continuousOn
    · have hp : 0 ≤ -(1 / ρ) := by
        have : 1 / ρ < 0 := one_div_neg.2 hρ'
        linarith
      exact (Continuous.rpow_const (f := fun z : ℝ => 1 + ρ * z) (by fun_prop)
        fun _ => Or.inr hp).intervalIntegrable _ _
  · subst hρ'
    rw [gpdMoment, one_mul]
    simp only [gpdSurvival_of_eq_zero, div_one, sub_self, rpow_zero, one_mul]
    have := integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1) one_pos one_pos
    simp only [sub_self, rpow_zero, one_mul, div_one, one_rpow, Real.Gamma_one] at this
    rw [this]
    norm_num

theorem gpdMoment_two (hρ : ρ ≤ 0) : gpdMoment ρ 2 = 2 / ((1 - ρ) * (1 - 2 * ρ)) := by
  rcases hρ.lt_or_eq with hρ' | hρ'
  · rw [gpdMoment]
    have := integral_Ioi_eq_intervalIntegral hρ' (fun z => z ^ ((2 : ℝ) - 1))
    rw [show (2 : ℝ) - 1 = 1 by norm_num] at this ⊢
    simp only [rpow_one] at this ⊢
    rw [this]
    have hρ0 : ρ ≠ 0 := hρ'.ne
    have h1ρ : 1 - ρ ≠ 0 := by linarith
    have h2ρ : 1 - 2 * ρ ≠ 0 := by linarith
    have hρ1 : ρ - 1 ≠ 0 := by linarith
    have hρ2 : 2 * ρ - 1 ≠ 0 := by linarith
    set a := 1 - 1 / ρ with ha
    have ha0 : 0 < a := by
      have : 1 / ρ < 0 := one_div_neg.2 hρ'
      rw [ha]; linarith
    set c₁ := (ρ - 1)⁻¹ with hc₁
    set c₂ := ((ρ - 1) * (2 * ρ - 1))⁻¹ with hc₂
    have e1 : c₁ * (ρ * a) = 1 := by rw [hc₁, ha]; field_simp
    have hρa1 : ρ * (a + 1) = 2 * ρ - 1 := by rw [ha]; field_simp; ring
    have e2 : c₁ - c₂ * (ρ * (a + 1)) = 0 := by
      rw [hρa1, hc₂, hc₁, mul_inv, mul_assoc, inv_mul_cancel₀ hρ2, mul_one, sub_self]
    set G : ℝ → ℝ := fun z => c₁ * (z * (1 + ρ * z) ^ a) - c₂ * (1 + ρ * z) ^ (a + 1) with hG
    have hF : ∀ z ∈ Ioo (0 : ℝ) (-1 / ρ), HasDerivAt G (z * (1 + ρ * z) ^ (-(1 / ρ))) z := by
      intro z hz
      have hb : 0 < 1 + ρ * z := by
        have := hz.2
        rw [lt_div_iff_of_neg hρ'] at this
        linarith
      have h1 : HasDerivAt (fun z => 1 + ρ * z) ρ z := by
        simpa using ((hasDerivAt_id z).const_mul ρ).const_add 1
      have h2 := (((hasDerivAt_id' z).mul (h1.rpow_const (p := a) (Or.inl hb.ne'))).const_mul
        c₁).sub ((h1.rpow_const (p := a + 1) (Or.inl hb.ne')).const_mul c₂)
      refine h2.congr_deriv ?_
      rw [show a - 1 = -(1 / ρ) by rw [ha]; ring, show a + 1 - 1 = a by ring]
      linear_combination (1 + ρ * z) ^ a * e2 + z * (1 + ρ * z) ^ (-(1 / ρ)) * e1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (div_pos_of_neg_of_neg (by norm_num) hρ').le ?_ hF ?_]
    · have : 1 + ρ * (-1 / ρ) = 0 := by field_simp; ring
      simp only [hG]
      rw [this, zero_rpow ha0.ne', zero_rpow (by linarith), hc₂]
      simp only [mul_zero, add_zero, one_rpow, sub_zero, zero_sub, mul_one]
      field_simp
      ring
    · have h1 : Continuous fun z : ℝ => (1 + ρ * z) ^ a :=
        Continuous.rpow_const (f := fun z : ℝ => 1 + ρ * z) (by fun_prop) fun _ => Or.inr ha0.le
      have h2 : Continuous fun z : ℝ => (1 + ρ * z) ^ (a + 1) :=
        Continuous.rpow_const (f := fun z : ℝ => 1 + ρ * z) (by fun_prop)
          fun _ => Or.inr (by linarith)
      exact (((continuous_id.mul h1).const_mul c₁).sub (h2.const_mul c₂)).continuousOn
    · have hp : 0 ≤ -(1 / ρ) := by
        have : 1 / ρ < 0 := one_div_neg.2 hρ'
        linarith
      exact (continuous_id.mul (Continuous.rpow_const (f := fun z : ℝ => 1 + ρ * z)
        (by fun_prop) fun _ => Or.inr hp)).intervalIntegrable _ _
  · subst hρ'
    rw [gpdMoment]
    simp only [gpdSurvival_of_eq_zero, div_one]
    have := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1) two_pos one_pos
    simp only [one_mul, div_one, one_rpow, Real.Gamma_two] at this
    rw [this]
    norm_num

end GPD

/-! ### Normalized log-excesses over a deterministic threshold -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}

/-- The layer cake formula for the normalized log-excess:
`E (log⁺ (Y / s) / q) ^ p = p ∫_0^∞ z ^ (p - 1) F̄(s e^{q z}) dz`, with integrability. -/
theorem integrable_and_integral_logExcess_div_rpow (hY : Measurable Y) {s q p : ℝ} (hs : 0 < s)
    (hq : 0 < q) (hp : 0 < p)
    (hint : IntegrableOn (fun z => z ^ (p - 1) * survival P Y (s * Real.exp (q * z))) (Ioi 0)) :
    Integrable (fun ω => (logExcess s (Y ω) / q) ^ p) P ∧
      ∫ ω, (logExcess s (Y ω) / q) ^ p ∂P =
        p * ∫ z in Ioi 0, z ^ (p - 1) * survival P Y (s * Real.exp (q * z)) := by
  set W : Ω → ℝ := fun ω => logExcess s (Y ω) / q with hW_def
  have hWm : Measurable W := ((measurable_logExcess s).comp hY).div_const q
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => div_nonneg (logExcess_nonneg hs _) hq.le
  have hset : ∀ z : ℝ, 0 < z → {a | z < W a} = {a | s * Real.exp (q * z) < Y a} := by
    intro z hz
    rw [← setOf_lt_logExcess (Y := Y) hs (mul_pos hq hz)]
    ext ω
    simp only [mem_ofPred_eq, hW_def]
    rw [lt_div_iff₀ hq, mul_comm]
  have hL := lintegral_rpow_eq_lintegral_meas_lt_mul P (Eventually.of_forall hW0)
    hWm.aemeasurable hp
  have hI : ∫⁻ t in Ioi 0, P {a | t < W a} * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (∫ z in Ioi 0, z ^ (p - 1) * survival P Y (s * Real.exp (q * z))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : 0 < t := ht
      rw [hset t ht', ENNReal.ofReal_mul (rpow_nonneg ht'.le _), mul_comm]
      congr 1
      exact (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht' : 0 < t := ht
      exact mul_nonneg (rpow_nonneg ht'.le _) (survival_nonneg _)
  have hm : AEStronglyMeasurable (fun ω => W ω ^ p) P := (hWm.pow_const p).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[P] fun ω => W ω ^ p := Eventually.of_forall fun ω => rpow_nonneg (hW0 ω) _
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩, ?_⟩
  · rw [hL, hI]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm, hL, hI, ← ENNReal.ofReal_mul hp.le,
      ENNReal.toReal_ofReal]
    refine mul_nonneg hp.le (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
    have ht' : 0 < t := ht
    exact mul_nonneg (rpow_nonneg ht'.le _) (survival_nonneg _)

/-- `z ^ (p - 1) (1 + z) ^ (-(p + 1)) ≤ (1 + z²)⁻¹` for `z ≥ 0` and `p ≥ 1`. -/
private lemma rpow_mul_one_add_rpow_le {p z : ℝ} (hp : 1 ≤ p) (hz : 0 ≤ z) :
    z ^ (p - 1) * (1 + z) ^ (-(p + 1)) ≤ (1 + z ^ 2)⁻¹ := by
  have h1 : 0 < 1 + z := by linarith
  calc z ^ (p - 1) * (1 + z) ^ (-(p + 1)) ≤ (1 + z) ^ (p - 1) * (1 + z) ^ (-(p + 1)) := by
        gcongr
        linarith
    _ = ((1 + z) ^ 2)⁻¹ := by
        rw [← rpow_add h1, show p - 1 + -(p + 1) = -2 by ring, rpow_neg h1.le,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
    _ ≤ (1 + z ^ 2)⁻¹ := by
        gcongr
        nlinarith

/-- **Moments of the normalized log-excess over `U(t)`**: if `log U` is extended regularly
varying with index `ρ ≤ 0` and auxiliary function `q`, then for `p ≥ 1`,
`t E[(log⁺ (Y / U(t)) / q(t)) ^ p] → p ∫_0^∞ z ^ (p - 1) Ḡ_ρ(z) dz` as `t → ∞`. -/
theorem tendsto_mul_integral_logExcess_div_rpow (hY : Measurable Y)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | Y ω ≤ x}).toReal)
    {ρ : ℝ} (hρ : ρ ≤ 0) {q : ℝ → ℝ}
    (hV : IsExtendedRegularlyVarying (fun t => Real.log (F.tailQuantile t)) ρ q) {c : ℝ}
    (hmono : MonotoneOn (fun t => Real.log (F.tailQuantile t)) (Ici c))
    (hU : ∀ᶠ t in atTop, 0 < F.tailQuantile t) {p : ℝ} (hp : 1 ≤ p) :
    (∀ᶠ t in atTop, Integrable (fun ω => (logExcess (F.tailQuantile t) (Y ω) / q t) ^ p) P) ∧
      Tendsto (fun t => t * ∫ ω, (logExcess (F.tailQuantile t) (Y ω) / q t) ^ p ∂P) atTop
        (𝓝 (gpdMoment ρ p)) := by
  have hp0 : 0 < p := by linarith
  set U := F.tailQuantile with hU_def
  have hS : ∀ x, survival P Y x = 1 - F x := by
    intro x
    have hc : {ω | x < Y ω} = {ω | Y ω ≤ x}ᶜ := by ext ω; simp
    rw [survival, hc, prob_compl_eq_one_sub (measurableSet_le hY measurable_const),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, hF]
  obtain ⟨C, T₀, hT₀, hb⟩ :=
    F.exists_mul_one_sub_exp_log_tailQuantile_le hρ hV hmono hU (r := p + 1) (by linarith)
  have hexp : ∀ t, 0 < U t → ∀ z, U t * Real.exp (q t * z) =
      Real.exp (Real.log (U t) + q t * z) := by
    intro t ht z
    rw [Real.exp_add, Real.exp_log ht]
  set Fn : ℝ → ℝ → ℝ := fun t z => z ^ (p - 1) * survival P Y (U t * Real.exp (q t * z))
    with hFn
  have hmeas : ∀ t, 0 < U t → 0 < q t → Measurable (Fn t) := by
    intro t hUt hqt
    refine (measurable_id.pow_const _).mul (Antitone.measurable ?_)
    exact (survival_anti Y).comp_monotone fun u v huv =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left huv hqt.le))
        hUt.le
  have hbound : ∀ t ≥ T₀, ∀ z, 0 ≤ z → t * Fn t z ≤ C * (1 + z ^ 2)⁻¹ := by
    intro t ht z hz
    obtain ⟨hqt, hUt, hbt⟩ := hb t ht
    have h1 := hbt z hz
    rw [← hexp t hUt, ← hS] at h1
    have h2 := rpow_mul_one_add_rpow_le hp hz
    have hzp : 0 ≤ z ^ (p - 1) := rpow_nonneg hz _
    have hC : 0 ≤ C := by
      have h3 : 0 ≤ t * survival P Y (U t * Real.exp (q t * z)) :=
        mul_nonneg (by linarith) (survival_nonneg _)
      have h4 : 0 < (1 + z) ^ (-(p + 1)) := rpow_pos_of_pos (by linarith) _
      by_contra hcon
      push Not at hcon
      nlinarith
    calc t * Fn t z = z ^ (p - 1) * (t * survival P Y (U t * Real.exp (q t * z))) := by
          simp only [hFn]; ring
      _ ≤ z ^ (p - 1) * (C * (1 + z) ^ (-(p + 1))) := mul_le_mul_of_nonneg_left h1 hzp
      _ = C * (z ^ (p - 1) * (1 + z) ^ (-(p + 1))) := by ring
      _ ≤ C * (1 + z ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 hC
  have hint : ∀ t ≥ T₀, IntegrableOn (Fn t) (Ioi 0) := by
    intro t ht
    obtain ⟨hqt, hUt, -⟩ := hb t ht
    have ht0 : 0 < t := by linarith
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C / t)).integrableOn)
      (hmeas t hUt hqt).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
    have hz' : 0 < z := hz
    have hFn0 : 0 ≤ Fn t z := mul_nonneg (rpow_nonneg hz'.le _) (survival_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hFn0, div_mul_eq_mul_div, le_div_iff₀ ht0, mul_comm]
    exact hbound t ht z hz'.le
  have hlay : ∀ t ≥ T₀, Integrable (fun ω => (logExcess (U t) (Y ω) / q t) ^ p) P ∧
      ∫ ω, (logExcess (U t) (Y ω) / q t) ^ p ∂P = p * ∫ z in Ioi 0, Fn t z := by
    intro t ht
    obtain ⟨hqt, hUt, -⟩ := hb t ht
    exact integrable_and_integral_logExcess_div_rpow hY hUt hqt hp0 (hint t ht)
  refine ⟨eventually_atTop.2 ⟨T₀, fun t ht => (hlay t ht).1⟩, ?_⟩
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (l := atTop) (F := fun t z => t * Fn t z)
    (f := fun z => z ^ (p - 1) * gpdSurvival ρ 1 z) (fun z => C * (1 + z ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · refine (key.const_mul p).congr' ?_
    filter_upwards [eventually_ge_atTop T₀] with t ht
    rw [(hlay t ht).2, integral_const_mul]
    ring
  · filter_upwards [eventually_ge_atTop T₀] with t ht
    obtain ⟨hqt, hUt, -⟩ := hb t ht
    exact ((hmeas t hUt hqt).const_mul t).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop T₀] with t ht
    refine (ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
    have hz' : 0 < z := hz
    have ht0 : 0 < t := by linarith
    have hFn0 : 0 ≤ t * Fn t z :=
      mul_nonneg ht0.le (mul_nonneg (rpow_nonneg hz'.le _) (survival_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hFn0]
    exact hbound t ht z hz'.le
  · exact (integrable_inv_one_add_sq.const_mul C).integrableOn
  · refine Eventually.of_forall fun z => ?_
    have h := (F.tendsto_mul_one_sub_exp_log_tailQuantile hρ hV hU z).const_mul (z ^ (p - 1))
    refine h.congr' ?_
    filter_upwards [hU] with t ht
    simp only [hFn]
    rw [hexp t ht, hS]
    ring

end Tail

/-! ### Replacing the random threshold by a deterministic one -/

section Deterministic

theorem logExcess_eq_max {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    logExcess t y = max (Real.log y - Real.log t) 0 := by
  rcases le_total y t with h | h
  · rw [logExcess_of_le ht h, max_eq_right]
    linarith [Real.log_le_log hy h]
  · rw [logExcess_of_ge ht h, max_eq_left]
    linarith [Real.log_le_log ht h]

/-- The log-excess is `1`-Lipschitz in the logarithm of the threshold, and vanishes below the
thresholds. -/
theorem abs_logExcess_sub_logExcess_le {S s lo y : ℝ} (hlo : 0 < lo) (hS : lo < S) (hs : lo < s) :
    |logExcess S y - logExcess s y| ≤
      |Real.log S - Real.log s| * (if lo < y then 1 else 0) := by
  have hS0 : 0 < S := hlo.trans hS
  have hs0 : 0 < s := hlo.trans hs
  split_ifs with hy
  · rw [mul_one, logExcess_eq_max hS0 (hlo.trans hy), logExcess_eq_max hs0 (hlo.trans hy)]
    refine (abs_max_sub_max_le_abs _ _ _).trans_eq ?_
    rw [show Real.log y - Real.log S - (Real.log y - Real.log s) =
      -(Real.log S - Real.log s) by ring, abs_neg]
  · push Not at hy
    rw [logExcess_of_le hS0 (hy.trans hS.le), logExcess_of_le hs0 (hy.trans hs.le)]
    simp

/-- **Comparison of the log-moments with a deterministic threshold.** Let `lo = s e^{-Q η}` and
`hi = s e^{Q η}`. If fewer than `k` sample points exceed `hi` and between `k` and `K k` exceed
`lo`, then `X_{(k+1)} ∈ (lo, hi]`, and the normalized log-moments over `X_{(k+1)}` differ from
those over `s` by `O(η)`. -/
theorem abs_logMoment_div_sub_le {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (hk : k < n) (hk0 : 0 < k)
    {s Q η K : ℝ} (hs : 0 < s) (hQ : 0 < Q) (hη : 0 < η)
    (h1 : (exceedCount x (Real.exp (Real.log s + Q * η)) : ℝ) / k < 1)
    (h2 : 1 < (exceedCount x (Real.exp (Real.log s + Q * -η)) : ℝ) / k)
    (h3 : (exceedCount x (Real.exp (Real.log s + Q * -η)) : ℝ) / k ≤ K) :
    |logMoment x k 1 / Q - (∑ i, logExcess s (x i) / Q) / k| ≤ η * K ∧
      |logMoment x k 2 / Q ^ 2 - (∑ i, (logExcess s (x i) / Q) ^ 2) / k| ≤
        η * (2 * ((∑ i, logExcess s (x i) / Q) / k) + η * K) := by
  set lo := Real.exp (Real.log s + Q * -η) with hlo_def
  set hi := Real.exp (Real.log s + Q * η) with hhi_def
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  set S := orderStat x k with hS_def
  have hShi : S ≤ hi := by
    rw [hS_def, orderStat_le_iff x hk]
    rw [div_lt_one hkR] at h1
    exact_mod_cast h1.le
  have hSlo : lo < S := by
    rw [hS_def, lt_orderStat_iff x hk]
    rw [one_lt_div hkR] at h2
    exact_mod_cast h2
  have hlo0 : 0 < lo := Real.exp_pos _
  have hS0 : 0 < S := hlo0.trans hSlo
  have hlos : lo < s := by
    rw [hlo_def]
    calc Real.exp (Real.log s + Q * -η) < Real.exp (Real.log s) :=
          Real.exp_lt_exp.2 (by nlinarith)
      _ = s := Real.exp_log hs
  have hlog : |Real.log S - Real.log s| ≤ Q * η := by
    have e1 : Real.log lo = Real.log s + Q * -η := Real.log_exp _
    have e2 : Real.log hi = Real.log s + Q * η := Real.log_exp _
    have l1 := Real.log_lt_log hlo0 hSlo
    have l2 := Real.log_le_log hS0 hShi
    rw [abs_le]
    constructor <;> linarith
  set A : Fin n → ℝ := fun i => logExcess S (x i) / Q with hA
  set B : Fin n → ℝ := fun i => logExcess s (x i) / Q with hB
  set I : Fin n → ℝ := fun i => if lo < x i then 1 else 0 with hI
  have hI01 : ∀ i, 0 ≤ I i ∧ I i ≤ 1 := by
    intro i; simp only [hI]; split_ifs <;> norm_num
  have hA0 : ∀ i, 0 ≤ A i := fun i => div_nonneg (logExcess_nonneg hS0 _) hQ.le
  have hB0 : ∀ i, 0 ≤ B i := fun i => div_nonneg (logExcess_nonneg hs _) hQ.le
  have hAB : ∀ i, |A i - B i| ≤ η * I i := by
    intro i
    have := abs_logExcess_sub_logExcess_le (y := x i) hlo0 hSlo hlos
    simp only [hA, hB, hI]
    rw [← sub_div, abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
    calc |logExcess S (x i) - logExcess s (x i)|
        ≤ |Real.log S - Real.log s| * (if lo < x i then 1 else 0) := this
      _ ≤ Q * η * (if lo < x i then 1 else 0) := by
          gcongr
      _ = η * (if lo < x i then 1 else 0) * Q := by ring
  have hAB2 : ∀ i, |A i ^ 2 - B i ^ 2| ≤ η * (2 * B i + η) * I i := by
    intro i
    have h := hAB i
    rcases (hI01 i).1.lt_or_eq with hpos | hzero
    · have hI1 : I i = 1 := by
        by_cases hh : lo < x i
        · simp [hI, hh]
        · simp [hI, hh] at hpos
      rw [hI1, mul_one] at h ⊢
      rw [show A i ^ 2 - B i ^ 2 = (A i - B i) * (A i + B i) by ring, abs_mul,
        abs_of_nonneg (add_nonneg (hA0 i) (hB0 i))]
      have hAle : A i ≤ B i + η := by linarith [(abs_le.1 h).2]
      calc |A i - B i| * (A i + B i) ≤ η * (A i + B i) :=
            mul_le_mul_of_nonneg_right h (add_nonneg (hA0 i) (hB0 i))
        _ ≤ η * (2 * B i + η) := by nlinarith
    · rw [← hzero, mul_zero] at h ⊢
      have : A i = B i := by
        have := abs_nonneg (A i - B i)
        have h0 : |A i - B i| = 0 := le_antisymm h this
        linarith [abs_eq_zero.1 h0]
      rw [this, sub_self, abs_zero]
  have hcnt : (exceedCount x lo : ℝ) = ∑ i, I i := exceedCount_eq_sum x lo
  have hM1 : logMoment x k 1 / Q = (∑ i, A i) / k := by
    rw [logMoment_eq_sum_logExcess x one_ne_zero hk hS0, ← hS_def]
    simp only [pow_one, hA, ← Finset.sum_div]
    field_simp
  have hM2 : logMoment x k 2 / Q ^ 2 = (∑ i, A i ^ 2) / k := by
    rw [logMoment_eq_sum_logExcess x two_ne_zero hk hS0, ← hS_def]
    simp only [hA, div_pow, ← Finset.sum_div]
    field_simp
  have hsumI : (∑ i, I i) / k ≤ K := by rw [← hcnt]; exact h3
  constructor
  · rw [hM1, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hkR, div_le_iff₀ hkR]
    calc |∑ i, (A i - B i)| ≤ ∑ i, |A i - B i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, η * I i := Finset.sum_le_sum fun i _ => hAB i
      _ = η * ((∑ i, I i) / k) * k := by rw [← Finset.mul_sum]; field_simp
      _ ≤ η * K * k := by gcongr
  · rw [hM2, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hkR, div_le_iff₀ hkR]
    calc |∑ i, (A i ^ 2 - B i ^ 2)| ≤ ∑ i, |A i ^ 2 - B i ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, η * (2 * B i + η) * I i := Finset.sum_le_sum fun i _ => hAB2 i
      _ ≤ ∑ i, (η * 2 * B i + η * η * I i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := mul_nonneg (mul_nonneg hη.le (hB0 i)) (sub_nonneg.2 (hI01 i).2)
          nlinarith
      _ = η * (2 * ((∑ i, B i) / k) + η * ((∑ i, I i) / k)) * k := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          field_simp
      _ ≤ η * (2 * ((∑ i, B i) / k) + η * K) * k := by gcongr

end Deterministic

/-! ### Consistency of the normalized log-moments -/

section Consistency

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Weak consistency of the normalized log-moments**, in terms of the tail quantile function:
if `log U` is extended regularly varying with index `ρ ≤ 0` and auxiliary function `q`, monotone
on some `[c, ∞)`, `U` is eventually positive, and `k → ∞`, `k / n → 0`, then
`M^{(1)} / q(n/k) → 1 / (1 - ρ)` and `M^{(2)} / q(n/k)² → 2 / ((1 - ρ)(1 - 2ρ))` in
probability. -/
theorem tendstoInMeasure_logMoment_div_of_log_tailQuantile {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | X 0 ω ≤ x}).toReal)
    {ρ : ℝ} (hρ : ρ ≤ 0) {q : ℝ → ℝ}
    (hV : IsExtendedRegularlyVarying (fun t => Real.log (F.tailQuantile t)) ρ q) {c : ℝ}
    (hmono : MonotoneOn (fun t => Real.log (F.tailQuantile t)) (Ici c))
    (hU : ∀ᶠ t in atTop, 0 < F.tailQuantile t) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P
        (fun n ω => logMoment (fun i : Fin n => X i ω) (k n) 1 / q ((n : ℝ) / k n)) atTop
        (fun _ => 1 / (1 - ρ)) ∧
      TendstoInMeasure P
        (fun n ω => logMoment (fun i : Fin n => X i ω) (k n) 2 / q ((n : ℝ) / k n) ^ 2) atTop
        (fun _ => 2 / ((1 - ρ) * (1 - 2 * ρ))) := by
  set U := F.tailQuantile with hU_def
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  set t : ℕ → ℝ := fun n => (n : ℝ) / k n with ht_def
  have ht : Tendsto t atTop atTop := by
    have h1 : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hkn, ?_⟩
      filter_upwards [hkpos, hnpos] with n h1 h2
      exact div_pos h1 h2
    refine (tendsto_inv_nhdsGT_zero.comp h1).congr fun n => ?_
    simp only [Function.comp_apply, ht_def, inv_div]
  set s : ℕ → ℝ := fun n => U (t n) with hs_def
  set Q : ℕ → ℝ := fun n => q (t n) with hQ_def
  have hsQ : ∀ᶠ n in atTop, 0 < s n ∧ 0 < Q n := by
    filter_upwards [ht.eventually hU, ht.eventually hV.1] with n h1 h2
    exact ⟨h1, h2⟩
  have hkn' : ∀ᶠ n : ℕ in atTop, k n < n := by
    filter_upwards [hkn.eventually (gt_mem_nhds one_pos), hnpos] with n h1 h2
    rw [div_lt_one h2] at h1
    exact_mod_cast h1
  have hFbar : ∀ a, (P {ω | a < X 0 ω}).toReal = 1 - F a := by
    intro a
    have hc : {ω | a < X 0 ω} = {ω | X 0 ω ≤ a}ᶜ := by ext ω; simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_le (hX 0) measurable_const),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, hF]
  -- exceedance counts
  have hcount : ∀ x δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |(exceedCount (fun i : Fin n => X i ω) (Real.exp (Real.log (s n) + Q n * x)) : ℝ) / k n -
        gpdSurvival ρ 1 x|}) atTop (𝓝 0) := by
    intro x δ hδ
    refine tendsto_measure_abs_exceedCount_div_sub hX hindep hident hk ?_ hδ
    refine ((F.tendsto_mul_one_sub_exp_log_tailQuantile hρ hV hU x).comp ht).congr' ?_
    filter_upwards [hkpos] with n hn
    simp only [Function.comp_apply, hFbar, ht_def, hs_def, hQ_def]
    ring
  -- weak laws of large numbers at the deterministic threshold `U(n/k)`
  have hW : ∀ j : ℕ, 1 ≤ j → ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |(∑ i ∈ range n, (logExcess (s n) (X i ω) / Q n) ^ j) / k n - gpdMoment ρ j|})
      atTop (𝓝 0) := by
    intro j hj δ hδ
    obtain ⟨hI1, hL1⟩ := tendsto_mul_integral_logExcess_div_rpow (hX 0) hF hρ hV hmono hU
      (p := (j : ℝ)) (by exact_mod_cast hj)
    obtain ⟨hI2, hL2⟩ := tendsto_mul_integral_logExcess_div_rpow (hX 0) hF hρ hV hmono hU
      (p := ((2 * j : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ 2 * j by omega))
    have hsq : ∀ n ω, ((logExcess (s n) (X 0 ω) / Q n) ^ j) ^ 2 =
        (logExcess (s n) (X 0 ω) / Q n) ^ ((2 * j : ℕ) : ℝ) := by
      intro n ω
      rw [rpow_natCast, ← pow_mul, mul_comm]
    refine tendsto_measure_abs_sum_div_sub hindep hident
      (g := fun n y => (logExcess (s n) y / Q n) ^ j)
      (fun n => ((measurable_logExcess _).div_const _).pow_const _) hkpos ?_ ?_ ?_ hδ
    · filter_upwards [ht.eventually hI2] with n hn
      refine (memLp_two_iff_integrable_sq
        ((((measurable_logExcess _).comp (hX 0)).div_const _).pow_const _).aestronglyMeasurable).2
        ?_
      refine hn.congr (Eventually.of_forall fun ω => ?_)
      exact (hsq n ω).symm
    · refine (hL1.comp ht).congr' ?_
      filter_upwards [hkpos] with n hn
      simp only [Function.comp_apply, ht_def, hs_def, hQ_def, rpow_natCast]
      ring
    · have := (hL2.comp ht).mul (tendsto_inv_atTop_zero.comp hkR)
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [hkpos] with n hn
      simp only [Function.comp_apply, ht_def, hs_def, hQ_def]
      field_simp
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun ω => (hsq n ω).symm)
  have hW1 := hW 1 le_rfl
  have hW2 := hW 2 (by norm_num)
  simp only [pow_one] at hW1
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num, gpdMoment_one hρ] at hW1
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, gpdMoment_two hρ] at hW2
  -- the main estimate
  set μ₁ : ℝ := 1 / (1 - ρ) with hμ₁
  set μ₂ : ℝ := 2 / ((1 - ρ) * (1 - 2 * ρ)) with hμ₂
  have hμ₁0 : 0 < μ₁ := by rw [hμ₁]; have : 0 < 1 - ρ := by linarith
                           positivity
  set K : ℝ := 3 with hK
  have main : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ε ≤
        |logMoment (fun i : Fin n => X i ω) (k n) 1 / Q n - μ₁|}) atTop (𝓝 0) ∧
      Tendsto (fun n => P {ω | ε ≤
        |logMoment (fun i : Fin n => X i ω) (k n) 2 / Q n ^ 2 - μ₂|}) atTop (𝓝 0) := by
    intro ε hε
    set C' : ℝ := 2 * (μ₁ + 1) + K with hC'
    have hC'0 : 0 < C' := by rw [hC', hK]; linarith
    have hG : Tendsto (fun η : ℝ => gpdSurvival ρ 1 (-η)) (𝓝 0) (𝓝 1) := by
      have h := ((continuous_gpdSurvival_of_nonpos hρ).comp continuous_neg).tendsto 0
      have e : (gpdSurvival ρ 1 ∘ fun a : ℝ => -a) 0 = 1 := by
        simp [gpdSurvival_zero]
      rw [e] at h
      exact h
    have e1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), gpdSurvival ρ 1 (-η) < 2 :=
      (hG.eventually (gt_mem_nhds one_lt_two)).filter_mono nhdsWithin_le_nhds
    have e2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ≤ 1 :=
      (eventually_le_nhds one_pos).filter_mono nhdsWithin_le_nhds
    have e3 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η * C' < ε / 2 := by
      have : Tendsto (fun η : ℝ => η * C') (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const C'
      exact (this.eventually (gt_mem_nhds (half_pos hε))).filter_mono nhdsWithin_le_nhds
    obtain ⟨η, h1, h2, h3, hη⟩ := (e1.and (e2.and (e3.and self_mem_nhdsWithin))).exists
    have hη0 : 0 < η := hη
    set Gp := gpdSurvival ρ 1 η with hGp
    set Gm := gpdSurvival ρ 1 (-η) with hGm
    have hGp1 : Gp < 1 := gpdSurvival_lt_one hη0
    have hGm1 : 1 < Gm := one_lt_gpdSurvival_of_neg hρ (by linarith)
    have hδp : 0 < 1 - Gp := by linarith
    have hδm : 0 < min (Gm - 1) 1 := lt_min (by linarith) one_pos
    have hδ1 : 0 < min (ε / 2) 1 := lt_min (half_pos hε) one_pos
    have Lhi := hcount η (1 - Gp) hδp
    have Llo := hcount (-η) (min (Gm - 1) 1) hδm
    have LW1 := hW1 (min (ε / 2) 1) hδ1
    have LW2 := hW2 (ε / 2) (half_pos hε)
    -- the deterministic consequences on the good event
    have good : ∀ n, k n < n → (0 : ℝ) < k n → 0 < s n → 0 < Q n → ∀ ω,
        |(exceedCount (fun i : Fin n => X i ω) (Real.exp (Real.log (s n) + Q n * η)) : ℝ) /
          k n - Gp| < 1 - Gp →
        |(exceedCount (fun i : Fin n => X i ω) (Real.exp (Real.log (s n) + Q n * -η)) : ℝ) /
          k n - Gm| < min (Gm - 1) 1 →
        |(∑ i ∈ range n, logExcess (s n) (X i ω) / Q n) / k n - μ₁| < min (ε / 2) 1 →
        |logMoment (fun i : Fin n => X i ω) (k n) 1 / Q n - μ₁| < ε ∧
          (|(∑ i ∈ range n, (logExcess (s n) (X i ω) / Q n) ^ 2) / k n - μ₂| < ε / 2 →
            |logMoment (fun i : Fin n => X i ω) (k n) 2 / Q n ^ 2 - μ₂| < ε) := by
      intro n hkn hk0 hs hQ ω c1 c2 c3
      have hk0' : 0 < k n := by exact_mod_cast hk0
      have d1 : (exceedCount (fun i : Fin n => X i ω) (Real.exp (Real.log (s n) + Q n * η)) : ℝ)
          / k n < 1 := by linarith [(abs_lt.1 c1).2]
      have d2 : 1 < (exceedCount (fun i : Fin n => X i ω)
          (Real.exp (Real.log (s n) + Q n * -η)) : ℝ) / k n := by
        linarith [(abs_lt.1 c2).1, min_le_left (Gm - 1) 1]
      have d3 : (exceedCount (fun i : Fin n => X i ω)
          (Real.exp (Real.log (s n) + Q n * -η)) : ℝ) / k n ≤ K := by
        rw [hK]
        linarith [(abs_lt.1 c2).2, min_le_right (Gm - 1) 1]
      obtain ⟨b1, b2⟩ := abs_logMoment_div_sub_le (fun i : Fin n => X i ω) hkn hk0' hs hQ hη0
        d1 d2 d3
      have hS1 : ∑ i : Fin n, logExcess (s n) (X i ω) / Q n =
          ∑ i ∈ range n, logExcess (s n) (X i ω) / Q n :=
        Fin.sum_univ_eq_sum_range (fun i => logExcess (s n) (X i ω) / Q n) n
      have hS2 : ∑ i : Fin n, (logExcess (s n) (X i ω) / Q n) ^ 2 =
          ∑ i ∈ range n, (logExcess (s n) (X i ω) / Q n) ^ 2 :=
        Fin.sum_univ_eq_sum_range (fun i => (logExcess (s n) (X i ω) / Q n) ^ 2) n
      rw [hS1] at b1 b2
      rw [hS2] at b2
      have c3' := abs_lt.1 c3
      have hm1 := min_le_left (ε / 2) 1
      have hm2 := min_le_right (ε / 2) 1
      have hηK : η * K ≤ η * C' := by
        rw [hC']
        have : 0 ≤ 2 * (μ₁ + 1) := by linarith
        nlinarith
      refine ⟨?_, fun c4 => ?_⟩
      · calc |logMoment (fun i : Fin n => X i ω) (k n) 1 / Q n - μ₁|
            ≤ |logMoment (fun i : Fin n => X i ω) (k n) 1 / Q n -
                (∑ i ∈ range n, logExcess (s n) (X i ω) / Q n) / k n| +
              |(∑ i ∈ range n, logExcess (s n) (X i ω) / Q n) / k n - μ₁| :=
              abs_sub_le _ _ _
          _ < η * C' + ε / 2 := by
              have := abs_lt.2 c3'
              linarith
          _ < ε := by linarith
      · have hW1b : (∑ i ∈ range n, logExcess (s n) (X i ω) / Q n) / k n ≤ μ₁ + 1 := by
          linarith [c3'.2]
        have hb2' : η * (2 * ((∑ i ∈ range n, logExcess (s n) (X i ω) / Q n) / k n) + η * K) ≤
            η * C' := by
          rw [hC']
          have : η * K ≤ K := by rw [hK]; nlinarith
          have : 2 * ((∑ i ∈ range n, logExcess (s n) (X i ω) / Q n) / k n) ≤ 2 * (μ₁ + 1) := by
            linarith
          nlinarith
        calc |logMoment (fun i : Fin n => X i ω) (k n) 2 / Q n ^ 2 - μ₂|
            ≤ |logMoment (fun i : Fin n => X i ω) (k n) 2 / Q n ^ 2 -
                (∑ i ∈ range n, (logExcess (s n) (X i ω) / Q n) ^ 2) / k n| +
              |(∑ i ∈ range n, (logExcess (s n) (X i ω) / Q n) ^ 2) / k n - μ₂| :=
              abs_sub_le _ _ _
          _ < η * C' + ε / 2 := by linarith
          _ < ε := by linarith
    constructor
    · have hlim := (Lhi.add Llo).add LW1
      simp only [add_zero] at hlim
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [hkn', hkpos, hsQ] with n hkn hk0 hsQn
      refine (measure_mono ?_).trans ((measure_union_le _ _).trans
        (add_le_add_left (measure_union_le _ _) _))
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
      obtain ⟨⟨c1, c2⟩, c3⟩ := hcon
      exact absurd hω (not_le.2 (good n hkn hk0 hsQn.1 hsQn.2 ω c1 c2 c3).1)
    · have hlim := ((Lhi.add Llo).add LW1).add LW2
      simp only [add_zero] at hlim
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [hkn', hkpos, hsQ] with n hkn hk0 hsQn
      refine (measure_mono ?_).trans ((measure_union_le _ _).trans
        (add_le_add_left ((measure_union_le _ _).trans
          (add_le_add_left (measure_union_le _ _) _)) _))
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
      obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hcon
      exact absurd hω (not_le.2 ((good n hkn hk0 hsQn.1 hsQn.2 ω c1 c2 c3).2 c4))
  refine ⟨?_, ?_⟩
  · rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simpa only [Real.dist_eq] using (main ε hε).1
  · rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simpa only [Real.dist_eq] using (main ε hε).2

omit [IsProbabilityMeasure P] in
/-- Convergence in probability to a constant only depends on the random variables for large
indices. -/
theorem tendstoInMeasure_congr_eventually {ι : Type*} {l : Filter ι} {f g : ι → Ω → ℝ} {a : ℝ}
    (hg : TendstoInMeasure P g l (fun _ => a)) (h : ∀ᶠ n in l, ∀ ω, f n ω = g n ω) :
    TendstoInMeasure P f l (fun _ => a) :=
  tendstoInMeasure_of_eventuallyEq hg h

omit [IsProbabilityMeasure P] in
/-- If `f_n → a` in probability and the deterministic `c_n → c`, then `c_n f_n → c a` in
probability. -/
theorem tendstoInMeasure_const_mul_of_tendsto {ι : Type*} {l : Filter ι} {f : ι → Ω → ℝ}
    {a c : ℝ} {cn : ι → ℝ} (hf : TendstoInMeasure P f l (fun _ => a))
    (hc : Tendsto cn l (𝓝 c)) :
    TendstoInMeasure P (fun n ω => cn n * f n ω) l (fun _ => c * a) :=
  tendstoInMeasure_mul (tendstoInMeasure_const_of_tendsto hc) hf

/-- For an intermediate sequence (`k → ∞`, `k / n → 0`), `n / k → ∞`. -/
theorem tendsto_div_atTop_of_intermediate {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop atTop := by
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have h1 : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hkn, ?_⟩
    filter_upwards [hkpos, hnpos] with n h1 h2
    exact div_pos h1 h2
  refine (tendsto_inv_nhdsGT_zero.comp h1).congr fun n => ?_
  simp only [Function.comp_apply, inv_div]

/-- **Weak consistency of the log-moments for every extreme value index** ([dHF, Lemma 3.5.1
and the proof of Theorem 3.5.2]). Let `X_0, X_1, …` be iid with c.d.f. `F ∈ MDA(H_γ)`, `γ ∈ ℝ`,
with positive right endpoint `U(∞) = x_F > 0`, and let `k(n) → ∞`, `k(n) / n → 0`. Then for the
auxiliary function `a` of the extended regular variation of the tail quantile function `U`,
`M^{(1)} U(n/k) / a(n/k) → 1 / (1 - γ₋)` and
`M^{(2)} (U(n/k) / a(n/k))² → 2 / ((1 - γ₋)(1 - 2γ₋))` in probability, `γ₋ = min γ 0`. -/
theorem tendstoInMeasure_logMoment_of_isInMDAGEV {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | X 0 ω ≤ x}).toReal)
    {γ : ℝ} (hMDA : F.IsInMDAGEV γ) (hxF : ∃ y, 0 < y ∧ F y < 1) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    ∃ a : ℝ → ℝ, IsExtendedRegularlyVarying F.tailQuantile γ a ∧
      TendstoInMeasure P (fun n ω => logMoment (fun i : Fin n => X i ω) (k n) 1 *
          F.tailQuantile ((n : ℝ) / k n) / a ((n : ℝ) / k n)) atTop
        (fun _ => 1 / (1 - min γ 0)) ∧
      TendstoInMeasure P (fun n ω => logMoment (fun i : Fin n => X i ω) (k n) 2 *
          (F.tailQuantile ((n : ℝ) / k n) / a ((n : ℝ) / k n)) ^ 2) atTop
        (fun _ => 2 / ((1 - min γ 0) * (1 - 2 * min γ 0))) := by
  obtain ⟨a, ha, hpos, ⟨c, hmono⟩, hV, -⟩ :=
    F.exists_isExtendedRegularlyVarying_log_tailQuantile hMDA hxF
  obtain ⟨h1, h2⟩ := tendstoInMeasure_logMoment_div_of_log_tailQuantile hX hindep hident hF
    (min_le_right γ 0) hV hmono hpos hk hkn
  refine ⟨a, ha, tendstoInMeasure_congr_eventually h1 (Eventually.of_forall fun n ω => ?_),
    tendstoInMeasure_congr_eventually h2 (Eventually.of_forall fun n ω => ?_)⟩
  · rw [div_div_eq_mul_div]
  · rw [div_pow, div_pow, div_div_eq_mul_div, mul_div_assoc]

/-- **Weak consistency of the moment estimator for every extreme value index** (Dekkers,
Einmahl and de Haan 1989; [dHF, Theorem 3.5.2]). Let `X_0, X_1, …` be iid with c.d.f.
`F ∈ MDA(H_γ)`, `γ ∈ ℝ`, with positive right endpoint `x_F > 0`, and let `k(n) → ∞`,
`k(n) / n → 0`. Then the moment estimator `γ̂_M` converges to `γ` in probability. -/
theorem tendstoInMeasure_momentEstimator_of_isInMDAGEV' {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {F : CumulativeDistributionFunction} (hF : ∀ x, F x = (P {ω | X 0 ω ≤ x}).toReal)
    {γ : ℝ} (hMDA : F.IsInMDAGEV γ) (hxF : ∃ y, 0 < y ∧ F y < 1) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => momentEstimator (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => γ) := by
  obtain ⟨a, -, hpos, ⟨c, hmono⟩, hV, hqlim⟩ :=
    F.exists_isExtendedRegularlyVarying_log_tailQuantile hMDA hxF
  set ρ := min γ 0 with hρ_def
  have hρ : ρ ≤ 0 := min_le_right γ 0
  obtain ⟨h1, h2⟩ := tendstoInMeasure_logMoment_div_of_log_tailQuantile hX hindep hident hF
    hρ hV hmono hpos hk hkn
  set q : ℝ → ℝ := fun t => a t / F.tailQuantile t with hq_def
  have ht := tendsto_div_atTop_of_intermediate hk hkn
  set μ₁ : ℝ := 1 / (1 - ρ) with hμ₁
  set μ₂ : ℝ := 2 / ((1 - ρ) * (1 - 2 * ρ)) with hμ₂
  have h1ρ : 0 < 1 - ρ := by linarith
  have h2ρ : 0 < 1 - 2 * ρ := by linarith
  have hμ₂0 : μ₂ ≠ 0 := by rw [hμ₂]; positivity
  have hratio : 1 - μ₁ ^ 2 / μ₂ = 1 / (2 * (1 - ρ)) := by
    rw [hμ₁, hμ₂]
    field_simp
    ring
  -- `A²/B → μ₁² / μ₂`
  have hAB := tendstoInMeasure_comp₂ h1 h2 (φ := fun p => p.1 ^ 2 / p.2)
    ((continuousAt_fst.pow 2).div continuousAt_snd hμ₂0)
  -- `q_n A → γ₊ μ₁`
  have hqA := tendstoInMeasure_const_mul_of_tendsto h1 (hqlim.comp ht)
  have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 + 1 - 1 / 2 * (1 - p.2)⁻¹)
      (max γ 0 * μ₁, μ₁ ^ 2 / μ₂) := by
    refine (continuousAt_fst.add continuousAt_const).sub (continuousAt_const.mul
      ((continuousAt_const.sub continuousAt_snd).inv₀ ?_))
    change 1 - μ₁ ^ 2 / μ₂ ≠ 0
    rw [hratio]
    positivity
  have hE := tendstoInMeasure_comp₂ hqA hAB hcont
  have hval : max γ 0 * μ₁ + 1 - 1 / 2 * (1 - μ₁ ^ 2 / μ₂)⁻¹ = γ := by
    rw [hratio, hμ₁]
    rcases le_or_gt γ 0 with hγ | hγ
    · rw [max_eq_right hγ, hρ_def, min_eq_left hγ]
      field_simp
      ring
    · rw [max_eq_left hγ.le, hρ_def, min_eq_right hγ.le]
      norm_num
  beta_reduce at hE
  rw [hval] at hE
  refine tendstoInMeasure_congr_eventually hE ?_
  filter_upwards [ht.eventually hV.1] with n hn ω
  simp only [momentEstimator, Function.comp_apply]
  have hq : q ((n : ℝ) / k n) ≠ 0 := hn.ne'
  congr 2
  · rw [mul_comm, div_mul_cancel₀ _ hq]
  · rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 hq)]

end Consistency

/-! Deprecated names from when the all-shape GPD survival function was `gpdSurvival'`. -/

@[deprecated (since := "2026-10-23")] alias continuous_gpdSurvival'_of_nonpos := continuous_gpdSurvival_of_nonpos
@[deprecated (since := "2026-10-23")] alias one_lt_gpdSurvival'_of_neg := one_lt_gpdSurvival_of_neg

end ExtremeValueTheory
