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

theorem continuous_gpdSurvival'_of_nonpos (hρ : ρ ≤ 0) : Continuous (gpdSurvival' ρ 1) := by
  rcases hρ.lt_or_eq with hρ' | hρ'
  · have : gpdSurvival' ρ 1 = fun x => (max (1 + ρ * x) 0) ^ (-(1 / ρ)) := by
      funext x; exact gpdSurvival'_one_of_ne hρ'.ne x
    rw [this]
    have hp : 0 < -(1 / ρ) := by
      have : 1 / ρ < 0 := one_div_neg.2 hρ'
      linarith
    exact (continuous_const.add (continuous_const.mul continuous_id)).max continuous_const
      |>.rpow_const fun _ => Or.inr hp.le
  · subst hρ'
    have : gpdSurvival' 0 1 = fun x => Real.exp (-x / 1) := by
      funext x; exact gpdSurvival'_zero_left 1 x
    rw [this]
    fun_prop

theorem one_lt_gpdSurvival'_of_neg (hρ : ρ ≤ 0) {x : ℝ} (hx : x < 0) :
    1 < gpdSurvival' ρ 1 x := by
  rcases hρ.lt_or_eq with hρ' | hρ'
  · rw [gpdSurvival'_one_of_ne hρ'.ne]
    have hb : 1 < 1 + ρ * x := by nlinarith
    rw [max_eq_left (by linarith)]
    exact one_lt_rpow hb (by have : 1 / ρ < 0 := one_div_neg.2 hρ'; linarith)
  · subst hρ'
    rw [gpdSurvival'_zero_left, div_one]
    exact Real.one_lt_exp_iff.2 (by linarith)

/-- The `p`-th moment `p ∫_0^∞ z ^ (p - 1) Ḡ_{ρ,1}(z) dz` of the generalized Pareto
distribution with shape `ρ` (layer cake form). -/
noncomputable def gpdMoment (ρ p : ℝ) : ℝ :=
  p * ∫ z in Ioi 0, z ^ (p - 1) * gpdSurvival' ρ 1 z

/-- For `ρ < 0` the integrand of `gpdMoment` vanishes beyond the right endpoint `-1/ρ`. -/
private lemma integral_Ioi_eq_intervalIntegral (hρ : ρ < 0) (g : ℝ → ℝ) :
    ∫ z in Ioi 0, g z * gpdSurvival' ρ 1 z = ∫ z in (0 : ℝ)..(-1 / ρ), g z * (1 + ρ * z) ^ (-(1 / ρ)) := by
  have he : 0 < -1 / ρ := div_pos_of_neg_of_neg (by norm_num) hρ
  have hp : 0 < -(1 / ρ) := by
    have : 1 / ρ < 0 := one_div_neg.2 hρ
    linarith
  rw [intervalIntegral.integral_of_le he.le,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
    rw [gpdSurvival'_one_of_ne hρ.ne, max_eq_left]
    have := hz.2
    rw [le_div_iff_of_neg hρ] at this
    linarith
  · intro z hz
    have h1 : -1 / ρ < z := by
      by_contra h
      exact hz.2 ⟨hz.1, not_lt.1 h⟩
    rw [div_lt_iff_of_neg hρ] at h1
    rw [gpdSurvival'_one_of_ne hρ.ne, max_eq_right (by linarith), zero_rpow hp.ne', mul_zero]

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
    simp only [gpdSurvival'_zero_left, div_one, sub_self, rpow_zero, one_mul]
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
    simp only [gpdSurvival'_zero_left, div_one]
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
      _ ≤ C * (1 + z ^ 2)⁻¹ := by
          by_cases hC0 : C = 0
          · rw [hC0, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left h2 (by
              by_contra hcon; push Not at hcon
              have h3 : 0 ≤ t * survival P Y (U t * Real.exp (q t * z)) :=
                mul_nonneg (by linarith) (survival_nonneg _)
              have h4 : 0 < (1 + z) ^ (-(p + 1)) := rpow_pos_of_pos (by linarith) _
              nlinarith)
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
    (f := fun z => z ^ (p - 1) * gpdSurvival' ρ 1 z) (fun z => C * (1 + z ^ 2)⁻¹) ?_ ?_ ?_ ?_
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

end ExtremeValueTheory
