/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.SREExponent

/-!
# GARCH(1,1) and ARCH(1): the squared volatility as a stochastic recurrence

skeleton
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped ENNReal

namespace ExtremeValueTheory

namespace SRE

namespace GARCH

variable (α₀ α₁ β₁ : ℝ)

/-- The random multiplier `A = α₁ Z² + β₁` of the squared volatility recursion. -/
def coeff (z : ℝ) : ℝ := α₁ * z ^ 2 + β₁

/-- The innovation map `z ↦ (α₁ z² + β₁, α₀)`. -/
def innov (z : ℝ) : ℝ × ℝ := (coeff α₁ β₁ z, α₀)

/-- The law of the coefficients `(A, B) = (α₁ Z² + β₁, α₀)` for `Z ∼ ζ`. -/
noncomputable def coeffLaw (ζ : Measure ℝ) : Measure (ℝ × ℝ) := ζ.map (innov α₀ α₁ β₁)

theorem measurable_coeff : Measurable (coeff α₁ β₁) := by unfold coeff; fun_prop

theorem measurable_innov : Measurable (innov α₀ α₁ β₁) := by
  unfold innov; exact (measurable_coeff α₁ β₁).prodMk measurable_const

/-- **The GARCH(1,1) squared volatility recursion** `σ²_{t+1} = α₀ + (α₁ Z_t² + β₁) σ²_t` is the
stochastic recurrence `X_{t+1} = A_t X_t + B_t` with `(A_t, B_t) = (α₁ Z_t² + β₁, α₀)`. -/
theorem affine_innov (x z : ℝ) :
    affine x (innov α₀ α₁ β₁ z) = α₀ + (α₁ * z ^ 2 + β₁) * x := by
  simp only [affine, innov, coeff]; ring

variable {α₀ α₁ β₁}

theorem coeff_nonneg (hα₁ : 0 ≤ α₁) (hβ₁ : 0 ≤ β₁) (z : ℝ) : 0 ≤ coeff α₁ β₁ z := by
  unfold coeff; positivity

variable {ζ : Measure ℝ} [IsProbabilityMeasure ζ]

instance : IsProbabilityMeasure (coeffLaw α₀ α₁ β₁ ζ) := by
  unfold coeffLaw; infer_instance

/-! ### Transfer of the hypotheses from `Z` to `(A, B)` -/

section Transfer

omit [IsProbabilityMeasure ζ] in
theorem integrable_log_coeffLaw (hlog : Integrable (fun z => log (coeff α₁ β₁ z)) ζ) :
    Integrable (fun p : ℝ × ℝ => log |p.1|) (coeffLaw α₀ α₁ β₁ ζ) := by
  rw [coeffLaw, integrable_map_measure
    (by fun_prop : Measurable fun p : ℝ × ℝ => log |p.1|).aestronglyMeasurable
    (measurable_innov α₀ α₁ β₁).aemeasurable]
  refine hlog.congr (ae_of_all _ fun z => ?_)
  simp [innov]

omit [IsProbabilityMeasure ζ] in
theorem integral_log_coeffLaw :
    ∫ p, log |p.1| ∂(coeffLaw α₀ α₁ β₁ ζ) = ∫ z, log (coeff α₁ β₁ z) ∂ζ := by
  rw [coeffLaw, integral_map (measurable_innov α₀ α₁ β₁).aemeasurable
    (by fun_prop : Measurable fun p : ℝ × ℝ => log |p.1|).aestronglyMeasurable]
  simp [innov]

omit [IsProbabilityMeasure ζ] in
theorem lintegral_rpow_coeffLaw (hα₁ : 0 ≤ α₁) (hβ₁ : 0 ≤ β₁) {κ : ℝ} (hκ : 0 ≤ κ)
    (hi : Integrable (fun z => coeff α₁ β₁ z ^ κ) ζ) :
    ∫⁻ p, ‖p.1‖ₑ ^ κ ∂(coeffLaw α₀ α₁ β₁ ζ) = ENNReal.ofReal (∫ z, coeff α₁ β₁ z ^ κ ∂ζ) := by
  rw [coeffLaw, lintegral_map (by fun_prop) (measurable_innov α₀ α₁ β₁),
    ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun z => rpow_nonneg (coeff_nonneg hα₁ hβ₁ z) _)]
  refine lintegral_congr fun z => ?_
  rw [enorm_rpow_eq_ofReal _ hκ]
  simp [innov, abs_of_nonneg (coeff_nonneg hα₁ hβ₁ z)]

end Transfer

omit [IsProbabilityMeasure ζ] in
theorem ae_coeffLaw_iff {P : ℝ × ℝ → Prop} (hP : MeasurableSet {p | P p}) :
    (∀ᵐ p ∂(coeffLaw α₀ α₁ β₁ ζ), P p) ↔ ∀ᵐ z ∂ζ, P (innov α₀ α₁ β₁ z) :=
  ae_map_iff (measurable_innov α₀ α₁ β₁).aemeasurable hP


theorem integrable_posLog_coeffLaw :
    Integrable (fun p : ℝ × ℝ => posLog p.2) (coeffLaw α₀ α₁ β₁ ζ) := by
  rw [coeffLaw, integrable_map_measure (g := fun p : ℝ × ℝ => posLog p.2)
    (continuous_posLog.measurable.comp measurable_snd).aestronglyMeasurable
    (measurable_innov α₀ α₁ β₁).aemeasurable]
  exact integrable_const (posLog α₀)

/-! ### Stationarity -/

section Main

variable (hα₁ : 0 ≤ α₁) (hβ₁ : 0 ≤ β₁)
  (hlog : Integrable (fun z => log (coeff α₁ β₁ z)) ζ)
  (hneg : ∫ z, log (coeff α₁ β₁ z) ∂ζ < 0)

include hlog hneg

/-- **Strict stationarity of GARCH(1,1)** ([Nelson 1990]; [Bougerol–Picard 1992];
[BDM16, §4.3]): if `E log(α₁ Z² + β₁) < 0`, the squared volatility recursion
`σ²_{t+1} = α₀ + (α₁ Z_t² + β₁) σ²_t`, started from the law of
`σ² = α₀ ∑_{k ≥ 0} ∏_{i < k} (α₁ Z_i² + β₁)` independently of the iid innovations `Z_t ∼ ζ`, is a
strictly stationary Markov chain. -/
theorem isStationary :
    IsStationary (RandomIteration.chain affine Prod.fst fun n (p : ℝ × (ℕ → ℝ × ℝ)) => p.2 n)
      (RandomIteration.canonicalMeasure (stationaryLaw (coeffLaw α₀ α₁ β₁ ζ))
        (coeffLaw α₀ α₁ β₁ ζ)) :=
  isStationary_chain (integrable_log_coeffLaw hlog) (by rwa [integral_log_coeffLaw])
    integrable_posLog_coeffLaw

/-- **Uniqueness of the stationary GARCH(1,1) volatility law**: under `E log(α₁ Z² + β₁) < 0`,
any law `π'` with `σ² =ᵈ α₀ + (α₁ Z² + β₁) σ²`, `σ² ⊥ Z`, is the stationary law. -/
theorem eq_stationaryLaw' (π' : Measure ℝ) [IsProbabilityMeasure π']
    (hinv : (π'.prod (coeffLaw α₀ α₁ β₁ ζ)).map (Function.uncurry affine) = π') :
    π' = stationaryLaw (coeffLaw α₀ α₁ β₁ ζ) :=
  eq_stationaryLaw (integrable_log_coeffLaw hlog) (by rwa [integral_log_coeffLaw])
    integrable_posLog_coeffLaw π' hinv

include hα₁ hβ₁

/-- **Moments of the GARCH(1,1) squared volatility below the tail index** ([BDM16, Theorem
4.3.1]; [EKM, §8.4]): if `E (α₁ Z² + β₁)^κ = 1` for `κ > 0` (with `α₁ Z² + β₁` not a.s. `1`),
then the stationary squared volatility has `E σ^{2s} < ∞` for every `0 < s < κ`. -/
theorem lintegral_rpow_lt_top {κ : ℝ} (hκ : 0 < κ)
    (hκi : Integrable (fun z => coeff α₁ β₁ z ^ κ) ζ) (hκ1 : ∫ z, coeff α₁ β₁ z ^ κ ∂ζ = 1)
    (hnd : ¬ ∀ᵐ z ∂ζ, coeff α₁ β₁ z = 1) {s : ℝ} (hs : 0 < s) (hsκ : s < κ) :
    ∫⁻ x, ‖x‖ₑ ^ s ∂stationaryLaw (coeffLaw α₀ α₁ β₁ ζ) < ∞ := by
  refine lintegral_enorm_rpow_stationaryLaw_lt_top_of_lt (integrable_log_coeffLaw hlog)
    (by rwa [integral_log_coeffLaw]) integrable_posLog_coeffLaw hκ ?_ ?_ ?_ hs hsκ
  · rw [lintegral_rpow_coeffLaw hα₁ hβ₁ hκ.le hκi, hκ1, ENNReal.ofReal_one]
  · rw [ae_coeffLaw_iff (measurableSet_eq_fun (by fun_prop) measurable_const)]
    simpa only [innov, abs_of_nonneg (coeff_nonneg hα₁ hβ₁ _)] using hnd
  · rw [coeffLaw, lintegral_map (by fun_prop) (measurable_innov α₀ α₁ β₁)]
    simpa [innov] using ENNReal.rpow_lt_top_of_nonneg hκ.le enorm_ne_top

/-- **Infinite moments of the GARCH(1,1) squared volatility above the tail index**: with
`α₀ > 0` and `κ` as in `lintegral_rpow_lt_top`, `E σ^{2s} = ∞` for every `s > κ`. Hence the
tail index of `σ²` is exactly the solution `κ` of `E (α₁ Z² + β₁)^κ = 1`. -/
theorem lintegral_rpow_eq_top (hα₀ : 0 < α₀) {κ : ℝ} (hκ : 0 < κ)
    (hκi : Integrable (fun z => coeff α₁ β₁ z ^ κ) ζ) (hκ1 : ∫ z, coeff α₁ β₁ z ^ κ ∂ζ = 1)
    (hnd : ¬ ∀ᵐ z ∂ζ, coeff α₁ β₁ z = 1) {s : ℝ} (hsκ : κ < s) :
    ∫⁻ x, ‖x‖ₑ ^ s ∂stationaryLaw (coeffLaw α₀ α₁ β₁ ζ) = ∞ := by
  refine lintegral_enorm_rpow_stationaryLaw_eq_top_of_lt (integrable_log_coeffLaw hlog)
    (by rwa [integral_log_coeffLaw]) integrable_posLog_coeffLaw ?_ ?_ ?_ hκ ?_ ?_ hsκ
  · rw [ae_coeffLaw_iff (measurableSet_le measurable_const measurable_fst)]
    exact ae_of_all _ fun z => coeff_nonneg hα₁ hβ₁ z
  · rw [ae_coeffLaw_iff (measurableSet_le measurable_const measurable_snd)]
    exact ae_of_all _ fun z => hα₀.le
  · rw [ae_coeffLaw_iff (measurableSet_eq_fun measurable_snd measurable_const)]
    simpa [innov, hα₀.ne'] using IsProbabilityMeasure.ne_zero ζ
  · rw [lintegral_rpow_coeffLaw hα₁ hβ₁ hκ.le hκi, hκ1, ENNReal.ofReal_one]
  · rw [ae_coeffLaw_iff (measurableSet_eq_fun (by fun_prop) measurable_const)]
    simpa only [innov, abs_of_nonneg (coeff_nonneg hα₁ hβ₁ _)] using hnd

/-- **Tail bounds for the GARCH(1,1) squared volatility**: `P(σ² > x) = O(x^{-s})` for every
`s < κ`, but `P(σ² > x) ≠ O(x^{-s})` for every `s > κ`. -/
theorem tail_bounds (hα₀ : 0 < α₀) {κ : ℝ} (hκ : 0 < κ)
    (hκi : Integrable (fun z => coeff α₁ β₁ z ^ κ) ζ) (hκ1 : ∫ z, coeff α₁ β₁ z ^ κ ∂ζ = 1)
    (hnd : ¬ ∀ᵐ z ∂ζ, coeff α₁ β₁ z = 1) :
    (∀ s, 0 < s → s < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      stationaryLaw (coeffLaw α₀ α₁ β₁ ζ) {y | x < |y|} ≤ ENNReal.ofReal (C * x ^ (-s))) ∧
    (∀ s, κ < s → ¬ ∃ C x₀ : ℝ, 0 ≤ C ∧ 0 < x₀ ∧ ∀ x, x₀ ≤ x →
      stationaryLaw (coeffLaw α₀ α₁ β₁ ζ) {y | x < |y|} ≤ ENNReal.ofReal (C * x ^ (-s))) := by
  refine ⟨fun s hs hsκ => exists_measure_lt_abs_le_of_lintegral_lt_top hs
    (lintegral_rpow_lt_top hα₁ hβ₁ hlog hneg hκ hκi hκ1 hnd hs hsκ),
    fun s hsκ ⟨C, x₀, hC, hx₀, h⟩ => ?_⟩
  have hr : κ < (κ + s) / 2 := by linarith
  have hfin := lintegral_lt_top_of_measure_lt_abs_le (r := (κ + s) / 2) (by linarith)
    (by linarith) hC hx₀ h
  rw [lintegral_rpow_eq_top hα₁ hβ₁ hlog hneg hα₀ hκ hκi hκ1 hnd hr] at hfin
  exact lt_irrefl _ hfin

omit hlog hneg in
/-- **Existence of the GARCH(1,1) tail index** ([BDM16, Theorem 4.3.1]; [Mikosch–Stărică 2000]):
if `α₁ Z² + β₁ ≠ 0` a.s., `E log(α₁ Z² + β₁) < 0`, and `E (α₁ Z² + β₁)^S > 1` for some `S > 0`
with `E (α₁ Z² + β₁)^S < ∞` (for instance for Gaussian `Z` and `α₁ > 0`), then there is a
`κ ∈ (0, S)` with `E (α₁ Z² + β₁)^κ = 1`; it is unique when `α₁ Z² + β₁` is not a.s. `1`
(`kesten_exponent_unique`). -/
theorem exists_tail_index (hlog : Integrable (fun z => log (coeff α₁ β₁ z)) ζ)
    (hneg : ∫ z, log (coeff α₁ β₁ z) ∂ζ < 0) (hA0 : ∀ᵐ z ∂ζ, coeff α₁ β₁ z ≠ 0) {S : ℝ}
    (hS : 0 < S) (hSi : Integrable (fun z => coeff α₁ β₁ z ^ S) ζ)
    (hS1 : 1 < ∫ z, coeff α₁ β₁ z ^ S ∂ζ) :
    ∃ κ ∈ Ioo 0 S, Integrable (fun z => coeff α₁ β₁ z ^ κ) ζ ∧
      ∫ z, coeff α₁ β₁ z ^ κ ∂ζ = 1 := by
  have habs : ∀ z, |coeff α₁ β₁ z| = coeff α₁ β₁ z := fun z => abs_of_nonneg (coeff_nonneg hα₁ hβ₁ z)
  have hm := measurable_coeff α₁ β₁
  obtain ⟨κ, hκ, hκ1⟩ := exists_integral_abs_rpow_eq_one hm hA0 (by simpa only [habs] using hlog)
    (by simpa only [habs] using hneg) hS (by simpa only [habs] using hSi)
    (by simpa only [habs] using hS1)
  refine ⟨κ, hκ, ?_, by simpa only [habs] using hκ1⟩
  simpa only [habs] using integrable_abs_rpow_of_le hm (by simpa only [habs] using hSi) hκ.1.le
    hκ.2.le

end Main

end GARCH

end SRE

end ExtremeValueTheory
