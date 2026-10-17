/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.Dependence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.StrongLaw

/-!
# The Pickands estimator of the dependence function

Let `(Y₁, Y₂)` be a bivariate simple max-stable vector (unit Fréchet margins) with Pickands
function `A`. For `0 < t < 1`,

  `ξ(t) = min (1 / (t Y₁), 1 / ((1 - t) Y₂))`

is exponentially distributed with rate `A(t)`: for `s > 0`,
`P(ξ(t) ≥ s) = P(Y₁ ≤ 1 / (t s), Y₂ ≤ 1 / ((1 - t) s)) = exp (-s V(1 / t, 1 / (1 - t)))
= exp (-s A(t))`. Hence `E ξ(t) = 1 / A(t)`, and given an i.i.d. sample with known (unit
Fréchet) margins, **Pickands' estimator**

  `Âₙ(t) = n / ∑_{i < n} ξᵢ(t)`

is strongly consistent by the strong law of large numbers ([Pickands 1981]; [BGST04, §9.4.1];
[dHF, §7.2]).

## Main results

* `pickandsVar t y = min (1 / (t y 0)) (1 / ((1 - t) y 1))`, `pickandsDependenceEstimator`.
* `IsSimpleMaxStable.measure_apply_le_zero`: unit Fréchet coordinates are a.s. positive.
* `IsSimpleMaxStable.measure_le_pickandsVar`: `P(ξ(t) ≥ s) = exp (-s A(t))`.
* `IsSimpleMaxStable.integrable_pickandsVar`, `IsSimpleMaxStable.integral_pickandsVar`:
  `E ξ(t) = 1 / A(t)`.
* `tendsto_pickandsDependenceEstimator`: almost sure consistency `Âₙ(t) → A(t)` for pairwise
  independent, identically distributed samples from a simple max-stable law.

The Capéraà–Fougères–Genest estimator and estimators with estimated margins are not formalized.

## References

* J. Pickands III, *Multivariate extreme value distributions*, Bull. Int. Statist. Inst. 49
  (1981).
* J. Beirlant, Y. Goegebeur, J. Segers, J. Teugels, *Statistics of Extremes*, Wiley (2004),
  Chapter 9 [BGST04].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 7 [dHF].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped ENNReal

namespace ExtremeValueTheory

/-- Pickands' transformed variable `ξ(t) = min (1 / (t y₀)) (1 / ((1 - t) y₁))`. -/
noncomputable def pickandsVar (t : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  min (t * y 0)⁻¹ ((1 - t) * y 1)⁻¹

/-- **Pickands' estimator** `Âₙ(t) = n / ∑_{i < n} ξ(t)(yᵢ)` of the dependence function from a
sample `y₀, y₁, …` with unit Fréchet margins. -/
noncomputable def pickandsDependenceEstimator (t : ℝ) (y : ℕ → Fin 2 → ℝ) (n : ℕ) : ℝ :=
  n / ∑ i ∈ range n, pickandsVar t (y i)

lemma measurable_pickandsVar (t : ℝ) : Measurable (pickandsVar t) :=
  ((measurable_const.mul (measurable_pi_apply 0)).inv).min
    ((measurable_const.mul (measurable_pi_apply 1)).inv)

/-- `s ≤ 1 / (c x)` iff `0 < x ≤ 1 / (s c)`, for `s, c > 0`. -/
lemma le_inv_mul_iff_of_pos {s c x : ℝ} (hs : 0 < s) (hc : 0 < c) :
    s ≤ (c * x)⁻¹ ↔ 0 < x ∧ x ≤ s⁻¹ * c⁻¹ := by
  by_cases hx : 0 < x
  · have hcx : 0 < c * x := mul_pos hc hx
    rw [le_inv_comm₀ hs hcx, ← div_eq_mul_inv, le_div_iff₀' hc]
    exact ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩
  · have : (c * x)⁻¹ ≤ 0 := inv_nonpos.2 (mul_nonpos_of_nonneg_of_nonpos hc.le (not_lt.1 hx))
    exact ⟨fun h ↦ absurd (hs.trans_le (h.trans this)) (lt_irrefl 0), fun h ↦ absurd h.1 hx⟩

namespace IsSimpleMaxStable

variable {μ : Measure (Fin 2 → ℝ)}

/-- Unit Fréchet coordinates are almost surely positive. -/
theorem measure_apply_le_zero (h : IsSimpleMaxStable μ) (i : Fin 2) :
    μ {x | x i ≤ 0} = 0 := by
  have hb (n : ℕ) : μ {x | x i ≤ 0} ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1))) := by
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    calc μ {x | x i ≤ 0} ≤ μ {x | x i ≤ ((n : ℝ) + 1)⁻¹} :=
          measure_mono fun x (hx : x i ≤ 0) ↦ hx.trans hpos.le
      _ = _ := by rw [h.measure_le i _ hpos, inv_inv]
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))))
    rw [ENNReal.ofReal_zero] at this
    exact this
  exact le_antisymm (ge_of_tendsto' hlim hb) zero_le

lemma ae_pos (h : IsSimpleMaxStable μ) : ∀ᵐ x ∂μ, 0 < x 0 ∧ 0 < x 1 := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_)
    (measure_union_null (h.measure_apply_le_zero 0) (h.measure_apply_le_zero 1))
  simp only [mem_ofPred_eq, not_and_or, not_lt] at hx
  exact hx

/-- **Pickands' variable is exponential**: `P(ξ(t) ≥ s) = exp (-s A(t))` for `s > 0`. -/
theorem measure_le_pickandsVar (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : 0 < s) :
    μ {x | s ≤ pickandsVar t x} = ENNReal.ofReal (Real.exp (-(s * pickandsDependence μ t))) := by
  have := h.isProbabilityMeasure
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  set y : Fin 2 → ℝ := s⁻¹ • ![t⁻¹, (1 - t)⁻¹] with hy
  have hS : {x : Fin 2 → ℝ | s ≤ pickandsVar t x} =
      {x | (0 < x 0 ∧ x 0 ≤ y 0) ∧ (0 < x 1 ∧ x 1 ≤ y 1)} := by
    ext x
    simp only [mem_ofPred_eq, pickandsVar, le_min_iff, le_inv_mul_iff_of_pos hs ht.1,
      le_inv_mul_iff_of_pos hs ht1, hy, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  have hsub : {x : Fin 2 → ℝ | s ≤ pickandsVar t x} ⊆ Iic y := by
    rw [hS]
    intro x hx i
    fin_cases i
    exacts [hx.1.2, hx.2.2]
  have hsup : Iic y ⊆ {x : Fin 2 → ℝ | s ≤ pickandsVar t x} ∪
      ({x | x 0 ≤ 0} ∪ {x | x 1 ≤ 0}) := by
    intro x hx
    by_cases h0 : 0 < x 0
    · by_cases h1 : 0 < x 1
      · left; rw [hS]; exact ⟨⟨h0, hx 0⟩, ⟨h1, hx 1⟩⟩
      · right; right; exact not_lt.1 h1
    · right; left; exact not_lt.1 h0
  have heq : μ {x : Fin 2 → ℝ | s ≤ pickandsVar t x} = μ (Iic y) := by
    refine le_antisymm (measure_mono hsub) ((measure_mono hsup).trans ?_)
    refine (measure_union_le _ _).trans ?_
    rw [measure_union_null (h.measure_apply_le_zero 0) (h.measure_apply_le_zero 1), add_zero]
  have hV : maxStableExponent μ y = s * pickandsDependence μ t := by
    rw [hy, h.maxStableExponent_smul (inv_pos.2 hs) (pos_vec_inv ht), inv_inv,
      pickandsDependence_of_mem_Ioo μ ht]
  have hypos : ∀ i, 0 < y i := fun i ↦ by
    rw [hy, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.2 hs) (pos_vec_inv ht i)
  rw [heq, ← ofReal_measureReal, ← h.exp_neg_maxStableExponent hypos, hV]

lemma ae_nonneg_pickandsVar (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ᵐ[μ] pickandsVar t := by
  filter_upwards [h.ae_pos] with x hx
  exact le_min (inv_nonneg.2 (mul_pos ht.1 hx.1).le)
    (inv_nonneg.2 (mul_pos (by linarith [ht.2]) hx.2).le)

lemma pickandsDependence_pos (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < pickandsDependence μ t :=
  lt_of_lt_of_le (by norm_num) (h.half_le_pickands (Ioo_subset_Icc_self ht))

/-- `E[ξ(t)] = 1 / A(t)`, as a lower integral. -/
theorem lintegral_pickandsVar (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ x, ENNReal.ofReal (pickandsVar t x) ∂μ = ENNReal.ofReal (pickandsDependence μ t)⁻¹ := by
  have hA := h.pickandsDependence_pos ht
  rw [lintegral_eq_lintegral_meas_le μ (h.ae_nonneg_pickandsVar ht)
    (measurable_pickandsVar t).aemeasurable]
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun s (hs : 0 < s) ↦ h.measure_le_pickandsVar ht hs)]
  simp_rw [show ∀ s : ℝ, -(s * pickandsDependence μ t) = -pickandsDependence μ t * s from
    fun s ↦ by ring]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hA) 0)
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le), integral_exp_mul_Ioi (neg_lt_zero.2 hA) 0,
    mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

theorem integrable_pickandsVar (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (pickandsVar t) μ :=
  (lintegral_ofReal_ne_top_iff_integrable (measurable_pickandsVar t).aestronglyMeasurable
    (h.ae_nonneg_pickandsVar ht)).1
    (by rw [h.lintegral_pickandsVar ht]; exact ENNReal.ofReal_ne_top)

/-- **The mean of Pickands' variable**: `E[ξ(t)] = 1 / A(t)`. -/
theorem integral_pickandsVar (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫ x, pickandsVar t x ∂μ = (pickandsDependence μ t)⁻¹ := by
  rw [integral_eq_lintegral_of_nonneg_ae (h.ae_nonneg_pickandsVar ht)
    (measurable_pickandsVar t).aestronglyMeasurable, h.lintegral_pickandsVar ht,
    ENNReal.toReal_ofReal (inv_nonneg.2 (h.pickandsDependence_pos ht).le)]

end IsSimpleMaxStable

/-- **Strong consistency of Pickands' estimator** ([Pickands 1981]; [BGST04, §9.4.1]). Let
`Z₀, Z₁, …` be pairwise independent, identically distributed random vectors whose common law `μ`
is simple max-stable. Then for `0 < t < 1`, almost surely
`Âₙ(t) = n / ∑_{i < n} ξ(t)(Zᵢ) → A(t)`. -/
theorem tendsto_pickandsDependenceEstimator {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Z : ℕ → Ω → Fin 2 → ℝ} (hZ : Measurable (Z 0))
    (hindep : Pairwise fun i j ↦ Z i ⟂ᵢ[P] Z j) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    {μ : Measure (Fin 2 → ℝ)} (hlaw : P.map (Z 0) = μ) (h : IsSimpleMaxStable μ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Tendsto (pickandsDependenceEstimator t fun i ↦ Z i ω) atTop
      (𝓝 (pickandsDependence μ t)) := by
  have hg := measurable_pickandsVar t
  set ξ : ℕ → Ω → ℝ := fun i ω ↦ pickandsVar t (Z i ω) with hξ
  have hint : Integrable (ξ 0) P := by
    have := h.integrable_pickandsVar ht
    rw [← hlaw] at this
    exact this.comp_measurable hZ
  have hmean : P[ξ 0] = (pickandsDependence μ t)⁻¹ := by
    rw [← h.integral_pickandsVar ht, ← hlaw, integral_map hZ.aemeasurable hg.aestronglyMeasurable]
  have hslln := strong_law_ae_real ξ hint
    (fun i j hij ↦ (hindep hij).comp hg hg) (fun i ↦ (hident i).comp hg)
  filter_upwards [hslln] with ω hω
  rw [hmean] at hω
  have := hω.inv₀ (inv_ne_zero (h.pickandsDependence_pos ht).ne')
  rw [inv_inv] at this
  refine this.congr fun n ↦ ?_
  simp only [pickandsDependenceEstimator, hξ, inv_div]
