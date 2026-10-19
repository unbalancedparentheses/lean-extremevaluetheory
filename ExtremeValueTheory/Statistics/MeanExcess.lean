/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.LMomentsEstimators

/-!
# The mean excess function: generalized Pareto law and empirical version

The mean excess function of a survival function `F̄` is the library's
`meanExcess F̄ u = (∫_u^∞ F̄) / F̄(u)` (`PeaksOverThreshold/Frechet.lean`). For the law `μ` of a
random variable `X` with `F̄(t) = P(X > t)` it is the conditional mean excess
`e(u) = E[(X - u)⁺] / P(X > u) = E[X - u | X > u]` (`meanExcess_measure_eq`, a layer-cake
computation).

## Main results

* `meanExcess_measure_eq`: `meanExcess (t ↦ P(X > t)) u = E[(X - u)⁺] / P(X > u)` whenever
  `E[(X - u)⁺] < ∞`.
* `gpdSurvival'_add`: **threshold stability of the GPD**, `Ḡ_{ξ,σ}(u + t) = Ḡ_{ξ,σ}(u)
  Ḡ_{ξ,σ+ξu}(t)` for `u` in the support: the excess over `u` is `GPD(ξ, σ + ξ u)`.
* `integral_gpdSurvival'`: `∫_0^∞ Ḡ_{ξ,σ} = σ / (1 - ξ)` for `ξ < 1`.
* `meanExcess_gpdSurvival'`, `meanExcess_gpdMeasure`: **the GPD mean excess function is
  linear**, `e(u) = (σ + ξ u)/(1 - ξ) = σ/(1 - ξ) + (ξ/(1 - ξ)) u` for `ξ < 1`, `u ≥ 0`,
  `σ + ξ u > 0` ([EKM, Theorem 3.4.13(e)], direct part).
* `empMeanExcess`, `ae_tendsto_empMeanExcess`: the **empirical mean excess function**
  `eₙ(u) = ∑_{i<n} (Xᵢ - u)⁺ / #{i < n : Xᵢ > u}` is strongly consistent for every fixed `u`
  with `P(X > u) > 0`, provided `E X⁺ < ∞`.

## Scope

The converse characterization (a linear mean excess function forces a GPD tail) is not
formalized here.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §3.4 and §6.2.2 [EKM].
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-- Translation on half-lines: `∫_0^∞ f(t + u) dt = ∫_u^∞ f(s) ds`. -/
lemma setIntegral_Ioi_zero_comp_add (f : ℝ → ℝ) (u : ℝ) :
    ∫ t in Ioi 0, f (t + u) = ∫ s in Ioi u, f s := by
  have h := integral_add_right_eq_self (μ := volume) ((Ioi u).indicator f) u
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi, ← h]
  congr 1
  funext t
  simp only [indicator_apply, mem_Ioi, lt_add_iff_pos_left]

section Population

variable {μ : Measure ℝ}

/-- **Mean excess as a conditional expectation**: if `E[(X - u)⁺] < ∞`,
`meanExcess (t ↦ P(X > t)) u = E[(X - u)⁺] / P(X > u)`. -/
theorem meanExcess_measure_eq {u : ℝ} (hint : Integrable (fun x ↦ max (x - u) 0) μ) :
    meanExcess (fun t ↦ μ.real (Ioi t)) u = (∫ x, max (x - u) 0 ∂μ) / μ.real (Ioi u) := by
  rw [meanExcess, hint.integral_eq_integral_meas_lt (ae_of_all _ fun x ↦ le_max_right _ _),
    ← setIntegral_Ioi_zero_comp_add]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, mem_Ioi, lt_max_iff, not_lt.2 ht.le, or_false]
  constructor <;> intro h <;> linarith

end Population

/-! ### The generalized Pareto law -/

section GPD

variable {ξ σ : ℝ}

lemma gpdSurvival'_pos {u : ℝ} (hσ : 0 < σ) (hu : 0 < σ + ξ * u) :
    0 < gpdSurvival' ξ σ u := by
  unfold gpdSurvival'
  split_ifs
  · exact exp_pos _
  · have : 0 < 1 + ξ * u / σ := by
      rw [show 1 + ξ * u / σ = (σ + ξ * u) / σ by field_simp]; positivity
    rw [max_eq_left this.le]
    exact rpow_pos_of_pos this _

/-- **Threshold stability of the GPD**: for `u` in the support (`σ + ξ u > 0`),
`Ḡ_{ξ,σ}(u + t) = Ḡ_{ξ,σ}(u) Ḡ_{ξ,σ+ξu}(t)`. -/
theorem gpdSurvival'_add (hσ : 0 < σ) {u : ℝ} (hu : 0 < σ + ξ * u) (t : ℝ) :
    gpdSurvival' ξ σ (u + t) = gpdSurvival' ξ σ u * gpdSurvival' ξ (σ + ξ * u) t := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [gpdSurvival'_zero_left, zero_mul, add_zero, ← exp_add]
    congr 1; ring
  · have hc : 0 < 1 + ξ * u / σ := by
      rw [show 1 + ξ * u / σ = (σ + ξ * u) / σ by field_simp]; positivity
    have e : 1 + ξ * (u + t) / σ = (1 + ξ * u / σ) * (1 + ξ * t / (σ + ξ * u)) := by
      field_simp; ring
    simp only [gpdSurvival', hξ, ↓reduceIte]
    rw [e, max_eq_left hc.le, ← mul_rpow hc.le (le_max_right _ _)]
    congr 1
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero]

/-- `∫_0^∞ Ḡ_{ξ,σ}(t) dt = σ / (1 - ξ)` for `ξ < 1`: the mean of `GPD(ξ, σ)`. -/
theorem integral_gpdSurvival' (hσ : 0 < σ) (hξ : ξ < 1) :
    ∫ t in Ioi 0, gpdSurvival' ξ σ t = σ / (1 - ξ) := by
  have hint := integrable_id_gpdMeasure hσ hξ
  have hnn : 0 ≤ᵐ[gpdMeasure ξ σ] fun x ↦ x := by
    filter_upwards [ae_gpdMeasure (ξ := ξ) hσ] with x hx using hx.1.le
  have h := hint.integral_eq_integral_meas_lt hnn
  rw [← pwm_zero, pwm_gpdMeasure_zero hσ hξ] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  change gpdSurvival' ξ σ t = (gpdMeasure ξ σ).real (Ioi t)
  rw [measureReal_def, gpdMeasure_Ioi hσ ht.le, ENNReal.toReal_ofReal (gpdSurvival'_nonneg _ _ _)]

/-- **The GPD mean excess function is linear** ([EKM, Theorem 3.4.13(e)]): for `ξ < 1`,
`u ≥ 0` in the support (`σ + ξ u > 0`), `e(u) = (σ + ξ u) / (1 - ξ)`. -/
theorem meanExcess_gpdSurvival' (hσ : 0 < σ) (hξ : ξ < 1) {u : ℝ} (hu : 0 < σ + ξ * u) :
    meanExcess (gpdSurvival' ξ σ) u = (σ + ξ * u) / (1 - ξ) := by
  have hpos := gpdSurvival'_pos (ξ := ξ) hσ hu
  rw [meanExcess, ← setIntegral_Ioi_zero_comp_add]
  simp_rw [add_comm _ u, gpdSurvival'_add hσ hu]
  rw [integral_const_mul, integral_gpdSurvival' hu hξ]
  field_simp

/-- The slope form: `e(u) = σ/(1 - ξ) + (ξ/(1 - ξ)) u`. -/
theorem meanExcess_gpdSurvival'_eq_linear (hσ : 0 < σ) (hξ : ξ < 1) {u : ℝ}
    (hu : 0 < σ + ξ * u) :
    meanExcess (gpdSurvival' ξ σ) u = σ / (1 - ξ) + ξ / (1 - ξ) * u := by
  rw [meanExcess_gpdSurvival' hσ hξ hu]
  have : 1 - ξ ≠ 0 := by linarith
  field_simp

/-- For `ξ < 1`, `E[(X - u)⁺] < ∞` under `GPD(ξ, σ)`. -/
lemma integrable_max_sub_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) (u : ℝ) :
    Integrable (fun x ↦ max (x - u) 0) (gpdMeasure ξ σ) := by
  have hb : Integrable (fun x ↦ |x| + |u|) (gpdMeasure ξ σ) :=
    (integrable_id_gpdMeasure hσ hξ).abs.add (integrable_const |u|)
  refine Integrable.mono' hb (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_abs_self x, neg_abs_le u])
    (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **Mean excess of the GPD as a conditional expectation**: for `X ~ GPD(ξ, σ)`, `ξ < 1`,
`u ≥ 0`, `σ + ξ u > 0`: `E[X - u | X > u] = (σ + ξ u) / (1 - ξ)`. -/
theorem meanExcess_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : 0 < σ + ξ * u) :
    (∫ x, max (x - u) 0 ∂gpdMeasure ξ σ) / (gpdMeasure ξ σ).real (Ioi u) =
      (σ + ξ * u) / (1 - ξ) := by
  rw [← meanExcess_measure_eq (integrable_max_sub_gpdMeasure hσ hξ u),
    ← meanExcess_gpdSurvival' hσ hξ hu, meanExcess, meanExcess]
  have hF : ∀ t, 0 ≤ t → (gpdMeasure ξ σ).real (Ioi t) = gpdSurvival' ξ σ t := fun t ht ↦ by
    rw [measureReal_def, gpdMeasure_Ioi hσ ht, ENNReal.toReal_ofReal (gpdSurvival'_nonneg _ _ _)]
  rw [hF u hu0, setIntegral_congr_fun measurableSet_Ioi fun t (ht : u < t) ↦ hF t (by linarith)]

end GPD

/-! ### The empirical mean excess function -/

section Empirical

/-- The **empirical mean excess function** of the first `n` observations:
`eₙ(u) = ∑_{i<n} (xᵢ - u)⁺ / #{i < n : xᵢ > u}`. -/
noncomputable def empMeanExcess (x : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, max (x i - u) 0) / (((Finset.range n).filter fun i ↦ u < x i).card : ℝ)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {μ : Measure ℝ}
  [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}

/-- `E X⁺ < ∞` implies `E (X - u)⁺ < ∞`. -/
lemma integrable_max_sub_of_pos_part (hpos : Integrable (fun x ↦ max x 0) μ) (u : ℝ) :
    Integrable (fun x ↦ max (x - u) 0) μ := by
  have hb : Integrable (fun x ↦ max x 0 + |u|) μ := hpos.add (integrable_const |u|)
  refine Integrable.mono' hb (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_max_left x 0, neg_abs_le u])
    (add_nonneg (le_max_right _ _) (abs_nonneg _))

/-- **Strong consistency of the empirical mean excess function**: for iid observations with
`E X⁺ < ∞` and a threshold `u` with `P(X > u) > 0`, `eₙ(u) → e(u) = E[(X - u)⁺]/P(X > u)`
almost surely. -/
theorem ae_tendsto_empMeanExcess (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hpos : Integrable (fun x ↦ max x 0) μ) {u : ℝ} (hu : 0 < μ.real (Ioi u)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ empMeanExcess (fun i ↦ X i ω) n u) atTop
      (𝓝 (meanExcess (fun t ↦ μ.real (Ioi t)) u)) := by
  have hg : Measurable ((Ioi u).indicator fun _ : ℝ ↦ (1 : ℝ)) :=
    measurable_const.indicator measurableSet_Ioi
  have hgi : Integrable ((Ioi u).indicator fun _ : ℝ ↦ (1 : ℝ)) μ :=
    (integrable_const 1).indicator measurableSet_Ioi
  have hint := integrable_max_sub_of_pos_part hpos u
  rw [meanExcess_measure_eq hint]
  filter_upwards [ae_tendsto_avg_comp hX hind (by fun_prop) hint,
    ae_tendsto_avg_comp hX hind hg hgi] with ω h1 h2
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one] at h2
  refine (h1.div h2 hu.ne').congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  simp only [Pi.div_apply]
  rw [empMeanExcess, mul_div_mul_left _ _ hn']
  congr 1
  simp only [Set.indicator_apply, mem_Ioi]
  rw [Finset.sum_boole]

/-- **The empirical mean excess function of GPD data** converges to the line
`(σ + ξ u)/(1 - ξ)`, for every `u ≥ 0` in the support, when `ξ < 1`. -/
theorem ae_tendsto_empMeanExcess_gpd {ξ σ : ℝ} (hσ : 0 < σ) (hξ : ξ < 1)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ) P) (hind : iIndepFun X P)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : 0 < σ + ξ * u) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ empMeanExcess (fun i ↦ X i ω) n u) atTop
      (𝓝 ((σ + ξ * u) / (1 - ξ))) := by
  have hpos : Integrable (fun x ↦ max x 0) (gpdMeasure ξ σ) := by
    simpa using integrable_max_sub_gpdMeasure hσ hξ 0
  have hS : 0 < (gpdMeasure ξ σ).real (Ioi u) := by
    rw [measureReal_def, gpdMeasure_Ioi hσ hu0, ENNReal.toReal_ofReal (gpdSurvival'_nonneg _ _ _)]
    exact gpdSurvival'_pos hσ hu
  rw [← meanExcess_gpdMeasure hσ hξ hu0 hu,
    ← meanExcess_measure_eq (integrable_max_sub_gpdMeasure hσ hξ u)]
  exact ae_tendsto_empMeanExcess hX hind hpos hS

end Empirical

end ExtremeValueTheory
