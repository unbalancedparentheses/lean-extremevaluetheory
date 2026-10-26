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
* `gpdSurvivalAll_add`: **threshold stability of the GPD**, `Ḡ_{ξ,σ}(u + t) = Ḡ_{ξ,σ}(u)
  Ḡ_{ξ,σ+ξu}(t)` for `u` in the support: the excess over `u` is `GPD(ξ, σ + ξ u)`.
* `integral_gpdSurvivalAll`: `∫_0^∞ Ḡ_{ξ,σ} = σ / (1 - ξ)` for `ξ < 1`.
* `meanExcess_gpdSurvivalAll`, `meanExcess_gpdMeasure`: **the GPD mean excess function is
  linear**, `e(u) = (σ + ξ u)/(1 - ξ) = σ/(1 - ξ) + (ξ/(1 - ξ)) u` for `ξ < 1`, `u ≥ 0`,
  `σ + ξ u > 0` ([EKM, Theorem 3.4.13(e)], direct part).
* `empMeanExcess`, `ae_tendsto_empMeanExcess`: the **empirical mean excess function**
  `eₙ(u) = ∑_{i<n} (Xᵢ - u)⁺ / #{i < n : Xᵢ > u}` is strongly consistent for every fixed `u`
  with `P(X > u) > 0`, provided `E X⁺ < ∞`.

* `eq_gpdSurvivalAll_of_meanExcess_eq_linear`: **the converse**: if `P(X > u) > 0` for all
  `u ≥ 0` and `e(u) = a + b u` on `[0, ∞)` with `a > 0`, `b ≥ 0`, then
  `P(X > u) = P(X > 0) Ḡ_{ξ,σ}(u)` with `ξ = b/(1 + b)`, `σ = a/(1 + b)`. The proof shows that
  `I(u) = ∫_u^∞ F̄` solves `I' = -I/(a + b u)` (so `F̄ = I/e` is continuous) and that
  `I(u)(a + b u)^{1/b}` (`I(u) e^{u/a}` if `b = 0`) is constant.

## Scope

The converse is proved for unbounded support (`ξ ∈ [0, 1)`); the case of a finite right
endpoint (`b < 0`, `ξ < 0`) is not formalized.

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

lemma gpdSurvivalAll_pos {u : ℝ} (hσ : 0 < σ) (hu : 0 < σ + ξ * u) :
    0 < gpdSurvivalAll ξ σ u := by
  unfold gpdSurvivalAll
  split_ifs
  · exact exp_pos _
  · have : 0 < 1 + ξ * u / σ := by
      rw [show 1 + ξ * u / σ = (σ + ξ * u) / σ by field_simp]; positivity
    rw [max_eq_left this.le]
    exact rpow_pos_of_pos this _

/-- **Threshold stability of the GPD**: for `u` in the support (`σ + ξ u > 0`),
`Ḡ_{ξ,σ}(u + t) = Ḡ_{ξ,σ}(u) Ḡ_{ξ,σ+ξu}(t)`. -/
theorem gpdSurvivalAll_add (hσ : 0 < σ) {u : ℝ} (hu : 0 < σ + ξ * u) (t : ℝ) :
    gpdSurvivalAll ξ σ (u + t) = gpdSurvivalAll ξ σ u * gpdSurvivalAll ξ (σ + ξ * u) t := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [gpdSurvivalAll_zero_left, zero_mul, add_zero, ← exp_add]
    congr 1; ring
  · have hc : 0 < 1 + ξ * u / σ := by
      rw [show 1 + ξ * u / σ = (σ + ξ * u) / σ by field_simp]; positivity
    have e : 1 + ξ * (u + t) / σ = (1 + ξ * u / σ) * (1 + ξ * t / (σ + ξ * u)) := by
      field_simp; ring
    simp only [gpdSurvivalAll, hξ, ↓reduceIte]
    rw [e, max_eq_left hc.le, ← mul_rpow hc.le (le_max_right _ _)]
    congr 1
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero]

/-- `∫_0^∞ Ḡ_{ξ,σ}(t) dt = σ / (1 - ξ)` for `ξ < 1`: the mean of `GPD(ξ, σ)`. -/
theorem integral_gpdSurvivalAll (hσ : 0 < σ) (hξ : ξ < 1) :
    ∫ t in Ioi 0, gpdSurvivalAll ξ σ t = σ / (1 - ξ) := by
  have hint := integrable_id_gpdMeasure hσ hξ
  have hnn : 0 ≤ᵐ[gpdMeasure ξ σ] fun x ↦ x := by
    filter_upwards [ae_gpdMeasure (ξ := ξ) hσ] with x hx using hx.1.le
  have h := hint.integral_eq_integral_meas_lt hnn
  rw [← pwm_zero, pwm_gpdMeasure_zero hσ hξ] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  change gpdSurvivalAll ξ σ t = (gpdMeasure ξ σ).real (Ioi t)
  rw [measureReal_def, gpdMeasure_Ioi hσ ht.le, ENNReal.toReal_ofReal (gpdSurvivalAll_nonneg _ _ _)]

/-- **The GPD mean excess function is linear** ([EKM, Theorem 3.4.13(e)]): for `ξ < 1`,
`u ≥ 0` in the support (`σ + ξ u > 0`), `e(u) = (σ + ξ u) / (1 - ξ)`. -/
theorem meanExcess_gpdSurvivalAll (hσ : 0 < σ) (hξ : ξ < 1) {u : ℝ} (hu : 0 < σ + ξ * u) :
    meanExcess (gpdSurvivalAll ξ σ) u = (σ + ξ * u) / (1 - ξ) := by
  have hpos := gpdSurvivalAll_pos (ξ := ξ) hσ hu
  rw [meanExcess, ← setIntegral_Ioi_zero_comp_add]
  simp_rw [add_comm _ u, gpdSurvivalAll_add hσ hu]
  rw [integral_const_mul, integral_gpdSurvivalAll hu hξ]
  field_simp

/-- The slope form: `e(u) = σ/(1 - ξ) + (ξ/(1 - ξ)) u`. -/
theorem meanExcess_gpdSurvivalAll_eq_linear (hσ : 0 < σ) (hξ : ξ < 1) {u : ℝ}
    (hu : 0 < σ + ξ * u) :
    meanExcess (gpdSurvivalAll ξ σ) u = σ / (1 - ξ) + ξ / (1 - ξ) * u := by
  rw [meanExcess_gpdSurvivalAll hσ hξ hu]
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
    ← meanExcess_gpdSurvivalAll hσ hξ hu, meanExcess, meanExcess]
  have hF : ∀ t, 0 ≤ t → (gpdMeasure ξ σ).real (Ioi t) = gpdSurvivalAll ξ σ t := fun t ht ↦ by
    rw [measureReal_def, gpdMeasure_Ioi hσ ht, ENNReal.toReal_ofReal (gpdSurvivalAll_nonneg _ _ _)]
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
    rw [measureReal_def, gpdMeasure_Ioi hσ hu0, ENNReal.toReal_ofReal (gpdSurvivalAll_nonneg _ _ _)]
    exact gpdSurvivalAll_pos hσ hu
  rw [← meanExcess_gpdMeasure hσ hξ hu0 hu,
    ← meanExcess_measure_eq (integrable_max_sub_gpdMeasure hσ hξ u)]
  exact ae_tendsto_empMeanExcess hX hind hpos hS

end Empirical

/-! ### Converse: a linear mean excess function forces a GPD tail -/

section Converse

/-- The integrating factor `(a + b v)^{1/b}` (`e^{v/a}` for `b = 0`) of the linear equation
`I' = -I/(a + b v)` satisfied by `I(v) = ∫_v^∞ F̄`. -/
private noncomputable def meWeight (a b v : ℝ) : ℝ :=
  if b = 0 then exp (v / a) else (a + b * v) ^ (1 / b)

private lemma hasDerivAt_meWeight {a b v : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hv : 0 ≤ v) :
    HasDerivAt (meWeight a b) (meWeight a b v / (a + b * v)) v := by
  by_cases hb0 : b = 0
  · subst hb0
    have e : meWeight a 0 = fun v ↦ exp (v / a) := funext fun v ↦ by simp [meWeight]
    rw [e]
    convert ((hasDerivAt_id v).div_const a).exp using 1
    · rfl
    · simp [div_eq_mul_inv]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hc : 0 < a + b * v := by positivity
    have e : meWeight a b = fun v ↦ (a + b * v) ^ (1 / b) := funext fun v ↦ by simp [meWeight, hb0]
    rw [e]
    convert (((hasDerivAt_id v).const_mul b).const_add a).rpow_const (p := 1 / b)
      (Or.inl hc.ne') using 1
    · rfl
    · show (a + b * v) ^ (1 / b) / (a + b * v) = b * 1 * (1 / b) * (a + b * v) ^ (1 / b - 1)
      rw [rpow_sub_one hc.ne']
      field_simp

private lemma meWeight_pos {a b v : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hv : 0 ≤ v) :
    0 < meWeight a b v := by
  unfold meWeight
  split_ifs
  · exact exp_pos _
  · exact rpow_pos_of_pos (by positivity) _

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- **A linear mean excess function characterizes the GPD** ([EKM, Theorem 3.4.13(e)],
converse part, for an unbounded support). Let `F̄(t) = P(X > t)` be positive on `[0, ∞)` and
suppose the mean excess function is linear, `e(u) = a + b u` for `u ≥ 0`, with `a > 0`,
`b ≥ 0`. Then the tail beyond `0` is generalized Pareto:
`F̄(u) = F̄(0) Ḡ_{ξ,σ}(u)` for `u ≥ 0`, with `ξ = b/(1 + b) ∈ [0, 1)` and `σ = a/(1 + b)`.
(Integrability of `F̄` is not assumed: it follows from `e(0) = a > 0`.) -/
theorem eq_gpdSurvivalAll_of_meanExcess_eq_linear {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hS : ∀ u, 0 ≤ u → 0 < μ.real (Ioi u))
    (he : ∀ u, 0 ≤ u → meanExcess (fun t ↦ μ.real (Ioi t)) u = a + b * u) {u : ℝ}
    (hu : 0 ≤ u) :
    μ.real (Ioi u) = μ.real (Ioi 0) * gpdSurvivalAll (b / (1 + b)) (a / (1 + b)) u := by
  set S : ℝ → ℝ := fun t ↦ μ.real (Ioi t) with hSdef
  have hanti : Antitone S := fun s t hst ↦ measureReal_mono (Ioi_subset_Ioi hst)
  have hmeas : Measurable S := hanti.measurable
  have hii : ∀ x y, IntervalIntegrable S volume x y := fun x y ↦ hanti.intervalIntegrable
  have hI : ∀ v, 0 ≤ v → ∫ t in Ioi v, S t = S v * (a + b * v) := by
    intro v hv
    have := he v hv
    rw [meanExcess, div_eq_iff (hS v hv).ne'] at this
    rw [this]; ring
  have hint : IntegrableOn S (Ioi 0) := by
    by_contra h
    have h1 := hI 0 le_rfl
    rw [integral_undef h] at h1
    have h2 := hS 0 le_rfl
    simp only [mul_zero, add_zero] at h1
    nlinarith
  set I0 := ∫ t in Ioi 0, S t with hI0
  set F : ℝ → ℝ := fun v ↦ ∫ t in (0 : ℝ)..v, S t with hFdef
  have hsplit : ∀ v, 0 ≤ v → ∫ t in Ioi v, S t = I0 - F v := by
    intro v hv
    have hU := Ioc_union_Ioi_eq_Ioi hv
    simp only [hI0, hFdef]
    rw [intervalIntegral.integral_of_le hv, ← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hint.mono_set (hU ▸ subset_union_left))
      (hint.mono_set (Ioi_subset_Ioi hv))]
    ring
  have hFc : Continuous F := intervalIntegral.continuous_primitive hii 0
  have hSeq : ∀ v, 0 ≤ v → S v = (I0 - F v) / (a + b * v) := by
    intro v hv
    have hpos : 0 < a + b * v := by positivity
    rw [← hsplit v hv, hI v hv]
    field_simp
  have hScont : ∀ v, 0 < v → ContinuousAt S v := by
    intro v hv
    have hev : (fun w ↦ (I0 - F w) / (a + b * w)) =ᶠ[𝓝 v] S :=
      (eventually_gt_nhds hv).mono fun w hw ↦ (hSeq w hw.le).symm
    refine ContinuousAt.congr ?_ hev
    have hpos : 0 < a + b * v := by positivity
    exact ((continuous_const.sub hFc).continuousAt).div (by fun_prop) hpos.ne'
  have hFd : ∀ v, 0 < v → HasDerivAt F (S v) v := fun v hv ↦
    intervalIntegral.integral_hasDerivAt_right (hii 0 v)
      hmeas.stronglyMeasurable.stronglyMeasurableAtFilter (hScont v hv)
  set Ψ : ℝ → ℝ := fun v ↦ (I0 - F v) * meWeight a b v with hΨ
  have hΨd : ∀ v, 0 < v → HasDerivAt Ψ 0 v := by
    intro v hv
    have h := ((hasDerivAt_const v I0).sub (hFd v hv)).mul (hasDerivAt_meWeight ha hb hv.le)
    convert h using 1
    have hpos : 0 < a + b * v := by positivity
    rw [hSeq v hv.le]
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hΨc : ContinuousOn Ψ (Icc 0 u) :=
    (continuous_const.sub hFc).continuousOn.mul fun v hv ↦
      (hasDerivAt_meWeight ha hb hv.1).continuousAt.continuousWithinAt
  have hΨu : Ψ u = Ψ 0 := by
    rcases hu.eq_or_lt with h0 | hu'
    · rw [h0]
    obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope Ψ (fun _ ↦ 0) hu' hΨc
      (fun v hv ↦ hΨd v hv.1)
    have hne : u - 0 ≠ 0 := by linarith
    rw [eq_comm, div_eq_zero_iff, or_iff_left hne, sub_eq_zero] at hc'
    exact hc'
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  have hwu := meWeight_pos ha hb hu
  have hc : 0 < a + b * u := by positivity
  have hS0 : S 0 = I0 / a := by rw [hSeq 0 le_rfl, hF0]; simp
  have hSu : S u = I0 * meWeight a b 0 / (meWeight a b u * (a + b * u)) := by
    rw [hSeq u hu]
    have : I0 - F u = I0 * meWeight a b 0 / meWeight a b u := by
      rw [eq_div_iff hwu.ne']
      have := hΨu
      simp only [hΨ, hF0, sub_zero] at this
      exact this
    rw [this, div_div]
  change S u = S 0 * _
  rw [hSu, hS0]
  by_cases hb0 : b = 0
  · subst hb0
    simp only [meWeight, ↓reduceIte, zero_div, exp_zero, mul_one, zero_mul, add_zero,
      gpdSurvivalAll_zero_left, div_one]
    field_simp
    rw [mul_assoc, ← exp_add]
    simp
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hξ : b / (1 + b) ≠ 0 := by positivity
    simp only [meWeight, hb0, ↓reduceIte, mul_zero, add_zero, gpdSurvivalAll, hξ]
    have e1 : 1 + b / (1 + b) * u / (a / (1 + b)) = (a + b * u) / a := by
      field_simp
    have e2 : -(1 / (b / (1 + b))) = -(1 / b + 1) := by field_simp
    rw [e1, max_eq_left (by positivity), e2, rpow_neg (by positivity),
      rpow_add_one (by positivity), div_rpow hc.le ha.le]
    have h1 := rpow_pos_of_pos ha (1 / b)
    have h2 := rpow_pos_of_pos hc (1 / b)
    field_simp

end Converse


/-! ### Deprecated names -/

@[deprecated (since := "2026-10-23")] alias gpdSurvival'_pos := gpdSurvivalAll_pos
@[deprecated (since := "2026-10-23")] alias gpdSurvival'_add := gpdSurvivalAll_add
@[deprecated (since := "2026-10-23")] alias integral_gpdSurvival' := integral_gpdSurvivalAll
@[deprecated (since := "2026-10-23")] alias meanExcess_gpdSurvival' := meanExcess_gpdSurvivalAll
@[deprecated (since := "2026-10-23")] alias meanExcess_gpdSurvival'_eq_linear := meanExcess_gpdSurvivalAll_eq_linear
@[deprecated (since := "2026-10-23")] alias eq_gpdSurvival'_of_meanExcess_eq_linear := eq_gpdSurvivalAll_of_meanExcess_eq_linear

end ExtremeValueTheory
