/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.Dependence
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The spectral representation of simple max-stable laws ("⇒")

Every simple max-stable law `μ` on `ℝ^ι` (`ι` finite) has a **spectral measure**: a finite
measure `H` on `[0, ∞]^ι`, concentrated on the unit sphere `{w ∈ [0, 1]^ι : max_i w i = 1}` of the
sup norm, with `∫ w i dH(w) = 1` for every `i` and

  `P(Y ≤ y) = exp (-∫ max_i w i / y i dH(w))`

([dHF, Theorem 6.1.9 "⇒"]; [Res87, Proposition 5.11]; [dHR77]). Together with
`exists_isSimpleMaxStable_hasSpectralMeasure` (the "⇐" direction, `MaxStable/Spectral.lean`) this
characterizes the simple max-stable laws. In the bivariate case it gives the convexity of the
Pickands dependence function for every simple max-stable law.

## The construction

Instead of building the exponent measure on `[0, ∞]^ι \ {0}` as a vague limit of `n P(Y / n ∈ ·)`
and decomposing it in polar coordinates, we build the angular measure directly, by compactness.
Write `R = max_i Y i` and `Θ = Y / R ∈ [0, 1]^ι` (`R > 0` a.s.). For `y` with positive coordinates
put `X_y = max_i Y i / y i = R · g_y(Θ)`, `g_y(θ) = max_i θ i / y i`. Homogeneity of the exponent
function gives the exact Fréchet tail `P(X_y > r) = 1 - exp (-V(y) / r)`, hence by the layer-cake
formula

  `E[min X_y c] = ∫₀ᶜ (1 - exp (-V(y) / t)) dt = V(y) log c + O(1)`

(`tendsto_lintegral_min_div_log`). Consider the finite measures on the compact cube `[0, 1]^ι`

  `Λ_M = E[min R M ; Θ ∈ ·] / log M`.

Since `g_y(Θ) min R M = min X_y (g_y(Θ) M)` and `g_y` is bounded above and below by positive
constants on the sphere, a sandwich gives `∫ g_y dΛ_M → V(y)` for every `y`
(`IsSimpleMaxStable.tendsto_lintegral_spectralTest`), and in particular the masses converge to
`V(1, …, 1)`. The masses being bounded, the measures `Λ_n` have a weak cluster point `P`
(Prokhorov's theorem on a compact space, `isCompact_setOfPred_finiteMeasure_le_of_compactSpace`),
and since `g_y` is continuous, `∫ g_y dP = V(y)` (`IsSimpleMaxStable.exists_angularMeasure`).
The normalization `∫ w i dH = 1` follows by letting the other coordinates of `y` tend to `∞`,
using `1 / y i ≤ V(y) ≤ ∑ j, 1 / y j`; the support on the sphere follows from the vanishing of
`∫ (1 - max_i θ i) dΛ_n`. No uniqueness of the limit and no asymptotic independence of radius
and angle are needed: only the values of `∫ g_y dP` are used.

## Main results

* `tendsto_lintegral_min_div_log`: `E[min X (a M)] / log M → v` when `P(X > r) = 1 - exp (-v / r)`.
* `IsSimpleMaxStable.ae_pos`: a simple max-stable vector has positive coordinates a.s.
* `IsSimpleMaxStable.exists_angularMeasure`: a finite measure `P` on `[0, 1]^ι`, concentrated on
  `{max_i θ i = 1}`, with `∫ max_i θ i / y i dP(θ) = V(y)`.
* `IsSimpleMaxStable.exists_hasSpectralMeasure`: **the spectral representation** — a finite
  `H` on `[0, ∞]^ι` with `w ≤ 1` and `max_i w i = 1` `H`-a.e., `∫ w i dH = 1`, and
  `HasSpectralMeasure μ H`.
* `HasSpectralMeasure.measure_univ_toReal`: the total mass of a spectral measure on the sphere is
  the extremal coefficient.
* `IsSimpleMaxStable.exists_pickandsDependence_eq_pickandsSpectral`,
  `IsSimpleMaxStable.convexOn_pickandsDependence`: every bivariate simple max-stable law has
  `A(t) = ∫ max(t w 0, (1 - t) w 1) dH(w)`, so its Pickands function is convex.

The spectral measure is not shown to be unique (it is, up to the choice of the sphere, by the
uniqueness of the exponent measure; this is not formalized).

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 6.1.9 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Proposition 5.11 [Res87].
* L. de Haan and S. I. Resnick, *Limit theory for multivariate sample extremes*, Z. Wahrsch.
  Verw. Gebiete 40 (1977) [dHR77].
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace ExtremeValueTheory

section Truncated

/-- The integrand `1 - exp (-v / t)` of the truncated mean of a Fréchet variable with scale `v`. -/
lemma intervalIntegrable_one_sub_exp {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c) :
    IntervalIntegrable (fun t : ℝ ↦ 1 - Real.exp (-(v / t))) volume 0 c := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun (by fun_prop) ?_
  rw [uIoc_of_le hc]
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦ ?_)
  have h1 : Real.exp (-(v / t)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hv ht.1.le))
  dsimp only
  rw [Real.norm_eq_abs, norm_one, abs_of_nonneg (by linarith)]
  linarith [Real.exp_pos (-(v / t))]

lemma integral_one_sub_exp_nonneg {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c) :
    0 ≤ ∫ t in (0)..c, (1 - Real.exp (-(v / t))) := by
  refine intervalIntegral.integral_nonneg hc fun t ht ↦ ?_
  have : Real.exp (-(v / t)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hv ht.1))
  linarith

lemma integral_one_sub_exp_le {v c : ℝ} (hv : 0 < v) (hc : 1 ≤ c) :
    ∫ t in (0)..c, (1 - Real.exp (-(v / t))) ≤ 1 + v * Real.log c := by
  have hint1 := intervalIntegrable_one_sub_exp hv.le zero_le_one
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ 1 - Real.exp (-(v / t))) volume 1 c := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hc] at ht
    have : t ≠ 0 := by linarith [ht.1]
    fun_prop (disch := assumption)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hinv : IntervalIntegrable (fun t : ℝ ↦ v * t⁻¹) volume 1 c := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hc] at ht
    have : t ≠ 0 := by linarith [ht.1]
    fun_prop (disch := assumption)
  have h1 : ∫ t in (0)..1, (1 - Real.exp (-(v / t))) ≤ ∫ t in (0)..1, (1 : ℝ) :=
    intervalIntegral.integral_mono_on zero_le_one hint1 intervalIntegrable_const fun t _ ↦ by
      linarith [Real.exp_pos (-(v / t))]
  have h2 : ∫ t in (1)..c, (1 - Real.exp (-(v / t))) ≤ ∫ t in (1)..c, v * t⁻¹ :=
    intervalIntegral.integral_mono_on hc hint2 hinv fun t ht ↦ by
      have := Real.add_one_le_exp (-(v / t))
      rw [div_eq_mul_inv] at this ⊢
      linarith
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith), div_one]
    at h2
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1
  linarith

lemma le_integral_one_sub_exp {v c : ℝ} (hv : 0 < v) (hc : 0 ≤ c) :
    v * Real.log (c + v) - v * Real.log v ≤ ∫ t in (0)..c, (1 - Real.exp (-(v / t))) := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ v * (t + v)⁻¹) volume 0 c := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hc] at ht
    have : t + v ≠ 0 := by linarith [ht.1]
    fun_prop (disch := assumption)
  have hmono : ∫ t in (0)..c, v * (t + v)⁻¹ ≤ ∫ t in (0)..c, (1 - Real.exp (-(v / t))) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hc hint
      (intervalIntegrable_one_sub_exp hv.le hc) fun t ht ↦ ?_
    have ht0 : 0 < t := ht.1
    -- `1 - exp (-u) ≥ u / (1 + u)` with `u = v / t`
    have h1 := Real.add_one_le_exp (v / t)
    have h2 : Real.exp (-(v / t)) * Real.exp (v / t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 : Real.exp (-(v / t)) ≤ t / (t + v) := by
      rw [le_div_iff₀ (by positivity)]
      have : Real.exp (-(v / t)) * (v / t + 1) ≤ 1 := by
        nlinarith [Real.exp_pos (-(v / t))]
      have e : v / t + 1 = (t + v) / t := by field_simp; ring
      rw [e, mul_div_assoc'] at this
      rwa [div_le_one ht0] at this
    have h4 : v * (t + v)⁻¹ = 1 - t / (t + v) := by field_simp; ring
    rw [h4]
    linarith
  have hcomp : ∫ t in (0)..c, v * (t + v)⁻¹ = v * (Real.log (c + v) - Real.log v) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun t ↦ t⁻¹) v, zero_add,
      integral_inv_of_pos hv (by linarith), Real.log_div (by linarith) hv.ne']
  linarith [hcomp ▸ hmono]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ}

/-- **Truncated means of Fréchet-tailed variables**: if `P(X > r) = 1 - exp (-v / r)`, then
`E[min X c] = ∫₀ᶜ (1 - exp (-v / t)) dt`. -/
lemma lintegral_ofReal_min_eq (hXm : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    (hX : ∀ r > 0, μ {x | r < X x} = ENNReal.ofReal (1 - Real.exp (-(v / r)))) (hv : 0 ≤ v)
    {c : ℝ} (hc : 0 < c) :
    ∫⁻ x, ENNReal.ofReal (min (X x) c) ∂μ =
      ENNReal.ofReal (∫ t in (0)..c, (1 - Real.exp (-(v / t)))) := by
  rw [lintegral_eq_lintegral_meas_lt μ (hX0.mono fun x hx ↦ le_min hx hc.le)
    (hXm.min measurable_const).aemeasurable]
  have hcongr : ∫⁻ t in Ioi 0, μ {a | t < min (X a) c} =
      ∫⁻ t in Ioi 0, (Iio c).indicator (fun t ↦ ENNReal.ofReal (1 - Real.exp (-(v / t)))) t := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    by_cases htc : t < c
    · rw [indicator_of_mem (show t ∈ Iio c from htc), ← hX t ht]
      congr 1
      ext x
      simp [lt_min_iff, htc]
    · rw [indicator_of_notMem (show t ∉ Iio c from htc)]
      have : {a | t < min (X a) c} = ∅ := by
        ext x; simp only [mem_ofPred_eq, lt_min_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun _ ↦ htc
      rw [this, measure_empty]
  rw [hcongr, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, intervalIntegral.integral_of_le hc.le, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal]
  · exact ((intervalIntegrable_one_sub_exp hv hc.le).1).mono_set Ioo_subset_Ioc_self
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht ↦ ?_)
    have : Real.exp (-(v / t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hv ht.1.le))
    simp only [Pi.zero_apply]
    linarith

/-- **Logarithmic growth of truncated means**: if `P(X > r) = 1 - exp (-v / r)` for `r > 0`,
then `E[min X (a M)] / log M → v` as `M → ∞`, for every `a > 0`. -/
theorem tendsto_lintegral_min_div_log (hXm : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    (hX : ∀ r > 0, μ {x | r < X x} = ENNReal.ofReal (1 - Real.exp (-(v / r)))) (hv : 0 < v)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun M : ℝ ↦ (∫⁻ x, ENNReal.ofReal (min (X x) (a * M)) ∂μ).toReal / Real.log M)
      atTop (𝓝 v) := by
  have hlow : Tendsto (fun M : ℝ ↦ v + (v * Real.log a - v * Real.log v) / Real.log M) atTop
      (𝓝 v) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have hup : Tendsto (fun M : ℝ ↦ v + (1 + v * Real.log a) / Real.log M) atTop (𝓝 v) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have hev : ∀ᶠ M : ℝ in atTop, 1 < M ∧ 1 ≤ a * M := by
    filter_upwards [eventually_gt_atTop 1, eventually_ge_atTop a⁻¹] with M hM hMa
    refine ⟨hM, ?_⟩
    calc (1 : ℝ) = a * a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
      _ ≤ a * M := by gcongr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hev] with M ⟨hM, haM⟩
    have hlog : 0 < Real.log M := Real.log_pos hM
    have h1 := le_integral_one_sub_exp hv (c := a * M) (by linarith)
    have h2 : Real.log (a * M) ≤ Real.log (a * M + v) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [lintegral_ofReal_min_eq hXm hX0 hX hv.le (by linarith),
      ENNReal.toReal_ofReal (integral_one_sub_exp_nonneg hv.le (by linarith))]
    rw [Real.log_mul ha.ne' (by linarith)] at h2
    rw [show v + (v * Real.log a - v * Real.log v) / Real.log M =
      (v * (Real.log a + Real.log M) - v * Real.log v) / Real.log M by field_simp; ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hlog.le
  · filter_upwards [hev] with M ⟨hM, haM⟩
    have hlog : 0 < Real.log M := Real.log_pos hM
    rw [lintegral_ofReal_min_eq hXm hX0 hX hv.le (by linarith),
      ENNReal.toReal_ofReal (integral_one_sub_exp_nonneg hv.le (by linarith))]
    have h1 := integral_one_sub_exp_le hv haM
    rw [Real.log_mul ha.ne' (by linarith)] at h1
    rw [show v + (1 + v * Real.log a) / Real.log M =
      (1 + v * (Real.log a + Real.log M)) / Real.log M by field_simp; ring]
    exact div_le_div_of_nonneg_right h1 hlog.le

end Truncated

section MaxRatio

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `max_i x i / y i`; `x` lies outside the lower orthant `Iic (r • y)` iff `r < maxRatio y x`. -/
noncomputable def maxRatio (y x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i / y i

lemma measurable_maxRatio (y : ι → ℝ) : Measurable (maxRatio y) := by
  have := Finset.measurable_sup' (δ := ι → ℝ) (α := ℝ) Finset.univ_nonempty
    (f := fun i x ↦ x i / y i) fun i _ ↦ (measurable_pi_apply i).div_const _
  convert this using 1
  ext x
  simp [maxRatio, Finset.sup'_apply]

lemma lt_maxRatio_iff {y : ι → ℝ} (hy : ∀ i, 0 < y i) {r : ℝ} {x : ι → ℝ} :
    r < maxRatio y x ↔ ¬ x ≤ r • y := by
  simp only [maxRatio, Finset.lt_sup'_iff, Finset.mem_univ, true_and, Pi.le_def, not_forall,
    not_le, Pi.smul_apply, smul_eq_mul, lt_div_iff₀ (hy _)]

lemma div_le_maxRatio (y x : ι → ℝ) (i : ι) : x i / y i ≤ maxRatio y x :=
  Finset.le_sup' (fun i ↦ x i / y i) (Finset.mem_univ i)

lemma exists_maxRatio_eq (y x : ι → ℝ) : ∃ i, maxRatio y x = x i / y i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i ↦ x i / y i
  exact ⟨i, hi⟩

lemma le_maxRatio_one (x : ι → ℝ) (i : ι) : x i ≤ maxRatio 1 x := by
  simpa using div_le_maxRatio 1 x i

lemma maxRatio_one_pos {x : ι → ℝ} (hx : ∀ i, 0 < x i) : 0 < maxRatio 1 x :=
  (hx (Classical.arbitrary ι)).trans_le (le_maxRatio_one x _)

lemma maxRatio_nonneg {y x : ι → ℝ} (hy : ∀ i, 0 < y i) (hx : ∀ i, 0 < x i) :
    0 ≤ maxRatio y x :=
  (div_pos (hx (Classical.arbitrary ι)) (hy _)).le.trans (div_le_maxRatio y x _)

/-- The angular part `x / max_i x i` of `x`, clamped to `[0, 1]^ι`. -/
noncomputable def angular (x : ι → ℝ) : ι → unitInterval :=
  fun i ↦ Set.projIcc 0 1 zero_le_one (x i / maxRatio 1 x)

lemma measurable_angular : Measurable (angular (ι := ι)) :=
  measurable_pi_iff.2 fun i ↦ continuous_projIcc.measurable.comp
    ((measurable_pi_apply i).div (measurable_maxRatio 1))

lemma coe_angular_of_pos {x : ι → ℝ} (hx : ∀ i, 0 < x i) (i : ι) :
    (angular x i : ℝ) = x i / maxRatio 1 x := by
  have hR := maxRatio_one_pos hx
  rw [angular, Set.projIcc_of_mem _
    ⟨div_nonneg (hx i).le hR.le, (div_le_one hR).2 (le_maxRatio_one x i)⟩]

/-- The test function `θ ↦ max_i θ i / y i` on `[0, 1]^ι`. -/
noncomputable def spectralTest (y : ι → ℝ) : (ι → unitInterval) →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun θ ↦ Finset.univ.sup fun i ↦ Real.toNNReal ((θ i : ℝ) / y i), by fun_prop⟩

omit [Nonempty ι] in
lemma coe_spectralTest {y : ι → ℝ} (hy : ∀ i, 0 < y i) (θ : ι → unitInterval) :
    (spectralTest y θ : ℝ≥0∞) = ⨆ i, ENNReal.ofReal (θ i) / ENNReal.ofReal (y i) := by
  simp only [spectralTest, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
    ENNReal.coe_finset_sup, Finset.sup_univ_eq_iSup]
  congr 1
  ext i
  rw [← ENNReal.ofReal_div_of_pos (hy i)]
  rfl

omit [Nonempty ι] in
lemma measurable_spectralTest (y : ι → ℝ) :
    Measurable fun θ : ι → unitInterval ↦ (spectralTest y θ : ℝ≥0∞) :=
  (spectralTest y).continuous.measurable.coe_nnreal_ennreal

lemma spectralTest_angular {y x : ι → ℝ} (hy : ∀ i, 0 < y i) (hx : ∀ i, 0 < x i) :
    (spectralTest y (angular x) : ℝ≥0∞) = ENNReal.ofReal (maxRatio y x / maxRatio 1 x) := by
  have hR := maxRatio_one_pos hx
  rw [coe_spectralTest hy]
  refine le_antisymm (iSup_le fun i ↦ ?_) ?_
  · rw [← ENNReal.ofReal_div_of_pos (hy i), coe_angular_of_pos hx]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right (div_le_maxRatio y x i) hR.le
  · obtain ⟨j, hj⟩ := exists_maxRatio_eq y x
    refine le_iSup_of_le j (le_of_eq ?_)
    rw [← ENNReal.ofReal_div_of_pos (hy j), coe_angular_of_pos hx, hj, div_div, mul_comm,
      ← div_div]

/-- The ratio `max_i x i / y i ÷ max_i x i` lies in `[(∑ y)⁻¹, ∑ y⁻¹]`. -/
lemma maxRatio_div_mem {y x : ι → ℝ} (hy : ∀ i, 0 < y i) (hx : ∀ i, 0 < x i) :
    (∑ i, y i)⁻¹ ≤ maxRatio y x / maxRatio 1 x ∧
      maxRatio y x / maxRatio 1 x ≤ ∑ i, (y i)⁻¹ := by
  have hR := maxRatio_one_pos hx
  constructor
  · obtain ⟨k, hk⟩ := exists_maxRatio_eq 1 x
    simp only [Pi.one_apply, div_one] at hk
    have h1 : maxRatio 1 x / y k ≤ maxRatio y x := hk ▸ div_le_maxRatio y x k
    have h2 : y k ≤ ∑ i, y i :=
      Finset.single_le_sum (fun i _ ↦ (hy i).le) (Finset.mem_univ k)
    rw [le_div_iff₀ hR]
    calc (∑ i, y i)⁻¹ * maxRatio 1 x ≤ (y k)⁻¹ * maxRatio 1 x := by
          gcongr; exact hy k
      _ = maxRatio 1 x / y k := by rw [div_eq_inv_mul]
      _ ≤ _ := h1
  · obtain ⟨j, hj⟩ := exists_maxRatio_eq y x
    rw [div_le_iff₀ hR, hj]
    calc x j / y j ≤ maxRatio 1 x / y j :=
          div_le_div_of_nonneg_right (le_maxRatio_one x j) (hy j).le
      _ = (y j)⁻¹ * maxRatio 1 x := by rw [div_eq_inv_mul]
      _ ≤ _ := by
          gcongr
          exact Finset.single_le_sum (fun i _ ↦ (inv_pos.2 (hy i)).le) (Finset.mem_univ j)

/-- The distance `1 - max_i θ i` of `θ ∈ [0, 1]^ι` to the unit sphere of the sup norm. -/
noncomputable def sphereDefect : (ι → unitInterval) →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun θ ↦ 1 - Finset.univ.sup fun i ↦ Real.toNNReal (θ i : ℝ), by fun_prop⟩

lemma sphereDefect_angular {x : ι → ℝ} (hx : ∀ i, 0 < x i) : sphereDefect (angular x) = 0 := by
  obtain ⟨k, hk⟩ := exists_maxRatio_eq 1 x
  simp only [Pi.one_apply, div_one] at hk
  simp only [sphereDefect, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk]
  refine tsub_eq_zero_of_le (Finset.le_sup_of_le (Finset.mem_univ k) (le_of_eq ?_))
  rw [coe_angular_of_pos hx, hk, div_self (hx k).ne', Real.toNNReal_one]

omit [Nonempty ι] in
lemma exists_eq_one_of_sphereDefect_eq_zero {θ : ι → unitInterval} (h : sphereDefect θ = 0) :
    ∃ i, (θ i : ℝ) = 1 := by
  simp only [sphereDefect, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
    tsub_eq_zero_iff_le] at h
  obtain ⟨i, -, hi⟩ := (Finset.le_sup_iff zero_lt_one).1 h
  exact ⟨i, le_antisymm (θ i).2.2 (Real.one_le_toNNReal.1 hi)⟩

/-- The truncated angular measure `E[min (max_i Y i) M ; Θ ∈ ·]`, `Θ = Y / max_i Y i`. -/
noncomputable def truncAngular (μ : Measure (ι → ℝ)) (M : ℝ) : Measure (ι → unitInterval) :=
  (μ.withDensity fun x ↦ ENNReal.ofReal (min (maxRatio 1 x) M)).map angular

lemma measurable_truncDensity (M : ℝ) :
    Measurable fun x : ι → ℝ ↦ ENNReal.ofReal (min (maxRatio 1 x) M) :=
  ENNReal.measurable_ofReal.comp ((measurable_maxRatio 1).min measurable_const)

lemma lintegral_truncAngular (μ : Measure (ι → ℝ)) {f : (ι → unitInterval) → ℝ≥0∞}
    (hf : Measurable f) (M : ℝ) :
    ∫⁻ θ, f θ ∂(truncAngular μ M) =
      ∫⁻ x, ENNReal.ofReal (min (maxRatio 1 x) M) * f (angular x) ∂μ := by
  rw [truncAngular, lintegral_map hf measurable_angular]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_truncDensity M)
    (hf.comp measurable_angular)

lemma truncAngular_univ (μ : Measure (ι → ℝ)) (M : ℝ) :
    truncAngular μ M univ = ∫⁻ x, ENNReal.ofReal (min (maxRatio 1 x) M) ∂μ := by
  rw [truncAngular, Measure.map_apply measurable_angular MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

instance isFiniteMeasure_truncAngular (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (M : ℝ) :
    IsFiniteMeasure (truncAngular μ M) := by
  refine ⟨?_⟩
  rw [truncAngular_univ]
  refine (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (min_le_right _ M)).trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

namespace IsSimpleMaxStable

variable {μ : Measure (ι → ℝ)}

omit [Nonempty ι] in
/-- A simple max-stable vector has positive coordinates almost surely. -/
lemma ae_pos (h : IsSimpleMaxStable μ) : ∀ᵐ x ∂μ, ∀ i, 0 < x i := by
  refine ae_all_iff.2 fun i ↦ ?_
  have hle (n : ℕ) : μ {x | ¬ 0 < x i} ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1))) := by
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    calc μ {x | ¬ 0 < x i} ≤ μ {x | x i ≤ ((n : ℝ) + 1)⁻¹} :=
          measure_mono fun x hx ↦ (not_lt.1 hx).trans hpos.le
      _ = _ := by rw [h.measure_le i _ hpos, inv_inv]
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  rw [ae_iff]
  exact le_antisymm (ge_of_tendsto' hlim hle) bot_le

/-- `P(max_i Y i / y i > r) = 1 - exp (-V(y) / r)`. -/
lemma measure_lt_maxRatio (h : IsSimpleMaxStable μ) {y : ι → ℝ} (hy : ∀ i, 0 < y i) {r : ℝ}
    (hr : 0 < r) : μ {x | r < maxRatio y x} =
      ENNReal.ofReal (1 - Real.exp (-(maxStableExponent μ y / r))) := by
  have := h.isProbabilityMeasure
  have hry : ∀ i, 0 < (r • y) i := fun i ↦ by simpa using mul_pos hr (hy i)
  have hset : {x | r < maxRatio y x} = (Iic (r • y))ᶜ := by
    ext x
    simp only [mem_ofPred_eq, lt_maxRatio_iff hy, mem_compl_iff, mem_Iic]
  rw [hset, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_measureReal,
    ← h.exp_neg_maxStableExponent hry, h.maxStableExponent_smul hr hy,
    ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one, inv_mul_eq_div]

lemma maxStableExponent_pos (h : IsSimpleMaxStable μ) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    0 < maxStableExponent μ y :=
  (inv_pos.2 (hy (Classical.arbitrary ι))).trans_le (h.inv_le_maxStableExponent hy _)

lemma maxRatio_nonneg_ae (h : IsSimpleMaxStable μ) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    0 ≤ᵐ[μ] maxRatio y :=
  h.ae_pos.mono fun _ hx ↦ maxRatio_nonneg hy hx

/-- **The total mass of the truncated angular measure** grows like `V(1, …, 1) log M`. -/
theorem tendsto_truncAngular_univ (h : IsSimpleMaxStable μ) :
    Tendsto (fun M : ℝ ↦ (truncAngular μ M univ).toReal / Real.log M) atTop
      (𝓝 (maxStableExponent μ 1)) := by
  have h1 : ∀ i, (0 : ℝ) < (1 : ι → ℝ) i := fun _ ↦ one_pos
  have := tendsto_lintegral_min_div_log (measurable_maxRatio 1) (h.maxRatio_nonneg_ae h1)
    (fun r hr ↦ h.measure_lt_maxRatio h1 hr) (h.maxStableExponent_pos h1) one_pos
  simp only [one_mul] at this
  simpa only [truncAngular_univ] using this

/-- **The truncated angular integrals of the test functions** grow like `V(y) log M`. -/
theorem tendsto_lintegral_spectralTest (h : IsSimpleMaxStable μ) {y : ι → ℝ}
    (hy : ∀ i, 0 < y i) :
    Tendsto (fun M : ℝ ↦ (∫⁻ θ, spectralTest y θ ∂(truncAngular μ M)).toReal / Real.log M)
      atTop (𝓝 (maxStableExponent μ y)) := by
  have := h.isProbabilityMeasure
  set a₀ := (∑ i, y i)⁻¹
  set a₁ := ∑ i, (y i)⁻¹
  have ha₀ : 0 < a₀ := inv_pos.2 (Finset.sum_pos (fun i _ ↦ hy i) Finset.univ_nonempty)
  have ha₁ : 0 < a₁ := Finset.sum_pos (fun i _ ↦ inv_pos.2 (hy i)) Finset.univ_nonempty
  have hlim (a : ℝ) (ha : 0 < a) := tendsto_lintegral_min_div_log (measurable_maxRatio y)
    (h.maxRatio_nonneg_ae hy) (fun r hr ↦ h.measure_lt_maxRatio hy hr)
    (h.maxStableExponent_pos hy) ha
  have hsand : ∀ M : ℝ, 0 ≤ M → ∀ᵐ x ∂μ,
      ENNReal.ofReal (min (maxRatio y x) (a₀ * M)) ≤
        ENNReal.ofReal (min (maxRatio 1 x) M) * spectralTest y (angular x) ∧
      ENNReal.ofReal (min (maxRatio 1 x) M) * spectralTest y (angular x) ≤
        ENNReal.ofReal (min (maxRatio y x) (a₁ * M)) := fun M hM ↦ h.ae_pos.mono fun x hx ↦ by
    have hR := maxRatio_one_pos hx
    have hq := maxRatio_div_mem hy hx
    have hq0 : 0 ≤ maxRatio y x / maxRatio 1 x := div_nonneg (maxRatio_nonneg hy hx) hR.le
    rw [spectralTest_angular hy hx, ← ENNReal.ofReal_mul (le_min hR.le hM),
      min_mul_of_nonneg _ _ hq0, mul_div_cancel₀ _ hR.ne']
    exact ⟨ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by rw [mul_comm]; gcongr; exact hq.1)),
      ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by rw [mul_comm M]; gcongr; exact hq.2))⟩
  have hfin : ∀ M : ℝ, ∫⁻ x, ENNReal.ofReal (min (maxRatio y x) (a₁ * M)) ∂μ ≠ ∞ := fun M ↦
    ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (a₁ * M) ∂μ)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top (by finiteness) (measure_ne_top _ _))
      (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim a₀ ha₀) (hlim a₁ ha₁) ?_ ?_
  all_goals
    filter_upwards [eventually_gt_atTop 1] with M hM
    have hlog : 0 < Real.log M := Real.log_pos hM
    refine div_le_div_of_nonneg_right ?_ hlog.le
    rw [lintegral_truncAngular μ (measurable_spectralTest y)]
    have hup := lintegral_mono_ae ((hsand M (by linarith)).mono fun x hx ↦ hx.2)
  · exact ENNReal.toReal_mono (ne_top_of_le_ne_top (hfin M) hup)
      (lintegral_mono_ae ((hsand M (by linarith)).mono fun x hx ↦ hx.1))
  · exact ENNReal.toReal_mono (hfin M) hup

end IsSimpleMaxStable

/-- The truncated angular measure as a finite measure. -/
noncomputable def truncAngularFM (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (M : ℝ) :
    FiniteMeasure (ι → unitInterval) :=
  ⟨truncAngular μ M, inferInstance⟩

/-- The truncated angular measures normalized by `log n`, as finite measures on `[0, 1]^ι`. -/
noncomputable def scaledTruncAngular (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (n : ℕ) :
    FiniteMeasure (ι → unitInterval) :=
  (Real.log n)⁻¹.toNNReal • truncAngularFM μ n

lemma coe_scaledTruncAngular_testAgainstNN (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (n : ℕ)
    (f : (ι → unitInterval) →ᵇ ℝ≥0) :
    ((scaledTruncAngular μ n).testAgainstNN f : ℝ) =
      (∫⁻ θ, f θ ∂(truncAngular μ n)).toReal / Real.log n := by
  rw [scaledTruncAngular, FiniteMeasure.smul_testAgainstNN_apply, smul_eq_mul, NNReal.coe_mul,
    Real.coe_toNNReal _ (inv_nonneg.2 (Real.log_natCast_nonneg n)), FiniteMeasure.testAgainstNN,
    truncAngularFM, FiniteMeasure.toMeasure_mk, ENNReal.coe_toNNReal_eq_toReal, div_eq_inv_mul]

lemma coe_scaledTruncAngular_mass (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (n : ℕ) :
    ((scaledTruncAngular μ n).mass : ℝ) = (truncAngular μ n univ).toReal / Real.log n := by
  rw [← FiniteMeasure.testAgainstNN_one, coe_scaledTruncAngular_testAgainstNN]
  simp

/-- A cluster point of a sequence of finite measures integrates a test function to the limit of
its integrals, when this limit exists. -/
lemma eq_of_clusterPt_testAgainstNN {K : Type*} [MeasurableSpace K] [TopologicalSpace K]
    [OpensMeasurableSpace K] {u : ℕ → FiniteMeasure K} {P : FiniteMeasure K}
    (hP : ClusterPt P (map u atTop)) (f : K →ᵇ ℝ≥0) {L : ℝ}
    (hL : Tendsto (fun n ↦ ((u n).testAgainstNN f : ℝ)) atTop (𝓝 L)) :
    (P.testAgainstNN f : ℝ) = L := by
  have hc : Continuous fun ν : FiniteMeasure K ↦ (ν.testAgainstNN f : ℝ) :=
    NNReal.continuous_coe.comp (FiniteMeasure.continuous_testAgainstNN_eval f)
  have h1 : MapClusterPt (P.testAgainstNN f : ℝ) atTop fun n ↦ ((u n).testAgainstNN f : ℝ) :=
    (show MapClusterPt P atTop u from hP).continuousAt_comp
      (f := fun ν : FiniteMeasure K ↦ (ν.testAgainstNN f : ℝ)) hc.continuousAt
  exact eq_of_nhds_neBot (h1.clusterPt.mono hL)

namespace IsSimpleMaxStable

variable {μ : Measure (ι → ℝ)}

/-- **Existence of the angular measure** on `[0, 1]^ι`: a finite measure `P` with
`∫ max_i θ i / y i dP(θ) = V(y)` for all `y` with positive coordinates. It is a cluster point of
the measures `E[min (max_i Y i) n ; Y / max_i Y i ∈ ·] / log n`. -/
theorem exists_angularMeasure (h : IsSimpleMaxStable μ) :
    ∃ P : FiniteMeasure (ι → unitInterval),
      (∀ᵐ θ ∂(P : Measure (ι → unitInterval)), ∃ i, (θ i : ℝ) = 1) ∧
      ∀ y : ι → ℝ, (∀ i, 0 < y i) →
        ∫⁻ θ, spectralTest y θ ∂(P : Measure (ι → unitInterval)) =
          ENNReal.ofReal (maxStableExponent μ y) := by
  have := h.isProbabilityMeasure
  have hV1 := h.maxStableExponent_pos (y := 1) fun _ ↦ one_pos
  set C : ℝ≥0 := (maxStableExponent μ 1 + 1).toNNReal
  have hmass : Tendsto (fun n : ℕ ↦ ((scaledTruncAngular μ n).mass : ℝ)) atTop
      (𝓝 (maxStableExponent μ 1)) := by
    simpa only [Function.comp_def, coe_scaledTruncAngular_mass] using
      h.tendsto_truncAngular_univ.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n in atTop, scaledTruncAngular μ n ∈ {ν : FiniteMeasure _ | ν.mass ≤ C} := by
    filter_upwards [hmass.eventually (gt_mem_nhds (lt_add_one (maxStableExponent μ 1)))]
      with n hn
    exact (Real.le_toNNReal_iff_coe_le (by linarith)).2 hn.le
  obtain ⟨P, -, hP⟩ := (isCompact_setOfPred_finiteMeasure_le_of_compactSpace
    (ι → unitInterval) C).exists_clusterPt (f := map (scaledTruncAngular μ) atTop)
    (le_principal_iff.2 hev)
  refine ⟨P, ?_, fun y hy ↦ ?_⟩
  · -- the cluster point is concentrated on the unit sphere `max_i θ i = 1`
    have hL : Tendsto (fun n : ℕ ↦ ((scaledTruncAngular μ n).testAgainstNN sphereDefect : ℝ))
        atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [coe_scaledTruncAngular_testAgainstNN, lintegral_truncAngular μ
        sphereDefect.continuous.measurable.coe_nnreal_ennreal]
      rw [lintegral_congr_ae (g := fun _ ↦ 0) (h.ae_pos.mono fun x hx ↦ by
        simp [sphereDefect_angular hx]), lintegral_zero, ENNReal.toReal_zero, zero_div]
    have h0 := eq_of_clusterPt_testAgainstNN hP _ hL
    have h0' : ∫⁻ θ, (sphereDefect θ : ℝ≥0∞) ∂(P : Measure (ι → unitInterval)) = 0 := by
      rw [← FiniteMeasure.testAgainstNN_coe_eq]
      exact_mod_cast NNReal.coe_eq_zero.1 h0
    filter_upwards [(lintegral_eq_zero_iff
      sphereDefect.continuous.measurable.coe_nnreal_ennreal).1 h0'] with θ hθ
    exact exists_eq_one_of_sphereDefect_eq_zero (by simpa using hθ)
  have hL : Tendsto (fun n : ℕ ↦ ((scaledTruncAngular μ n).testAgainstNN (spectralTest y) : ℝ))
      atTop (𝓝 (maxStableExponent μ y)) := by
    simpa only [Function.comp_def, coe_scaledTruncAngular_testAgainstNN] using
      (h.tendsto_lintegral_spectralTest hy).comp tendsto_natCast_atTop_atTop
  rw [← FiniteMeasure.testAgainstNN_coe_eq, ← eq_of_clusterPt_testAgainstNN hP _ hL,
    ENNReal.ofReal_coe_nnreal]

end IsSimpleMaxStable

end MaxRatio

section Main

variable {ι : Type*} [Fintype ι] {μ : Measure (ι → ℝ)}

/-- The embedding `[0, 1]^ι → [0, ∞]^ι`. -/
noncomputable def unitCubeToENNReal (θ : ι → unitInterval) : ι → ℝ≥0∞ :=
  fun i ↦ ENNReal.ofReal (θ i)

omit [Fintype ι] in
lemma measurable_unitCubeToENNReal : Measurable (unitCubeToENNReal (ι := ι)) :=
  measurable_pi_iff.2 fun i ↦
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp (measurable_pi_apply i))

lemma measurable_spectralIntegrand (y : ι → ℝ) :
    Measurable fun w : ι → ℝ≥0∞ ↦ ⨆ i, w i / ENNReal.ofReal (y i) :=
  Measurable.iSup fun i ↦ (measurable_pi_apply i).div_const _

lemma measurableSet_le_one : MeasurableSet {w : ι → ℝ≥0∞ | ∀ i, w i ≤ 1} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le (measurable_pi_apply i) measurable_const

namespace IsSimpleMaxStable

/-- **The spectral representation of simple max-stable laws** ([dHF, Theorem 6.1.9 "⇒"];
[Res87, Proposition 5.11]; de Haan–Resnick 1977): every simple max-stable law `μ` on `ℝ^ι`
(`ι` finite) has a finite spectral measure `H`, concentrated on `[0, 1]^ι`, normalized by
`∫ w i dH(w) = 1`, with `P(Y ≤ y) = exp (-∫ max_i w i / y i dH(w))`. -/
theorem exists_hasSpectralMeasure (h : IsSimpleMaxStable μ) :
    ∃ H : Measure (ι → ℝ≥0∞), IsFiniteMeasure H ∧ (∀ᵐ w ∂H, ∀ i, w i ≤ 1) ∧
      (∀ᵐ w ∂H, ⨆ i, w i = 1) ∧ (∀ i, ∫⁻ w, w i ∂H = 1) ∧ HasSpectralMeasure μ H := by
  have := h.isProbabilityMeasure
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨0, inferInstance, by simp, by simp, fun i ↦ isEmptyElim i, fun y _ ↦ ?_⟩
    rw [show Iic y = univ from eq_univ_of_forall fun x i ↦ isEmptyElim i, measure_univ]
    simp
  obtain ⟨P, hsph, hP⟩ := h.exists_angularMeasure
  refine ⟨(P : Measure (ι → unitInterval)).map unitCubeToENNReal, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [ae_map_iff measurable_unitCubeToENNReal.aemeasurable measurableSet_le_one]
    exact Eventually.of_forall fun θ i ↦ ENNReal.ofReal_le_one.2 (θ i).2.2
  · rw [ae_map_iff measurable_unitCubeToENNReal.aemeasurable (measurableSet_eq_fun
      (Measurable.iSup fun i ↦ measurable_pi_apply i) measurable_const)]
    filter_upwards [hsph] with θ ⟨k, hk⟩
    refine le_antisymm (iSup_le fun i ↦ ENNReal.ofReal_le_one.2 (θ i).2.2)
      (le_iSup_of_le k ?_)
    simp [unitCubeToENNReal, hk]
  · intro i
    classical
    rw [lintegral_map (measurable_pi_apply i) measurable_unitCubeToENNReal]
    simp only [unitCubeToENNReal]
    set I := ∫⁻ θ, ENNReal.ofReal (θ i : ℝ) ∂(P : Measure (ι → unitInterval))
    -- the test points `y n = (1 at i, n + 1 elsewhere)`
    set y : ℕ → ι → ℝ := fun n j ↦ if j = i then 1 else (n : ℝ) + 1 with hydef
    have hy (n : ℕ) : ∀ j, 0 < y n j := fun j ↦ by
      by_cases hj : j = i <;> simp [hydef, hj]; positivity
    have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hsum : Tendsto (fun n : ℕ ↦ ∑ j, (y n j)⁻¹) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ ↦ ∑ j, (y n j)⁻¹) atTop
          (𝓝 (∑ j, if j = i then (1 : ℝ) else 0)) :=
        tendsto_finsetSum _ fun j _ ↦ by
          by_cases hj : j = i
          · simp [hydef, hj]
          · simpa [hydef, hj] using hinv
      simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using this
    -- `I ≤ V(y n) ≤ ∑ j, 1 / y n j → 1`
    have hle (n : ℕ) : I ≤ ENNReal.ofReal (∑ j, (y n j)⁻¹) := by
      refine le_trans ?_ (ENNReal.ofReal_le_ofReal (h.maxStableExponent_le_sum_inv (hy n)))
      rw [← hP _ (hy n)]
      refine lintegral_mono fun θ ↦ ?_
      rw [coe_spectralTest (hy n)]
      refine le_iSup_of_le i (le_of_eq ?_)
      simp [hydef]
    -- `1 ≤ V(y n) ≤ I + P(univ) / (n + 1)`
    have hge (n : ℕ) : 1 ≤ I + ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * P.mass := by
      have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (maxStableExponent μ (y n)) := by
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        simpa [hydef] using h.inv_le_maxStableExponent (hy n) i
      rw [← hP _ (hy n)] at h1
      have hpt : ∀ θ : ι → unitInterval, (spectralTest (y n) θ : ℝ≥0∞) ≤
          ENNReal.ofReal (θ i : ℝ) + ENNReal.ofReal ((n : ℝ) + 1)⁻¹ := fun θ ↦ by
        rw [coe_spectralTest (hy n)]
        refine iSup_le fun j ↦ ?_
        by_cases hj : j = i
        · subst hj
          simp [hydef]
        · simp only [hydef, hj, ite_false]
          refine le_add_left ((ENNReal.div_le_div_right (ENNReal.ofReal_le_one.2 (θ j).2.2)
            _).trans (le_of_eq ?_))
          rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      refine h1.trans ((lintegral_mono hpt).trans (le_of_eq ?_))
      rw [lintegral_add_right _ measurable_const, lintegral_const, FiniteMeasure.ennreal_mass]
    refine le_antisymm ?_ ?_
    · have := ENNReal.tendsto_ofReal hsum
      rw [ENNReal.ofReal_one] at this
      exact ge_of_tendsto' this hle
    · have : Tendsto (fun n : ℕ ↦ I + ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * P.mass) atTop
          (𝓝 (I + 0 * P.mass)) := by
        refine tendsto_const_nhds.add (ENNReal.Tendsto.mul_const ?_ (Or.inr ENNReal.coe_ne_top))
        simpa using ENNReal.tendsto_ofReal hinv
      rw [zero_mul, add_zero] at this
      exact ge_of_tendsto' this hge
  · intro y hy
    rw [lintegral_map (measurable_spectralIntegrand y) measurable_unitCubeToENNReal]
    simp only [unitCubeToENNReal]
    simp_rw [← coe_spectralTest hy]
    rw [hP y hy, ENNReal.toReal_ofReal (h.maxStableExponent_pos hy).le,
      h.exp_neg_maxStableExponent hy, ofReal_measureReal]

end IsSimpleMaxStable

omit [Fintype ι] in
/-- The total mass of a spectral measure concentrated on the unit sphere of the sup norm is the
extremal coefficient `θ = V(1, …, 1)`. -/
theorem HasSpectralMeasure.measure_univ_toReal {H : Measure (ι → ℝ≥0∞)}
    (hμ : HasSpectralMeasure μ H) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    (H univ).toReal = extremalCoefficient μ := by
  rw [extremalCoefficient, hμ.maxStableExponent_eq fun _ ↦ one_pos, ← lintegral_one]
  congr 1
  refine (lintegral_congr_ae (hH.mono fun w hw ↦ ?_)).symm
  simp [hw]

/-! ### Bivariate consequences: the Pickands dependence function -/

namespace IsSimpleMaxStable

variable {ν : Measure (Fin 2 → ℝ)}

/-- Every bivariate simple max-stable law has a normalized spectral measure, and its Pickands
function is `A(t) = ∫ max(t w 0, (1 - t) w 1) dH(w)` on `[0, 1]`. -/
theorem exists_pickandsDependence_eq_pickandsSpectral (h : IsSimpleMaxStable ν) :
    ∃ H : Measure (Fin 2 → ℝ≥0∞), IsFiniteMeasure H ∧ (∀ i, ∫⁻ w, w i ∂H = 1) ∧
      HasSpectralMeasure ν H ∧ EqOn (pickandsDependence ν) (pickandsSpectral H) (Icc 0 1) := by
  obtain ⟨H, hfin, -, -, hH, hS⟩ := h.exists_hasSpectralMeasure
  exact ⟨H, hfin, hH, hS, fun _ ht ↦ hS.pickandsDependence_eq hH ht⟩

/-- **Convexity of the Pickands dependence function** ([Pickands 1981]; [dHF, §6.1.5]) for every
bivariate simple max-stable law. -/
theorem convexOn_pickandsDependence (h : IsSimpleMaxStable ν) :
    ConvexOn ℝ (Icc 0 1) (pickandsDependence ν) := by
  obtain ⟨H, -, -, -, hH, hS⟩ := h.exists_hasSpectralMeasure
  exact hS.convexOn_pickands hH

end IsSimpleMaxStable

end Main

end ExtremeValueTheory
