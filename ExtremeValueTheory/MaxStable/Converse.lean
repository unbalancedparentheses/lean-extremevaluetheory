import ExtremeValueTheory.Multivariate.Dependence
import Mathlib.MeasureTheory.Measure.Prokhorov

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

lemma coe_spectralTest {y : ι → ℝ} (hy : ∀ i, 0 < y i) (θ : ι → unitInterval) :
    (spectralTest y θ : ℝ≥0∞) = ⨆ i, ENNReal.ofReal (θ i) / ENNReal.ofReal (y i) := by
  simp only [spectralTest, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
    ENNReal.coe_finset_sup, Finset.sup_univ_eq_iSup]
  congr 1
  ext i
  rw [← ENNReal.ofReal_div_of_pos (hy i)]
  rfl

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

end MaxRatio

end ExtremeValueTheory
