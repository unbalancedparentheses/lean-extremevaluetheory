import ExtremeValueTheory.RegularVariation.Composition
import ExtremeValueTheory.RegularVariation.KaramataIntegrals
import ExtremeValueTheory.RegularVariation.RepresentationIndex
import ExtremeValueTheory.Minimality.ClassicalKaramata

/-!
# Known answers and non-vacuity: regular variation

Checks the general forms of Karamata's theorem, its converse, the two tails of the uniform
convergence theorem and the facts of `RegularVariation/` on explicit functions, in cases that the
earlier, monotone forms did not reach.

References: [BGT] Bingham, Goldie, Teugels, *Regular Variation* (1987), §1.5 and §1.6.
-/

open Filter Topology Set Real MeasureTheory ExtremeValueTheory

namespace Test.KnownAnswers.RegularVariation

/-! ### Karamata's theorem from an arbitrary lower limit -/

/-- The function `t⁻²` on `(-∞, 1]`, `1` on `(1, ∞)`: not integrable near `0`, regularly varying of
index `0`. The motivating example of `IsRegularlyVarying.tendsto_integral_interval_div`. -/
private noncomputable def singularAtZero (t : ℝ) : ℝ := if t ≤ 1 then (t ^ 2)⁻¹ else 1

/-- `singularAtZero` is measurable. -/
private lemma measurable_singularAtZero : Measurable singularAtZero :=
  Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

/-- `singularAtZero` is regularly varying with index `0`. -/
private lemma isRegularlyVarying_singularAtZero : IsRegularlyVarying singularAtZero 0 := by
  refine (IsRegularlyVarying.const one_pos).congr ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [singularAtZero, not_le.2 hx]

/-- Exercises `IsRegularlyVarying.tendsto_integral_interval_div` where the old form with lower limit `0` did
not apply: the limit `1 / (0 + 1) = 1` for a function not integrable near `0`. -/
theorem test_tendsto_integral_div_singularAtZero :
    Tendsto (fun x => (∫ t in (1 : ℝ)..x, singularAtZero t) / (x * singularAtZero x)) atTop
      (𝓝 (1 / (0 + 1))) := by
  refine isRegularlyVarying_singularAtZero.tendsto_integral_interval_div measurable_singularAtZero
    (by norm_num) fun x hx => ?_
  refine (intervalIntegrable_const (c := (1 : ℝ))).congr fun t ht => ?_
  rw [uIoc_of_le hx] at ht
  simp [singularAtZero, not_le.2 ht.1]

/-! ### Karamata's converse without monotonicity -/

/-- Exercises `IsRegularlyVarying.of_tendsto_mul_div_integral` on `f x = x`, which is increasing and
so out of reach of the antitone form: `x * x / ∫₀ˣ t dt = 2 = ρ + 1`, and the index is `ρ = 1`. -/
theorem test_of_tendsto_mul_div_integral_id : IsRegularlyVarying (fun x : ℝ => x) 1 := by
  refine IsRegularlyVarying.of_tendsto_mul_div_integral (a := 0)
    (eventually_gt_atTop 0) (by norm_num) ?_
  refine (tendsto_const_nhds (x := (1 : ℝ) + 1)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [integral_id]
  field_simp
  ring

/-- Exercises `IsRegularlyVarying.of_tendsto_rpow_mul_div_integral`, the weighted form, on
`f x = x` with weight `σ = 1`: `x² * x / ∫₀ˣ t * t dt = 3 = σ + ρ + 1`, and the index is `ρ = 1`. -/
theorem test_of_tendsto_rpow_mul_div_integral_id : IsRegularlyVarying (fun x : ℝ => x) 1 := by
  refine IsRegularlyVarying.of_tendsto_rpow_mul_div_integral (a := 0) (σ := 1)
    (eventually_gt_atTop 0) (by norm_num) ?_
  refine (tendsto_const_nhds (x := (1 : ℝ) + 1 + 1)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have : ∫ t in (0 : ℝ)..x, t ^ (1 : ℝ) * t = x ^ 3 / 3 := by
    simp only [rpow_one]
    have : ∀ t : ℝ, t * t = t ^ 2 := fun t => (sq t).symm
    simp only [this, integral_pow]
    norm_num
  rw [this, show (1 : ℝ) + 1 = 2 by norm_num, rpow_ofNat]
  field_simp
  ring

/-! ### The tails of the uniform convergence theorem -/

/-- Exercises `IsRegularlyVarying.tendstoUniformlyOn_Ici_of_measurableNearTop` on `x⁻¹`, `ρ = -1`:
the convergence is uniform on the unbounded set `[1, ∞)`. -/
theorem test_tendstoUniformlyOn_Ici_inv :
    TendstoUniformlyOn (fun (x c : ℝ) => (c * x) ^ (-1 : ℝ) / x ^ (-1 : ℝ)) (fun c => c ^ (-1 : ℝ)) atTop
      (Ici 1) :=
  (IsRegularlyVarying.rpow_id (-1)).tendstoUniformlyOn_Ici_of_measurableNearTop
    (Measurable.measurableNearTop (by fun_prop)) (by norm_num) one_pos

/-- Exercises `IsRegularlyVarying.tendstoUniformlyOn_Ioc_of_measurableNearTop` on `x²`, `ρ = 2`,
which is bounded on each `(0, b]`. -/
theorem test_tendstoUniformlyOn_Ioc_sq (b : ℝ) :
    TendstoUniformlyOn (fun (x c : ℝ) => (c * x) ^ (2 : ℝ) / x ^ (2 : ℝ)) (fun c => c ^ (2 : ℝ)) atTop
      (Ioc 0 b) := by
  refine (IsRegularlyVarying.rpow_id 2).tendstoUniformlyOn_Ioc_of_measurableNearTop
    (Measurable.measurableNearTop (by fun_prop)) two_pos (fun b => ⟨b ^ (2 : ℝ), fun y hy => ?_⟩) b
  rw [abs_of_nonneg (rpow_nonneg hy.1.le _)]
  exact rpow_le_rpow hy.1.le hy.2 two_pos.le

/-- `ρ > 0` gives `f → ∞`: `IsRegularlyVarying.tendsto_atTop_of_measurableNearTop` on `x²`. -/
theorem test_tendsto_atTop_rpow : Tendsto (fun x : ℝ => x ^ (2 : ℝ)) atTop atTop :=
  (IsRegularlyVarying.rpow_id 2).tendsto_atTop_of_measurableNearTop
    (Measurable.measurableNearTop (by fun_prop)) two_pos

/-- `ρ < 0` gives `f → 0`: `IsRegularlyVarying.tendsto_zero_of_measurableNearTop` on `x⁻¹`. -/
theorem test_tendsto_zero_rpow : Tendsto (fun x : ℝ => x ^ (-1 : ℝ)) atTop (𝓝 0) :=
  (IsRegularlyVarying.rpow_id (-1)).tendsto_zero_of_measurableNearTop
    (Measurable.measurableNearTop (by fun_prop)) (by norm_num)

/-! ### The index `-1` -/

/-- `t⁻¹` for `t ≥ 1`, and `0` below, whose integral from `1` to `x` is `log x`. -/
private noncomputable def invFromOne : ℝ → ℝ := (Ici (1 : ℝ)).indicator fun t => t ^ (-1 : ℝ)

/-- `invFromOne` is measurable. -/
private lemma measurable_invFromOne : Measurable invFromOne :=
  Measurable.indicator (by fun_prop) measurableSet_Ici

/-- `invFromOne` is regularly varying with index `-1`. -/
private lemma isRegularlyVarying_invFromOne : IsRegularlyVarying invFromOne (-1) :=
  (IsRegularlyVarying.rpow_id (-1)).indicator_Ici 1

/-- `invFromOne` is nonnegative. -/
private lemma invFromOne_nonneg (x : ℝ) : 0 ≤ invFromOne x := by
  refine indicator_nonneg (fun t ht => rpow_nonneg (zero_le_one.trans (mem_Ici.1 ht)) _) x

/-- `invFromOne` is interval integrable from `1`. -/
private lemma intervalIntegrable_invFromOne (x : ℝ) (hx : x ≥ 1) :
    IntervalIntegrable invFromOne volume 1 x := by
  have h : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x :=
    intervalIntegral.intervalIntegrable_inv (fun t ht => by
      rw [uIcc_of_le hx] at ht
      exact (zero_lt_one.trans_le ht.1).ne') continuousOn_id
  refine h.congr fun t ht => ?_
  rw [uIoc_of_le hx] at ht
  simp [invFromOne, indicator_of_mem (mem_Ici.2 ht.1.le), rpow_neg_one]

/-- `∫₁ˣ invFromOne = log x`. -/
private lemma integral_invFromOne {x : ℝ} (hx : x ≥ 1) :
    ∫ t in (1 : ℝ)..x, invFromOne t = log x := by
  have h : ∫ t in (1 : ℝ)..x, invFromOne t = ∫ t in (1 : ℝ)..x, t⁻¹ :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hx] at ht
      simp [invFromOne, indicator_of_mem (mem_Ici.2 ht.1), rpow_neg_one]
  rw [h, integral_inv_of_pos one_pos (by linarith), div_one]

/-- Exercises `IsRegularlyVarying.tendsto_integral_div_atTop_of_neg_one`: at index `-1` the ratio of
Karamata's theorem is `log x`, which tends to `∞`. -/
theorem test_tendsto_integral_div_atTop_invFromOne :
    Tendsto (fun x => (∫ t in (1 : ℝ)..x, invFromOne t) / (x * invFromOne x)) atTop atTop :=
  isRegularlyVarying_invFromOne.tendsto_integral_div_atTop_of_neg_one
    measurable_invFromOne.measurableNearTop (fun x _ => invFromOne_nonneg x)
    intervalIntegrable_invFromOne

/-- Exercises `IsRegularlyVarying.integral_of_neg_one`: `x ↦ ∫₁ˣ t⁻¹ dt = log x` is slowly varying,
as `isSlowlyVarying_log` states directly. -/
theorem test_integral_of_neg_one_log : IsSlowlyVarying log := by
  have h := isRegularlyVarying_invFromOne.integral_of_neg_one
    measurable_invFromOne.measurableNearTop (fun x _ => invFromOne_nonneg x)
    intervalIntegrable_invFromOne
  have := h.isRegularlyVarying.congr (g := log) (by
    filter_upwards [eventually_ge_atTop 1] with x hx
    exact integral_invFromOne hx)
  exact this.isSlowlyVarying

/-- Exercises `IsRegularlyVarying.tendsto_integral_Ioi_div_atTop_of_neg_one` on
`logTail 2 x = (x log² x)⁻¹`, whose ratio is `log x`
(`ExtremeValueTheory.Minimality.integral_Ioi_div_logTail_two`). -/
theorem test_tendsto_integral_Ioi_div_atTop_logTail :
    Tendsto (fun x => (∫ t in Ioi x, Minimality.logTail 2 t) / (x * Minimality.logTail 2 x)) atTop
      atTop :=
  (Minimality.isRegularlyVarying_logTail 2).tendsto_integral_Ioi_div_atTop_of_neg_one
    (Minimality.antitone_logTail 2).measurable.measurableNearTop
    (Minimality.integrableOn_Ioi_logTail_two 0)

/-- Exercises `IsRegularlyVarying.integral_Ioi_of_neg_one`: `∫ₓ^∞ logTail 2 = (log x)⁻¹` is slowly
varying. -/
theorem test_integral_Ioi_of_neg_one_logTail :
    IsSlowlyVarying fun x => ∫ t in Ioi x, Minimality.logTail 2 t :=
  (Minimality.isRegularlyVarying_logTail 2).integral_Ioi_of_neg_one
    (Minimality.antitone_logTail 2).measurable.measurableNearTop
    (Minimality.integrableOn_Ioi_logTail_two 0)

/-- Exercises `IsRegularlyVarying.integral`: `x ↦ ∫₀ˣ t dt` is regularly varying of index `2`. -/
theorem test_integral_id :
    IsRegularlyVarying (fun x => ∫ t in (0 : ℝ)..x, t ^ (1 : ℝ)) (1 + 1) :=
  (IsRegularlyVarying.rpow_id 1).integral (Measurable.measurableNearTop (by fun_prop))
    (by norm_num) fun x _ => (continuous_id.rpow_const fun _ => Or.inr zero_le_one).intervalIntegrable _ _

/-- Exercises `IsRegularlyVarying.integral_Ioi_of_measurableNearTop`: `∫ₓ^∞ t⁻² dt` is regularly varying of index `-1`. -/
theorem test_integral_Ioi_inv_sq :
    IsRegularlyVarying (fun x => ∫ t in Ioi x, t ^ (-2 : ℝ)) (1 - 2) :=
  IsRegularlyVarying.integral_Ioi_of_measurableNearTop (Measurable.measurableNearTop (by fun_prop))
    (IsRegularlyVarying.rpow_id (-2)) (by norm_num)

/-- Karamata's constant at `α = 2`, from `tendsto_integral_Ioi_div_of_measurableNearTop`:
`∫ₓ^∞ t⁻² dt / (x x⁻²) → 1/(2 - 1) = 1`, the exact value, since `∫ₓ^∞ t⁻² dt = x⁻¹`. -/
theorem test_tendsto_integral_Ioi_div_inv_sq :
    Tendsto (fun x : ℝ => (∫ t in Ioi x, t ^ (-2 : ℝ)) / (x * x ^ (-2 : ℝ))) atTop (𝓝 1) := by
  have h := IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurableNearTop (α := 2)
    (F := fun t : ℝ => t ^ (-2 : ℝ)) (Measurable.measurableNearTop (by fun_prop))
    (IsRegularlyVarying.rpow_id (-2)) (by norm_num)
  rwa [show (1 : ℝ) / (2 - 1) = 1 by norm_num] at h

/-- Exercises `tendsto_integral_div_of_measurableNearTop`: from the lower limit `a = 2`, where
`singularAtZero` is integrable although it is not near `0`, the ratio tends to `1/(ρ + 1)` with
`ρ = 0`; the exact value, since the function is `1` on `(1, ∞)`. -/
theorem test_tendsto_integral_div_singularAtZero_of_measurableNearTop :
    Tendsto (fun x : ℝ => (∫ t in (2 : ℝ)..x, singularAtZero t) / (x * singularAtZero x)) atTop
      (𝓝 (1 / (0 + 1))) :=
  isRegularlyVarying_singularAtZero.tendsto_integral_div_of_measurableNearTop
    measurable_singularAtZero.measurableNearTop (by norm_num) fun x hx => by
      refine (intervalIntegrable_const (c := (1 : ℝ))).congr ?_
      rw [uIoc_of_le hx]
      intro t ht
      have ht1 : ¬ t ≤ 1 := by linarith [ht.1]
      simp [singularAtZero, ht1]

/-! ### The representation theorem for index `ρ` -/

/-- Exercises `IsRegularlyVarying.of_representation` on the known representation of `x ^ ρ`:
`x ^ ρ = 1 * exp (∫ t in 1..x, ρ / t)` for `x ≥ 1`, with `c = 1` and `r = ρ`. -/
theorem test_of_representation_rpow (ρ : ℝ) : IsRegularlyVarying (fun x : ℝ => x ^ ρ) ρ := by
  refine IsRegularlyVarying.of_representation (a := 1) (c₀ := 1) (c := fun _ => 1)
    (r := fun _ => ρ) one_pos one_pos tendsto_const_nhds tendsto_const_nhds (fun x hx => ?_)
    fun x hx => ?_
  · have h : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x :=
      intervalIntegral.intervalIntegrable_inv (fun t ht => by
        rw [uIcc_of_le hx] at ht
        exact (zero_lt_one.trans_le ht.1).ne') continuousOn_id
    simpa [div_eq_mul_inv] using h.const_mul ρ
  · have hx0 : 0 < x := zero_lt_one.trans_le hx
    have : ∫ t in (1 : ℝ)..x, ρ / t = ρ * log x := by
      simp only [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hx0, div_one]
    rw [this, one_mul, rpow_def_of_pos hx0, mul_comm]

/-- Exercises `IsRegularlyVarying.exists_representation`, the direction that needs measurability,
on `x ^ ρ`: the index in the representation is the index of `f`. -/
theorem test_exists_representation_rpow (ρ : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∃ c r : ℝ → ℝ, Tendsto r atTop (𝓝 ρ) ∧
      ∀ x ≥ a, x ^ ρ = c x * exp (∫ t in a..x, r t / t) := by
  obtain ⟨a, ha, c, r, -, -, -, hr, -, -, hrep⟩ := (IsRegularlyVarying.rpow_id ρ).exists_representation
    (Measurable.measurableNearTop (by fun_prop))
  exact ⟨a, ha, c, r, hr, hrep⟩

/-! ### Composition, and the limit is a power -/

/-- `IsRegularlyVarying.comp`: `(x ^ 2) ^ 3` has index `3 * 2`. -/
theorem test_comp_rpow :
    IsRegularlyVarying (fun x : ℝ => (x ^ (2 : ℝ)) ^ (3 : ℝ)) (3 * 2) :=
  (IsRegularlyVarying.rpow_id 3).comp (Measurable.measurableNearTop (by fun_prop))
    (IsRegularlyVarying.rpow_id 2) (tendsto_rpow_atTop two_pos)

/-- `exists_isRegularlyVarying_of_tendsto` on `f x = x²`, with `k c = c²`: the index it finds has
`c ^ ρ = c²`, so `ρ = 2`. -/
theorem test_exists_isRegularlyVarying_of_tendsto_sq :
    ∃ ρ : ℝ, IsRegularlyVarying (fun x : ℝ => x ^ (2 : ℝ)) ρ ∧ (2 : ℝ) ^ ρ = 2 ^ (2 : ℝ) := by
  obtain ⟨ρ, hρ, hk⟩ := exists_isRegularlyVarying_of_tendsto (k := fun c => c ^ (2 : ℝ))
    (IsRegularlyVarying.rpow_id 2).1 (Measurable.measurableNearTop (by fun_prop))
    (fun c hc => rpow_pos_of_pos hc _) (IsRegularlyVarying.rpow_id 2).2
  exact ⟨ρ, hρ, (hk 2 two_pos).symm⟩

end Test.KnownAnswers.RegularVariation
