/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT
import ExtremeValueTheory.StableLaws.LevyContinuity

/-!
# The converse of the generalized central limit theorem (symmetric case)

-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

/-- `Z(x) = E[min (x², X²)]`. -/
noncomputable def minSqMoment (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, min (x ^ 2) (y ^ 2) ∂μ

/-- The truncated second moment `U(x) = E[X² 1{|X| ≤ x}]`. -/
noncomputable def truncSecondMoment (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y in {y : ℝ | |y| ≤ x}, y ^ 2 ∂μ

namespace GCLTConverse

section Tauberian

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem integrable_min_sq (x : ℝ) : Integrable (fun y : ℝ => min (x ^ 2) (y ^ 2)) μ :=
  (integrable_const (x ^ 2)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
      exact min_le_left _ _)

theorem measurableSet_abs_le (x : ℝ) : MeasurableSet {y : ℝ | |y| ≤ x} :=
  measurableSet_le continuous_abs.measurable measurable_const

theorem sq_le_sq_of_abs_le {x y : ℝ} (h : |y| ≤ x) : y ^ 2 ≤ x ^ 2 := by
  have := pow_le_pow_left₀ (abs_nonneg y) h 2
  rwa [sq_abs] at this

theorem sq_le_sq_of_le_abs {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ |y|) : x ^ 2 ≤ y ^ 2 := by
  have := pow_le_pow_left₀ hx h 2
  rwa [sq_abs] at this

theorem min_sq_eq {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    min (x ^ 2) (y ^ 2) = {y : ℝ | |y| ≤ x}.indicator (fun y => y ^ 2) y +
      {y : ℝ | x < |y|}.indicator (fun _ => x ^ 2) y := by
  rcases le_or_gt |y| x with h | h
  · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | |y| ≤ x} from h),
      Set.indicator_of_notMem (show y ∉ {y : ℝ | x < |y|} from not_lt.2 h), add_zero,
      min_eq_right (sq_le_sq_of_abs_le h)]
  · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | |y| ≤ x} from not_le.2 h),
      Set.indicator_of_mem (show y ∈ {y : ℝ | x < |y|} from h), zero_add,
      min_eq_left (sq_le_sq_of_le_abs hx h.le)]

/-- `Z(x) = U(x) + x² P(|X| > x)`. -/
theorem minSqMoment_eq {x : ℝ} (hx : 0 ≤ x) :
    minSqMoment μ x = truncSecondMoment μ x + x ^ 2 * absTail μ x := by
  have hU : Integrable ({y : ℝ | |y| ≤ x}.indicator (fun y => y ^ 2)) μ := by
    refine (integrable_const (x ^ 2)).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((continuous_pow 2).aestronglyMeasurable).indicator (measurableSet_abs_le x)
    · by_cases h : |y| ≤ x
      · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | |y| ≤ x} from h), Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq_of_abs_le h
      · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | |y| ≤ x} from h), norm_zero]
        positivity
  rw [minSqMoment, funext (min_sq_eq hx), integral_add hU
    ((integrable_const _).indicator (GCLT.measurableSet_abs_gt x)),
    integral_indicator (measurableSet_abs_le x), integral_indicator_const _
    (GCLT.measurableSet_abs_gt x), truncSecondMoment, absTail, smul_eq_mul, mul_comm]

omit [IsFiniteMeasure μ] in
theorem minSqMoment_nonneg (x : ℝ) : 0 ≤ minSqMoment μ x :=
  integral_nonneg fun _ => le_min (sq_nonneg _) (sq_nonneg _)

theorem minSqMoment_mono {x x' : ℝ} (hx : 0 ≤ x) (h : x ≤ x') :
    minSqMoment μ x ≤ minSqMoment μ x' :=
  integral_mono (integrable_min_sq x) (integrable_min_sq x') fun _ =>
    min_le_min_right _ (pow_le_pow_left₀ hx h 2)

theorem min_sq_sub_le {x l : ℝ} (hx : 0 ≤ x) (hl : 1 ≤ l) (y : ℝ) :
    min ((l * x) ^ 2) (y ^ 2) - min (x ^ 2) (y ^ 2) ≤
      {y : ℝ | x < |y|}.indicator (fun _ => (l ^ 2 - 1) * x ^ 2) y := by
  have hlx : x ≤ l * x := le_mul_of_one_le_left hx hl
  rcases le_or_gt |y| x with h | h
  · rw [min_eq_right (sq_le_sq_of_abs_le h), min_eq_right (sq_le_sq_of_abs_le (h.trans hlx)),
      sub_self, Set.indicator_of_notMem (show y ∉ {y : ℝ | x < |y|} from not_lt.2 h)]
  · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | x < |y|} from h),
      min_eq_left (sq_le_sq_of_le_abs hx h.le)]
    have : min ((l * x) ^ 2) (y ^ 2) ≤ (l * x) ^ 2 := min_le_left _ _
    nlinarith

theorem le_min_sq_sub {x l : ℝ} (hx : 0 ≤ x) (hl : 1 ≤ l) (y : ℝ) :
    {y : ℝ | l * x < |y|}.indicator (fun _ => (l ^ 2 - 1) * x ^ 2) y ≤
      min ((l * x) ^ 2) (y ^ 2) - min (x ^ 2) (y ^ 2) := by
  have hlx : x ≤ l * x := le_mul_of_one_le_left hx hl
  by_cases h : l * x < |y|
  · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | l * x < |y|} from h),
      min_eq_left (sq_le_sq_of_le_abs hx (hlx.trans h.le)),
      min_eq_left (sq_le_sq_of_le_abs (hx.trans hlx) h.le)]
    ring_nf; rfl
  · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | l * x < |y|} from h)]
    exact sub_nonneg.2 (min_le_min_right _ (pow_le_pow_left₀ hx hlx 2))

theorem minSqMoment_sub_le {x l : ℝ} (hx : 0 ≤ x) (hl : 1 ≤ l) :
    minSqMoment μ (l * x) - minSqMoment μ x ≤ (l ^ 2 - 1) * x ^ 2 * absTail μ x := by
  rw [minSqMoment, minSqMoment, ← integral_sub (integrable_min_sq _) (integrable_min_sq _)]
  calc _ ≤ ∫ y, {y : ℝ | x < |y|}.indicator (fun _ => (l ^ 2 - 1) * x ^ 2) y ∂μ :=
        integral_mono ((integrable_min_sq _).sub (integrable_min_sq _))
          ((integrable_const _).indicator (GCLT.measurableSet_abs_gt x)) (min_sq_sub_le hx hl)
    _ = _ := by
        rw [integral_indicator_const _ (GCLT.measurableSet_abs_gt x), absTail, smul_eq_mul,
          mul_comm]

theorem le_minSqMoment_sub {x l : ℝ} (hx : 0 ≤ x) (hl : 1 ≤ l) :
    (l ^ 2 - 1) * x ^ 2 * absTail μ (l * x) ≤ minSqMoment μ (l * x) - minSqMoment μ x := by
  rw [minSqMoment, minSqMoment, ← integral_sub (integrable_min_sq _) (integrable_min_sq _)]
  calc _ = ∫ y, {y : ℝ | l * x < |y|}.indicator (fun _ => (l ^ 2 - 1) * x ^ 2) y ∂μ := by
        rw [integral_indicator_const _ (GCLT.measurableSet_abs_gt _), absTail, smul_eq_mul,
          mul_comm]
    _ ≤ _ :=
        integral_mono ((integrable_const _).indicator (GCLT.measurableSet_abs_gt _))
          ((integrable_min_sq _).sub (integrable_min_sq _)) (le_min_sq_sub hx hl)

/-- The difference quotient `(l ^ β - 1) / (l - 1) → β` as `l → 1⁺`. -/
theorem tendsto_rpow_sub_one_div (β : ℝ) :
    Tendsto (fun l : ℝ => (l ^ β - 1) / (l - 1)) (𝓝[>] 1) (𝓝 β) := by
  have h := hasDerivAt_iff_tendsto_slope.1
    (Real.hasDerivAt_rpow_const (x := 1) (p := β) (Or.inl one_ne_zero))
  simp only [Real.one_rpow, mul_one] at h
  refine (h.mono_left (nhdsWithin_mono _ fun l (hl : 1 < l) => ne_of_gt hl)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with l _
  rw [slope_def_field, Real.one_rpow]

/-- `(l ^ β - 1) / (l ^ 2 - 1) → β / 2` as `l → 1⁺`. -/
theorem tendsto_rpow_sub_one_div_sq (β : ℝ) :
    Tendsto (fun l : ℝ => (l ^ β - 1) / (l ^ 2 - 1)) (𝓝[>] 1) (𝓝 (β / 2)) := by
  have h2 := tendsto_rpow_sub_one_div 2
  refine ((tendsto_rpow_sub_one_div β).div h2 two_ne_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with l (hl : 1 < l)
  have : l - 1 ≠ 0 := by linarith
  simp only [Pi.div_apply]
  rw [Real.rpow_two]
  field_simp

/-- **Elementary Tauberian step.** If `Z(x) = E[min (x², X²)]` is regularly varying with index
`ρ`, then `x² P(|X| > x) / Z(x) → ρ / 2`. -/
theorem tendsto_sq_mul_absTail_div_minSqMoment {ρ : ℝ}
    (hZ : IsRegularlyVarying (minSqMoment μ) ρ) :
    Tendsto (fun x => x ^ 2 * absTail μ x / minSqMoment μ x) atTop (𝓝 (ρ / 2)) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨l, hlb, hl1⟩ := (((tendsto_rpow_sub_one_div_sq ρ).eventually
      (lt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have hl1 : 1 < l := hl1
    have hlim : Tendsto (fun x => (minSqMoment μ (l * x) / minSqMoment μ x - 1) / (l ^ 2 - 1))
        atTop (𝓝 ((l ^ ρ - 1) / (l ^ 2 - 1))) :=
      ((hZ.2 l (by linarith)).sub_const 1).div_const _
    filter_upwards [hlim.eventually (lt_mem_nhds hlb), hZ.1, eventually_ge_atTop 0]
      with x hx hZx hx0
    refine hx.trans_le ?_
    have hl2 : 0 < l ^ 2 - 1 := by nlinarith
    rw [div_sub_one hZx.ne', div_div, div_le_div_iff₀ (mul_pos hZx hl2) hZx]
    have := minSqMoment_sub_le (μ := μ) hx0 hl1.le
    nlinarith
  · have hg : Tendsto (fun l : ℝ => 1 - (l ^ (2 - ρ) - 1) / (l ^ 2 - 1)) (𝓝[>] 1)
        (𝓝 (ρ / 2)) := by
      have := (tendsto_rpow_sub_one_div_sq (2 - ρ)).const_sub 1
      convert this using 2; ring
    obtain ⟨l, hlb, hl1⟩ := ((hg.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have hl1 : 1 < l := hl1
    have hl0 : 0 < l := by linarith
    have hlim : Tendsto (fun x => l ^ 2 * (1 - minSqMoment μ (l⁻¹ * x) / minSqMoment μ x) /
        (l ^ 2 - 1)) atTop (𝓝 (l ^ 2 * (1 - l⁻¹ ^ ρ) / (l ^ 2 - 1))) :=
      (((hZ.2 l⁻¹ (inv_pos.2 hl0)).const_sub 1).const_mul _).div_const _
    have he : l ^ 2 * (1 - l⁻¹ ^ ρ) / (l ^ 2 - 1) = 1 - (l ^ (2 - ρ) - 1) / (l ^ 2 - 1) := by
      have hl2 : l ^ 2 - 1 ≠ 0 := by nlinarith
      rw [Real.inv_rpow hl0.le, ← Real.rpow_neg hl0.le, Real.rpow_sub hl0, Real.rpow_two,
        Real.rpow_neg hl0.le]
      field_simp
      ring
    rw [he] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hlb), hZ.1, eventually_ge_atTop 0]
      with x hx hZx hx0
    refine lt_of_le_of_lt ?_ hx
    have hl2 : 0 < l ^ 2 - 1 := by nlinarith
    have h := le_minSqMoment_sub (μ := μ) (mul_nonneg (inv_nonneg.2 hl0.le) hx0) hl1.le
    rw [← mul_assoc, mul_inv_cancel₀ hl0.ne', one_mul] at h
    rw [one_sub_div hZx.ne', mul_div_assoc', div_div, div_le_div_iff₀ hZx (mul_pos hZx hl2)]
    have h2 : (l ^ 2 - 1) * x ^ 2 * absTail μ x ≤
        l ^ 2 * (minSqMoment μ x - minSqMoment μ (l⁻¹ * x)) := by
      have := mul_le_mul_of_nonneg_left h (pow_pos hl0 2).le
      calc _ = l ^ 2 * ((l ^ 2 - 1) * (l⁻¹ * x) ^ 2 * absTail μ x) := by
            field_simp
        _ ≤ _ := this
    nlinarith [mul_le_mul_of_nonneg_right h2 hZx.le]

/-- If `Z(x) = E[min (x², X²)]` is regularly varying with index `ρ > 0`, then the two-sided tail
`P(|X| > x)` is regularly varying with index `ρ - 2`. -/
theorem isRegularlyVarying_absTail_of_minSqMoment {ρ : ℝ} (hρ : 0 < ρ)
    (hZ : IsRegularlyVarying (minSqMoment μ) ρ) : IsRegularlyVarying (absTail μ) (ρ - 2) := by
  have hg : IsRegularlyVarying (fun x => minSqMoment μ x * x ^ (-2 : ℝ)) (ρ + -2) :=
    hZ.mul (IsRegularlyVarying.rpow_id (-2))
  rw [← sub_eq_add_neg] at hg
  refine hg.of_tendsto_div ((tendsto_sq_mul_absTail_div_minSqMoment hZ).congr' ?_)
    (by linarith)
  filter_upwards [eventually_gt_atTop 0, hZ.1] with x hx hZx
  rw [Real.rpow_neg hx.le, Real.rpow_two]
  field_simp

/-- If `Z(x) = E[min (x², X²)]` is regularly varying with index `ρ < 2`, then
`U(x) / Z(x) → 1 - ρ / 2`. -/
theorem tendsto_truncSecondMoment_div_minSqMoment {ρ : ℝ}
    (hZ : IsRegularlyVarying (minSqMoment μ) ρ) :
    Tendsto (fun x => truncSecondMoment μ x / minSqMoment μ x) atTop (𝓝 (1 - ρ / 2)) := by
  refine ((tendsto_sq_mul_absTail_div_minSqMoment hZ).const_sub 1).congr' ?_
  filter_upwards [eventually_ge_atTop 0, hZ.1] with x hx hZx
  rw [minSqMoment_eq hx] at hZx ⊢
  field_simp
  ring

/-- If `Z(x) = E[min (x², X²)]` is regularly varying with index `ρ < 2`, then so is the
truncated second moment `U(x) = E[X² 1{|X| ≤ x}]`. -/
theorem isRegularlyVarying_truncSecondMoment_of_minSqMoment {ρ : ℝ} (hρ : ρ < 2)
    (hZ : IsRegularlyVarying (minSqMoment μ) ρ) :
    IsRegularlyVarying (truncSecondMoment μ) ρ :=
  hZ.of_tendsto_div (tendsto_truncSecondMoment_div_minSqMoment hZ) (by linarith)

end Tauberian

section SeqToFun

variable {T L : ℝ → ℝ} {a : ℕ → ℝ}

/-- If `T` is positive and nonincreasing and `n T(aₙ) → L > 0`, then `aₙ → ∞`. -/
theorem tendsto_atTop_of_tendsto_mul_comp (hT : AntitoneOn T (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < T x) (ha : ∀ n, 0 < a n)
    (hL : Tendsto (fun n : ℕ => (n : ℝ) * T (a n)) atTop (𝓝 (L 1))) :
    Tendsto a atTop atTop := by
  have h0 : Tendsto (fun n : ℕ => T (a n)) atTop (𝓝 0) := by
    refine (hL.div_atTop tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  refine tendsto_atTop.2 fun A => ?_
  set A' := max A 1
  have hA' : 0 < A' := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [(tendsto_order.1 h0).2 _ (hpos A' hA')] with n hn
  by_contra hlt
  have : a n ≤ A' := (lt_of_not_ge hlt).le.trans (le_max_left _ _)
  exact absurd (hT (ha n) hA' this) (not_le.2 hn)

/-- Bracketing: if `aₙ → ∞` and `a_K ≤ x`, there is `N ≥ K` with `a_N ≤ x < a_{N+1}`. -/
theorem exists_bracket (hatop : Tendsto a atTop atTop) {K : ℕ} {x : ℝ} (hx : a K ≤ x) :
    ∃ N, K ≤ N ∧ a N ≤ x ∧ x < a (N + 1) := by
  classical
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_atTop.1 hatop) (x + 1))
  have hKM : K ≤ M := by
    by_contra h
    have := hM K (not_le.1 h).le
    linarith
  refine ⟨Nat.findGreatest (fun n => a n ≤ x) M, Nat.le_findGreatest hKM hx,
    Nat.findGreatest_spec (P := fun n => a n ≤ x) hKM hx, ?_⟩
  by_cases h : Nat.findGreatest (fun n => a n ≤ x) M + 1 ≤ M
  · exact not_le.1 (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h)
  · have := hM _ (not_le.1 h).le
    linarith

/-- **From sequences to functions.** If `T > 0` is nonincreasing and `n T(aₙ x) → L(x) > 0`
for every `x > 0`, then `T(l x) / T(x) → L(l) / L(1)` for every `l > 0`
([Feller, Vol. II, §VIII.8, Lemma 3], [BGT, Theorem 1.9.2]). -/
theorem tendsto_div_of_tendsto_mul_comp (hT : AntitoneOn T (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < T x) (ha : ∀ n, 0 < a n)
    (hL : ∀ x, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * T (a n * x)) atTop (𝓝 (L x)))
    (hL0 : ∀ x, 0 < x → 0 < L x) {l : ℝ} (hl : 0 < l) :
    Tendsto (fun x => T (l * x) / T x) atTop (𝓝 (L l / L 1)) := by
  have hL1 : Tendsto (fun n : ℕ => (n : ℝ) * T (a n)) atTop (𝓝 (L 1)) := by
    simpa using hL 1 one_pos
  have hatop := tendsto_atTop_of_tendsto_mul_comp hT hpos ha hL1
  have hsucc : ∀ x, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * T (a (n + 1) * x)) atTop
      (𝓝 (L x)) := by
    intro x hx
    have h1 := (hL x hx).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
      have := tendsto_natCast_div_add_atTop (1 : ℝ)
      refine this.congr fun n => ?_
      push_cast; ring
    refine (by simpa using h2.mul h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ) *
      (((n + 1 : ℕ) : ℝ) * T (a (n + 1) * x))) atTop (𝓝 (L x))).congr' ?_
    filter_upwards with n
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hup : Tendsto (fun n : ℕ => T (l * a n) / T (a (n + 1))) atTop (𝓝 (L l / L 1)) := by
    refine ((hL l hl).div (by simpa using hsucc 1 one_pos) (hL0 1 one_pos).ne').congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    rw [mul_comm (a n) l]
    field_simp
  have hlo : Tendsto (fun n : ℕ => T (l * a (n + 1)) / T (a n)) atTop (𝓝 (L l / L 1)) := by
    refine ((hsucc l hl).div hL1 (hL0 1 one_pos).ne').congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    rw [mul_comm (a (n + 1)) l]
    field_simp
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 hlo).1 b hb)
    filter_upwards [eventually_ge_atTop (a K)] with x hx
    obtain ⟨N, hKN, h1, h2⟩ := exists_bracket hatop hx
    have hx0 : 0 < x := (ha K).trans_le hx
    refine (hK N hKN).trans_le ?_
    exact div_le_div₀ (hpos _ (mul_pos hl hx0)).le
      (hT (mul_pos hl hx0) (mul_pos hl (ha _)) (mul_le_mul_of_nonneg_left h2.le hl.le))
      (hpos _ hx0) (hT (ha N) hx0 h1)
  · obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 hup).2 b hb)
    filter_upwards [eventually_ge_atTop (a K)] with x hx
    obtain ⟨N, hKN, h1, h2⟩ := exists_bracket hatop hx
    have hx0 : 0 < x := (ha K).trans_le hx
    refine lt_of_le_of_lt ?_ (hK N hKN)
    exact div_le_div₀ (hpos _ (mul_pos hl (ha _))).le
      (hT (mul_pos hl (ha N)) (mul_pos hl hx0) (mul_le_mul_of_nonneg_left h1 hl.le))
      (hpos _ (ha _)) (hT hx0 (ha _) h2.le)

/-- If `T > 0` is nonincreasing and `n T(aₙ x) → K x ^ (-α)` with `K > 0` for every `x > 0`,
then `T` is regularly varying with index `-α`. -/
theorem isRegularlyVarying_of_tendsto_mul_comp (hT : AntitoneOn T (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < T x) (ha : ∀ n, 0 < a n) {K α : ℝ} (hK : 0 < K)
    (hL : ∀ x, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * T (a n * x)) atTop
      (𝓝 (K * x ^ (-α)))) :
    IsRegularlyVarying T (-α) := by
  refine ⟨(eventually_gt_atTop 0).mono hpos, fun l hl => ?_⟩
  have := tendsto_div_of_tendsto_mul_comp (L := fun x => K * x ^ (-α)) hT hpos ha hL
    (fun x hx => mul_pos hK (Real.rpow_pos_of_pos hx _)) hl
  simpa [hK.ne'] using this

end SeqToFun

section CosInequalities

/-- `f(s) = ∫ cos (s x) dμ(x)`, the characteristic function of a symmetric law. -/
noncomputable def cosTransform (μ : Measure ℝ) (s : ℝ) : ℝ := ∫ x, cos (s * x) ∂μ

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem integrable_cos (s : ℝ) : Integrable (fun x : ℝ => cos (s * x)) μ :=
  (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun x => by simpa using abs_cos_le_one (s * x))

theorem integrable_cos_sq (s : ℝ) : Integrable (fun x : ℝ => cos (s * x) ^ 2) μ :=
  (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_cos_le_one (s * x), sq_abs (cos (s * x)), abs_nonneg (cos (s * x))])

theorem cosTransform_zero : cosTransform μ 0 = 1 := by simp [cosTransform]

theorem cosTransform_le_one (s : ℝ) : cosTransform μ s ≤ 1 := by
  calc cosTransform μ s ≤ ∫ _x, (1 : ℝ) ∂μ :=
        integral_mono (integrable_cos s) (integrable_const _) fun x => cos_le_one _
    _ = 1 := by simp

theorem neg_one_le_cosTransform (s : ℝ) : -1 ≤ cosTransform μ s := by
  calc (-1 : ℝ) = ∫ _x, (-1 : ℝ) ∂μ := by simp
    _ ≤ cosTransform μ s :=
        integral_mono (integrable_const _) (integrable_cos s) fun x => neg_one_le_cos _

omit [IsProbabilityMeasure μ] in
theorem cosTransform_neg (s : ℝ) : cosTransform μ (-s) = cosTransform μ s := by
  simp [cosTransform, neg_mul, cos_neg]

/-- `f(2s) ≥ 2 f(s)² - 1` (Jensen's inequality `(∫ cos)² ≤ ∫ cos²`). -/
theorem two_mul_sq_sub_one_le_cosTransform (s : ℝ) :
    2 * cosTransform μ s ^ 2 - 1 ≤ cosTransform μ (2 * s) := by
  set F := cosTransform μ s with hF
  have h0 : 0 ≤ ∫ x, (cos (s * x) - F) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have e1 : ∫ x, (cos (s * x) - F) ^ 2 ∂μ = (∫ x, cos (s * x) ^ 2 ∂μ) - F ^ 2 := by
    have e : ∀ x, (cos (s * x) - F) ^ 2 = cos (s * x) ^ 2 - 2 * F * cos (s * x) + F ^ 2 :=
      fun x => by ring
    simp_rw [e]
    rw [integral_add (f := fun x => cos (s * x) ^ 2 - 2 * F * cos (s * x)) (g := fun _ => F ^ 2)
      ((integrable_cos_sq s).sub ((integrable_cos s).const_mul _)) (integrable_const _),
      integral_sub (f := fun x => cos (s * x) ^ 2) (g := fun x => 2 * F * cos (s * x))
      (integrable_cos_sq s) ((integrable_cos s).const_mul _), integral_const_mul, integral_const]
    have : ∫ x, cos (s * x) ∂μ = F := rfl
    simp only [probReal_univ, one_smul, this]
    ring
  have e2 : cosTransform μ (2 * s) = 2 * (∫ x, cos (s * x) ^ 2 ∂μ) - 1 := by
    have e : ∀ x, cos (2 * s * x) = 2 * cos (s * x) ^ 2 - 1 := fun x => by
      rw [mul_assoc, cos_two_mul]
    simp_rw [cosTransform, e]
    rw [integral_sub (f := fun x => 2 * cos (s * x) ^ 2) (g := fun _ => (1 : ℝ))
      ((integrable_cos_sq s).const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp
  rw [e2]
  linarith

theorem abs_sin_nat_mul_le (k : ℕ) (φ : ℝ) : |sin (k * φ)| ≤ k * |sin φ| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add]
    calc |sin (k * φ) * cos φ + cos (k * φ) * sin φ|
        ≤ |sin (k * φ)| * |cos φ| + |cos (k * φ)| * |sin φ| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |sin (k * φ)| * 1 + 1 * |sin φ| := by
          gcongr
          · exact abs_cos_le_one _
          · exact abs_cos_le_one _
      _ ≤ (k + 1) * |sin φ| := by linarith

theorem one_sub_cos_eq (θ : ℝ) : 1 - cos θ = 2 * sin (θ / 2) ^ 2 := by
  have h := cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  have h2 := sin_sq_add_cos_sq (θ / 2)
  linarith

/-- `1 - cos (k θ) ≤ k² (1 - cos θ)`. -/
theorem one_sub_cos_nat_mul_le (k : ℕ) (θ : ℝ) :
    1 - cos (k * θ) ≤ (k : ℝ) ^ 2 * (1 - cos θ) := by
  rw [one_sub_cos_eq, one_sub_cos_eq, mul_div_assoc]
  have h := abs_sin_nat_mul_le k (θ / 2)
  have h2 : sin (k * (θ / 2)) ^ 2 ≤ (k * |sin (θ / 2)|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [mul_pow, sq_abs] at h2
  linarith

/-- `1 - f(k s) ≤ k² (1 - f(s))`. -/
theorem one_sub_cosTransform_nat_mul_le (k : ℕ) (s : ℝ) :
    1 - cosTransform μ (k * s) ≤ (k : ℝ) ^ 2 * (1 - cosTransform μ s) := by
  have e : ∀ r, 1 - cosTransform μ r = ∫ x, (1 - cos (r * x)) ∂μ := fun r => by
    rw [integral_sub (integrable_const _) (integrable_cos r)]; simp [cosTransform]
  rw [e, e, ← integral_const_mul]
  refine integral_mono ((integrable_const _).sub (integrable_cos _))
    (((integrable_const _).sub (integrable_cos _)).const_mul _) fun x => ?_
  simpa [mul_assoc] using one_sub_cos_nat_mul_le k (s * x)

end CosInequalities

section Tight

/-- For a tight family of probability measures, the characteristic functions are uniformly
close to `1` near the origin. -/
theorem exists_forall_norm_charFun_sub_one_le {ν : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (ν n)] (hT : IsTightMeasureSet (range ν)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ n t, |t| ≤ δ → ‖charFun (ν n) t - 1‖ ≤ ε := by
  have h := tendsto_measure_norm_gt_of_isTightMeasureSet hT
  have hε4 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 _ hε4)
  set R := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := by linarith
  have htail : ∀ n, (ν n).real {x | R < ‖x‖} ≤ ε / 4 := by
    intro n
    have h1 := hR₀ R (le_max_left _ _)
    have h2 : ν n {x | R < ‖x‖} ≤ ⨆ μ ∈ range ν, μ {x | R < ‖x‖} :=
      le_iSup₂ (f := fun μ (_ : μ ∈ range ν) => μ {x | R < ‖x‖}) (ν n) (mem_range_self n)
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) (h2.trans h1.le)
  refine ⟨ε / (2 * R), by positivity, fun n t ht => ?_⟩
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) (ν n) := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hS : MeasurableSet {x : ℝ | R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  have hbound : ∀ x : ℝ, ‖Complex.exp (t * x * Complex.I) - 1‖ ≤
      |t| * R + {x : ℝ | R < ‖x‖}.indicator (fun _ => (2 : ℝ)) x := by
    intro x
    by_cases hx : R < ‖x‖
    · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | R < ‖x‖} from hx)]
      have : ‖Complex.exp (t * x * Complex.I) - 1‖ ≤ 2 := by
        calc _ ≤ ‖Complex.exp (t * x * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by
            rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
      have : 0 ≤ |t| * R := by positivity
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | R < ‖x‖} from hx), add_zero]
      have h1 : ‖Complex.exp (t * x * Complex.I) - 1‖ ≤ ‖t * x‖ := by
        have := norm_exp_I_mul_ofReal_sub_one_le (x := t * x)
        rwa [mul_comm Complex.I, Complex.ofReal_mul] at this
      rw [Real.norm_eq_abs, abs_mul] at h1
      rw [Real.norm_eq_abs] at hx
      exact h1.trans (mul_le_mul_of_nonneg_left (not_lt.1 hx) (abs_nonneg _))
  have e : charFun (ν n) t - 1 = ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂(ν n) := by
    rw [integral_sub hint (integrable_const _), charFun_apply_real]; simp
  rw [e]
  calc _ ≤ ∫ x, ‖Complex.exp (t * x * Complex.I) - 1‖ ∂(ν n) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|t| * R + {x : ℝ | R < ‖x‖}.indicator (fun _ => (2 : ℝ)) x) ∂(ν n) :=
        integral_mono (hint.sub (integrable_const _)).norm
          ((integrable_const _).add ((integrable_const _).indicator hS)) hbound
    _ = |t| * R + 2 * (ν n).real {x | R < ‖x‖} := by
        rw [integral_add (integrable_const _) ((integrable_const _).indicator hS),
          integral_indicator_const _ hS]
        simp [mul_comm]
    _ ≤ ε / (2 * R) * R + 2 * (ε / 4) := by
        gcongr
        exact htail n
    _ = ε := by field_simp; ring

end Tight

end GCLTConverse

end ExtremeValueTheory
