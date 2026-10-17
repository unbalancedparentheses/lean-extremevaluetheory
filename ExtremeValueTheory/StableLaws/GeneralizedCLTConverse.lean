/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT
import ExtremeValueTheory.StableLaws.LevyContinuity

/-!
# The converse of the generalized central limit theorem (symmetric case)

Let `X₁, X₂, …` be i.i.d. with a *symmetric* law `μ`, let `aₙ > 0`, and suppose that the laws
of `Sₙ / aₙ = (X₁ + ⋯ + Xₙ) / aₙ` converge weakly to a law `ν ≠ δ₀`. We prove the necessity half
of Feller's criterion for the domain of attraction of a stable law
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2]): the truncated second moment
`U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α` for some `0 < α ≤ 2`, and for
`α < 2` the two-sided tail `P(|X| > x)` is regularly varying with index `-α`. This is the converse
of `tendsto_map_convPow_of_isRegularlyVarying` (in
`ExtremeValueTheory.StableLaws.DomainOfAttraction`).

## Main definitions

* `minSqMoment μ x = E[min (x², X²)]` and `truncSecondMoment μ x = E[X² 1{|X| ≤ x}]`.
* `GCLTConverse.nh μ a n t = n (1 - f(t / aₙ))`, `f(s) = ∫ cos (s x) dμ`.
* `GCLTConverse.lamMeasure μ a n`, the finite measure `y² / (1 + y²) · law(X / aₙ)(dy)`, and
  `GCLTConverse.lamNorm` its normalization (a version of Feller's canonical measures).

## Main results

* `GCLTConverse.exists_isRegularlyVarying_of_tendsto`: **converse GCLT, index derived.** If
  `Sₙ / aₙ → ν ≠ δ₀` weakly, there is `0 < α ≤ 2` with `U ∈ RV(2 - α)` and, if `α < 2`,
  `P(|X| > ·) ∈ RV(-α)`.
* `GCLTConverse.isRegularlyVarying_of_tendsto_isSymmStable`: **converse GCLT, index given.**
  If `Sₙ / aₙ → SαS(c)` with `0 < α < 2`, `c > 0`, then `P(|X| > ·) ∈ RV(-α)`,
  `U ∈ RV(2 - α)` and `n P(|X| > aₙ) → K > 0`.
* `GCLTConverse.tendsto_sq_mul_absTail_div_minSqMoment`: the elementary Tauberian step: if
  `Z(x) = E[min (x², X²)]` is `RV(ρ)` then `x² P(|X| > x) / Z(x) → ρ / 2`, hence the tail is
  `RV(ρ - 2)` (`ρ > 0`) and `U ∈ RV(ρ)` (`ρ < 2`).
* `GCLTConverse.tendsto_div_of_tendsto_mul_comp`: from sequences to functions: for monotone
  `T`, `n T(aₙ x) → L(x) > 0` implies `T(l x) / T(x) → L(l) / L(1)`
  ([Feller, §VIII.8, Lemma 3], [BGT, Theorem 1.9.2]).
* `GCLTConverse.exists_rpow_of_tendsto_div`: the limit of `T(l x) / T(x)` is a power of `l`.

## Proof outline

1. *Tightness* (`exists_forall_norm_charFun_sub_one_le`, `exists_nh_le`): the characteristic
   functions `f(t / aₙ)ⁿ` of `Sₙ / aₙ` are uniformly close to `1` for `|t| ≤ δ`; with
   `f(2s) ≥ 2 f(s)² - 1` and `1 - f(k s) ≤ k² (1 - f(s))` this gives the quadratic bound
   `hₙ(t) = n (1 - f(t / aₙ)) ≤ log 2 (|t| / δ + 1)²`.
2. *Logarithms* (`tendsto_nh`): `ψ = Re φ_ν > 0` and `hₙ(t) → h(t) = -log ψ(t)`.
3. *Canonical measures* (`charFun_kMeasure`, `charFun_lamMeasure`): with
   `1 / (1 + y²) = ∫₀^∞ e^{-s} cos (s y) ds`, the measures
   `Λₙ(dy) = n y² / (1 + y²) P(X / aₙ ∈ dy)` have characteristic functions
   `λ_{hₙ}(t) = ∫₀^∞ e^{-s} ((hₙ(t + s) + hₙ(t - s)) / 2 - hₙ(t)) ds`, which converge to
   `λ_h(t)` by dominated convergence (`tendsto_lap`).
4. *Lévy* (`exists_charFun_eq_lap`, `tendsto_mul_sqRatio`): `Λₙ / Λₙ(ℝ)` converges weakly to a
   probability `P`, so testing against the bounded continuous `(1 + y²) / max (y², x²)` gives
   `n T(aₙ x) → L(x) > 0` with `T(x) = E[min (1, X² / x²)] = Z(x) / x²`.
5. *Regular variation*: `T` is monotone, so `T(l x) / T(x) → L(l) / L(1) = l ^ (-α)`; then the
   elementary Tauberian step transfers this to `U` and to the tail. With `ν = SαS(c)` the
   scaling `aₙ ↦ r aₙ` identifies `α` (`isRegularlyVarying_of_tendsto_isSymmStable`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

/-- `Z(x) = E[min (x², X²)]`. -/
noncomputable def minSqMoment (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, min (x ^ 2) (y ^ 2) ∂μ

/-- The truncated second moment `U(x) = E[X² 1{|X| ≤ x}]`. -/
noncomputable def truncSecondMoment (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y in {y : ℝ | |y| ≤ x}, y ^ 2 ∂μ

namespace GCLTConverse

open Subexp

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

section FromWeakConvergence

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

/-- `hₙ(t) = n (1 - f(t / aₙ))`, where `f` is the (real) characteristic function of `μ`. -/
noncomputable def nh (μ : Measure ℝ) (a : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  n * (1 - cosTransform μ ((a n)⁻¹ * t))

theorem nh_nonneg (n : ℕ) (t : ℝ) : 0 ≤ nh μ a n t :=
  mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.2 (cosTransform_le_one _))

theorem nh_zero (n : ℕ) : nh μ a n 0 = 0 := by simp [nh, cosTransform_zero]

omit [IsProbabilityMeasure μ] in
theorem nh_neg (n : ℕ) (t : ℝ) : nh μ a n (-t) = nh μ a n t := by
  simp [nh, mul_neg, cosTransform_neg]

theorem charFun_map_convPow (hsymm : μ.map (fun x => -x) = μ) (n : ℕ) (t : ℝ) :
    charFun ((convPow μ n).map ((a n)⁻¹ * ·)) t =
      ((cosTransform μ ((a n)⁻¹ * t) ^ n : ℝ) : ℂ) := by
  rw [charFun_map_mul, charFun_convPow, GCLT.charFun_eq_integral_cos hsymm, Complex.ofReal_pow]
  rfl

/-- **Step 1 of the converse.** If `Sₙ / aₙ` converges weakly, then `hₙ(t) ≤ log 2 (|t| / δ + 1)²`
for some `δ > 0` and all `n ≥ 3`, `t ∈ ℝ`. -/
theorem exists_nh_le (hsymm : μ.map (fun x => -x) = μ) {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ δ > 0, ∀ n : ℕ, 3 ≤ n → ∀ t, nh μ a n t ≤ Real.log 2 * (|t| / δ + 1) ^ 2 := by
  have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hconv
  have hT := isTightMeasureSet_of_tendsto_charFun
    (μ := fun n : ℕ => (convPow μ n).map ((a n)⁻¹ * ·))
    (continuous_charFun (μ := (ν : Measure ℝ))).continuousAt hcf
  obtain ⟨δ, hδ, hδ'⟩ := exists_forall_norm_charFun_sub_one_le hT (ε := 1 / 2) (by norm_num)
  have hhalf : ∀ n t, |t| ≤ δ → 1 / 2 ≤ cosTransform μ ((a n)⁻¹ * t) ^ n := by
    intro n t ht
    have h := hδ' n t ht
    rw [charFun_map_convPow hsymm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at h
    linarith [(abs_le.1 h).1]
  have hloc : ∀ n : ℕ, 3 ≤ n → ∀ t, |t| ≤ δ → nh μ a n t ≤ Real.log 2 := by
    intro n hn t ht
    set F := cosTransform μ ((a n)⁻¹ * t)
    set F2 := cosTransform μ ((a n)⁻¹ * (t / 2))
    have h1 : 1 / 2 ≤ F ^ n := hhalf n t ht
    have h2 : 1 / 2 ≤ F2 ^ n := hhalf n (t / 2) (by rw [abs_div]; linarith [abs_nonneg t])
    have hF2 : 1 / 2 < F2 ^ 2 := by
      by_contra hc
      have h3 : (F2 ^ 2) ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (sq_nonneg _) (not_lt.1 hc) n
      have h4 : ((1 : ℝ) / 2) ^ n ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num)
        (by norm_num) hn
      have h5 : (1 / 2 : ℝ) ^ 2 ≤ (F2 ^ n) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      rw [← pow_mul, mul_comm, pow_mul] at h3
      norm_num at h4 h5
      linarith
    have hF : 0 < F := by
      have := two_mul_sq_sub_one_le_cosTransform (μ := μ) ((a n)⁻¹ * (t / 2))
      rw [show 2 * ((a n)⁻¹ * (t / 2)) = (a n)⁻¹ * t by ring] at this
      linarith
    have hlog : 1 - F ≤ -Real.log F := by linarith [Real.log_le_sub_one_of_pos hF]
    have hlogn : Real.log (1 / 2) ≤ Real.log (F ^ n) := Real.log_le_log (by norm_num) h1
    rw [Real.log_pow, one_div, Real.log_inv] at hlogn
    calc nh μ a n t = n * (1 - F) := rfl
      _ ≤ n * (-Real.log F) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
      _ ≤ Real.log 2 := by linarith
  refine ⟨δ, hδ, fun n hn t => ?_⟩
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [nh_zero]; positivity
  set k := ⌈|t| / δ⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun h => by
    rw [hk, Nat.ceil_eq_zero] at h
    have : 0 < |t| / δ := div_pos (abs_pos.2 ht0) hδ
    linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkle : |t| / δ ≤ k := Nat.le_ceil _
  have hkle' : (k : ℝ) ≤ |t| / δ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hloc' := hloc n hn (t / k) (by
    rw [abs_div, abs_of_pos hk0, div_le_iff₀ hk0]
    rw [div_le_iff₀ hδ] at hkle
    linarith)
  have hmul := one_sub_cosTransform_nat_mul_le (μ := μ) k ((a n)⁻¹ * (t / k))
  rw [show (k : ℝ) * ((a n)⁻¹ * (t / k)) = (a n)⁻¹ * t by field_simp] at hmul
  calc nh μ a n t = n * (1 - cosTransform μ ((a n)⁻¹ * t)) := rfl
    _ ≤ n * ((k : ℝ) ^ 2 * (1 - cosTransform μ ((a n)⁻¹ * (t / k)))) :=
        mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg n)
    _ = (k : ℝ) ^ 2 * nh μ a n (t / k) := by rw [nh]; ring
    _ ≤ (|t| / δ + 1) ^ 2 * Real.log 2 :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hkle' 2) hloc' (nh_nonneg _ _)
          (by positivity)
    _ = _ := mul_comm _ _

/-- **Step 2 of the converse.** If `Sₙ / aₙ → ν` weakly, then `ψ(t) = Re φ_ν(t) > 0` and
`hₙ(t) → -log ψ(t)` for every `t`. -/
theorem tendsto_nh (hsymm : μ.map (fun x => -x) = μ) {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν))
    {δ B : ℝ} (hB : ∀ n : ℕ, 3 ≤ n → ∀ t, nh μ a n t ≤ B * (|t| / δ + 1) ^ 2) (t : ℝ) :
    0 < (charFun (ν : Measure ℝ) t).re ∧
      Tendsto (fun n => nh μ a n t) atTop (𝓝 (-Real.log (charFun (ν : Measure ℝ) t).re)) := by
  have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hconv t
  set ψ := (charFun (ν : Measure ℝ) t).re
  set F : ℕ → ℝ := fun n => cosTransform μ ((a n)⁻¹ * t) with hFdef
  have hFn : Tendsto (fun n => F n ^ n) atTop (𝓝 ψ) := by
    have := (Complex.continuous_re.tendsto _).comp hcf
    refine this.congr fun n => ?_
    change (charFun ((convPow μ n).map ((a n)⁻¹ * ·)) t).re = _
    rw [charFun_map_convPow hsymm, Complex.ofReal_re]
  set C := B * (|t| / δ + 1) ^ 2
  have hC : ∀ n : ℕ, 3 ≤ n → nh μ a n t ≤ C := fun n hn => hB n hn t
  have hC0 : 0 ≤ C := (nh_nonneg (μ := μ) (a := a) 3 t).trans (hC 3 le_rfl)
  have hFeq : ∀ n : ℕ, 1 ≤ n → F n = 1 - nh μ a n t / n := by
    intro n hn
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [nh, hFdef]; field_simp; ring
  -- `F n ≥ 1 / 2` eventually
  have hF2 : ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ F n := by
    filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop ⌈2 * C⌉₊] with n hn hn'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h2C : 2 * C ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn')
    rw [hFeq n (by omega)]
    have : nh μ a n t / n ≤ 1 / 2 := by
      rw [div_le_iff₀ hn0]; linarith [hC n hn]
    linarith
  -- positivity of the limit
  have hψ : 0 < ψ := by
    have hlim := Real.tendsto_one_add_div_pow_exp (-C)
    have hle : ∀ᶠ n : ℕ in atTop, (1 + -C / n) ^ n ≤ F n ^ n := by
      filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop ⌈C⌉₊] with n hn hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hCn : C ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn')
      refine pow_le_pow_left₀ ?_ ?_ n
      · rw [neg_div, ← sub_eq_add_neg, sub_nonneg, div_le_one hn0]; exact hCn
      · rw [hFeq n (by omega), neg_div, ← sub_eq_add_neg]
        exact sub_le_sub_left (div_le_div_of_nonneg_right (hC n hn) hn0.le) _
    exact (Real.exp_pos _).trans_le (le_of_tendsto_of_tendsto hlim hFn hle)
  refine ⟨hψ, ?_⟩
  have hlog : Tendsto (fun n => -Real.log (F n ^ n)) atTop (𝓝 (-Real.log ψ)) :=
    ((Real.continuousAt_log hψ.ne').tendsto.comp hFn).neg
  -- the error term
  have herr : Tendsto (fun n : ℕ => -Real.log (F n ^ n) - nh μ a n t) atTop (𝓝 0) := by
    have hup : Tendsto (fun n : ℕ => 2 * C ^ 2 / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hF2, eventually_ge_atTop 1] with n hFn2 hn
      have hFp : 0 < F n := by linarith
      rw [Real.log_pow]
      have := Real.log_le_sub_one_of_pos hFp
      simp only [nh, hFdef] at this ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · filter_upwards [hF2, eventually_ge_atTop 3] with n hFn2 hn
      have hFp : 0 < F n := by linarith
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [Real.log_pow]
      -- `-log F ≤ 1 / F - 1`
      have h1 : -Real.log (F n) ≤ (F n)⁻¹ - 1 := by
        have := Real.log_le_sub_one_of_pos (inv_pos.2 hFp)
        rwa [Real.log_inv] at this
      have hnh := hC n hn
      have hnh0 := nh_nonneg (μ := μ) (a := a) n t
      have e : 1 - F n = nh μ a n t / n := by rw [hFeq n (by omega)]; ring
      have hnhF : nh μ a n t = n * (1 - F n) := rfl
      have key : -(n * Real.log (F n)) - nh μ a n t ≤ nh μ a n t * (nh μ a n t / n) / F n := by
        have h2 : -(n * Real.log (F n)) ≤ n * ((F n)⁻¹ - 1) := by nlinarith
        have h3 : n * ((F n)⁻¹ - 1) - nh μ a n t = nh μ a n t * (nh μ a n t / n) / F n := by
          rw [← e, hnhF]; field_simp
        linarith
      refine key.trans ?_
      rw [div_le_div_iff₀ hFp hn0]
      have : nh μ a n t * (nh μ a n t / n) * n = nh μ a n t ^ 2 := by field_simp
      rw [this]
      have : nh μ a n t ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hnh0 hnh 2
      nlinarith
  have := hlog.sub herr
  simp only [sub_zero, sub_sub_cancel] at this
  exact this

end FromWeakConvergence

section Kernel

/-- `∫₀^∞ e^{-s} cos (s y) ds = 1 / (1 + y²)`. -/
theorem integral_exp_neg_mul_cos (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-s) * cos (s * y) = 1 / (1 + y ^ 2) := by
  have ha : (-1 + y * Complex.I : ℂ).re < 0 := by simp
  have h := integral_exp_mul_complex_Ioi ha 0
  have h2 := integral_re (integrableOn_exp_mul_complex_Ioi ha 0)
  simp only [RCLike.re_to_complex] at h2
  have hval : (-Complex.exp ((-1 + y * Complex.I) * (0 : ℝ)) / (-1 + y * Complex.I)).re =
      1 / (1 + y ^ 2) := by
    have hne : (-1 + y * Complex.I : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h1 : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
    have e : -Complex.exp ((-1 + y * Complex.I) * (0 : ℝ)) / (-1 + y * Complex.I) =
        ((1 / (1 + y ^ 2) : ℝ) : ℂ) + ((y / (1 + y ^ 2) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_eq_iff hne]
      have h1' : (1 + (y : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1
      push_cast
      field_simp
      linear_combination (-(y : ℂ) ^ 2) * Complex.I_sq
    rw [e]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [← hval, ← h, ← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [Complex.exp_re, Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.one_re,
    Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.neg_im, Complex.one_im]
  ring_nf

theorem integrableOn_exp_neg : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 0) := by
  simpa using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0

theorem integral_exp_neg : ∫ s in Ioi (0 : ℝ), Real.exp (-s) = 1 := by
  simpa using integral_exp_mul_Ioi (a := -1) (by norm_num) 0

theorem integrableOn_exp_neg_mul_sq : IntegrableOn (fun s : ℝ => Real.exp (-s) * s ^ 2) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent (s := 3) (by norm_num)).congr_fun (fun s hs => ?_)
    measurableSet_Ioi
  simp only
  rw [show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]

theorem integrableOn_exp_neg_mul_add (A D : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) * (A + D * s ^ 2)) (Ioi 0) := by
  have := (integrableOn_exp_neg.const_mul A).add (integrableOn_exp_neg_mul_sq.const_mul D)
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]; ring

/-- The density `y² / (1 + y²)` of the measures `Λₙ`. -/
noncomputable def kDensity (y : ℝ) : ℝ≥0 := ⟨y ^ 2 / (1 + y ^ 2), by positivity⟩

theorem kDensity_coe (y : ℝ) : (kDensity y : ℝ) = y ^ 2 / (1 + y ^ 2) := rfl

theorem measurable_kDensity : Measurable kDensity := by
  refine Measurable.subtype_mk ?_
  fun_prop

theorem kDensity_le_one (y : ℝ) : (kDensity y : ℝ) ≤ 1 := by
  rw [kDensity_coe, div_le_one (by positivity)]; linarith

/-- `Λ = (y² / (1 + y²)) ρ(dy)`. -/
noncomputable def kMeasure (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity fun y => (kDensity y : ℝ≥0∞)

instance (ρ : Measure ℝ) [IsFiniteMeasure ρ] : IsFiniteMeasure (kMeasure ρ) := by
  refine isFiniteMeasure_withDensity ?_
  refine ne_top_of_le_ne_top (measure_ne_top ρ univ) ?_
  calc ∫⁻ y, (kDensity y : ℝ≥0∞) ∂ρ ≤ ∫⁻ _y, 1 ∂ρ := lintegral_mono fun y =>
        ENNReal.coe_le_one_iff.2 (by exact_mod_cast kDensity_le_one y)
    _ = ρ univ := by simp

theorem integral_kMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : Measure ℝ)
    (g : ℝ → E) : ∫ y, g y ∂(kMeasure ρ) = ∫ y, (y ^ 2 / (1 + y ^ 2)) • g y ∂ρ := by
  rw [kMeasure, integral_withDensity_eq_integral_smul measurable_kDensity]
  rfl

theorem cos_mul_exp_eq (s t y : ℝ) :
    (cos (s * y) : ℂ) * Complex.exp (t * y * Complex.I) =
      (Complex.exp ((t + s) * y * Complex.I) + Complex.exp ((t - s) * y * Complex.I)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, add_div, add_div, add_mul, div_mul_eq_mul_div,
    div_mul_eq_mul_div, ← Complex.exp_add, ← Complex.exp_add]
  congr 3 <;> push_cast <;> ring

/-- **Characteristic function of `Λ`.** For a finite measure `ρ`,
`φ_Λ(t) = φ_ρ(t) - ∫₀^∞ e^{-s} (φ_ρ(t + s) + φ_ρ(t - s)) / 2 ds`. -/
theorem charFun_kMeasure (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    charFun (kMeasure ρ) t = charFun ρ t -
      ∫ s in Ioi (0 : ℝ), (Real.exp (-s) : ℂ) * ((charFun ρ (t + s) + charFun ρ (t - s)) / 2) := by
  have hexp : ∀ u : ℝ, Integrable (fun y : ℝ => Complex.exp (u * y * Complex.I)) ρ := fun u =>
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun y => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I])
  -- the kernel identity
  have hk : ∀ y : ℝ, ((y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) =
      1 - ∫ s in Ioi (0 : ℝ), ((Real.exp (-s) * cos (s * y) : ℝ) : ℂ) := by
    intro y
    rw [integral_complex_ofReal, integral_exp_neg_mul_cos]
    have : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
    have h' : (1 + (y : ℂ) ^ 2) ≠ 0 := by exact_mod_cast this
    push_cast
    field_simp
    ring
  -- Fubini
  have hint : Integrable (Function.uncurry fun (s y : ℝ) =>
      ((Real.exp (-s) * cos (s * y) : ℝ) : ℂ) * Complex.exp (t * y * Complex.I))
      ((volume.restrict (Ioi (0 : ℝ))).prod ρ) := by
    have hb : Integrable (fun p : ℝ × ℝ => Real.exp (-p.1) * (1 : ℝ))
        ((volume.restrict (Ioi (0 : ℝ))).prod ρ) :=
      integrableOn_exp_neg.mul_prod (integrable_const 1)
    refine hb.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun p => ?_)
    obtain ⟨s, y⟩ := p
    simp only [Function.uncurry_apply_pair, norm_mul, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_cos_le_one _)
  have hswap := integral_integral_swap hint
  have e1 : ∀ y : ℝ, (y ^ 2 / (1 + y ^ 2)) • Complex.exp (t * y * Complex.I) =
      Complex.exp (t * y * Complex.I) - ∫ s in Ioi (0 : ℝ),
        ((Real.exp (-s) * cos (s * y) : ℝ) : ℂ) * Complex.exp (t * y * Complex.I) := by
    intro y
    rw [Complex.real_smul, hk, sub_mul, one_mul, integral_mul_const]
  rw [charFun_apply_real, integral_kMeasure]
  simp_rw [e1]
  rw [integral_sub (hexp t) ?_, ← hswap]
  swap
  · exact hint.integral_prod_right
  congr 1
  · rw [charFun_apply_real]
  refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun s _ => ?_
  have e2 : ∀ y : ℝ, ((Real.exp (-s) * cos (s * y) : ℝ) : ℂ) * Complex.exp (t * y * Complex.I) =
      (Real.exp (-s) : ℂ) * ((Complex.exp ((t + s) * y * Complex.I) +
        Complex.exp ((t - s) * y * Complex.I)) / 2) := fun y => by
    rw [Complex.ofReal_mul, mul_assoc, cos_mul_exp_eq]
  simp only [e2]
  have h1 := hexp (t + s)
  have h2 := hexp (t - s)
  push_cast at h1 h2
  rw [integral_const_mul, integral_div, integral_add h1 h2, charFun_apply_real,
    charFun_apply_real]
  push_cast
  rfl

end Kernel

section Lap

/-- The transform `λ_g(t) = ∫₀^∞ e^{-s} ((g(t + s) + g(t - s)) / 2 - g(t)) ds`. -/
noncomputable def lap (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-s) * ((g (t + s) + g (t - s)) / 2 - g t)

theorem abs_lap_integrand_le {g : ℝ → ℝ} {B δ : ℝ} (hB0 : 0 ≤ B) (hδ : 0 < δ)
    (hg : ∀ u, |g u| ≤ B * (|u| / δ + 1) ^ 2) (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |(g (t + s) + g (t - s)) / 2 - g t| ≤ 3 * B * (|t| / δ + 1) ^ 2 + 2 * B / δ ^ 2 * s ^ 2 := by
  set c := |t| / δ + 1
  have hc : 0 ≤ c := by positivity
  have key : ∀ u, |u| ≤ |t| + s → |g u| ≤ B * (2 * c ^ 2 + 2 * (s / δ) ^ 2) := by
    intro u hu
    refine (hg u).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    have h1 : |u| / δ + 1 ≤ c + s / δ := by
      have : |u| / δ ≤ (|t| + s) / δ := div_le_div_of_nonneg_right hu hδ.le
      rw [add_div] at this; linarith
    have h2 : (|u| / δ + 1) ^ 2 ≤ (c + s / δ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith [sq_nonneg (c - s / δ)]
  have h1 := key (t + s) ((abs_add_le _ _).trans (by rw [abs_of_nonneg hs]))
  have h2 := key (t - s) ((abs_sub _ _).trans (by rw [abs_of_nonneg hs]))
  have h3 := hg t
  have e : 2 * B / δ ^ 2 * s ^ 2 = B * (2 * (s / δ) ^ 2) := by field_simp
  rw [e]
  calc |(g (t + s) + g (t - s)) / 2 - g t| ≤ (|g (t + s)| + |g (t - s)|) / 2 + |g t| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_div, abs_two]
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by nlinarith

theorem integrableOn_lap_bound (A D : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) * (A + D * s ^ 2)) (Ioi 0) :=
  integrableOn_exp_neg_mul_add A D

/-- Dominated convergence for `λ`. -/
theorem tendsto_lap {g : ℕ → ℝ → ℝ} {g₀ : ℝ → ℝ} {B δ : ℝ} (hB0 : 0 ≤ B) (hδ : 0 < δ)
    (hm : ∀ n, Continuous (g n))
    (hB : ∀ᶠ n in atTop, ∀ u, |g n u| ≤ B * (|u| / δ + 1) ^ 2)
    (hlim : ∀ u, Tendsto (fun n => g n u) atTop (𝓝 (g₀ u))) (t : ℝ) :
    Tendsto (fun n => lap (g n) t) atTop (𝓝 (lap g₀ t)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => Real.exp (-s) * (3 * B * (|t| / δ + 1) ^ 2 + 2 * B / δ ^ 2 * s ^ 2))
    (Eventually.of_forall fun n => Continuous.aestronglyMeasurable (by
      have := hm n; fun_prop)) ?_ (integrableOn_lap_bound _ _) ?_
  · filter_upwards [hB] with n hn
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun s (hs : 0 < s) => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_lap_integrand_le hB0 hδ hn t hs.le)
      (Real.exp_pos _).le
  · refine ae_of_all _ fun s => ?_
    exact (((hlim _).add (hlim _)).div_const 2 |>.sub (hlim t)).const_mul _

theorem continuousAt_lap {g : ℝ → ℝ} {B δ : ℝ} (hB0 : 0 ≤ B) (hδ : 0 < δ) (hc : Continuous g)
    (hg : ∀ u, |g u| ≤ B * (|u| / δ + 1) ^ 2) (t₀ : ℝ) : ContinuousAt (lap g) t₀ := by
  refine continuousAt_of_dominated
    (bound := fun s => Real.exp (-s) * (3 * B * ((|t₀| + 1) / δ + 1) ^ 2 + 2 * B / δ ^ 2 * s ^ 2))
    (Eventually.of_forall fun t => Continuous.aestronglyMeasurable (by fun_prop)) ?_
    (integrableOn_lap_bound _ _) (ae_of_all _ fun s => by
      have : Continuous fun t => Real.exp (-s) * ((g (t + s) + g (t - s)) / 2 - g t) := by
        fun_prop
      exact this.continuousAt)
  filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with t ht
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine ae_of_all _ fun s (hs : 0 < s) => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ((abs_lap_integrand_le hB0 hδ hg t hs.le).trans ?_)
    (Real.exp_pos _).le
  have : |t| ≤ |t₀| + 1 := by
    have := Metric.mem_ball.1 ht
    rw [Real.dist_eq] at this
    linarith [abs_sub_abs_le_abs_sub t t₀]
  have : |t| / δ + 1 ≤ (|t₀| + 1) / δ + 1 := by gcongr
  have : (|t| / δ + 1) ^ 2 ≤ ((|t₀| + 1) / δ + 1) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
  nlinarith

theorem lap_pos {g : ℝ → ℝ} {B δ : ℝ} (hB0 : 0 ≤ B) (hδ : 0 < δ) (hc : Continuous g)
    (hg : ∀ u, |g u| ≤ B * (|u| / δ + 1) ^ 2) (hg0 : g 0 = 0) (hnn : ∀ u, 0 ≤ g u)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hgs₀ : 0 < g s₀) : 0 < lap g 0 := by
  set φ : ℝ → ℝ := fun s => Real.exp (-s) * ((g (0 + s) + g (0 - s)) / 2 - g 0)
  have hφc : Continuous φ := by fun_prop
  have hint : IntegrableOn φ (Ioi 0) := by
    refine (integrableOn_lap_bound (3 * B * (|0| / δ + 1) ^ 2) (2 * B / δ ^ 2)).mono' ?_ ?_
    · exact hφc.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun s (hs : 0 < s) => ?_
      simp only [φ]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (abs_lap_integrand_le hB0 hδ hg 0 hs.le)
        (Real.exp_pos _).le
  have hnn' : ∀ s, 0 ≤ φ s := fun s => by
    simp only [φ, hg0, sub_zero]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hnn (0 + s), hnn (0 - s)])
  have hpos : 0 < φ s₀ := by
    simp only [φ, hg0, sub_zero, zero_add, zero_sub]
    exact mul_pos (Real.exp_pos _) (by linarith [hnn (-s₀)])
  refine (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hnn') hint).2 ?_
  have hopen : IsOpen ({s | 0 < φ s} ∩ Ioi 0) := (isOpen_lt continuous_const hφc).inter isOpen_Ioi
  have hne : ({s | 0 < φ s} ∩ Ioi 0).Nonempty := ⟨s₀, hpos, hs₀⟩
  refine lt_of_lt_of_le (pos_iff_ne_zero.2 (hopen.measure_ne_zero volume hne)) (measure_mono ?_)
  rintro s ⟨hs1, hs2⟩
  exact ⟨ne_of_gt hs1, hs2⟩

theorem lap_smul (c : ℝ) (g : ℝ → ℝ) (t : ℝ) : lap (fun u => c * g u) t = c * lap g t := by
  rw [lap, lap, ← integral_const_mul]
  congr 1; funext s; ring

end Lap

section Symmetric

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

theorem cosTransform_eq_re (s : ℝ) : cosTransform μ s = (charFun μ s).re := by
  have hint : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I)) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply_real, ← RCLike.re_to_complex, ← integral_re hint, cosTransform]
  congr 1; funext x
  rw [RCLike.re_to_complex, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem continuous_cosTransform : Continuous (cosTransform μ) := by
  have : cosTransform μ = fun s => (charFun μ s).re := funext cosTransform_eq_re
  rw [this]
  exact Complex.continuous_re.comp continuous_charFun

theorem continuous_nh (n : ℕ) : Continuous (nh μ a n) := by
  unfold nh
  have := continuous_cosTransform (μ := μ)
  fun_prop

/-- `Λₙ`, the image of `μ` under `x ↦ x / aₙ` weighted by `y² / (1 + y²)`. -/
noncomputable def lamMeasure (μ : Measure ℝ) (a : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  kMeasure (μ.map ((a n)⁻¹ * ·))

instance (n : ℕ) : IsFiniteMeasure (lamMeasure μ a n) := by
  unfold lamMeasure; infer_instance

theorem charFun_map_inv_mul (hsymm : μ.map (fun x => -x) = μ) (n : ℕ) (u : ℝ) :
    charFun (μ.map ((a n)⁻¹ * ·)) u = (cosTransform μ ((a n)⁻¹ * u) : ℂ) := by
  rw [charFun_map_mul, GCLT.charFun_eq_integral_cos hsymm]
  rfl

omit [IsProbabilityMeasure μ] in
theorem cosTransform_eq_one_sub_nh {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    cosTransform μ ((a n)⁻¹ * u) = 1 - nh μ a n u / n := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [nh]; field_simp; ring

/-- `φ_{Λₙ}(t) = λ_{hₙ}(t) / n`. -/
theorem charFun_lamMeasure (hsymm : μ.map (fun x => -x) = μ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    charFun (lamMeasure μ a n) t = ((lap (nh μ a n) t / n : ℝ) : ℂ) := by
  set F : ℝ → ℝ := fun u => cosTransform μ ((a n)⁻¹ * u) with hFdef
  have hFc : Continuous F := continuous_cosTransform.comp (continuous_const.mul continuous_id)
  have hF1 : ∀ u, |F u| ≤ 1 := fun u =>
    abs_le.2 ⟨neg_one_le_cosTransform _, cosTransform_le_one _⟩
  rw [lamMeasure, charFun_kMeasure]
  simp_rw [charFun_map_inv_mul hsymm]
  have e : ∀ s : ℝ, ((Real.exp (-s) : ℝ) : ℂ) *
      ((((cosTransform μ ((a n)⁻¹ * (t + s)) : ℝ) : ℂ) +
        ((cosTransform μ ((a n)⁻¹ * (t - s)) : ℝ) : ℂ)) / 2) =
      ((Real.exp (-s) * ((F (t + s) + F (t - s)) / 2) : ℝ) : ℂ) := fun s => by
    push_cast; ring
  simp_rw [e, integral_complex_ofReal, ← Complex.ofReal_sub]
  congr 1
  have hint1 : IntegrableOn (fun s : ℝ => Real.exp (-s) * F t) (Ioi 0) :=
    integrableOn_exp_neg.mul_const _
  have hint2 : IntegrableOn (fun s : ℝ => Real.exp (-s) * ((F (t + s) + F (t - s)) / 2)) (Ioi 0) := by
    refine integrableOn_exp_neg.mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
    rw [abs_div, abs_two, div_le_one two_pos]
    exact (abs_add_le _ _).trans (by linarith [hF1 (t + s), hF1 (t - s)])
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have e2 : ∀ s : ℝ, Real.exp (-s) * ((nh μ a n (t + s) + nh μ a n (t - s)) / 2 - nh μ a n t) =
      n * (Real.exp (-s) * F t - Real.exp (-s) * ((F (t + s) + F (t - s)) / 2)) := fun s => by
    simp only [nh, hFdef]; ring
  rw [lap]
  simp_rw [e2]
  rw [integral_const_mul, integral_sub hint1 hint2, integral_mul_const, integral_exp_neg]
  field_simp
  simp [hFdef, div_eq_inv_mul]

theorem measureReal_univ_lamMeasure (hsymm : μ.map (fun x => -x) = μ) {n : ℕ} (hn : n ≠ 0) :
    (lamMeasure μ a n).real univ = lap (nh μ a n) 0 / n := by
  have h := charFun_lamMeasure (a := a) hsymm hn 0
  rw [charFun_zero] at h
  exact_mod_cast h

end Symmetric

section Pipeline

/-- `T(x) = E[X² / max (X², x²)] = E[min (1, X² / x²)]`. -/
noncomputable def sqRatio (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, y ^ 2 / max (y ^ 2) (x ^ 2) ∂μ

/-- The bounded continuous test function `(1 + y²) / max (y², x²)`. -/
noncomputable def gfun {x : ℝ} (hx : 0 < x) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => (1 + y ^ 2) / max (y ^ 2) (x ^ 2))
    (by
      refine Continuous.div (by fun_prop) (by fun_prop) fun y => ?_
      exact ne_of_gt (lt_of_lt_of_le (by positivity) (le_max_right _ _)))
    (1 / x ^ 2 + 1) (fun y => by
      have hM : 0 < max (y ^ 2) (x ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), add_div]
      gcongr
      · exact le_max_right _ _
      · rw [div_le_one hM]; exact le_max_left _ _)

theorem gfun_apply {x : ℝ} (hx : 0 < x) (y : ℝ) :
    gfun hx y = (1 + y ^ 2) / max (y ^ 2) (x ^ 2) := rfl

theorem kernel_mul_gfun {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (y : ℝ) :
    ((a⁻¹ * y) ^ 2 / (1 + (a⁻¹ * y) ^ 2)) * gfun hx (a⁻¹ * y) =
      y ^ 2 / max (y ^ 2) ((a * x) ^ 2) := by
  rw [gfun_apply]
  have h1 : (1 + (a⁻¹ * y) ^ 2) ≠ 0 := by positivity
  have hM : 0 < max ((a⁻¹ * y) ^ 2) (x ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have e1 : (a⁻¹ * y) ^ 2 / (1 + (a⁻¹ * y) ^ 2) * ((1 + (a⁻¹ * y) ^ 2) /
      max ((a⁻¹ * y) ^ 2) (x ^ 2)) = (a⁻¹ * y) ^ 2 / max ((a⁻¹ * y) ^ 2) (x ^ 2) := by
    field_simp
  rw [e1]
  have ha2 : (0 : ℝ) ≤ a ^ 2 := by positivity
  have e2 : max ((a⁻¹ * y) ^ 2) (x ^ 2) = max (y ^ 2) ((a * x) ^ 2) / a ^ 2 := by
    rw [← max_div_div_right ha2]
    congr 1 <;> field_simp
  rw [e2]
  field_simp

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

omit [IsProbabilityMeasure μ] in
theorem integral_gfun_lamMeasure (ha : ∀ n, 0 < a n) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ y, gfun hx y ∂(lamMeasure μ a n) = sqRatio μ (a n * x) := by
  show ∫ y, gfun hx y ∂(kMeasure (μ.map ((a n)⁻¹ * ·))) = _
  rw [integral_kMeasure, integral_map (by fun_prop)
    (Continuous.aestronglyMeasurable (by
      have := (gfun hx).continuous
      exact ((continuous_pow 2).div (by fun_prop) fun y => by positivity).smul this))]
  simp_rw [smul_eq_mul, kernel_mul_gfun (ha n) hx]
  rfl

/-- The normalized measures `Λₙ / Λₙ(ℝ)`. -/
noncomputable def lamNorm (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  FiniteMeasure.normalize ⟨lamMeasure μ a n, inferInstance⟩

theorem lamNorm_eq (hsymm : μ.map (fun x => -x) = μ) {n : ℕ} (hn : n ≠ 0)
    (h0 : 0 < lap (nh μ a n) 0) :
    (lamNorm μ a n : Measure ℝ) = ((lap (nh μ a n) 0 / n : ℝ).toNNReal)⁻¹ • lamMeasure μ a n := by
  set Λ : FiniteMeasure ℝ := ⟨lamMeasure μ a n, inferInstance⟩
  have hmass : (Λ.mass : ℝ) = (lamMeasure μ a n).real univ := by
    rw [measureReal_def, ← ENNReal.coe_toReal, FiniteMeasure.ennreal_mass]
    rfl
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hne : Λ ≠ 0 := by
    refine (FiniteMeasure.mass_nonzero_iff _).1 fun hz => ?_
    rw [hz, measureReal_univ_lamMeasure hsymm hn] at hmass
    exact absurd hmass.symm (by simpa using (div_pos h0 hn').ne')
  rw [lamNorm, FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hne]
  congr 2
  rw [← measureReal_univ_lamMeasure hsymm hn, ← hmass, Real.toNNReal_coe]

theorem charFun_lamNorm (hsymm : μ.map (fun x => -x) = μ) {n : ℕ} (hn : n ≠ 0)
    (h0 : 0 < lap (nh μ a n) 0) (t : ℝ) :
    charFun (lamNorm μ a n : Measure ℝ) t = ((lap (nh μ a n) t / lap (nh μ a n) 0 : ℝ) : ℂ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [lamNorm_eq hsymm hn h0, charFun_apply_real, integral_smul_nnreal_measure,
    ← charFun_apply_real, charFun_lamMeasure hsymm hn, NNReal.smul_def, Complex.real_smul,
    ← Complex.ofReal_mul]
  simp only [NNReal.coe_inv, Real.coe_toNNReal _ (div_pos h0 hn').le]
  congr 1
  field_simp

theorem mul_sqRatio_eq (hsymm : μ.map (fun x => -x) = μ) (ha : ∀ n, 0 < a n) {n : ℕ}
    (hn : n ≠ 0) (h0 : 0 < lap (nh μ a n) 0) {x : ℝ} (hx : 0 < x) :
    (n : ℝ) * sqRatio μ (a n * x) =
      lap (nh μ a n) 0 * ∫ y, gfun hx y ∂(lamNorm μ a n : Measure ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [lamNorm_eq hsymm hn h0, integral_smul_nnreal_measure, integral_gfun_lamMeasure ha,
    NNReal.smul_def, smul_eq_mul]
  simp only [NNReal.coe_inv, Real.coe_toNNReal _ (div_pos h0 hn').le]
  field_simp

variable {h : ℝ → ℝ} {B δ : ℝ}

/-- The characteristic functions of `Λₙ / Λₙ(ℝ)` converge to `λ_h / λ_h(0)`. -/
theorem tendsto_charFun_lamNorm (hsymm : μ.map (fun x => -x) = μ) (hB0 : 0 ≤ B) (hδ : 0 < δ)
    (hB : ∀ᶠ n in atTop, ∀ u, |nh μ a n u| ≤ B * (|u| / δ + 1) ^ 2)
    (hlim : ∀ u, Tendsto (fun n => nh μ a n u) atTop (𝓝 (h u))) (hpos : 0 < lap h 0) (t : ℝ) :
    Tendsto (fun n => charFun (lamNorm μ a n : Measure ℝ) t) atTop
      (𝓝 ((lap h t / lap h 0 : ℝ) : ℂ)) := by
  have hLam : ∀ t, Tendsto (fun n => lap (nh μ a n) t) atTop (𝓝 (lap h t)) :=
    tendsto_lap hB0 hδ continuous_nh hB hlim
  refine (Complex.continuous_ofReal.tendsto _ |>.comp ((hLam t).div (hLam 0) hpos.ne')).congr' ?_
  filter_upwards [eventually_ne_atTop 0, (tendsto_order.1 (hLam 0)).1 0 hpos] with n hn h0
  rw [Function.comp_apply, charFun_lamNorm hsymm hn h0]
  rfl

/-- **The pipeline.** If `hₙ → h` with quadratic bounds and `λ_h(0) > 0`, and `P` is a
probability measure with characteristic function `λ_h / λ_h(0)`, then
`n T(aₙ x) → λ_h(0) ∫ (1 + y²) / max (y², x²) dP(y)` for every `x > 0`. -/
theorem tendsto_mul_sqRatio (hsymm : μ.map (fun x => -x) = μ) (ha : ∀ n, 0 < a n)
    (hB0 : 0 ≤ B) (hδ : 0 < δ)
    (hB : ∀ᶠ n in atTop, ∀ u, |nh μ a n u| ≤ B * (|u| / δ + 1) ^ 2)
    (hlim : ∀ u, Tendsto (fun n => nh μ a n u) atTop (𝓝 (h u))) (hpos : 0 < lap h 0)
    (P : ProbabilityMeasure ℝ) (hP : ∀ t, charFun (P : Measure ℝ) t = ((lap h t / lap h 0 : ℝ) : ℂ))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (lap h 0 * ∫ y, gfun hx y ∂(P : Measure ℝ))) := by
  have hLam0 : Tendsto (fun n => lap (nh μ a n) 0) atTop (𝓝 (lap h 0)) :=
    tendsto_lap hB0 hδ continuous_nh hB hlim 0
  have hconv := ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => by
    rw [hP]; exact tendsto_charFun_lamNorm hsymm hB0 hδ hB hlim hpos t
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv) (gfun hx)
  refine (hLam0.mul hint).congr' ?_
  filter_upwards [eventually_ne_atTop 0, (tendsto_order.1 hLam0).1 0 hpos] with n hn h0
  exact (mul_sqRatio_eq hsymm ha hn h0 hx).symm

/-- Existence of the limit `P` of `Λₙ / Λₙ(ℝ)` (Lévy's continuity theorem). -/
theorem exists_charFun_eq_lap (hsymm : μ.map (fun x => -x) = μ) (hB0 : 0 ≤ B) (hδ : 0 < δ)
    (hB : ∀ᶠ n in atTop, ∀ u, |nh μ a n u| ≤ B * (|u| / δ + 1) ^ 2)
    (hlim : ∀ u, Tendsto (fun n => nh μ a n u) atTop (𝓝 (h u))) (hpos : 0 < lap h 0)
    (hc : Continuous h) (hh : ∀ u, |h u| ≤ B * (|u| / δ + 1) ^ 2) :
    ∃ P : ProbabilityMeasure ℝ, ∀ t, charFun (P : Measure ℝ) t = ((lap h t / lap h 0 : ℝ) : ℂ) := by
  have hf : ContinuousAt (fun t => ((lap h t / lap h 0 : ℝ) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp
      ((continuousAt_lap hB0 hδ hc hh 0).div_const _)
  obtain ⟨P, hP, -⟩ := exists_tendsto_of_tendsto_charFun (μ := lamNorm μ a) hf
    (tendsto_charFun_lamNorm hsymm hB0 hδ hB hlim hpos)
  exact ⟨P, fun t => congrFun hP t⟩

end Pipeline

section SqRatio

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem sq_div_max_eq {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    y ^ 2 / max (y ^ 2) (x ^ 2) = min (x ^ 2) (y ^ 2) / x ^ 2 := by
  have hx2 : 0 < x ^ 2 := by positivity
  rcases le_total (y ^ 2) (x ^ 2) with h | h
  · rw [max_eq_right h, min_eq_right h]
  · rw [max_eq_left h, min_eq_left h, div_self (ne_of_gt (hx2.trans_le h)), div_self hx2.ne']

omit [IsFiniteMeasure μ] in
theorem sqRatio_eq_div {x : ℝ} (hx : x ≠ 0) : sqRatio μ x = minSqMoment μ x / x ^ 2 := by
  rw [sqRatio, minSqMoment, ← integral_div]
  simp_rw [sq_div_max_eq hx]

omit [IsFiniteMeasure μ] in
theorem sqRatio_nonneg (x : ℝ) : 0 ≤ sqRatio μ x :=
  integral_nonneg fun _ => div_nonneg (sq_nonneg _) (le_max_of_le_left (sq_nonneg _))

theorem integrable_sq_div_max {x : ℝ} (hx : x ≠ 0) :
    Integrable (fun y : ℝ => y ^ 2 / max (y ^ 2) (x ^ 2)) μ := by
  have hx2 : 0 < x ^ 2 := by positivity
  refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact Continuous.aestronglyMeasurable (Continuous.div (by fun_prop) (by fun_prop)
      fun y => ne_of_gt (lt_of_lt_of_le hx2 (le_max_right _ _)))
  · have hM : 0 < max (y ^ 2) (x ^ 2) := lt_of_lt_of_le hx2 (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hM.le), div_le_one hM]
    exact le_max_left _ _

theorem sqRatio_antitoneOn : AntitoneOn (sqRatio μ) (Ioi 0) := by
  intro x hx x' hx' hxx'
  have hx0 : (0 : ℝ) < x := hx
  refine integral_mono (integrable_sq_div_max (ne_of_gt (hx0.trans_le hxx')))
    (integrable_sq_div_max hx0.ne') fun y => ?_
  have hM : 0 < max (y ^ 2) (x ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  exact div_le_div_of_nonneg_left (sq_nonneg _) hM
    (max_le_max le_rfl (pow_le_pow_left₀ hx0.le hxx' 2))

theorem sqRatio_pos_of_pos {x₀ : ℝ} (hx₀ : 0 < x₀) (h : 0 < sqRatio μ x₀) {x : ℝ}
    (hx : 0 < x) : 0 < sqRatio μ x := by
  rcases le_total x x₀ with hle | hle
  · exact h.trans_le (sqRatio_antitoneOn hx hx₀ hle)
  · rw [sqRatio_eq_div hx.ne']
    rw [sqRatio_eq_div hx₀.ne'] at h
    have hZ0 : 0 < minSqMoment μ x₀ := (div_pos_iff_of_pos_right (by positivity)).1 h
    exact div_pos (hZ0.trans_le (minSqMoment_mono hx₀.le hle)) (by positivity)

end SqRatio

section Main

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

omit [IsProbabilityMeasure μ] in
theorem nh_const_mul {r : ℝ} (hr : r ≠ 0) (n : ℕ) (u : ℝ) :
    nh μ (fun n => r * a n) n u = nh μ a n (u / r) := by
  simp only [nh, mul_inv]
  congr 3
  field_simp

theorem integral_gfun_pos (P : ProbabilityMeasure ℝ) {x : ℝ} (hx : 0 < x) :
    0 < ∫ y, gfun hx y ∂(P : Measure ℝ) := by
  have hpos : ∀ y, 0 < gfun hx y := fun y => by
    rw [gfun_apply]
    exact div_pos (by positivity) (lt_of_lt_of_le (by positivity) (le_max_right _ _))
  refine (integral_pos_iff_support_of_nonneg (fun y => (hpos y).le)
    ((gfun hx).integrable _)).2 ?_
  have : Function.support (fun y => gfun hx y) = univ :=
    Function.support_eq_univ fun y => (hpos y).ne'
  rw [this, measure_univ]
  exact one_pos

/-- From the converse pipeline to regular variation: if `n T(aₙ x) → K x ^ (-α)` for all
`x > 0`, with `K > 0` and `0 < α < 2`, then the tail is regularly varying with index `-α`,
`U` with index `2 - α`, and `n P(|X| > aₙ) → K (2 - α) / 2`. -/
theorem isRegularlyVarying_of_tendsto_mul_sqRatio (ha : ∀ n, 0 < a n) {K α : ℝ} (hK : 0 < K)
    (hα0 : 0 < α) (hα2 : α < 2)
    (hL : ∀ x, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (K * x ^ (-α)))) :
    IsRegularlyVarying (absTail μ) (-α) ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 (K * ((2 - α) / 2))) := by
  have hL1 : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n)) atTop (𝓝 K) := by
    simpa using hL 1 one_pos
  have hTpos : ∀ x, 0 < x → 0 < sqRatio μ x := by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hL1).1 0 hK).exists
    have h1 : 0 < sqRatio μ (a n) := by
      by_contra hc
      have : sqRatio μ (a n) = 0 := le_antisymm (not_lt.1 hc) (sqRatio_nonneg _)
      rw [this, mul_zero] at hn
      exact lt_irrefl _ hn
    exact fun x hx => sqRatio_pos_of_pos (ha n) h1 hx
  have hT : IsRegularlyVarying (sqRatio μ) (-α) :=
    isRegularlyVarying_of_tendsto_mul_comp sqRatio_antitoneOn hTpos ha hK hL
  have hZ : IsRegularlyVarying (minSqMoment μ) (2 - α) := by
    have := (IsRegularlyVarying.rpow_id 2).mul hT
    rw [← sub_eq_add_neg] at this
    refine this.congr ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqRatio_eq_div hx.ne', Real.rpow_two]
    field_simp
  have hG := isRegularlyVarying_absTail_of_minSqMoment (by linarith) hZ
  rw [show 2 - α - 2 = -α by ring] at hG
  refine ⟨hG, isRegularlyVarying_truncSecondMoment_of_minSqMoment (by linarith) hZ, ?_⟩
  have hatop := tendsto_atTop_of_tendsto_mul_comp (L := fun _ => K) sqRatio_antitoneOn hTpos ha hL1
  have hr := (tendsto_sq_mul_absTail_div_minSqMoment hZ).comp hatop
  refine (hL1.mul hr).congr' ?_
  filter_upwards [hatop.eventually hZ.1] with n hn
  simp only [Function.comp_apply]
  rw [sqRatio_eq_div (ha n).ne']
  have := (ha n).ne'
  field_simp

/-- **Converse of the generalized central limit theorem, symmetric case**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35]). Let `μ` be a symmetric probability law on
`ℝ`, `aₙ > 0`, and suppose the laws of `(X₁ + ⋯ + Xₙ) / aₙ` converge weakly to the symmetric
`α`-stable law `ν` with characteristic function `exp (-c |t| ^ α)`, `0 < α < 2`, `c > 0`.
Then the two-sided tail `P(|X| > x)` is regularly varying with index `-α`, the truncated second
moment `U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α`, and
`n P(|X| > aₙ)` converges to a positive constant. -/
theorem isRegularlyVarying_of_tendsto_isSymmStable (hsymm : μ.map (fun x => -x) = μ)
    (ha : ∀ n, 0 < a n) {α c : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hc : 0 < c)
    {ν : ProbabilityMeasure ℝ} (hν : IsSymmStable α c (ν : Measure ℝ))
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) :
    IsRegularlyVarying (absTail μ) (-α) ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      ∃ K > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 K) := by
  obtain ⟨δ, hδ, hb⟩ := exists_nh_le hsymm hconv
  set B := Real.log 2
  have hB0 : 0 ≤ B := Real.log_nonneg one_le_two
  set h : ℝ → ℝ := fun u => c * |u| ^ α with hh
  have hBa : ∀ᶠ n in atTop, ∀ u, |nh μ a n u| ≤ B * (|u| / δ + 1) ^ 2 := by
    filter_upwards [eventually_ge_atTop 3] with n hn u
    rw [abs_of_nonneg (nh_nonneg _ _)]
    exact hb n hn u
  have hlim : ∀ u, Tendsto (fun n => nh μ a n u) atTop (𝓝 (h u)) := by
    intro u
    have := (tendsto_nh hsymm hconv hb u).2
    rwa [hν.2 u, Complex.ofReal_re, Real.log_exp, neg_neg] at this
  have hhc : Continuous h := continuous_const.mul (continuous_abs.rpow_const fun _ => Or.inr hα0.le)
  have hhb : ∀ u, |h u| ≤ B * (|u| / δ + 1) ^ 2 := by
    intro u
    rw [abs_of_nonneg (by positivity)]
    exact le_of_tendsto (hlim u) (by
      filter_upwards [hBa] with n hn
      exact (le_abs_self _).trans (hn u))
  have hpos : 0 < lap h 0 := lap_pos hB0 hδ hhc hhb (by simp [hh, Real.zero_rpow hα0.ne'])
    (fun u => by positivity) one_pos (by simp [hh, hc])
  obtain ⟨P, hP⟩ := exists_charFun_eq_lap hsymm hB0 hδ hBa hlim hpos hhc hhb
  set L : ℝ → ℝ := fun x => lap h 0 * ∫ y, (1 + y ^ 2) / max (y ^ 2) (x ^ 2) ∂(P : Measure ℝ)
  have hlimL : ∀ x (hx : 0 < x), Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (L x)) := fun x hx => tendsto_mul_sqRatio hsymm ha hB0 hδ hBa hlim hpos P hP hx
  -- scaling: `L (r x) = r ^ (-α) L x`
  have hscale : ∀ r x, 0 < r → 0 < x → L (r * x) = r ^ (-α) * L x := by
    intro r x hr hx
    set h' : ℝ → ℝ := fun u => r ^ (-α) * h u
    have hlap : ∀ t, lap h' t = r ^ (-α) * lap h t := lap_smul _ _
    have hr' : 0 < r ^ (-α) := Real.rpow_pos_of_pos hr _
    have hBa' : ∀ᶠ n in atTop, ∀ u, |nh μ (fun n => r * a n) n u| ≤
        B * (|u| / (r * δ) + 1) ^ 2 := by
      filter_upwards [hBa] with n hn u
      rw [nh_const_mul hr.ne', ← div_div, ← abs_of_pos hr, ← abs_div, abs_of_pos hr]
      exact hn _
    have hlim' : ∀ u, Tendsto (fun n => nh μ (fun n => r * a n) n u) atTop (𝓝 (h' u)) := by
      intro u
      simp_rw [nh_const_mul hr.ne']
      convert hlim (u / r) using 2
      simp only [h', hh]
      rw [abs_div, abs_of_pos hr, Real.div_rpow (abs_nonneg _) hr.le, Real.rpow_neg hr.le]
      field_simp
    have hpos' : 0 < lap h' 0 := by rw [hlap]; exact mul_pos hr' hpos
    have hP' : ∀ t, charFun (P : Measure ℝ) t = ((lap h' t / lap h' 0 : ℝ) : ℂ) := by
      intro t; rw [hP, hlap, hlap, mul_div_mul_left _ _ hr'.ne']
    have h1 := tendsto_mul_sqRatio (a := fun n => r * a n) hsymm (fun n => mul_pos hr (ha n))
      hB0 (mul_pos hr hδ) hBa' hlim' hpos' P hP' hx
    have h2 := hlimL (r * x) (mul_pos hr hx)
    have e : ∀ n, r * a n * x = a n * (r * x) := fun n => by ring
    simp_rw [e] at h1
    rw [hlap] at h1
    have := tendsto_nhds_unique h2 h1
    rw [this, mul_assoc]
    rfl
  have hL1 : 0 < L 1 := mul_pos hpos (integral_gfun_pos P one_pos)
  obtain ⟨hG, hU, hK⟩ := isRegularlyVarying_of_tendsto_mul_sqRatio (μ := μ) ha hL1 hα0 hα2
    (fun x hx => by
      have := hscale x 1 hx one_pos
      rw [mul_one] at this
      rw [← mul_comm (x ^ (-α)), ← this]
      exact hlimL x hx)
  exact ⟨hG, hU, _, mul_pos hL1 (by linarith), hK⟩

end Main

section Characterization

/-- An additive antitone function `ℝ → ℝ` is linear. -/
theorem eq_mul_of_add_of_antitone {φ : ℝ → ℝ} (hadd : ∀ u v, φ (u + v) = φ u + φ v)
    (hanti : Antitone φ) (u : ℝ) : φ u = u * φ 1 := by
  set f : ℝ →+ ℝ := AddMonoidHom.mk' φ hadd
  have hq : ∀ q : ℚ, φ q = q * φ 1 := fun q => by
    have := map_ratCast_smul f ℝ ℝ q 1
    simpa [f] using this
  set c := φ 1
  have h0 : φ 0 = 0 := by have := hadd 0 0; rw [add_zero] at this; linarith
  have hc : c ≤ 0 := h0 ▸ hanti zero_le_one
  have hη : ∀ ε : ℝ, 0 < ε → 0 < ε / (1 - c) := fun ε hε => div_pos hε (by linarith)
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u - ε / (1 - c) < u by linarith [hη ε hε])
    have h1 : φ u ≤ φ q := hanti hq2.le
    rw [hq] at h1
    have h2 : (q : ℝ) * c ≤ (u - ε / (1 - c)) * c := mul_le_mul_of_nonpos_right hq1.le hc
    have h3 : -(ε / (1 - c)) * c ≤ ε := by
      have : ε / (1 - c) * (1 - c) = ε := div_mul_cancel₀ _ (by linarith)
      nlinarith [hη ε hε]
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < u + ε / (1 - c) by linarith [hη ε hε])
    have h1 : φ q ≤ φ u := hanti hq1.le
    rw [hq] at h1
    have h2 : (u + ε / (1 - c)) * c ≤ (q : ℝ) * c := mul_le_mul_of_nonpos_right hq2.le hc
    have h3 : -(ε / (1 - c)) * c ≤ ε := by
      have : ε / (1 - c) * (1 - c) = ε := div_mul_cancel₀ _ (by linarith)
      nlinarith [hη ε hε]
    linarith

/-- **Characterization of the limit.** If `T > 0` is nonincreasing and `T(l x) / T(x) → g(l)`
with `g(l) > 0` for every `l > 0`, then `g(l) = l ^ ρ` for some `ρ ≤ 0`. -/
theorem exists_rpow_of_tendsto_div {T g : ℝ → ℝ} (hT : AntitoneOn T (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < T x) (hg0 : ∀ l, 0 < l → 0 < g l)
    (hg : ∀ l, 0 < l → Tendsto (fun x => T (l * x) / T x) atTop (𝓝 (g l))) :
    ∃ ρ : ℝ, ρ ≤ 0 ∧ ∀ l, 0 < l → g l = l ^ ρ := by
  have hmul : ∀ l m, 0 < l → 0 < m → g (l * m) = g l * g m := by
    intro l m hl hm
    have h1 := ((hg l hl).comp (tendsto_id.const_mul_atTop hm)).mul (hg m hm)
    refine tendsto_nhds_unique (hg (l * m) (mul_pos hl hm)) (h1.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, id]
    have := (hpos _ (mul_pos hm hx)).ne'
    rw [mul_assoc l m x]
    field_simp
  have hmono : ∀ l m, 0 < l → l ≤ m → g m ≤ g l := by
    intro l m hl hlm
    refine le_of_tendsto_of_tendsto (hg m (hl.trans_le hlm)) (hg l hl) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_le_div_of_nonneg_right (hT (mul_pos hl hx) (mul_pos (hl.trans_le hlm) hx)
      (mul_le_mul_of_nonneg_right hlm hx.le)) (hpos x hx).le
  set φ : ℝ → ℝ := fun u => Real.log (g (Real.exp u))
  have hadd : ∀ u v, φ (u + v) = φ u + φ v := by
    intro u v
    simp only [φ, Real.exp_add]
    rw [hmul _ _ (Real.exp_pos _) (Real.exp_pos _),
      Real.log_mul (hg0 _ (Real.exp_pos _)).ne' (hg0 _ (Real.exp_pos _)).ne']
  have hanti : Antitone φ := fun u v huv =>
    Real.log_le_log (hg0 _ (Real.exp_pos _))
      (hmono _ _ (Real.exp_pos _) (Real.exp_le_exp.2 huv))
  refine ⟨φ 1, ?_, fun l hl => ?_⟩
  · have := hanti zero_le_one
    have h0 : φ 0 = 0 := by
      have := hadd 0 0; simp only [add_zero] at this; linarith
    linarith
  · have := eq_mul_of_add_of_antitone hadd hanti (Real.log l)
    simp only [φ, Real.exp_log hl] at this
    rw [Real.rpow_def_of_pos hl, ← this, Real.exp_log (hg0 l hl)]

end Characterization

section General

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

theorem tendsto_integral_gfun_atTop (P : ProbabilityMeasure ℝ) :
    Tendsto (fun x : ℝ => ∫ y, (1 + y ^ 2) / max (y ^ 2) (x ^ 2) ∂(P : Measure ℝ)) atTop
      (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _y, (0 : ℝ) ∂(P : Measure ℝ) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => gfun one_pos y) ?_ ?_
    ((gfun one_pos).integrable _) (ae_of_all _ fun y => ?_)
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact (gfun hx).continuous.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with x hx
    refine ae_of_all _ fun y => ?_
    have hM : 0 < max (y ^ 2) (1 ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    rw [gfun_apply, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity)
      (le_max_of_le_right (sq_nonneg _)))]
    exact div_le_div_of_nonneg_left (by positivity) hM
      (max_le_max le_rfl (pow_le_pow_left₀ zero_le_one hx 2))
  · have h1 : Tendsto (fun x : ℝ => (1 + y ^ 2) / x ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · exact Eventually.of_forall fun x =>
        div_nonneg (by positivity) (le_max_of_le_left (sq_nonneg _))
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_right _ _)

/-- **Converse of the generalized central limit theorem, symmetric case, with the index
derived** (Feller's criterion, necessity: [Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35]).
Let `μ` be a symmetric probability law on `ℝ`, `aₙ > 0`, and suppose the laws of
`(X₁ + ⋯ + Xₙ) / aₙ` converge weakly to a law `ν ≠ δ₀`. Then there is `0 < α ≤ 2` such that
the truncated second moment `U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α`,
and, if `α < 2`, the two-sided tail `P(|X| > x)` is regularly varying with index `-α`. -/
theorem exists_isRegularlyVarying_of_tendsto (hsymm : μ.map (fun x => -x) = μ)
    (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ} (hnd : (ν : Measure ℝ) ≠ Measure.dirac 0)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α, 0 < α ∧ α ≤ 2 ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      (α < 2 → IsRegularlyVarying (absTail μ) (-α)) := by
  obtain ⟨δ, hδ, hb⟩ := exists_nh_le hsymm hconv
  set B := Real.log 2
  have hB0 : 0 ≤ B := Real.log_nonneg one_le_two
  set ψ : ℝ → ℝ := fun u => (charFun (ν : Measure ℝ) u).re with hψ
  set h : ℝ → ℝ := fun u => -Real.log (ψ u) with hh
  have hψpos : ∀ u, 0 < ψ u := fun u => (tendsto_nh hsymm hconv hb u).1
  have hlim : ∀ u, Tendsto (fun n => nh μ a n u) atTop (𝓝 (h u)) :=
    fun u => (tendsto_nh hsymm hconv hb u).2
  have hBa : ∀ᶠ n in atTop, ∀ u, |nh μ a n u| ≤ B * (|u| / δ + 1) ^ 2 := by
    filter_upwards [eventually_ge_atTop 3] with n hn u
    rw [abs_of_nonneg (nh_nonneg _ _)]
    exact hb n hn u
  have hhnn : ∀ u, 0 ≤ h u := fun u =>
    ge_of_tendsto (hlim u) (Eventually.of_forall fun n => nh_nonneg _ _)
  have hhc : Continuous h :=
    ((Complex.continuous_re.comp continuous_charFun).log fun u => (hψpos u).ne').neg
  have hhb : ∀ u, |h u| ≤ B * (|u| / δ + 1) ^ 2 := by
    intro u
    rw [abs_of_nonneg (hhnn u)]
    exact le_of_tendsto (hlim u) (by
      filter_upwards [hBa] with n hn
      exact (le_abs_self _).trans (hn u))
  have hh0 : h 0 = 0 := by
    simp [hh, hψ, charFun_zero]
  have hheven : ∀ u, h (-u) = h u := fun u =>
    tendsto_nhds_unique (hlim (-u)) (by simpa only [nh_neg] using hlim u)
  -- non-degeneracy gives `h(s₀) > 0` for some `s₀ > 0`
  obtain ⟨s₀, hs₀, hhs₀⟩ : ∃ s₀ > 0, 0 < h s₀ := by
    have : ∃ t, charFun (ν : Measure ℝ) t ≠ 1 := by
      by_contra hc
      apply hnd
      refine Measure.ext_of_charFun (funext fun t => ?_)
      have h1 : charFun (ν : Measure ℝ) t = 1 := by
        by_contra h'
        exact hc ⟨t, h'⟩
      rw [h1, charFun_dirac]
      simp
    obtain ⟨t, ht⟩ := this
    have hlt : ψ t < 1 := by
      have hn1 : ‖charFun (ν : Measure ℝ) t‖ ≤ 1 := norm_charFun_le_one t
      refine lt_of_le_of_ne ((Complex.re_le_norm _).trans hn1) fun heq => ht ?_
      have hsq : ‖charFun (ν : Measure ℝ) t‖ ^ 2 = (charFun (ν : Measure ℝ) t).re ^ 2 +
          (charFun (ν : Measure ℝ) t).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have him : (charFun (ν : Measure ℝ) t).im = 0 := by
        have : ‖charFun (ν : Measure ℝ) t‖ ^ 2 ≤ 1 := by
          have := norm_nonneg (charFun (ν : Measure ℝ) t); nlinarith
        simp only [hψ] at heq
        rw [hsq, heq] at this
        nlinarith [sq_nonneg (charFun (ν : Measure ℝ) t).im]
      exact Complex.ext (by simpa [hψ] using heq) (by simpa using him)
    have hpos : 0 < h t := by
      simp only [hh]
      exact neg_pos.2 (Real.log_neg (hψpos t) hlt)
    have ht0 : t ≠ 0 := by rintro rfl; rw [hh0] at hpos; exact lt_irrefl _ hpos
    refine ⟨|t|, abs_pos.2 ht0, ?_⟩
    rcases le_or_gt 0 t with h0 | h0
    · rwa [abs_of_nonneg h0]
    · rwa [abs_of_neg h0, hheven]
  have hpos : 0 < lap h 0 := lap_pos hB0 hδ hhc hhb hh0 hhnn hs₀ hhs₀
  obtain ⟨P, hP⟩ := exists_charFun_eq_lap hsymm hB0 hδ hBa hlim hpos hhc hhb
  set L : ℝ → ℝ := fun x => lap h 0 * ∫ y, (1 + y ^ 2) / max (y ^ 2) (x ^ 2) ∂(P : Measure ℝ)
  have hlimL : ∀ x, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (L x)) := fun x hx => tendsto_mul_sqRatio hsymm ha hB0 hδ hBa hlim hpos P hP hx
  have hLpos : ∀ x, 0 < x → 0 < L x := fun x hx => mul_pos hpos (integral_gfun_pos P hx)
  have hL1 : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n)) atTop (𝓝 (L 1)) := by
    simpa using hlimL 1 one_pos
  have hTpos : ∀ x, 0 < x → 0 < sqRatio μ x := by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hL1).1 0 (hLpos 1 one_pos)).exists
    have h1 : 0 < sqRatio μ (a n) := by
      by_contra hc
      have : sqRatio μ (a n) = 0 := le_antisymm (not_lt.1 hc) (sqRatio_nonneg _)
      rw [this, mul_zero] at hn
      exact lt_irrefl _ hn
    exact fun x hx => sqRatio_pos_of_pos (ha n) h1 hx
  have hratio : ∀ l, 0 < l → Tendsto (fun x => sqRatio μ (l * x) / sqRatio μ x) atTop
      (𝓝 (L l / L 1)) := fun l hl =>
    tendsto_div_of_tendsto_mul_comp sqRatio_antitoneOn hTpos ha hlimL hLpos hl
  obtain ⟨ρ, hρ0, hρ⟩ := exists_rpow_of_tendsto_div sqRatio_antitoneOn hTpos
    (fun l hl => div_pos (hLpos l hl) (hLpos 1 one_pos)) hratio
  have hLρ : ∀ x, 0 < x → L x = L 1 * x ^ ρ := fun x hx => by
    have := hρ x hx
    rw [div_eq_iff (hLpos 1 one_pos).ne'] at this
    rw [this, mul_comm]
  -- `α = -ρ > 0`: otherwise `L` would be constant, but `L x → 0`
  have hρneg : ρ < 0 := by
    rcases lt_or_eq_of_le hρ0 with hρz | hρz
    · exact hρz
    · exfalso
      have hconst : ∀ x, 0 < x → L x = L 1 := fun x hx => by
        rw [hLρ x hx, hρz]; simp
      have hto : Tendsto L atTop (𝓝 0) := by
        have := (tendsto_integral_gfun_atTop P).const_mul (lap h 0)
        simpa [L] using this
      have : Tendsto L atTop (𝓝 (L 1)) := tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop 0] with x hx
        exact (hconst x hx).symm)
      exact (hLpos 1 one_pos).ne' (tendsto_nhds_unique this hto)
  set α := -ρ with hα
  have hα0 : 0 < α := by linarith
  have hTRV : IsRegularlyVarying (sqRatio μ) (-α) := by
    rw [hα, neg_neg]
    refine ⟨(eventually_gt_atTop 0).mono hTpos, fun l hl => ?_⟩
    rw [← hρ l hl]
    exact hratio l hl
  have hZ : IsRegularlyVarying (minSqMoment μ) (2 - α) := by
    have := (IsRegularlyVarying.rpow_id 2).mul hTRV
    rw [← sub_eq_add_neg] at this
    refine this.congr ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqRatio_eq_div hx.ne', Real.rpow_two]
    field_simp
  have hα2 : α ≤ 2 := by
    by_contra hc
    replace hc : 2 < α := not_le.1 hc
    have h2 := hZ.2 2 two_pos
    have hle : (1 : ℝ) ≤ 2 ^ (2 - α) := ge_of_tendsto h2 (by
      filter_upwards [hZ.1, eventually_gt_atTop 0] with x hx hx0
      rw [le_div_iff₀ hx, one_mul]
      exact minSqMoment_mono hx0.le (by linarith))
    have : (2 : ℝ) ^ (2 - α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    linarith
  refine ⟨α, hα0, hα2, isRegularlyVarying_truncSecondMoment_of_minSqMoment (by linarith) hZ,
    fun hlt => ?_⟩
  have hG := isRegularlyVarying_absTail_of_minSqMoment (by linarith) hZ
  rwa [show 2 - α - 2 = -α by ring] at hG

end General

end GCLTConverse

end ExtremeValueTheory
