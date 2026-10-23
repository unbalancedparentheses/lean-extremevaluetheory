/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.StableIndex
import ExtremeValueTheory.StableLaws.GaussianDomain.Lindeberg

/-!
# The Gaussian case of the converse generalized CLT

When the converse index is `2`, the symmetrized scaling limit
`n E[min (1, (X - X')² / (aₙ x)²)] → K x⁻²` yields the Lindeberg conditions with `σ² = K / 2`, so
every non-degenerate limit of normalized sums is Gaussian. Consequently every such limit is
stable (of index `α < 2`, or Gaussian), and the stable laws of index `2` are exactly the
non-degenerate Gaussian laws.

## Main results

* `lindeberg_of_tendsto_mul_sqRatio_two`: **The Lindeberg conditions from the converse with index
  `2`.** If `n E[min (1, (X - X')² / (aₙ x)²)] → K x⁻²` for every `x > 0`, then `aₙ → ∞`, `n P(|X| >
  ε aₙ) → 0` for every `ε > 0`, and `n Var (clip (X / aₙ)) → K / 2`.
* `exists_eq_gaussianReal_of_tendsto_mul_sqRatio_two`: **The Gaussian case of the converse GCLT.**
  If `(Sₙ - bₙ) / aₙ → ν` and the symmetrized scaling limit has index `2`, `n E[min (1, (X - X')² /
  (aₙ x)²)] → K x⁻²`, then `ν` is the Gaussian law `N(m, K / 2)` for some `m`.
* `exists_isStableIndex_or_gaussian_of_tendsto`: **Dichotomy for limits of normalized sums.** If
  `(Sₙ - bₙ) / aₙ → ν`, `ν` not a Dirac mass, then either the converse index is `α < 2` and `ν` is
  stable with index `α`, or the index is `2`, `U(x) = E[X² 1{|X| ≤ x}]` is slowly varying and `ν` is
  Gaussian.
* `isStable_of_tendsto`: **Every non-degenerate limit of normalized sums is stable** ([Feller, Vol.
  II, §VI.1, Theorem 1 and §XVII.5], [GK, §33]).
* `exists_eq_gaussianReal_of_isRegularlyVarying_truncSecondMoment`: **The Gaussian limit in the
  converse** ([Feller, Vol. II, §IX.8 and §XVII.5], [GK, §35]).
* `IsStableIndex.exists_eq_gaussianReal`: **Stable laws of index `2` are Gaussian.**
* `isStableIndex_two_iff`: `IsStableIndex 2 ν` iff `ν` is a non-degenerate Gaussian law.

This file is part of the proof in `ExtremeValueTheory.StableLaws.GaussianDomain`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), §IX.8 and §XVII.5 [Feller].
* B. V. Gnedenko and A. N. Kolmogorov, *Limit Distributions for Sums of Independent Random
  Variables*, Addison-Wesley (1954), §35 [GK].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

open Subexp GCLT StableIntegral GCLTConverse

section Necessity

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

/-- `3 P(|Z| > 2y) ≤ 4 E[min (1, Z² / (2y)²)] - E[min (1, Z² / y²)]`. -/
theorem absTail_two_mul_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {y : ℝ} (hy : 0 < y) :
    3 * absTail ρ (2 * y) ≤ 4 * sqRatio ρ (2 * y) - sqRatio ρ y := by
  rw [sqRatio_eq_integral_min' (μ := ρ) (by positivity : (2 * y) ≠ 0),
    sqRatio_eq_integral_min' (μ := ρ) hy.ne', ← integral_indicator_one, ← integral_const_mul,
    ← integral_const_mul, ← integral_sub]
  · refine integral_mono ((integrable_indicator_one _).const_mul _)
      (((integrable_min_one_sq_mul ρ _).const_mul _).sub (integrable_min_one_sq_mul ρ _))
      fun z => ?_
    by_cases hz : 2 * y < |z|
    · rw [Set.indicator_of_mem (show z ∈ {x : ℝ | 2 * y < |x|} from hz)]
      have h1 : 1 ≤ ((2 * y)⁻¹ * z) ^ 2 := by
        rw [mul_pow, ← sq_abs z, inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
        nlinarith [abs_nonneg z]
      have h2 : 1 ≤ (y⁻¹ * z) ^ 2 := by
        rw [mul_pow, ← sq_abs z, inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
        nlinarith [abs_nonneg z]
      rw [min_eq_left h1, min_eq_left h2]; norm_num
    · rw [Set.indicator_of_notMem (show z ∉ {x : ℝ | 2 * y < |x|} from hz), mul_zero]
      have h1 : ((2 * y)⁻¹ * z) ^ 2 ≤ 1 := by
        rw [mul_pow, ← sq_abs z, inv_pow, inv_mul_eq_div, div_le_one (by positivity)]
        have := not_lt.1 hz
        nlinarith [abs_nonneg z]
      rw [min_eq_right h1]
      have : 4 * ((2 * y)⁻¹ * z) ^ 2 = (y⁻¹ * z) ^ 2 := by field_simp; ring
      rw [this]
      linarith [min_le_right 1 ((y⁻¹ * z) ^ 2)]
  all_goals first
    | exact (integrable_min_one_sq_mul ρ _).const_mul _
    | exact integrable_min_one_sq_mul ρ _

/-- The symmetrized scaling limit with index `2` makes `n P(|X - X'| > aₙ x) → 0`. -/
theorem tendsto_mul_absTail_symmLaw_of_two {K : ℝ}
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
      (𝓝 (K * x ^ (-(2 : ℝ))))) (ha : ∀ n, 0 < a n) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (n : ℝ) * absTail (symmLaw μ) (a n * x)) atTop (𝓝 0) := by
  have hup := (((hL x hx).const_mul 4).sub (hL (x / 2) (by positivity))).div_const 3
  have he : (4 * (K * x ^ (-(2 : ℝ))) - K * (x / 2) ^ (-(2 : ℝ))) / 3 = 0 := by
    rw [Real.rpow_neg hx.le, Real.rpow_neg (by positivity), Real.rpow_two, Real.rpow_two]
    field_simp; ring
  rw [he] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) fun n => ?_
  have h := absTail_two_mul_le (symmLaw μ) (mul_pos (ha n) (half_pos hx))
  rw [show 2 * (a n * (x / 2)) = a n * x by ring] at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only
  nlinarith [mul_le_mul_of_nonneg_left h hn]

/-- The variance of `clip (X / a)` through the symmetrization:
`|2 Var (clip (X / a)) - 4 E[min (1, (X - X')² / (2a)²)]| ≤ 8 P(|X| > a)`. -/
theorem abs_two_mul_clipVar_sub_le (n : ℕ) (ha : 0 < a n) :
    |2 * clipVar μ a n - 4 * sqRatio (symmLaw μ) (a n * 2)| ≤ 8 * absTail μ (a n * 1) := by
  set f : ℝ → ℝ := fun x => clip ((a n)⁻¹ * x) with hfdef
  set τ := ctr μ a n
  have hτf : ∫ x, f x ∂μ = τ := rfl
  have hfc : Continuous f := continuous_clip.comp (continuous_const.mul continuous_id)
  have hfb : ∀ x, |f x| ≤ 1 := fun x => abs_clip_le _
  have hfi : Integrable f μ := integrable_clip n
  have hf2 : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hfc.pow 2).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]; nlinarith [hfb x, abs_nonneg (f x)])
  have hP : ∀ (g : ℝ × ℝ → ℝ), Continuous g → (∀ p, |g p| ≤ 4) → Integrable g (μ.prod μ) :=
    fun g hg hb => Integrable.of_bound hg.aestronglyMeasurable 4
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hb p)
  have hd2 : ∀ p : ℝ × ℝ, |f p.1 - f p.2| ≤ 2 := fun p =>
    (abs_sub _ _).trans (by linarith [hfb p.1, hfb p.2])
  have hd4 : ∀ p : ℝ × ℝ, (f p.1 - f p.2) ^ 2 ≤ 4 := fun p => by
    rw [← sq_abs]; nlinarith [abs_nonneg (f p.1 - f p.2), hd2 p]
  -- `∫∫ (f x - f y)² = 2 Var f`
  have hvar : ∫ p : ℝ × ℝ, (f p.1 - f p.2) ^ 2 ∂(μ.prod μ) = 2 * clipVar μ a n := by
    have e : ∀ p : ℝ × ℝ, (f p.1 - f p.2) ^ 2 =
        f p.1 ^ 2 + f p.2 ^ 2 - 2 * (f p.1 * f p.2) := by
      intro p; ring
    have hi1 : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2) (μ.prod μ) := hf2.comp_fst μ
    have hi2 : Integrable (fun p : ℝ × ℝ => f p.2 ^ 2) (μ.prod μ) := hf2.comp_snd μ
    have hi3 : Integrable (fun p : ℝ × ℝ => f p.1 * f p.2) (μ.prod μ) := hfi.mul_prod hfi
    have hi12 : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2 + f p.2 ^ 2) (μ.prod μ) := hi1.add hi2
    have hi3' : Integrable (fun p : ℝ × ℝ => 2 * (f p.1 * f p.2)) (μ.prod μ) := hi3.const_mul 2
    simp_rw [e]
    rw [integral_sub hi12 hi3', integral_add hi1 hi2, integral_const_mul,
      integral_fun_fst (fun x => f x ^ 2), integral_fun_snd (fun x => f x ^ 2),
      integral_prod_mul f f]
    simp only [probReal_univ, one_smul]
    have hc : clipVar μ a n = ∫ x, f x ^ 2 ∂μ - τ ^ 2 := by
      have e2 : ∀ x, (f x - τ) ^ 2 = f x ^ 2 - 2 * τ * f x + τ ^ 2 := fun x => by ring
      have hA : Integrable (fun x => f x ^ 2 - 2 * τ * f x) μ := hf2.sub (hfi.const_mul _)
      have hcv : clipVar μ a n = ∫ x, (f x - τ) ^ 2 ∂μ := rfl
      rw [hcv]
      simp_rw [e2]
      rw [integral_add hA (integrable_const _), integral_sub hf2 (hfi.const_mul _),
        integral_const_mul, integral_const, probReal_univ, one_smul, hτf]
      ring
    rw [hc, hτf]; ring
  -- `E min (1, (Z / 2a)²)` as an integral over the product
  have hS : sqRatio (symmLaw μ) (a n * 2) =
      ∫ p : ℝ × ℝ, min 1 (((a n * 2)⁻¹ * (p.1 - p.2)) ^ 2) ∂(μ.prod μ) := by
    rw [sqRatio_eq_integral_min' (by have := ha; positivity), symmLaw,
      integral_map measurable_fst_sub_snd.aemeasurable (by fun_prop)]
  set I : ℝ → ℝ := {y : ℝ | a n * 1 < |y|}.indicator (fun _ => (1 : ℝ)) with hIdef
  have hI0 : ∀ y, 0 ≤ I y := fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hIi : Integrable I μ := integrable_indicator_one _
  have hA : ∫ p : ℝ × ℝ, (I p.1 + I p.2) ∂(μ.prod μ) = 2 * absTail μ (a n * 1) := by
    rw [integral_add (hIi.comp_fst μ) (hIi.comp_snd μ), integral_fun_fst I, integral_fun_snd I]
    simp only [probReal_univ, one_smul, hIdef, integral_indicator_one]
    ring
  have hg1 : Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2) (μ.prod μ) :=
    hP _ (by fun_prop) fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact hd4 p
  have hg2 : Integrable (fun p : ℝ × ℝ => 4 * min 1 (((a n * 2)⁻¹ * (p.1 - p.2)) ^ 2))
      (μ.prod μ) :=
    hP _ (by fun_prop) fun p => by
      rw [abs_of_nonneg (by positivity)]
      linarith [min_le_left 1 (((a n * 2)⁻¹ * (p.1 - p.2)) ^ 2)]
  have hg3 : Integrable (fun p : ℝ × ℝ => I p.1 + I p.2) (μ.prod μ) :=
    (hIi.comp_fst μ).add (hIi.comp_snd μ)
  have hg12 : Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2 -
      4 * min 1 (((a n * 2)⁻¹ * (p.1 - p.2)) ^ 2)) (μ.prod μ) := hg1.sub hg2
  rw [← hvar, hS, ← integral_const_mul, ← integral_sub hg1 hg2]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [show 8 * absTail μ (a n * 1) = 4 * (2 * absTail μ (a n * 1)) by ring, ← hA,
    ← integral_const_mul]
  refine integral_mono hg12.abs (hg3.const_mul 4) fun p => ?_
  have h3 := min_le_left 1 (((a n * 2)⁻¹ * (p.1 - p.2)) ^ 2)
  have h4 : 0 ≤ min 1 (((a n * 2)⁻¹ * (p.1 - p.2)) ^ 2) := le_min zero_le_one (sq_nonneg _)
  have h2 := hd4 p
  have h0 := sq_nonneg (f p.1 - f p.2)
  by_cases hx : a n * 1 < |p.1|
  · have : I p.1 = 1 := Set.indicator_of_mem (show p.1 ∈ {y : ℝ | a n * 1 < |y|} from hx) _
    have := hI0 p.2
    rw [abs_le]; constructor <;> nlinarith
  · by_cases hy : a n * 1 < |p.2|
    · have : I p.2 = 1 := Set.indicator_of_mem (show p.2 ∈ {y : ℝ | a n * 1 < |y|} from hy) _
      have := hI0 p.1
      rw [abs_le]; constructor <;> nlinarith
    · have e1 : I p.1 = 0 :=
        Set.indicator_of_notMem (show p.1 ∉ {y : ℝ | a n * 1 < |y|} from hx) _
      have e2 : I p.2 = 0 :=
        Set.indicator_of_notMem (show p.2 ∉ {y : ℝ | a n * 1 < |y|} from hy) _
      rw [e1, e2]
      have hx' : |(a n)⁻¹ * p.1| ≤ 1 := by
        rw [abs_mul, abs_inv, abs_of_pos ha, inv_mul_le_iff₀ ha]; linarith [not_lt.1 hx]
      have hy' : |(a n)⁻¹ * p.2| ≤ 1 := by
        rw [abs_mul, abs_inv, abs_of_pos ha, inv_mul_le_iff₀ ha]; linarith [not_lt.1 hy]
      have hf1 : f p.1 = (a n)⁻¹ * p.1 := clip_eq_of_abs_le hx'
      have hf2' : f p.2 = (a n)⁻¹ * p.2 := clip_eq_of_abs_le hy'
      have e : (a n * 2)⁻¹ * (p.1 - p.2) = ((a n)⁻¹ * p.1 - (a n)⁻¹ * p.2) / 2 := by
        field_simp
      have hm : ((a n * 2)⁻¹ * (p.1 - p.2)) ^ 2 ≤ 1 := by
        have : |(a n * 2)⁻¹ * (p.1 - p.2)| ≤ 1 := by
          rw [e, abs_div, abs_two, div_le_one two_pos]
          exact (abs_sub _ _).trans (by linarith)
        rw [← sq_abs]; nlinarith [abs_nonneg ((a n * 2)⁻¹ * (p.1 - p.2))]
      simp only
      rw [min_eq_right hm, hf1, hf2', e]
      have : ((a n)⁻¹ * p.1 - (a n)⁻¹ * p.2) ^ 2 - 4 * (((a n)⁻¹ * p.1 - (a n)⁻¹ * p.2) / 2) ^ 2
          = 0 := by ring
      rw [this, abs_zero]; norm_num

/-- **The Lindeberg conditions from the converse with index `2`.** If
`n E[min (1, (X - X')² / (aₙ x)²)] → K x⁻²` for every `x > 0`, then `aₙ → ∞`,
`n P(|X| > ε aₙ) → 0` for every `ε > 0`, and `n Var (clip (X / aₙ)) → K / 2`. -/
theorem lindeberg_of_tendsto_mul_sqRatio_two (ha : ∀ n, 0 < a n) {K : ℝ} (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
      (𝓝 (K * x ^ (-(2 : ℝ))))) :
    Tendsto a atTop atTop ∧
      (∀ ε > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n * ε)) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * clipVar μ a n) atTop (𝓝 (K / 2)) := by
  have hL1 : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n)) atTop (𝓝 K) := by
    simpa using hL 1 one_pos
  have hTpos : ∀ x, 0 < x → 0 < sqRatio (symmLaw μ) x := by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hL1).1 0 hK).exists
    have h1 : 0 < sqRatio (symmLaw μ) (a n) := by
      by_contra hc
      have : sqRatio (symmLaw μ) (a n) = 0 := le_antisymm (not_lt.1 hc) (sqRatio_nonneg _)
      rw [this, mul_zero] at hn
      exact lt_irrefl _ hn
    exact fun x hx => sqRatio_pos_of_pos (ha n) h1 hx
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_of_tendsto_mul_comp (T := sqRatio (symmLaw μ)) (L := fun _ => K)
      sqRatio_antitoneOn hTpos ha hL1
  -- tails of `X` from tails of `X - X'`
  obtain ⟨u₀, hu₀⟩ := (eventually_atTop.1 ((tendsto_order.1 (tendsto_absTail_zero (μ := μ))).2
    (1 / 2) (by norm_num)))
  set u := max u₀ 0
  have hu : absTail μ u ≤ 1 / 2 := (hu₀ u (le_max_left _ _)).le
  have hcmp : ∀ s, 0 ≤ s → absTail μ (s + u) ≤ absTail (symmLaw μ) s := by
    intro s hs
    have h := two_mul_absTail_mul_le_absTail_symmLaw (μ := μ) (u := u) hs
    have h0 : 0 ≤ absTail μ (s + u) := measureReal_nonneg
    nlinarith
  have hT : ∀ ε > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n * ε)) atTop (𝓝 0) := by
    intro ε hε
    have h := tendsto_mul_absTail_symmLaw_of_two hL ha (half_pos hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) ?_
    filter_upwards [hatop.eventually_ge_atTop (2 * u / ε)] with n hn
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hle : a n * (ε / 2) + u ≤ a n * ε := by
      rw [div_le_iff₀ hε] at hn; nlinarith
    exact (absTail_antitone hle).trans (hcmp _ (mul_pos (ha n) (half_pos hε)).le)
  refine ⟨hatop, hT, ?_⟩
  -- the variance
  have h4 : Tendsto (fun n : ℕ => 4 * ((n : ℝ) * sqRatio (symmLaw μ) (a n * 2))) atTop
      (𝓝 K) := by
    have := (hL 2 two_pos).const_mul 4
    convert this using 2
    rw [Real.rpow_neg two_pos.le, Real.rpow_two]; ring
  have h8 := (hT 1 one_pos).const_mul 8
  rw [mul_zero] at h8
  have hdiff : Tendsto (fun n : ℕ => 2 * ((n : ℝ) * clipVar μ a n) -
      4 * ((n : ℝ) * sqRatio (symmLaw μ) (a n * 2))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) h8
    rw [Real.norm_eq_abs]
    have := abs_two_mul_clipVar_sub_le (μ := μ) n (ha n)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc |2 * ((n : ℝ) * clipVar μ a n) - 4 * ((n : ℝ) * sqRatio (symmLaw μ) (a n * 2))|
        = |(n : ℝ) * (2 * clipVar μ a n - 4 * sqRatio (symmLaw μ) (a n * 2))| := by ring_nf
      _ = (n : ℝ) * |2 * clipVar μ a n - 4 * sqRatio (symmLaw μ) (a n * 2)| := by
          rw [abs_mul, abs_of_nonneg hn]
      _ ≤ (n : ℝ) * (8 * absTail μ (a n * 1)) := mul_le_mul_of_nonneg_left this hn
      _ = 8 * ((n : ℝ) * absTail μ (a n * 1)) := by ring
  have := (hdiff.add h4).div_const 2
  rw [zero_add] at this
  refine this.congr fun n => ?_
  ring

end Necessity

section Identification

theorem IsRegularlyVarying.index_eq {f : ℝ → ℝ} {ρ σ : ℝ} (h1 : IsRegularlyVarying f ρ)
    (h2 : IsRegularlyVarying f σ) : ρ = σ := by
  have h := tendsto_nhds_unique (h1.2 2 two_pos) (h2.2 2 two_pos)
  have hl := congrArg Real.log h
  rw [Real.log_rpow two_pos, Real.log_rpow two_pos] at hl
  exact mul_right_cancel₀ (Real.log_pos one_lt_two).ne' hl

theorem norm_charFun_gaussianReal (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    ‖charFun (gaussianReal m v) t‖ = Real.exp (-((v : ℝ) / 2 * |t| ^ (2 : ℝ))) := by
  rw [charFun_gaussianReal, Complex.norm_exp, Real.rpow_two, sq_abs]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.div_re]
  norm_num
  rw [show ((t : ℂ) ^ 2) = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  ring

/-- Non-degenerate Gaussian laws are stable with index `2`. -/
theorem isStableIndex_two_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    IsStableIndex 2 (gaussianReal m v) :=
  (isStable_gaussianReal m hv).isStableIndex_of_norm_charFun two_pos
    (div_pos (by positivity) two_pos) (norm_charFun_gaussianReal m v)

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

/-- **The Gaussian case of the converse GCLT.** If `(Sₙ - bₙ) / aₙ → ν` and the symmetrized
scaling limit has index `2`, `n E[min (1, (X - X')² / (aₙ x)²)] → K x⁻²`, then `ν` is the
Gaussian law `N(m, K / 2)` for some `m`. -/
theorem exists_eq_gaussianReal_of_tendsto_mul_sqRatio_two (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    {K : ℝ} (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
      (𝓝 (K * x ^ (-(2 : ℝ))))) :
    ∃ m : ℝ, (ν : Measure ℝ) = gaussianReal m (K / 2).toNNReal := by
  obtain ⟨hatop, hT, hV⟩ := lindeberg_of_tendsto_mul_sqRatio_two ha hK hL
  exact exists_eq_gaussianReal_of_lindeberg ha hatop hT hV hconv

/-- **Dichotomy for limits of normalized sums.** If `(Sₙ - bₙ) / aₙ → ν`, `ν` not a Dirac mass,
then either the converse index is `α < 2` and `ν` is stable with index `α`, or the index is `2`,
`U(x) = E[X² 1{|X| ≤ x}]` is slowly varying and `ν` is Gaussian. -/
theorem exists_isStableIndex_or_gaussian_of_tendsto (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ} (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    (∃ α, 0 < α ∧ α < 2 ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
        IsStableIndex α ν) ∨
      (IsRegularlyVarying (truncSecondMoment μ) 0 ∧
        ∃ m : ℝ, ∃ v : ℝ≥0, v ≠ 0 ∧ (ν : Measure ℝ) = gaussianReal m v) := by
  obtain ⟨α, hα0, hα2, K, hK, hL⟩ := exists_tendsto_mul_sqRatio_symmLaw ha hnd hconv
  have hZs := isRegularlyVarying_minSqMoment_of_tendsto_mul_sqRatio ha hK hL
  rcases lt_or_eq_of_le hα2 with hlt | rfl
  · left
    have hGs := isRegularlyVarying_absTail_of_minSqMoment (by linarith) hZs
    rw [show 2 - α - 2 = -α by ring] at hGs
    have hG := isRegularlyVarying_absTail_of_symmLaw hGs
    refine ⟨α, hα0, hlt, isRegularlyVarying_truncSecondMoment_of_absTail hα0 hlt hG, ?_⟩
    obtain ⟨-, B, hB0, -, p, -, -, -, m, hm1, hm2⟩ :=
      identify_of_tendsto_mul_sqRatio ha hconv hα0 hlt hK hL
    rcases eq_or_ne α 1 with h1 | h1
    · subst h1
      exact ((hm2 rfl).isStableIndex
        (mul_pos hB0 (stableConst_pos one_pos (by norm_num)))).of_map_add_const
    · exact ((hm1 h1).isStableIndex hα0 (mul_pos hB0 (stableConst_pos hα0 hlt))).of_map_add_const
  · right
    rw [sub_self] at hZs
    refine ⟨isRegularlyVarying_truncSecondMoment_of_minSqMoment (by norm_num)
      (isRegularlyVarying_minSqMoment_of_symmLaw hZs), ?_⟩
    obtain ⟨m, hm⟩ := exists_eq_gaussianReal_of_tendsto_mul_sqRatio_two ha hconv hK hL
    refine ⟨m, (K / 2).toNNReal, ?_, hm⟩
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    positivity

/-- **Every non-degenerate limit of normalized sums is stable** ([Feller, Vol. II, §VI.1,
Theorem 1 and §XVII.5], [GK, §33]). -/
theorem isStable_of_tendsto (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ} (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    IsStable (ν : Measure ℝ) := by
  rcases exists_isStableIndex_or_gaussian_of_tendsto ha hnd hconv with
    ⟨α, -, -, -, h⟩ | ⟨-, m, v, hv, h⟩
  · exact h.1
  · rw [h]; exact isStable_gaussianReal m hv

/-- **The Gaussian limit in the converse** ([Feller, Vol. II, §IX.8 and §XVII.5],
[GK, §35]). If `(Sₙ - bₙ) / aₙ → ν`, `ν` not a Dirac mass, and the truncated second moment
`U(x) = E[X² 1{|X| ≤ x}]` is slowly varying (the converse index is `2`), then `ν` is a
non-degenerate Gaussian law. -/
theorem exists_eq_gaussianReal_of_isRegularlyVarying_truncSecondMoment (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ} (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    (hU : IsRegularlyVarying (truncSecondMoment μ) 0) :
    ∃ m : ℝ, ∃ v : ℝ≥0, v ≠ 0 ∧ (ν : Measure ℝ) = gaussianReal m v := by
  rcases exists_isStableIndex_or_gaussian_of_tendsto ha hnd hconv with
    ⟨α, -, hlt, hU', -⟩ | ⟨-, h⟩
  · have := hU'.index_eq hU
    linarith
  · exact h

/-- **Stable laws of index `2` are Gaussian.** -/
theorem IsStableIndex.exists_eq_gaussianReal {ν : Measure ℝ} (h : IsStableIndex 2 ν) :
    ∃ m : ℝ, ∃ v : ℝ≥0, v ≠ 0 ∧ ν = gaussianReal m v := by
  have := h.1.isProbabilityMeasure
  obtain ⟨a, b, ha, hconv⟩ := h.1.exists_tendsto_self
  rcases exists_isStableIndex_or_gaussian_of_tendsto (μ := ν) (ν := ⟨ν, inferInstance⟩) ha
      h.1.ne_dirac hconv with
    ⟨α, -, hlt, -, hα⟩ | ⟨-, hg⟩
  · have := hα.index_eq h
    linarith
  · exact hg

/-- `IsStableIndex 2 ν` iff `ν` is a non-degenerate Gaussian law. -/
theorem isStableIndex_two_iff {ν : Measure ℝ} :
    IsStableIndex 2 ν ↔ ∃ m : ℝ, ∃ v : ℝ≥0, v ≠ 0 ∧ ν = gaussianReal m v :=
  ⟨fun h => h.exists_eq_gaussianReal, fun ⟨m, _, hv, h⟩ => h ▸ isStableIndex_two_gaussianReal m hv⟩

end Identification

end ExtremeValueTheory
