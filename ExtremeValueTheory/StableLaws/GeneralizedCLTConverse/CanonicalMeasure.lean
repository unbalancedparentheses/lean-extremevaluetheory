/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT
import ExtremeValueTheory.StableLaws.LevyContinuity
import ExtremeValueTheory.RegularVariation.KaramataConverse
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverse.Tauberian
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverse.CharFun

/-!
# Converse GCLT: canonical measures

Steps 3 and 4 of the converse of the generalized central limit theorem (symmetric case).
Using `1 / (1 + y²) = ∫₀^∞ e^{-s} cos (s y) ds`, the finite measures
`Λₙ(dy) = n y² / (1 + y²) P(X / aₙ ∈ dy)` (Feller's canonical measures) have characteristic
functions given by the functional `lap` of `hₙ`; these converge, and Lévy's continuity theorem
turns this into the scaling limit `n T(aₙ x) → L(x) > 0` of `T(x) = E[min (1, X² / x²)]`
(`sqRatio`).

## Main definitions

* `GCLTConverse.kDensity`: The density `y² / (1 + y²)` of the measures `Λₙ`.
* `GCLTConverse.kMeasure`: `Λ = (y² / (1 + y²)) ρ(dy)`.
* `GCLTConverse.lap`: The transform `λ_g(t) = ∫₀^∞ e^{-s} ((g(t + s) + g(t - s)) / 2 - g(t)) ds`.
* `GCLTConverse.lamMeasure`: `Λₙ`, the image of `μ` under `x ↦ x / aₙ` weighted by `y² / (1 + y²)`.
* `GCLTConverse.sqRatio`: `T(x) = E[X² / max (X², x²)] = E[min (1, X² / x²)]`.
* `GCLTConverse.gfun`: The bounded continuous test function `(1 + y²) / max (y², x²)`.
* `GCLTConverse.lamNorm`: The normalized measures `Λₙ / Λₙ(ℝ)`.

## Main results

* `GCLTConverse.charFun_kMeasure`: **Characteristic function of `Λ`.** For a finite measure `ρ`,
  `φ_Λ(t) = φ_ρ(t) - ∫₀^∞ e^{-s} (φ_ρ(t + s) + φ_ρ(t - s)) / 2 ds`.
* `GCLTConverse.tendsto_lap`: Dominated convergence for `λ`.
* `GCLTConverse.charFun_lamMeasure`: `φ_{Λₙ}(t) = λ_{hₙ}(t) / n`.
* `GCLTConverse.tendsto_mul_sqRatio`: **The pipeline.** If `hₙ → h` with quadratic bounds and
  `λ_h(0) > 0`, and `P` is a probability measure with characteristic function `λ_h / λ_h(0)`, then
  `n T(aₙ x) → λ_h(0) ∫ (1 + y²) / max (y², x²) dP(y)` for every `x > 0`.
* `GCLTConverse.exists_charFun_eq_lap`: Existence of the limit `P` of `Λₙ / Λₙ(ℝ)` (Lévy's
  continuity theorem).

This file is part of the proof in `ExtremeValueTheory.StableLaws.GeneralizedCLTConverse`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), §VIII.8 and §XVII.5 [Feller].
* B. V. Gnedenko and A. N. Kolmogorov, *Limit Distributions for Sums of Independent Random
  Variables*, Addison-Wesley (1954), §35 [GK].
* N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge (1987) [BGT].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace GCLTConverse

open Subexp

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

end GCLTConverse

end ExtremeValueTheory
