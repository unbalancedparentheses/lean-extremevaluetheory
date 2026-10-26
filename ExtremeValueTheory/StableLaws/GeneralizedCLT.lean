/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.DomainOfAttraction
import Mathlib.Basic.Real.Sign
import ExtremeValueTheory.StableLaws.GeneralizedCLT.CharFun

/-!
# The generalized central limit theorem for asymmetric tails

Let `X₁, X₂, …` be i.i.d. with law `μ` whose two-sided tail `G(x) = P(|X| > x)` is regularly
varying with index `-α`, `0 < α < 2`, satisfying the *tail balance condition*
`P(X > x) / G(x) → p` (so that `P(X < -x) / G(x) → q = 1 - p`), and let `aₙ > 0` with
`n G(aₙ) → 1`. Then ([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2],
[EKM, Theorem 2.2.8], sufficiency direction):

* for `0 < α < 1`, `(X₁ + ⋯ + Xₙ) / aₙ` converges in law;
* for `1 < α < 2`, `(X₁ + ⋯ + Xₙ - n E X) / aₙ` converges in law;

and in both cases the limit is the `α`-stable law with characteristic function
`exp (-C_α |t|^α + i (p - q) E_α sign(t) |t|^α)`, where `C_α = stableConst α` and `E_α` is
`stableSkewConst α`. Classically `C_α = Γ(1 - α) cos (π α / 2)` and
`E_α = Γ(1 - α) sin (π α / 2) = C_α tan (π α / 2)`, so the limit is
`exp (-C_α |t|^α (1 - i β sign(t) tan (π α / 2)))` with `β = p - q` ([ST, (1.1.6)]); we keep the
constants as the explicit integrals here, and prove these Gamma-function closed forms (and the
textbook restatements of the theorems) in `StableLaws/Constants.lean`.

The case `α = 1` (centering `n E[X 1{|X| ≤ aₙ}]`, logarithmic term in the exponent) is in
`ExtremeValueTheory.StableLaws.GeneralizedCLTOne`.

## Main definitions

* `stableExponent α c e t = -c |t|^α + i e sign(t) |t|^α`.
* `HasStableCharFun α c e μ`: `μ` is a probability measure with characteristic function
  `exp (stableExponent α c e ·)`.
* `StableIntegral.stableSkewConst α`: `α ∫₀^∞ sin u · u^(-α-1) du` (`α < 1`) or
  `-∫₀^∞ (1 - cos u) u^(-α) du` (`α > 1`).

## Main results

* `tendsto_map_convPow_of_isRegularlyVarying_of_lt_one`: the GCLT for `0 < α < 1`.
* `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt`: the GCLT for `1 < α < 2`,
  centered by the mean (`GCLT.integrable_id_of_isRegularlyVarying` shows the mean exists).
* `HasStableCharFun.isStrictlyStable`, `HasStableCharFun.isStable`: the limit laws are
  (strictly) stable, linking the domain-of-attraction theorem with `IsStable`.
* `HasStableCharFun.iff_isSymmStable`: the case `e = 0` is `IsSymmStable`.

## Proof outline

`n (φ(t / aₙ) - 1 - i t bₙ / (n aₙ)) = -n ∫ (1 - cos) + i n ∫ (sin - centering)`. The cosine part
is `GCLT.tendsto_mul_integral_one_sub_cos`. The sine part is split, the integrand being odd, into
the contributions of the right tail of `μ` and of the right tail of `law (-X)`
(`GCLT.integral_odd_eq_sub`). For a right tail `R(y) = P(X > y)` with `n R(aₙ u) → c u^(-α)`:

* `α < 1`: a truncated one-sided layer-cake formula
  `∫ sin (t min (x⁺ / a, M)) dμ = ∫₀^M t cos (t u) R(a u) du`, dominated convergence with Potter
  bounds, and the integration by parts
  `∫₀^M t cos (t u) u^(-α) du = sin (t M) M^(-α) + α ∫₀^M sin (t u) u^(-α-1) du`;
* `1 < α < 2`: the untruncated formula
  `∫ (sin (t x⁺ / a) - t x⁺ / a) dμ = -∫₀^∞ t (1 - cos (t u)) R(a u) du` (using `E|X| < ∞`)
  and dominated convergence on `(0, ∞)`.

Finally `(z e^{-i cₙ})ⁿ → e^ψ` when `n (zₙ - 1 - i cₙ) → ψ` and `n cₙ² → 0` (here
`cₙ = t E X / aₙ`, and `n / aₙ² → 0` because `x² G(x) → ∞`), and Lévy's continuity theorem
produces the limit law.

## File layout

This file holds the final part of the development and imports the others:

* `ExtremeValueTheory.StableLaws.GeneralizedCLT.StableIntegral`: the integrals behind the skewness
  constant `stableSkewConst`.
* `ExtremeValueTheory.StableLaws.GeneralizedCLT.CharFun`: layer-cake formulas and the asymptotics of
  the sine part of `n (φ(t / aₙ) - 1)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

section StableExponent

open StableIntegral

/-- The exponent `ψ(t) = -c |t|^α + i e sign(t) |t|^α` of an `α`-stable characteristic function
(the `α ≠ 1` parametrization of [ST, Definition 1.1.6]: `c = σ^α`, `e = c β tan (π α / 2)`). -/
noncomputable def stableExponent (α c e t : ℝ) : ℂ :=
  ((-(c * |t| ^ α) : ℝ) : ℂ) + ((e * Real.sign t * |t| ^ α : ℝ) : ℂ) * Complex.I

/-- `HasStableCharFun α c e μ`: `μ` is a probability measure with characteristic function
`t ↦ exp (-c |t|^α + i e sign(t) |t|^α)`. For `0 < α < 2`, `α ≠ 1`, `c > 0` these are the
`α`-stable laws `S_α(σ, β, 0)` with `σ^α = c`, `β = e / (c tan (π α / 2))` ([ST, (1.1.6)],
[Feller, §XVII.3–4]). -/
def HasStableCharFun (α c e : ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t, charFun μ t = Complex.exp (stableExponent α c e t)

variable {α c e : ℝ}

theorem stableExponent_zero (hα0 : 0 < α) : stableExponent α c e 0 = 0 := by
  simp [stableExponent, zero_rpow hα0.ne']

theorem sign_mul_of_pos {r : ℝ} (hr : 0 < r) (t : ℝ) : Real.sign (r * t) = Real.sign t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, Real.sign_of_neg (mul_neg_of_pos_of_neg hr ht)]
  · simp
  · rw [Real.sign_of_pos ht, Real.sign_of_pos (mul_pos hr ht)]

/-- Homogeneity: `ψ(r t) = r^α ψ(t)` for `r > 0`. -/
theorem stableExponent_mul {r : ℝ} (hr : 0 < r) (t : ℝ) :
    stableExponent α c e (r * t) = ((r ^ α : ℝ) : ℂ) * stableExponent α c e t := by
  simp only [stableExponent]
  rw [sign_mul_of_pos hr, abs_mul, abs_of_pos hr, mul_rpow hr.le (abs_nonneg t)]
  push_cast
  ring

theorem continuousAt_stableExponent (hα0 : 0 < α) : ContinuousAt (stableExponent α c e) 0 := by
  have h1 : Tendsto (fun t : ℝ => |t| ^ α) (𝓝 0) (𝓝 0) := by
    have := (continuous_abs.rpow_const fun _ => Or.inr hα0.le).tendsto (0 : ℝ)
    simpa [zero_rpow hα0.ne'] using this
  have h2 : Tendsto (fun t : ℝ => e * Real.sign t * |t| ^ α) (𝓝 0) (𝓝 0) := by
    have h3 := h1.const_mul |e|
    rw [mul_zero] at h3
    refine squeeze_zero_norm (fun t => ?_) h3
    have hs : |Real.sign t| ≤ 1 := by
      rcases Real.sign_apply_eq t with h | h | h <;> simp [h]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (rpow_nonneg (abs_nonneg t) _)]
    calc |e| * |Real.sign t| * |t| ^ α ≤ |e| * 1 * |t| ^ α := by gcongr
      _ = _ := by ring
  have h4 : Tendsto (fun t : ℝ => -(c * |t| ^ α)) (𝓝 0) (𝓝 0) := by
    simpa using (h1.const_mul c).neg
  have := ((Complex.continuous_ofReal.tendsto 0).comp h4).add
    (((Complex.continuous_ofReal.tendsto 0).comp h2).mul_const Complex.I)
  rw [ContinuousAt, stableExponent_zero hα0]
  rw [Complex.ofReal_zero, zero_mul, add_zero] at this
  exact this.congr fun t => rfl

namespace HasStableCharFun

variable {μ : Measure ℝ}

/-- A law with characteristic function `exp (-c |t|^α + i e sign(t) |t|^α)`, `α > 0`, `c > 0`,
is **strictly stable**, with `aₙ = n ^ (1 / α)` ([ST, Theorem 1.1.3], [Feller, §VI.1]). -/
theorem isStrictlyStable (h : HasStableCharFun α c e μ) (hα0 : 0 < α) (hc : 0 < c) :
    IsStrictlyStable μ where
  isProbabilityMeasure := h.1
  ne_dirac := by
    refine ne_dirac_of_norm_charFun_lt_one (t := 1) ?_
    rw [h.2, Complex.norm_exp]
    simp [stableExponent, hc]
  exists_mul n hn := by
    have := h.1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨(n : ℝ) ^ α⁻¹, rpow_pos_of_pos hn' _, ?_⟩
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_convPow, charFun_map_mul, h.2, h.2, ← Complex.exp_nat_mul,
      stableExponent_mul (rpow_pos_of_pos hn' _), rpow_inv_rpow hn'.le hα0.ne']
    push_cast; ring_nf

theorem isStable (h : HasStableCharFun α c e μ) (hα0 : 0 < α) (hc : 0 < c) : IsStable μ :=
  (h.isStrictlyStable hα0 hc).isStable

/-- Symmetric stable laws are the case `e = 0`. -/
theorem iff_isSymmStable : HasStableCharFun α c 0 μ ↔ IsSymmStable α c μ := by
  refine and_congr_right fun _ => forall_congr' fun t => ?_
  rw [Complex.ofReal_exp]
  simp [stableExponent]

end HasStableCharFun

end StableExponent

namespace GCLT

open StableIntegral

section Main

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α p : ℝ} {a : ℕ → ℝ}

theorem isProbabilityMeasure_map_neg : IsProbabilityMeasure (μ.map fun x => -x) :=
  inferInstance

/-- `n (φ(t / aₙ) - 1) → ψ(t)` for `0 < α < 1` ([Feller, §XVII.5], [GK, §35]). -/
theorem tendsto_mul_charFun_sub_one (hα0 : 0 < α) (hα1 : α < 1)
    (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hp : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p)) (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * (charFun μ ((a n)⁻¹ * t) - 1)) atTop
      (𝓝 (stableExponent α (stableConst α) ((2 * p - 1) * stableSkewConst α) t)) := by
  have := isProbabilityMeasure_map_neg (μ := μ)
  have hRV' : IsRegularlyVarying (absTail (μ.map fun x => -x)) (-α) := by
    rw [absTail_map_neg]; exact hRV
  have hna' : Tendsto (fun n : ℕ => (n : ℝ) * absTail (μ.map fun x => -x) (a n)) atTop (𝓝 1) := by
    rw [absTail_map_neg]; exact hna
  have hpos := tendsto_mul_integral_sin_max hα0 hα1 hRV ha hna hp t
  have hneg := tendsto_mul_integral_sin_max hα0 hα1 hRV' ha hna'
    (tendsto_measureReal_Ioi_map_neg_div hRV hp) t
  have hreal := (tendsto_mul_integral_one_sub_cos hα0 (by linarith) hRV ha hna t).neg
  have hF : Continuous fun v : ℝ => sin (t * v) := by fun_prop
  have hodd : ∀ v : ℝ, sin (t * -v) = -sin (t * v) := fun v => by rw [mul_neg, sin_neg]
  have hbd : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (f : ℝ → ℝ), Continuous f →
      Integrable (fun x => sin (t * f x)) ν := fun ν _ f hf =>
    Integrable.of_bound (by fun_prop) 1
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_sin_le_one _))
  have key : ∀ n : ℕ, (n : ℂ) * (charFun μ ((a n)⁻¹ * t) - 1) =
      (((-((n : ℝ) * ∫ x, (1 - cos ((a n)⁻¹ * t * x)) ∂μ)) : ℝ) : ℂ) +
      ((((n : ℝ) * ∫ x, sin (t * max (x / a n) 0) ∂μ) -
        (n : ℝ) * ∫ x, sin (t * max (x / a n) 0) ∂(μ.map fun x => -x) : ℝ) : ℂ) *
        Complex.I := by
    intro n
    have hs := integral_odd_eq_sub (μ := μ) hF hodd (a n) (hbd μ _ (by fun_prop))
      (hbd μ _ (by fun_prop))
    have hs' : ∫ x, sin ((a n)⁻¹ * t * x) ∂μ = ∫ x, sin (t * (x / a n)) ∂μ := by
      congr 1; funext x; congr 1; ring
    rw [← mul_sub, ← hs, ← hs', integral_one_sub_cos_eq, charFun_eq_integral_cos_add_sin]
    push_cast; ring
  simp_rw [key]
  have h := tendsto_ofReal_add_mul_I hreal (hpos.sub hneg)
  convert h using 2
  simp only [stableExponent]
  push_cast; ring

/-- `n (φ(t / aₙ) - 1 - i t m / aₙ) → ψ(t)` for `1 < α < 2`, `m = E X`. -/
theorem tendsto_mul_charFun_sub_one_sub (hα1 : 1 < α) (hα2 : α < 2)
    (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hp : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p)) (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * (charFun μ ((a n)⁻¹ * t) - 1 -
        (((a n)⁻¹ * t * ∫ x, x ∂μ : ℝ) : ℂ) * Complex.I)) atTop
      (𝓝 (stableExponent α (stableConst α) ((2 * p - 1) * stableSkewConst α) t)) := by
  have := isProbabilityMeasure_map_neg (μ := μ)
  have hα0 : 0 < α := by linarith
  have hν := integrable_id_of_isRegularlyVarying hα1 hRV
  have hRV' : IsRegularlyVarying (absTail (μ.map fun x => -x)) (-α) := by
    rw [absTail_map_neg]; exact hRV
  have hna' : Tendsto (fun n : ℕ => (n : ℝ) * absTail (μ.map fun x => -x) (a n)) atTop (𝓝 1) := by
    rw [absTail_map_neg]; exact hna
  have hpos := tendsto_mul_integral_sin_sub_max hα1 hα2 hRV ha hna hp t
  have hneg := tendsto_mul_integral_sin_sub_max hα1 hα2 hRV' ha hna'
    (tendsto_measureReal_Ioi_map_neg_div hRV hp) t
  have hreal := (tendsto_mul_integral_one_sub_cos hα0 hα2 hRV ha hna t).neg
  have hF : Continuous fun v : ℝ => sin (t * v) - t * v := by fun_prop
  have hodd : ∀ v : ℝ, sin (t * -v) - t * -v = -(sin (t * v) - t * v) := fun v => by
    rw [mul_neg, sin_neg]; ring
  have hbd : ∀ (f : ℝ → ℝ), Continuous f → (∀ x, |f x| ≤ |x| / a 0 * 0 + |x| * 0 + |f x|) →
      True := fun _ _ _ => trivial
  clear hbd
  have hint : ∀ (b : ℝ), 0 < b → ∀ (f : ℝ → ℝ), Continuous f → (∀ x, |f x| ≤ |x| / b) →
      Integrable (fun x => sin (t * f x) - t * f x) μ := by
    intro b hb f hf hfb
    refine (hν.norm.const_mul (2 * |t| / b)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |sin (t * f x) - t * f x| ≤ 2 * |t| * |f x| := abs_sin_mul_sub_le t (f x)
      _ ≤ 2 * |t| * (|x| / b) := by gcongr; exact hfb x
      _ = _ := by ring
  have hmax : ∀ (b : ℝ), 0 < b → ∀ x : ℝ, |max (x / b) 0| ≤ |x| / b := fun b hb x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (div_le_div_of_nonneg_right (le_abs_self x) hb.le) (by positivity)
  have key : ∀ n : ℕ, (n : ℂ) * (charFun μ ((a n)⁻¹ * t) - 1 -
        (((a n)⁻¹ * t * ∫ x, x ∂μ : ℝ) : ℂ) * Complex.I) =
      (((-((n : ℝ) * ∫ x, (1 - cos ((a n)⁻¹ * t * x)) ∂μ)) : ℝ) : ℂ) +
      ((((n : ℝ) * ∫ x, (sin (t * max (x / a n) 0) - t * max (x / a n) 0) ∂μ) -
        (n : ℝ) * ∫ x, (sin (t * max (x / a n) 0) - t * max (x / a n) 0)
          ∂(μ.map fun x => -x) : ℝ) : ℂ) * Complex.I := by
    intro n
    have hs := integral_odd_eq_sub (μ := μ) hF hodd (a n)
      (hint (a n) (ha n) _ (by fun_prop) (hmax (a n) (ha n)))
      (hint (a n) (ha n) (fun x => max (-x / a n) 0) (by fun_prop) fun x => by
        simpa [abs_neg] using hmax (a n) (ha n) (-x))
    have hs' : ∫ x, sin ((a n)⁻¹ * t * x) ∂μ - (a n)⁻¹ * t * ∫ x, x ∂μ =
        ∫ x, (sin (t * (x / a n)) - t * (x / a n)) ∂μ := by
      rw [← integral_const_mul, ← integral_sub (Integrable.of_bound (by fun_prop) 1
        (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_sin_le_one _)))
        (hν.const_mul _)]
      congr 1; funext x; rw [show (a n)⁻¹ * t * x = t * (x / a n) by ring]
    rw [← mul_sub, ← hs, ← hs', integral_one_sub_cos_eq, charFun_eq_integral_cos_add_sin]
    push_cast; ring
  simp_rw [key]
  have h := tendsto_ofReal_add_mul_I hreal (hpos.sub hneg)
  convert h using 2
  simp only [stableExponent]
  push_cast; ring

/-- If `n (zₙ - 1 - i cₙ) → ψ` with `n cₙ² → 0`, then `(zₙ e^{-i cₙ})ⁿ → e^ψ`. -/
theorem tendsto_mul_exp_pow {z : ℕ → ℂ} {c : ℕ → ℝ} {ψ : ℂ}
    (hz : Tendsto (fun n : ℕ => (n : ℂ) * (z n - 1 - (c n : ℂ) * Complex.I)) atTop (𝓝 ψ))
    (hc : Tendsto (fun n : ℕ => (n : ℝ) * c n ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (z n * Complex.exp (-(c n : ℂ) * Complex.I)) ^ n) atTop
      (𝓝 (Complex.exp ψ)) := by
  have hc2 : Tendsto (fun n : ℕ => c n ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => sq_nonneg _) ?_ hc
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg (c n)]
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have := (continuous_sqrt.tendsto 0).comp hc2
    simp only [Function.comp_def, sqrt_sq_eq_abs, sqrt_zero] at this
    exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 this
  have hE : Tendsto (fun n => Complex.exp (-(c n : ℂ) * Complex.I)) atTop (𝓝 1) := by
    have : Tendsto (fun n => -(c n : ℂ) * Complex.I) atTop (𝓝 0) := by
      simpa using (((Complex.continuous_ofReal.tendsto 0).comp hc0).neg).mul_const Complex.I
    have h := (Complex.continuous_exp.tendsto 0).comp this
    rw [Complex.exp_zero] at h
    exact h
  have hR : Tendsto (fun n : ℕ => (n : ℂ) *
      ((1 + (c n : ℂ) * Complex.I) * Complex.exp (-(c n : ℂ) * Complex.I) - 1)) atTop (𝓝 0) := by
    have hcc : Tendsto (fun n : ℕ => ((n : ℝ) * c n ^ 2 : ℝ)) atTop (𝓝 0) := hc
    refine squeeze_zero_norm' ?_ hcc
    filter_upwards [hc0.eventually (Metric.ball_mem_nhds 0 one_pos)] with n hn
    have hn1 : ‖(c n : ℂ) * Complex.I‖ ≤ 1 := by
      simp only [Real.dist_eq, sub_zero] at hn
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hn.le
    have hb := Complex.norm_exp_sub_one_sub_id_le hn1
    have e1 : (1 + (c n : ℂ) * Complex.I) * Complex.exp (-(c n : ℂ) * Complex.I) - 1 =
        -(Complex.exp (-(c n : ℂ) * Complex.I) *
          (Complex.exp ((c n : ℂ) * Complex.I) - 1 - (c n : ℂ) * Complex.I)) := by
      have : Complex.exp (-(c n : ℂ) * Complex.I) * Complex.exp ((c n : ℂ) * Complex.I) = 1 := by
        rw [← Complex.exp_add]; ring_nf; simp
      linear_combination this
    have hnorm : ‖Complex.exp (-(c n : ℂ) * Complex.I)‖ = 1 := by
      rw [show -(c n : ℂ) * Complex.I = ((-c n : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [e1, norm_mul, norm_neg, norm_mul, hnorm, one_mul, Complex.norm_natCast]
    have : ‖(c n : ℂ) * Complex.I‖ ^ 2 = c n ^ 2 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [← this]
    exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
  refine Complex.tendsto_one_add_pow_exp_of_tendsto
    (g := fun n => z n * Complex.exp (-(c n : ℂ) * Complex.I) - 1) ?_ |>.congr fun n => by ring
  have := (hz.mul hE).add hR
  rw [mul_one, add_zero] at this
  refine this.congr fun n => ?_
  ring

end Main

end GCLT

open GCLT StableIntegral Subexp

/-- **Generalized central limit theorem, `0 < α < 1`** ([Feller, Vol. II, §XVII.5, Theorem 2],
[GK, §35, Theorem 2], [EKM, Theorem 2.2.8]). Let `μ` be a probability law on `ℝ` whose
two-sided tail `G(x) = P(|X| > x)` is regularly varying with index `-α`, `0 < α < 1`, with tail
balance `P(X > x) / G(x) → p` (hence `P(X < -x) / G(x) → q = 1 - p`), and let `aₙ > 0` with
`n G(aₙ) → 1`. Then the laws of `(X₁ + ⋯ + Xₙ) / aₙ` converge weakly (no centering) to an
`α`-stable law `ν` with characteristic function
`exp (-C_α |t|^α + i (p - q) E_α sign(t) |t|^α)`, where `C_α = stableConst α` and
`E_α = stableSkewConst α = α ∫₀^∞ sin u · u^(-α-1) du` (classically
`= C_α tan (π α / 2)`, so this is `exp (-C_α |t|^α (1 - i β sign t tan (π α / 2)))`,
`β = p - q`). The limit exists by Lévy's continuity theorem. -/
theorem tendsto_map_convPow_of_isRegularlyVarying_of_lt_one {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {α p : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hp : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p))
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) :
    ∃ ν : ProbabilityMeasure ℝ,
      HasStableCharFun α (stableConst α) ((2 * p - 1) * stableSkewConst α) (ν : Measure ℝ) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν) := by
  have hf : ContinuousAt (fun t => Complex.exp (stableExponent α (stableConst α)
      ((2 * p - 1) * stableSkewConst α) t)) 0 := (continuousAt_stableExponent hα0).cexp
  obtain ⟨ν, hν, hlim⟩ := exists_tendsto_of_tendsto_charFun
    (μ := fun n => ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) hf (fun t => by
      simp only [ProbabilityMeasure.coe_mk]
      simp_rw [charFun_map_mul, charFun_convPow]
      have := Complex.tendsto_one_add_pow_exp_of_tendsto
        (tendsto_mul_charFun_sub_one hα0 hα1 hRV hp ha hna t)
      simpa using this)
  exact ⟨ν, ⟨inferInstance, fun t => congrFun hν t⟩, hlim⟩

/-- **Generalized central limit theorem, `1 < α < 2`** ([Feller, Vol. II, §XVII.5, Theorem 2],
[GK, §35, Theorem 2], [EKM, Theorem 2.2.8]). Under the hypotheses of
`tendsto_map_convPow_of_isRegularlyVarying_of_lt_one` but with `1 < α < 2` (so `X` is
integrable, `integrable_id_of_isRegularlyVarying`), the laws of `(X₁ + ⋯ + Xₙ - n E X) / aₙ`
converge weakly to an `α`-stable law with characteristic function
`exp (-C_α |t|^α + i (p - q) E_α sign(t) |t|^α)`, where
`E_α = stableSkewConst α = -∫₀^∞ (1 - cos u) u^(-α) du` (classically `= C_α tan (π α / 2)`). -/
theorem tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {α p : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hp : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p))
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) :
    ∃ ν : ProbabilityMeasure ℝ,
      HasStableCharFun α (stableConst α) ((2 * p - 1) * stableSkewConst α) (ν : Measure ℝ) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - n * ∫ y, y ∂μ)), inferInstance⟩) atTop
        (𝓝 ν) := by
  have hα0 : 0 < α := by linarith
  set m := ∫ y, y ∂μ with hm
  have hf : ContinuousAt (fun t => Complex.exp (stableExponent α (stableConst α)
      ((2 * p - 1) * stableSkewConst α) t)) 0 := (continuousAt_stableExponent hα0).cexp
  have hchar : ∀ t, Tendsto (fun n : ℕ =>
      charFun ((convPow μ n).map (fun x => (a n)⁻¹ * (x - n * m))) t) atTop
      (𝓝 (Complex.exp (stableExponent α (stableConst α) ((2 * p - 1) * stableSkewConst α) t))) := by
    intro t
    have hc : Tendsto (fun n : ℕ => (n : ℝ) * ((a n)⁻¹ * t * m) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_mul_inv_sq hα2 hRV hna).const_mul (t ^ 2 * m ^ 2)
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      ring
    have h := tendsto_mul_exp_pow (tendsto_mul_charFun_sub_one_sub hα1 hα2 hRV hp ha hna t) hc
    refine h.congr fun n => ?_
    have e : (fun x => (a n)⁻¹ * (x - n * m)) = fun x => (a n)⁻¹ * x + (-((a n)⁻¹ * (n * m))) := by
      funext x; ring
    rw [e, charFun_map_mul_add, charFun_convPow, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast; ring
  obtain ⟨ν, hν, hlim⟩ := exists_tendsto_of_tendsto_charFun
    (μ := fun n => ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - n * m)), inferInstance⟩) hf
    (fun t => by simpa using hchar t)
  exact ⟨ν, ⟨inferInstance, fun t => congrFun hν t⟩, hlim⟩

end ExtremeValueTheory
