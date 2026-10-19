/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT
import ExtremeValueTheory.StableLaws.LevyContinuity
import ExtremeValueTheory.RegularVariation.KaramataConverse

/-!
# Converse GCLT: characteristic-function bounds

Steps 1 and 2 of the converse of the generalized central limit theorem (symmetric case). For
a symmetric law `μ` with cosine transform `f(s) = ∫ cos (s x) dμ`: the inequalities
`f(2s) ≥ 2 f(s)² - 1` and `1 - f(k s) ≤ k² (1 - f(s))`, uniform closeness of tight
characteristic functions to `1` near the origin, and, when `Sₙ / aₙ → ν` weakly, the quadratic
bound on `hₙ(t) = n (1 - f(t / aₙ))` and its convergence to `-log Re φ_ν(t)`.

## Main definitions

* `GCLTConverse.cosTransform`: `f(s) = ∫ cos (s x) dμ(x)`, the characteristic function of a
  symmetric law.
* `GCLTConverse.nh`: `hₙ(t) = n (1 - f(t / aₙ))`, where `f` is the (real) characteristic function of
  `μ`.

## Main results

* `GCLTConverse.exists_forall_norm_charFun_sub_one_le`: For a tight family of probability measures,
  the characteristic functions are uniformly close to `1` near the origin.
* `GCLTConverse.exists_nh_le`: **Step 1 of the converse.** If `Sₙ / aₙ` converges weakly, then
  `hₙ(t) ≤ log 2 (|t| / δ + 1)²` for some `δ > 0` and all `n ≥ 3`, `t ∈ ℝ`.
* `GCLTConverse.tendsto_nh`: **Step 2 of the converse.** If `Sₙ / aₙ → ν` weakly, then `ψ(t) = Re
  φ_ν(t) > 0` and `hₙ(t) → -log ψ(t)` for every `t`.

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

end GCLTConverse

end ExtremeValueTheory
