/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.DomainOfAttractionIff

/-!
# The index of a stable law

Every stable law has norming constants `aₙ = n ^ (1 / α)` for a unique `0 < α ≤ 2`
([Feller, Vol. II, §VI.1, Theorem 1], [GK, §34], [ST, Theorem 1.1.3]).

Feller's route goes through the functional equation `a_{mn} = a_m a_n` and the monotonicity of
`aₙ`. We use instead the converse of the generalized central limit theorem: a stable law `μ` is
trivially in its own domain of attraction (`(Sₙ - bₙ) / aₙ` has law `μ` for every `n`), so the
converse gives an index `0 < α ≤ 2` and the symmetrized scaling limit
`n E[min (1, (X - X')² / (aₙ x)²)] → K x ^ (-α)`. For `α < 2` the limit is identified as an
explicit `α`-stable law (`identify_of_tendsto_mul_sqRatio`); for `α = 2` a second-order
expansion of `1 - cos` gives `n (1 - |φ(t / aₙ)|²) → K t² / 2`, hence `|φ(t)|² = e^{-K t² / 2}`.
In both cases `|φ_μ(t)| = exp (-c |t|^α)` with `c > 0`, which pins `aₙ = n ^ (1 / α)` and the
index.

## Main results

* `abs_one_sub_cos_sub_le`: the pointwise bound behind the Gaussian case.
* `tendsto_mul_one_sub_cosTransform_of_two`: if `n E[min (1, Z² / (aₙ x)²)] → K x⁻²` for all
  `x > 0`, then `n (1 - E cos (t Z / aₙ)) → K t² / 2`.
* `norm_charFun_sq_of_tendsto_mul_sqRatio_two`: in the converse GCLT with index `2`, the limit
  has `|φ_ν(t)|² = exp (-K t² / 2)`.
* `IsStable.isStableIndex_of_norm_charFun`: a stable law with `|φ(t)| = exp (-c |t|^β)` has
  index `β`.
* `IsStable.exists_norm_charFun`, `IsStable.exists_isStableIndex`: **[Feller, VI.1, Theorem 1]**:
  every stable law has `IsStableIndex α` for some `0 < α ≤ 2`, and `|φ(t)| = exp (-c |t|^α)`.
* `IsStableIndex.index_eq`, `IsStableIndex.pos`, `IsStableIndex.le_two`,
  `IsStable.existsUnique_isStableIndex`: the index is unique and lies in `(0, 2]`.
* `stableIndex μ`: the index of a stable law; `isStable_iff_exists_isStableIndex`.
* `domainOfAttraction_isStable_iff`: Feller's criterion with a plain `IsStable` limit whose
  (now well-defined) index is `α ∈ (0, 2)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

open Subexp GCLT StableIntegral GCLTConverse

section Pointwise

/-- **Second-order expansion of `1 - cos`, globally.** For `0 < e ≤ 1 / 2`,
`|1 - cos (e v) - (e² / 2) min (1, v²)| ≤ e⁴ min (1, (v / 2)²) + 2 (4 min (1, (v / 2)²) -
min (1, v²))`. -/
theorem abs_one_sub_cos_sub_le {e : ℝ} (he0 : 0 < e) (he : e ≤ 1 / 2) (v : ℝ) :
    |1 - Real.cos (e * v) - e ^ 2 / 2 * min 1 (v ^ 2)| ≤
      e ^ 4 * min 1 ((v / 2) ^ 2) + 2 * (4 * min 1 ((v / 2) ^ 2) - min 1 (v ^ 2)) := by
  have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  rcases le_or_gt |v| 2 with h2 | h2
  · have hev : |e * v| ≤ 1 := by
      rw [abs_mul, abs_of_pos he0]; nlinarith [abs_nonneg v]
    have hb := Real.cos_bound hev
    have hm2 : min 1 ((v / 2) ^ 2) = v ^ 2 / 4 := by
      rw [min_eq_right] <;> [ring; nlinarith [abs_nonneg v]]
    rw [hm2]
    have h4 : |e * v| ^ 4 = e ^ 4 * v ^ 4 := by
      rw [abs_mul, abs_of_pos he0, mul_pow, show v ^ 4 = (v ^ 2) ^ 2 by ring, hv2]; ring
    rw [h4] at hb
    have hvsq : v ^ 2 ≤ 4 := by rw [hv2]; nlinarith [abs_nonneg v]
    have hvv : v ^ 4 ≤ 4 * v ^ 2 := by
      rw [show v ^ 4 = v ^ 2 * v ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right hvsq (sq_nonneg v)
    have he4 : 0 ≤ e ^ 4 := by positivity
    rcases le_or_gt |v| 1 with h1 | h1
    · have hm1 : min 1 (v ^ 2) = v ^ 2 := min_eq_right (by nlinarith [abs_nonneg v])
      rw [hm1]
      have hvsq1 : v ^ 2 ≤ 1 := by rw [hv2]; nlinarith [abs_nonneg v]
      have hvv' : v ^ 4 ≤ v ^ 2 := by
        rw [show v ^ 4 = v ^ 2 * v ^ 2 by ring]
        nlinarith [mul_le_mul_of_nonneg_right hvsq1 (sq_nonneg v)]
      have : |1 - Real.cos (e * v) - e ^ 2 / 2 * v ^ 2| =
          |Real.cos (e * v) - (1 - (e * v) ^ 2 / 2)| := by
        rw [← abs_neg]; ring_nf
      rw [this]
      refine hb.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left hvv' he4]
    · have hm1 : min 1 (v ^ 2) = 1 := min_eq_left (by nlinarith [abs_nonneg v])
      rw [hm1]
      have hsplit : 1 - Real.cos (e * v) - e ^ 2 / 2 * 1 =
          -(Real.cos (e * v) - (1 - (e * v) ^ 2 / 2)) + e ^ 2 / 2 * (v ^ 2 - 1) := by ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      have hv1 : 1 ≤ v ^ 2 := by rw [hv2]; nlinarith [abs_nonneg v]
      have h5 : |e ^ 2 / 2 * (v ^ 2 - 1)| = e ^ 2 / 2 * (v ^ 2 - 1) :=
        abs_of_nonneg (mul_nonneg (by positivity) (by linarith))
      rw [abs_neg, h5]
      have he2 : e ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hvv he4]
  · have hm1 : min 1 (v ^ 2) = 1 := min_eq_left (by nlinarith [abs_nonneg v])
    have hm2 : min 1 ((v / 2) ^ 2) = 1 := min_eq_left (by
      rw [div_pow]; rw [le_div_iff₀ (by norm_num)]; nlinarith [abs_nonneg v])
    rw [hm1, hm2]
    have hc := Real.neg_one_le_cos (e * v)
    have hc' := Real.cos_le_one (e * v)
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg e, pow_nonneg he0.le 4]

end Pointwise

section GaussianSymm

theorem integrable_min_one_sq_mul (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (c : ℝ) :
    Integrable (fun z => min 1 ((c * z) ^ 2)) ρ :=
  Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (sq_nonneg _))]
    exact min_le_left _ _)

/-- An `ε`-squeeze: if for every `η > 0` the distance to `L` is eventually bounded by a sequence
converging to some `c < η`, then the sequence converges to `L`. -/
theorem tendsto_of_forall_abs_sub_le {x : ℕ → ℝ} {L : ℝ}
    (h : ∀ η > 0, ∃ B : ℕ → ℝ, ∃ c, c < η ∧ Tendsto B atTop (𝓝 c) ∧
      ∀ᶠ n in atTop, |x n - L| ≤ B n) : Tendsto x atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨B, c, hc, hB, hx⟩ := h η hη
  filter_upwards [hx, (tendsto_order.1 hB).2 η hc] with n h1 h2
  rw [Real.dist_eq]
  exact h1.trans_lt h2

/-- **The Gaussian scaling of `1 - cos`.** If `n E[min (1, Z² / (aₙ x)²)] → K x⁻²` for every
`x > 0`, then `n (1 - E cos (t Z / aₙ)) → K t² / 2` for every `t`. -/
theorem tendsto_mul_one_sub_cosTransform_of_two {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {K : ℝ} (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio ρ (a n * x)) atTop
      (𝓝 (K * x ^ (-(2 : ℝ))))) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - cosTransform ρ ((a n)⁻¹ * t))) atTop
      (𝓝 (K * t ^ 2 / 2)) := by
  have hL' : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio ρ (a n * x)) atTop
      (𝓝 (K / x ^ 2)) := by
    intro x hx
    convert hL x hx using 2
    rw [Real.rpow_neg hx.le, Real.rpow_two, div_eq_mul_inv]
  -- reduce to `t > 0`
  suffices hpos : ∀ t : ℝ, 0 < t → Tendsto (fun n : ℕ => (n : ℝ) *
      (1 - cosTransform ρ ((a n)⁻¹ * t))) atTop (𝓝 (K * t ^ 2 / 2)) by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · refine (hpos (-t) (neg_pos.2 ht)).congr (fun n => ?_) |>.trans (by rw [neg_sq])
      rw [mul_neg, cosTransform_neg]
    · simp [cosTransform_zero]
    · exact hpos t ht
  intro t ht
  refine tendsto_of_forall_abs_sub_le fun η hη => ?_
  set e := min (1 / 2) (η / (K * t ^ 2 + 1)) with hedef
  have hKt : 0 < K * t ^ 2 + 1 := by positivity
  have he0 : 0 < e := lt_min (by norm_num) (div_pos hη hKt)
  have he : e ≤ 1 / 2 := min_le_left _ _
  have he' : e ≤ η / (K * t ^ 2 + 1) := min_le_right _ _
  set x₁ := e / t
  set x₂ := 2 * e / t
  have hx₁ : 0 < x₁ := div_pos he0 ht
  have hx₂ : 0 < x₂ := div_pos (by positivity) ht
  set B : ℕ → ℝ := fun n => (e ^ 4 + 8) * ((n : ℝ) * sqRatio ρ (a n * x₂)) -
    2 * ((n : ℝ) * sqRatio ρ (a n * x₁)) +
    |e ^ 2 / 2 * ((n : ℝ) * sqRatio ρ (a n * x₁)) - K * t ^ 2 / 2|
  refine ⟨B, (e ^ 4 + 8) * (K / x₂ ^ 2) - 2 * (K / x₁ ^ 2) +
    |e ^ 2 / 2 * (K / x₁ ^ 2) - K * t ^ 2 / 2|, ?_, ?_, Eventually.of_forall fun n => ?_⟩
  · have h1 : e ^ 2 / 2 * (K / x₁ ^ 2) - K * t ^ 2 / 2 = 0 := by
      simp only [x₁]; field_simp; ring
    have h2 : (e ^ 4 + 8) * (K / x₂ ^ 2) - 2 * (K / x₁ ^ 2) = e ^ 2 * (K * t ^ 2) / 4 := by
      simp only [x₁, x₂]; field_simp; ring
    rw [h1, abs_zero, add_zero, h2]
    have he2 : e ^ 2 ≤ η / (K * t ^ 2 + 1) / 2 := by nlinarith
    have : e ^ 2 * (K * t ^ 2) ≤ η / (K * t ^ 2 + 1) / 2 * (K * t ^ 2) :=
      mul_le_mul_of_nonneg_right he2 (by positivity)
    have h3 : η / (K * t ^ 2 + 1) / 2 * (K * t ^ 2) < η := by
      rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  · exact ((((hL' x₂ hx₂).const_mul (e ^ 4 + 8)).sub ((hL' x₁ hx₁).const_mul 2)).add
      (((hL' x₁ hx₁).const_mul (e ^ 2 / 2)).sub_const _).abs)
  · -- the integral bound
    have han := ha n
    set y₁ := a n * x₁
    set y₂ := a n * x₂
    have hy₁ : y₁ ≠ 0 := (mul_pos han hx₁).ne'
    have hy₂ : y₂ ≠ 0 := (mul_pos han hx₂).ne'
    have hv : ∀ z : ℝ, (a n)⁻¹ * t * z = e * (y₁⁻¹ * z) := by
      intro z; simp only [y₁, x₁]; field_simp
    have hv2 : ∀ z : ℝ, y₂⁻¹ * z = y₁⁻¹ * z / 2 := by
      intro z; simp only [y₁, y₂, x₁, x₂]; field_simp
    have hS1 := sqRatio_eq_integral_min' (μ := ρ) hy₁
    have hS2 := sqRatio_eq_integral_min' (μ := ρ) hy₂
    have hI1 := integrable_min_one_sq_mul ρ y₁⁻¹
    have hI2 := integrable_min_one_sq_mul ρ y₂⁻¹
    have hcos : 1 - cosTransform ρ ((a n)⁻¹ * t) = ∫ z, (1 - Real.cos (e * (y₁⁻¹ * z))) ∂ρ := by
      have hcint : Integrable (fun z => Real.cos (e * (y₁⁻¹ * z))) ρ := by
        simpa [hv] using (integrable_cos (μ := ρ) ((a n)⁻¹ * t))
      rw [integral_sub (integrable_const _) hcint, integral_const, cosTransform]
      simp only [probReal_univ, one_smul, hv]
    have hIc : Integrable (fun z => 1 - Real.cos (e * (y₁⁻¹ * z))) ρ :=
      (integrable_const _).sub (by
        simpa [hv] using (integrable_cos (μ := ρ) ((a n)⁻¹ * t)))
    have hmain : |(1 - cosTransform ρ ((a n)⁻¹ * t)) - e ^ 2 / 2 * sqRatio ρ y₁| ≤
        (e ^ 4 + 8) * sqRatio ρ y₂ - 2 * sqRatio ρ y₁ := by
      rw [hcos, hS1, hS2, ← integral_const_mul, ← integral_sub hIc (hI1.const_mul _)]
      refine (abs_integral_le_integral_abs).trans ?_
      have hR : (e ^ 4 + 8) * ∫ z, min 1 ((y₂⁻¹ * z) ^ 2) ∂ρ -
          2 * ∫ z, min 1 ((y₁⁻¹ * z) ^ 2) ∂ρ = ∫ z, (e ^ 4 * min 1 ((y₂⁻¹ * z) ^ 2) +
          2 * (4 * min 1 ((y₂⁻¹ * z) ^ 2) - min 1 ((y₁⁻¹ * z) ^ 2))) ∂ρ := by
        have hA : Integrable (fun z => e ^ 4 * min 1 ((y₂⁻¹ * z) ^ 2)) ρ := hI2.const_mul _
        have hB4 : Integrable (fun z => 4 * min 1 ((y₂⁻¹ * z) ^ 2)) ρ := hI2.const_mul _
        have hB : Integrable (fun z => 2 * (4 * min 1 ((y₂⁻¹ * z) ^ 2) -
            min 1 ((y₁⁻¹ * z) ^ 2))) ρ := (hB4.sub hI1).const_mul 2
        rw [integral_add hA hB, integral_const_mul, integral_const_mul, integral_sub hB4 hI1,
          integral_const_mul]
        ring
      rw [hR]
      refine integral_mono (hIc.sub (hI1.const_mul _)).abs
        ((hI2.const_mul _).add (((hI2.const_mul 4).sub hI1).const_mul 2)) fun z => ?_
      have := abs_one_sub_cos_sub_le he0 he (y₁⁻¹ * z)
      simp only [hv2]
      exact this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 : (n : ℝ) * (1 - cosTransform ρ ((a n)⁻¹ * t)) - K * t ^ 2 / 2 =
        (n : ℝ) * ((1 - cosTransform ρ ((a n)⁻¹ * t)) - e ^ 2 / 2 * sqRatio ρ y₁) +
        (e ^ 2 / 2 * ((n : ℝ) * sqRatio ρ y₁) - K * t ^ 2 / 2) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    simp only [B]
    rw [abs_mul, abs_of_nonneg hn0]
    have := mul_le_mul_of_nonneg_left hmain hn0
    nlinarith

/-- If `n (1 - fₙ) → L` then `fₙ ^ n → e^{-L}`. -/
theorem tendsto_pow_of_tendsto_mul_one_sub {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ) * (1 - f n)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => f n ^ n) atTop (𝓝 (Real.exp (-L))) := by
  set w : ℕ → ℂ := fun n => ((f n - 1 : ℝ) : ℂ)
  have hw : ∀ n : ℕ, (n : ℂ) * w n = ((-((n : ℝ) * (1 - f n)) : ℝ) : ℂ) := by
    intro n; simp only [w]; push_cast; ring
  have hC : ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * w n‖ ≤ |L| + 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 h) 1 one_pos] with n hn
    rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    rw [Real.dist_eq] at hn
    have := abs_sub_abs_le_abs_sub ((n : ℝ) * (1 - f n)) L
    linarith
  have h1 := tendsto_one_add_pow_sub_exp hC
  have h2 : Tendsto (fun n : ℕ => Complex.exp ((n : ℂ) * w n)) atTop
      (𝓝 (Complex.exp ((-L : ℝ) : ℂ))) := by
    simp_rw [hw]
    exact (Complex.continuous_exp.tendsto _).comp
      ((Complex.continuous_ofReal.tendsto _).comp h.neg)
  have h3 := h1.add h2
  rw [zero_add] at h3
  have h4 : Tendsto (fun n : ℕ => Complex.ofReal (f n ^ n)) atTop
      (𝓝 (Complex.ofReal (Real.exp (-L)))) := by
    rw [Complex.ofReal_exp]
    refine h3.congr fun n => ?_
    simp only [w]
    push_cast
    ring
  have := (Complex.continuous_re.tendsto _).comp h4
  simpa only [Function.comp_def, Complex.ofReal_re] using this

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

/-- **The symmetrized limit in the Gaussian case.** If `(Sₙ - bₙ) / aₙ → ν` and the symmetrized
scaling limit holds with index `2`, `n E[min (1, (X - X')² / (aₙ x)²)] → K x⁻²`, then
`|φ_ν(t)|² = exp (-K t² / 2)`. -/
theorem norm_charFun_sq_of_tendsto_mul_sqRatio_two (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    {K : ℝ} (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
      (𝓝 (K * x ^ (-(2 : ℝ))))) (t : ℝ) :
    ‖charFun (ν : Measure ℝ) t‖ ^ 2 = Real.exp (-(K * t ^ 2 / 2)) := by
  set f : ℝ → ℝ := fun s => ‖charFun μ s‖ ^ 2 with hfdef
  have hf : ∀ s, f s = cosTransform (symmLaw μ) s := by
    intro s
    rw [cosTransform_eq_re, charFun_symmLaw, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hlim : Tendsto (fun n : ℕ => f ((a n)⁻¹ * t) ^ n) atTop
      (𝓝 (‖charFun (ν : Measure ℝ) t‖ ^ 2)) := by
    have h := ((continuous_norm.pow 2).tendsto _).comp
      (((continuous_charFun_probabilityMeasure t).tendsto ν).comp hconv)
    refine h.congr fun n => ?_
    simp only [Function.comp, ProbabilityMeasure.coe_mk, hfdef, Pi.pow_apply]
    have e : (fun x => (a n)⁻¹ * (x - b n)) = fun x => (a n)⁻¹ * x + (-((a n)⁻¹ * b n)) := by
      funext x; ring
    rw [e, charFun_map_mul_add, charFun_convPow, norm_mul, norm_pow,
      show (((-((a n)⁻¹ * b n) : ℝ) : ℂ) * (t : ℂ) * Complex.I) =
        ((-((a n)⁻¹ * b n) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    ring
  have h2 := tendsto_pow_of_tendsto_mul_one_sub
    (tendsto_mul_one_sub_cosTransform_of_two (ρ := symmLaw μ) ha hK hL t)
  simp_rw [← hf] at h2
  exact tendsto_nhds_unique hlim h2

end GaussianSymm

section Index

variable {μ : Measure ℝ}

/-- A stable law whose characteristic function has modulus `exp (-c |t|^β)`, `c, β > 0`, has
index `β`: comparing `|φ(1)|ⁿ = |φ(aₙ)|` forces `aₙ ^ β = n`. -/
theorem IsStable.isStableIndex_of_norm_charFun (h : IsStable μ) {β c : ℝ} (hβ : 0 < β)
    (hc : 0 < c) (hφ : ∀ t, ‖charFun μ t‖ = Real.exp (-(c * |t| ^ β))) :
    IsStableIndex β μ := by
  have := h.isProbabilityMeasure
  refine ⟨h, fun n hn => ?_⟩
  obtain ⟨a, b, ha, hab⟩ := h.exists_affine n hn
  have h1 := congrArg (fun ρ => charFun ρ 1) hab
  simp only [charFun_convPow, charFun_map_mul_add] at h1
  have h2 : ‖charFun μ 1‖ ^ n = ‖charFun μ a‖ := by
    rw [← norm_pow, h1, norm_mul, mul_one,
      show (b : ℂ) * ((1 : ℝ) : ℂ) * Complex.I = ((b * 1 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hφ, hφ, ← Real.exp_nat_mul, Real.exp_eq_exp, abs_one, Real.one_rpow, mul_one,
    abs_of_pos ha] at h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have haβ : a ^ β = n := by
    have : c * a ^ β = c * n := by linarith
    exact mul_left_cancel₀ hc.ne' this
  have hae : a = (n : ℝ) ^ β⁻¹ := by
    rw [← haβ, Real.rpow_rpow_inv ha.le hβ.ne']
  exact ⟨b, by rw [hab, hae]⟩

/-- **A stable law is in its own domain of attraction**: there are `aₙ > 0` and `bₙ` with
`(Sₙ - bₙ) / aₙ ∼ μ` for every `n ≥ 1`. -/
theorem IsStable.exists_tendsto_self [IsProbabilityMeasure μ] (h : IsStable μ) :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop
      (𝓝 ⟨μ, inferInstance⟩) := by
  have hex : ∀ n : ℕ, ∃ a b : ℝ, 0 < a ∧ (1 ≤ n → convPow μ n = μ.map (fun x => a * x + b)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, 0, one_pos, fun h => absurd h (by norm_num)⟩
    · obtain ⟨a, b, ha, hab⟩ := h.exists_affine n hn
      exact ⟨a, b, ha, fun _ => hab⟩
  choose a b ha hab using hex
  refine ⟨a, b, ha, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply Subtype.ext
  change μ = (convPow μ n).map (fun x => (a n)⁻¹ * (x - b n))
  rw [hab n hn, Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun x => (a n)⁻¹ * (x - b n)) ∘ fun x => a n * x + b n) = id := by
    funext x
    simp only [Function.comp, id]
    field_simp [(ha n).ne']
    ring
  rw [this, Measure.map_id]

/-- **Feller, Vol. II, §VI.1, Theorem 1 (modulus form).** The characteristic function of a
stable law has modulus `exp (-c |t|^α)` for some `0 < α ≤ 2`, `c > 0`.

The law is in its own domain of attraction, so the converse GCLT gives the index `α` and the
symmetrized scaling limit. For `α < 2` the explicit identification of the limit
(`identify_of_tendsto_mul_sqRatio`) gives the modulus; for `α = 2`,
`norm_charFun_sq_of_tendsto_mul_sqRatio_two` gives `|φ(t)|² = exp (-K t² / 2)`. -/
theorem IsStable.exists_norm_charFun (h : IsStable μ) :
    ∃ α c : ℝ, 0 < α ∧ α ≤ 2 ∧ 0 < c ∧ ∀ t, ‖charFun μ t‖ = Real.exp (-(c * |t| ^ α)) := by
  have := h.isProbabilityMeasure
  obtain ⟨a, b, ha, hconv⟩ := h.exists_tendsto_self
  set ν : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩
  obtain ⟨α, hα0, hα2, K, hK, hL⟩ :=
    exists_tendsto_mul_sqRatio_symmLaw ha (ν := ν) h.ne_dirac hconv
  rcases lt_or_eq_of_le hα2 with hlt | rfl
  · obtain ⟨-, B, hB0, -, p, -, -, -, m, hm1, hm2⟩ :=
      identify_of_tendsto_mul_sqRatio ha hconv hα0 hlt hK hL
    rcases eq_or_ne α 1 with h1 | h1
    · subst h1
      refine ⟨1, B * stableConst 1, one_pos, by norm_num,
        mul_pos hB0 (stableConst_pos one_pos (by norm_num)), fun t => ?_⟩
      rw [← norm_charFun_map_add_const m]
      change ‖charFun ((ν : Measure ℝ).map (· + m)) t‖ = _
      rw [(hm2 rfl).2, Complex.norm_exp, Real.rpow_one]
      simp [stableExponentOne]
    · refine ⟨α, B * stableConst α, hα0, hα2, mul_pos hB0 (stableConst_pos hα0 hlt),
        fun t => ?_⟩
      rw [← norm_charFun_map_add_const m]
      change ‖charFun ((ν : Measure ℝ).map (· + m)) t‖ = _
      rw [(hm1 h1).2, Complex.norm_exp]
      simp [stableExponent]
  · refine ⟨2, K / 4, two_pos, le_rfl, by positivity, fun t => ?_⟩
    have h2 := norm_charFun_sq_of_tendsto_mul_sqRatio_two ha hconv hK hL t
    change ‖charFun μ t‖ ^ 2 = _ at h2
    have hpos : 0 ≤ Real.exp (-(K / 4 * |t| ^ (2 : ℝ))) := (Real.exp_pos _).le
    refine (pow_left_inj₀ (norm_nonneg _) hpos two_ne_zero).1 ?_
    rw [h2, ← Real.exp_nat_mul, Real.rpow_two, sq_abs]
    congr 1
    push_cast
    ring

/-- **Feller, Vol. II, §VI.1, Theorem 1.** Every stable law has norming constants
`aₙ = n ^ (1 / α)` for some `0 < α ≤ 2`. -/
theorem IsStable.exists_isStableIndex (h : IsStable μ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 2 ∧ IsStableIndex α μ := by
  obtain ⟨α, c, hα0, hα2, hc, hφ⟩ := h.exists_norm_charFun
  exact ⟨α, hα0, hα2, h.isStableIndex_of_norm_charFun hα0 hc hφ⟩

/-- **Uniqueness of the index.** -/
theorem IsStableIndex.index_eq {α β : ℝ} (hα : IsStableIndex α μ) (hβ : IsStableIndex β μ) :
    α = β := by
  obtain ⟨γ, c, -, -, hc, hφ⟩ := hα.1.exists_norm_charFun
  exact (hα.eq_of_norm_charFun hc hφ).symm.trans (hβ.eq_of_norm_charFun hc hφ)

theorem IsStableIndex.pos {α : ℝ} (h : IsStableIndex α μ) : 0 < α := by
  obtain ⟨γ, hγ0, -, hγ⟩ := h.1.exists_isStableIndex
  exact (hγ.index_eq h) ▸ hγ0

theorem IsStableIndex.le_two {α : ℝ} (h : IsStableIndex α μ) : α ≤ 2 := by
  obtain ⟨γ, -, hγ2, hγ⟩ := h.1.exists_isStableIndex
  exact (hγ.index_eq h) ▸ hγ2

/-- **The index of a stable law exists and is unique.** -/
theorem IsStable.existsUnique_isStableIndex (h : IsStable μ) : ∃! α : ℝ, IsStableIndex α μ := by
  obtain ⟨α, -, -, hα⟩ := h.exists_isStableIndex
  exact ⟨α, hα, fun β hβ => hβ.index_eq hα⟩

theorem isStable_iff_exists_isStableIndex :
    IsStable μ ↔ ∃ α : ℝ, 0 < α ∧ α ≤ 2 ∧ IsStableIndex α μ :=
  ⟨fun h => h.exists_isStableIndex, fun ⟨_, _, _, h⟩ => h.1⟩

open Classical in
/-- The index `α ∈ (0, 2]` of a stable law (`0` for a law which is not stable). -/
noncomputable def stableIndex (μ : Measure ℝ) : ℝ :=
  if h : IsStable μ then Classical.choose h.exists_isStableIndex else 0

theorem IsStable.isStableIndex_stableIndex (h : IsStable μ) :
    IsStableIndex (stableIndex μ) μ := by
  simp only [stableIndex, h, ↓reduceDIte]
  exact (Classical.choose_spec h.exists_isStableIndex).2.2

theorem IsStableIndex.stableIndex_eq {α : ℝ} (h : IsStableIndex α μ) : stableIndex μ = α :=
  h.1.isStableIndex_stableIndex.index_eq h

theorem IsStable.stableIndex_pos (h : IsStable μ) : 0 < stableIndex μ :=
  h.isStableIndex_stableIndex.pos

theorem IsStable.stableIndex_le_two (h : IsStable μ) : stableIndex μ ≤ 2 :=
  h.isStableIndex_stableIndex.le_two

theorem isStableIndex_iff_stableIndex_eq {α : ℝ} :
    IsStableIndex α μ ↔ IsStable μ ∧ stableIndex μ = α :=
  ⟨fun h => ⟨h.1, h.stableIndex_eq⟩, fun ⟨h, e⟩ => e ▸ h.isStableIndex_stableIndex⟩

end Index

section Iff

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- **Feller's criterion with a plain stable limit** ([Feller, Vol. II, §XVII.5, Theorem 2]).
For `0 < α < 2`, `(Sₙ - bₙ) / aₙ` converges weakly to a stable law of index `α` (in the sense
of `IsStable`, the index being the unique `stableIndex`) iff `P(|X| > ·) ∈ RV(-α)` and the tails
are balanced. -/
theorem domainOfAttraction_isStable_iff (hα0 : 0 < α) (hα2 : α < 2) :
    (∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ b : ℕ → ℝ, ∃ ν : ProbabilityMeasure ℝ,
      IsStable ν ∧ stableIndex ν = α ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) ↔
      IsRegularlyVarying (absTail μ) (-α) ∧ ∃ p, 0 ≤ p ∧ p ≤ 1 ∧
        Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p) := by
  rw [← domainOfAttraction_isStableIndex_iff hα0 hα2]
  simp only [isStableIndex_iff_stableIndex_eq, and_assoc]

end Iff

end ExtremeValueTheory
