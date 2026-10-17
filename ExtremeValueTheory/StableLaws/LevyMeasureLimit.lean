/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverse
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Convergence of the Lévy measures of normalized sums

WIP
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace GCLTConverse

open GCLT Subexp

section Centering

/-- The truncation `clip y = max (-1) (min 1 y)`. -/
noncomputable def clip (y : ℝ) : ℝ := max (-1) (min 1 y)

theorem continuous_clip : Continuous clip := by unfold clip; fun_prop

theorem abs_clip_le (y : ℝ) : |clip y| ≤ 1 := by
  unfold clip; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_eq_of_abs_le {y : ℝ} (h : |y| ≤ 1) : clip y = y := by
  unfold clip
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem clip_sq_le (y : ℝ) : clip y ^ 2 ≤ min 1 (y ^ 2) := by
  refine le_min ?_ ?_
  · have := abs_clip_le y
    nlinarith [abs_nonneg (clip y), sq_abs (clip y)]
  · rcases le_or_gt |y| 1 with h | h
    · rw [clip_eq_of_abs_le h]
    · have := abs_clip_le y
      nlinarith [abs_nonneg (clip y), sq_abs (clip y), sq_abs y]

theorem sq_div_max_eq_min {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    y ^ 2 / max (y ^ 2) (a ^ 2) = min 1 ((a⁻¹ * y) ^ 2) := by
  have ha2 : 0 < a ^ 2 := by positivity
  rw [sq_div_max_eq ha, mul_pow, inv_pow, ← div_eq_inv_mul]
  rcases le_total (y ^ 2) (a ^ 2) with h | h
  · rw [min_eq_right h, min_eq_right ((div_le_one ha2).2 h)]
  · rw [min_eq_left h, min_eq_left ((one_le_div ha2).2 h), div_self ha2.ne']

/-- A numerical bound: `‖e^{iθ} - 1 - iθ‖ ≤ 3 θ²`. -/
theorem norm_exp_mul_I_sub_one_sub_le (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1 - θ * Complex.I‖ ≤ 3 * θ ^ 2 := by
  have he : Complex.exp (θ * Complex.I) - 1 - θ * Complex.I =
      ((Real.cos θ - 1 : ℝ) : ℂ) + ((Real.sin θ - θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h1 : |Real.cos θ - 1| ≤ θ ^ 2 / 2 := by
    rw [abs_le]
    constructor
    · linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
    · linarith [Real.cos_le_one θ, sq_nonneg θ]
  have h2 : |Real.sin θ - θ| ≤ 2 * θ ^ 2 := by
    rcases le_or_gt |θ| 1 with h | h
    · have hb := Real.sin_bound h
      have h3 : |θ| ^ 3 ≤ θ ^ 2 := by
        rw [← sq_abs θ]; nlinarith [abs_nonneg θ]
      have h5 : |θ| ^ 5 ≤ θ ^ 2 := by
        rw [← sq_abs θ]
        have : |θ| ^ 5 = |θ| ^ 2 * |θ| ^ 3 := by ring
        rw [this]
        have h6 : |θ| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg θ) h
        nlinarith [sq_nonneg |θ|]
      calc |Real.sin θ - θ| = |(Real.sin θ - (θ - θ ^ 3 / 6)) - θ ^ 3 / 6| := by ring_nf
        _ ≤ |Real.sin θ - (θ - θ ^ 3 / 6)| + |θ ^ 3 / 6| := abs_sub _ _
        _ ≤ |θ| ^ 5 / 100 + |θ| ^ 3 / 6 := by
            gcongr; rw [abs_div, abs_pow]; norm_num
        _ ≤ 2 * θ ^ 2 := by linarith [sq_nonneg θ]
    · have h1' : |Real.sin θ - θ| ≤ 1 + |θ| :=
        (abs_sub _ _).trans (by linarith [Real.abs_sin_le_one θ])
      have : |θ| ≤ θ ^ 2 := by rw [← sq_abs]; nlinarith
      linarith
  linarith [sq_nonneg θ]

end Centering

section CenteredLaw

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ → ℝ)

/-- The truncated mean `τₙ = E[clip (X / aₙ)]`. -/
noncomputable def ctr (n : ℕ) : ℝ := ∫ x, clip ((a n)⁻¹ * x) ∂μ

/-- The law of the centered variable `X / aₙ - τₙ`. -/
noncomputable def cLaw (n : ℕ) : Measure ℝ := μ.map (fun x => (a n)⁻¹ * x - ctr μ a n)

instance (n : ℕ) : IsProbabilityMeasure (cLaw μ a n) := by
  unfold cLaw; infer_instance

/-- `wₙ(t) = φ_{X / aₙ - τₙ}(t) - 1`. -/
noncomputable def wfun (n : ℕ) (t : ℝ) : ℂ := charFun (cLaw μ a n) t - 1

variable {μ a}

theorem integrable_clip (n : ℕ) : Integrable (fun x => clip ((a n)⁻¹ * x)) μ :=
  Integrable.of_bound (continuous_clip.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    1 (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_clip_le _)

theorem abs_ctr_le (n : ℕ) : |ctr μ a n| ≤ 1 := by
  rw [ctr, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ x, ‖clip ((a n)⁻¹ * x)‖ ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ :=
        integral_mono (integrable_clip n).norm (integrable_const _) fun x => by
          rw [Real.norm_eq_abs]; exact abs_clip_le _
    _ = 1 := by simp

omit [IsProbabilityMeasure μ] in
theorem sqRatio_eq_integral_min {n : ℕ} (ha : a n ≠ 0) :
    sqRatio μ (a n) = ∫ x, min 1 (((a n)⁻¹ * x) ^ 2) ∂μ := by
  rw [sqRatio]; simp_rw [sq_div_max_eq_min ha]

theorem integrable_min_one_sq (n : ℕ) :
    Integrable (fun x => min 1 (((a n)⁻¹ * x) ^ 2)) μ :=
  Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (sq_nonneg _))]
    exact min_le_left _ _)

/-- `τₙ² ≤ E[min (1, (X / aₙ)²)]`. -/
theorem ctr_sq_le {n : ℕ} (ha : a n ≠ 0) : ctr μ a n ^ 2 ≤ sqRatio μ (a n) := by
  have hm : MemLp (fun x => clip ((a n)⁻¹ * x)) 2 μ :=
    MemLp.of_bound (continuous_clip.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      1 (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_clip_le _)
  have hv := variance_nonneg (fun x => clip ((a n)⁻¹ * x)) μ
  rw [variance_eq_sub hm] at hv
  rw [sqRatio_eq_integral_min ha, ctr]
  refine le_trans ?_ (integral_mono (hm.integrable_sq) (integrable_min_one_sq n)
    fun x => clip_sq_le _)
  simp only [Pi.pow_apply] at hv
  linarith

/-- The centering identity `E[clip (X / aₙ) - τₙ] = 0`. -/
theorem integral_clip_sub_ctr (n : ℕ) :
    ∫ x, (clip ((a n)⁻¹ * x) - ctr μ a n) ∂μ = 0 := by
  rw [integral_sub (integrable_clip n) (integrable_const _), integral_const, probReal_univ,
    one_smul, ctr, sub_self]

omit [IsProbabilityMeasure μ] in
theorem charFun_cLaw (n : ℕ) (t : ℝ) :
    charFun (cLaw μ a n) t =
      ∫ x, Complex.exp (((t * ((a n)⁻¹ * x - ctr μ a n) : ℝ) : ℂ) * Complex.I) ∂μ := by
  rw [charFun_apply_real, cLaw, integral_map (by fun_prop) (by fun_prop)]
  congr 1; funext x; push_cast; ring_nf

/-- Pointwise bound behind `n |wₙ(t)| = O(n E[min (1, (X / aₙ)²)])`. -/
theorem norm_exp_sub_one_sub_clip_le (t y τ : ℝ) (hτ : |τ| ≤ 1) :
    ‖Complex.exp (((t * (y - τ)) : ℝ) * Complex.I) - 1 - ((t * (clip y - τ) : ℝ) : ℂ) * Complex.I‖
      ≤ (6 * t ^ 2 + 2 * |t| + 2) * min 1 (y ^ 2) + 6 * t ^ 2 * τ ^ 2 := by
  rcases le_or_gt |y| 1 with hy | hy
  · rw [clip_eq_of_abs_le hy]
    refine (norm_exp_mul_I_sub_one_sub_le _).trans ?_
    have hm : min 1 (y ^ 2) = y ^ 2 := min_eq_right (by rw [← sq_abs]; nlinarith [abs_nonneg y])
    rw [hm]
    nlinarith [sq_nonneg (y + τ), sq_nonneg t, abs_nonneg t, sq_nonneg (t * τ), sq_nonneg y]
  · have hm : min 1 (y ^ 2) = 1 := min_eq_left (by rw [← sq_abs]; nlinarith)
    rw [hm]
    have h1 : ‖Complex.exp (((t * (y - τ)) : ℝ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖((t * (clip y - τ) : ℝ) : ℂ) * Complex.I‖ ≤ 2 * |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have : |clip y - τ| ≤ 2 := (abs_sub _ _).trans (by linarith [abs_clip_le y])
      nlinarith [abs_nonneg t]
    have h3 := norm_sub_le (Complex.exp (((t * (y - τ)) : ℝ) * Complex.I)) (1 : ℂ)
    calc _ ≤ ‖Complex.exp (((t * (y - τ)) : ℝ) * Complex.I)‖ + ‖(1 : ℂ)‖ +
          ‖((t * (clip y - τ) : ℝ) : ℂ) * Complex.I‖ :=
          (norm_sub_le _ _).trans (by linarith)
      _ ≤ 1 + 1 + 2 * |t| := by rw [h1, norm_one]; linarith
      _ ≤ _ := by nlinarith [sq_nonneg t, sq_nonneg (t * τ)]

/-- **The centered characteristic function is close to `1`**:
`|wₙ(t)| ≤ (12 t² + 2 |t| + 2) E[min (1, (X / aₙ)²)]`. -/
theorem norm_wfun_le {n : ℕ} (ha : a n ≠ 0) (t : ℝ) :
    ‖wfun μ a n t‖ ≤ (12 * t ^ 2 + 2 * |t| + 2) * sqRatio μ (a n) := by
  set τ := ctr μ a n
  have hτ := abs_ctr_le (μ := μ) (a := a) n
  have hint1 : Integrable (fun x => Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) *
      Complex.I)) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Complex.norm_exp_ofReal_mul_I])
  have hint2 : Integrable (fun x => ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) * Complex.I) μ := by
    refine Integrable.mul_const ?_ _
    exact (((integrable_clip n).sub (integrable_const τ)).const_mul t).ofReal
  have hint1' : Integrable (fun x => Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) *
      Complex.I) - 1) μ := hint1.sub (integrable_const 1)
  have hB : ∫ x, ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) * Complex.I ∂μ = 0 := by
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, integral_clip_sub_ctr]
    simp
  have hw : wfun μ a n t = ∫ x, (Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) *
      Complex.I) - 1 - ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) * Complex.I) ∂μ := by
    rw [integral_sub hint1' hint2, hB, sub_zero, integral_sub hint1 (integrable_const 1),
      integral_const, probReal_univ, one_smul, wfun, charFun_cLaw]
  rw [hw]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hS := ctr_sq_le (μ := μ) ha
  calc ∫ x, ‖Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) * Complex.I) - 1 -
        ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) * Complex.I‖ ∂μ
      ≤ ∫ x, ((6 * t ^ 2 + 2 * |t| + 2) * min 1 (((a n)⁻¹ * x) ^ 2) + 6 * t ^ 2 * τ ^ 2) ∂μ :=
        integral_mono (hint1'.sub hint2).norm
          (((integrable_min_one_sq n).const_mul _).add (integrable_const _))
          fun x => norm_exp_sub_one_sub_clip_le t _ τ hτ
    _ = (6 * t ^ 2 + 2 * |t| + 2) * sqRatio μ (a n) + 6 * t ^ 2 * τ ^ 2 := by
        rw [integral_add ((integrable_min_one_sq n).const_mul _) (integrable_const _),
          integral_const_mul, integral_const, probReal_univ, one_smul,
          sqRatio_eq_integral_min ha]
    _ ≤ _ := by nlinarith [sq_nonneg t]

end CenteredLaw

section PowExp

/-- If `n wₙ` is bounded, then `(1 + wₙ)ⁿ - e^{n wₙ} → 0`. -/
theorem tendsto_one_add_pow_sub_exp {w : ℕ → ℂ} {C : ℝ}
    (hC : ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * w n‖ ≤ C) :
    Tendsto (fun n : ℕ => (1 + w n) ^ n - Complex.exp (n * w n)) atTop (𝓝 0) := by
  have hw0 : Tendsto (fun n : ℕ => ‖w n‖) atTop (𝓝 0) := by
    have hle : ∀ᶠ n : ℕ in atTop, ‖w n‖ ≤ C / n := by
      filter_upwards [hC, eventually_gt_atTop 0] with n hn hn0
      have : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [norm_mul, Complex.norm_natCast] at hn
      rw [le_div_iff₀ this]; linarith
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hle
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  -- `εₙ = n (log (1 + wₙ) - wₙ) → 0`
  set ε : ℕ → ℂ := fun n => (n : ℂ) * (Complex.log (1 + w n) - w n) with hε
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    have hb : ∀ᶠ n : ℕ in atTop, ‖ε n‖ ≤ C * ‖w n‖ := by
      filter_upwards [hC, (tendsto_order.1 hw0).2 (1 / 2) (by norm_num)] with n hn hn2
      have hl := Complex.norm_log_one_add_sub_self_le (z := w n) (by linarith)
      simp only [hε, norm_mul, Complex.norm_natCast] at hn ⊢
      have h1 : ‖w n‖ ^ 2 * (1 - ‖w n‖)⁻¹ / 2 ≤ ‖w n‖ ^ 2 := by
        have : (1 - ‖w n‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) two_pos]; linarith
        nlinarith [sq_nonneg ‖w n‖, inv_pos.2 (show (0 : ℝ) < 1 - ‖w n‖ by linarith)]
      calc (n : ℝ) * ‖Complex.log (1 + w n) - w n‖ ≤ n * ‖w n‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (hl.trans h1) (Nat.cast_nonneg _)
        _ = (n * ‖w n‖) * ‖w n‖ := by ring
        _ ≤ C * ‖w n‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    have := hw0.const_mul C
    rw [mul_zero] at this
    exact squeeze_zero_norm' hb this
  have hE : Tendsto (fun n => Complex.exp (ε n) - 1) atTop (𝓝 0) := by
    have := ((Complex.continuous_exp.tendsto 0).comp hε0).sub_const 1
    simpa using this
  have hbound : ∀ᶠ n : ℕ in atTop, ‖(1 + w n) ^ n - Complex.exp (n * w n)‖ ≤
      Real.exp C * ‖Complex.exp (ε n) - 1‖ := by
    filter_upwards [hC, (tendsto_order.1 hw0).2 (1 / 2) (by norm_num)] with n hn hn2
    have h1 : (1 : ℂ) + w n ≠ 0 := by
      intro h
      have : w n = -1 := by linear_combination h
      rw [this, norm_neg, norm_one] at hn2; norm_num at hn2
    have hpow : (1 + w n) ^ n = Complex.exp (n * w n) * Complex.exp (ε n) := by
      rw [← Complex.exp_add, hε]
      rw [show (n : ℂ) * w n + (n : ℂ) * (Complex.log (1 + w n) - w n) =
        (n : ℂ) * Complex.log (1 + w n) by ring, Complex.exp_nat_mul, Complex.exp_log h1]
    rw [hpow, ← mul_sub_one, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 hn)
  have := (hE.norm.const_mul (Real.exp C))
  rw [norm_zero, mul_zero] at this
  exact squeeze_zero_norm' hbound this

end PowExp

section SecondDifference

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

/-- The second differences `Dₙ(t, s) = n (wₙ(t + s) + wₙ(t - s) - 2 wₙ(t))`. -/
noncomputable def dfun (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ)
    (t s : ℝ) : ℂ :=
  n * (wfun μ a n (t + s) + wfun μ a n (t - s) - 2 * wfun μ a n t)

omit [IsProbabilityMeasure μ] in
theorem charFun_cLaw_eq (n : ℕ) (t : ℝ) :
    charFun (cLaw μ a n) t = charFun μ ((a n)⁻¹ * t) *
      Complex.exp ((-ctr μ a n : ℝ) * t * Complex.I) := by
  have : (fun x => (a n)⁻¹ * x - ctr μ a n) = fun x => (a n)⁻¹ * x + (-ctr μ a n) := by
    funext x; ring
  rw [cLaw, this, charFun_map_mul_add]

/-- The characteristic function of `(Sₙ - bₙ) / aₙ` in terms of the centered one. -/
theorem charFun_sum_eq (n : ℕ) (t : ℝ) :
    charFun ((convPow μ n).map (fun x => (a n)⁻¹ * (x - b n))) t =
      (1 + wfun μ a n t) ^ n *
        Complex.exp (((t * (n * ctr μ a n - (a n)⁻¹ * b n)) : ℝ) * Complex.I) := by
  have hf : (fun x => (a n)⁻¹ * (x - b n)) = fun x => (a n)⁻¹ * x + (-((a n)⁻¹ * b n)) := by
    funext x; ring
  have h1 : charFun μ ((a n)⁻¹ * t) = (1 + wfun μ a n t) *
      Complex.exp ((ctr μ a n : ℝ) * t * Complex.I) := by
    rw [wfun, add_sub_cancel, charFun_cLaw_eq, mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  rw [hf, charFun_map_mul_add, charFun_convPow, h1, mul_pow, ← Complex.exp_nat_mul,
    mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

variable {ν : ProbabilityMeasure ℝ}

/-- **Second differences of the logarithms converge**: if `(Sₙ - bₙ) / aₙ → ν` and `n wₙ` is
locally bounded, then `exp Dₙ(t, s) → φ(t + s) φ(t - s) / φ(t)²`, `φ = φ_ν`. -/
theorem tendsto_exp_dfun
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    (hφ : ∀ t, charFun (ν : Measure ℝ) t ≠ 0)
    (hw : ∀ t, ∃ C, ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * wfun μ a n t‖ ≤ C) (t s : ℝ) :
    Tendsto (fun n => Complex.exp (dfun μ a n t s)) atTop
      (𝓝 (charFun (ν : Measure ℝ) (t + s) * charFun (ν : Measure ℝ) (t - s) /
        charFun (ν : Measure ℝ) t ^ 2)) := by
  have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hconv
  set γ : ℕ → ℝ := fun n => n * ctr μ a n - (a n)⁻¹ * b n
  set E : ℕ → ℝ → ℂ := fun n u => Complex.exp (n * wfun μ a n u) *
    Complex.exp (((u * γ n) : ℝ) * Complex.I)
  have hE : ∀ u, Tendsto (fun n => E n u) atTop (𝓝 (charFun (ν : Measure ℝ) u)) := by
    intro u
    obtain ⟨C, hC⟩ := hw u
    have hd := tendsto_one_add_pow_sub_exp hC
    have h1 := hcf u
    simp only [ProbabilityMeasure.coe_mk, charFun_sum_eq] at h1
    have h2 : Tendsto (fun n => ((1 + wfun μ a n u) ^ n - Complex.exp (n * wfun μ a n u)) *
        Complex.exp (((u * γ n) : ℝ) * Complex.I)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by simpa using hd.norm)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have := h1.sub h2
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    simp only [E, γ]
    ring
  have hkey : ∀ n, Complex.exp (dfun μ a n t s) = E n (t + s) * E n (t - s) / E n t ^ 2 := by
    intro n
    have hne : E n t ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    rw [eq_div_iff (pow_ne_zero 2 hne)]
    simp only [E, dfun]
    simp only [← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hkey]
  exact ((hE (t + s)).mul (hE (t - s))).div ((hE t).pow 2) (pow_ne_zero 2 (hφ t))

end SecondDifference

section DfunBound

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

theorem one_sub_cos_le_two_mul_min (θ : ℝ) : 1 - Real.cos θ ≤ 2 * min 1 (θ ^ 2) := by
  rcases le_total 1 (θ ^ 2) with h | h
  · rw [min_eq_left h]; linarith [Real.neg_one_le_cos θ]
  · rw [min_eq_right h]; nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ)]

theorem min_one_sq_sub_le (u v : ℝ) : min 1 ((u - v) ^ 2) ≤ 2 * min 1 (u ^ 2) + 2 * v ^ 2 := by
  rcases le_total 1 (u ^ 2) with h | h
  · rw [min_eq_left h]; nlinarith [min_le_left 1 ((u - v) ^ 2), sq_nonneg v]
  · rw [min_eq_right h]; nlinarith [min_le_right 1 ((u - v) ^ 2), sq_nonneg (u + v)]

omit [IsProbabilityMeasure μ] in
theorem sqRatio_eq_integral_min' {c : ℝ} (hc : c ≠ 0) :
    sqRatio μ c = ∫ x, min 1 ((c⁻¹ * x) ^ 2) ∂μ := by
  rw [sqRatio]; simp_rw [sq_div_max_eq_min hc]

/-- `Dₙ(t, s) = -2n ∫ (1 - cos (s z)) e^{itz} dρₙ(z)`, `ρₙ = law (X / aₙ - τₙ)`. -/
theorem dfun_eq (n : ℕ) (t s : ℝ) :
    dfun μ a n t s = -(2 * n : ℂ) * ∫ z, ((1 - Real.cos (s * z) : ℝ) : ℂ) *
      Complex.exp (t * z * Complex.I) ∂(cLaw μ a n) := by
  have hexp : ∀ u : ℝ, Integrable (fun y : ℝ => Complex.exp (u * y * Complex.I))
      (cLaw μ a n) := fun u =>
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun y => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I])
  have e : ∀ z : ℝ, ((1 - Real.cos (s * z) : ℝ) : ℂ) * Complex.exp (t * z * Complex.I) =
      Complex.exp (t * z * Complex.I) - (Complex.exp ((t + s) * z * Complex.I) +
        Complex.exp ((t - s) * z * Complex.I)) / 2 := by
    intro z
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul, cos_mul_exp_eq]
  simp_rw [e]
  have h1 := hexp (t + s)
  have h2 := hexp (t - s)
  push_cast at h1 h2
  have h12 : Integrable (fun y : ℝ => (Complex.exp ((t + s) * y * Complex.I) +
      Complex.exp ((t - s) * y * Complex.I)) / 2) (cLaw μ a n) := (h1.add h2).div_const 2
  rw [integral_sub (hexp t) h12, integral_div, integral_add h1 h2]
  simp only [dfun, wfun, charFun_apply_real]
  push_cast
  ring

/-- `|Dₙ(t, s)| ≤ 8 n E[min (1, (s X / aₙ)²)] + 8 s² n E[min (1, (X / aₙ)²)]`. -/
theorem norm_dfun_le {n : ℕ} (ha : a n ≠ 0) {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    ‖dfun μ a n t s‖ ≤ 8 * (n * sqRatio μ (a n / s)) + 8 * s ^ 2 * (n * sqRatio μ (a n)) := by
  set τ := ctr μ a n
  have hint : Integrable (fun z : ℝ => 1 - Real.cos (s * z)) (cLaw μ a n) :=
    (integrable_const 1).sub (Integrable.of_bound (by fun_prop) 1
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
  have hnorm : ‖∫ z, ((1 - Real.cos (s * z) : ℝ) : ℂ) * Complex.exp (t * z * Complex.I)
      ∂(cLaw μ a n)‖ ≤ ∫ z, (1 - Real.cos (s * z)) ∂(cLaw μ a n) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
      (ae_of_all _ fun z => ?_)))
    dsimp only
    rw [norm_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.cos_le_one (s * z)])]
  have hS := ctr_sq_le (μ := μ) ha
  have hτ2 : τ ^ 2 ≤ sqRatio μ (a n) := hS
  have hbd : ∫ z, (1 - Real.cos (s * z)) ∂(cLaw μ a n) ≤
      4 * sqRatio μ (a n / s) + 4 * s ^ 2 * sqRatio μ (a n) := by
    rw [cLaw, integral_map (by fun_prop) (by fun_prop)]
    have hm : Integrable (fun x => min 1 (((a n / s)⁻¹ * x) ^ 2)) μ :=
      Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (sq_nonneg _))]
        exact min_le_left _ _)
    calc ∫ x, (1 - Real.cos (s * ((a n)⁻¹ * x - τ))) ∂μ
        ≤ ∫ x, (4 * min 1 (((a n / s)⁻¹ * x) ^ 2) + 4 * s ^ 2 * τ ^ 2) ∂μ := by
          refine integral_mono ((integrable_const 1).sub (Integrable.of_bound (by fun_prop) 1
            (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)))
            ((hm.const_mul 4).add (integrable_const _)) fun x => ?_
          have h1 := one_sub_cos_le_two_mul_min (s * ((a n)⁻¹ * x - τ))
          have h2 := min_one_sq_sub_le (s * ((a n)⁻¹ * x)) (s * τ)
          have e1 : s * ((a n)⁻¹ * x - τ) = s * ((a n)⁻¹ * x) - s * τ := by ring
          have e2 : (a n / s)⁻¹ * x = s * ((a n)⁻¹ * x) := by
            rw [inv_div]; field_simp
          rw [e1] at h1
          rw [e1, e2]
          nlinarith
      _ = 4 * sqRatio μ (a n / s) + 4 * s ^ 2 * τ ^ 2 := by
          rw [integral_add (hm.const_mul 4) (integrable_const _), integral_const_mul,
            integral_const, probReal_univ, one_smul,
            sqRatio_eq_integral_min' (div_ne_zero ha hs)]
      _ ≤ _ := by nlinarith [sq_nonneg s]
  rw [dfun_eq, norm_mul, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc 2 * (n : ℝ) * ‖∫ z, ((1 - Real.cos (s * z) : ℝ) : ℂ) * Complex.exp (t * z * Complex.I)
        ∂(cLaw μ a n)‖ ≤ 2 * n * (4 * sqRatio μ (a n / s) + 4 * s ^ 2 * sqRatio μ (a n)) :=
        mul_le_mul_of_nonneg_left (hnorm.trans hbd) (by positivity)
    _ = _ := by ring

/-- **Uniform smallness of the second differences**: if `n E[min (1, (X / aₙ)²)]` is bounded
and `n E[min (1, (s X / aₙ)²)]` is uniformly small for small `s`, then there is `s₀ > 0` with
`|Dₙ(t, s)| ≤ 1` for all `t`, `0 ≤ s ≤ s₀` and `n` large. -/
theorem exists_forall_norm_dfun_le (ha : ∀ n, 0 < a n)
    (hS : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio μ (a n) ≤ C)
    (hsmall : ∀ η > 0, ∃ s₀ > 0, ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio μ (a n / s₀) ≤ η) :
    ∃ s₀ > 0, ∀ᶠ n : ℕ in atTop, ∀ t s, 0 ≤ s → s ≤ s₀ → ‖dfun μ a n t s‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := hS
  obtain ⟨s₁, hs₁, hη⟩ := hsmall (1 / 16) (by norm_num)
  set C' := max C 0 + 1
  have hC' : 0 < C' := by positivity
  set s₀ := min (min s₁ 1) (1 / (16 * C'))
  have hs₀ : 0 < s₀ := by positivity
  refine ⟨s₀, hs₀, ?_⟩
  filter_upwards [hC, hη] with n hn hn' t s hs0 hss
  rcases hs0.lt_or_eq with hs | hs
  · refine (norm_dfun_le (ha n).ne' hs.ne' t).trans ?_
    have h1 : sqRatio μ (a n / s) ≤ sqRatio μ (a n / s₁) := by
      refine sqRatio_antitoneOn (div_pos (ha n) hs₁) (div_pos (ha n) hs) ?_
      exact div_le_div_of_nonneg_left (ha n).le hs (hss.trans ((min_le_left _ _).trans
        (min_le_left _ _)))
    have h2 : (n : ℝ) * sqRatio μ (a n / s) ≤ 1 / 16 :=
      (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)).trans hn'
    have hs1 : s ≤ 1 := hss.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hsC : s ≤ 1 / (16 * C') := hss.trans (min_le_right _ _)
    have hnC : (n : ℝ) * sqRatio μ (a n) ≤ C' := hn.trans (by
      simp only [C']; linarith [le_max_left C 0])
    have hnn : 0 ≤ (n : ℝ) * sqRatio μ (a n) :=
      mul_nonneg (Nat.cast_nonneg n) (sqRatio_nonneg _)
    have h3 : s ^ 2 * ((n : ℝ) * sqRatio μ (a n)) ≤ 1 / 16 := by
      have : s * C' ≤ 1 / 16 := by
        rw [le_div_iff₀ (by positivity)] at hsC; nlinarith
      calc s ^ 2 * ((n : ℝ) * sqRatio μ (a n)) ≤ s * (s * C') := by
            rw [sq, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnC hs.le) hs.le
        _ ≤ 1 * (1 / 16) := mul_le_mul hs1 this (by positivity) zero_le_one
        _ = 1 / 16 := one_mul _
    nlinarith
  · subst hs
    simp only [dfun, add_zero, sub_zero]
    ring_nf
    simp

variable {ν : ProbabilityMeasure ℝ}

/-- **Logarithmic second differences**: under the hypotheses of `tendsto_exp_dfun`, if
`|Dₙ(t, s)| ≤ 1` eventually, then `R(t, s) = φ(t + s) φ(t - s) / φ(t)²` has positive real part
and `Dₙ(t, s) → log R(t, s)`. -/
theorem tendsto_dfun_log
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    (hφ : ∀ t, charFun (ν : Measure ℝ) t ≠ 0)
    (hw : ∀ t, ∃ C, ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * wfun μ a n t‖ ≤ C) {t s : ℝ}
    (hD : ∀ᶠ n : ℕ in atTop, ‖dfun μ a n t s‖ ≤ 1) :
    Real.exp (-1) * Real.cos 1 ≤ (charFun (ν : Measure ℝ) (t + s) * charFun (ν : Measure ℝ)
        (t - s) / charFun (ν : Measure ℝ) t ^ 2).re ∧
      Tendsto (fun n => dfun μ a n t s) atTop
        (𝓝 (Complex.log (charFun (ν : Measure ℝ) (t + s) * charFun (ν : Measure ℝ) (t - s) /
          charFun (ν : Measure ℝ) t ^ 2))) := by
  set R := charFun (ν : Measure ℝ) (t + s) * charFun (ν : Measure ℝ) (t - s) /
    charFun (ν : Measure ℝ) t ^ 2
  have hE := tendsto_exp_dfun hconv hφ hw t s
  have hre : Real.exp (-1) * Real.cos 1 ≤ R.re := by
    refine ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hE) ?_
    filter_upwards [hD] with n hn
    simp only [Function.comp, Complex.exp_re]
    have him : |(dfun μ a n t s).im| ≤ 1 := (Complex.abs_im_le_norm _).trans hn
    have hre' : -1 ≤ (dfun μ a n t s).re :=
      (abs_le.1 ((Complex.abs_re_le_norm _).trans hn)).1
    have hcos : Real.cos 1 ≤ Real.cos (dfun μ a n t s).im := by
      rw [← Real.cos_abs (dfun μ a n t s).im]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
        him
    have hcos1 : 0 ≤ Real.cos 1 :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by
        linarith [Real.pi_gt_three]⟩
    exact mul_le_mul (Real.exp_le_exp.2 hre') hcos hcos1 (Real.exp_pos _).le
  have hpos : 0 < R.re := lt_of_lt_of_le (mul_pos (Real.exp_pos _)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by
      linarith [Real.pi_gt_three]⟩)) hre
  refine ⟨hre, ?_⟩
  have hlog := ((continuousAt_clog (Complex.mem_slitPlane_iff.2 (Or.inl hpos))).tendsto
    ).comp hE
  refine hlog.congr' ?_
  filter_upwards [hD] with n hn
  have him : |(dfun μ a n t s).im| ≤ 1 := (Complex.abs_im_le_norm _).trans hn
  simp only [Function.comp]
  rw [Complex.log_exp (by linarith [abs_le.1 him, Real.pi_gt_three])
    (by linarith [abs_le.1 him, Real.pi_gt_three])]

end DfunBound

section Kern

variable {s₀ : ℝ}

/-- The kernel `k(z) = ∫₀^{s₀} (1 - cos (s z)) ds = s₀ - sin (s₀ z) / z`. -/
noncomputable def kern (s₀ z : ℝ) : ℝ := ∫ s in (0 : ℝ)..s₀, (1 - Real.cos (s * z))

theorem continuous_kern : Continuous (kern s₀) := by
  unfold kern
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun z s => 1 - Real.cos (s * z)) (by fun_prop) 0 s₀

theorem kern_eq (z : ℝ) (hz : z ≠ 0) : kern s₀ z = s₀ - Real.sin (s₀ * z) / z := by
  have hi : IntervalIntegrable (fun s : ℝ => Real.cos (s * z)) volume 0 s₀ :=
    (by fun_prop : Continuous fun s : ℝ => Real.cos (s * z)).intervalIntegrable _ _
  rw [kern, intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one]
  have : ∫ s in (0 : ℝ)..s₀, Real.cos (s * z) = ∫ s in (0 : ℝ)..s₀, Real.cos (z * s) := by
    congr 1; funext s; rw [mul_comm]
  rw [this, intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hz, integral_cos,
    mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, mul_comm z s₀, inv_mul_eq_div]

theorem kern_nonneg (hs₀ : 0 ≤ s₀) (z : ℝ) : 0 ≤ kern s₀ z :=
  intervalIntegral.integral_nonneg hs₀ fun s _ => by linarith [Real.cos_le_one (s * z)]

theorem kern_le (hs₀ : 0 ≤ s₀) (z : ℝ) : kern s₀ z ≤ 2 * s₀ := by
  have h := intervalIntegral.integral_mono_on hs₀
    ((by fun_prop : Continuous fun s : ℝ => 1 - Real.cos (s * z)).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume) (c := (2 : ℝ))) fun s _ => by linarith [Real.neg_one_le_cos (s * z)]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  unfold kern; linarith

theorem kern_pos (hs₀ : 0 < s₀) {z : ℝ} (hz : z ≠ 0) : 0 < kern s₀ z := by
  rw [kern_eq z hz, sub_pos]
  rcases lt_or_gt_of_ne hz with h | h
  · rw [div_lt_iff_of_neg h]
    have := Real.sin_lt (show 0 < s₀ * -z by nlinarith)
    rw [mul_neg, Real.sin_neg] at this
    linarith
  · rw [div_lt_iff₀ h]
    exact Real.sin_lt (by positivity)

/-- `k` is bounded below away from `0`. -/
theorem exists_le_kern (hs₀ : 0 < s₀) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ c > 0, ∀ z, x₀ ≤ |z| → c ≤ kern s₀ z := by
  set R := max x₀ (2 / s₀)
  have hK : IsCompact {z : ℝ | x₀ ≤ |z| ∧ |z| ≤ R} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · refine (Metric.isBounded_Icc (-R) R).subset fun z hz => ?_
      exact abs_le.1 hz.2
  have hne : ({z : ℝ | x₀ ≤ |z| ∧ |z| ≤ R}).Nonempty :=
    ⟨x₀, by simp [abs_of_pos hx₀, R]⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_kern.continuousOn
  have hz₀0 : z₀ ≠ 0 := by
    rintro rfl; simp at hz₀; linarith [hz₀.1]
  refine ⟨min (kern s₀ z₀) (s₀ / 2), lt_min (kern_pos hs₀ hz₀0) (by positivity), fun z hz => ?_⟩
  by_cases hzR : |z| ≤ R
  · exact (min_le_left _ _).trans (hmin ⟨hz, hzR⟩)
  · refine (min_le_right _ _).trans ?_
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
    have hzR' : 2 / s₀ < |z| := lt_of_le_of_lt (le_max_right _ _) (not_le.1 hzR)
    rw [kern_eq z hz0]
    have h1 : |Real.sin (s₀ * z) / z| ≤ 1 / |z| := by
      rw [abs_div]; exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
    have h2 : 1 / |z| ≤ s₀ / 2 := by
      rw [div_le_iff₀ (abs_pos.2 hz0)]
      rw [div_lt_iff₀ hs₀] at hzR'
      linarith
    linarith [le_abs_self (Real.sin (s₀ * z) / z)]

end Kern

section KernMeasure

variable {s₀ : ℝ}

/-- `ρ` weighted by the kernel `k`. -/
noncomputable def kernMeasure (s₀ : ℝ) (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity fun z => ((kern s₀ z).toNNReal : ℝ≥0∞)

theorem measurable_kern_toNNReal : Measurable fun z => (kern s₀ z).toNNReal :=
  continuous_kern.measurable.real_toNNReal

instance (ρ : Measure ℝ) [IsFiniteMeasure ρ] : IsFiniteMeasure (kernMeasure s₀ ρ) := by
  refine isFiniteMeasure_withDensity ?_
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := (2 * |s₀|).toNNReal))
    (measure_ne_top ρ univ)) ?_
  calc ∫⁻ z, ((kern s₀ z).toNNReal : ℝ≥0∞) ∂ρ ≤ ∫⁻ _z, ((2 * |s₀|).toNNReal : ℝ≥0∞) ∂ρ :=
        lintegral_mono fun z => by
          refine ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ?_)
          rcases le_total 0 s₀ with h | h
          · rw [abs_of_nonneg h]; exact kern_le h z
          · have : kern s₀ z ≤ 0 := by
              rw [kern, intervalIntegral.integral_symm]
              exact neg_nonpos.2 (intervalIntegral.integral_nonneg h fun s _ => by
                linarith [Real.cos_le_one (s * z)])
            linarith [abs_nonneg s₀]
    _ = _ := by rw [lintegral_const]

theorem integral_kernMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hs₀ : 0 ≤ s₀) (ρ : Measure ℝ) (g : ℝ → E) :
    ∫ z, g z ∂(kernMeasure s₀ ρ) = ∫ z, kern s₀ z • g z ∂ρ := by
  rw [kernMeasure, integral_withDensity_eq_integral_smul measurable_kern_toNNReal]
  congr 1; funext z
  rw [NNReal.smul_def, Real.coe_toNNReal _ (kern_nonneg hs₀ z)]

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

/-- **Characteristic function of the kernel measure**:
`φ_{k ρₙ}(t) = ∫₀^{s₀} -Dₙ(t, s) / (2n) ds`. -/
theorem charFun_kernMeasure (hs₀ : 0 ≤ s₀) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    charFun (kernMeasure s₀ (cLaw μ a n)) t =
      ∫ s in (0 : ℝ)..s₀, -dfun μ a n t s / (2 * n) := by
  set ρ := cLaw μ a n
  set F : ℝ → ℝ → ℂ := fun z s => ((1 - Real.cos (s * z) : ℝ) : ℂ) *
    Complex.exp (t * z * Complex.I)
  have hF : Continuous (Function.uncurry F) := by
    simp only [F]; fun_prop
  have hint : Integrable (Function.uncurry F) (ρ.prod (volume.restrict (Ioc 0 s₀))) := by
    refine Integrable.of_bound hF.aestronglyMeasurable 2 (ae_of_all _ fun p => ?_)
    obtain ⟨z, s⟩ := p
    simp only [Function.uncurry_apply_pair, F, norm_mul, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> linarith [Real.cos_le_one (s * z), Real.neg_one_le_cos (s * z)]
  have hk : ∀ z, kern s₀ z • Complex.exp (t * z * Complex.I) = ∫ s in Ioc 0 s₀, F z s := by
    intro z
    rw [kern, intervalIntegral.integral_of_le hs₀, Complex.real_smul, ← integral_complex_ofReal,
      ← integral_mul_const]
  rw [charFun_apply_real, integral_kernMeasure hs₀]
  simp_rw [hk]
  rw [integral_integral_swap hint, intervalIntegral.integral_of_le hs₀]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [dfun_eq]
  field_simp
  ring

end KernMeasure

section LevyLimit

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ} {ν : ProbabilityMeasure ℝ}
  {s₀ : ℝ}

/-- `R(t, s) = φ(t + s) φ(t - s) / φ(t)²`. -/
noncomputable def rfun (ν : Measure ℝ) (t s : ℝ) : ℂ :=
  charFun ν (t + s) * charFun ν (t - s) / charFun ν t ^ 2

/-- The limit transform `λ(t) = ∫₀^{s₀} -log R(t, s) / 2 ds`. -/
noncomputable def lamK (ν : Measure ℝ) (s₀ t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..s₀, -Complex.log (rfun ν t s) / 2

theorem continuous_wfun (n : ℕ) : Continuous (wfun μ a n) := by
  unfold wfun; have := continuous_charFun (μ := cLaw μ a n); fun_prop

theorem continuous_dfun (n : ℕ) (t : ℝ) : Continuous (dfun μ a n t) := by
  unfold dfun; have := continuous_wfun (μ := μ) (a := a) n; fun_prop

/-- Local boundedness of `n wₙ` from the bound on `n E[min (1, (X / aₙ)²)]`. -/
theorem exists_norm_mul_wfun_le (ha : ∀ n, 0 < a n)
    (hS : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio μ (a n) ≤ C) (t : ℝ) :
    ∃ C, ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * wfun μ a n t‖ ≤ C := by
  obtain ⟨C, hC⟩ := hS
  refine ⟨(12 * t ^ 2 + 2 * |t| + 2) * C, hC.mono fun n hn => ?_⟩
  rw [norm_mul, Complex.norm_natCast]
  calc (n : ℝ) * ‖wfun μ a n t‖ ≤ n * ((12 * t ^ 2 + 2 * |t| + 2) * sqRatio μ (a n)) :=
        mul_le_mul_of_nonneg_left (norm_wfun_le (ha n).ne' t) (Nat.cast_nonneg n)
    _ = (12 * t ^ 2 + 2 * |t| + 2) * (n * sqRatio μ (a n)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

variable (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
  (hφ : ∀ t, charFun (ν : Measure ℝ) t ≠ 0)
  (hw : ∀ t, ∃ C, ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * wfun μ a n t‖ ≤ C)
  (hD : ∀ᶠ n : ℕ in atTop, ∀ t s, 0 ≤ s → s ≤ s₀ → ‖dfun μ a n t s‖ ≤ 1)
include hconv hφ hw hD

theorem tendsto_dfun_log' {t s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₀) :
    Real.exp (-1) * Real.cos 1 ≤ (rfun ν t s).re ∧
      Tendsto (fun n => dfun μ a n t s) atTop (𝓝 (Complex.log (rfun ν t s))) :=
  tendsto_dfun_log hconv hφ hw (hD.mono fun _ hn => hn t s hs0 hs)

theorem norm_log_rfun_le {t s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₀) :
    ‖Complex.log (rfun ν t s)‖ ≤ 1 :=
  le_of_tendsto (tendsto_dfun_log' hconv hφ hw hD hs0 hs).2.norm
    (hD.mono fun _ hn => hn t s hs0 hs)

/-- `n φ_{k ρₙ}(t) → λ(t)`. -/
theorem tendsto_mul_charFun_kernMeasure (hs₀ : 0 ≤ s₀) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * charFun (kernMeasure s₀ (cLaw μ a n)) t) atTop
      (𝓝 (lamK (ν : Measure ℝ) s₀ t)) := by
  have he : ∀ᶠ n : ℕ in atTop, (n : ℂ) * charFun (kernMeasure s₀ (cLaw μ a n)) t =
      ∫ s in (0 : ℝ)..s₀, -dfun μ a n t s / 2 := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [charFun_kernMeasure hs₀ hn, ← intervalIntegral.integral_const_mul]
    congr 1; funext s; field_simp
  refine Tendsto.congr' (EventuallyEq.symm he) ?_
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1 / 2)
    (Eventually.of_forall fun n => ((continuous_dfun n t).neg.div_const 2).aestronglyMeasurable)
    ?_ intervalIntegrable_const (ae_of_all _ fun s hs => ?_)
  · filter_upwards [hD] with n hn
    refine ae_of_all _ fun s hs => ?_
    rw [Set.uIoc_of_le hs₀] at hs
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith [hn t s hs.1.le hs.2]
  · rw [Set.uIoc_of_le hs₀] at hs
    exact ((tendsto_dfun_log' hconv hφ hw hD hs.1.le hs.2).2.neg).div_const 2

theorem continuousAt_lamK (hs₀ : 0 ≤ s₀) : ContinuousAt (lamK (ν : Measure ℝ) s₀) 0 := by
  have hRc : ∀ s, Continuous fun t => rfun (ν : Measure ℝ) t s := by
    intro s
    have hc := continuous_charFun (μ := (ν : Measure ℝ))
    exact ((hc.comp (continuous_id.add continuous_const)).mul
      (hc.comp (continuous_id.sub continuous_const))).div (hc.pow 2)
      fun t => pow_ne_zero 2 (hφ t)
  have hRs : ∀ t, Continuous fun s => rfun (ν : Measure ℝ) t s := by
    intro t
    have hc := continuous_charFun (μ := (ν : Measure ℝ))
    exact ((hc.comp (continuous_const.add continuous_id)).mul
      (hc.comp (continuous_const.sub continuous_id))).div continuous_const
      fun _ => pow_ne_zero 2 (hφ t)
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => 1 / 2)
    (Eventually.of_forall fun t => ((Complex.measurable_log.comp (hRs t).measurable).neg.div_const
      2).aestronglyMeasurable) (Eventually.of_forall fun t => ae_of_all _ fun s hs => ?_)
    intervalIntegrable_const (ae_of_all _ fun s hs => ?_)
  · rw [Set.uIoc_of_le hs₀] at hs
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith [norm_log_rfun_le hconv hφ hw hD (t := t) hs.1.le hs.2]
  · rw [Set.uIoc_of_le hs₀] at hs
    have hpos : 0 < (rfun (ν : Measure ℝ) 0 s).re := lt_of_lt_of_le (mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by
        linarith [Real.pi_gt_three]⟩)) (tendsto_dfun_log' hconv hφ hw hD hs.1.le hs.2).1
    have h1 : ContinuousAt (fun t => Complex.log (rfun (ν : Measure ℝ) t s)) 0 :=
      ContinuousAt.comp (x := (0 : ℝ)) (g := Complex.log)
        (continuousAt_clog (Complex.mem_slitPlane_iff.2 (Or.inl hpos))) (hRc s).continuousAt
    exact h1.neg.div_const 2

omit hconv hφ hw hD in
omit [IsProbabilityMeasure μ] in
theorem measureReal_univ_kernMeasure (hs₀ : 0 ≤ s₀) (n : ℕ) :
    (kernMeasure s₀ (cLaw μ a n)).real univ = ∫ z, kern s₀ z ∂(cLaw μ a n) := by
  have h := integral_kernMeasure hs₀ (cLaw μ a n) (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  exact h

omit hconv hφ hw hD in
/-- The mass of the kernel measure is at least `c P(|X| > 2 aₙ)`. -/
theorem le_measureReal_univ_kernMeasure (hs₀ : 0 < s₀) {c : ℝ}
    (hc : ∀ z, 1 ≤ |z| → c ≤ kern s₀ z) {n : ℕ} (ha : 0 < a n) :
    c * absTail μ (2 * a n) ≤ (kernMeasure s₀ (cLaw μ a n)).real univ := by
  rw [measureReal_univ_kernMeasure hs₀.le, cLaw, integral_map (by fun_prop)
    continuous_kern.aestronglyMeasurable]
  have hτ := abs_ctr_le (μ := μ) (a := a) n
  calc c * absTail μ (2 * a n) = ∫ x, {y : ℝ | 2 * a n < |y|}.indicator (fun _ => c) x ∂μ := by
        rw [integral_indicator_const _ (measurableSet_abs_gt _), smul_eq_mul, mul_comm]; rfl
    _ ≤ ∫ x, kern s₀ ((a n)⁻¹ * x - ctr μ a n) ∂μ := by
        refine integral_mono ((integrable_const c).indicator (measurableSet_abs_gt _))
          (Integrable.of_bound ((continuous_kern.comp (by fun_prop : Continuous fun x : ℝ =>
            (a n)⁻¹ * x - ctr μ a n)).aestronglyMeasurable)
            (2 * s₀) (ae_of_all _ fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg hs₀.le _)]
              exact kern_le hs₀.le _)) fun x => ?_
        by_cases hx : 2 * a n < |x|
        · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | 2 * a n < |y|} from hx)]
          refine hc _ ?_
          have h1 : 2 < |(a n)⁻¹ * x| := by
            rw [abs_mul, abs_inv, abs_of_pos ha, ← div_eq_inv_mul, lt_div_iff₀ ha]
            linarith
          have := abs_sub_abs_le_abs_sub ((a n)⁻¹ * x) (ctr μ a n)
          linarith
        · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | 2 * a n < |y|} from hx)]
          exact kern_nonneg hs₀.le _

/-- The normalized kernel measures `k ρₙ / (k ρₙ)(ℝ)`. -/
noncomputable def kernNorm (s₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ → ℝ)
    (n : ℕ) : ProbabilityMeasure ℝ :=
  FiniteMeasure.normalize ⟨kernMeasure s₀ (cLaw μ a n), inferInstance⟩

omit hconv hφ hw hD in
theorem kernNorm_eq {n : ℕ} (h0 : 0 < (kernMeasure s₀ (cLaw μ a n)).real univ) :
    (kernNorm s₀ μ a n : Measure ℝ) =
      ((kernMeasure s₀ (cLaw μ a n)).real univ).toNNReal⁻¹ • kernMeasure s₀ (cLaw μ a n) := by
  set Λ : FiniteMeasure ℝ := ⟨kernMeasure s₀ (cLaw μ a n), inferInstance⟩
  have hmass : (Λ.mass : ℝ) = (kernMeasure s₀ (cLaw μ a n)).real univ := by
    rw [measureReal_def, ← ENNReal.coe_toReal, FiniteMeasure.ennreal_mass]
    rfl
  have hne : Λ ≠ 0 := by
    refine (FiniteMeasure.mass_nonzero_iff _).1 fun hz => ?_
    rw [hz] at hmass
    simp only [NNReal.coe_zero] at hmass
    linarith
  rw [kernNorm, FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hne]
  congr 2
  rw [← hmass, Real.toNNReal_coe]

omit hconv hφ hw hD in
theorem integral_kernNorm {n : ℕ} (h0 : 0 < (kernMeasure s₀ (cLaw μ a n)).real univ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ z, g z ∂(kernNorm s₀ μ a n : Measure ℝ) =
      ((kernMeasure s₀ (cLaw μ a n)).real univ)⁻¹ • ∫ z, g z ∂(kernMeasure s₀ (cLaw μ a n)) := by
  rw [kernNorm_eq h0, integral_smul_nnreal_measure, NNReal.smul_def]
  simp only [NNReal.coe_inv, Real.coe_toNNReal _ h0.le]

/-- **Convergence of the canonical measures.** Under the standing hypotheses, together with the
lower bound `n P(|X| > 2 aₙ) ≥ c > 0`, there are `L₀ > 0` and a probability measure `P` with
`n ∫ k(z) g(z) dρₙ(z) → L₀ ∫ g dP` for every bounded continuous `g`. -/
theorem exists_tendsto_mul_integral_kern (ha : ∀ n, 0 < a n) (hs₀ : 0 < s₀)
    (hlow : ∃ c > 0, ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) * absTail μ (2 * a n)) :
    ∃ L₀ > 0, ∃ P : ProbabilityMeasure ℝ, ∀ g : ℝ →ᵇ ℝ,
      Tendsto (fun n : ℕ => (n : ℝ) * ∫ z, kern s₀ z * g z ∂(cLaw μ a n)) atTop
        (𝓝 (L₀ * ∫ z, g z ∂(P : Measure ℝ))) := by
  obtain ⟨c, hc, hlow⟩ := hlow
  obtain ⟨ck, hck, hk⟩ := exists_le_kern hs₀ one_pos
  set r : ℕ → ℝ := fun n => (n : ℝ) * (kernMeasure s₀ (cLaw μ a n)).real univ with hr
  have hr_lim : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (lamK (ν : Measure ℝ) s₀ 0)) := by
    refine (tendsto_mul_charFun_kernMeasure hconv hφ hw hD hs₀.le 0).congr fun n => ?_
    rw [charFun_zero, hr]; push_cast; ring
  have hr_low : ∀ᶠ n : ℕ in atTop, ck * c ≤ r n := by
    filter_upwards [hlow] with n hn
    have h1 := le_measureReal_univ_kernMeasure (μ := μ) hs₀ hk (ha n)
    calc ck * c ≤ ck * ((n : ℝ) * absTail μ (2 * a n)) := mul_le_mul_of_nonneg_left hn hck.le
      _ = n * (ck * absTail μ (2 * a n)) := by ring
      _ ≤ r n := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
  set L₀ := (lamK (ν : Measure ℝ) s₀ 0).re
  have hr_lim' : Tendsto r atTop (𝓝 L₀) := by
    have := (Complex.continuous_re.tendsto _).comp hr_lim
    exact this.congr fun n => by simp
  have hL₀ : ck * c ≤ L₀ := ge_of_tendsto hr_lim' hr_low
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le (mul_pos hck hc) hL₀
  have hlam0 : lamK (ν : Measure ℝ) s₀ 0 = (L₀ : ℂ) := by
    have him := (Complex.continuous_im.tendsto _).comp hr_lim
    have h0 : (lamK (ν : Measure ℝ) s₀ 0).im = 0 :=
      tendsto_nhds_unique him (tendsto_const_nhds.congr fun n => by simp)
    exact Complex.ext rfl (by rw [h0]; simp)
  -- eventually the mass is positive
  have hmass : ∀ᶠ n : ℕ in atTop, 0 < (kernMeasure s₀ (cLaw μ a n)).real univ ∧ 0 < r n := by
    filter_upwards [hr_low, eventually_gt_atTop 0] with n hn hn0
    have hrpos : 0 < r n := lt_of_lt_of_le (mul_pos hck hc) hn
    refine ⟨?_, hrpos⟩
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    by_contra h
    have h' : (kernMeasure s₀ (cLaw μ a n)).real univ = 0 := le_antisymm (not_lt.1 h)
      measureReal_nonneg
    simp only [hr, h', mul_zero] at hrpos
    exact lt_irrefl _ hrpos
  -- characteristic functions of the normalized measures
  have hcf : ∀ t, Tendsto (fun n => charFun (kernNorm s₀ μ a n : Measure ℝ) t) atTop
      (𝓝 (lamK (ν : Measure ℝ) s₀ t / (L₀ : ℂ))) := by
    intro t
    refine ((tendsto_mul_charFun_kernMeasure hconv hφ hw hD hs₀.le t).div hr_lim'.ofReal
      (by exact_mod_cast hL₀pos.ne')).congr' ?_
    filter_upwards [hmass, eventually_gt_atTop 0] with n hn hn0
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [charFun_apply_real, integral_kernNorm hn.1, ← charFun_apply_real, Complex.real_smul, hr]
    push_cast
    have h1 : ((kernMeasure s₀ (cLaw μ a n)).real univ : ℂ) ≠ 0 := by exact_mod_cast hn.1.ne'
    have h2 : (n : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    simp only [Pi.div_apply]
    field_simp
  have hcont : ContinuousAt (fun t => lamK (ν : Measure ℝ) s₀ t / (L₀ : ℂ)) 0 :=
    (continuousAt_lamK hconv hφ hw hD hs₀.le).div_const _
  obtain ⟨P, -, hPlim⟩ := exists_tendsto_of_tendsto_charFun (μ := kernNorm s₀ μ a) hcont hcf
  refine ⟨L₀, hL₀pos, P, fun g => ?_⟩
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hPlim) g
  refine (hr_lim'.mul hint).congr' ?_
  filter_upwards [hmass] with n hn
  rw [integral_kernNorm hn.1, integral_kernMeasure hs₀.le, smul_eq_mul, hr]
  simp only [smul_eq_mul]
  have := hn.1.ne'
  field_simp

end LevyLimit

end GCLTConverse

end ExtremeValueTheory
