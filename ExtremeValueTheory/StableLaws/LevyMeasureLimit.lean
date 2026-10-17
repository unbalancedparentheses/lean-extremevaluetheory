/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverse

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

end GCLTConverse

end ExtremeValueTheory
