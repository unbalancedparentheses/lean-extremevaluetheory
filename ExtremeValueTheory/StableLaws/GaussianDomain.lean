/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.StableIndex

/-!
# The domain of attraction of the normal law

WIP
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

open Subexp GCLT StableIntegral GCLTConverse

section Taylor

/-- `‖e^{iu} - 1 - iu + u² / 2‖ ≤ 4 min (|u|³, u²)`. -/
theorem norm_exp_mul_I_sub_taylor_le (u : ℝ) :
    ‖Complex.exp (u * Complex.I) - 1 - u * Complex.I + ((u ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      4 * min (|u| ^ 3) (u ^ 2) := by
  rcases le_or_gt |u| 1 with h | h
  · have hn : ‖(u : ℂ) * Complex.I‖ = |u| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hb := Complex.exp_bound (x := (u : ℂ) * Complex.I) (hn.le.trans h) (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + u * Complex.I - ((u ^ 2 / 2 : ℝ) : ℂ) := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hs, hn] at hb
    have hmin : min (|u| ^ 3) (u ^ 2) = |u| ^ 3 :=
      min_eq_left (by rw [← sq_abs]; nlinarith [abs_nonneg u, sq_nonneg u])
    rw [hmin]
    have e : Complex.exp (u * Complex.I) - 1 - u * Complex.I + ((u ^ 2 / 2 : ℝ) : ℂ) =
        Complex.exp (u * Complex.I) - (1 + u * Complex.I - ((u ^ 2 / 2 : ℝ) : ℂ)) := by ring
    rw [e]
    refine hb.trans ?_
    norm_num
    nlinarith [pow_nonneg (abs_nonneg u) 3]
  · have hmin : min (|u| ^ 3) (u ^ 2) = u ^ 2 :=
      min_eq_right (by rw [← sq_abs]; nlinarith [abs_nonneg u, sq_nonneg u])
    rw [hmin]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_exp_mul_I_sub_one_sub_le u
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith [sq_nonneg u]

theorem abs_clip_le_abs (y : ℝ) : |clip y| ≤ |y| := by
  rcases le_or_gt |y| 1 with h | h
  · rw [clip_eq_of_abs_le h]
  · exact (abs_clip_le y).trans h.le

theorem clip_sq_eq (y : ℝ) : clip y ^ 2 = min 1 (y ^ 2) := by
  rcases le_or_gt |y| 1 with h | h
  · rw [clip_eq_of_abs_le h, min_eq_right]
    rw [← sq_abs]; nlinarith [abs_nonneg y]
  · rw [min_eq_left (by rw [← sq_abs]; nlinarith [abs_nonneg y])]
    unfold clip
    rcases le_or_gt y 0 with hy | hy
    · rw [abs_of_nonpos hy] at h
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]; norm_num
    · rw [abs_of_pos hy] at h
      rw [min_eq_left h.le, max_eq_right (by norm_num)]; norm_num

end Taylor

section Lindeberg

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

/-- The variance of the truncated variable `clip (X / aₙ)`. -/
noncomputable def clipVar (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∫ x, (clip ((a n)⁻¹ * x) - ctr μ a n) ^ 2 ∂μ

theorem continuous_clip_sub (c d : ℝ) : Continuous fun x : ℝ => clip (c * x) - d :=
  (continuous_clip.comp (continuous_const.mul continuous_id)).sub continuous_const

theorem abs_clip_sub_ctr_le (n : ℕ) (x : ℝ) : |clip ((a n)⁻¹ * x) - ctr μ a n| ≤ 2 :=
  (abs_sub _ _).trans (by linarith [abs_clip_le ((a n)⁻¹ * x), abs_ctr_le (μ := μ) (a := a) n])

theorem integrable_clip_sub_sq (n : ℕ) :
    Integrable (fun x => (clip ((a n)⁻¹ * x) - ctr μ a n) ^ 2) μ :=
  Integrable.of_bound ((continuous_clip_sub _ _).pow 2).aestronglyMeasurable 4
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      have := abs_clip_sub_ctr_le (μ := μ) (a := a) n x
      nlinarith [abs_nonneg (clip ((a n)⁻¹ * x) - ctr μ a n)])

theorem clipVar_nonneg (n : ℕ) : 0 ≤ clipVar μ a n :=
  integral_nonneg fun _ => sq_nonneg _

/-- The truncated means vanish when `aₙ → ∞` (dominated convergence). -/
theorem tendsto_ctr_zero (hatop : Tendsto a atTop atTop) :
    Tendsto (fun n => ctr μ a n) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun n x => clip ((a n)⁻¹ * x)) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun n => (continuous_clip.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact abs_clip_le _)
    (integrable_const _)
    (ae_of_all _ fun x => by
      have h1 : Tendsto (fun n => (a n)⁻¹ * x) atTop (𝓝 (0 * x)) :=
        (tendsto_inv_atTop_zero.comp hatop).mul_const x
      rw [zero_mul] at h1
      have h2 := (continuous_clip.tendsto 0).comp h1
      simpa [clip, Function.comp_def] using h2)
  simpa [ctr] using h

/-- The pointwise Lindeberg bound. -/
theorem norm_lindeberg_le {n : ℕ} (ha : 0 < a n) {t δ : ℝ} (hδ0 : 0 < δ)
    (hτ : |ctr μ a n| ≤ δ / 2) (x : ℝ) :
    ‖Complex.exp (((t * ((a n)⁻¹ * x - ctr μ a n)) : ℝ) * Complex.I) - 1 -
        ((t * (clip ((a n)⁻¹ * x) - ctr μ a n) : ℝ) : ℂ) * Complex.I +
        (((t * (clip ((a n)⁻¹ * x) - ctr μ a n)) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      4 * (|t| ^ 3 * δ * (clip ((a n)⁻¹ * x) - ctr μ a n) ^ 2 +
        4 * t ^ 2 * {y : ℝ | a n * (δ / 2) < |y|}.indicator (fun _ => (1 : ℝ)) x) +
      2 * {y : ℝ | a n * 1 < |y|}.indicator (fun _ => (1 : ℝ)) x := by
  set τ := ctr μ a n
  set Y := (a n)⁻¹ * x
  set V := clip Y - τ
  have hV2 : |V| ≤ 2 := abs_clip_sub_ctr_le (μ := μ) n x
  have hI1 : 0 ≤ {y : ℝ | a n * (δ / 2) < |y|}.indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hI2 : 0 ≤ {y : ℝ | a n * 1 < |y|}.indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hsplit : Complex.exp (((t * (Y - τ)) : ℝ) * Complex.I) - 1 -
      ((t * V : ℝ) : ℂ) * Complex.I + (((t * V) ^ 2 / 2 : ℝ) : ℂ) =
      (Complex.exp (((t * V) : ℝ) * Complex.I) - 1 - ((t * V : ℝ) : ℂ) * Complex.I +
        (((t * V) ^ 2 / 2 : ℝ) : ℂ)) +
      (Complex.exp (((t * (Y - τ)) : ℝ) * Complex.I) - Complex.exp (((t * V) : ℝ) * Complex.I)) := by
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_exp_mul_I_sub_taylor_le (t * V)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rcases le_or_gt |V| δ with hVδ | hVδ
    · refine (min_le_left _ _).trans ?_
      rw [abs_mul, mul_pow]
      have : |V| ^ 3 ≤ δ * V ^ 2 := by
        rw [show |V| ^ 3 = |V| * |V| ^ 2 by ring, sq_abs]
        exact mul_le_mul_of_nonneg_right hVδ (sq_nonneg _)
      nlinarith [pow_nonneg (abs_nonneg t) 3, sq_nonneg t]
    · have hY : a n * (δ / 2) < |x| := by
        have h1 : δ / 2 < |clip Y| := by
          have := abs_sub (clip Y) τ
          have h3 : |V| ≤ |clip Y| + |τ| := abs_sub _ _
          linarith
        have h2 := (h1.trans_le (abs_clip_le_abs Y))
        simp only [Y, abs_mul, abs_inv, abs_of_pos ha] at h2
        rw [lt_inv_mul_iff₀ ha] at h2
        exact h2
      rw [Set.indicator_of_mem (show x ∈ {y : ℝ | a n * (δ / 2) < |y|} from hY)]
      refine (min_le_right _ _).trans ?_
      rw [mul_pow]
      have : V ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [abs_nonneg V]
      nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hδ0.le) (sq_nonneg V),
        sq_nonneg t]
  · by_cases hx : a n * 1 < |x|
    · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | a n * 1 < |y|} from hx), mul_one]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
      norm_num
    · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | a n * 1 < |y|} from hx), mul_zero]
      have hY : |Y| ≤ 1 := by
        simp only [Y, abs_mul, abs_inv, abs_of_pos ha]
        rw [inv_mul_le_iff₀ ha]
        exact not_lt.1 hx
      have : Y - τ = V := by simp only [V, clip_eq_of_abs_le hY]
      rw [this, sub_self, norm_zero]

/-- An `ε`-squeeze for complex sequences. -/
theorem tendsto_of_forall_norm_sub_le {x : ℕ → ℂ} {L : ℂ}
    (h : ∀ η > 0, ∃ B : ℕ → ℝ, ∃ c, c < η ∧ Tendsto B atTop (𝓝 c) ∧
      ∀ᶠ n in atTop, ‖x n - L‖ ≤ B n) : Tendsto x atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨B, c, hc, hB, hx⟩ := h η hη
  filter_upwards [hx, (tendsto_order.1 hB).2 η hc] with n h1 h2
  rw [dist_eq_norm]
  exact h1.trans_lt h2

omit [IsProbabilityMeasure μ] in
theorem integral_indicator_one (r : ℝ) :
    ∫ x, {y : ℝ | r < |y|}.indicator (fun _ => (1 : ℝ)) x ∂μ = absTail μ r := by
  rw [integral_indicator_const _ (measurableSet_abs_gt r), smul_eq_mul, mul_one]; rfl

theorem integrable_indicator_one (r : ℝ) :
    Integrable ({y : ℝ | r < |y|}.indicator (fun _ => (1 : ℝ))) μ :=
  (integrable_const _).indicator (measurableSet_abs_gt r)

/-- **The Lindeberg step.** Suppose `aₙ → ∞`, `n P(|X| > ε aₙ) → 0` for every `ε > 0`, and
`n Var (clip (X / aₙ)) → σ²`. Then `n wₙ(t) → -σ² t² / 2`, where
`wₙ(t) = φ_{X / aₙ - τₙ}(t) - 1` is the centered characteristic function. -/
theorem tendsto_mul_wfun_of_lindeberg (ha : ∀ n, 0 < a n) (hatop : Tendsto a atTop atTop)
    (hT : ∀ ε > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n * ε)) atTop (𝓝 0))
    {σ2 : ℝ} (hV : Tendsto (fun n : ℕ => (n : ℝ) * clipVar μ a n) atTop (𝓝 σ2)) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * wfun μ a n t) atTop (𝓝 ((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ)) := by
  have hσ : 0 ≤ σ2 := ge_of_tendsto' hV fun n => mul_nonneg (Nat.cast_nonneg _) (clipVar_nonneg n)
  have hτ0 := tendsto_ctr_zero (μ := μ) hatop
  refine tendsto_of_forall_norm_sub_le fun η hη => ?_
  set C := |t| ^ 3 + 1
  have hC : 0 < C := by positivity
  set δ := min 1 (η / (8 * C * (σ2 + 1)))
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ ≤ η / (8 * C * (σ2 + 1)) := min_le_right _ _
  set B : ℕ → ℝ := fun n => 4 * (|t| ^ 3 * δ * ((n : ℝ) * clipVar μ a n) +
      4 * t ^ 2 * ((n : ℝ) * absTail μ (a n * (δ / 2)))) +
      2 * ((n : ℝ) * absTail μ (a n * 1)) + t ^ 2 / 2 * |(n : ℝ) * clipVar μ a n - σ2|
  refine ⟨B, 4 * (|t| ^ 3 * δ * σ2 + 4 * t ^ 2 * 0) + 2 * 0 + t ^ 2 / 2 * |σ2 - σ2|, ?_, ?_, ?_⟩
  · rw [sub_self, abs_zero]
    have h1 : |t| ^ 3 * δ * σ2 ≤ C * (η / (8 * C * (σ2 + 1))) * (σ2 + 1) := by
      have : |t| ^ 3 ≤ C := by simp only [C]; linarith
      have h2 : |t| ^ 3 * δ ≤ C * (η / (8 * C * (σ2 + 1))) :=
        mul_le_mul this hδη hδ0.le hC.le
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg t) 3) hδ0.le]
    have h3 : C * (η / (8 * C * (σ2 + 1))) * (σ2 + 1) = η / 8 := by field_simp
    linarith
  · refine ((((hV.const_mul (|t| ^ 3 * δ)).add ((hT _ (by positivity)).const_mul (4 * t ^ 2))
      ).const_mul 4).add ((hT 1 one_pos).const_mul 2)).add ?_
    exact ((hV.sub_const σ2).abs).const_mul _
  · filter_upwards [(tendsto_order.1 hτ0.abs).2 (δ / 2) (by simp; positivity)] with n hn
    set τ := ctr μ a n
    have hτ : |τ| ≤ δ / 2 := by simpa using hn.le
    have hint1 : Integrable (fun x => Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) *
        Complex.I)) μ :=
      Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
        rw [Complex.norm_exp_ofReal_mul_I])
    have hint2 : Integrable (fun x => ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) *
        Complex.I) μ := by
      refine Integrable.mul_const ?_ _
      exact (((integrable_clip n).sub (integrable_const τ)).const_mul t).ofReal
    have hint1' : Integrable (fun x => Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) *
        Complex.I) - 1) μ := hint1.sub (integrable_const 1)
    have hint3 : Integrable (fun x => (((t * (clip ((a n)⁻¹ * x) - τ)) ^ 2 / 2 : ℝ) : ℂ)) μ := by
      have : Integrable (fun x => (t * (clip ((a n)⁻¹ * x) - τ)) ^ 2 / 2) μ := by
        have h := ((integrable_clip_sub_sq (μ := μ) (a := a) n).const_mul (t ^ 2)).div_const 2
        refine h.congr (ae_of_all _ fun x => ?_)
        ring
      exact this.ofReal
    have hB0 : ∫ x, ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) * Complex.I ∂μ = 0 := by
      rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, integral_clip_sub_ctr]
      simp
    have hw : wfun μ a n t = ∫ x, (Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) *
        Complex.I) - 1 - ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) * Complex.I) ∂μ := by
      rw [integral_sub hint1' hint2, hB0, sub_zero, integral_sub hint1 (integrable_const 1),
        integral_const, probReal_univ, one_smul, wfun, charFun_cLaw]
    have hQ : ∫ x, (((t * (clip ((a n)⁻¹ * x) - τ)) ^ 2 / 2 : ℝ) : ℂ) ∂μ =
        ((t ^ 2 / 2 * clipVar μ a n : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, clipVar, ← integral_const_mul]
      congr 2
      funext x; ring
    -- the main integral estimate
    have hmain : ‖wfun μ a n t + ((t ^ 2 / 2 * clipVar μ a n : ℝ) : ℂ)‖ ≤
        4 * (|t| ^ 3 * δ * clipVar μ a n + 4 * t ^ 2 * absTail μ (a n * (δ / 2))) +
        2 * absTail μ (a n * 1) := by
      have hA : Integrable (fun x => Complex.exp (((t * ((a n)⁻¹ * x - τ) : ℝ) : ℂ) *
          Complex.I) - 1 - ((t * (clip ((a n)⁻¹ * x) - τ) : ℝ) : ℂ) * Complex.I) μ :=
        hint1'.sub hint2
      rw [hw, ← hQ, ← integral_add hA hint3]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hb1 : Integrable (fun x => |t| ^ 3 * δ * (clip ((a n)⁻¹ * x) - τ) ^ 2) μ :=
        (integrable_clip_sub_sq n).const_mul _
      have hb2 : Integrable (fun x => 4 * t ^ 2 *
          {y : ℝ | a n * (δ / 2) < |y|}.indicator (fun _ => (1 : ℝ)) x) μ :=
        (integrable_indicator_one _).const_mul _
      have hb3 : Integrable (fun x => 2 *
          {y : ℝ | a n * 1 < |y|}.indicator (fun _ => (1 : ℝ)) x) μ :=
        (integrable_indicator_one _).const_mul _
      calc _ ≤ ∫ x, (4 * (|t| ^ 3 * δ * (clip ((a n)⁻¹ * x) - τ) ^ 2 +
            4 * t ^ 2 * {y : ℝ | a n * (δ / 2) < |y|}.indicator (fun _ => (1 : ℝ)) x) +
            2 * {y : ℝ | a n * 1 < |y|}.indicator (fun _ => (1 : ℝ)) x) ∂μ :=
            integral_mono (hA.add hint3).norm
              (((hb1.add hb2).const_mul 4).add hb3)
              fun x => norm_lindeberg_le (ha n) hδ0 hτ x
        _ = _ := by
            have hb12 : Integrable (fun x => 4 * (|t| ^ 3 * δ * (clip ((a n)⁻¹ * x) - τ) ^ 2 +
                4 * t ^ 2 * {y : ℝ | a n * (δ / 2) < |y|}.indicator (fun _ => (1 : ℝ)) x)) μ :=
              (hb1.add hb2).const_mul 4
            rw [integral_add hb12 hb3, integral_const_mul,
              integral_add hb1 hb2, integral_const_mul, integral_const_mul, integral_const_mul,
              integral_indicator_one, integral_indicator_one, clipVar]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 : (n : ℂ) * wfun μ a n t - ((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ) =
        (n : ℂ) * (wfun μ a n t + ((t ^ 2 / 2 * clipVar μ a n : ℝ) : ℂ)) -
          ((t ^ 2 / 2 * ((n : ℝ) * clipVar μ a n - σ2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)]
    simp only [B]
    have := mul_le_mul_of_nonneg_left hmain hn0
    nlinarith

end Lindeberg

end ExtremeValueTheory
