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

section GaussianLimit

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

/-- **Central limit theorem under the Lindeberg-type conditions.** If `aₙ → ∞`,
`n P(|X| > ε aₙ) → 0` for every `ε > 0` and `n Var (clip (X / aₙ)) → σ²`, then
`(Sₙ - n aₙ τₙ) / aₙ → N(0, σ²)`, `τₙ = E[clip (X / aₙ)]`. -/
theorem tendsto_map_convPow_gaussianReal_of_lindeberg (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a atTop atTop)
    (hT : ∀ ε > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n * ε)) atTop (𝓝 0))
    {σ2 : ℝ} (hV : Tendsto (fun n : ℕ => (n : ℝ) * clipVar μ a n) atTop (𝓝 σ2)) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - n * a n * ctr μ a n)), inferInstance⟩) atTop
      (𝓝 ⟨gaussianReal 0 σ2.toNNReal, inferInstance⟩) := by
  have hσ : 0 ≤ σ2 :=
    ge_of_tendsto' hV fun n => mul_nonneg (Nat.cast_nonneg _) (clipVar_nonneg n)
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  simp only [ProbabilityMeasure.coe_mk]
  have hw := tendsto_mul_wfun_of_lindeberg ha hatop hT hV t
  set L : ℂ := ((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ)
  have hC : ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * wfun μ a n t‖ ≤ ‖L‖ + 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 hw) 1 one_pos] with n hn
    rw [dist_eq_norm] at hn
    have := norm_sub_norm_le ((n : ℂ) * wfun μ a n t) L
    linarith
  have h3 := (tendsto_one_add_pow_sub_exp hC).add ((Complex.continuous_exp.tendsto _).comp hw)
  rw [zero_add] at h3
  have hL : Complex.exp L = charFun (gaussianReal 0 σ2.toNNReal) t := by
    rw [charFun_gaussianReal]
    congr 1
    simp only [L, Real.coe_toNNReal _ hσ]
    push_cast; ring
  rw [← hL]
  refine h3.congr fun n => ?_
  simp only [Function.comp]
  have hs := charFun_sum_eq (μ := μ) (a := a) (b := fun n : ℕ => (n : ℝ) * a n * ctr μ a n) n t
  rw [hs]
  have hz : t * (n * ctr μ a n - (a n)⁻¹ * (n * a n * ctr μ a n)) = 0 := by
    field_simp [(ha n).ne']; ring
  rw [hz]
  simp

/-- **Identification of a Gaussian limit.** Under the Lindeberg-type conditions, any weak limit
of `(Sₙ - bₙ) / aₙ` is a Gaussian law `N(m, σ²)`. -/
theorem exists_eq_gaussianReal_of_lindeberg (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a atTop atTop)
    (hT : ∀ ε > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n * ε)) atTop (𝓝 0))
    {σ2 : ℝ} (hV : Tendsto (fun n : ℕ => (n : ℝ) * clipVar μ a n) atTop (𝓝 σ2))
    {b : ℕ → ℝ} {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ m : ℝ, (ν : Measure ℝ) = gaussianReal m σ2.toNNReal := by
  have h := tendsto_map_convPow_gaussianReal_of_lindeberg ha hatop hT hV
  have hc : ∀ n : ℕ, (⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩ :
      ProbabilityMeasure ℝ) = ⟨(((⟨(convPow μ n).map (fun x => (a n)⁻¹ *
        (x - n * a n * ctr μ a n)), inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)).map
        (· + (a n)⁻¹ * (n * a n * ctr μ a n - b n)), inferInstance⟩ := by
    intro n
    apply Subtype.ext
    simp only
    rw [Measure.map_map (measurable_add_const _) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp]
    ring
  obtain ⟨c₀, hc₀⟩ := exists_map_add_eq_of_tendsto h (hconv.congr hc)
  refine ⟨c₀, ?_⟩
  rw [← hc₀]
  simp only [ProbabilityMeasure.coe_mk]
  rw [gaussianReal_map_add_const, zero_add]

end GaussianLimit

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
