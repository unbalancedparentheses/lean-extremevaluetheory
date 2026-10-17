/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
Modified by Federico Carrone, 2026, from kkytola/ExtremeValueProject (commit f7c9a8ce260d):
ported to Lean/Mathlib v4.35.0 and renamed `ExtremeValueProject` to `ExtremeValueTheory`.
-/
import ExtremeValueTheory.AffineTransformation
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

section ExtremeValueDistribution

open Filter Topology NNReal ENNReal

namespace CumulativeDistributionFunction

/-- A c.d.f. `G` is an extreme value distribution (of max type) if it is nondegenerate and
it is the limit of the distributions of maxima of independent and identically distributed random
variables up to orientation preserving affine transforms (pointwise limit on the set of continuity
points of `G`). -/
def IsExtremeValueDistr (G : CumulativeDistributionFunction) : Prop :=
  ¬G.IsDegenerate ∧
    ∃ (F : CumulativeDistributionFunction) (As : ℕ → AffineIncrEquiv),
      ∀ x, ContinuousAt G x → Tendsto (fun n ↦ ((As n • F) x)^n) atTop (𝓝 (G x))

lemma IsExtremeValueDistr.nondegenerate
    {G : CumulativeDistributionFunction} (G_evd : G.IsExtremeValueDistr) :
    ¬G.IsDegenerate :=
  G_evd.1

/-- Orientation preserving affine transfroms of extreme value distributions are extreme value
distributions. -/
lemma IsExtremeValueDistr.affineTransform (G : CumulativeDistributionFunction)
    (G_evd : G.IsExtremeValueDistr) (A : AffineIncrEquiv) :
    (A • G).IsExtremeValueDistr := by
  refine ⟨by simpa [affine_isDegenerate_iff] using G_evd.1, ?_⟩
  choose F As h using G_evd.2
  refine ⟨F, fun n ↦ A * As n, ?_⟩
  intro x AG_cont
  have G_cont := affine_continuousAt_of_continuousAt AG_cont A⁻¹
  simp only [inv_smul_smul, InvMemClass.coe_inv] at G_cont
  exact h (A⁻¹  x) G_cont

end CumulativeDistributionFunction

/-- An extreme value distribution is a c.d.f. which satisfies the property
`IsExtremeValueDistribution`. -/
structure ExtremeValueDistr where
  (toCDF : CumulativeDistributionFunction)
  (isEVD : toCDF.IsExtremeValueDistr)

/-- The domain of attraction of an extreme value distribution `G` is the set of all
those c.d.f.s `F` for which `G` is the limit (pointwise on the set of continuity points
of `G`) of the distributions of maxima of independent random variables up to orientation
preserving affine transforms  -/
def ExtremeValueDistr.domainOfAtraction (G : ExtremeValueDistr) :
    Set CumulativeDistributionFunction :=
  {F | ∃ (As : ℕ → AffineIncrEquiv),
       ∀ x, ContinuousAt F x → Tendsto (fun n ↦ ((As n • G.toCDF) x)^n) atTop (𝓝 (F x))}

namespace ExtremeValueDistr

lemma domainOfAtraction_nonempty (G : ExtremeValueDistr) :
    G.domainOfAtraction ≠ ∅ := by
  set H := G.toCDF
  have ht : ∀ n : ℕ, ∃ t, 1 - 1 / ((n : ℝ) + 1) ^ 2 < H t := fun n ↦ by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2 := by positivity
    exact (H.tendsto_atTop.eventually (lt_mem_nhds (by linarith))).exists
  choose t ht using ht
  obtain ⟨y₀, hy₀⟩ : ∃ y, H y < 1 / 2 :=
    (H.tendsto_atBot.eventually (gt_mem_nhds (by norm_num))).exists
  set s : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) * (|t n| + |y₀| + 1) with hs
  have s_pos : ∀ n, 0 < s n := fun n ↦ by positivity
  rw [← Set.nonempty_iff_ne_empty]
  refine ⟨(MeasureTheory.diracProba (0 : ℝ)).cdf, fun n ↦ (AffineIncrEquiv.mkOfCoefs (s_pos n) (t n))⁻¹, ?_⟩
  intro x _
  simp only
  rw [CumulativeDistributionFunction.cdf_diracProba_apply]
  by_cases hx : x < 0
  · simp only [hx, ↓reduceIte]
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (-x))
    have hle : ∀ᶠ n : ℕ in atTop, H (s n * x + t n) ≤ 1 / 2 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnx : 1 ≤ ((n : ℝ) + 1) * (-x) := by
        have h1 : 1 / (-x) < (n : ℝ) + 1 := by
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        rw [div_lt_iff₀ (by linarith)] at h1
        linarith
      have hpos : 0 ≤ |t n| + |y₀| + 1 := by positivity
      have key : s n * x + t n ≤ y₀ := by
        have e : s n * x = -((((n : ℝ) + 1) * (-x)) * (|t n| + |y₀| + 1)) := by
          simp only [hs]; ring
        have : 1 * (|t n| + |y₀| + 1) ≤ (((n : ℝ) + 1) * (-x)) * (|t n| + |y₀| + 1) :=
          mul_le_mul_of_nonneg_right hnx hpos
        have := le_abs_self (t n)
        have := neg_abs_le y₀
        linarith
      exact (H.mono key).trans hy₀.le
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)) (Eventually.of_forall fun n ↦ pow_nonneg (H.apply_nonneg _) n) ?_
    filter_upwards [hle] with n hn
    exact pow_le_pow_left₀ (H.apply_nonneg _) hn n
  · simp only [hx, ↓reduceIte]
    have hlow : Tendsto (fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
    · intro n
      have hmono : H (t n) ≤ H (s n * x + t n) :=
        H.mono (by have := mul_nonneg (s_pos n).le (not_lt.mp hx); linarith)
      refine le_trans ?_ (pow_le_pow_left₀ (H.apply_nonneg _) hmono n)
      have hb := one_add_mul_le_pow (a := H (t n) - 1)
        (by have := H.apply_nonneg (t n); linarith) n
      rw [add_sub_cancel] at hb
      refine le_trans ?_ hb
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have ha : -(1 / ((n : ℝ) + 1) ^ 2) ≤ H (t n) - 1 := by linarith [ht n]
      have h2 : (n : ℝ) * -(1 / ((n : ℝ) + 1) ^ 2) ≤ n * (H (t n) - 1) :=
        mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg n)
      have h3 : (n : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) ≤ 1 / ((n : ℝ) + 1) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hn1]
        nlinarith
      linarith
    · intro n
      exact pow_le_one₀ (H.apply_nonneg _) (H.apply_le_one _)

section rewriting_the_limit_condition

private def limitCondition (γ : ℝ) (φs : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ (φs n)^n) atTop (𝓝 γ)

variable (γ : ℝ) (φs : ℕ → ℝ)

-- Corrected from upstream: added the hypothesis `hφ` that `φs n` is eventually nonnegative
-- (without it the statement is false, see `not_limitCondition_iff_log` below).
lemma limitCondition_iff_log {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ)
    (hφ : ∀ᶠ n in atTop, 0 ≤ φs n) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 (Real.log γ)) := by
  unfold limitCondition
  constructor
  · intro h
    refine ((Real.continuousAt_log hγ.1.ne').tendsto.comp h).congr' ?_
    filter_upwards [h.eventually (lt_mem_nhds hγ.1)] with n hn
    simp [Real.log_pow]
  · intro h
    have hlog : Real.log γ < 0 := Real.log_neg hγ.1 hγ.2
    have hpos : ∀ᶠ n in atTop, 0 < φs n := by
      filter_upwards [hφ, h.eventually (gt_mem_nhds (by linarith : Real.log γ < Real.log γ / 2))]
        with n hn hn'
      refine lt_of_le_of_ne hn fun h0 ↦ ?_
      rw [← h0, Real.log_zero, mul_zero] at hn'
      linarith
    have := (Real.continuous_exp.tendsto _).comp h
    rw [Function.comp_def, Real.exp_log hγ.1] at this
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    rw [← Real.log_pow, Real.exp_log (pow_pos hn n)]

/-- If `φs n → 1` then `n log φs n` and `n (φs n - 1)` have the same limit. -/
private lemma tendsto_mul_log_iff_of_tendsto_one {φs : ℕ → ℝ} (h1 : Tendsto φs atTop (𝓝 1)) (L : ℝ) :
    Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 L)
      ↔ Tendsto (fun n ↦ n * (φs n - 1)) atTop (𝓝 L) := by
  have hpos : ∀ᶠ n in atTop, 0 < φs n := h1.eventually (lt_mem_nhds one_pos)
  have hle : ∀ᶠ n : ℕ in atTop, (n : ℝ) * Real.log (φs n) ≤ n * (φs n - 1) := by
    filter_upwards [hpos] with n hn
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hn) n.cast_nonneg
  have hge : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (φs n - 1) / φs n ≤ n * Real.log (φs n) := by
    filter_upwards [hpos] with n hn
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ n.cast_nonneg
    have := Real.one_sub_inv_le_log_of_pos hn
    rwa [_root_.sub_div, div_self hn.ne', one_div]
  constructor
  · intro h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h (by simpa using h.mul h1) hle ?_
    filter_upwards [hge, hpos] with n hn hn'
    rwa [div_le_iff₀ hn'] at hn
  · intro h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by have := h.div h1 one_ne_zero; rw [div_one] at this; exact this) h hge hle

private lemma tendsto_zero_of_tendsto_natCast_mul {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n ↦ n * f n) atTop (𝓝 L)) : Tendsto f atTop (𝓝 0) := by
  have := h.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply]
  field_simp

-- Corrected from upstream: added the hypothesis `hφ` that `φs n` is eventually nonnegative
-- (without it the statement is false, see `not_limitCondition_iff_log` below).
lemma tendsto_of_limitcondition {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ)
    (hφ : ∀ᶠ n in atTop, 0 ≤ φs n) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 (Real.log γ)) :=
  limitCondition_iff_log hγ φs hφ

-- Corrected from upstream: added the hypothesis `hφ` that `φs n` is eventually nonnegative
-- (without it the statement is false, see `not_limitCondition_iff` below).
lemma limitCondition_iff {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ)
    (hφ : ∀ᶠ n in atTop, 0 ≤ φs n) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * (1 - φs n)) atTop (𝓝 (-Real.log γ)) := by
  rw [limitCondition_iff_log hγ φs hφ]
  have e : (fun n : ℕ ↦ (n : ℝ) * (1 - φs n)) = fun n ↦ -(n * (φs n - 1)) := by
    funext n; ring
  rw [e]
  constructor
  · intro h
    have hlog : Real.log γ < 0 := Real.log_neg hγ.1 hγ.2
    have hpos : ∀ᶠ n in atTop, 0 < φs n := by
      filter_upwards [hφ, h.eventually (gt_mem_nhds (by linarith : Real.log γ < Real.log γ / 2))]
        with n hn hn'
      refine lt_of_le_of_ne hn fun h0 ↦ ?_
      rw [← h0, Real.log_zero, mul_zero] at hn'
      linarith
    have h1 : Tendsto φs atTop (𝓝 1) := by
      have := (Real.continuous_exp.tendsto _).comp (tendsto_zero_of_tendsto_natCast_mul h)
      rw [Real.exp_zero] at this
      refine this.congr' ?_
      filter_upwards [hpos] with n hn
      exact Real.exp_log hn
    exact ((tendsto_mul_log_iff_of_tendsto_one h1 _).1 h).neg
  · intro h
    have h' := h.neg
    simp only [neg_neg] at h'
    have h1 : Tendsto φs atTop (𝓝 1) := by
      have := (tendsto_zero_of_tendsto_natCast_mul h').add_const 1
      simpa using this
    exact (tendsto_mul_log_iff_of_tendsto_one h1 _).2 h'

-- Corrected from upstream: added the hypothesis `hφ` that `φs n` is eventually nonnegative
-- (without it the statement is false, see `not_limitCondition_iff_inv` below).
lemma limitCondition_iff_inv {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ)
    (hφ : ∀ᶠ n in atTop, 0 ≤ φs n) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ (n * (1 - φs n))⁻¹) atTop (𝓝 (-Real.log γ)⁻¹) := by
  have hL : -Real.log γ ≠ 0 := (neg_pos.2 (Real.log_neg hγ.1 hγ.2)).ne'
  rw [limitCondition_iff hγ φs hφ]
  refine ⟨fun h ↦ h.inv₀ hL, fun h ↦ ?_⟩
  simpa using h.inv₀ (inv_ne_zero hL)

/- The four statements above are false without the hypothesis `hφ` (as stated upstream), because `φs n` is allowed to be negative
(and `Real.log` is even). The following lemmas give explicit counterexamples with
`γ = exp (-1)`. -/

private lemma exp_neg_one_mem_Ioo : Real.exp (-1) ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by norm_num)⟩

private lemma tendsto_two_mul_add (c : ℕ) : Tendsto (fun k : ℕ ↦ 2 * k + c) atTop atTop :=
  tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun a ha ↦ by omega⟩

/-- Counterexample to `tendsto_of_limitcondition` and `limitCondition_iff_log`
(the `←` direction fails for `φs n = -exp (-1/n)`). -/
lemma not_limitCondition_iff_log :
    ¬ ∀ (γ : ℝ), γ ∈ Set.Ioo 0 1 → ∀ φs : ℕ → ℝ, (limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 (Real.log γ))) := by
  intro h
  have hlim := (h _ exp_neg_one_mem_Ioo (fun n ↦ -Real.exp (-1 / n))).2 (by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [Real.log_neg_eq_log, Real.log_exp, Real.log_exp]
    field_simp)
  unfold limitCondition at hlim
  have e : ∀ k : ℕ, (-Real.exp (-1 / ((2 * k + 1 : ℕ) : ℝ))) ^ (2 * k + 1) = -Real.exp (-1) := by
    intro k
    have hk : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [neg_pow, ← Real.exp_nat_mul, pow_succ, pow_mul]
    simp only [even_two, Even.neg_pow, one_pow, one_mul, neg_one_mul, neg_inj]
    congr 1
    field_simp
  have h1 := hlim.comp (tendsto_two_mul_add 1)
  have h2 : Tendsto (fun k : ℕ ↦ (-Real.exp (-1 / ((2 * k + 1 : ℕ) : ℝ))) ^ (2 * k + 1)) atTop
      (𝓝 (-Real.exp (-1))) := by
    simp_rw [e]; exact tendsto_const_nhds
  have := tendsto_nhds_unique h1 h2
  linarith [Real.exp_pos (-1)]

private noncomputable def altSeq (n : ℕ) : ℝ :=
  if Even n then -Real.exp (-1 / n) else Real.exp (-1 / n)

private lemma limitCondition_altSeq : limitCondition (Real.exp (-1)) altSeq := by
  unfold limitCondition
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have : Real.exp (-1 / n) ^ n = Real.exp (-1) := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  unfold altSeq
  split_ifs with he
  · rw [he.neg_pow, this]
  · rw [this]

private lemma tendsto_altSeq_atTop :
    Tendsto (fun k : ℕ ↦ ((2 * k + 2 : ℕ) : ℝ) * (1 - altSeq (2 * k + 2))) atTop atTop := by
  refine tendsto_atTop_mono (fun k ↦ ?_)
    (tendsto_natCast_atTop_atTop.comp (tendsto_two_mul_add 2))
  have he : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  simp only [Function.comp_apply, altSeq, he, ↓reduceIte, sub_neg_eq_add]
  have := Real.exp_pos (-1 / ((2 * k + 2 : ℕ) : ℝ))
  nlinarith [(Nat.cast_nonneg (2 * k + 2) : (0 : ℝ) ≤ _)]

/-- Counterexample to `limitCondition_iff` (the `→` direction fails). -/
lemma not_limitCondition_iff :
    ¬ ∀ (γ : ℝ), γ ∈ Set.Ioo 0 1 → ∀ φs : ℕ → ℝ, (limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * (1 - φs n)) atTop (𝓝 (-Real.log γ))) := by
  intro h
  have hlim := (h _ exp_neg_one_mem_Ioo altSeq).1 limitCondition_altSeq
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_altSeq_atTop _
    (hlim.comp (tendsto_two_mul_add 2))

/-- Counterexample to `limitCondition_iff_inv` (the `→` direction fails). -/
lemma not_limitCondition_iff_inv :
    ¬ ∀ (γ : ℝ), γ ∈ Set.Ioo 0 1 → ∀ φs : ℕ → ℝ, (limitCondition γ φs
      ↔ Tendsto (fun n ↦ (n * (1 - φs n))⁻¹) atTop (𝓝 (-Real.log γ)⁻¹)) := by
  intro h
  have hlim := (h _ exp_neg_one_mem_Ioo altSeq).1 limitCondition_altSeq
  have h1 := hlim.comp (tendsto_two_mul_add 2)
  have h2 := tendsto_inv_atTop_zero.comp tendsto_altSeq_atTop
  have := tendsto_nhds_unique h1 h2
  simp at this

private def limitCondition' {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 (Real.log γ))

end rewriting_the_limit_condition

end ExtremeValueDistr

section three_evds

private noncomputable def standardGumbelAux (x : ℝ) := Real.exp (-Real.exp (-x))

private lemma continuous_standardGumbelAux : Continuous standardGumbelAux := by
  unfold standardGumbelAux; fun_prop

noncomputable def standardGumbelCDF : CumulativeDistributionFunction where
  toFun := standardGumbelAux
  mono' := by
    intro x y hxy
    unfold standardGumbelAux
    gcongr
  right_continuous' := fun x ↦ continuous_standardGumbelAux.continuousWithinAt
  tendsto_atTop := by
    have h : Tendsto (fun x : ℝ ↦ -Real.exp (-x)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg
    have h2 := (Real.continuous_exp.tendsto 0).comp h
    rw [Real.exp_zero] at h2
    exact h2
  tendsto_atBot :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop))

lemma standardGumbelCDF_apply_eq (x : ℝ) :
    standardGumbelCDF x = Real.exp (-Real.exp (-x)) :=
  rfl

noncomputable def standardFrechetAux (α : ℝ) (x : ℝ) :=
  if x ≤ 0 then 0 else Real.exp (-(Real.rpow x (-α)))

lemma standardFrechetAux_eq_expNegInvGlue {α : ℝ} (α_pos : 0 < α) (x : ℝ) :
    standardFrechetAux α x = expNegInvGlue ((max x 0) ^ α) := by
  by_cases hx : x ≤ 0
  · simp [standardFrechetAux, hx, Real.zero_rpow α_pos.ne']
  · have hx' : 0 < x := lt_of_not_ge hx
    have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx' α
    simp [standardFrechetAux, hx, max_eq_left hx'.le, expNegInvGlue, not_le.mpr hxα,
      Real.rpow_neg hx'.le]

lemma continuous_standardFrechetAux {α : ℝ} (α_pos : 0 < α) :
    Continuous (standardFrechetAux α) := by
  have : (standardFrechetAux α) = fun x ↦ expNegInvGlue ((max x 0) ^ α) :=
    funext (standardFrechetAux_eq_expNegInvGlue α_pos)
  rw [this]
  exact (expNegInvGlue.contDiff (n := 0)).continuous.comp
    ((Real.continuous_rpow_const α_pos.le).comp (continuous_id.max continuous_const))

noncomputable def standardFrechetCDF {α : ℝ} (α_pos : 0 < α) : CumulativeDistributionFunction where
  toFun := standardFrechetAux α
  mono' := by
    intro x y hxy
    simp only [standardFrechetAux_eq_expNegInvGlue α_pos]
    exact expNegInvGlue.monotone
      (Real.rpow_le_rpow (le_max_right _ _) (max_le_max hxy le_rfl) α_pos.le)
  right_continuous' := fun x ↦ (continuous_standardFrechetAux α_pos).continuousWithinAt
  tendsto_atTop := by
    have h : Tendsto (fun x : ℝ ↦ Real.exp (-(x ^ (-α)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun x : ℝ ↦ -(x ^ (-α))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop α_pos).neg
      have h2 := (Real.continuous_exp.tendsto 0).comp h0
      rw [Real.exp_zero] at h2
      exact h2
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [standardFrechetAux, not_le.mpr hx]
  tendsto_atBot := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot 0] with x hx
    simp [standardFrechetAux, hx]

lemma standardFrechetCDF_apply_pos_eq {α x : ℝ} (α_pos : 0 < α) (hx : 0 < x) :
    standardFrechetCDF α_pos x = Real.exp (-(Real.rpow x (-α))) := by
  simp [standardFrechetCDF, standardFrechetAux, hx]

lemma standardFrechetCDF_apply_nonpos_eq {α x : ℝ} (α_pos : 0 < α) (hx : x ≤ 0) :
    standardFrechetCDF α_pos x = 0 := by
  simp [standardFrechetCDF, standardFrechetAux, hx]

noncomputable def standardWeibullAux (α : ℝ) (x : ℝ) :=
  if x < 0 then Real.exp (-(Real.rpow (-x) α)) else 1

lemma standardWeibullAux_eq {α : ℝ} (α_pos : 0 < α) (x : ℝ) :
    standardWeibullAux α x = Real.exp (-((max (-x) 0) ^ α)) := by
  by_cases hx : x < 0
  · simp [standardWeibullAux, hx, max_eq_left (neg_nonneg.mpr hx.le)]
  · have hx' : -x ≤ 0 := by linarith
    simp [standardWeibullAux, hx, max_eq_right hx', Real.zero_rpow α_pos.ne']

noncomputable def standardWeibullCDF {α : ℝ} (α_pos : 0 < α) : CumulativeDistributionFunction where
  toFun := standardWeibullAux α
  mono' := by
    intro x y hxy
    simp only [standardWeibullAux_eq α_pos]
    apply Real.exp_le_exp.2
    apply neg_le_neg
    exact Real.rpow_le_rpow (le_max_right _ _) (max_le_max (neg_le_neg hxy) le_rfl) α_pos.le
  right_continuous' := by
    intro x
    have : (standardWeibullAux α) = fun x ↦ Real.exp (-((max (-x) 0) ^ α)) :=
      funext (standardWeibullAux_eq α_pos)
    rw [this]
    exact (Real.continuous_exp.comp ((Real.continuous_rpow_const α_pos.le).comp
      (continuous_neg.max continuous_const)).neg).continuousWithinAt
  tendsto_atTop := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp [standardWeibullAux, not_lt.mpr hx]
  tendsto_atBot := by
    have h : Tendsto (fun x : ℝ ↦ Real.exp (-((-x) ^ α))) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp ((_root_.tendsto_rpow_atTop α_pos).comp tendsto_neg_atBot_atTop))
    refine h.congr' ?_
    filter_upwards [eventually_lt_atBot 0] with x hx
    simp [standardWeibullAux, hx]

lemma standardWeibullCDF_apply_nonneg_eq {α x : ℝ} (α_pos : 0 < α) (hx : 0 ≤ x) :
    standardWeibullCDF α_pos x = 1 := by
  simp [standardWeibullCDF, standardWeibullAux, hx]

lemma standardWeibullCDF_apply_neg_eq {α x : ℝ} (α_pos : 0 < α) (hx : x < 0) :
    standardWeibullCDF α_pos x = Real.exp (-(Real.rpow (-x) α)) := by
  simp [standardWeibullCDF, standardWeibullAux, hx]

private lemma inv_mkOfCoefs_smul_apply (G : CumulativeDistributionFunction) {a : ℝ} (ha : 0 < a)
    (b x : ℝ) : ((AffineIncrEquiv.mkOfCoefs ha b)⁻¹ • G) x = G (a * x + b) := by
  simp

private lemma not_isDegenerate_of_apply_eq (G : CumulativeDistributionFunction) {x : ℝ}
    (hx : G x = Real.exp (-1)) : ¬ G.IsDegenerate := by
  intro h
  rcases h x with h0 | h1
  · exact (Real.exp_pos _).ne' (hx ▸ h0)
  · have := Real.exp_eq_one_iff (-1) |>.mp (hx ▸ h1)
    norm_num at this

private lemma max_natCast_one_eq {n : ℕ} (hn : 1 ≤ n) : max (n : ℝ) 1 = n :=
  max_eq_left (by exact_mod_cast hn)

lemma isExtremeValueDistr_standardGumbelCDF :
    standardGumbelCDF.IsExtremeValueDistr := by
  refine ⟨not_isDegenerate_of_apply_eq _ (x := 0) (by simp [standardGumbelCDF_apply_eq]),
    standardGumbelCDF, fun n ↦ (AffineIncrEquiv.mkOfCoefs one_pos (Real.log n))⁻¹, ?_⟩
  intro x _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_mkOfCoefs_smul_apply, standardGumbelCDF_apply_eq, standardGumbelCDF_apply_eq,
    ← Real.exp_nat_mul, one_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
    Real.exp_log hn']
  congr 1
  field_simp

lemma isExtremeValueDistr_standardFrechetCDF {ξ : ℝ} (ξ_pos : 0 < ξ) :
    (standardFrechetCDF ξ_pos).IsExtremeValueDistr := by
  refine ⟨not_isDegenerate_of_apply_eq _ (x := 1)
    (by simp [standardFrechetCDF_apply_pos_eq ξ_pos one_pos]), standardFrechetCDF ξ_pos,
    fun n ↦ (AffineIncrEquiv.mkOfCoefs
      (Real.rpow_pos_of_pos (lt_max_of_lt_right one_pos) (1 / ξ) : 0 < (max (n : ℝ) 1) ^ (1 / ξ))
      0)⁻¹, ?_⟩
  intro x _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_mkOfCoefs_smul_apply, max_natCast_one_eq hn, add_zero]
  have hc : 0 < (n : ℝ) ^ (1 / ξ) := Real.rpow_pos_of_pos hn' _
  by_cases hx : x ≤ 0
  · rw [standardFrechetCDF_apply_nonpos_eq ξ_pos hx,
      standardFrechetCDF_apply_nonpos_eq ξ_pos (mul_nonpos_of_nonneg_of_nonpos hc.le hx),
      zero_pow (by omega)]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [standardFrechetCDF_apply_pos_eq ξ_pos hx',
      standardFrechetCDF_apply_pos_eq ξ_pos (mul_pos hc hx'), ← Real.exp_nat_mul]
    congr 1
    change -(x ^ (-ξ)) = (n : ℝ) * -(((n : ℝ) ^ (1 / ξ) * x) ^ (-ξ))
    rw [Real.mul_rpow hc.le hx'.le, ← Real.rpow_mul hn'.le, show 1 / ξ * -ξ = -1 by
      field_simp, Real.rpow_neg_one]
    field_simp

lemma isExtremeValueDistr_standardWeibullCDF {ξ : ℝ} (ξ_pos : 0 < ξ) :
    (standardWeibullCDF ξ_pos).IsExtremeValueDistr := by
  refine ⟨not_isDegenerate_of_apply_eq _ (x := -1)
    (by simp [standardWeibullCDF_apply_neg_eq ξ_pos (by norm_num : (-1 : ℝ) < 0)]),
    standardWeibullCDF ξ_pos,
    fun n ↦ (AffineIncrEquiv.mkOfCoefs
      (Real.rpow_pos_of_pos (lt_max_of_lt_right one_pos) (-1 / ξ) :
        0 < (max (n : ℝ) 1) ^ (-1 / ξ)) 0)⁻¹, ?_⟩
  intro x _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_mkOfCoefs_smul_apply, max_natCast_one_eq hn, add_zero]
  have hc : 0 < (n : ℝ) ^ (-1 / ξ) := Real.rpow_pos_of_pos hn' _
  by_cases hx : 0 ≤ x
  · rw [standardWeibullCDF_apply_nonneg_eq ξ_pos hx,
      standardWeibullCDF_apply_nonneg_eq ξ_pos (mul_nonneg hc.le hx), one_pow]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [standardWeibullCDF_apply_neg_eq ξ_pos hx',
      standardWeibullCDF_apply_neg_eq ξ_pos (mul_neg_of_pos_of_neg hc hx'), ← Real.exp_nat_mul]
    congr 1
    change -((-x) ^ ξ) = (n : ℝ) * -((-((n : ℝ) ^ (-1 / ξ) * x)) ^ ξ)
    rw [← mul_neg, Real.mul_rpow hc.le (by linarith), ← Real.rpow_mul hn'.le,
      show -1 / ξ * ξ = -1 by field_simp, Real.rpow_neg_one]
    field_simp

end three_evds

end ExtremeValueDistribution
