/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
Modified by Federico Carrone, 2026, from kkytola/ExtremeValueProject (commit f7c9a8ce260d):
ported to Lean/Mathlib v4.35.0 and renamed `ExtremeValueProject` to `ExtremeValueTheory`.
-/
import Mathlib
import ExtremeValueTheory.OneParameterAffine
import ExtremeValueTheory.OrderContinuity
import ExtremeValueTheory.ExtremeValueDistribution

/-!
# Self-similar cumulative distribution functions

A CDF `G` is *self-similar* with respect to a one-parameter group of increasing affine maps `f`
when `f s • G = G ^ (exp s)` for all `s`. This file defines real powers `G ^ t` of a CDF
(`CumulativeDistributionFunction.pow`) and shows that a non-degenerate self-similar CDF is of
Gumbel, Fréchet or Weibull type according to the index of the group
(`gumbel_type_of_selfSimilar_index_zero`, `frechet_type_of_selfSimilar_index_pos`,
`weibull_type_of_selfSimilar_index_neg`).

It is the first part of `ExtremeValueTheory.SelfSimilarCDF`, which deduces the
Fisher–Tippett–Gnedenko classification of extreme value distributions.
-/

section self_similar_cdf

noncomputable def CumulativeDistributionFunction.comp_rightOrdContinuous
    (F : CumulativeDistributionFunction) (φ : ℝ → ℝ) (hφ : RightOrdContinuous φ)
    (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1) (hφc1 : ContinuousWithinAt φ (Set.Iic 1) 1) :
    CumulativeDistributionFunction where
  toFun x := φ (F x)
  mono' := hφ.mono.comp F.mono'
  right_continuous' := by
    intro x
    have hφc : ContinuousWithinAt φ (Set.Ici (F x)) (F x) :=
      (hφ.mono.continuousWithinAt_Ici_iff_isGLB_image_Ioi (not_isMax _)).mpr
        (hφ Set.nonempty_Ioi isGLB_Ioi)
    exact hφc.comp (F.right_continuous' x) (fun y hy ↦ F.mono' hy)
  -- Corrected from upstream: left-continuity of `φ` at `1` (`hφc1`) is needed here, since a right
  -- order-continuous `φ` may jump at `1` (e.g. `φ = indicator (Ici 1) 1`).
  tendsto_atTop := by
    have hF : Filter.Tendsto F.toFun Filter.atTop (nhdsWithin 1 (Set.Iic 1)) :=
      tendsto_nhdsWithin_iff.mpr ⟨F.tendsto_atTop, Filter.Eventually.of_forall F.apply_le_one⟩
    have := hφc1.tendsto.comp hF
    rwa [hφ1] at this
  tendsto_atBot := by
    have hφc : ContinuousWithinAt φ (Set.Ici 0) 0 :=
      (hφ.mono.continuousWithinAt_Ici_iff_isGLB_image_Ioi (not_isMax _)).mpr
        (hφ Set.nonempty_Ioi isGLB_Ioi)
    have hF : Filter.Tendsto F.toFun Filter.atBot (nhdsWithin 0 (Set.Ici 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨F.tendsto_atBot, Filter.Eventually.of_forall F.apply_nonneg⟩
    have := hφc.tendsto.comp hF
    rwa [‹φ 0 = 0›] at this

open Set Topology in
lemma Real.rightOrdContinuous_indicator_Ici_rpow {t : ℝ} (t_nn : 0 < t) :
    RightOrdContinuous (indicator (Ici 0) (fun p ↦ Real.rpow p t)) := by
  -- This is a bad proof. Should just prove continuity.
  refine Monotone.rightOrdContinuous_of_forall_continuousWithinAt_Ici ?_ ?_
  · intro p₁ p₂ hp
    by_cases nn₁ : 0 ≤ p₁
    · simpa [show p₁ ∈ Ici 0 from nn₁, show p₂ ∈ Ici 0 from nn₁.trans hp]
        using rpow_le_rpow nn₁ hp t_nn.le
    · have hp₁ : ¬ p₁ ∈ Ici 0 := nn₁
      by_cases nn₂ : 0 ≤ p₂
      · simpa [hp₁, show p₂ ∈ Ici 0 from nn₂] using rpow_nonneg nn₂ t
      · simp [hp₁, show ¬ p₂ ∈ Ici 0 from nn₂]
  · intro p
    by_cases p_nn : 0 ≤ p
    · apply ContinuousWithinAt.congr (f := fun q ↦ Real.rpow q t)
      · exact (continuous_rpow_const t_nn.le).continuousWithinAt
      · intro y hy
        simp [p_nn.trans hy]
      · simp [p_nn]
    · apply ContinuousWithinAt.congr_of_eventuallyEq (f := 0)
      · exact continuous_const.continuousWithinAt
      · have nhd : Iio 0 ∈ 𝓝[≥] p :=
          mem_nhdsGE_iff_exists_Ico_subset.mpr ⟨0, lt_of_not_ge p_nn, Ico_subset_Iio_self⟩
        filter_upwards [nhd] with y hy
        simp [show ¬ y ∈ Ici 0 from notMem_Ici.mpr hy]
      · simp [p_nn]

noncomputable def CumulativeDistributionFunction.pow
    (F : CumulativeDistributionFunction) {t : ℝ} (t_pos : 0 < t) :
    CumulativeDistributionFunction :=
  F.comp_rightOrdContinuous _ (Real.rightOrdContinuous_indicator_Ici_rpow t_pos)
    (by simpa using Real.zero_rpow t_pos.ne.symm) (by simp) <| by
      refine ((Real.continuous_rpow_const t_pos.le).continuousAt.congr_of_eventuallyEq ?_
        ).continuousWithinAt
      filter_upwards [Ioi_mem_nhds one_pos] with y hy
      rw [Set.indicator_of_mem (Set.mem_Ici.mpr (le_of_lt hy))]; rfl

lemma CumulativeDistributionFunction.pow_apply_eq
    (F : CumulativeDistributionFunction) {t : ℝ} (t_pos : 0 < t) (x : ℝ) :
    F.pow t_pos x = (F x) ^ t := by
  simp [pow, comp_rightOrdContinuous, show ¬ F x < 0 by simpa using apply_nonneg F x]

lemma CumulativeDistributionFunction.npow_apply_eq
    (F : CumulativeDistributionFunction) {n : ℕ} (n_pos : 0 < n) (x : ℝ) :
    F.pow (show 0 < (n : ℝ) from Nat.cast_pos'.mpr n_pos) x = (F x) ^ n := by
  simp [pow, comp_rightOrdContinuous, show ¬ F x < 0 by simpa using apply_nonneg F x]

@[simp] lemma CumulativeDistributionFunction.smul_pow_eq_pow_smul
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) {t : ℝ} (t_pos : 0 < t) :
    A • (F.pow t_pos) = (A • F).pow t_pos := by
  ext x
  simp only [mulAction_apply_eq, pow_apply_eq]

open Filter Topology in
-- Corrected from upstream: the hypothesis was `((As n) • F) x → G x`, which makes the statement
-- false (e.g. `As n = 1`, `F = G`, `G x = 1/2`, `t = 1` gives `(1/2)^n → 0 ≠ 1/2`); the intended
-- hypothesis is `((As n • F) x) ^ n → G x`, i.e. `As n • F^n → G` at `x`.
lemma continuous_parameter_ev_limit_relation
    {F G : CumulativeDistributionFunction} {As : ℕ → AffineIncrEquiv} {x : ℝ}
    (hAF : Tendsto (fun n ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) {t : ℝ} (t_pos : 0 < t) :
    Tendsto (fun n ↦ ((As n) • F).pow
        (t := 1 ⊔ Nat.floor (n * t)) (lt_max_of_lt_left zero_lt_one) x)
      atTop (𝓝 (G.pow t_pos x)) := by
  simp only [CumulativeDistributionFunction.pow_apply_eq]
  have hfl : Tendsto (fun n : ℕ ↦ (Nat.floor (t * n) : ℝ) / n) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop t_pos.le).comp tendsto_natCast_atTop_atTop
  refine (hAF.rpow hfl (Or.inr t_pos)).congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : 1 ≤ Nat.floor ((n : ℝ) * t) := by
    rw [Nat.one_le_floor_iff]
    have : (1 / t) * t ≤ (n : ℝ) * t := by
      gcongr; exact hN.trans (by exact_mod_cast (show N ≤ n by omega))
    rwa [one_div_mul_cancel t_pos.ne'] at this
  rw [max_eq_right (by exact_mod_cast h1), mul_comm t, ← Real.rpow_natCast,
    ← Real.rpow_mul ((As n • F).apply_nonneg x), mul_div_cancel₀ _ hn0.ne']

open Real

lemma CumulativeDistributionFunction.conjugate_smul_self_eq (G : CumulativeDistributionFunction)
    {F : CumulativeDistributionFunction} {A : AffineIncrEquiv} (hAG : A • G = F)
    (B : AffineIncrEquiv) :
    (B * A * B⁻¹) • (B • G) = B • F := by
  ext x
  rw [← congr_fun (f := fun x ↦ ((B * A * B⁻¹) • (B • G)) x) (g := fun x ↦ (B • F) x) ?_ x]
  simp only [show B • F = (B * A) • G by simp only [mul_smul, hAG],
             ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]

open AffineIncrEquiv in
lemma CumulativeDistributionFunction.selfSimilar_index_zero_transform
    (G : CumulativeDistributionFunction) {β s : ℝ} (β_pos : 0 < β)
    (hG : (homOfIndex₀ β s) • G = G.pow (exp_pos s)) :
    (homOfIndex₀ 1 s) • ((mkOfCoefs (Right.inv_pos.mpr β_pos) 0) • G)
      = ((mkOfCoefs (Right.inv_pos.mpr β_pos) 0) • G).pow (exp_pos s) := by
  have obs := ((mkOfCoefs (Right.inv_pos.mpr β_pos) 0)).conjugate_homOfIndex₀ β s
  simp only [coefs_fst_mkOfCoefs, mul_inv_cancel₀ β_pos.ne.symm] at obs
  rw [← smul_pow_eq_pow_smul, ← hG, ← obs]
  simp [← mul_smul]

open AffineIncrEquiv in
lemma CumulativeDistributionFunction.selfSimilar_index_apply {G : CumulativeDistributionFunction}
    {α c : ℝ} (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) (s x : ℝ) :
    G (exp (-(α * s)) * (x - c) + c) = G x ^ exp s := by
  have h := congrArg (fun F : CumulativeDistributionFunction ↦ F x) (hG s)
  simp only [CumulativeDistributionFunction.mulAction_apply_eq,
    CumulativeDistributionFunction.pow_apply_eq] at h
  rw [← h]
  congr 1
  simp only [homOfIndex_inv, apply_eq, homOfIndex_coefs_fst, homOfIndex_coefs_snd]
  ring_nf

open AffineIncrEquiv in
lemma CumulativeDistributionFunction.selfSimilar_index_zero_apply
    {G : CumulativeDistributionFunction} {β : ℝ}
    (hG : ∀ s : ℝ, (homOfIndex₀ β s) • G = G.pow (exp_pos s)) (s x : ℝ) :
    G (x - β * s) = G x ^ exp s := by
  have h := congrArg (fun F : CumulativeDistributionFunction ↦ F x) (hG s)
  simp only [CumulativeDistributionFunction.mulAction_apply_eq,
    CumulativeDistributionFunction.pow_apply_eq] at h
  rw [← h]
  congr 1
  simp only [homOfIndex₀_inv, apply_eq, homOfIndex₀_coefs_fst, homOfIndex₀_coefs_snd]
  ring_nf

open AffineIncrEquiv in
lemma CumulativeDistributionFunction.selfSimilar_apply_center {G : CumulativeDistributionFunction}
    {α c : ℝ} (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    G c = 0 ∨ G c = 1 := by
  have h := G.selfSimilar_index_apply hG (log 2) c
  rw [sub_self, mul_zero, zero_add, exp_log two_pos, rpow_two] at h
  have h' : G c * (G c - 1) = 0 := by rw [mul_sub, mul_one, ← sq]; linarith
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

open AffineIncrEquiv in
lemma CumulativeDistributionFunction.selfSimilar_apply_of_ratio_pos
    {G : CumulativeDistributionFunction} {α c : ℝ} (α_ne : α ≠ 0)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) {x y : ℝ}
    (hxy : 0 < (y - c) / (x - c)) :
    G y = G x ^ (((y - c) / (x - c)) ^ (-α⁻¹)) := by
  have hxc : x - c ≠ 0 := by intro h; simp [h] at hxy
  have h := G.selfSimilar_index_apply hG (-α⁻¹ * log ((y - c) / (x - c))) x
  have e1 : exp (-(α * (-α⁻¹ * log ((y - c) / (x - c))))) = (y - c) / (x - c) := by
    rw [neg_mul, mul_neg, neg_neg, ← mul_assoc, mul_inv_cancel₀ α_ne, one_mul]
    exact exp_log hxy
  rw [e1, div_mul_cancel₀ _ hxc, sub_add_cancel] at h
  rw [h, rpow_def_of_pos hxy, mul_comm]

lemma Real.rpow_rpow_eq_exp_aux {g a α : ℝ} (g0 : 0 < g) (g1 : g < 1) (α_ne : α ≠ 0)
    (a_nn : 0 ≤ a) :
    g ^ (a ^ (-α⁻¹)) = exp (-((a / (-(log g)) ^ α) ^ (-α⁻¹))) := by
  have L_pos : 0 < -log g := neg_pos.mpr (log_neg g0 g1)
  rw [div_rpow a_nn (rpow_nonneg L_pos.le _), ← rpow_mul L_pos.le,
      show α * -α⁻¹ = -1 by rw [mul_neg, mul_inv_cancel₀ α_ne], rpow_neg_one, div_inv_eq_mul,
      rpow_def_of_pos g0]
  congr 1
  ring

open AffineIncrEquiv in
lemma gumbel_type_of_selfSimilar_aux {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {β : ℝ} (β_pos : 0 < β)
    (hG : ∀ s : ℝ, (homOfIndex₀ β s) • G = G.pow (exp_pos s)) (x : ℝ) :
    G x = exp (-(exp (-β⁻¹ * x + log (- (log (G 0)))))) := by
  have key : ∀ y, G y = G 0 ^ exp (-β⁻¹ * y) := by
    intro y
    have h := G.selfSimilar_index_zero_apply hG (-β⁻¹ * y) 0
    have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ β_pos.ne'
    rwa [show (0:ℝ) - β * (-β⁻¹ * y) = y by linear_combination y * hb] at h
  have h0 : G 0 ≠ 0 := by
    intro h
    exact G_nondeg (fun y ↦ Or.inl (by rw [key y, h, zero_rpow (exp_pos _).ne']))
  have h1 : G 0 ≠ 1 := by
    intro h
    exact G_nondeg (fun y ↦ Or.inr (by rw [key y, h, one_rpow]))
  have g0 : 0 < G 0 := lt_of_le_of_ne (G.apply_nonneg 0) (Ne.symm h0)
  have g1 : G 0 < 1 := lt_of_le_of_ne (G.apply_le_one 0) h1
  rw [key x, rpow_def_of_pos g0, exp_add, exp_log (neg_pos.mpr (log_neg g0 g1))]
  congr 1
  ring

open AffineIncrEquiv in
lemma gumbel_type_of_selfSimilar_index_zero'' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) (hG : ∀ s : ℝ, (homOfIndex₀ 1 s) • G = G.pow (exp_pos s)) (x : ℝ) :
    G x = exp (-(exp (-x + log (- (log (G 0)))))) := by
  simpa using gumbel_type_of_selfSimilar_aux G_nondeg one_pos (by simpa using hG) x

open AffineIncrEquiv in
lemma gumbel_type_of_selfSimilar_index_zero' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {β : ℝ} (β_pos : 0 < β)
    (hG : ∀ s : ℝ, (homOfIndex₀ β s) • G = G.pow (exp_pos s)) :
    ∀ x, G x = exp (-(exp (-β⁻¹ * x + log (- (log (G 0)))))) :=
  gumbel_type_of_selfSimilar_aux G_nondeg β_pos hG

open AffineIncrEquiv in
theorem gumbel_type_of_selfSimilar_index_zero
    {G : CumulativeDistributionFunction} (G_nondeg : ¬ G.IsDegenerate) {β : ℝ} (β_pos : 0 < β)
    (hG : ∀ s : ℝ, (homOfIndex₀ β s) • G = G.pow (exp_pos s)) :
    G = (mkOfCoefs (Right.inv_pos.mpr β_pos) (-(log (- (log (G 0))))))⁻¹ • standardGumbelCDF := by
  ext x
  rw [gumbel_type_of_selfSimilar_index_zero' G_nondeg β_pos hG]
  simp only [CumulativeDistributionFunction.mulAction_apply_eq, inv_inv, apply_eq,
             coefs_fst_mkOfCoefs, coefs_snd_mkOfCoefs]
  rw [standardGumbelCDF_apply_eq]
  simp only [neg_mul, log_neg_eq_log, neg_add_rev, neg_neg, exp_eq_exp, neg_inj]
  ring

open AffineIncrEquiv Topology Filter in
lemma apply_eq_zero_of_lt_of_selfSimilar_index_pos' {G : CumulativeDistributionFunction}
    {α c : ℝ} (α_pos : 0 < α) (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s))
    {x : ℝ} (hx : x < c) :
    G x = 0 := by
  have Gx_eq : (G x) ^ 2 = G x := by
    have Gx_sq : (homOfIndex α c (Real.log 2) • G) x = (G x) ^ 2 := by
      rw [← CumulativeDistributionFunction.npow_apply_eq G zero_lt_two x, hG (Real.log 2)]
      congr
      simpa only [Nat.cast_ofNat] using exp_log zero_lt_two
    have obs : (homOfIndex α c (Real.log 2))⁻¹ x > x := by
      simp only [homOfIndex_inv, apply_eq, homOfIndex_coefs_fst, mul_neg, homOfIndex_coefs_snd]
      have aux_pos : 0 < rexp (-(α * log 2)) := exp_pos _
      have aux_lt_one : rexp (-(α * log 2)) < 1 := by
        simpa only [exp_lt_one_iff, Left.neg_neg_iff, mul_comm]
          using mul_pos (log_pos one_lt_two) α_pos
      linarith [show (c - x) * (1 - rexp (-(α * log 2))) > 0
                from mul_pos (by linarith) (by linarith)]
    apply le_antisymm
    · exact pow_le_of_le_one (G.apply_nonneg x) (G.apply_le_one x) two_ne_zero
    · simpa [← Gx_sq] using G.mono obs.le
  have Gx_eq_01 : G x = 0 ∨ G x = 1 := by
    rw [← sub_eq_zero (b := (1 : ℝ)), ← mul_eq_zero]
    linarith
  cases' Gx_eq_01 with h0 h1
  · exact h0 -- This what actually happens.
  -- The other case leads to a contradiction.
  exfalso
  have Gx_pow (s : ℝ) : (homOfIndex α c s • G) x = Real.rpow (G x) (Real.exp s) := by
    simp only [rpow_eq_pow, ← CumulativeDistributionFunction.pow_apply_eq G (exp_pos s) x, hG s]
  have but : Tendsto (fun (s : ℝ) ↦ (homOfIndex α c s)⁻¹ x) atBot atBot := by
    have same_but : Tendsto (fun s ↦ Real.exp (-(α * s)) * (x - c) + c) atBot atBot := by
      apply tendsto_atBot_add_const_right atBot c
      apply (tendsto_mul_const_atBot_of_neg (show x - c < 0 by linarith)).mpr
      apply tendsto_exp_atTop.comp
      simp only [tendsto_neg_atTop_iff]
      exact (tendsto_const_mul_atBot_of_pos α_pos).mpr tendsto_id
    exact same_but.congr fun s => by
      simp only [homOfIndex_inv, apply_eq, homOfIndex_coefs_fst, mul_neg, homOfIndex_coefs_snd]
      ring
  have oops (s : ℝ) : G ((homOfIndex α c s)⁻¹ x) = 1 := by
    change (homOfIndex α c s • G) x = 1
    rw [Gx_pow s] -- (Keep this as a separate step to avoid risk of unwanted simping.)
    simp [h1]
  have well := (G.tendsto_atBot).comp but
  apply zero_lt_one.ne
    (tendsto_nhds_unique (Tendsto.congr (f₂ := fun _ ↦ 1) ?_ well) tendsto_const_nhds)
  intro s
  dsimp
  rw [← CumulativeDistributionFunction.mulAction_apply_eq, Gx_pow] -- (Avoid unwanted simping.)
  simp [h1]

open AffineIncrEquiv in
lemma frechet_apply_mem_Ioo_of_selfSimilar_index_pos {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    0 < G (c + 1) ∧ G (c + 1) < 1 := by
  have key : G (c + 1) ≠ 0 ∧ G (c + 1) ≠ 1 := by
    by_contra hcon
    have h01 : G (c + 1) = 0 ∨ G (c + 1) = 1 := by tauto
    refine G_nondeg (fun z ↦ ?_)
    rcases lt_trichotomy z c with hz | hz | hz
    · exact Or.inl (apply_eq_zero_of_lt_of_selfSimilar_index_pos' α_pos hG hz)
    · exact hz ▸ G.selfSimilar_apply_center hG
    · have hr : 0 < (z - c) / (c + 1 - c) := by rw [add_sub_cancel_left, div_one]; linarith
      rw [G.selfSimilar_apply_of_ratio_pos α_pos.ne' hG hr]
      have hp : ((z - c) / (c + 1 - c)) ^ (-α⁻¹) ≠ 0 := (rpow_pos_of_pos hr _).ne'
      rcases h01 with h | h
      · exact Or.inl (by rw [h, zero_rpow hp])
      · exact Or.inr (by rw [h, one_rpow])
  exact ⟨lt_of_le_of_ne (G.apply_nonneg _) (Ne.symm key.1),
    lt_of_le_of_ne (G.apply_le_one _) key.2⟩

open AffineIncrEquiv in
lemma frechet_scale_pos_of_selfSimilar_index_pos' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    0 < (-(log (G (c + 1)))) ^ α := by
  apply rpow_pos_of_pos
  simp only [Left.neg_pos_iff]
  apply log_neg
  · exact (frechet_apply_mem_Ioo_of_selfSimilar_index_pos G_nondeg α_pos hG).1
  · exact (frechet_apply_mem_Ioo_of_selfSimilar_index_pos G_nondeg α_pos hG).2

open AffineIncrEquiv in
lemma frechet_type_of_selfSimilar_index_pos' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) {x : ℝ} (hx : c < x) :
    G x = exp (-(((x - c) / ((-(log (G (c + 1)))) ^ α)) ^ (-α⁻¹))) := by
  obtain ⟨h0, h1⟩ := frechet_apply_mem_Ioo_of_selfSimilar_index_pos G_nondeg α_pos hG
  have hr : 0 < (x - c) / (c + 1 - c) := by rw [add_sub_cancel_left, div_one]; linarith
  rw [G.selfSimilar_apply_of_ratio_pos α_pos.ne' hG hr, add_sub_cancel_left, div_one]
  exact Real.rpow_rpow_eq_exp_aux h0 h1 α_pos.ne' (by linarith)

open AffineIncrEquiv in
theorem frechet_type_of_selfSimilar_index_pos
    {G : CumulativeDistributionFunction} (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    G = (mkOfCoefs (frechet_scale_pos_of_selfSimilar_index_pos' G_nondeg α_pos hG) c)
        • standardFrechetCDF (Right.inv_pos.mpr α_pos) := by
  have scale_pos := frechet_scale_pos_of_selfSimilar_index_pos' G_nondeg α_pos hG
  have scale_inv_pos : 0 < ((-log (G (c + 1))) ^ α)⁻¹ := Right.inv_pos.mpr scale_pos
  set A := (mkOfCoefs (frechet_scale_pos_of_selfSimilar_index_pos' G_nondeg α_pos hG) c) with def_A
  apply CumulativeDistributionFunction.eq_of_forall_dense_eq (dense_compl_singleton c)
  intro x x_ne_c
  by_cases hxc : x < c
  · rw [apply_eq_zero_of_lt_of_selfSimilar_index_pos' α_pos hG hxc]
    have Ainv_x_neg : A⁻¹ x < 0 := by
      simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
                 coefs_snd_mkOfCoefs, neg_mul, add_neg_lt_iff_lt_add, zero_add]
      exact (mul_lt_mul_iff_of_pos_left scale_inv_pos).mpr hxc
    simp only [CumulativeDistributionFunction.mulAction_apply_eq]
    rw [standardFrechetCDF_apply_nonpos_eq]
    exact Ainv_x_neg.le
  · have hxc' : c < x := lt_of_le_of_ne (not_lt.mp hxc) fun h ↦ x_ne_c h.symm
    rw [frechet_type_of_selfSimilar_index_pos' G_nondeg α_pos hG hxc']
    have Ainv_x_pos : 0 < A⁻¹ x := by
      simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
                 coefs_snd_mkOfCoefs, neg_mul, lt_add_neg_iff_add_lt, zero_add]
      exact (mul_lt_mul_iff_of_pos_left scale_inv_pos).mpr hxc'
    simp only [CumulativeDistributionFunction.mulAction_apply_eq]
    rw [standardFrechetCDF_apply_pos_eq _ Ainv_x_pos]
    simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
               coefs_snd_mkOfCoefs, neg_mul, rpow_eq_pow, exp_eq_exp, neg_inj]
    congr
    ring

open AffineIncrEquiv Topology Filter in
lemma apply_eq_one_of_gt_of_selfSimilar_index_neg' {G : CumulativeDistributionFunction}
    {α c : ℝ} (α_neg : α < 0) (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s))
    {x : ℝ} (hx : c < x) :
    G x = 1 := by
  have hsq := G.selfSimilar_index_apply hG (log 2) x
  rw [exp_log two_pos, rpow_two] at hsq
  have hge : x ≤ exp (-(α * log 2)) * (x - c) + c := by
    have : 1 ≤ exp (-(α * log 2)) :=
      one_le_exp (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg α_neg.le (log_nonneg one_le_two)))
    nlinarith [mul_nonneg (sub_nonneg.mpr this) (sub_nonneg.mpr hx.le)]
  have Gx_eq : G x ^ 2 = G x := le_antisymm
    (pow_le_of_le_one (G.apply_nonneg x) (G.apply_le_one x) two_ne_zero) (hsq ▸ G.mono hge)
  have h' : G x * (G x - 1) = 0 := by rw [mul_sub, mul_one, ← sq]; linarith
  rcases mul_eq_zero.mp h' with h0 | h1
  · exfalso
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (G.tendsto_atTop.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)))
    have hz : (1 / 2 : ℝ) < G (max N x) := hN _ (le_max_left _ _)
    have hr : 0 < (max N x - c) / (x - c) :=
      div_pos (by linarith [le_max_right N x]) (by linarith)
    have := G.selfSimilar_apply_of_ratio_pos α_neg.ne hG hr
    rw [h0, zero_rpow (rpow_pos_of_pos hr _).ne'] at this
    linarith
  · linarith

open AffineIncrEquiv in
lemma weibull_apply_mem_Ioo_of_selfSimilar_index_neg {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    0 < G (c - 1) ∧ G (c - 1) < 1 := by
  have key : G (c - 1) ≠ 0 ∧ G (c - 1) ≠ 1 := by
    by_contra hcon
    have h01 : G (c - 1) = 0 ∨ G (c - 1) = 1 := by tauto
    refine G_nondeg (fun z ↦ ?_)
    rcases lt_trichotomy z c with hz | hz | hz
    · have hratio : (z - c) / (c - 1 - c) = c - z := by ring
      have hr : 0 < (z - c) / (c - 1 - c) := by rw [hratio]; linarith
      rw [G.selfSimilar_apply_of_ratio_pos α_neg.ne hG hr]
      have hp : ((z - c) / (c - 1 - c)) ^ (-α⁻¹) ≠ 0 := (rpow_pos_of_pos hr _).ne'
      rcases h01 with h | h
      · exact Or.inl (by rw [h, zero_rpow hp])
      · exact Or.inr (by rw [h, one_rpow])
    · exact hz ▸ G.selfSimilar_apply_center hG
    · exact Or.inr (apply_eq_one_of_gt_of_selfSimilar_index_neg' α_neg hG hz)
  exact ⟨lt_of_le_of_ne (G.apply_nonneg _) (Ne.symm key.1),
    lt_of_le_of_ne (G.apply_le_one _) key.2⟩

open AffineIncrEquiv in
lemma weibull_scale_pos_of_selfSimilar_index_neg' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    0 < (-(log (G (c - 1)))) ^ α := by
  -- Corrected from upstream, whose exponent `-α` gave the wrong Weibull scale (see
  -- `weibull_type_of_selfSimilar_index_neg'`).
  apply rpow_pos_of_pos
  simp only [Left.neg_pos_iff]
  apply log_neg
  · exact (weibull_apply_mem_Ioo_of_selfSimilar_index_neg G_nondeg α_neg hG).1
  · exact (weibull_apply_mem_Ioo_of_selfSimilar_index_neg G_nondeg α_neg hG).2

open AffineIncrEquiv in
lemma weibull_type_of_selfSimilar_index_neg' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) {x : ℝ} (hx : x ≤ c) :
    G x = exp (-(((c - x) / ((-(log (G (c - 1)))) ^ α)) ^ (-α⁻¹))) := by
  obtain ⟨h0, h1⟩ := weibull_apply_mem_Ioo_of_selfSimilar_index_neg G_nondeg α_neg hG
  rw [← Real.rpow_rpow_eq_exp_aux h0 h1 α_neg.ne (by linarith : 0 ≤ c - x)]
  rcases hx.lt_or_eq with hx | hx
  · have hratio : (x - c) / (c - 1 - c) = c - x := by ring
    have hr : 0 < (x - c) / (c - 1 - c) := by rw [hratio]; linarith
    rw [G.selfSimilar_apply_of_ratio_pos α_neg.ne hG hr, hratio]
  · rw [hx, sub_self, zero_rpow (neg_ne_zero.mpr (inv_ne_zero α_neg.ne)), rpow_zero]
    rcases G.selfSimilar_apply_center hG with h | h
    · exfalso
      refine G_nondeg (fun z ↦ ?_)
      rcases le_or_gt z c with hz | hz
      · exact Or.inl (le_antisymm (h ▸ G.mono hz) (G.apply_nonneg z))
      · exact Or.inr (apply_eq_one_of_gt_of_selfSimilar_index_neg' α_neg hG hz)
    · exact h

example (ξ : ℝ) (hξ : ξ < 0) : 0 < -ξ⁻¹ := by simp [hξ]

open AffineIncrEquiv in
theorem weibull_type_of_selfSimilar_index_neg
    {G : CumulativeDistributionFunction} (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s : ℝ, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    G = (mkOfCoefs (weibull_scale_pos_of_selfSimilar_index_neg' G_nondeg α_neg hG) c)
        • standardWeibullCDF (show 0 < -α⁻¹ by simp [α_neg]) := by
  have scale_pos := weibull_scale_pos_of_selfSimilar_index_neg' G_nondeg α_neg hG
  have scale_inv_pos : 0 < ((-log (G (c - 1))) ^ α)⁻¹ := Right.inv_pos.mpr scale_pos
  set A := (mkOfCoefs (weibull_scale_pos_of_selfSimilar_index_neg' G_nondeg α_neg hG) c)
    with def_A
  apply CumulativeDistributionFunction.eq_of_forall_dense_eq (dense_compl_singleton c)
  intro x x_ne_c
  by_cases hxc : c < x
  · rw [apply_eq_one_of_gt_of_selfSimilar_index_neg' α_neg hG hxc]
    have Ainv_x_pos : 0 < A⁻¹ x := by
      simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
                 coefs_snd_mkOfCoefs, neg_mul, lt_add_neg_iff_add_lt, zero_add]
      exact (mul_lt_mul_iff_of_pos_left scale_inv_pos).mpr hxc
    simp only [CumulativeDistributionFunction.mulAction_apply_eq]
    rw [standardWeibullCDF_apply_nonneg_eq _ Ainv_x_pos.le]
  · have hxc' : x < c := lt_of_le_of_ne (not_lt.mp hxc) x_ne_c
    rw [weibull_type_of_selfSimilar_index_neg' G_nondeg α_neg hG hxc'.le]
    have Ainv_x_neg : A⁻¹ x < 0 := by
      simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
                 coefs_snd_mkOfCoefs, neg_mul, add_neg_lt_iff_lt_add, zero_add]
      exact (mul_lt_mul_iff_of_pos_left scale_inv_pos).mpr hxc'
    simp only [CumulativeDistributionFunction.mulAction_apply_eq]
    rw [standardWeibullCDF_apply_neg_eq _ Ainv_x_neg]
    simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
               coefs_snd_mkOfCoefs, neg_mul, rpow_eq_pow, exp_eq_exp, neg_inj]
    congr 1
    ring

end self_similar_cdf
