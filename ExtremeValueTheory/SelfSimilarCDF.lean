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


section convergence_of_types_aux

open Real Filter Topology Set

namespace CumulativeDistributionFunction

private lemma dense_continuousAt' (F : CumulativeDistributionFunction) :
    Dense {x | ContinuousAt F x} := by
  simpa [compl] using
    Set.Countable.dense_compl (𝕜 := ℝ) (Monotone.countable_not_continuousAt F.mono')

private lemma exists_continuousAt_lt' (F : CumulativeDistributionFunction) {ε : ℝ}
    (ε_pos : 0 < ε) : ∃ a, F a < ε ∧ ContinuousAt F a := by
  obtain ⟨x', hx'⟩ := (F.tendsto_atBot.eventually (eventually_lt_nhds ε_pos)).exists
  obtain ⟨a, ha_cont, ha⟩ := F.dense_continuousAt'.exists_between (show x' - 1 < x' by linarith)
  exact ⟨a, (F.mono ha.2.le).trans_lt hx', ha_cont⟩

private lemma exists_continuousAt_gt' (F : CumulativeDistributionFunction) {c : ℝ}
    (hc : c < 1) : ∃ b, c < F b ∧ ContinuousAt F b := by
  obtain ⟨y', hy'⟩ := (F.tendsto_atTop.eventually (eventually_gt_nhds hc)).exists
  obtain ⟨b, hb_cont, hb⟩ := F.dense_continuousAt'.exists_between (show y' < y' + 1 by linarith)
  exact ⟨b, lt_of_lt_of_le hy' (F.mono hb.1.le), hb_cont⟩

private lemma exists₂_continuousAt' (F : CumulativeDistributionFunction)
    (hF : ¬ F.IsDegenerate) :
    ∃ x₁ x₂, x₁ < x₂ ∧ 0 < F x₁ ∧ F x₂ < 1 ∧ ContinuousAt F x₁ ∧ ContinuousAt F x₂ := by
  obtain ⟨x, hx0, hx1⟩ : ∃ x, F x ≠ 0 ∧ F x ≠ 1 := by
    by_contra h
    push Not at h
    exact hF (fun x ↦ by
      by_cases h0 : F x = 0
      · exact Or.inl h0
      · exact Or.inr (h x h0))
  have hlt : F x < 1 := lt_of_le_of_ne (F.apply_le_one x) hx1
  have hpos : 0 < F x := lt_of_le_of_ne (F.apply_nonneg x) (Ne.symm hx0)
  have hev : ∀ᶠ y in 𝓝[≥] x, F y < 1 := (F.right_continuous x).eventually (gt_mem_nhds hlt)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  obtain ⟨x₁, h1c, h1⟩ := F.dense_continuousAt'.exists_between hu
  obtain ⟨x₂, h2c, h2⟩ := F.dense_continuousAt'.exists_between h1.2
  refine ⟨x₁, x₂, h2.1, hpos.trans_le (F.mono h1.1.le), ?_, h1c, h2c⟩
  exact hsub ⟨(h1.1.trans h2.1).le, h2.2⟩

private lemma iterate_apply_eq' (G : CumulativeDistributionFunction) {A : AffineIncrEquiv}
    (hA : ∀ x, G (A x) = G x) (n : ℕ) (x : ℝ) :
    G ((⇑A)^[n] x) = G x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hA, ih]

private lemma apply_eq_one_of_iterate_tendsto_atTop (G : CumulativeDistributionFunction)
    {A : AffineIncrEquiv} (hA : ∀ x, G (A x) = G x) {x : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (⇑A)^[n] x) atTop atTop) : G x = 1 := by
  have h2 : Tendsto (fun _ : ℕ ↦ G x) atTop (𝓝 1) :=
    (G.tendsto_atTop.comp h).congr (fun n ↦ iterate_apply_eq' G hA n x)
  exact tendsto_nhds_unique tendsto_const_nhds h2

private lemma apply_eq_zero_of_iterate_tendsto_atBot (G : CumulativeDistributionFunction)
    {A : AffineIncrEquiv} (hA : ∀ x, G (A x) = G x) {x : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (⇑A)^[n] x) atTop atBot) : G x = 0 := by
  have h2 : Tendsto (fun _ : ℕ ↦ G x) atTop (𝓝 0) :=
    (G.tendsto_atBot.comp h).congr (fun n ↦ iterate_apply_eq' G hA n x)
  exact tendsto_nhds_unique tendsto_const_nhds h2

private lemma false_of_apply_invariant_of_one_lt (G : CumulativeDistributionFunction)
    (hG : ¬ G.IsDegenerate) {A : AffineIncrEquiv} (hA : ∀ x, G (A x) = G x)
    (ha : 1 < A.coefs.1) : False := by
  obtain ⟨x₁, x₂, hlt, h1, h2, -, -⟩ := G.exists₂_continuousAt' hG
  set a := A.coefs.1 with def_a
  set b := A.coefs.2 with def_b
  have ha' : 1 - a ≠ 0 := by intro h; linarith
  set c := b / (1 - a) with def_c
  have hc : a * c + b = c := by
    rw [def_c]
    field_simp
    ring
  have hiter : ∀ n : ℕ, ∀ x, (⇑A)^[n] x = a ^ n * (x - c) + c := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, AffineIncrEquiv.apply_eq, pow_succ]
      linear_combination hc
  have hpow : Tendsto (fun n : ℕ ↦ a ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt ha
  have key : ∀ x, 0 < G x → G x < 1 → x = c := by
    intro x hx0 hx1
    rcases lt_trichotomy x c with hxc | hxc | hxc
    · exfalso
      have : Tendsto (fun n : ℕ ↦ (⇑A)^[n] x) atTop atBot := by
        simp_rw [hiter]
        exact tendsto_atBot_add_const_right _ c
          ((tendsto_mul_const_atBot_of_neg (by linarith : x - c < 0)).mpr hpow)
      exact hx0.ne' (apply_eq_zero_of_iterate_tendsto_atBot G hA this)
    · exact hxc
    · exfalso
      have : Tendsto (fun n : ℕ ↦ (⇑A)^[n] x) atTop atTop := by
        simp_rw [hiter]
        exact tendsto_atTop_add_const_right _ c (hpow.atTop_mul_const (by linarith))
      exact hx1.ne (apply_eq_one_of_iterate_tendsto_atTop G hA this)
  have G1 : 0 < G x₁ ∧ G x₁ < 1 := ⟨h1, lt_of_le_of_lt (G.mono hlt.le) h2⟩
  have G2 : 0 < G x₂ ∧ G x₂ < 1 := ⟨lt_of_lt_of_le h1 (G.mono hlt.le), h2⟩
  exact hlt.ne ((key x₁ G1.1 G1.2).trans (key x₂ G2.1 G2.2).symm)

/-- A nondegenerate c.d.f. is not invariant under any nontrivial affine transformation. -/
private lemma eq_one_of_smul_eq_self (G : CumulativeDistributionFunction)
    (hG : ¬ G.IsDegenerate) {A : AffineIncrEquiv} (h : A • G = G) : A = 1 := by
  have hA : ∀ x, G (A x) = G x := by
    intro x
    have := congrArg (fun F : CumulativeDistributionFunction ↦ F (A x)) h
    simp only [mulAction_apply_eq_self_apply] at this
    exact this.symm
  have hAinv : ∀ x, G (A⁻¹ x) = G x := by
    intro x
    have h' := hA (A⁻¹ x)
    have e : A (A⁻¹ x) = x := EquivLike.right_inv A x
    rw [e] at h'
    exact h'.symm
  rcases lt_trichotomy A.coefs.1 1 with ha | ha | ha
  · exact (false_of_apply_invariant_of_one_lt G hG hAinv
      (by rw [AffineIncrEquiv.inv_coefs_fst]; exact (one_lt_inv₀ A.coefs_fst_pos).mpr ha)).elim
  · obtain ⟨x₀, x₃, hlt, h1, h2, -, -⟩ := G.exists₂_continuousAt' hG
    have h2' : G x₀ < 1 := lt_of_le_of_lt (G.mono hlt.le) h2
    have hiter : ∀ n : ℕ, ∀ x, (⇑A)^[n] x = n * A.coefs.2 + x := by
      intro n x
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, AffineIncrEquiv.apply_eq, ha]
        push_cast
        ring
    rcases lt_trichotomy A.coefs.2 0 with hb | hb | hb
    · exfalso
      have : Tendsto (fun n : ℕ ↦ (⇑A)^[n] x₀) atTop atBot := by
        simp_rw [hiter]
        exact tendsto_atBot_add_const_right _ x₀
          ((tendsto_mul_const_atBot_of_neg hb).mpr tendsto_natCast_atTop_atTop)
      exact h1.ne' (apply_eq_zero_of_iterate_tendsto_atBot G hA this)
    · ext x
      rw [AffineIncrEquiv.apply_eq, ha, hb, AffineIncrEquiv.one_apply]
      ring
    · exfalso
      have : Tendsto (fun n : ℕ ↦ (⇑A)^[n] x₀) atTop atTop := by
        simp_rw [hiter]
        exact tendsto_atTop_add_const_right _ x₀ (tendsto_natCast_atTop_atTop.atTop_mul_const hb)
      exact h2'.ne (apply_eq_one_of_iterate_tendsto_atTop G hA this)
  · exact (false_of_apply_invariant_of_one_lt G hG hA ha).elim

private lemma smul_left_cancel_of_not_isDegenerate (G : CumulativeDistributionFunction)
    (hG : ¬ G.IsDegenerate) {A₁ A₂ : AffineIncrEquiv} (h : A₁ • G = A₂ • G) : A₁ = A₂ := by
  have : (A₂⁻¹ * A₁) • G = G := by rw [mul_smul, h, inv_smul_smul]
  exact (inv_mul_eq_one.mp (eq_one_of_smul_eq_self G hG this)).symm

end CumulativeDistributionFunction

end convergence_of_types_aux

section convergence_of_types

open Real Filter Topology Set

namespace CumulativeDistributionFunction

private lemma tendsto_apply_of_tendsto_of_tendsto' (H : ℕ → CumulativeDistributionFunction)
    (G : CumulativeDistributionFunction)
    (hH : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ H n x) atTop (𝓝 (G x)))
    {y : ℕ → ℝ} {y₀ : ℝ} (hy : Tendsto y atTop (𝓝 y₀)) (hc : ContinuousAt G y₀) :
    Tendsto (fun n ↦ H n (y n)) atTop (𝓝 (G y₀)) := by
  rw [tendsto_order]
  constructor
  · intro l hl
    have hev : ∀ᶠ z in 𝓝 y₀, l < G z := hc.eventually (lt_mem_nhds hl)
    obtain ⟨l', u', ⟨hl', hu'⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
    obtain ⟨y', hy'c, hy'⟩ := G.dense_continuousAt'.exists_between hl'
    have h1 : l < G y' := hsub ⟨hy'.1, hy'.2.trans hu'⟩
    filter_upwards [(hH y' hy'c).eventually (lt_mem_nhds h1), hy.eventually (lt_mem_nhds hy'.2)]
      with n hn1 hn2
    exact lt_of_lt_of_le hn1 ((H n).mono hn2.le)
  · intro l hl
    have hev : ∀ᶠ z in 𝓝 y₀, G z < l := hc.eventually (gt_mem_nhds hl)
    obtain ⟨l', u', ⟨hl', hu'⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
    obtain ⟨y', hy'c, hy'⟩ := G.dense_continuousAt'.exists_between hu'
    have h1 : G y' < l := hsub ⟨hl'.trans hy'.1, hy'.2⟩
    filter_upwards [(hH y' hy'c).eventually (gt_mem_nhds h1), hy.eventually (gt_mem_nhds hy'.1)]
      with n hn1 hn2
    exact lt_of_le_of_lt ((H n).mono hn2.le) hn1

private lemma eventually_bounds_of_tendsto (H : ℕ → CumulativeDistributionFunction)
    (G₁ G₂ : CumulativeDistributionFunction) (B : ℕ → AffineIncrEquiv)
    (hH : ∀ x, ContinuousAt G₁ x → Tendsto (fun n ↦ H n x) atTop (𝓝 (G₁ x)))
    (hBH : ∀ x, ContinuousAt G₂ x → Tendsto (fun n ↦ (B n • H n) x) atTop (𝓝 (G₂ x)))
    (hG₂ : ¬ G₂.IsDegenerate) :
    ∃ z₁ z₂ u v, z₁ < z₂ ∧ ∀ᶠ n in atTop, u < (B n)⁻¹ z₁ ∧ (B n)⁻¹ z₂ < v := by
  obtain ⟨z₁, z₂, hz, h1, h2, c1, c2⟩ := G₂.exists₂_continuousAt' hG₂
  obtain ⟨u, hu, hu_c⟩ := G₁.exists_continuousAt_lt' h1
  obtain ⟨v, hv, hv_c⟩ := G₁.exists_continuousAt_gt' h2
  refine ⟨z₁, z₂, u, v, hz, ?_⟩
  have e1 := (hH u hu_c).eventually (gt_mem_nhds (show G₁ u < (G₁ u + G₂ z₁) / 2 by linarith))
  have e2 := (hBH z₁ c1).eventually (lt_mem_nhds (show (G₁ u + G₂ z₁) / 2 < G₂ z₁ by linarith))
  have e3 := (hH v hv_c).eventually (lt_mem_nhds (show (G₁ v + G₂ z₂) / 2 < G₁ v by linarith))
  have e4 := (hBH z₂ c2).eventually (gt_mem_nhds (show G₂ z₂ < (G₁ v + G₂ z₂) / 2 by linarith))
  filter_upwards [e1, e2, e3, e4] with n h1 h2 h3 h4
  simp only [mulAction_apply_eq] at h2 h4
  constructor
  · by_contra hcon
    push Not at hcon
    linarith [(H n).mono hcon]
  · by_contra hcon
    push Not at hcon
    linarith [(H n).mono hcon]

/-- **Convergence of types** (existence part): if `Hₙ → G₁` and `Bₙ • Hₙ → G₂` with `G₁`, `G₂`
nondegenerate, then `G₂` is an affine transform of `G₁`. -/
private lemma exists_smul_eq_of_tendsto (H : ℕ → CumulativeDistributionFunction)
    (G₁ G₂ : CumulativeDistributionFunction) (B : ℕ → AffineIncrEquiv)
    (hH : ∀ x, ContinuousAt G₁ x → Tendsto (fun n ↦ H n x) atTop (𝓝 (G₁ x)))
    (hBH : ∀ x, ContinuousAt G₂ x → Tendsto (fun n ↦ (B n • H n) x) atTop (𝓝 (G₂ x)))
    (hG₁ : ¬ G₁.IsDegenerate) (hG₂ : ¬ G₂.IsDegenerate) :
    ∃ A : AffineIncrEquiv, A • G₁ = G₂ := by
  obtain ⟨z₁, z₂, u, v, hz, hev⟩ := eventually_bounds_of_tendsto H G₁ G₂ B hH hBH hG₂
  have hH' : ∀ x, ContinuousAt G₁ x →
      Tendsto (fun n ↦ ((B n)⁻¹ • (B n • H n)) x) atTop (𝓝 (G₁ x)) := by
    simpa only [inv_smul_smul] using hH
  obtain ⟨x₁, x₂, u', v', hx, hev'⟩ :=
    eventually_bounds_of_tendsto (fun n ↦ B n • H n) G₂ G₁ (fun n ↦ (B n)⁻¹) hBH hH' hG₁
  simp only [inv_inv] at hev'
  -- Bounds for the coefficients.
  have hcoef : ∀ᶠ n in atTop, z₂ - z₁ < (v - u) * (B n).coefs.1 ∧
      (B n).coefs.1 * (x₂ - x₁) < v' - u' ∧
      u' < (B n).coefs.1 * x₁ + (B n).coefs.2 ∧ (B n).coefs.1 * x₂ + (B n).coefs.2 < v' := by
    filter_upwards [hev, hev'] with n h h'
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h1', h2'⟩ := h'
    simp only [AffineIncrEquiv.apply_eq, AffineIncrEquiv.inv_coefs_fst,
      AffineIncrEquiv.inv_coefs_snd] at h1 h2 h1' h2'
    have apos := (B n).coefs_fst_pos
    set a := (B n).coefs.1
    set b := (B n).coefs.2
    have e1 : a * (a⁻¹ * z₁ + -a⁻¹ * b) = z₁ - b := by field_simp; ring
    have e2 : a * (a⁻¹ * z₂ + -a⁻¹ * b) = z₂ - b := by field_simp; ring
    have k1 : a * u < z₁ - b := by rw [← e1]; exact mul_lt_mul_of_pos_left h1 apos
    have k2 : z₂ - b < a * v := by rw [← e2]; exact mul_lt_mul_of_pos_left h2 apos
    refine ⟨by linarith, ?_, h1', ?_⟩
    · have : a * x₁ + b < a * x₂ + b := by nlinarith
      nlinarith
    · nlinarith [mul_lt_mul_of_pos_left hx apos]
  obtain ⟨n₀, hn₀⟩ := hcoef.exists
  have vu_pos : 0 < v - u := by
    by_contra hcon
    push Not at hcon
    nlinarith [hn₀.1, (B n₀).coefs_fst_pos]
  set M := (v' - u') / (x₂ - x₁) with def_M
  set δ := (z₂ - z₁) / (v - u) with def_δ
  have δ_pos : 0 < δ := div_pos (by linarith) vu_pos
  set K₁ := u' - M * |x₁|
  set K₂ := v' + M * |x₂|
  have hS : ∀ᶠ n in atTop, ((B n).coefs.1, (B n).coefs.2) ∈ Icc δ M ×ˢ Icc K₁ K₂ := by
    filter_upwards [hcoef] with n hn
    obtain ⟨h1, h2, h3, h4⟩ := hn
    have apos := (B n).coefs_fst_pos
    set a := (B n).coefs.1
    set b := (B n).coefs.2
    have haδ : δ ≤ a := by rw [def_δ, div_le_iff₀ vu_pos]; linarith
    have haM : a ≤ M := by rw [def_M, le_div_iff₀ (by linarith)]; linarith
    have t1 : a * x₁ ≤ M * |x₁| :=
      (mul_le_mul_of_nonneg_left (le_abs_self x₁) apos.le).trans
        (mul_le_mul_of_nonneg_right haM (abs_nonneg _))
    have t2 : -(a * x₂) ≤ M * |x₂| := by
      rw [← mul_neg]
      exact (mul_le_mul_of_nonneg_left (neg_le_abs x₂) apos.le).trans
        (mul_le_mul_of_nonneg_right haM (abs_nonneg _))
    refine ⟨⟨haδ, haM⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨p, hp, φ, hφ, hlim⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq' hS.frequently
  have p_pos : 0 < p.1 := lt_of_lt_of_le δ_pos hp.1.1
  set A := AffineIncrEquiv.mkOfCoefs p_pos p.2 with def_A
  have ha_lim : Tendsto (fun n ↦ (B (φ n)).coefs.1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hlim
  have hb_lim : Tendsto (fun n ↦ (B (φ n)).coefs.2) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hBinv : ∀ y, Tendsto (fun n ↦ (B (φ n))⁻¹ y) atTop (𝓝 (A⁻¹ y)) := by
    intro y
    have h := ((ha_lim.inv₀ p_pos.ne').mul_const y).add ((ha_lim.inv₀ p_pos.ne').neg.mul hb_lim)
    simp only [AffineIncrEquiv.apply_eq, AffineIncrEquiv.inv_coefs_fst,
      AffineIncrEquiv.inv_coefs_snd, def_A, AffineIncrEquiv.coefs_fst_mkOfCoefs,
      AffineIncrEquiv.coefs_snd_mkOfCoefs]
    simpa only [neg_mul] using h
  have hlim1 : ∀ y, ContinuousAt (A • G₁) y →
      Tendsto (fun n ↦ (B (φ n) • H (φ n)) y) atTop (𝓝 ((A • G₁) y)) := by
    intro y hy
    rw [affine_continuousAt_iff] at hy
    simp only [mulAction_apply_eq]
    exact tendsto_apply_of_tendsto_of_tendsto' (fun n ↦ H (φ n)) G₁
      (fun x hx ↦ (hH x hx).comp hφ.tendsto_atTop) (hBinv y) hy
  refine ⟨A, ?_⟩
  have hD : Dense {x | ContinuousAt (A • G₁) x ∧ ContinuousAt G₂ x} := by
    have hcount := ((A • G₁).mono'.countable_not_continuousAt).union
      (G₂.mono'.countable_not_continuousAt)
    refine (hcount.dense_compl (𝕜 := ℝ)).mono (fun x hx ↦ ?_)
    simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_not] at hx
    exact hx
  apply eq_of_forall_dense_eq hD
  rintro x ⟨h1, h2⟩
  exact tendsto_nhds_unique (hlim1 x h1) ((hBH x h2).comp hφ.tendsto_atTop)

end CumulativeDistributionFunction

end convergence_of_types

section max_stability

open Real Filter Topology Set

namespace CumulativeDistributionFunction

private lemma pow_apply_eq_of_eq (G : CumulativeDistributionFunction) {t t' : ℝ} (ht : 0 < t)
    (ht' : 0 < t') (h : t = t') : G.pow ht = G.pow ht' := by
  subst h
  rfl

private lemma pow_pow_eq (G : CumulativeDistributionFunction) {t₁ t₂ : ℝ} (h₁ : 0 < t₁)
    (h₂ : 0 < t₂) : (G.pow h₁).pow h₂ = G.pow (mul_pos h₁ h₂) := by
  ext x
  rw [pow_apply_eq, pow_apply_eq, pow_apply_eq, ← rpow_mul (G.apply_nonneg x)]

private lemma pow_one_eq (G : CumulativeDistributionFunction) : G.pow one_pos = G := by
  ext x
  rw [pow_apply_eq, rpow_one]

/-- An extreme value distribution is max-stable for all real powers. -/
private lemma exists_smul_eq_pow_of_isExtremeValueDistr {G : CumulativeDistributionFunction}
    (G_evd : G.IsExtremeValueDistr) {t : ℝ} (t_pos : 0 < t) :
    ∃ A : AffineIncrEquiv, A • G = G.pow t_pos := by
  obtain ⟨G_nondeg, F, As, hlim⟩ := G_evd
  let m : ℕ → ℕ := fun n ↦ ⌊t * n⌋₊ + 1
  have m_pos : ∀ n, 0 < (m n : ℝ) := fun n ↦ by positivity
  have m_lim : Tendsto m atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ _)
      (tendsto_nat_floor_atTop.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop t_pos))
  have m_div : Tendsto (fun n : ℕ ↦ (m n : ℝ) / n) atTop (𝓝 t) := by
    have h1 := (tendsto_nat_floor_mul_div_atTop (R := ℝ) t_pos.le).comp
      tendsto_natCast_atTop_atTop
    have h2 := h1.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h2
    refine h2.congr (fun n ↦ ?_)
    simp only [Function.comp, m, Nat.cast_add, Nat.cast_one, add_div]
  have Gt_nondeg : ¬ (G.pow t_pos).IsDegenerate := by
    intro hdeg
    apply G_nondeg
    intro x
    rcases hdeg x with h | h
    · left
      rw [pow_apply_eq] at h
      exact ((rpow_eq_zero_iff_of_nonneg (G.apply_nonneg x)).mp h).1
    · right
      rw [pow_apply_eq] at h
      by_contra hne
      have hlt := lt_of_le_of_ne (G.apply_le_one x) hne
      have := rpow_lt_one (G.apply_nonneg x) hlt t_pos
      linarith
  have cont : ∀ x, ContinuousAt (G.pow t_pos) x → ContinuousAt G x := by
    intro x hx
    have heq : (fun y ↦ ((G.pow t_pos) y) ^ t⁻¹) = fun y ↦ G y := by
      funext y
      rw [pow_apply_eq, ← rpow_mul (G.apply_nonneg y), mul_inv_cancel₀ t_pos.ne', rpow_one]
    have h := hx.rpow_const (p := t⁻¹) (Or.inr (inv_nonneg.mpr t_pos.le))
    rw [heq] at h
    exact h
  have hH : ∀ x, ContinuousAt (G.pow t_pos) x →
      Tendsto (fun n ↦ (As n • F).pow (m_pos n) x) atTop (𝓝 ((G.pow t_pos) x)) := by
    intro x hx
    have hGx := hlim x (cont x hx)
    have h2 := hGx.rpow m_div (Or.inr t_pos)
    rw [pow_apply_eq]
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [pow_apply_eq, ← rpow_natCast, ← rpow_mul (apply_nonneg _ _)]
    congr 1
    field_simp
  have hBH : ∀ x, ContinuousAt G x →
      Tendsto (fun n ↦ ((As (m n) * (As n)⁻¹) • (As n • F).pow (m_pos n)) x) atTop
        (𝓝 (G x)) := by
    intro x hx
    refine ((hlim x hx).comp m_lim).congr (fun n ↦ ?_)
    have e : (As (m n) * (As n)⁻¹) • (As n • F).pow (m_pos n) = (As (m n) • F).pow (m_pos n) := by
      rw [smul_pow_eq_pow_smul, ← mul_smul, inv_mul_cancel_right]
    rw [e, pow_apply_eq, rpow_natCast]
    rfl
  obtain ⟨A, hA⟩ := exists_smul_eq_of_tendsto (fun n ↦ (As n • F).pow (m_pos n)) (G.pow t_pos) G
    (fun n ↦ As (m n) * (As n)⁻¹) hH hBH Gt_nondeg G_nondeg
  refine ⟨A⁻¹, ?_⟩
  have := congrArg (fun F ↦ A⁻¹ • F) hA
  simp only [inv_smul_smul] at this
  exact this.symm

/-- The left-continuous quantile function (generalized inverse) of a c.d.f. -/
private noncomputable def lowerQuantile (F : CumulativeDistributionFunction) (p : ℝ) : ℝ :=
  sInf {y | p ≤ F y}

private lemma setOf_le_nonempty (F : CumulativeDistributionFunction) {p : ℝ} (hp : p < 1) :
    {y | p ≤ F y}.Nonempty := by
  obtain ⟨y, hy⟩ := (F.tendsto_atTop.eventually (eventually_gt_nhds hp)).exists
  exact ⟨y, hy.le⟩

private lemma setOf_le_bddBelow (F : CumulativeDistributionFunction) {p : ℝ} (hp : 0 < p) :
    BddBelow {y | p ≤ F y} := by
  obtain ⟨N, hN⟩ := eventually_atBot.mp (F.tendsto_atBot.eventually (eventually_lt_nhds hp))
  refine ⟨N, fun y hy ↦ ?_⟩
  by_contra h
  push Not at h
  have hy' : p ≤ F y := hy
  linarith [hN y h.le]

private lemma isLeast_lowerQuantile (F : CumulativeDistributionFunction) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : IsLeast {y | p ≤ F y} (lowerQuantile F p) := by
  refine ⟨?_, fun y hy ↦ csInf_le (setOf_le_bddBelow F hp0) hy⟩
  by_contra hcon
  have hlt : F (lowerQuantile F p) < p := lt_of_not_ge hcon
  have hev : ∀ᶠ y in 𝓝[≥] (lowerQuantile F p), F y < p :=
    (F.right_continuous _).eventually (gt_mem_nhds hlt)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  obtain ⟨y, hy, hyu⟩ := exists_lt_of_csInf_lt (setOf_le_nonempty F hp1) hu
  have hqy : lowerQuantile F p ≤ y := csInf_le (setOf_le_bddBelow F hp0) hy
  have hy' : p ≤ F y := hy
  have := hsub ⟨hqy, hyu⟩
  simp only [mem_ofPred_eq] at this
  linarith

private lemma lowerQuantile_smul (F : CumulativeDistributionFunction) (A : AffineIncrEquiv)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    lowerQuantile (A • F) p = A (lowerQuantile F p) := by
  obtain ⟨h1, h2⟩ := isLeast_lowerQuantile F hp0 hp1
  refine IsLeast.csInf_eq ⟨?_, fun y hy ↦ ?_⟩
  · show p ≤ (A • F) (A (lowerQuantile F p))
    rw [mulAction_apply_eq_self_apply]
    exact h1
  · have : lowerQuantile F p ≤ A⁻¹ y := h2 (show p ≤ F (A⁻¹ y) from hy)
    calc A (lowerQuantile F p) ≤ A (A⁻¹ y) := A.mono this
      _ = y := EquivLike.right_inv A y

private lemma lowerQuantile_pow (F : CumulativeDistributionFunction) {t : ℝ} (t_pos : 0 < t)
    {p : ℝ} (hp0 : 0 ≤ p) :
    lowerQuantile (F.pow t_pos) p = lowerQuantile F (p ^ t⁻¹) := by
  unfold lowerQuantile
  congr 1
  ext y
  simp only [mem_ofPred_eq, pow_apply_eq]
  exact (rpow_inv_le_iff_of_pos hp0 (F.apply_nonneg y) t_pos).symm

private lemma lowerQuantile_mono (F : CumulativeDistributionFunction) {p p' : ℝ} (hp0 : 0 < p)
    (hp' : p' < 1) (h : p ≤ p') : lowerQuantile F p ≤ lowerQuantile F p' :=
  csInf_le_csInf (setOf_le_bddBelow F hp0) (setOf_le_nonempty F hp')
    (fun _ hy ↦ le_trans h hy)

end CumulativeDistributionFunction

end max_stability

section self_simiarity_of_extreme_value_distributions

open Real

namespace CumulativeDistributionFunction.IsExtremeValueDistr

theorem self_similar {G : CumulativeDistributionFunction}
    (G_evd : G.IsExtremeValueDistr) :
    ∃ (f : Multiplicative ℝ →* AffineIncrEquiv), f ≠ 1 ∧ Measurable f ∧
      (∀ (s : ℝ), f s • G = G.pow (exp_pos s)) := by
  have hex : ∀ s : ℝ, ∃ A : AffineIncrEquiv, A • G = G.pow (exp_pos s) :=
    fun s ↦ exists_smul_eq_pow_of_isExtremeValueDistr G_evd (exp_pos s)
  choose A hA using hex
  have G_nondeg := G_evd.nondegenerate
  have hA0 : A 0 = 1 := by
    apply smul_left_cancel_of_not_isDegenerate G G_nondeg
    rw [hA 0, one_smul, pow_apply_eq_of_eq G (exp_pos 0) one_pos exp_zero, pow_one_eq]
  have hAadd : ∀ s₁ s₂, A (s₁ + s₂) = A s₁ * A s₂ := by
    intro s₁ s₂
    apply smul_left_cancel_of_not_isDegenerate G G_nondeg
    rw [hA (s₁ + s₂), mul_smul, hA s₂, smul_pow_eq_pow_smul, hA s₁, pow_pow_eq]
    exact pow_apply_eq_of_eq G _ _ (exp_add s₁ s₂)
  -- Measurability via monotonicity of `s ↦ A s y` at quantile points `y`.
  obtain ⟨x₁, x₂, hlt, h1, h2, -, -⟩ := G.exists₂_continuousAt' G_nondeg
  have hx1 : G x₁ < 1 := lt_of_le_of_lt (G.mono hlt.le) h2
  have hp₂0 : 0 < (G x₁ + 1) / 2 := by linarith
  have hp₂1 : (G x₁ + 1) / 2 < 1 := by linarith
  have hy₁ : lowerQuantile G (G x₁) ≤ x₁ :=
    (isLeast_lowerQuantile G h1 hx1).2 (show G x₁ ≤ G x₁ from le_rfl)
  have hy₂ : x₁ < lowerQuantile G ((G x₁ + 1) / 2) := by
    by_contra hcon
    push Not at hcon
    have h' : (G x₁ + 1) / 2 ≤ G (lowerQuantile G ((G x₁ + 1) / 2)) :=
      (isLeast_lowerQuantile G hp₂0 hp₂1).1
    linarith [G.mono hcon]
  have hq : ∀ p, 0 < p → p < 1 → ∀ s,
      A s (lowerQuantile G p) = lowerQuantile G (p ^ (exp s)⁻¹) := by
    intro p hp0 hp1 s
    rw [← lowerQuantile_smul G (A s) hp0 hp1, hA s, lowerQuantile_pow G (exp_pos s) hp0.le]
  have hmono : ∀ p, 0 < p → p < 1 → Monotone (fun s ↦ A s (lowerQuantile G p)) := by
    intro p hp0 hp1 s s' hss'
    simp only [hq p hp0 hp1]
    apply lowerQuantile_mono G (rpow_pos_of_pos hp0 _)
      (rpow_lt_one hp0.le hp1 (inv_pos.mpr (exp_pos _)))
    exact rpow_le_rpow_of_exponent_ge hp0 hp1.le (inv_anti₀ (exp_pos s) (exp_le_exp.mpr hss'))
  set y₁ := lowerQuantile G (G x₁)
  set y₂ := lowerQuantile G ((G x₁ + 1) / 2)
  have hm₁ : Measurable (fun s ↦ A s y₁) := (hmono _ h1 hx1).measurable
  have hm₂ : Measurable (fun s ↦ A s y₂) := (hmono _ hp₂0 hp₂1).measurable
  have hne : y₂ - y₁ ≠ 0 := by intro h; linarith
  have hc1 : (fun s ↦ (A s).coefs.1) = fun s ↦ (A s y₂ - A s y₁) / (y₂ - y₁) := by
    funext s
    simp only [AffineIncrEquiv.apply_eq]
    rw [eq_div_iff hne]
    ring
  have hc2 : (fun s ↦ (A s).coefs.2) = fun s ↦ A s y₁ - (A s).coefs.1 * y₁ := by
    funext s
    simp only [AffineIncrEquiv.apply_eq]
    ring
  have hmc1 : Measurable (fun s ↦ (A s).coefs.1) := by
    rw [hc1]
    exact (hm₂.sub hm₁).div_const _
  have hmc2 : Measurable (fun s ↦ (A s).coefs.2) := by
    rw [hc2]
    exact hm₁.sub (hmc1.mul_const _)
  let f : Multiplicative ℝ →* AffineIncrEquiv :=
    { toFun := fun z ↦ A z.toAdd
      map_one' := by
        show A (Multiplicative.toAdd 1) = 1
        rw [toAdd_one]
        exact hA0
      map_mul' := fun z₁ z₂ ↦ by
        show A (Multiplicative.toAdd (z₁ * z₂)) = A z₁.toAdd * A z₂.toAdd
        rw [toAdd_mul]
        exact hAadd _ _ }
  refine ⟨f, ?_, ?_, fun s ↦ hA s⟩
  · intro hf
    apply G_nondeg
    have h2 : A (log 2) = 1 := by
      have := congrArg
        (fun g : Multiplicative ℝ →* AffineIncrEquiv ↦ g (Multiplicative.ofAdd (log 2))) hf
      exact this
    intro x
    have hx := congrArg (fun F : CumulativeDistributionFunction ↦ F x) (hA (log 2))
    simp only [h2, one_smul, pow_apply_eq, exp_log two_pos] at hx
    rw [rpow_two] at hx
    have h' : G x * (G x - 1) = 0 := by rw [mul_sub, mul_one, ← sq]; linarith
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · apply AffineIncrEquiv.measurable_of_measurable_coefs
    · exact hmc1.comp measurable_toAdd
    · exact hmc2.comp measurable_toAdd

open AffineIncrEquiv in
/-- **Fisher-Tippett-Gnedenko theorem**:
Any extreme value distribution is of Gumbel, Fréchet, or Weibull type.
-/
theorem classification {G : CumulativeDistributionFunction}
    (G_evd : G.IsExtremeValueDistr) :
    (∃ (A : AffineIncrEquiv), A • G = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ) , A • G = standardFrechetCDF hξ) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ) , A • G = standardWeibullCDF hξ) := by
  obtain ⟨f, f_nontriv, f_mble, hf⟩ := IsExtremeValueDistr.self_similar G_evd
  cases' homomorphism_from_Real_characterization_of_nontrivial f_nontriv f_mble with h₀ h₁
  · left -- **the Gumbel case**
    obtain ⟨β, β_ne_zero, hβ⟩ := h₀
    have β_pos : 0 < β := by
      by_contra con -- β ≤ 0 is a contradiction with the self-similarity property and nondegeneracy
      simp only [not_lt] at con
      have β_neg : β < 0 := lt_of_le_of_ne con β_ne_zero
      obtain ⟨x, hx⟩ : ∃ x, G x ≠ 0 ∧ G x ≠ 1 := by simpa [IsDegenerate] using G_evd.nondegenerate
      have Gx_eq : (G x) ^ 2 = G x := by
        have Gx_sq : (homOfIndex₀ β (Real.log 2) • G) x = (G x) ^ 2 := by
          have selfsim := hβ ▸ hf
          rw [← CumulativeDistributionFunction.npow_apply_eq G zero_lt_two x, selfsim (log 2)]
          congr
          simpa only [Nat.cast_ofNat] using exp_log zero_lt_two
        have obs : (homOfIndex₀ β (Real.log 2))⁻¹ x > x := by
          simp [show β * Real.log 2 < 0 from mul_neg_of_neg_of_pos β_neg (log_pos one_lt_two)]
        apply le_antisymm
        · exact pow_le_of_le_one (G.apply_nonneg x) (G.apply_le_one x) two_ne_zero
        · simpa [← Gx_sq] using G.mono obs.le
      have Gx_eq_01 : G x = 0 ∨ G x = 1 := by
        rw [← sub_eq_zero (b := (1 : ℝ)), ← mul_eq_zero]
        linarith
      cases' Gx_eq_01 with hGx₀ hGx₁
      · exact hx.1 hGx₀
      · exact hx.2 hGx₁
    have key := gumbel_type_of_selfSimilar_index_zero G_evd.nondegenerate β_pos (hβ ▸ hf)
    set A := (mkOfCoefs (Right.inv_pos.mpr β_pos) (-(log (- (log (G 0))))))
      with def_A
    refine ⟨A, ?_⟩
    simpa using congr_arg (fun F ↦ A • F) key
  · right -- Fréchet or Weibull case
    obtain ⟨α, c, α_ne_zero, h⟩ := h₁
    by_cases sign_α : 0 < α
    · left -- **the Fréchet case**
      have key := frechet_type_of_selfSimilar_index_pos G_evd.nondegenerate sign_α (h ▸ hf)
      set A := (mkOfCoefs
          (frechet_scale_pos_of_selfSimilar_index_pos' G_evd.nondegenerate sign_α (h ▸ hf)) c)
        with def_A
      refine ⟨A⁻¹, α⁻¹, by simp [sign_α], ?_⟩
      simpa [← mul_smul] using congr_arg (fun F ↦ A⁻¹ • F) key
    · right -- **the Weibull case**
      have α_neg : α < 0 := lt_of_le_of_ne (not_lt.mp sign_α) α_ne_zero
      have key := weibull_type_of_selfSimilar_index_neg G_evd.nondegenerate α_neg (h ▸ hf)
      set A := (mkOfCoefs
          (weibull_scale_pos_of_selfSimilar_index_neg' G_evd.nondegenerate α_neg (h ▸ hf)) c)
        with def_A
      refine ⟨A⁻¹, -α⁻¹, by simp [α_neg], ?_⟩
      simpa [← mul_smul] using congr_arg (fun F ↦ A⁻¹ • F) key

end CumulativeDistributionFunction.IsExtremeValueDistr

end self_simiarity_of_extreme_value_distributions
