/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Okko Heiniö ...
Modified by Federico Carrone, 2026, from kkytola/ExtremeValueProject (commit f7c9a8ce260d):
ported to Lean/Mathlib v4.35.0 and renamed `ExtremeValueProject` to `ExtremeValueTheory`.
-/
import Mathlib
import ExtremeValueTheory.CumulativeDistributionFunction
import ExtremeValueTheory.AffineTransformation

import ExtremeValueTheory.WeakConvergenceCDF

section preliminaries_for_type_of_cdf

open Topology Filter

open scoped Topology


/-- Construct an orientation preserving affine isomorphism `x ↦ a * x + b` of `ℝ` from
coefficients `a > 0` and `b ∈ ℝ`. -/
noncomputable def orientationPreservingAffineEquiv.mkOfCoefs {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    orientationPreservingAffineEquiv where
  val := AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b
  property := by
    change (AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b).IsOrientationPreserving
    rw [AffineEquiv.IsOrientationPreserving]
    convert a_pos
    simp

lemma orientationPreservingAffineEquiv.mkOfCoefs_apply {a : ℝ} (a_pos : 0 < a) (b : ℝ) (x : ℝ) :
    (mkOfCoefs a_pos b).val x = a * x + b :=
  rfl

lemma orientationPreservingAffineEquiv.mkOfCoefs_val {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    (mkOfCoefs a_pos b).val = AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b :=
  rfl

namespace CumulativeDistributionFunction

/-- The continuity points of a c.d.f. form a dense set. -/
private lemma dense_continuousAt_aux (F : CumulativeDistributionFunction) :
    Dense {x | ContinuousAt F x} := by
  simpa [compl] using Set.Countable.dense_compl (𝕜 := ℝ) (Monotone.countable_not_continuousAt F.mono')

lemma exists₂_continuousAt_of_not_isDegenerate
    (F : CumulativeDistributionFunction) (hF : ¬ F.IsDegenerate) :
    ∃ x₁ x₂, (x₁ < x₂) ∧ (0 < F x₁) ∧ (F x₂ < 1) ∧ (ContinuousAt F x₁) ∧ (ContinuousAt F x₂) := by
  simp only [isDegenerate_def, not_forall, not_or] at hF
  obtain ⟨x₀, h0, h1⟩ := hF
  have pos : 0 < F x₀ := lt_of_le_of_ne (F.apply_nonneg x₀) (Ne.symm h0)
  have lt1 : F x₀ < 1 := lt_of_le_of_ne (F.apply_le_one x₀) h1
  have ev : ∀ᶠ x in 𝓝[≥] x₀, F x < 1 := (F.right_continuous x₀).eventually (eventually_lt_nhds lt1)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp ev
  obtain ⟨x₁, hx₁c, hx₁⟩ := F.dense_continuousAt_aux.exists_between hu
  obtain ⟨x₂, hx₂c, hx₂⟩ := F.dense_continuousAt_aux.exists_between hx₁.2
  refine ⟨x₁, x₂, hx₂.1, pos.trans_le (F.mono hx₁.1.le), ?_, hx₁c, hx₂c⟩
  exact hsub ⟨(hx₁.1.trans hx₂.1).le, hx₂.2⟩

/-- The "quantile" `sInf {x | t ≤ F x}` transforms equivariantly under affine maps. -/
lemma sInf_setOf_le_smul_apply (F : CumulativeDistributionFunction) (A : AffineIncrEquiv)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    sInf {x | t ≤ (A • F) x} = A (sInf {x | t ≤ F x}) := by
  have hset : {x | t ≤ (A • F) x} = A '' {x | t ≤ F x} := by
    ext y
    constructor
    · intro hy
      refine ⟨A⁻¹ y, ?_, ?_⟩
      · simpa only [Set.mem_setOf_eq, mulAction_apply_eq] using hy
      · exact EquivLike.apply_inv_apply A y
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_setOf_eq, mulAction_apply_eq_self_apply] using hx
  have ne : {x | t ≤ F x}.Nonempty := by
    obtain ⟨x, hx⟩ := (F.tendsto_atTop.eventually (eventually_gt_nhds ht1)).exists
    exact ⟨x, hx.le⟩
  have bdd : BddBelow {x | t ≤ F x} := by
    obtain ⟨a, ha⟩ := eventually_atBot.mp (F.tendsto_atBot.eventually (eventually_lt_nhds ht0))
    refine ⟨a, fun x hx ↦ ?_⟩
    by_contra! con
    exact absurd (ha x con.le) (not_lt.mpr hx)
  rw [hset]
  exact (Monotone.map_csInf_of_continuousAt
    (A.val.continuous_of_finiteDimensional.continuousAt) A.mono ne bdd).symm

lemma unique_orientationPreservingAffineEquiv_smul_eq_not_isDegenerate
    {F G : CumulativeDistributionFunction} {A₁ A₂ : AffineIncrEquiv}
    (hG : ¬ G.IsDegenerate) (h₁ : A₁ • F = G) (h₂ : A₂ • F = G) :
    A₁ = A₂ := by
  have hF : ¬ F.IsDegenerate := by
    rwa [← h₁, affine_isDegenerate_iff] at hG
  obtain ⟨x₁, x₂, x₁_lt, Fx₁_pos, Fx₂_lt, -, -⟩ := F.exists₂_continuousAt_of_not_isDegenerate hF
  have Fx₁_lt : F x₁ < 1 := (F.mono x₁_lt.le).trans_lt Fx₂_lt
  set t₂ := (F x₂ + 1) / 2 with ht₂
  have t₂_pos : 0 < t₂ := by linarith [F.apply_nonneg x₂]
  have t₂_lt : t₂ < 1 := by linarith
  have agree {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
      A₁ (sInf {x | t ≤ F x}) = A₂ (sInf {x | t ≤ F x}) := by
    rw [← sInf_setOf_le_smul_apply F A₁ ht0 ht1, ← sInf_setOf_le_smul_apply F A₂ ht0 ht1, h₁, h₂]
  set p := sInf {x | F x₁ ≤ F x} with hp
  set q := sInf {x | t₂ ≤ F x} with hq
  have p_le : p ≤ x₁ := by
    apply csInf_le _ (show x₁ ∈ {x | F x₁ ≤ F x} from Set.mem_setOf.mpr le_rfl)
    obtain ⟨a, ha⟩ := eventually_atBot.mp (F.tendsto_atBot.eventually (eventually_lt_nhds Fx₁_pos))
    refine ⟨a, fun x hx ↦ ?_⟩
    by_contra! con
    exact absurd (ha x con.le) (not_lt.mpr hx)
  have le_q : x₂ ≤ q := by
    apply le_csInf
    · obtain ⟨x, hx⟩ := (F.tendsto_atTop.eventually (eventually_gt_nhds t₂_lt)).exists
      exact ⟨x, hx.le⟩
    · intro x hx
      by_contra! con
      have := F.mono con.le
      simp only [Set.mem_setOf_eq] at hx
      linarith
  have hpq : p ≠ q := by intro h; linarith
  have e_p := agree Fx₁_pos Fx₁_lt
  have e_q := agree t₂_pos t₂_lt
  rw [← hp] at e_p
  rw [← hq] at e_q
  apply AffineIncrEquiv.ext_of_coefs
  have e1 : A₁.coefs.1 = A₂.coefs.1 := by
    rw [A₁.coefs_fst_eq_div_sub hpq, A₂.coefs_fst_eq_div_sub hpq, e_p, e_q]
  have e2 : A₁.coefs.2 = A₂.coefs.2 := by
    rw [A₁.coefs_snd_eq_apply_sub_mul p, A₂.coefs_snd_eq_apply_sub_mul p, e_p, e1]
  exact Prod.ext e1 e2

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'(x) = 0` for all `x < β`. -/
lemma apply_eq_zero_of_tendsto_of_lt
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x)))
    {x : ℝ} (x_lt : x < β) :
    G' x = 0 := by
  have G'x_small (ε : ℝ) (ε_pos : ε > 0) : G' x < ε := by
    -- Choose `x'` s.t. `x < x' < β` and `G'` is continuous at `x'`
    obtain ⟨x', x'_cont, x'_gt, x'_lt⟩ :=
      G'.dense_continuousAt_aux.exists_between x_lt
    -- Choose `z` s.t. `G(z) < ε/2` and `G` is continuous at `z`
    set ε' := ε/2 with hε'
    obtain ⟨z', hz'⟩ := (G.tendsto_atBot.eventually
      (eventually_lt_nhds (show (0:ℝ) < ε' by linarith))).exists
    obtain ⟨z, z_cont, -, z_lt⟩ :=
      G.dense_continuousAt_aux.exists_between (show z' - 1 < z' by linarith)
    have Gz_lt : G z < ε' := (G.mono z_lt.le).trans_lt hz'
    -- `Aₙ(z) → β`
    have : Tendsto (fun n ↦ a n * z) atTop (𝓝 (0 * z)) := a_lim.mul_const z
    simp only [zero_mul] at this
    have A_lim : Tendsto (fun n ↦ a n * z + b n) atTop (𝓝 (0 + β)) := this.add b_lim
    simp only [zero_add] at A_lim
    have Anz_ev_gt : ∀ᶠ n in atTop, x' < a n * z + b n :=
      A_lim.eventually (eventually_gt_nhds x'_lt)
    have Fnz_ev_lt : ∀ᶠ n in atTop, F n z < ε' :=
      (F_lim z z_cont).eventually (eventually_lt_nhds Gz_lt)
    set F' : ℕ → CumulativeDistributionFunction :=
      fun n ↦ (mkOfCoefs (a_pos n) (b n)) • (F n) with hF'
    by_contra con
    have F'nx'_ev_gt : ∀ᶠ n in atTop, ε' < F' n x' :=
      (F_lim' x' x'_cont).eventually
        (eventually_gt_nhds (show ε' < G' x' by linarith [G'.mono x'_gt.le]))
    obtain ⟨n, ⟨hn₁, hn₂⟩, hn₃⟩ := ((Fnz_ev_lt.and Anz_ev_gt).and F'nx'_ev_gt).exists
    have := calc
      F' n x' ≤ F' n (a n * z + b n) := (F' n).mono' hn₂.le
      _ = (F n) z := by
        rw [← mulAction_apply_eq_self_apply (F n) (mkOfCoefs (a_pos n) (b n))]
        rfl
    linarith
  have : G' x ≤ 0 := by
    by_contra h
    linarith [G'x_small (G' x / 2) (by linarith)]
  linarith [apply_nonneg G' x]

open AffineIncrEquiv Set Countable Monotone in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'(x) = 1` for all `x > β`. -/
lemma apply_eq_one_of_tendsto_of_gt
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x)))
    {x : ℝ} (x_gt : β < x) :
    G' x = 1 := by
  have G'x_large (ε : ℝ) (ε_pos : ε > 0) : G' x > 1 - ε := by

    have dense_cont_pts (H : CumulativeDistributionFunction) : Dense {x | ContinuousAt H x} := by
      simpa [compl] using dense_compl (𝕜 := ℝ) (countable_not_continuousAt H.mono')

    -- Choose `x'` s.t. `β < x' < x` and `G'` is continuous at `x'`
    obtain ⟨x', ⟨x'_gt, x'_lt⟩, x'_cont⟩ :=
      (dense_cont_pts G').inter_open_nonempty (Ioo β x) isOpen_Ioo (nonempty_Ioo.mpr x_gt)
    simp only [mem_setOf_eq] at x'_cont

    -- Choose `z'` s.t. `G(z') > 1 - ε'` where `ε' := ε/2`
    set ε' := ε/2 with hε'
    have Gz'_ev_gt : ∀ᶠ z' in atTop, 1 - ε' < G z' := by
      filter_upwards
        [G.tendsto_atTop (show Ioi (1-ε') ∈ 𝓝 1 from Ioi_mem_nhds (by linarith))]
        with z' hz' using hz'
    obtain ⟨z', hz'⟩ := Gz'_ev_gt.exists

    -- Choose `z` s.t. `G(z) > 1 - ε'` and `G` is continuous at `z`
    obtain ⟨z, z_gt, z_cont⟩ :=
      (dense_cont_pts G).inter_open_nonempty {z | z' < z} isOpen_Ioi nonempty_Ioi
    simp only [mem_setOf_eq] at z_gt z_cont
    have Gz_gt : 1 - ε' < G z := hz'.trans_le <| G.mono (by linarith)

    -- `Aₙ(z) → β`
    have : Tendsto (λ n ↦ a n * z) atTop (𝓝 (0 * z)) := a_lim.mul_const z
    simp only [zero_mul] at this
    have A_lim : Tendsto (λ n ↦ a n * z + b n) atTop (𝓝 (0 + β)) := this.add b_lim
    simp only [zero_add] at A_lim

    -- `Aₙ(z) < x'` for large `n`
    have Anz_ev_lt : ∀ᶠ n in atTop, a n * z + b n < x' := by
      filter_upwards [A_lim (Iio_mem_nhds x'_gt)] with n hn using hn

    -- `1 - ε' < Fₙ(z)` for large `n`
    have Fnz_ev_gt : ∀ᶠ n in atTop, 1 - ε' < F n z := by
      filter_upwards [F_lim z z_cont (Ioi_mem_nhds Gz_gt)] with n hn using hn

    -- Shorthand `Fₙ' = Aₙ.Fₙ`
    set F' : ℕ → CumulativeDistributionFunction :=
      fun n ↦ (mkOfCoefs (a_pos n) (b n)) • (F n) with hF'

    -- Assume the opposite to get `Fₙ'(x') < 1 - ε'` for large `n`
    by_contra con
    have F'nx'_ev_gt : ∀ᶠ n in atTop, F' n x' < 1 - ε' := by
      filter_upwards
        [F_lim' x' x'_cont (Iio_mem_nhds (show G' x' < 1 - ε' by linarith [G'.mono x'_lt.le]))]
        with n hn using hn

    obtain ⟨n, ⟨hn₁, hn₂⟩, hn₃⟩ := ((Fnz_ev_gt.and Anz_ev_lt).and F'nx'_ev_gt).exists

    -- Contradiction `1 - ε' < Fₙ(z) ≤ Fₙ'(x') < 1 - ε'`
    have := calc
      (F n) z = F' n (a n * z + b n) := by
        rw [← mulAction_apply_eq_self_apply (F n) (mkOfCoefs (a_pos n) (b n))]
        rfl
      _ ≤ F' n x' := (F' n).mono' (by linarith)
    linarith

  have : G' x ≥ 1 := by
    by_contra h
    linarith [G'x_large ((1 - G' x) / 2) (by linarith)]
  linarith [apply_le_one G' x]

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'` is degenerate (a delta mass at `β`). -/
lemma isDegenerate_of_tendsto_shrinking
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x))) :
    G'.IsDegenerate := by
  rw [isDegenerate_iff]
  use β
  suffices (∀ x < β, G' x = 0) ∧ (∀ x > β, G' x = 1) by
    funext x
    by_cases x_lt : x < β
    · have obs : ¬ x ∈ Set.Ici β := by simpa using x_lt
      simp [obs, this.1 _ x_lt]
    · have obs : x ∈ Set.Ici β := by simpa using x_lt
      by_cases x_eq : x = β
      · simp only [obs, Set.indicator_of_mem]
        have key := G'.right_continuous
        have key' : ContinuousWithinAt G' (Set.Ioi β) β := continuousWithinAt_Ioi_iff_Ici.mpr (key β)
        have aux : ∀ᶠ x in (𝓝[>] β), G' x = 1 := by
          filter_upwards [self_mem_nhdsWithin] with x hx using this.2 _ hx
        have wow := Tendsto.congr' aux key'
        rw [tendsto_const_nhds_iff] at wow
        rw [x_eq, wow]
      have x_gt : β < x := lt_of_le_of_ne (le_of_not_gt x_lt) ((Ne.eq_def _ _).symm ▸ x_eq).symm
      simp [obs, this.2 _ x_gt]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact apply_eq_zero_of_tendsto_of_lt a_pos a_lim b_lim F_lim F_lim' hx
  · intro x hx
    exact apply_eq_one_of_tendsto_of_gt a_pos a_lim b_lim F_lim F_lim' hx

open orientationPreservingAffineEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` where `G` is nondegenerate and if `Aₙ`
is a sequence of oriented affine isomorphisms with scaling coefficients `aₙ → +∞`,
then `Aₙ • Fₙ` cannot converge to any c.d.f. -/
lemma not_tendsto_cdf_of_expanding_of_tendsto_not_isDegenerate
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (hG : ¬ G.IsDegenerate) {A : ℕ → AffineIncrEquiv}
    (a_lim : Tendsto (fun n ↦ (A n).val.toAffineMap.coefs_of_field.1) atTop atTop) :
    ¬ ∀ x, ContinuousAt G' x → Tendsto (fun n ↦ ((A n) • (F n)) x) atTop (𝓝 (G' x)) := by
  intro nottrue
  have ⟨x1,x2,x1_lt_x2,Gx1_pos,Gx2_bound,x1_cont,x2_cont⟩:=
    CumulativeDistributionFunction.exists₂_continuousAt_of_not_isDegenerate _ hG
  have right_tendsto {z : ℝ} (z_spec_cont : ContinuousAt G' z) {s : ℕ → ℕ}
      (s_atTop : Tendsto s atTop atTop) :
      Tendsto (fun k ↦ (A (s k) • F (s k)) z) atTop (𝓝 (G' z))  :=
    (nottrue z z_spec_cont).comp s_atTop
  have left_tendsto {x1 : ℝ} (x1_cont : ContinuousAt G x1) {s : ℕ → ℕ}
      (s_atTop : Tendsto s atTop atTop) :
      Tendsto (fun k ↦ F (s k) x1) atTop (𝓝 (G x1)) :=
    (F_lim _ x1_cont).comp s_atTop
  -- the names `lt` and `min` have lost their meaning.
  have not_bounded_after' {B : ℕ → ℝ} {lt : ℝ → ℝ → Prop} {min : ℝ → ℝ → ℝ}
      (not_bounded : ∀z, ∃ x, lt (B x) z )
      (min_spec : ∀ ⦃a b c⦄, lt a (min b c) → a ≠ b ∧ lt a c)
      (z) (t) : ∃ x ≥ t, lt (B x) z := by
    induction t generalizing z with
    | zero =>
      simp only [ge_iff_le, zero_le, true_and]
      exact not_bounded z
    | succ t prev =>
      -- `prev (min (B t) z)` ensures that `y ≠ t`, using `B y < B t`
      have ⟨y, y_gt_t, y_spec⟩ := prev (min (B t) z)
      apply min_spec at y_spec
      have yyt : t ≠ y := by
        intro con
        exact (con ▸  y_spec.left) rfl
      refine ⟨y, Nat.lt_iff_add_one_le.mp (Nat.lt_of_le_of_ne y_gt_t yyt), y_spec.right⟩
  have ⟨below,claim_below⟩ : ∃ below, ∀ n, A n x1 > below := by
    by_contra! not_bounded
    have not_bounded_after := not_bounded_after' not_bounded
      (lt := (· ≤ ·)) (min := (fun a b ↦ min (a - 1) b))
      (by intro a b c abc ; constructor <;> linarith [le_inf_iff.mp abc] )
    obtain ⟨z, _, _, z_spec_lt, _, z_spec_cont, _⟩ := G'.forall_pos_exists_lt_gt_continuousAt Gx1_pos
    have ⟨(s : ℕ → ℕ), (s_atTop : Tendsto s atTop atTop), (s_spec : ∀ (n : ℕ), A (s n) x1 ≤ z)⟩
      := subseq_forall_of_frequently tendsto_id (frequently_atTop.mpr (not_bounded_after z))
    have ineq (k) : F (s k) x1 ≤ (A (s k) • F (s k)) z := by
      rw [←mulAction_apply_eq_self_apply (F (s k)) (A (s k)) x1]
      set qf := A (s k) • F (s k)
      exact (qf.mono) (s_spec k)
    exact (tendsto_le_of_eventuallyLE (left_tendsto x1_cont s_atTop)
      (right_tendsto z_spec_cont s_atTop) (Eventually.of_forall ineq)).not_gt z_spec_lt
  have ⟨above,claim_above⟩ : ∃ above, ∀ n, A n x2 < above := by
    by_contra not_bounded
    simp only [not_exists, not_forall, not_lt] at not_bounded
    have not_bounded_after := not_bounded_after' not_bounded
      (lt := (· ≥ ·)) (min := (fun a b ↦ max (a + 1) b))
      (by intro a b c abc ; constructor <;> linarith [sup_le_iff.mp abc])
    have ⟨z,z_spec_cont,z_spec_lt⟩ : ∃z, ContinuousAt G' z ∧ G' z > G x2 := by
      have Gx2_pos' : 0 < 1 - (G x2) := by linarith [Gx1_pos, G.mono x1_lt_x2.le]
      have ⟨_,w,_,_,w_lt,_,w_cont⟩:= G'.forall_pos_exists_lt_gt_continuousAt Gx2_pos'
      simp only [sub_sub_cancel] at w_lt
      use w
    have ⟨(s : ℕ → ℕ), (s_atTop : Tendsto s atTop atTop), (s_spec : ∀ (n : ℕ), A (s n) x2 ≥ z)⟩
      := subseq_forall_of_frequently tendsto_id (frequently_atTop.mpr (not_bounded_after z))
    have ineq (k) : F (s k) x2 ≥ (A (s k) • F (s k)) z := by
      rw [←mulAction_apply_eq_self_apply (F (s k)) (A (s k)) x2]
      exact (A (s k) • F (s k)).mono (s_spec k)
    exact (tendsto_le_of_eventuallyLE (right_tendsto z_spec_cont s_atTop)
      (left_tendsto x2_cont s_atTop) (Eventually.of_forall ineq)).not_gt z_spec_lt
  set a := fun n ↦ (A n).val.toAffineMap.coefs_of_field.1
  have ⟨an_above, an_claim_above⟩ : ∃ a_above, ∀ n, a n < a_above := by
    use (above - below) / (x2 - x1)
    intro n
    have x2x1_positive : 0 < x2 - x1 := by linarith
    have an_value (n) : a n = (A n x2 - A n x1) / (x2 - x1) := by
      field_simp
      simp only [AffineIncrEquiv.apply_eq, a, AffineIncrEquiv.coefs]
      ring
    have aux : ((A n) x2 - (A n) x1) < (above - below) := by
      linarith only [claim_below n, claim_above n]
    simpa [an_value n] using (div_lt_div_iff_of_pos_right x2x1_positive).mpr aux
  clear * - a_lim an_claim_above
  have impossible : ∀ᶠ n in atTop, a n ∈ Set.Ioi an_above := a_lim (Ioi_mem_atTop an_above)
  obtain ⟨m, (hm : an_above < a m)⟩ := impossible.exists
  apply lt_irrefl _ <| (an_claim_above m).trans hm


end CumulativeDistributionFunction

end preliminaries_for_type_of_cdf


section type_of_cdf

end type_of_cdf
