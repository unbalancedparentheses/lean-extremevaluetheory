/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.GEVDomain
import Mathlib.Analysis.Calculus.LHopital

/-!
# The unified von Mises condition

The second-order von Mises condition `(1 - F) F'' / (F')² → -γ - 1`, that is, `((1 - F) / F')' → γ`,
places `F` in `MDA(H_γ)` for every `γ` ([dHF, Theorem 1.1.8], as cited in
`docs/HIRATA_COMPARISON.md`; the book was not available to check it).

The two theorems split on the endpoint, and each assumes the sign of `γ` that goes with it. The other
signs should be impossible: with an infinite endpoint, `f = (1 - F) / F'` is positive with derivative
tending to `γ`, so `γ < 0` cannot occur; with a finite endpoint and `F → 1`, `γ > 0` cannot occur. That
argument is not mechanized here: the sign is a hypothesis `hγ`, which is the one way these statements
are narrower than the book's single statement.

## Main results

* `isInMDAGEV_of_vonMises`: right endpoint infinite, `γ ≥ 0`.
* `isInMDAGEV_of_vonMises_nhdsLT`: finite right endpoint, `γ ≤ 0`.

The first-order conditions, which need less, are `isInMDAFrechet_of_vonMises` and
`isInMDAWeibull_of_vonMises`. For `γ ≠ 0`, the proofs here show that the second-order condition
implies them.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006) [dHF].
-/

open Filter Topology Set Real

namespace CumulativeDistributionFunction

variable {F : CumulativeDistributionFunction}

/-- The derivative of the auxiliary function `(1 - F) / F'`. -/
private lemma hasDerivAt_auxiliary {F₁ F₂ : ℝ → ℝ} {t : ℝ} (h1 : HasDerivAt F (F₁ t) t)
    (h2 : HasDerivAt F₁ (F₂ t) t) (hpos : 0 < F₁ t) :
    HasDerivAt (fun s ↦ (1 - F s) / F₁ s) (-1 - (1 - F t) * F₂ t / F₁ t ^ 2) t := by
  refine ((h1.const_sub 1).div h2 hpos.ne').congr_deriv ?_
  field_simp

/-- **The unified von Mises condition, infinite right endpoint** ([dHF, Theorem 1.1.8]): if `F` is
twice differentiable on `(z, ∞)` with `F' > 0`, and `(1 - F) F'' / (F')² → -γ - 1` with `γ ≥ 0`, then
`F ∈ MDA(H_γ)`. -/
theorem isInMDAGEV_of_vonMises (F : CumulativeDistributionFunction) {z γ : ℝ} (hγ : 0 ≤ γ)
    {F₁ F₂ : ℝ → ℝ} (h1 : ∀ x > z, HasDerivAt F (F₁ x) x)
    (h2 : ∀ x > z, HasDerivAt F₁ (F₂ x) x) (hpos : ∀ x > z, 0 < F₁ x)
    (hvm : Tendsto (fun t ↦ (1 - F t) * F₂ t / F₁ t ^ 2) atTop (𝓝 (-γ - 1))) :
    F.IsInMDAGEV γ := by
  rcases hγ.eq_or_lt with rfl | hγ
  · refine IsInMDAGumbel.isInMDAGEV (F.isInMDAGumbel_of_vonMises h1 h2 hpos ?_)
    simpa using hvm
  -- `F < 1`
  have hstrict : StrictMonoOn F (Ioi z) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi z)
      (fun x hx ↦ (h1 x hx).continuousAt.continuousWithinAt) fun x hx ↦ ?_
    rw [interior_Ioi] at hx
    rw [(h1 x hx).deriv]
    exact hpos x hx
  have hF : ∀ x > z, F x < 1 := fun x hx ↦
    (hstrict hx (show z < x + 1 by linarith) (by linarith)).trans_le (F.apply_le_one _)
  set f : ℝ → ℝ := fun t ↦ (1 - F t) / F₁ t with hf
  set fd : ℝ → ℝ := fun t ↦ -1 - (1 - F t) * F₂ t / F₁ t ^ 2 with hfd_def
  have hderiv : ∀ t > z, HasDerivAt f (fd t) t := fun t ht ↦
    hasDerivAt_auxiliary (h1 t ht) (h2 t ht) (hpos t ht)
  have hfd : Tendsto fd atTop (𝓝 γ) := by
    have := hvm.const_sub (-1)
    simpa [hfd_def, sub_eq_add_neg] using this
  -- `f t / t → γ`
  have hratio : Tendsto (fun t ↦ f t / t) atTop (𝓝 γ) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hfd (ε / 2) hε2)
    set T := max (max T₀ z + 1) 1 with hT_def
    have hTz : z < T := by
      have h1' : z ≤ max T₀ z := le_max_right _ _
      have h2' : max T₀ z + 1 ≤ T := le_max_left _ _
      linarith
    have hTT₀ : T₀ ≤ T := by
      have h1' : T₀ ≤ max T₀ z := le_max_left _ _
      have h2' : max T₀ z + 1 ≤ T := le_max_left _ _
      linarith
    have hT0 : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
    set h : ℝ → ℝ := fun t ↦ f t - γ * t with hh
    have hbound : ∀ t ≥ T, ‖h t - h T‖ ≤ ε / 2 * ‖t - T‖ := by
      intro t ht
      refine (convex_Ici T).norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun s ↦ fd s - γ)
        (fun s hs ↦ ?_) (fun s hs ↦ ?_) (mem_Ici.2 le_rfl) (mem_Ici.2 ht)
      · have hs' : z < s := hTz.trans_le hs
        have := (hderiv s hs').fun_sub ((hasDerivAt_id' s).const_mul γ)
        simpa [hh] using this.hasDerivWithinAt
      · have := hT₀ s (hTT₀.trans hs)
        rw [Real.dist_eq] at this
        exact this.le
    filter_upwards [eventually_ge_atTop T, eventually_gt_atTop (|h T| / (ε / 2))] with t ht ht2
    have ht0 : 0 < t := hT0.trans_le ht
    have hb := hbound t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht)] at hb
    have h3 : |h t| ≤ |h T| + ε / 2 * (t - T) := by
      have := abs_sub_abs_le_abs_sub (h t) (h T)
      linarith
    have h4 : |h T| < t * (ε / 2) := by rwa [div_lt_iff₀ hε2] at ht2
    rw [Real.dist_eq, show f t / t - γ = h t / t by simp only [hh]; field_simp, abs_div,
      abs_of_pos ht0, div_lt_iff₀ ht0]
    nlinarith
  -- the first-order condition follows
  have hα : 0 < 1 / γ := one_div_pos.2 hγ
  have hvm1 : Tendsto (fun x ↦ x * F₁ x / (1 - F x)) atTop (𝓝 (1 / γ)) := by
    have := hratio.inv₀ hγ.ne'
    rw [← one_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop z, eventually_gt_atTop 0] with x hx hx0
    have h3 := hpos x hx
    have h4 : 1 - F x ≠ 0 := by linarith [hF x hx]
    simp only [hf]
    field_simp
  simpa using (F.isInMDAFrechet_of_vonMises hα h1 hvm1).isInMDAGEV

/-- **The unified von Mises condition, finite right endpoint** ([dHF, Theorem 1.1.8]): if `F` is twice
differentiable on `(z, x_F)` with `F' > 0`, `F (t) → 1` as `t ↑ x_F`, and
`(1 - F) F'' / (F')² → -γ - 1` as `t ↑ x_F` with `γ ≤ 0`, then `F ∈ MDA(H_γ)`.
`Minimality/ClassicalVonMises.lean` shows that the condition `F → 1` cannot be dropped. -/
theorem isInMDAGEV_of_vonMises_nhdsLT (F : CumulativeDistributionFunction) {z xF γ : ℝ}
    (hz : z < xF) (hγ : γ ≤ 0) {F₁ F₂ : ℝ → ℝ} (h1 : ∀ x ∈ Ioo z xF, HasDerivAt F (F₁ x) x)
    (h2 : ∀ x ∈ Ioo z xF, HasDerivAt F₁ (F₂ x) x) (hpos : ∀ x ∈ Ioo z xF, 0 < F₁ x)
    (hF1 : Tendsto F (𝓝[<] xF) (𝓝 1))
    (hvm : Tendsto (fun t ↦ (1 - F t) * F₂ t / F₁ t ^ 2) (𝓝[<] xF) (𝓝 (-γ - 1))) :
    F.IsInMDAGEV γ := by
  rcases hγ.eq_or_lt with rfl | hγ
  · refine IsInMDAGumbel.isInMDAGEV (F.isInMDAGumbel_of_vonMises_nhdsLT hz h1 h2 hpos hF1 ?_)
    simpa using hvm
  have hstrict : StrictMonoOn F (Ioo z xF) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo z xF)
      (fun x hx ↦ (h1 x hx).continuousAt.continuousWithinAt) fun x hx ↦ ?_
    rw [interior_Ioo] at hx
    rw [(h1 x hx).deriv]
    exact hpos x hx
  have hF : ∀ x ∈ Ioo z xF, F x < 1 := fun x hx ↦
    (hstrict hx ⟨hx.1.trans (lt_add_of_pos_right _ (half_pos (sub_pos.2 hx.2))), by
      linarith [hx.2]⟩ (lt_add_of_pos_right _ (half_pos (sub_pos.2 hx.2)))).trans_le
      (F.apply_le_one _)
  set f : ℝ → ℝ := fun t ↦ (1 - F t) / F₁ t with hf
  set fd : ℝ → ℝ := fun t ↦ -1 - (1 - F t) * F₂ t / F₁ t ^ 2 with hfd_def
  have hderiv : ∀ t ∈ Ioo z xF, HasDerivAt f (fd t) t := fun t ht ↦
    hasDerivAt_auxiliary (h1 t ht) (h2 t ht) (hpos t ht)
  have hfpos : ∀ t ∈ Ioo z xF, 0 < f t := fun t ht ↦
    div_pos (by linarith [hF t ht]) (hpos t ht)
  have hfd : Tendsto fd (𝓝[<] xF) (𝓝 γ) := by
    have := hvm.const_sub (-1)
    simpa [hfd_def, sub_eq_add_neg] using this
  -- near `x_F`, `f` is antitone
  have hneg : ∀ᶠ t in 𝓝[<] xF, fd t < 0 := hfd.eventually (gt_mem_nhds hγ)
  obtain ⟨T, hT, hTneg⟩ := (nhdsLT_basis xF).eventually_iff.1
    (hneg.and (Ioo_mem_nhdsLT hz))
  have hT' : z < T ∨ T ≤ z := lt_or_ge z T
  set S := max T z with hS
  have hSz : z ≤ S := le_max_right _ _
  have hSxF : S < xF := max_lt hT hz
  have hSIoo : ∀ t ∈ Ioo S xF, t ∈ Ioo z xF ∧ fd t < 0 := fun t ht ↦
    ⟨⟨hSz.trans_lt ht.1, ht.2⟩, (hTneg ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩).1⟩
  have hanti : AntitoneOn f (Ioo S xF) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo S xF)
      (fun t ht ↦ (hderiv t (hSIoo t ht).1).continuousAt.continuousWithinAt)
      (fun t ht ↦ ?_) fun t ht ↦ ?_
    · rw [interior_Ioo] at ht
      exact (hderiv t (hSIoo t ht).1).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo] at ht
      rw [(hderiv t (hSIoo t ht).1).deriv]
      exact (hSIoo t ht).2.le
  -- `f → 0`: otherwise `(log (1 - F))' = -1 / f` is bounded and `1 - F` does not tend to `0`
  have hf0 : Tendsto f (𝓝[<] xF) (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun m hm ↦ ?_, fun M hM ↦ ?_⟩
    · filter_upwards [Ioo_mem_nhdsLT hz] with t ht
      exact hm.trans (hfpos t ht)
    · by_contra hcon
      have hge : ∀ s ∈ Ioo S xF, M ≤ f s := by
        intro s hs
        by_contra hlt
        push Not at hlt
        refine hcon ?_
        filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
        exact (hanti hs ⟨hs.1.trans ht.1, ht.2⟩ ht.1.le).trans_lt hlt
      set T₁ := (S + xF) / 2 with hT₁
      have hT₁m : T₁ ∈ Ioo S xF := ⟨by rw [hT₁]; linarith, by rw [hT₁]; linarith⟩
      set G : ℝ → ℝ := fun t ↦ log (1 - F t) with hG
      have hGd : ∀ s ∈ Ico T₁ xF, HasDerivWithinAt G (-(F₁ s / (1 - F s))) (Ico T₁ xF) s := by
        intro s hs
        have hsm : s ∈ Ioo S xF := ⟨hT₁m.1.trans_le hs.1, hs.2⟩
        have hsz := (hSIoo s hsm).1
        have hne : 1 - F s ≠ 0 := by linarith [hF s hsz]
        have := ((h1 s hsz).const_sub 1).log hne
        simpa [neg_div] using this.hasDerivWithinAt
      have hbd : ∀ s ∈ Ico T₁ xF, ‖-(F₁ s / (1 - F s))‖ ≤ M⁻¹ := by
        intro s hs
        have hsm : s ∈ Ioo S xF := ⟨hT₁m.1.trans_le hs.1, hs.2⟩
        have hsz := (hSIoo s hsm).1
        have hG0 : 0 < 1 - F s := by linarith [hF s hsz]
        have hf1 := hpos s hsz
        have hMf := hge s hsm
        rw [norm_neg, Real.norm_eq_abs, abs_of_pos (div_pos hf1 hG0), ← inv_div]
        exact inv_anti₀ hM hMf
      have hLip : ∀ t ∈ Ico T₁ xF, |G t - G T₁| ≤ M⁻¹ * (xF - T₁) := by
        intro t ht
        have := (convex_Ico T₁ xF).norm_image_sub_le_of_norm_hasDerivWithin_le hGd hbd
          (left_mem_Ico.2 hT₁m.2) ht
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht.1)] at this
        refine this.trans (mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hM).le)
        linarith [ht.2]
      have hG0lim : Tendsto (fun t ↦ 1 - F t) (𝓝[<] xF) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨by simpa using hF1.const_sub 1, ?_⟩
        filter_upwards [Ioo_mem_nhdsLT hz] with t ht
        have := hF t ht
        simp only [mem_Ioi]
        linarith
      have hGbot : Tendsto G (𝓝[<] xF) atBot := tendsto_log_nhdsGT_zero.comp hG0lim
      have hev := hGbot.eventually (eventually_lt_atBot (G T₁ - M⁻¹ * (xF - T₁)))
      obtain ⟨t, ht1, ht2⟩ := (hev.and (Ioo_mem_nhdsLT hT₁m.2)).exists
      have := hLip t ⟨ht2.1.le, ht2.2⟩
      rw [abs_le] at this
      linarith [this.1]
  -- L'Hôpital
  have hdist : Tendsto (fun t ↦ xF - t) (𝓝[<] xF) (𝓝 0) := by
    have : Tendsto (fun t ↦ xF - t) (𝓝 xF) (𝓝 (xF - xF)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun t ↦ f t / (xF - t)) (𝓝[<] xF) (𝓝 (-γ)) := by
    refine HasDerivAt.lhopital_zero_nhdsLT (f' := fd) (g' := fun _ ↦ -1) ?_ ?_ ?_ hf0 hdist ?_
    · filter_upwards [Ioo_mem_nhdsLT hz] with t ht using hderiv t ht
    · exact Eventually.of_forall fun t ↦ by
        simpa using (hasDerivAt_id t).const_sub xF
    · exact Eventually.of_forall fun _ ↦ by norm_num
    · simpa [div_neg] using hfd.neg
  have hα : 0 < -1 / γ := div_pos_of_neg_of_neg neg_one_lt_zero hγ
  have hvm1 : Tendsto (fun x ↦ (xF - x) * F₁ x / (1 - F x)) (𝓝[<] xF) (𝓝 (-1 / γ)) := by
    have := hL.inv₀ (neg_ne_zero.2 hγ.ne)
    rw [show (-γ)⁻¹ = -1 / γ by field_simp] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hz] with x hx
    have h3 := hpos x hx
    have h4 : 1 - F x ≠ 0 := by linarith [hF x hx]
    have h5 : xF - x ≠ 0 := by linarith [hx.2]
    simp only [hf]
    field_simp
  have := (F.isInMDAWeibull_of_vonMises hα hz h1 hvm1).isInMDAGEV
  rwa [show -1 / (-1 / γ) = γ by field_simp] at this

end CumulativeDistributionFunction
