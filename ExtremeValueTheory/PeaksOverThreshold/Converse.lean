/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.PeaksOverThreshold.Balkema

/-!
# The converse of the Pickands–Balkema–de Haan theorem

`ExtremeValueTheory.PeaksOverThreshold.Balkema` proves that `F ∈ MDA(H_ξ)` gives a scale
function `β > 0` with `F̄ (u + β(u) x) / F̄ u → Ḡ_{ξ,1}(x)` uniformly in `x ≥ 0` as `u ↑ x_F`.
Here we prove the converse for every `ξ ∈ ℝ` and an *arbitrary* scale function `β`, which makes
the Pickands–Balkema–de Haan theorem an equivalence ([EKM, Theorem 3.4.13(b)]).

## Proof sketch

Write `F̄ = 1 - F`, `Ḡ = Ḡ_{ξ,1}` and `Λ = Λ_ξ` for its inverse
(`(v ^ (-ξ) - 1) / ξ`, resp. `-log v`).

1. `F̄ u → 0` as `u ↑ x_F` (no atom at a finite endpoint), and at the quantile points
   `q(λ) = sInf {y | F̄ y ≤ λ}` there are no relative jumps: `F̄ (q λ) / λ → 1` as `λ → 0+`.
   Both follow from an infimum argument using the relation at a single `δ > 0`.
2. **Key comparison.** For `c > 1` let `s(t) = q(c F̄ t) ≤ t`. Uniformity at the moving base
   point `s(t)` gives `(t - s(t)) / β(s(t)) → Λ(1/c)` and, comparing the base points `t` and
   `s(t)`, `β(t) / β(s(t)) → c ^ ξ`. Hence `t + β(t) x` lies eventually to the right of `s(t)`
   if `x > Λ(c)` and to the left if `x < Λ(c)`.
3. Consequently `F̄ (t + β(t) x) / F̄ t → Ḡ(x)` also for `x < 0` with `1 + ξ x > 0`, i.e. `β` is
   an auxiliary function on the whole domain of `Ḡ`.
4. With `b n = q(1/n)` and `a n = β(b n)` this yields `n F̄ (b n + a n x) → Ḡ(x)`, from which the
   Fréchet (via `Frechet.isRegularlyVarying_of_tendsto_mul_affine`) and Weibull cases follow;
   the Gumbel case follows from step 3 and `isInMDAGumbel_of_auxiliary_atTop` / `..._nhdsLT`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 3.4.13 [EKM].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.1.6 [dHF].
* A. A. Balkema and L. de Haan, *Residual life time at great age*, Ann. Probab. 2 (1974).

## Main results

* `CumulativeDistributionFunction.tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival`: the
  excess limit relation extends to negative arguments.
* `CumulativeDistributionFunction.isInMDAGumbel_of_tendstoUniformlyOn_excessSurvival`,
  `CumulativeDistributionFunction.isRegularlyVarying_of_tendstoUniformlyOn_excessSurvival`,
  `CumulativeDistributionFunction.isInMDAWeibull_of_tendstoUniformlyOn_excessSurvival`: the
  three cases of the converse.
* `CumulativeDistributionFunction.isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` and
  `..._iff_exists_tendsto_sup_excessSurvival`: the Pickands–Balkema–de Haan theorem as an
  equivalence for all `ξ ∈ ℝ`.
-/

open Filter Topology Set Real

namespace ExtremeValueTheory

/-! ### The inverse of the GPD survival function -/

/-- The inverse `Λ_ξ` of the GPD survival function `Ḡ_{ξ,1}`: `Λ_ξ v = (v ^ (-ξ) - 1) / ξ` for
`ξ ≠ 0` and `Λ_0 v = -log v`. It satisfies `Λ_ξ (Ḡ_{ξ,1} x) = x` whenever `Ḡ_{ξ,1} x > 0`
(`gpdSurvivalInv_gpdSurvival'`), and it is strictly decreasing on `(0, ∞)`. -/
noncomputable def gpdSurvivalInv (ξ v : ℝ) : ℝ :=
  if ξ = 0 then -Real.log v else (v ^ (-ξ) - 1) / ξ

section GPDInv

variable {ξ : ℝ}

theorem gpdSurvival'_one_of_ne (hξ : ξ ≠ 0) (x : ℝ) :
    gpdSurvival' ξ 1 x = (max (1 + ξ * x) 0) ^ (-(1 / ξ)) := by
  simp [gpdSurvival', hξ]

/-- Where `Ḡ_{ξ,1} x > 0` (`ξ ≠ 0`), one has `Ḡ_{ξ,1} x ^ (-ξ) = 1 + ξ x`. -/
theorem gpdSurvival'_rpow_neg (hξ : ξ ≠ 0) {x : ℝ} (hpos : 0 < gpdSurvival' ξ 1 x) :
    gpdSurvival' ξ 1 x ^ (-ξ) = 1 + ξ * x := by
  rw [gpdSurvival'_one_of_ne hξ] at hpos ⊢
  have hne : -(1 / ξ) ≠ 0 := by
    rw [neg_ne_zero]; exact one_div_ne_zero hξ
  have hb : 0 < 1 + ξ * x := by
    by_contra hcon
    rw [max_eq_right (not_lt.1 hcon), zero_rpow hne] at hpos
    exact lt_irrefl _ hpos
  rw [max_eq_left hb.le, ← rpow_mul hb.le, show -(1 / ξ) * -ξ = 1 by field_simp, rpow_one]

theorem gpdSurvivalInv_gpdSurvival' {x : ℝ} (hpos : 0 < gpdSurvival' ξ 1 x) :
    gpdSurvivalInv ξ (gpdSurvival' ξ 1 x) = x := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [gpdSurvivalInv]
  · simp only [gpdSurvivalInv, hξ, ↓reduceIte]
    rw [gpdSurvival'_rpow_neg hξ hpos]
    field_simp
    ring

/-- The functional equation of `Λ_ξ`: `Λ_ξ (Ḡ_{ξ,1}(w) v) = Λ_ξ v + v ^ (-ξ) w`. -/
theorem gpdSurvivalInv_mul {v w : ℝ} (hv : 0 < v) (hw : 0 < gpdSurvival' ξ 1 w) :
    gpdSurvivalInv ξ (gpdSurvival' ξ 1 w * v) = gpdSurvivalInv ξ v + v ^ (-ξ) * w := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [gpdSurvivalInv, ↓reduceIte, gpdSurvival'_zero_left, neg_zero, rpow_zero,
      one_mul, div_one]
    rw [Real.log_mul (exp_pos _).ne' hv.ne', Real.log_exp]
    ring
  · simp only [gpdSurvivalInv, hξ, ↓reduceIte]
    rw [mul_rpow hw.le hv.le, gpdSurvival'_rpow_neg hξ hw]
    field_simp
    ring

theorem continuousAt_gpdSurvivalInv {v : ℝ} (hv : 0 < v) :
    ContinuousAt (gpdSurvivalInv ξ) v := by
  by_cases hξ : ξ = 0
  · have : gpdSurvivalInv ξ = fun v ↦ -Real.log v := by
      funext v; simp [gpdSurvivalInv, hξ]
    rw [this]
    exact (continuousAt_log hv.ne').neg
  · have : gpdSurvivalInv ξ = fun v ↦ (v ^ (-ξ) - 1) / ξ := by
      funext v; simp [gpdSurvivalInv, hξ]
    rw [this]
    exact ((continuousAt_id.rpow_const (Or.inl hv.ne')).sub continuousAt_const).div_const _

theorem gpdSurvivalInv_lt_gpdSurvivalInv {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    gpdSurvivalInv ξ b < gpdSurvivalInv ξ a := by
  rcases lt_trichotomy ξ 0 with hξ | hξ | hξ
  · simp only [gpdSurvivalInv, hξ.ne, ↓reduceIte]
    rw [div_lt_div_right_of_neg hξ]
    have := rpow_lt_rpow ha.le hab (neg_pos.2 hξ)
    linarith
  · subst hξ
    simp only [gpdSurvivalInv, ↓reduceIte, neg_lt_neg_iff]
    exact Real.log_lt_log ha hab
  · simp only [gpdSurvivalInv, hξ.ne', ↓reduceIte]
    rw [div_lt_div_iff_of_pos_right hξ]
    have := rpow_lt_rpow_of_neg ha hab (neg_neg_of_pos hξ)
    linarith

theorem gpdSurvivalInv_inv_add {c : ℝ} (hc : 0 < c) (x : ℝ) :
    gpdSurvivalInv ξ c⁻¹ + x * c⁻¹ ^ (-ξ) = c⁻¹ ^ (-ξ) * (x - gpdSurvivalInv ξ c) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [gpdSurvivalInv, ↓reduceIte, neg_zero, rpow_zero, Real.log_inv]
    ring
  · simp only [gpdSurvivalInv, hξ, ↓reduceIte]
    rw [inv_rpow hc.le]
    have hp : c ^ (-ξ) ≠ 0 := (rpow_pos_of_pos hc _).ne'
    field_simp
    ring

/-- `Ḡ_{ξ,1} x < 1` for `x > 0`. -/
theorem gpdSurvival'_lt_one {x : ℝ} (hx : 0 < x) : gpdSurvival' ξ 1 x < 1 := by
  rcases lt_trichotomy ξ 0 with hξ | hξ | hξ
  · rw [gpdSurvival'_one_of_ne hξ.ne]
    have hp : 0 < -(1 / ξ) := by
      have : 1 / ξ < 0 := one_div_neg.2 hξ
      linarith
    rcases le_or_gt (1 + ξ * x) 0 with hb | hb
    · rw [max_eq_right hb, zero_rpow hp.ne']; exact one_pos
    · rw [max_eq_left hb.le]
      exact rpow_lt_one hb.le (by nlinarith) hp
  · subst hξ
    simp only [gpdSurvival'_zero_left, div_one]
    exact Real.exp_lt_one_iff.2 (by linarith)
  · rw [gpdSurvival'_one_of_ne hξ.ne']
    have hb : 1 < 1 + ξ * x := by nlinarith
    rw [max_eq_left (by linarith)]
    exact rpow_lt_one_of_one_lt_of_neg hb (by
      have : 0 < 1 / ξ := one_div_pos.2 hξ
      linarith)

/-- For every `θ < 1` there is `δ > 0` with `θ < Ḡ_{ξ,1} δ < 1`. -/
theorem exists_lt_gpdSurvival'_lt_one {θ : ℝ} (hθ : θ < 1) :
    ∃ δ > 0, θ < gpdSurvival' ξ 1 δ ∧ gpdSurvival' ξ 1 δ < 1 := by
  have hc : Tendsto (gpdSurvival' ξ 1) (𝓝[>] 0) (𝓝 1) := by
    have := (gpdSurvival'_continuousOn (ξ := ξ) one_pos) 0 (mem_Ici.2 le_rfl)
    have h := this.tendsto
    rw [gpdSurvival'_zero_right] at h
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  obtain ⟨δ, h1, h2⟩ := ((hc.eventually (lt_mem_nhds hθ)).and self_mem_nhdsWithin).exists
  exact ⟨δ, h2, h1, gpdSurvival'_lt_one h2⟩

end GPDInv

/-- Composing a uniform limit with a convergent sequence of base points: if `f u → g` uniformly
on `S` along `L`, `σ → L` and `ζ ∈ S` eventually, then `f (σ k) (ζ k) - g (ζ k) → 0`. -/
theorem TendstoUniformlyOn.tendsto_sub_comp {ι κ : Type*} {L : Filter ι} {l : Filter κ}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ} {S : Set ℝ} (hU : TendstoUniformlyOn f g L S) {σ : κ → ι}
    {ζ : κ → ℝ} (hσ : Tendsto σ l L) (hζ : ∀ᶠ k in l, ζ k ∈ S) :
    Tendsto (fun k ↦ f (σ k) (ζ k) - g (ζ k)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hσ.eventually (Metric.tendstoUniformlyOn_iff.1 hU ε hε), hζ] with k h1 h2
  rw [Real.dist_eq, sub_zero, abs_sub_comm, ← Real.dist_eq]
  exact h1 _ h2

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

variable (F : CumulativeDistributionFunction)

private lemma conv_antitone : Antitone (fun x ↦ 1 - F x) :=
  fun _ _ h ↦ sub_le_sub_left (F.mono' h) 1

private lemma conv_rightContinuous : ∀ x, ContinuousWithinAt (fun x ↦ 1 - F x) (Ici x) x :=
  fun x ↦ continuousWithinAt_const.sub (F.right_continuous x)

private lemma conv_nonneg (x : ℝ) : 0 ≤ 1 - F x := by linarith [F.apply_le_one x]

/-! ### The filter `u ↑ x_F` -/

/-- The filter `u ↑ x_F` has the basis `(x, ∞) ∩ {F < 1}`, `F x < 1`. -/
theorem upperEndpointFilter_hasBasis :
    F.upperEndpointFilter.HasBasis (fun x ↦ F x < 1) (fun x ↦ Ioi x ∩ {y | F y < 1}) := by
  refine hasBasis_biInf_principal ?_ ?_
  · intro x hx y hy
    refine ⟨max x y, ?_, ?_, ?_⟩
    · rcases max_choice x y with h | h <;> rw [h] <;> assumption
    · exact inter_subset_inter_left _ (Ioi_subset_Ioi (le_max_left _ _))
    · exact inter_subset_inter_left _ (Ioi_subset_Ioi (le_max_right _ _))
  · obtain ⟨x, hx⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds one_pos)).exists
    exact ⟨x, hx⟩

instance upperEndpointFilter_neBot : F.upperEndpointFilter.NeBot := by
  refine (F.upperEndpointFilter_hasBasis.neBot_iff).2 fun {x} hx ↦ ?_
  have h : ∀ᶠ y in 𝓝[>] x, F y < 1 :=
    ((F.right_continuous x).mono Ioi_subset_Ici_self).eventually (gt_mem_nhds hx)
  obtain ⟨y, hy1, hy2⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨y, hy2, hy1⟩

theorem eventually_gt_upperEndpointFilter {x : ℝ} (hx : F x < 1) :
    ∀ᶠ u in F.upperEndpointFilter, x < u ∧ F u < 1 :=
  F.upperEndpointFilter_hasBasis.mem_of_mem hx

theorem eventually_tail_pos_upperEndpointFilter :
    ∀ᶠ u in F.upperEndpointFilter, 0 < 1 - F u := by
  obtain ⟨x, hx⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds one_pos)).exists
  filter_upwards [F.eventually_gt_upperEndpointFilter hx] with u hu
  linarith [hu.2]

/-! ### Consequences of the uniform GPD approximation -/

section Converse

variable {F} {ξ : ℝ} {β : ℝ → ℝ}
  (hβ : ∀ᶠ u in F.upperEndpointFilter, 0 < β u)
  (hU : TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
    (gpdSurvival' ξ 1) F.upperEndpointFilter (Ici 0))
include hβ hU

omit hβ in
private lemma conv_pt {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun u ↦ (1 - F (u + β u * x)) / (1 - F u)) F.upperEndpointFilter
      (𝓝 (gpdSurvival' ξ 1 x)) :=
  hU.tendsto_at (mem_Ici.2 hx)

/-- Under the uniform GPD approximation, `F̄ u → 0` as `u ↑ x_F` (`F` has no atom at a finite
right endpoint). -/
theorem tendsto_tail_zero_of_tendstoUniformlyOn_excessSurvival :
    Tendsto (fun u ↦ 1 - F u) F.upperEndpointFilter (𝓝 0) := by
  obtain ⟨w, hw, hw0, hw1⟩ := exists_lt_gpdSurvival'_lt_one (ξ := ξ) (θ := 0) one_pos
  set g := gpdSurvival' ξ 1 w with hg
  set κ := (g + 1) / 2 with hκ
  have hA : ∀ᶠ u in F.upperEndpointFilter, 0 < β u ∧ 0 < 1 - F u ∧
      0 < (1 - F (u + β u * w)) / (1 - F u) ∧ (1 - F (u + β u * w)) / (1 - F u) < κ := by
    filter_upwards [hβ, F.eventually_tail_pos_upperEndpointFilter,
      (conv_pt hU hw.le).eventually (Ioo_mem_nhds hw0 (show g < κ by rw [hκ]; linarith))]
      with u h1 h2 h3
    exact ⟨h1, h2, h3.1, h3.2⟩
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun u ↦ ha.trans_le (F.conv_nonneg u), fun ε hε ↦ ?_⟩
  suffices h : ∃ y, F y < 1 ∧ 1 - F y < ε by
    obtain ⟨y, hy1, hy2⟩ := h
    filter_upwards [F.eventually_gt_upperEndpointFilter hy1] with u hu
    exact (F.conv_antitone hu.1.le).trans_lt hy2
  by_contra hcon
  push Not at hcon
  set S := (fun y ↦ 1 - F y) '' {y | F y < 1} with hS
  obtain ⟨y₀, hy₀⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds one_pos)).exists
  have hne : S.Nonempty := ⟨_, mem_image_of_mem _ (show y₀ ∈ {y | F y < 1} from hy₀)⟩
  have hB : BddBelow S := ⟨0, by rintro _ ⟨y, -, rfl⟩; exact F.conv_nonneg y⟩
  have hεm : ε ≤ sInf S := le_csInf hne (by rintro _ ⟨y, hy, rfl⟩; exact hcon y hy)
  have hm : 0 < sInf S := hε.trans_le hεm
  have hκ1 : κ < 1 := by rw [hκ]; linarith
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hlt : sInf S < sInf S / κ := by rw [lt_div_iff₀ hκ0]; nlinarith
  obtain ⟨_, ⟨y, hy, rfl⟩, hyc⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨u, ⟨h1, h2, h3, h4⟩, hu⟩ := (hA.and (F.eventually_gt_upperEndpointFilter hy)).exists
  have hGu : 1 - F u ≤ 1 - F y := F.conv_antitone hu.1.le
  rw [div_pos_iff_of_pos_right h2] at h3
  rw [div_lt_iff₀ h2] at h4
  have hmem : F (u + β u * w) < 1 := by linarith
  have := csInf_le hB (mem_image_of_mem _ (show u + β u * w ∈ {y | F y < 1} from hmem))
  have : κ * (1 - F u) < sInf S := by
    calc κ * (1 - F u) ≤ κ * (1 - F y) := mul_le_mul_of_nonneg_left hGu hκ0.le
      _ < κ * (sInf S / κ) := mul_lt_mul_of_pos_left hyc hκ0
      _ = sInf S := by field_simp
  linarith

theorem exists_tail_pos_le_of_tendstoUniformlyOn_excessSurvival {c : ℝ} (hc : 0 < c) :
    ∃ y, 0 < 1 - F y ∧ 1 - F y ≤ c := by
  obtain ⟨y, h1, h2⟩ := (((tendsto_tail_zero_of_tendstoUniformlyOn_excessSurvival hβ hU).eventually
    (gt_mem_nhds hc)).and F.eventually_tail_pos_upperEndpointFilter).exists
  exact ⟨y, h2, h1.le⟩


omit hβ hU in
/-- The quantile-type point `sInf {y | F̄ y ≤ λ}`. -/
private lemma conv_quantile_spec {lam : ℝ} (hlo : ∃ y, lam < 1 - F y)
    (hhi : ∃ y, 0 < 1 - F y ∧ 1 - F y ≤ lam) :
    1 - F (sInf {y | 1 - F y ≤ lam}) ≤ lam ∧
      (∀ y < sInf {y | 1 - F y ≤ lam}, lam < 1 - F y) ∧
      0 < 1 - F (sInf {y | 1 - F y ≤ lam}) := by
  obtain ⟨y₁, hy₁, hy₁'⟩ := hhi
  have hq := Gumbel.quantile_spec F.conv_antitone F.conv_rightContinuous ⟨y₁, hy₁'⟩ hlo
  refine ⟨hq.1, hq.2, ?_⟩
  have hle : sInf {y | 1 - F y ≤ lam} ≤ y₁ := by
    by_contra hcon
    have := hq.2 y₁ (not_le.1 hcon)
    linarith
  exact hy₁.trans_le (F.conv_antitone hle)

omit hU in
/-- **No relative jumps at the quantiles.** For every `θ < 1` there is `x₀ < x_F` such that,
whenever `q > x₀` and `F̄ > λ > 0` on `(-∞, q)`, one has `F̄ q ≥ θ λ`. -/
private lemma conv_claimJ (hU : TendstoUniformlyOn
      (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x)) (gpdSurvival' ξ 1)
      F.upperEndpointFilter (Ici 0)) {θ : ℝ} (hθ : θ < 1) :
    ∃ x₀, F x₀ < 1 ∧ ∀ q lam : ℝ, 0 < lam → (∀ y < q, lam < 1 - F y) → x₀ < q →
      θ * lam ≤ 1 - F q := by
  obtain ⟨δ, hδ, hθg, hg1⟩ := exists_lt_gpdSurvival'_lt_one (ξ := ξ) hθ
  set g := gpdSurvival' ξ 1 δ with hg
  set ε := min (g - θ) ((1 - g) / 2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ g - θ := min_le_left _ _
  have hε2 : ε ≤ (1 - g) / 2 := min_le_right _ _
  set κ := g + ε with hκ
  have hg0 : 0 ≤ g := gpdSurvival'_nonneg _ _ _
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hκ1 : κ < 1 := by rw [hκ]; linarith
  have hA : ∀ᶠ u in F.upperEndpointFilter, 0 < β u ∧
      |(1 - F (u + β u * δ)) / (1 - F u) - g| < ε := by
    filter_upwards [hβ, (conv_pt hU hδ.le).eventually (Metric.ball_mem_nhds g hε0)] with u h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨x₀, hx₀, hA'⟩ := F.upperEndpointFilter_hasBasis.eventually_iff.1 hA
  refine ⟨x₀, hx₀, fun q lam hlam hq hxq ↦ ?_⟩
  rcases le_or_gt θ 0 with hθ0 | hθ0
  · exact (mul_nonpos_of_nonpos_of_nonneg hθ0 hlam.le).trans (F.conv_nonneg q)
  by_contra hcon
  push Not at hcon
  have hgood : ∀ t ∈ Ioo x₀ q, 0 < β t ∧ 0 < 1 - F t ∧
      θ * (1 - F t) < 1 - F (t + β t * δ) ∧ 1 - F (t + β t * δ) < κ * (1 - F t) := by
    intro t ht
    have hGt : lam < 1 - F t := hq t ht.2
    have hGt0 : 0 < 1 - F t := hlam.trans hGt
    obtain ⟨h1, h2⟩ := hA' ⟨ht.1, show F t < 1 by linarith⟩
    rw [abs_lt] at h2
    refine ⟨h1, hGt0, ?_, ?_⟩
    · have : θ < (1 - F (t + β t * δ)) / (1 - F t) := by linarith
      rwa [lt_div_iff₀ hGt0] at this
    · have : (1 - F (t + β t * δ)) / (1 - F t) < κ := by linarith
      rwa [div_lt_iff₀ hGt0] at this
  have hall : ∀ t ∈ Ioo x₀ q, t + β t * δ < q := by
    intro t ht
    by_contra hcon'
    push Not at hcon'
    obtain ⟨-, -, h3, -⟩ := hgood t ht
    have h4 : 1 - F (t + β t * δ) ≤ 1 - F q := F.conv_antitone hcon'
    have h5 : θ * lam < θ * (1 - F t) := mul_lt_mul_of_pos_left (hq t ht.2) hθ0
    linarith
  set S := (fun y ↦ 1 - F y) '' Ioo x₀ q with hS
  have hne : S.Nonempty := ⟨_, mem_image_of_mem _ (show (x₀ + q) / 2 ∈ Ioo x₀ q from
    ⟨by linarith, by linarith⟩)⟩
  have hB : BddBelow S := ⟨0, by rintro _ ⟨y, -, rfl⟩; exact F.conv_nonneg y⟩
  have hlm : lam ≤ sInf S := le_csInf hne (by rintro _ ⟨y, hy, rfl⟩; exact (hq y hy.2).le)
  have hm : 0 < sInf S := hlam.trans_le hlm
  have hlt : sInf S < sInf S / κ := by rw [lt_div_iff₀ hκ0]; nlinarith
  obtain ⟨_, ⟨t, ht, rfl⟩, htc⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨h1, h2, -, h4⟩ := hgood t ht
  have ht' : t + β t * δ ∈ Ioo x₀ q := ⟨by nlinarith [ht.1], hall t ht⟩
  have := csInf_le hB (mem_image_of_mem _ ht')
  have : κ * (1 - F t) < sInf S := by
    calc κ * (1 - F t) < κ * (sInf S / κ) := mul_lt_mul_of_pos_left htc hκ0
      _ = sInf S := by field_simp
  linarith

/-- **Quantiles under the uniform GPD approximation.** The quantile points
`q(λ) = sInf {y | F̄ y ≤ λ}` at levels `λ → 0+` tend to the right endpoint, and `F̄` at the
quantile is asymptotic to the level: `F̄ (q λ) / λ → 1` (no relative jumps). -/
theorem tendsto_quantile_of_tendstoUniformlyOn_excessSurvival {κ : Type*} {l : Filter κ}
    {lam : κ → ℝ} (hlam : Tendsto lam l (𝓝[>] 0)) :
    Tendsto (fun k ↦ sInf {y | 1 - F y ≤ lam k}) l F.upperEndpointFilter ∧
      Tendsto (fun k ↦ (1 - F (sInf {y | 1 - F y ≤ lam k})) / lam k) l (𝓝 1) ∧
      ∀ x₀, F x₀ < 1 → ∀ᶠ k in l, 0 < lam k ∧ 1 - F (sInf {y | 1 - F y ≤ lam k}) ≤ lam k ∧
        (∀ y < sInf {y | 1 - F y ≤ lam k}, lam k < 1 - F y) ∧
        0 < 1 - F (sInf {y | 1 - F y ≤ lam k}) ∧ x₀ < sInf {y | 1 - F y ≤ lam k} := by
  have hlam0 : Tendsto lam l (𝓝 0) := hlam.mono_right nhdsWithin_le_nhds
  have hlampos : ∀ᶠ k in l, 0 < lam k := hlam.eventually self_mem_nhdsWithin
  have hspec : ∀ x₀, F x₀ < 1 → ∀ᶠ k in l, 0 < lam k ∧
      1 - F (sInf {y | 1 - F y ≤ lam k}) ≤ lam k ∧
      (∀ y < sInf {y | 1 - F y ≤ lam k}, lam k < 1 - F y) ∧
      0 < 1 - F (sInf {y | 1 - F y ≤ lam k}) ∧ x₀ < sInf {y | 1 - F y ≤ lam k} := by
    intro x₀ hx₀
    filter_upwards [hlampos, hlam0.eventually (gt_mem_nhds (show 0 < 1 - F x₀ by linarith))]
      with k hk1 hk2
    obtain ⟨h1, h2, h3⟩ := conv_quantile_spec ⟨x₀, hk2⟩
      (exists_tail_pos_le_of_tendstoUniformlyOn_excessSurvival hβ hU hk1)
    refine ⟨hk1, h1, h2, h3, ?_⟩
    by_contra hcon
    have := F.conv_antitone (not_lt.1 hcon)
    simp only at this
    linarith
  refine ⟨?_, ?_, hspec⟩
  · refine F.upperEndpointFilter_hasBasis.tendsto_right_iff.2 fun x₀ hx₀ ↦ ?_
    filter_upwards [hspec x₀ hx₀] with k hk
    exact ⟨hk.2.2.2.2, show F _ < 1 by linarith [hk.2.2.2.1]⟩
  · rw [tendsto_order]
    refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · obtain ⟨x₀, hx₀, hJ⟩ := conv_claimJ hβ hU (show (a + 1) / 2 < 1 by linarith)
      filter_upwards [hspec x₀ hx₀] with k hk
      obtain ⟨hk1, -, hk3, -, hk5⟩ := hk
      have := hJ _ _ hk1 hk3 hk5
      rw [lt_div_iff₀ hk1]
      nlinarith
    · obtain ⟨y₀, hy₀⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds one_pos)).exists
      filter_upwards [hspec y₀ hy₀] with k hk
      obtain ⟨hk1, hk2, -⟩ := hk
      rw [div_lt_iff₀ hk1]
      nlinarith

/-- **The key comparison.** For `c > 1` let `s(t) = sInf {y | F̄ y ≤ c F̄ t}`. Then
`(t - s(t)) / β(s(t)) → Λ_ξ(1/c)` and `β(t) / β(s(t)) → c ^ ξ` as `t ↑ x_F`; consequently, for
`x > Λ_ξ(c)` eventually `t + β(t) x ≥ s(t)`, so `F̄ (t + β(t) x) ≤ c F̄ t`, and for `x < Λ_ξ(c)`
eventually `t + β(t) x < s(t)`, so `F̄ (t + β(t) x) > c F̄ t`. -/
private lemma conv_step {c : ℝ} (hc : 1 < c) :
    (∀ x, gpdSurvivalInv ξ c < x →
      ∀ᶠ t in F.upperEndpointFilter, 1 - F (t + β t * x) ≤ c * (1 - F t)) ∧
    (∀ x, x < gpdSurvivalInv ξ c →
      ∀ᶠ t in F.upperEndpointFilter, c * (1 - F t) < 1 - F (t + β t * x)) := by
  have hc0 : 0 < c := by linarith
  set s : ℝ → ℝ := fun t ↦ sInf {y | 1 - F y ≤ c * (1 - F t)} with hs_def
  have hG0 := tendsto_tail_zero_of_tendstoUniformlyOn_excessSurvival hβ hU
  have hlam : Tendsto (fun t ↦ c * (1 - F t)) F.upperEndpointFilter (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by simpa using hG0.const_mul c, ?_⟩
    filter_upwards [F.eventually_tail_pos_upperEndpointFilter] with t ht
    exact mul_pos hc0 ht
  obtain ⟨hs, hJ, hspec⟩ := tendsto_quantile_of_tendstoUniformlyOn_excessSurvival hβ hU hlam
  obtain ⟨y₀, hy₀⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds one_pos)).exists
  have hsp := hspec y₀ hy₀
  have hst : ∀ᶠ t in F.upperEndpointFilter, s t ≤ t ∧ 0 < 1 - F t ∧ 0 < β (s t) ∧
      0 < 1 - F (s t) := by
    filter_upwards [hsp, F.eventually_tail_pos_upperEndpointFilter, hs.eventually hβ]
      with t h1 h2 h3
    refine ⟨?_, h2, h3, h1.2.2.2.1⟩
    by_contra hcon
    have := h1.2.2.1 t (not_le.1 hcon)
    nlinarith
  -- `F̄ t / F̄ (s t) → 1 / c`
  have hratio : Tendsto (fun t ↦ (1 - F t) / (1 - F (s t))) F.upperEndpointFilter (𝓝 c⁻¹) := by
    have := (hJ.inv₀ one_ne_zero).const_mul c⁻¹
    rw [inv_one, mul_one] at this
    refine this.congr' ?_
    filter_upwards [hst] with t ht
    have h1 := ht.2.1.ne'
    have h2 := ht.2.2.2.ne'
    simp only [hs_def] at h2 ⊢
    field_simp
  -- `z t = (t - s t) / β (s t) → Λ (1 / c)`
  set z : ℝ → ℝ := fun t ↦ (t - s t) / β (s t) with hz_def
  have hz0 : ∀ᶠ t in F.upperEndpointFilter, z t ∈ Ici 0 := by
    filter_upwards [hst] with t ht
    exact div_nonneg (sub_nonneg.2 ht.1) ht.2.2.1.le
  have hGz : Tendsto (fun t ↦ gpdSurvival' ξ 1 (z t)) F.upperEndpointFilter (𝓝 c⁻¹) := by
    have := hratio.sub (hU.tendsto_sub_comp hs hz0)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hst] with t ht
    have h1 := ht.2.2.1.ne'
    simp only [excessSurvival, hz_def]
    rw [show s t + β (s t) * ((t - s t) / β (s t)) = t by field_simp; ring]
    ring
  have hzlim : Tendsto z F.upperEndpointFilter (𝓝 (gpdSurvivalInv ξ c⁻¹)) := by
    refine ((continuousAt_gpdSurvivalInv (inv_pos.2 hc0)).tendsto.comp hGz).congr' ?_
    filter_upwards [hGz.eventually (lt_mem_nhds (inv_pos.2 hc0))] with t ht
    exact gpdSurvivalInv_gpdSurvival' ht
  -- `r t = β t / β (s t) → c⁻¹ ^ (-ξ)`
  obtain ⟨w, hw, hw0, -⟩ := exists_lt_gpdSurvival'_lt_one (ξ := ξ) (θ := 0) one_pos
  set r : ℝ → ℝ := fun t ↦ β t / β (s t) with hr_def
  set ζ : ℝ → ℝ := fun t ↦ z t + r t * w with hζ_def
  have hζ0 : ∀ᶠ t in F.upperEndpointFilter, ζ t ∈ Ici 0 := by
    filter_upwards [hst, hz0, hβ] with t ht h1 h2
    exact add_nonneg h1 (mul_nonneg (div_nonneg h2.le ht.2.2.1.le) hw.le)
  have hGζ : Tendsto (fun t ↦ gpdSurvival' ξ 1 (ζ t)) F.upperEndpointFilter
      (𝓝 (gpdSurvival' ξ 1 w * c⁻¹)) := by
    have := ((conv_pt hU hw.le).mul hratio).sub (hU.tendsto_sub_comp hs hζ0)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hst] with t ht
    have h1 := ht.2.2.1.ne'
    have h2 := ht.2.1.ne'
    have h3 := ht.2.2.2.ne'
    simp only [excessSurvival, hζ_def, hz_def, hr_def]
    rw [show s t + β (s t) * ((t - s t) / β (s t) + β t / β (s t) * w) = t + β t * w by
      field_simp; ring]
    simp only [hs_def] at h3 ⊢
    field_simp
    ring
  have hζlim : Tendsto ζ F.upperEndpointFilter
      (𝓝 (gpdSurvivalInv ξ c⁻¹ + c⁻¹ ^ (-ξ) * w)) := by
    rw [← gpdSurvivalInv_mul (inv_pos.2 hc0) hw0]
    have hpos : 0 < gpdSurvival' ξ 1 w * c⁻¹ := mul_pos hw0 (inv_pos.2 hc0)
    refine ((continuousAt_gpdSurvivalInv hpos).tendsto.comp hGζ).congr' ?_
    filter_upwards [hGζ.eventually (lt_mem_nhds hpos)] with t ht
    exact gpdSurvivalInv_gpdSurvival' ht
  have hrlim : Tendsto r F.upperEndpointFilter (𝓝 (c⁻¹ ^ (-ξ))) := by
    have := (hζlim.sub hzlim).div_const w
    rw [show (gpdSurvivalInv ξ c⁻¹ + c⁻¹ ^ (-ξ) * w - gpdSurvivalInv ξ c⁻¹) / w = c⁻¹ ^ (-ξ) by
      field_simp; ring] at this
    refine this.congr fun t ↦ ?_
    simp only [hζ_def]
    field_simp
    ring
  have hρ : 0 < c⁻¹ ^ (-ξ) := rpow_pos_of_pos (inv_pos.2 hc0) _
  -- the position of `t + β t * x` relative to `s t`
  have hlin : ∀ x, Tendsto (fun t ↦ (t + β t * x - s t) / β (s t)) F.upperEndpointFilter
      (𝓝 (c⁻¹ ^ (-ξ) * (x - gpdSurvivalInv ξ c))) := by
    intro x
    rw [← gpdSurvivalInv_inv_add hc0]
    refine (hzlim.add (hrlim.const_mul x)).congr' ?_
    filter_upwards [hst] with t ht
    have h1 := ht.2.2.1.ne'
    simp only [hz_def, hr_def]
    field_simp
    ring
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hpos : 0 < c⁻¹ ^ (-ξ) * (x - gpdSurvivalInv ξ c) := mul_pos hρ (by linarith)
    filter_upwards [(hlin x).eventually (lt_mem_nhds hpos), hst, hsp] with t h1 h2 h3
    have : s t ≤ t + β t * x := by
      have := (div_pos_iff_of_pos_right h2.2.2.1).1 h1
      linarith
    exact (F.conv_antitone this).trans h3.2.1
  · have hneg : c⁻¹ ^ (-ξ) * (x - gpdSurvivalInv ξ c) < 0 :=
      mul_neg_of_pos_of_neg hρ (by linarith)
    filter_upwards [(hlin x).eventually (gt_mem_nhds hneg), hst, hsp] with t h1 h2 h3
    have : t + β t * x < s t := by
      have := (div_neg_iff.1 h1)
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · linarith [h2.2.2.1]
      · linarith
    exact h3.2.2.1 _ this

/-- **Extension of the excess limit relation to negative arguments.** Under the uniform GPD
approximation on `[0, ∞)`, the relation `F̄ (t + β(t) x) / F̄ t → T` holds as `t ↑ x_F` for
every `x` and `T > 1` with `Λ_ξ T = x`, i.e. for every `x < 0` with `1 + ξ x > 0`, where
`T = (1 + ξ x) ^ (-1/ξ)` (`exp (-x)` if `ξ = 0`). -/
theorem tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival {x T : ℝ} (hT : 1 < T)
    (hx : gpdSurvivalInv ξ T = x) :
    Tendsto (fun t ↦ (1 - F (t + β t * x)) / (1 - F t)) F.upperEndpointFilter (𝓝 T) := by
  rw [tendsto_order]
  refine ⟨fun l hl ↦ ?_, fun m hm ↦ ?_⟩
  · set c := (max l 1 + T) / 2 with hc
    have hc1 : 1 < c := by rw [hc]; linarith [le_max_right l 1]
    have hlc : l < c := by rw [hc]; linarith [le_max_left l 1]
    have hcT : c < T := by rw [hc]; linarith [max_lt hl hT]
    have := gpdSurvivalInv_lt_gpdSurvivalInv (ξ := ξ) (by linarith) hcT
    filter_upwards [(conv_step hβ hU hc1).2 x (by rw [← hx]; exact this),
      F.eventually_tail_pos_upperEndpointFilter] with t h1 h2
    rw [lt_div_iff₀ h2]
    nlinarith
  · set c := (T + m) / 2 with hc
    have hc1 : 1 < c := by rw [hc]; linarith
    have hcm : c < m := by rw [hc]; linarith
    have hTc : T < c := by rw [hc]; linarith
    have := gpdSurvivalInv_lt_gpdSurvivalInv (ξ := ξ) (by linarith) hTc
    filter_upwards [(conv_step hβ hU hc1).1 x (by rw [← hx]; exact this),
      F.eventually_tail_pos_upperEndpointFilter] with t h1 h2
    rw [div_lt_iff₀ h2]
    nlinarith

/-- The normalizing sequences `b n = sInf {y | F̄ y ≤ 1 / n}` and `a n = β (b n)` turn every
excess limit relation `F̄ (t + β(t) x) / F̄ t → T` into `n F̄ (b n + a n x) → T`. -/
private lemma conv_seq : ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∀ x T : ℝ,
    Tendsto (fun t ↦ (1 - F (t + β t * x)) / (1 - F t)) F.upperEndpointFilter (𝓝 T) →
      Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (b n + a n * x))) atTop (𝓝 T) := by
  have hlam : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    show (0 : ℝ) < 1 / (n : ℝ)
    exact div_pos one_pos (by linarith)
  obtain ⟨hb, hJ, -⟩ := tendsto_quantile_of_tendstoUniformlyOn_excessSurvival hβ hU hlam
  set b : ℕ → ℝ := fun n ↦ sInf {y | 1 - F y ≤ 1 / (n : ℝ)} with hb_def
  refine ⟨fun n ↦ if 0 < β (b n) then β (b n) else 1, b, fun n ↦ ?_, fun x T h ↦ ?_⟩
  · simp only
    split_ifs with h
    · exact h
    · exact one_pos
  · have := hJ.mul (h.comp hb)
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [hb.eventually hβ, hb.eventually F.eventually_tail_pos_upperEndpointFilter,
      eventually_ge_atTop 1] with n h1 h2 h3
    have hn : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast h3
      positivity
    simp only [Function.comp_apply, hb_def] at h1 h2 ⊢
    simp only [h1, ↓reduceIte]
    generalize sInf {y | 1 - F y ≤ 1 / (n : ℝ)} = B at h1 h2 ⊢
    have h2' := h2.ne'
    field_simp

end Converse

section Main

variable {F} {ξ : ℝ} {β : ℝ → ℝ}

/-- **Converse of the Pickands–Balkema–de Haan theorem, Gumbel case** ([EKM, Theorem
3.4.13(b)], [dHF, Theorem 1.1.6]): if for some scale function `β > 0` the rescaled excesses
`F̄ (u + β(u) x) / F̄ u` converge to `exp (-x)` uniformly in `x ≥ 0` as `u ↑ x_F`, then `F` is in
the Gumbel domain of attraction. The relation is first extended to `x < 0`
(`tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival`), so that `β` is an auxiliary
function, and then `isInMDAGumbel_of_auxiliary_atTop` / `..._nhdsLT` applies. -/
theorem isInMDAGumbel_of_tendstoUniformlyOn_excessSurvival
    (hβ : ∀ᶠ u in F.upperEndpointFilter, 0 < β u)
    (hU : TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
      (gpdSurvival' 0 1) F.upperEndpointFilter (Ici 0)) :
    F.IsInMDAGumbel := by
  have hall : ∀ x, Tendsto (fun t ↦ (1 - F (t + x * β t)) / (1 - F t)) F.upperEndpointFilter
      (𝓝 (Real.exp (-x))) := by
    intro x
    have e : (fun t ↦ (1 - F (t + x * β t)) / (1 - F t)) =
        fun t ↦ (1 - F (t + β t * x)) / (1 - F t) := by
      funext t; rw [mul_comm]
    rw [e]
    rcases le_or_gt 0 x with hx | hx
    · have := conv_pt hU hx
      simpa using this
    · refine tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival hβ hU ?_ (by
        simp [gpdSurvivalInv])
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by linarith)
  by_cases hF : ∀ x, F x < 1
  · rw [F.upperEndpointFilter_eq_atTop hF] at hβ hall
    exact F.isInMDAGumbel_of_auxiliary_atTop hF hβ hall
  · obtain ⟨xF, hlt, heq⟩ := F.exists_rightEndpoint_of_not_lt_one hF
    rw [F.upperEndpointFilter_eq_nhdsLT heq hlt] at hβ hall
    exact F.isInMDAGumbel_of_auxiliary_nhdsLT hlt heq hβ hall

/-- **Converse of the Pickands–Balkema–de Haan theorem, Fréchet case** ([EKM, Theorem
3.4.13(b)]): if for some scale function `β > 0` the rescaled excesses converge to
`Ḡ_{ξ,1}(x) = (1 + ξ x) ^ (-1/ξ)`, `ξ > 0`, uniformly in `x ≥ 0` as `u ↑ x_F`, then the tail
`1 - F` is regularly varying with index `-1/ξ`. No relation between `β` and the canonical
`u ↦ ξ u` is assumed. -/
theorem isRegularlyVarying_of_tendstoUniformlyOn_excessSurvival (hξ : 0 < ξ)
    (hβ : ∀ᶠ u in F.upperEndpointFilter, 0 < β u)
    (hU : TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
      (gpdSurvival' ξ 1) F.upperEndpointFilter (Ici 0)) :
    IsRegularlyVarying (fun x ↦ 1 - F x) (-(1 / ξ)) := by
  obtain ⟨a, b, ha, hseq⟩ := conv_seq hβ hU
  refine Frechet.isRegularlyVarying_of_tendsto_mul_affine F.conv_antitone (one_div_pos.2 hξ)
    (a := fun n ↦ a n / ξ) (b := fun n ↦ b n - a n / ξ) (fun n ↦ div_pos (ha n) hξ)
    fun y hy ↦ ?_
  have hrel : Tendsto (fun t ↦ (1 - F (t + β t * ((y - 1) / ξ))) / (1 - F t))
      F.upperEndpointFilter (𝓝 (y ^ (-(1 / ξ)))) := by
    rcases le_or_gt 1 y with hy1 | hy1
    · have hx : 0 ≤ (y - 1) / ξ := div_nonneg (by linarith) hξ.le
      have := conv_pt hU hx
      rwa [gpdSurvival'_one_of_ne hξ.ne', show 1 + ξ * ((y - 1) / ξ) = y by field_simp; ring,
        max_eq_left hy.le] at this
    · refine tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival hβ hU
        (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hy hy1
          (neg_neg_of_pos (one_div_pos.2 hξ))) ?_
      simp only [gpdSurvivalInv, hξ.ne', ↓reduceIte]
      rw [← rpow_mul hy.le, show -(1 / ξ) * -ξ = 1 by field_simp, rpow_one]
  refine (hseq _ _ hrel).congr fun n ↦ ?_
  have hξ' := hξ.ne'
  rw [show b n + a n * ((y - 1) / ξ) = a n / ξ * y + (b n - a n / ξ) by field_simp; ring]

/-- **Converse of the Pickands–Balkema–de Haan theorem, Weibull case** ([EKM, Theorem
3.4.13(b)]): if for some scale function `β > 0` the rescaled excesses converge to
`Ḡ_{ξ,1}(x) = (max (1 + ξ x) 0) ^ (-1/ξ)`, `ξ < 0`, uniformly in `x ≥ 0` as `u ↑ x_F`, then `F` is
in the maximum domain of attraction of the Weibull distribution `Ψ_{-1/ξ}`. The normalization
is `b n + a n α (1 + z)` with `α = -1/ξ`, `b n = F^← (1 - 1/n)` and `a n = β (b n)`. -/
theorem isInMDAWeibull_of_tendstoUniformlyOn_excessSurvival (hξ : ξ < 0)
    (hβ : ∀ᶠ u in F.upperEndpointFilter, 0 < β u)
    (hU : TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
      (gpdSurvival' ξ 1) F.upperEndpointFilter (Ici 0)) :
    F.IsInMDAWeibull (div_pos_of_neg_of_neg neg_one_lt_zero hξ) := by
  have hα : 0 < -1 / ξ := div_pos_of_neg_of_neg neg_one_lt_zero hξ
  set α := -1 / ξ with hα_def
  have hξ' := hξ.ne
  have hαξ : -(1 / ξ) = α := by rw [hα_def]; ring
  obtain ⟨a, b, ha, hseq⟩ := conv_seq hβ hU
  have ha' : ∀ n, 0 < a n * α := fun n ↦ mul_pos (ha n) hα
  refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (ha' n) (b n + a n * α))⁻¹, fun z ↦ ?_⟩
  have happ : ∀ n, ((AffineIncrEquiv.mkOfCoefs (ha' n) (b n + a n * α))⁻¹ • F) z =
      F (b n + a n * (α * (1 + z))) := by
    intro n
    rw [show b n + a n * (α * (1 + z)) = a n * α * z + (b n + a n * α) by ring]
    simp
  have hlin : 1 + ξ * (α * (1 + z)) = -z := by rw [hα_def]; field_simp; ring
  rcases lt_or_ge z 0 with hz | hz
  · have hGz : standardWeibullCDF hα z ∈ Ioo 0 1 := by
      rw [standardWeibullCDF_apply_neg_eq hα hz]
      refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 ?_⟩
      have : 0 < Real.rpow (-z) α := Real.rpow_pos_of_pos (by linarith) _
      linarith
    refine ((tfae_ev_limit_relation (F := F) _ hGz).out 1 3).2 ?_
    rw [standardWeibullCDF_apply_neg_eq hα hz, Real.log_exp, neg_neg, Real.rpow_eq_pow]
    simp only [happ]
    refine hseq _ _ ?_
    rcases le_or_gt (-1) z with hz1 | hz1
    · have hx : 0 ≤ α * (1 + z) := mul_nonneg hα.le (by linarith)
      have := conv_pt hU hx
      rwa [gpdSurvival'_one_of_ne hξ', hlin, max_eq_left (by linarith), hαξ] at this
    · refine tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival hβ hU
        (Real.one_lt_rpow (by linarith) hα) ?_
      simp only [gpdSurvivalInv, hξ', ↓reduceIte]
      rw [← rpow_mul (by linarith), show α * -ξ = 1 by rw [hα_def]; field_simp, rpow_one,
        hα_def]
      field_simp
      ring
  · rw [standardWeibullCDF_apply_nonneg_eq hα hz]
    have hx : 0 ≤ α * (1 + z) := mul_nonneg hα.le (by linarith)
    have h0 := conv_pt hU hx
    rw [gpdSurvival'_one_of_ne hξ', hlin, max_eq_right (by linarith), hαξ,
      zero_rpow hα.ne'] at h0
    have hn := hseq _ _ h0
    simp only [happ]
    set p : ℕ → ℝ := fun n ↦ F (b n + a n * (α * (1 + z))) with hp
    have hlow : Tendsto (fun n : ℕ ↦ 1 - (n : ℝ) * (1 - p n)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hn
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n ↦ ?_)
      (fun n ↦ pow_le_one₀ (F.apply_nonneg _) (F.apply_le_one _))
    have h := one_add_mul_le_pow (a := p n - 1) (by linarith [F.apply_nonneg (b n +
      a n * (α * (1 + z)))]) n
    simp only [hp] at h ⊢
    rw [add_sub_cancel] at h
    linarith

/-- **Converse of the Pickands–Balkema–de Haan theorem** ([EKM, Theorem 3.4.13(b)],
[dHF, Theorem 1.1.6]): if for some scale function `β > 0` the rescaled conditional excess
survival function `x ↦ F̄ (u + β(u) x) / F̄ u` converges to `Ḡ_{ξ,1}` uniformly on `[0, ∞)` as
`u ↑ x_F`, then `F` is in the maximum domain of attraction of `H_ξ`. -/
theorem isInMDAGEV_of_tendstoUniformlyOn_excessSurvival
    (hβ : ∀ᶠ u in F.upperEndpointFilter, 0 < β u)
    (hU : TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
      (gpdSurvival' ξ 1) F.upperEndpointFilter (Ici 0)) :
    F.IsInMDAGEV ξ := by
  unfold IsInMDAGEV
  split_ifs with h1 h2
  · exact (F.isInMDAFrechet_iff _).2 (isRegularlyVarying_of_tendstoUniformlyOn_excessSurvival h1
      hβ hU)
  · exact isInMDAWeibull_of_tendstoUniformlyOn_excessSurvival h2 hβ hU
  · have h0 : ξ = 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    subst h0
    exact isInMDAGumbel_of_tendstoUniformlyOn_excessSurvival hβ hU

variable (F) in
/-- **Pickands–Balkema–de Haan theorem** ([EKM, Theorem 3.4.13(b)], [dHF, Theorem 1.1.6],
[Balkema–de Haan 1974], [Pickands 1975]): for every `ξ ∈ ℝ`, `F` is in the maximum domain of
attraction of `H_ξ` if and only if there is a scale function `β > 0` such that
`F̄ (u + β(u) x) / F̄ u → Ḡ_{ξ,1}(x)` uniformly in `x ≥ 0` as `u ↑ x_F`. -/
theorem isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ β : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < β u) ∧
      TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
        (gpdSurvival' ξ 1) F.upperEndpointFilter (Ici 0) :=
  ⟨F.exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV',
    fun ⟨_, hβ, hU⟩ ↦ isInMDAGEV_of_tendstoUniformlyOn_excessSurvival hβ hU⟩

variable (F) in
/-- **Pickands–Balkema–de Haan theorem**, supremum form: `F ∈ MDA(H_ξ)` if and only if there is
`β > 0` with `sup_{x ≥ 0} |F̄ (u + β(u) x) / F̄ u - Ḡ_{ξ,1}(x)| → 0` as `u ↑ x_F`. -/
theorem isInMDAGEV_iff_exists_tendsto_sup_excessSurvival (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ β : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < β u) ∧
      Tendsto (fun u ↦ ⨆ x ∈ Ici (0 : ℝ),
        |excessSurvival (fun y ↦ 1 - F y) u (β u * x) - gpdSurvival' ξ 1 x|)
        F.upperEndpointFilter (𝓝 0) := by
  rw [F.isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival ξ]
  refine exists_congr fun β ↦ and_congr_right fun hβ ↦ (tendsto_iSup_abs_sub_iff (B := 1) ?_).symm
  filter_upwards [hβ] with u hu x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have h1 : 0 ≤ excessSurvival (fun y ↦ 1 - F y) u (β u * x) :=
    div_nonneg (F.conv_nonneg _) (F.conv_nonneg _)
  have h2 : excessSurvival (fun y ↦ 1 - F y) u (β u * x) ≤ 1 :=
    div_le_one_of_le₀ (F.conv_antitone (le_add_of_nonneg_right (mul_nonneg hu.le hx')))
      (F.conv_nonneg _)
  have h3 := gpdSurvival'_nonneg ξ 1 x
  have h4 := gpdSurvival'_le_one (ξ := ξ) one_pos hx'
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

end Main


end CumulativeDistributionFunction
