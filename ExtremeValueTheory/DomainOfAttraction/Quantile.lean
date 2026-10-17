/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Extended
import ExtremeValueTheory.PeaksOverThreshold.Converse

/-!
# The quantile form of the domain of attraction condition

For a distribution function `F` let `U(t) = F^←(1 - 1/t) = inf {y | F̄ y ≤ 1/t}` be its tail
quantile function. By de Haan's theorem ([dHF, Theorem 1.1.6]), `F ∈ MDA(H_γ)` if and only if
`U` is extended regularly varying with index `γ`: there is `a > 0` with

  `(U(t x) - U(t)) / a(t) → (x ^ γ - 1) / γ`   (`log x` if `γ = 0`)

for every `x > 0`. Here we prove the direction `F ∈ MDA(H_γ) ⇒ U ∈ ERV_γ`.

## Main results

* `CumulativeDistributionFunction.tailQuantile`: the tail quantile function `U`.
* `CumulativeDistributionFunction.isExtendedRegularlyVarying_tailQuantile`: **the quantile form
  of the domain of attraction condition** ([dHF, Theorem 1.1.6]): if `F ∈ MDA(H_γ)` then `U` is
  extended regularly varying with index `γ`, with auxiliary function `a(t) = β(U(t))`, where `β`
  is the scale function of the Pickands–Balkema–de Haan theorem.
* `CumulativeDistributionFunction.isRegularlyVarying_tailQuantile_of_pos`: for `γ > 0`, `U` is
  regularly varying with index `γ` and `a(t) ~ γ U(t)`.
* `CumulativeDistributionFunction.exists_isRegularlyVarying_tailQuantile_of_neg`: for `γ < 0`,
  `U(∞) = lim U` is finite and `U(∞) - U` is regularly varying with index `γ`.

## Proof

Let `β` be the Pickands–Balkema–de Haan scale: `F̄ (u + β(u) x) / F̄ u → Ḡ_{γ,1}(x)` uniformly
in `x ≥ 0` as `u ↑ x_F`. For `x > 1` let `z(t) = (U(t x) - U(t)) / β(U(t)) ≥ 0`. Since `F` has no
relative jumps at its quantiles (`tendsto_quantile_of_tendstoUniformlyOn_excessSurvival`),
`F̄ (U(s)) ~ 1/s`, so `Ḡ(z(t)) ≈ F̄(U(t x)) / F̄(U(t)) → 1/x` by uniformity, and therefore
`z(t) → Λ_γ(1/x) = (x ^ γ - 1) / γ`. The case `x < 1` follows from the case `x > 1`
(`IsExtendedRegularlyVarying.of_one_lt`).

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.1.6 and Lemma 1.2.9 [dHF].
-/

open Filter Topology Set Real

namespace ExtremeValueTheory

theorem gpdSurvivalInv_inv {ξ x : ℝ} (hx : 0 < x) : gpdSurvivalInv ξ x⁻¹ = extRVLimit ξ x := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [gpdSurvivalInv, extRVLimit, Real.log_inv]
  · simp only [gpdSurvivalInv, extRVLimit, hξ, ↓reduceIte]
    rw [inv_rpow hx.le, rpow_neg hx.le, inv_inv]

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

variable (F : CumulativeDistributionFunction)

/-- The **tail quantile function** `U(t) = F^←(1 - 1/t) = inf {y | 1 - F y ≤ 1/t}` (meaningful
for `t > 1`). -/
noncomputable def tailQuantile (t : ℝ) : ℝ :=
  sInf {y | 1 - F y ≤ 1 / t}

/-- The tail quantile function is monotone on `(1, ∞)`. -/
theorem tailQuantile_mono {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    F.tailQuantile s ≤ F.tailQuantile t := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  obtain ⟨y₁, hy₁⟩ := (F.tendsto_atTop.eventually
    (lt_mem_nhds (show 1 - 1 / t < 1 by have := one_div_pos.2 ht0; linarith))).exists
  obtain ⟨y₀, hy₀⟩ := (F.tendsto_atBot.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 - 1 / s by
      rw [sub_pos, div_lt_one hs0]; exact hs))).exists
  refine csInf_le_csInf ⟨y₀, fun y hy => ?_⟩ ⟨y₁, ?_⟩ fun y hy => ?_
  · by_contra hcon
    have := F.mono' (not_le.1 hcon).le
    simp only [mem_ofPred_eq] at hy
    change F y ≤ F y₀ at this
    linarith
  · simp only [mem_ofPred_eq]
    linarith
  · simp only [mem_ofPred_eq] at hy ⊢
    exact hy.trans (one_div_le_one_div_of_le hs0 hst)

/-- **The quantile form of the domain of attraction condition** ([dHF, Theorem 1.1.6]): if `F`
is in the maximum domain of attraction of `H_γ`, `γ ∈ ℝ`, then the tail quantile function
`U(t) = F^←(1 - 1/t)` is extended regularly varying with index `γ`:
`(U(t x) - U(t)) / a(t) → (x ^ γ - 1) / γ` for every `x > 0`, for some `a > 0`. -/
theorem isExtendedRegularlyVarying_tailQuantile {γ : ℝ} (hF : F.IsInMDAGEV γ) :
    ∃ a : ℝ → ℝ, IsExtendedRegularlyVarying F.tailQuantile γ a := by
  obtain ⟨β, hβ, hU⟩ := F.exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV' hF
  set U := F.tailQuantile with hU_def
  have hlam : ∀ c : ℝ, 0 < c → Tendsto (fun t : ℝ => 1 / (c * t)) atTop (𝓝[>] 0) := by
    intro c hc
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hc)
    · filter_upwards [eventually_gt_atTop 0] with t ht
      show 0 < 1 / (c * t)
      positivity
  have hq : ∀ c : ℝ, 0 < c → _ := fun c hc =>
    tendsto_quantile_of_tendstoUniformlyOn_excessSurvival hβ hU (hlam c hc)
  obtain ⟨hU1, hJ1, hsp1⟩ := hq 1 one_pos
  simp only [one_mul] at hU1 hJ1 hsp1
  have hUlim : Tendsto U atTop F.upperEndpointFilter := hU1
  obtain ⟨y₀, hy₀⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds one_pos)).exists
  refine ⟨fun t => β (U t), IsExtendedRegularlyVarying.of_one_lt (hUlim.eventually hβ)
    fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  obtain ⟨hUx, hJx, hspx⟩ := hq x hx0
  have hUxlim : Tendsto (fun t => U (x * t)) atTop F.upperEndpointFilter := hUx
  -- `z t = (U (x t) - U t) / β (U t) ≥ 0`
  set z : ℝ → ℝ := fun t => (U (x * t) - U t) / β (U t) with hz_def
  have hev : ∀ᶠ t in atTop, 0 < t ∧ 0 < β (U t) ∧ U t ≤ U (x * t) ∧ 0 < 1 - F (U t) := by
    filter_upwards [eventually_gt_atTop 0, hUlim.eventually hβ, hsp1 y₀ hy₀, hspx y₀ hy₀]
      with t h0 h1 h2 h3
    refine ⟨h0, h1, ?_, h2.2.2.2.1⟩
    by_contra hcon
    have h4 := h2.2.2.1 _ (not_le.1 hcon)
    have h5 := h3.2.1
    have : 1 / (x * t) < 1 / t := one_div_lt_one_div_of_lt h0 (by nlinarith)
    change 1 / t < 1 - F (U (x * t)) at h4
    change 1 - F (U (x * t)) ≤ 1 / (x * t) at h5
    linarith
  have hz0 : ∀ᶠ t in atTop, z t ∈ Ici 0 := by
    filter_upwards [hev] with t ht
    exact div_nonneg (sub_nonneg.2 ht.2.2.1) ht.2.1.le
  -- `F̄ (U (x t)) / F̄ (U t) → 1 / x`
  have hratio : Tendsto (fun t => (1 - F (U (x * t))) / (1 - F (U t))) atTop (𝓝 x⁻¹) := by
    have := (hJx.div hJ1 one_ne_zero).mul_const x⁻¹
    rw [div_one, one_mul] at this
    refine this.congr' ?_
    filter_upwards [hev] with t ht
    obtain ⟨h0, -, -, h3⟩ := ht
    change (1 - F (U (x * t))) / (1 / (x * t)) / ((1 - F (U t)) / (1 / t)) * x⁻¹ = _
    field_simp
  have hGz : Tendsto (fun t => gpdSurvival' γ 1 (z t)) atTop (𝓝 x⁻¹) := by
    have := hratio.sub (hU.tendsto_sub_comp hUlim hz0)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hev] with t ht
    have h1 := ht.2.1.ne'
    simp only [excessSurvival, hz_def]
    rw [show U t + β (U t) * ((U (x * t) - U t) / β (U t)) = U (x * t) by field_simp; ring]
    ring
  have hxi : 0 < x⁻¹ := inv_pos.2 hx0
  rw [← gpdSurvivalInv_inv hx0]
  refine ((continuousAt_gpdSurvivalInv hxi).tendsto.comp hGz).congr' ?_
  filter_upwards [hGz.eventually (lt_mem_nhds hxi)] with t ht
  exact gpdSurvivalInv_gpdSurvival' ht

/-- The tail quantile function, made globally monotone: `U(max t 2)`. -/
private lemma monotone_tailQuantile_max : Monotone fun t => F.tailQuantile (max t 2) :=
  fun _ _ h => F.tailQuantile_mono (one_lt_two.trans_le (le_max_right _ _)) (max_le_max h le_rfl)

private lemma tailQuantile_max_eventuallyEq :
    (fun t => F.tailQuantile (max t 2)) =ᶠ[atTop] F.tailQuantile := by
  filter_upwards [eventually_ge_atTop 2] with t ht
  rw [max_eq_left ht]

/-- **Positive index** ([dHF, Theorem 1.1.6 and Lemma 1.2.9]): if `F ∈ MDA(H_γ)` with `γ > 0`,
then `U` is regularly varying with index `γ`, and there is an auxiliary function `a` for the
extended regular variation of `U` with `a(t) / U(t) → γ`. -/
theorem isRegularlyVarying_tailQuantile_of_pos {γ : ℝ} (hF : F.IsInMDAGEV γ) (hγ : 0 < γ) :
    ∃ a : ℝ → ℝ, IsExtendedRegularlyVarying F.tailQuantile γ a ∧
      IsRegularlyVarying F.tailQuantile γ ∧
      Tendsto (fun t => a t / F.tailQuantile t) atTop (𝓝 γ) := by
  obtain ⟨a, ha⟩ := F.isExtendedRegularlyVarying_tailQuantile hF
  have hg := ha.congr (F.tailQuantile_max_eventuallyEq).symm
  refine ⟨a, ha, (hg.isRegularlyVarying_of_pos F.monotone_tailQuantile_max hγ).congr
    F.tailQuantile_max_eventuallyEq, ?_⟩
  refine (hg.tendsto_aux_div_of_pos F.monotone_tailQuantile_max hγ).congr' ?_
  filter_upwards [F.tailQuantile_max_eventuallyEq] with t ht
  rw [ht]

/-- **Negative index** ([dHF, Theorem 1.1.6 and Lemma 1.2.9]): if `F ∈ MDA(H_γ)` with `γ < 0`,
then `U(∞) = lim U` is finite and `U(∞) - U` is regularly varying with index `γ`; moreover
`(U(∞) - U(t)) / a(t) → -1 / γ`. -/
theorem exists_isRegularlyVarying_tailQuantile_of_neg {γ : ℝ} (hF : F.IsInMDAGEV γ)
    (hγ : γ < 0) :
    ∃ a : ℝ → ℝ, ∃ ℓ : ℝ, IsExtendedRegularlyVarying F.tailQuantile γ a ∧
      Tendsto F.tailQuantile atTop (𝓝 ℓ) ∧
      IsRegularlyVarying (fun t => ℓ - F.tailQuantile t) γ ∧
      Tendsto (fun t => (ℓ - F.tailQuantile t) / a t) atTop (𝓝 (-γ⁻¹)) := by
  obtain ⟨a, ha⟩ := F.isExtendedRegularlyVarying_tailQuantile hF
  have hg := ha.congr (F.tailQuantile_max_eventuallyEq).symm
  obtain ⟨ℓ, h1, -, h3⟩ := hg.exists_tendsto_of_neg F.monotone_tailQuantile_max hγ
  have he := F.tailQuantile_max_eventuallyEq
  have h3' : Tendsto (fun t => (ℓ - F.tailQuantile t) / a t) atTop (𝓝 (-γ⁻¹)) := by
    refine h3.congr' ?_
    filter_upwards [he] with t ht
    rw [ht]
  refine ⟨a, ℓ, ha, h1.congr' he, ?_, h3'⟩
  exact ha.isRegularlyVarying.of_tendsto_div h3' (neg_pos.2 (inv_lt_zero.2 hγ))

/-! ### The tail quantile function on the logarithmic scale -/

/-- The defining properties of the tail quantile: for `t > 1`, `F̄(U(t)) ≤ 1/t`, and
`F̄(y) > 1/t` for every `y < U(t)`. -/
theorem tailQuantile_spec {t : ℝ} (ht : 1 < t) :
    1 - F (F.tailQuantile t) ≤ 1 / t ∧ ∀ y < F.tailQuantile t, 1 / t < 1 - F y := by
  have ht0 : 0 < t := by linarith
  have hlt : 1 / t < 1 := (div_lt_one ht0).2 ht
  have hpos : 0 < 1 / t := one_div_pos.2 ht0
  obtain ⟨y₁, hy₁⟩ := (F.tendsto_atTop.eventually
    (lt_mem_nhds (show 1 - 1 / t < 1 by linarith))).exists
  obtain ⟨y₀, hy₀⟩ := (F.tendsto_atBot.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 - 1 / t by linarith))).exists
  exact Gumbel.quantile_spec (g := fun y => 1 - F y) (fun _ _ h => sub_le_sub_left (F.mono' h) 1)
    (fun x => continuousWithinAt_const.sub (F.right_continuous x)) ⟨y₁, by linarith⟩
    ⟨y₀, by linarith⟩

theorem le_tailQuantile {t y : ℝ} (ht : 1 < t) (hy : 1 / t < 1 - F y) : y ≤ F.tailQuantile t := by
  by_contra hcon
  have h1 := (F.tailQuantile_spec ht).1
  have h2 := F.mono' (not_le.1 hcon).le
  change F (F.tailQuantile t) ≤ F y at h2
  linarith

/-- **The logarithm of the tail quantile function** ([dHF, Lemma 3.5.1]): if `F ∈ MDA(H_γ)` and
the right endpoint `U(∞)` is positive, then `U` is eventually positive, `log U` is monotone on
some `[c, ∞)` and extended regularly varying with index `γ₋ = min γ 0` and auxiliary function
`a / U`, and `a(t) / U(t) → γ₊ = max γ 0`. -/
theorem exists_isExtendedRegularlyVarying_log_tailQuantile {γ : ℝ} (hF : F.IsInMDAGEV γ)
    (hxF : ∃ y, 0 < y ∧ F y < 1) :
    ∃ a : ℝ → ℝ, IsExtendedRegularlyVarying F.tailQuantile γ a ∧
      (∀ᶠ t in atTop, 0 < F.tailQuantile t) ∧
      (∃ c, MonotoneOn (fun t => Real.log (F.tailQuantile t)) (Ici c)) ∧
      IsExtendedRegularlyVarying (fun t => Real.log (F.tailQuantile t)) (min γ 0)
        (fun t => a t / F.tailQuantile t) ∧
      Tendsto (fun t => a t / F.tailQuantile t) atTop (𝓝 (max γ 0)) := by
  obtain ⟨a, ha⟩ := F.isExtendedRegularlyVarying_tailQuantile hF
  obtain ⟨y, hy0, hFy⟩ := hxF
  have hpos : ∀ᶠ t in atTop, 0 < F.tailQuantile t := by
    have h1 : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [h1.eventually (gt_mem_nhds (show 0 < 1 - F y by linarith)),
      eventually_gt_atTop 1] with t h2 h3
    exact hy0.trans_le (F.le_tailQuantile h3 h2)
  obtain ⟨T, hT⟩ := eventually_atTop.1 hpos
  have hmono : MonotoneOn (fun t => Real.log (F.tailQuantile t)) (Ici (max T 2)) := by
    intro s hs t _ hst
    have hs1 : 1 < s := lt_of_lt_of_le one_lt_two ((le_max_right _ _).trans hs)
    exact Real.log_le_log (hT s ((le_max_left _ _).trans hs)) (F.tailQuantile_mono hs1 hst)
  have hmono' : MonotoneOn F.tailQuantile (Ici 2) := fun s hs t _ hst =>
    F.tailQuantile_mono (one_lt_two.trans_le hs) hst
  refine ⟨a, ha, hpos, ⟨_, hmono⟩, ha.log hmono' hpos, ?_⟩
  rcases le_or_gt γ 0 with hγ | hγ
  · rw [max_eq_right hγ]
    exact ha.tendsto_aux_div_zero_of_nonpos hγ hpos
  · rw [max_eq_left hγ.le]
    have hg := ha.congr (F.tailQuantile_max_eventuallyEq).symm
    refine (hg.tendsto_aux_div_of_pos F.monotone_tailQuantile_max hγ).congr' ?_
    filter_upwards [F.tailQuantile_max_eventuallyEq] with t ht
    rw [ht]

/-- **Tail asymptotics on the logarithmic scale**: if `log U` is extended regularly varying with
index `ρ ≤ 0` and auxiliary function `q`, then for every `x`,
`t F̄(exp (log U(t) + q(t) x)) → Ḡ_{ρ,1}(x) = (1 + ρ x)₊ ^ (-1/ρ)` as `t → ∞`. -/
theorem tendsto_mul_one_sub_exp_log_tailQuantile {ρ : ℝ} (hρ : ρ ≤ 0) {q : ℝ → ℝ}
    (hV : IsExtendedRegularlyVarying (fun t => Real.log (F.tailQuantile t)) ρ q)
    (hU : ∀ᶠ t in atTop, 0 < F.tailQuantile t) (x : ℝ) :
    Tendsto (fun t => t * (1 - F (Real.exp (Real.log (F.tailQuantile t) + q t * x)))) atTop
      (𝓝 (gpdSurvival' ρ 1 x)) := by
  set U := F.tailQuantile with hU_def
  set L := gpdSurvival' ρ 1 x with hL_def
  have hL0 : 0 ≤ L := gpdSurvival'_nonneg _ _ _
  have hlim : ∀ v : ℝ, 0 < v → Tendsto (fun t => (Real.log (U (v⁻¹ * t)) - Real.log (U t)) / q t)
      atTop (𝓝 (gpdSurvivalInv ρ v)) := by
    intro v hv
    have := hV.2 v⁻¹ (inv_pos.2 hv)
    rwa [← gpdSurvivalInv_inv (inv_pos.2 hv), inv_inv] at this
  have hev : ∀ v : ℝ, 0 < v → ∀ᶠ t in atTop, 0 < t ∧ 0 < q t ∧ 0 < U (v⁻¹ * t) ∧ 1 < v⁻¹ * t := by
    intro v hv
    have hs := tendsto_id.const_mul_atTop (inv_pos.2 hv)
    filter_upwards [eventually_gt_atTop 0, hV.1, hs.eventually hU,
      hs.eventually (eventually_gt_atTop 1)] with t h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  have hup : ∀ v : ℝ, 0 < v → gpdSurvivalInv ρ v < x →
      ∀ᶠ t in atTop, t * (1 - F (Real.exp (Real.log (U t) + q t * x))) ≤ v := by
    intro v hv hvx
    filter_upwards [(hlim v hv).eventually (gt_mem_nhds hvx), hev v hv] with t h1 h2
    obtain ⟨h0, hq, hUy, hy1⟩ := h2
    rw [div_lt_iff₀ hq] at h1
    have hlt : U (v⁻¹ * t) ≤ Real.exp (Real.log (U t) + q t * x) := by
      rw [← Real.exp_log hUy]
      exact Real.exp_le_exp.2 (by linarith)
    have h3 := (F.tailQuantile_spec hy1).1
    have h4 : 1 - F (Real.exp (Real.log (U t) + q t * x)) ≤ 1 - F (U (v⁻¹ * t)) :=
      sub_le_sub_left (F.mono' hlt) 1
    have h5 : t * (1 / (v⁻¹ * t)) = v := by field_simp
    calc t * (1 - F (Real.exp (Real.log (U t) + q t * x))) ≤ t * (1 / (v⁻¹ * t)) :=
          mul_le_mul_of_nonneg_left (h4.trans h3) h0.le
      _ = v := h5
  have hlow : ∀ v : ℝ, 0 < v → x < gpdSurvivalInv ρ v →
      ∀ᶠ t in atTop, v < t * (1 - F (Real.exp (Real.log (U t) + q t * x))) := by
    intro v hv hvx
    filter_upwards [(hlim v hv).eventually (lt_mem_nhds hvx), hev v hv] with t h1 h2
    obtain ⟨h0, hq, hUy, hy1⟩ := h2
    rw [lt_div_iff₀ hq] at h1
    have hlt : Real.exp (Real.log (U t) + q t * x) < U (v⁻¹ * t) := by
      rw [← Real.exp_log hUy]
      exact Real.exp_lt_exp.2 (by linarith)
    have h3 := (F.tailQuantile_spec hy1).2 _ hlt
    have h5 : t * (1 / (v⁻¹ * t)) = v := by field_simp
    calc v = t * (1 / (v⁻¹ * t)) := h5.symm
      _ < t * (1 - F (Real.exp (Real.log (U t) + q t * x))) := mul_lt_mul_of_pos_left h3 h0
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- `b < L`
    rcases lt_or_ge b 0 with hb0 | hb0
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have h1 := F.apply_le_one (Real.exp (Real.log (U t) + q t * x))
      exact hb0.trans_le (mul_nonneg ht.le (by linarith))
    have hLpos : 0 < L := hb0.trans_lt hb
    set v := (b + L) / 2 with hv
    have hv0 : 0 < v := by rw [hv]; linarith
    have hvL : v < L := by rw [hv]; linarith
    have hbv : b < v := by rw [hv]; linarith
    have hΛ : gpdSurvivalInv ρ L = x := gpdSurvivalInv_gpdSurvival' hLpos
    have := gpdSurvivalInv_lt_gpdSurvivalInv (ξ := ρ) hv0 hvL
    filter_upwards [hlow v hv0 (by rw [← hΛ]; exact this)] with t ht
    exact hbv.trans ht
  · -- `b > L`
    rcases hL0.lt_or_eq with hLpos | hLzero
    · set v := (L + b) / 2 with hv
      have hv0 : 0 < v := by rw [hv]; linarith
      have hLv : L < v := by rw [hv]; linarith
      have hvb : v < b := by rw [hv]; linarith
      have hΛ : gpdSurvivalInv ρ L = x := gpdSurvivalInv_gpdSurvival' hLpos
      have := gpdSurvivalInv_lt_gpdSurvivalInv (ξ := ρ) hLpos hLv
      filter_upwards [hup v hv0 (by rw [← hΛ]; exact this)] with t ht
      exact ht.trans_lt hvb
    · -- `L = 0`: then `x > 0`
      have hb0 : 0 < b := hLzero ▸ hb
      set v := min (b / 2) (1 / 2) with hv
      have hv0 : 0 < v := lt_min (half_pos hb0) (by norm_num)
      have hvb : v < b := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hb0)
      have hv1 : v < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hΛ0 : 0 < gpdSurvivalInv ρ v := by
        have := gpdSurvivalInv_lt_gpdSurvivalInv (ξ := ρ) hv0 hv1
        rwa [gpdSurvivalInv_one] at this
      have hx : gpdSurvivalInv ρ v < x := by
        by_contra hcon
        push Not at hcon
        have hx0 : 0 ≤ x := by
          by_contra hx0
          push Not at hx0
          have : 0 < gpdSurvival' ρ 1 x := by
            rcases hρ.lt_or_eq with hρ' | hρ'
            · rw [gpdSurvival'_one_of_ne hρ'.ne]
              have : 0 < 1 + ρ * x := by nlinarith
              rw [max_eq_left this.le]
              exact rpow_pos_of_pos this _
            · subst hρ'
              simp [Real.exp_pos]
          rw [← hL_def] at this
          linarith
        have h1 := gpdSurvival'_antitoneOn (ξ := ρ) one_pos (mem_Ici.2 hx0)
          (mem_Ici.2 (hx0.trans hcon)) hcon
        rw [gpdSurvival'_gpdSurvivalInv hv0, ← hL_def, ← hLzero] at h1
        linarith
      filter_upwards [hup v hv0 hx] with t ht
      exact ht.trans_lt hvb

/-- **Potter-type domination on the logarithmic scale**: under the assumptions of
`tendsto_mul_one_sub_exp_log_tailQuantile`, if moreover `log U` is monotone on `[c, ∞)`, then
for every `r > 0` there are `C` and `T₀ > 1` with
`t F̄(exp (log U(t) + q(t) z)) ≤ C (1 + z) ^ (-r)` for all `t ≥ T₀` and `z ≥ 0`. -/
theorem exists_mul_one_sub_exp_log_tailQuantile_le {ρ : ℝ} (hρ : ρ ≤ 0) {q : ℝ → ℝ}
    (hV : IsExtendedRegularlyVarying (fun t => Real.log (F.tailQuantile t)) ρ q) {c : ℝ}
    (hmono : MonotoneOn (fun t => Real.log (F.tailQuantile t)) (Ici c))
    (hU : ∀ᶠ t in atTop, 0 < F.tailQuantile t) {r : ℝ} (hr : 0 < r) :
    ∃ C T₀ : ℝ, 1 < T₀ ∧ ∀ t ≥ T₀, 0 < q t ∧ 0 < F.tailQuantile t ∧ ∀ z : ℝ, 0 ≤ z →
      t * (1 - F (Real.exp (Real.log (F.tailQuantile t) + q t * z))) ≤ C * (1 + z) ^ (-r) := by
  set U := F.tailQuantile with hU_def
  obtain ⟨C₀, T₁, hT₁, hP⟩ := hV.exists_sub_le_of_nonpos hρ hmono (inv_pos.2 hr)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 (hV.1.and hU)
  set T₀ := max (max T₁ T₂) 2 with hT₀_def
  have hT₀1 : 1 < T₀ := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  set K := max C₀ 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  refine ⟨(1 + K) ^ r, T₀, hT₀1, fun t ht => ?_⟩
  have htT₁ : T₁ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT₂ : T₂ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht1 : 1 < t := hT₀1.trans_le ht
  have ht0 : 0 < t := by linarith
  obtain ⟨hq, hUt⟩ := hT₂ t htT₂
  refine ⟨hq, hUt, fun z hz => ?_⟩
  have hratio : ∀ w : ℝ, 0 ≤ w → w ≤ (1 + K) / (1 + z) → w ^ r ≤ (1 + K) ^ r * (1 + z) ^ (-r) := by
    intro w hw0 hw
    rw [rpow_neg (by linarith), ← div_eq_mul_inv, ← div_rpow (by linarith) (by linarith)]
    exact rpow_le_rpow hw0 hw hr.le
  rcases le_or_gt z K with hzK | hzK
  · -- `z ≤ K`: the bound `t F̄(U(t)) ≤ 1`
    have hle : U t ≤ Real.exp (Real.log (U t) + q t * z) := by
      have h0 := mul_nonneg hq.le hz
      have := Real.exp_le_exp.2 (show Real.log (U t) ≤ Real.log (U t) + q t * z by linarith)
      rwa [Real.exp_log hUt] at this
    have h1 : 1 - F (Real.exp (Real.log (U t) + q t * z)) ≤ 1 / t :=
      (sub_le_sub_left (F.mono' hle) 1).trans (F.tailQuantile_spec ht1).1
    have h2 : t * (1 - F (Real.exp (Real.log (U t) + q t * z))) ≤ 1 := by
      calc _ ≤ t * (1 / t) := mul_le_mul_of_nonneg_left h1 ht0.le
        _ = 1 := by field_simp
    refine h2.trans ?_
    have := hratio 1 zero_le_one (by rw [le_div_iff₀ (by linarith)]; linarith)
    rwa [one_rpow] at this
  · -- `z > K`: compare with `U(y t)`, `y = (z / K) ^ r`
    set y := (z / K) ^ r with hy
    have hzK' : 1 < z / K := by rw [lt_div_iff₀ hK0]; linarith
    have hy1 : 1 ≤ y := one_le_rpow hzK'.le hr.le
    have hyδ : y ^ r⁻¹ = z / K := by
      rw [hy, rpow_rpow_inv (by positivity) hr.ne']
    have hyt : 1 < y * t := by nlinarith
    have hUyt : 0 < U (y * t) := (hT₂ (y * t) (le_trans htT₂ (by nlinarith))).2
    have hP' := hP t htT₁ y hy1
    rw [hyδ] at hP'
    have hle : U (y * t) ≤ Real.exp (Real.log (U t) + q t * z) := by
      rw [← Real.exp_log hUyt]
      refine Real.exp_le_exp.2 ?_
      have : C₀ * q t * (z / K) ≤ q t * z := by
        have h1 : C₀ * (z / K) ≤ K * (z / K) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        rw [mul_div_cancel₀ _ hK0.ne'] at h1
        nlinarith
      linarith
    have h1 : 1 - F (Real.exp (Real.log (U t) + q t * z)) ≤ 1 / (y * t) :=
      (sub_le_sub_left (F.mono' hle) 1).trans (F.tailQuantile_spec hyt).1
    have h2 : t * (1 - F (Real.exp (Real.log (U t) + q t * z))) ≤ (K / z) ^ r := by
      calc _ ≤ t * (1 / (y * t)) := mul_le_mul_of_nonneg_left h1 ht0.le
        _ = y⁻¹ := by field_simp
        _ = (K / z) ^ r := by rw [hy, ← inv_rpow (by positivity), inv_div]
    refine h2.trans (hratio _ (by positivity) ?_)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

end CumulativeDistributionFunction
