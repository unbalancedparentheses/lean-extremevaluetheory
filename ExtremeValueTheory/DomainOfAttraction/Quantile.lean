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

/-- Extended regular variation only depends on the germ of the function at `+∞`. -/
theorem IsExtendedRegularlyVarying.congr {f g a : ℝ → ℝ} {γ : ℝ}
    (hf : IsExtendedRegularlyVarying f γ a) (hfg : f =ᶠ[atTop] g) :
    IsExtendedRegularlyVarying g γ a := by
  refine ⟨hf.1, fun x hx => (hf.2 x hx).congr' ?_⟩
  filter_upwards [hfg, (tendsto_id.const_mul_atTop hx).eventually hfg] with t h1 h2
  simp only [id] at h2
  rw [h1, h2]

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
  exact ha.isRegularlyVarying.of_tendsto_div (neg_pos.2 (inv_lt_zero.2 hγ)) h3'

end CumulativeDistributionFunction
