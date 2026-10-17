/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.Frechet
import ExtremeValueTheory.DomainOfAttraction.Weibull
import ExtremeValueTheory.RegularVariation.KaramataConverse

/-!
# Von Mises conditions for the Fréchet and Weibull domains of attraction

We prove the von Mises sufficient conditions for the Fréchet and Weibull maximum domains of
attraction ([EKM, Corollaries 3.3.8 and 3.3.13], [dHF, Theorem 1.1.8]):

* `CumulativeDistributionFunction.isInMDAFrechet_of_vonMises`: if `F` is differentiable on
  `(z, ∞)` with derivative `F₁` and `x F₁(x) / (1 - F(x)) → α > 0` as `x → ∞`, then
  `F ∈ MDA(Φ_α)`.
* `CumulativeDistributionFunction.isInMDAWeibull_of_vonMises`: if `F` is differentiable on
  `(z, x_F)` with derivative `F₁` and `(x_F - x) F₁(x) / (1 - F(x)) → α > 0` as `x ↑ x_F`, then
  `F ∈ MDA(Ψ_α)`; moreover `x_F` is the right endpoint of `F`
  (`CumulativeDistributionFunction.isRegularlyVarying_of_vonMises_nhdsLT`).

Here [EKM] is Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events* (Springer, 1997)
and [dHF] is de Haan and Ferreira, *Extreme Value Theory: An Introduction* (Springer, 2006).

No positivity of the density is assumed: positivity of the tail `1 - F` near the endpoint is
forced by the convergence of the von Mises ratio to `α ≠ 0`.

## Proof

The tail `g = 1 - F` (resp. `g t = 1 - F (x_F - t⁻¹)`) is eventually positive and differentiable,
and the von Mises ratio is `-t g'(t) / g(t)`. By
`ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_deriv_div`, `g` is regularly varying with
index `-α`, and Gnedenko's theorem (`isInMDAFrechet_iff`, `isInMDAWeibull_iff`) concludes.

## Examples

* `CumulativeDistributionFunction.paretoCDF`: the Pareto distribution `1 - x ^ (-α)` on
  `[1, ∞)` is in `MDA(Φ_α)`.
* `CumulativeDistributionFunction.powerCDF`: the distribution `1 - (1 - x) ^ α` on `[0, 1]` (the
  uniform distribution for `α = 1`, the `Beta(1, α)` distribution in general) is in `MDA(Ψ_α)`.
-/

open Filter Topology Set

namespace CumulativeDistributionFunction

open ExtremeValueTheory

/-- If `F` is differentiable on `(z, ∞)` with derivative `F₁` and the von Mises ratio
`x F₁(x) / (1 - F(x))` tends to `α > 0` as `x → ∞`, then the tail `1 - F` is regularly varying
with index `-α`. -/
theorem isRegularlyVarying_of_vonMises (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) {z : ℝ} {F₁ : ℝ → ℝ} (h1 : ∀ x > z, HasDerivAt F (F₁ x) x)
    (hvm : Tendsto (fun x ↦ x * F₁ x / (1 - F x)) atTop (𝓝 α)) :
    IsRegularlyVarying (fun x ↦ 1 - F x) (-α) := by
  refine IsRegularlyVarying.of_tendsto_mul_deriv_div (g' := fun x ↦ -F₁ x) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop z] with x hx
    exact (h1 x hx).const_sub 1
  · filter_upwards [hvm.eventually (lt_mem_nhds hα)] with x hx
    have h0 : 0 ≤ 1 - F x := by linarith [F.apply_le_one x]
    refine lt_of_le_of_ne h0 fun h ↦ ?_
    rw [← h, div_zero] at hx
    exact lt_irrefl _ hx
  · refine hvm.neg.congr fun x ↦ ?_
    ring

/-- **The von Mises condition for the Fréchet domain of attraction** ([EKM, Corollary 3.3.8],
[dHF, Theorem 1.1.8 (1)]): if `F` is differentiable on `(z, ∞)` with derivative `F₁` and
`x F₁(x) / (1 - F(x)) → α > 0` as `x → ∞`, then `F` is in the maximum domain of attraction of
the Fréchet distribution `Φ_α`. -/
theorem isInMDAFrechet_of_vonMises (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) {z : ℝ} {F₁ : ℝ → ℝ} (h1 : ∀ x > z, HasDerivAt F (F₁ x) x)
    (hvm : Tendsto (fun x ↦ x * F₁ x / (1 - F x)) atTop (𝓝 α)) :
    F.IsInMDAFrechet hα :=
  (F.isInMDAFrechet_iff hα).2 (F.isRegularlyVarying_of_vonMises hα h1 hvm)

/-- If `F` is differentiable on `(z, x_F)` with derivative `F₁` and the von Mises ratio
`(x_F - x) F₁(x) / (1 - F(x))` tends to `α > 0` as `x ↑ x_F`, then `x_F` is the right endpoint
of `F` (`F x_F = 1` and `F x < 1` for `x < x_F`) and `t ↦ 1 - F (x_F - t⁻¹)` is regularly varying
with index `-α`. -/
theorem isRegularlyVarying_of_vonMises_nhdsLT (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) {z xF : ℝ} (hz : z < xF) {F₁ : ℝ → ℝ}
    (h1 : ∀ x ∈ Ioo z xF, HasDerivAt F (F₁ x) x)
    (hvm : Tendsto (fun x ↦ (xF - x) * F₁ x / (1 - F x)) (𝓝[<] xF) (𝓝 α)) :
    F xF = 1 ∧ (∀ x < xF, F x < 1) ∧ IsRegularlyVarying (fun t ↦ 1 - F (xF - t⁻¹)) (-α) := by
  -- `F < 1` to the left of `x_F`
  have hlt : ∀ x < xF, F x < 1 := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := ((hvm.eventually (lt_mem_nhds hα)).and
      (Ioo_mem_nhdsLT hx)).exists
    refine (F.mono' hxy.1.le).trans_lt ?_
    refine lt_of_le_of_ne (F.apply_le_one y) fun h ↦ ?_
    rw [h, sub_self, div_zero] at hy
    exact lt_irrefl _ hy
  -- the substitution `x = x_F - t⁻¹`
  have hs : Tendsto (fun t : ℝ ↦ xF - t⁻¹) atTop (𝓝[<] xF) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using tendsto_inv_atTop_zero.const_sub xF
    · filter_upwards [eventually_gt_atTop 0] with t ht
      exact sub_lt_self xF (inv_pos.2 ht)
  have hsz : ∀ᶠ t in atTop, xF - t⁻¹ ∈ Ioo z xF := hs.eventually (Ioo_mem_nhdsLT hz)
  have hRV : IsRegularlyVarying (fun t ↦ 1 - F (xF - t⁻¹)) (-α) := by
    refine IsRegularlyVarying.of_tendsto_mul_deriv_div
      (g' := fun t ↦ -(F₁ (xF - t⁻¹) * -(-(t ^ 2)⁻¹))) ?_ ?_ ?_
    · filter_upwards [hsz, eventually_gt_atTop 0] with t ht ht0
      exact ((h1 _ ht).comp t ((hasDerivAt_inv ht0.ne').const_sub xF)).const_sub 1
    · filter_upwards [eventually_gt_atTop 0] with t ht
      linarith [hlt (xF - t⁻¹) (sub_lt_self xF (inv_pos.2 ht))]
    · refine (hvm.comp hs).neg.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simp only [Function.comp_apply, sub_sub_cancel]
      field_simp
  refine ⟨?_, hlt, hRV⟩
  -- `x_F` carries no atom: the tail tends to `0`
  set G : ℝ → ℝ := fun t ↦ 1 - F (xF - (max t 1)⁻¹) with hG
  have hmax : ∀ t : ℝ, 0 < max t 1 := fun t ↦ lt_of_lt_of_le one_pos (le_max_right _ _)
  have hGa : Antitone G := fun s t hst ↦ sub_le_sub_left (F.mono' (sub_le_sub_left
    (inv_anti₀ (hmax s) (max_le_max hst le_rfl)) xF)) 1
  have hGpos : ∀ t, 0 < G t := fun t ↦ by
    have := hlt (xF - (max t 1)⁻¹) (sub_lt_self xF (inv_pos.2 (hmax t)))
    simp only [hG]
    linarith
  have hGRV : IsRegularlyVarying G (-α) := hRV.congr (by
    filter_upwards [eventually_ge_atTop 1] with t ht
    simp [hG, max_eq_left ht])
  have hG0 := Weibull.tendsto_zero_of_isRegularlyVarying hGa hGpos hα hGRV
  have hle : ∀ t, 1 - F xF ≤ G t := fun t ↦
    sub_le_sub_left (F.mono' (sub_le_self xF (inv_pos.2 (hmax t)).le)) 1
  have := ge_of_tendsto' hG0 hle
  linarith [F.apply_le_one xF]

/-- **The von Mises condition for the Weibull domain of attraction** ([EKM, Corollary 3.3.13],
[dHF, Theorem 1.1.8 (2)]): if `F` is differentiable on `(z, x_F)` with derivative `F₁` and
`(x_F - x) F₁(x) / (1 - F(x)) → α > 0` as `x ↑ x_F`, then `F` is in the maximum domain of
attraction of the Weibull distribution `Ψ_α`. -/
theorem isInMDAWeibull_of_vonMises (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) {z xF : ℝ} (hz : z < xF) {F₁ : ℝ → ℝ}
    (h1 : ∀ x ∈ Ioo z xF, HasDerivAt F (F₁ x) x)
    (hvm : Tendsto (fun x ↦ (xF - x) * F₁ x / (1 - F x)) (𝓝[<] xF) (𝓝 α)) :
    F.IsInMDAWeibull hα :=
  (F.isInMDAWeibull_iff hα).2 ⟨xF, F.isRegularlyVarying_of_vonMises_nhdsLT hα hz h1 hvm⟩

end CumulativeDistributionFunction
