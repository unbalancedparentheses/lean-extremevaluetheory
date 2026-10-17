/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Karamata
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Peaks over threshold: the Pickands–Balkema–de Haan theorem in the Fréchet case

The *generalized Pareto distribution* (GPD) with shape `ξ ≥ 0` and scale `β > 0` has survival
function `Ḡ_{ξ,β}(x) = (1 + ξ x / β) ^ (-1/ξ)` for `ξ > 0` and `Ḡ_{0,β}(x) = exp (-x / β)`,
for `x ≥ 0`.

The Pickands–Balkema–de Haan theorem (Balkema and de Haan, *Residual life time at great age*,
Ann. Probab. 2 (1974); Pickands, *Statistical inference using extreme order statistics*,
Ann. Statist. 3 (1975)) says that, for distributions in a maximum domain of attraction, the
conditional excess distribution over a high threshold `u` is, after rescaling by a suitable
`β(u)`, uniformly close to a GPD. We prove the heavy-tailed (Fréchet) case: if the survival
function `F̄` is regularly varying with index `-α`, `α > 0`, then with `β(u) = u / α`,

  `sup_{x ≥ 0} |F̄ (u + β(u) x) / F̄ u - Ḡ_{1/α,1}(x)| → 0` as `u → ∞`.

See Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events* (Springer, 1997),
Theorem 3.4.13, and McNeil, Frey and Embrechts, *Quantitative Risk Management* (Princeton
University Press, 2005), §5.2.

We also derive the asymptotics of the mean excess function, `e(u) / u → 1 / (α - 1)` for
`α > 1`, from Karamata's theorem.

## Main definitions

* `ExtremeValueTheory.gpdSurvival ξ β x`: the GPD survival function.
* `ExtremeValueTheory.excessSurvival F u x = F (u + x) / F u`: the conditional excess survival
  function `P(X - u > x | X > u)` when `F x = P(X > x)`.
* `ExtremeValueTheory.meanExcess F u = (∫ t in Ioi u, F t) / F u`: the mean excess function
  `E[X - u | X > u]`.

## Main results

* `gpdSurvival_zero`, `gpdSurvival_pos`, `gpdSurvival_le_one`, `gpdSurvival_antitoneOn`,
  `gpdSurvival_tendsto_atTop`, `gpdSurvival_continuousOn`: basic properties of the GPD.
* `IsRegularlyVarying.tendsto_excessSurvival`: pointwise convergence of the rescaled excess
  survival function to the GPD.
* `IsRegularlyVarying.tendstoUniformlyOn_excessSurvival`: the Pickands–Balkema–de Haan theorem
  (Fréchet case), uniform convergence on `[0, ∞)`.
* `IsRegularlyVarying.tendsto_sup_excessSurvival`: the same statement phrased with the
  supremum of the error.
* `IsRegularlyVarying.tendsto_meanExcess_div`: `e(u) / u → 1 / (α - 1)`.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

/-- The survival function of the generalized Pareto distribution with shape `ξ` and scale `β`:
`(1 + ξ x / β) ^ (-(1 / ξ))` if `ξ ≠ 0` and `exp (-x / β)` if `ξ = 0`. It is meant to be used
for `ξ ≥ 0`, `β > 0`, `x ≥ 0`. -/
noncomputable def gpdSurvival (ξ β x : ℝ) : ℝ :=
  if ξ = 0 then exp (-x / β) else (1 + ξ * x / β) ^ (-(1 / ξ))

section GPD

variable {ξ β x : ℝ}

theorem gpdSurvival_of_eq_zero (β x : ℝ) : gpdSurvival 0 β x = exp (-x / β) := by
  simp [gpdSurvival]

theorem gpdSurvival_of_ne_zero (hξ : ξ ≠ 0) (β x : ℝ) :
    gpdSurvival ξ β x = (1 + ξ * x / β) ^ (-(1 / ξ)) := by
  simp [gpdSurvival, hξ]

@[simp] theorem gpdSurvival_zero (ξ β : ℝ) : gpdSurvival ξ β 0 = 1 := by
  by_cases hξ : ξ = 0 <;> simp [gpdSurvival, hξ]

private theorem one_add_pos (hξ : 0 ≤ ξ) (hβ : 0 < β) (hx : 0 ≤ x) : 0 < 1 + ξ * x / β := by
  have : 0 ≤ ξ * x / β := by positivity
  linarith

theorem gpdSurvival_pos (hξ : 0 ≤ ξ) (hβ : 0 < β) (hx : 0 ≤ x) : 0 < gpdSurvival ξ β x := by
  unfold gpdSurvival
  split_ifs
  · exact exp_pos _
  · exact rpow_pos_of_pos (one_add_pos hξ hβ hx) _

/-- The GPD survival function is antitone on `[0, ∞)`. -/
theorem gpdSurvival_antitoneOn (hξ : 0 ≤ ξ) (hβ : 0 < β) :
    AntitoneOn (gpdSurvival ξ β) (Ici 0) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  unfold gpdSurvival
  split_ifs with h
  · exact exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hβ.le)
  · have hξ' : 0 < ξ := lt_of_le_of_ne hξ (Ne.symm h)
    refine rpow_le_rpow_of_nonpos (one_add_pos hξ hβ hx) ?_ (by
      have : 0 < 1 / ξ := by positivity
      linarith)
    have : ξ * x / β ≤ ξ * y / β :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hξ) hβ.le
    linarith

theorem gpdSurvival_le_one (hξ : 0 ≤ ξ) (hβ : 0 < β) (hx : 0 ≤ x) : gpdSurvival ξ β x ≤ 1 := by
  simpa using gpdSurvival_antitoneOn hξ hβ (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx

/-- The GPD survival function tends to `0` at `+∞`. -/
theorem gpdSurvival_tendsto_atTop (hξ : 0 ≤ ξ) (hβ : 0 < β) :
    Tendsto (gpdSurvival ξ β) atTop (𝓝 0) := by
  unfold gpdSurvival
  split_ifs with h
  · have h1 : Tendsto (fun x : ℝ => x / β) atTop atTop := tendsto_id.atTop_div_const hβ
    refine (tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun x => ?_
    simp [neg_div]
  · have hξ' : 0 < ξ := lt_of_le_of_ne hξ (Ne.symm h)
    have h1 : Tendsto (fun x : ℝ => 1 + ξ * x / β) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        ((tendsto_id.const_mul_atTop hξ').atTop_div_const hβ)
    exact (tendsto_rpow_neg_atTop (by positivity : 0 < 1 / ξ)).comp h1

/-- The GPD survival function is continuous on `[0, ∞)`. -/
theorem gpdSurvival_continuousOn (hξ : 0 ≤ ξ) (hβ : 0 < β) :
    ContinuousOn (gpdSurvival ξ β) (Ici 0) := by
  unfold gpdSurvival
  split_ifs with h
  · exact (continuous_exp.comp (continuous_neg.div_const β)).continuousOn
  · refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
    exact (one_add_pos hξ hβ hx).ne'

/-- For `α ≠ 0`, `Ḡ_{1/α,1}(x) = (1 + x / α) ^ (-α)`. -/
theorem gpdSurvival_inv_one {α : ℝ} (hα : α ≠ 0) (x : ℝ) :
    gpdSurvival (1 / α) 1 x = (1 + x / α) ^ (-α) := by
  rw [gpdSurvival_of_ne_zero (by simpa using hα), one_div_one_div]
  congr 2
  field_simp

end GPD

/-- The conditional excess survival function `F̄_u(x) = F̄ (u + x) / F̄ u`; if `F̄ x = P(X > x)`,
this is `P(X - u > x | X > u)`. -/
noncomputable def excessSurvival (F : ℝ → ℝ) (u x : ℝ) : ℝ := F (u + x) / F u

/-- The mean excess function `e(u) = (∫ t in Ioi u, F̄ t) / F̄ u`; if `F̄ x = P(X > x)` with
`E[X⁺] < ∞`, this is `E[X - u | X > u]`. -/
noncomputable def meanExcess (F : ℝ → ℝ) (u : ℝ) : ℝ := (∫ t in Ioi u, F t) / F u

namespace IsRegularlyVarying

variable {F : ℝ → ℝ} {α : ℝ}

private theorem excess_eq (hα : 0 < α) (u x : ℝ) :
    excessSurvival F u (u / α * x) = F ((1 + x / α) * u) / F u := by
  unfold excessSurvival
  congr 2
  field_simp

/-- **Pickands–Balkema–de Haan**, pointwise form (Fréchet case): if `F` is regularly varying
with index `-α`, `α > 0`, then with `β(u) = u / α`,
`F (u + β(u) x) / F u → Ḡ_{1/α,1}(x)` for each `x ≥ 0`. -/
theorem tendsto_excessSurvival (hRV : IsRegularlyVarying F (-α)) (hα : 0 < α) {x : ℝ}
    (hx : 0 ≤ x) :
    Tendsto (fun u => excessSurvival F u (u / α * x)) atTop
      (𝓝 (gpdSurvival (1 / α) 1 x)) := by
  rw [gpdSurvival_inv_one hα.ne']
  simp_rw [excess_eq hα]
  exact hRV.2 _ (by have : 0 ≤ x / α := by positivity
                    linarith)

/-- **Pickands–Balkema–de Haan theorem** (Fréchet case; [EKM, Theorem 3.4.13]): if the survival
function `F` is antitone and regularly varying with index `-α`, `α > 0`, then with
`β(u) = u / α` the rescaled excess survival function `x ↦ F (u + β(u) x) / F u` converges to
the GPD survival function `Ḡ_{1/α,1}` uniformly on `[0, ∞)` as `u → ∞`. -/
theorem tendstoUniformlyOn_excessSurvival (hF : Antitone F) (hRV : IsRegularlyVarying F (-α))
    (hα : 0 < α) :
    TendstoUniformlyOn (fun u x => excessSurvival F u (u / α * x)) (gpdSurvival (1 / α) 1)
      atTop (Ici 0) := by
  have hξ : (0 : ℝ) ≤ 1 / α := by positivity
  have hFpos := pos_of_antitone hF hRV.1
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- choose `M` with `Ḡ(M) < ε / 2`
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((gpdSurvival_tendsto_atTop hξ one_pos).eventually_lt_const (half_pos hε))
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hGM : gpdSurvival (1 / α) 1 M' < ε / 2 := hM M' (le_max_left _ _)
  -- uniform convergence on the compact range `c ∈ [1, 1 + M' / α]`
  have hU := Metric.tendstoUniformlyOn_iff.1
    (hRV.tendstoUniformlyOn_Icc (a := 0) (Or.inr (hF.antitoneOn _)) (b₁ := 1)
      (b₂ := 1 + M' / α) one_pos) (ε / 2) (half_pos hε)
  filter_upwards [hU, eventually_gt_atTop 0] with u hu hu0
  intro x hx
  rw [mem_Ici] at hx
  have hc : ∀ y : ℝ, 0 ≤ y → y ≤ M' →
      dist ((1 + y / α) ^ (-α)) (excessSurvival F u (u / α * y)) < ε / 2 := by
    intro y hy0 hyM
    rw [excess_eq hα]
    refine hu _ ⟨?_, ?_⟩
    · have : 0 ≤ y / α := by positivity
      linarith
    · have : y / α ≤ M' / α := div_le_div_of_nonneg_right hyM hα.le
      linarith
  rcases le_total x M' with hxM | hxM
  · rw [gpdSurvival_inv_one hα.ne']
    exact (hc x hx hxM).trans (half_lt_self hε)
  · -- tail region: both quantities lie in `[0, ε)`
    have hG0 := gpdSurvival_pos hξ one_pos hx
    have hGx : gpdSurvival (1 / α) 1 x ≤ gpdSurvival (1 / α) 1 M' :=
      gpdSurvival_antitoneOn hξ one_pos (mem_Ici.2 hM'0) (mem_Ici.2 hx) hxM
    have hE0 : 0 ≤ excessSurvival F u (u / α * x) :=
      (div_pos (hFpos _) (hFpos _)).le
    have hEx : excessSurvival F u (u / α * x) ≤ excessSurvival F u (u / α * M') := by
      unfold excessSurvival
      refine div_le_div_of_nonneg_right (hF ?_) (hFpos u).le
      have : u / α * M' ≤ u / α * x := mul_le_mul_of_nonneg_left hxM (by positivity)
      linarith
    have hEM := hc M' hM'0 le_rfl
    rw [← gpdSurvival_inv_one hα.ne', Real.dist_eq, abs_lt] at hEM
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-- **Pickands–Balkema–de Haan theorem** (Fréchet case), supremum form:
`sup_{x ≥ 0} |F (u + β(u) x) / F u - Ḡ_{1/α,1}(x)| → 0` as `u → ∞`, with `β(u) = u / α`. -/
theorem tendsto_sup_excessSurvival (hF : Antitone F) (hRV : IsRegularlyVarying F (-α))
    (hα : 0 < α) :
    Tendsto (fun u => ⨆ x ∈ Ici (0 : ℝ),
        |excessSurvival F u (u / α * x) - gpdSurvival (1 / α) 1 x|) atTop (𝓝 0) := by
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_excessSurvival hF hRV hα)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hU (ε / 2) (half_pos hε)] with u hu
  have hb : ∀ x ∈ Ici (0 : ℝ),
      |excessSurvival F u (u / α * x) - gpdSurvival (1 / α) 1 x| ≤ ε / 2 := by
    intro x hx
    have := hu x hx
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hsup0 : 0 ≤ ⨆ x ∈ Ici (0 : ℝ),
      |excessSurvival F u (u / α * x) - gpdSurvival (1 / α) 1 x| :=
    Real.iSup_nonneg fun x => Real.iSup_nonneg fun _ => abs_nonneg _
  have hsup : (⨆ x ∈ Ici (0 : ℝ),
      |excessSurvival F u (u / α * x) - gpdSurvival (1 / α) 1 x|) ≤ ε / 2 := by
    refine Real.iSup_le (fun x => Real.iSup_le (fun hx => hb x hx) (half_pos hε).le)
      (half_pos hε).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup0]
  linarith

/-- **Mean excess function** of a regularly varying tail ([EKM, §3.4], [MFE, §5.2]): if `F` is
antitone and regularly varying with index `-α`, `α > 1`, then `e(u) / u → 1 / (α - 1)`. This
matches the mean `β(u) / (1 - ξ) = u / (α - 1)` of the limiting GPD with `ξ = 1 / α`,
`β(u) = u / α`. -/
theorem tendsto_meanExcess_div (hF : Antitone F) (hRV : IsRegularlyVarying F (-α))
    (hα : 1 < α) :
    Tendsto (fun u => meanExcess F u / u) atTop (𝓝 (1 / (α - 1))) := by
  refine (hRV.tendsto_integral_Ioi_div hF hα).congr fun u => ?_
  unfold meanExcess
  rw [div_div, mul_comm]

end IsRegularlyVarying

end ExtremeValueTheory
