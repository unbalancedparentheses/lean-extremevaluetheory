/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
Modified by Federico Carrone, 2026, from kkytola/ExtremeValueProject (commit f7c9a8ce260d):
ported to Lean/Mathlib v4.35.0 and renamed `ExtremeValueProject` to `ExtremeValueTheory`.
-/
import ExtremeValueTheory.AffineTransformation

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
  sorry

section rewriting_the_limit_condition

private def limitCondition (γ : ℝ) (φs : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ (φs n)^n) atTop (𝓝 γ)

variable (γ : ℝ) (φs : ℕ → ℝ)

lemma tendsto_of_limitcondition {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 (Real.log γ)) := by
  sorry

lemma limitCondition_iff_log {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 (Real.log γ)) := by
  sorry

lemma limitCondition_iff {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ n * (1 - φs n)) atTop (𝓝 (-Real.log γ)) := by
  sorry

lemma limitCondition_iff_inv {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ) :
    limitCondition γ φs
      ↔ Tendsto (fun n ↦ (n * (1 - φs n))⁻¹) atTop (𝓝 (-Real.log γ)⁻¹) := by
  sorry

private def limitCondition' {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) (φs : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ n * Real.log (φs n)) atTop (𝓝 (Real.log γ))

end rewriting_the_limit_condition

end ExtremeValueDistr

section three_evds

private noncomputable def standardGumbelAux (x : ℝ) := Real.exp (-Real.exp (-x))

noncomputable def standardGumbelCDF : CumulativeDistributionFunction where
  toFun := standardGumbelAux
  mono' := sorry -- **Issue #13**
  right_continuous' := sorry -- **Issue #13**
  tendsto_atTop := sorry -- **Issue #13**
  tendsto_atBot := sorry -- **Issue #13**

lemma standardGumbelCDF_apply_eq (x : ℝ) :
    standardGumbelCDF x = Real.exp (-Real.exp (-x)) :=
  rfl

noncomputable def standardFrechetAux (α : ℝ) (x : ℝ) :=
  if x ≤ 0 then 0 else Real.exp (-(Real.rpow x (-α)))

noncomputable def standardFrechetCDF {α : ℝ} (α_pos : 0 < α) : CumulativeDistributionFunction where
  toFun := standardFrechetAux α
  mono' := sorry
  right_continuous' := sorry
  tendsto_atTop := sorry
  tendsto_atBot := sorry

lemma standardFrechetCDF_apply_pos_eq {α x : ℝ} (α_pos : 0 < α) (hx : 0 < x) :
    standardFrechetCDF α_pos x = Real.exp (-(Real.rpow x (-α))) := by
  simp [standardFrechetCDF, standardFrechetAux, hx]

lemma standardFrechetCDF_apply_nonpos_eq {α x : ℝ} (α_pos : 0 < α) (hx : x ≤ 0) :
    standardFrechetCDF α_pos x = 0 := by
  simp [standardFrechetCDF, standardFrechetAux, hx]

noncomputable def standardWeibullAux (α : ℝ) (x : ℝ) :=
  if x < 0 then Real.exp (-(Real.rpow (-x) α)) else 1

noncomputable def standardWeibullCDF {α : ℝ} (α_pos : 0 < α) : CumulativeDistributionFunction where
  toFun := standardWeibullAux α
  mono' := sorry
  right_continuous' := sorry
  tendsto_atTop := sorry
  tendsto_atBot := sorry

lemma standardWeibullCDF_apply_nonneg_eq {α x : ℝ} (α_pos : 0 < α) (hx : 0 ≤ x) :
    standardWeibullCDF α_pos x = 1 := by
  simp [standardWeibullCDF, standardWeibullAux, hx]

lemma standardWeibullCDF_apply_neg_eq {α x : ℝ} (α_pos : 0 < α) (hx : x < 0) :
    standardWeibullCDF α_pos x = Real.exp (-(Real.rpow (-x) α)) := by
  simp [standardWeibullCDF, standardWeibullAux, hx]

lemma isExtremeValueDistr_standardGumbelCDF :
    standardGumbelCDF.IsExtremeValueDistr := by
  sorry -- **Issue #14**

lemma isExtremeValueDistr_standardFrechetCDF {ξ : ℝ} (ξ_pos : 0 < ξ) :
    (standardFrechetCDF ξ_pos).IsExtremeValueDistr := by
  sorry

lemma isExtremeValueDistr_standardWeibullCDF {ξ : ℝ} (ξ_pos : 0 < ξ) :
    (standardWeibullCDF ξ_pos).IsExtremeValueDistr := by
  sorry

end three_evds

end ExtremeValueDistribution
