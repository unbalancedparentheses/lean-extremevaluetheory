/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.AffineTransformation
import ExtremeValueTheory.RegularVariation.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw

/-!
# Bridge between the three representations of a law on `ℝ`

The library meets a probability law on `ℝ` in three forms:

* a measure `μ : Measure ℝ` with `[IsProbabilityMeasure μ]` (the canonical form of a *law*, as in
  Mathlib; `ProbabilityMeasure ℝ` is used only where the topology of convergence in distribution
  is needed);
* Mathlib's distribution function `ProbabilityTheory.cdf μ : StieltjesFunction ℝ` (the canonical
  form of a *distribution function of a law*);
* the library's `CumulativeDistributionFunction`, a Stieltjes function with limits `0` at `-∞` and
  `1` at `+∞`, on which the orientation-preserving affine maps act (`A • F`). It is the canonical
  form for the classical theory of maxima: types, Fisher–Tippett–Gnedenko, max-stability, domains
  of attraction, peaks over threshold.

This file is the single bridge between them; see `docs/DESIGN.md`, section "Representing laws".

## Main definitions and statements

* `CumulativeDistributionFunction.ofMeasure μ`: the distribution function of a measure on `ℝ`,
  bundled as a `CumulativeDistributionFunction`. Its underlying Stieltjes function is *literally*
  Mathlib's `cdf μ` (`toStieltjesFunction_ofMeasure`, `coe_ofMeasure`, both `rfl`). It needs no
  `IsProbabilityMeasure` instance, so `ofMeasure (P.map X)` always typechecks; its values are
  meaningful when `μ` is a probability measure (`ofMeasure_apply`).
* In the other direction `F.measure` (Mathlib's `StieltjesFunction.measure`) is the law of `F`;
  it is a probability measure (`CumulativeDistributionFunction.isProbabilityMeasure_measure_coe`).
* The round trips: `measure_ofMeasure : (ofMeasure μ).measure = μ`,
  `ofMeasure_measure : ofMeasure F.measure = F`, `cdf_measure : cdf F.measure = F`, and the
  resulting equivalence `equivMeasure` between c.d.f.s and probability measures.
* Evaluation: `measureReal_Iic`, `measureReal_Ioi`, `measureReal_Ioc`, `ofMeasure_apply`,
  `one_sub_ofMeasure_apply`.
* Random variables: `ofMeasure_map_apply`, `one_sub_ofMeasure_map_apply`,
  `eq_ofMeasure_map_iff`, `measure_eq_map_iff`, `hasLaw_measure_iff` translate between
  `F`, the law `P.map X`, `HasLaw X μ P` and the hypothesis `∀ x, F x = P.real {ω | X ω ≤ x}`
  used by several statistical theorems.
* `ProbabilityMeasure.cdf` (the library's map `ProbabilityMeasure ℝ → CumulativeDistributionFunction`
  used by the weak-convergence files) agrees with `ofMeasure` (`ProbabilityMeasure.cdf_eq_ofMeasure`).
* The affine action on c.d.f.s is the push-forward of laws: `measure_smul_eq_map`,
  `ofMeasure_map_affine`.
* Tails: `isRegularlyVarying_one_sub_iff` and `isRegularlyVarying_one_sub_ofMeasure_iff` move
  regular variation of `1 - F` to the tail `x ↦ μ.real (Ioi x)` of the law.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology ExtremeValueTheory

namespace CumulativeDistributionFunction

/-! ### From a measure to a c.d.f. -/

/-- The distribution function `x ↦ μ (-∞, x]` of a measure `μ` on `ℝ`, as a
`CumulativeDistributionFunction`. Its underlying Stieltjes function is Mathlib's `cdf μ`.

No `IsProbabilityMeasure` instance is required (Mathlib's `cdf μ` has the right limits for every
measure), so `ofMeasure (P.map X)` is always well formed; it is the distribution function of `μ`
when `μ` is a probability measure (`ofMeasure_apply`). -/
noncomputable def ofMeasure (μ : Measure ℝ) : CumulativeDistributionFunction where
  toStieltjesFunction := cdf μ
  tendsto_atTop := tendsto_cdf_atTop μ
  tendsto_atBot := tendsto_cdf_atBot μ

variable {μ ν : Measure ℝ} (F G : CumulativeDistributionFunction)

@[simp] lemma toStieltjesFunction_ofMeasure (μ : Measure ℝ) :
    (ofMeasure μ).toStieltjesFunction = cdf μ := rfl

@[simp] lemma coe_ofMeasure (μ : Measure ℝ) : ⇑(ofMeasure μ) = ⇑(cdf μ) := rfl

lemma ofMeasure_apply_eq_cdf (μ : Measure ℝ) (x : ℝ) : ofMeasure μ x = cdf μ x := rfl

/-- The value of the distribution function of a probability measure. -/
lemma ofMeasure_apply [IsProbabilityMeasure μ] (x : ℝ) : ofMeasure μ x = μ.real (Iic x) :=
  cdf_eq_real μ x

lemma ofReal_ofMeasure_apply [IsProbabilityMeasure μ] (x : ℝ) :
    ENNReal.ofReal (ofMeasure μ x) = μ (Iic x) :=
  ofReal_cdf μ x

/-- The survival function of a probability measure: `1 - F(x) = μ (x, ∞)`. -/
lemma one_sub_ofMeasure_apply [IsProbabilityMeasure μ] (x : ℝ) :
    1 - ofMeasure μ x = μ.real (Ioi x) := by
  rw [ofMeasure_apply, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- The law of the c.d.f. of a probability measure is that measure. -/
@[simp] lemma measure_ofMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (ofMeasure μ).measure = μ :=
  ProbabilityTheory.measure_cdf μ

/-! ### From a c.d.f. to a measure -/

/-- Mathlib's `cdf` of the law of `F` is `F`. -/
@[simp] lemma cdf_measure : cdf F.measure = F.toStieltjesFunction :=
  cdf_measure_stieltjesFunction F.toStieltjesFunction F.tendsto_atBot F.tendsto_atTop

@[simp] lemma cdf_measure_apply (x : ℝ) : cdf F.measure x = F x := by
  rw [cdf_measure]

/-- The c.d.f. of the law of `F` is `F`. -/
@[simp] lemma ofMeasure_measure : ofMeasure F.measure = F := by
  ext x; exact F.cdf_measure_apply x

@[simp] lemma measureReal_Iic (x : ℝ) : F.measure.real (Iic x) = F x :=
  (F.apply_eq_measure_Iic x).symm

lemma measure_Iic (x : ℝ) : F.measure (Iic x) = ENNReal.ofReal (F x) := by
  rw [StieltjesFunction.measure_Iic _ F.tendsto_atBot, sub_zero]

lemma measure_Ioi (x : ℝ) : F.measure (Ioi x) = ENNReal.ofReal (1 - F x) := by
  rw [StieltjesFunction.measure_Ioi _ F.tendsto_atTop]

/-- The survival function of `F` is the tail of its law: `F.measure (x, ∞) = 1 - F x`. -/
@[simp] lemma measureReal_Ioi (x : ℝ) : F.measure.real (Ioi x) = 1 - F x := by
  rw [measureReal_def, measure_Ioi, ENNReal.toReal_ofReal (sub_nonneg.2 (F.apply_le_one x))]

lemma measureReal_Ioc {a b : ℝ} (hab : a ≤ b) : F.measure.real (Ioc a b) = F b - F a := by
  rw [measureReal_def, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono' hab))]

/-! ### Injectivity and the equivalence with probability measures -/

lemma measure_injective : Function.Injective (fun F : CumulativeDistributionFunction ↦ F.measure) :=
  fun F G h ↦ by simpa using congrArg ofMeasure h

lemma measure_inj : F.measure = G.measure ↔ F = G := measure_injective.eq_iff

lemma ofMeasure_inj [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ofMeasure μ = ofMeasure ν ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [← measure_ofMeasure μ, ← measure_ofMeasure ν, h]

/-- A c.d.f. is the c.d.f. of `μ` iff its law is `μ`. -/
lemma eq_ofMeasure_iff [IsProbabilityMeasure μ] : F = ofMeasure μ ↔ F.measure = μ := by
  rw [← measure_inj, measure_ofMeasure]

/-- C.d.f.s are in bijection with probability measures on `ℝ` (as measures with an
`IsProbabilityMeasure` proof). This is `equiv_probabilityMeasure` with `Measure ℝ` in place of
`ProbabilityMeasure ℝ`. -/
noncomputable def equivMeasure :
    CumulativeDistributionFunction ≃ {μ : Measure ℝ // IsProbabilityMeasure μ} where
  toFun F := ⟨F.measure, inferInstance⟩
  invFun μ := ofMeasure μ.1
  left_inv F := F.ofMeasure_measure
  right_inv μ := by
    obtain ⟨μ, hμ⟩ := μ
    exact Subtype.ext (measure_ofMeasure μ)

@[simp] lemma coe_probabilityMeasure : (F.probabilityMeasure : Measure ℝ) = F.measure := rfl

/-- The library's `ProbabilityMeasure.cdf` is `ofMeasure` of the underlying measure. -/
lemma _root_.MeasureTheory.ProbabilityMeasure.cdf_eq_ofMeasure (μ : ProbabilityMeasure ℝ) :
    μ.cdf = ofMeasure μ := by
  rw [eq_ofMeasure_iff, ProbabilityMeasure.measure_cdf]

/-- The library's `ProbabilityMeasure.cdf` agrees with Mathlib's `cdf`. -/
lemma _root_.MeasureTheory.ProbabilityMeasure.coe_cdf_eq (μ : ProbabilityMeasure ℝ) :
    ⇑μ.cdf = ⇑(cdf (μ : Measure ℝ)) := by
  rw [μ.cdf_eq_ofMeasure]; rfl

@[simp] lemma probabilityMeasure_ofMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((ofMeasure μ).probabilityMeasure : Measure ℝ) = μ := measure_ofMeasure μ

/-! ### Random variables -/

section RandomVariable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

/-- The c.d.f. of the law of a random variable: `F_X(x) = P(X ≤ x)`. -/
lemma ofMeasure_map_apply (hX : AEMeasurable X P) (x : ℝ) :
    ofMeasure (P.map X) x = P.real {ω | X ω ≤ x} := by
  rw [ofMeasure_apply, map_measureReal_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

/-- The survival function of a random variable: `1 - F_X(x) = P(X > x)`. -/
lemma one_sub_ofMeasure_map_apply (hX : AEMeasurable X P) (x : ℝ) :
    1 - ofMeasure (P.map X) x = P.real {ω | x < X ω} := by
  rw [one_sub_ofMeasure_apply, map_measureReal_apply_of_aemeasurable hX measurableSet_Ioi]
  rfl

/-- `F` is the c.d.f. of `X` iff `F x = P(X ≤ x)` for all `x`. The right-hand side is the
hypothesis `hF` of the statistical theorems stated with a `CumulativeDistributionFunction`
(note `P.real s` and `(P s).toReal` are definitionally equal). -/
lemma eq_ofMeasure_map_iff (hX : AEMeasurable X P) :
    F = ofMeasure (P.map X) ↔ ∀ x, F x = P.real {ω | X ω ≤ x} := by
  refine ⟨fun h x ↦ h ▸ ofMeasure_map_apply hX x, fun h ↦ ?_⟩
  ext x; rw [h x, ofMeasure_map_apply hX]

/-- The law of `F` is the law of `X` iff `F x = P(X ≤ x)` for all `x`. -/
lemma measure_eq_map_iff (hX : AEMeasurable X P) :
    F.measure = P.map X ↔ ∀ x, F x = P.real {ω | X ω ≤ x} := by
  rw [← eq_ofMeasure_iff, eq_ofMeasure_map_iff F hX]

/-- `X` has law `F.measure` iff `F` is its c.d.f. -/
lemma hasLaw_measure_iff (hX : AEMeasurable X P) :
    HasLaw X F.measure P ↔ ∀ x, F x = P.real {ω | X ω ≤ x} := by
  rw [← measure_eq_map_iff F hX]
  exact ⟨fun h ↦ h.map_eq.symm, fun h ↦ ⟨hX, h.symm⟩⟩

/-- If `X` has law `μ`, then `ofMeasure μ` is its c.d.f. -/
lemma _root_.ProbabilityTheory.HasLaw.ofMeasure_apply (h : HasLaw X μ P) (x : ℝ) :
    ofMeasure μ x = P.real {ω | X ω ≤ x} := by
  rw [← h.map_eq, ofMeasure_map_apply h.aemeasurable]

lemma _root_.ProbabilityTheory.HasLaw.one_sub_ofMeasure_apply (h : HasLaw X μ P) (x : ℝ) :
    1 - ofMeasure μ x = P.real {ω | x < X ω} := by
  rw [← h.map_eq, one_sub_ofMeasure_map_apply h.aemeasurable]

/-- From the hypothesis `∀ x, F x = P(X ≤ x)` to `F = ofMeasure (P.map X)`. -/
lemma eq_ofMeasure_map_of_forall (hX : AEMeasurable X P)
    (hF : ∀ x, F x = P.real {ω | X ω ≤ x}) : F = ofMeasure (P.map X) :=
  (eq_ofMeasure_map_iff F hX).2 hF

end RandomVariable

/-! ### The affine action is the push-forward of laws -/

/-- The law of `A • F` is the image of the law of `F` under the affine map
`x ↦ a x + b`, `(a, b) = A.coefs`. -/
theorem measure_smul_eq_map (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    (A • F).measure = F.measure.map (fun x ↦ A.coefs.1 * x + A.coefs.2) := by
  have ha := A.coefs_fst_pos
  have hm : Measurable (fun x : ℝ ↦ A.coefs.1 * x + A.coefs.2) := by fun_prop
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply hm measurableSet_Iic,
    StieltjesFunction.measure_Iic _ (A • F).tendsto_atBot]
  have hpre : (fun x : ℝ ↦ A.coefs.1 * x + A.coefs.2) ⁻¹' Iic x =
      Iic (A.coefs.1⁻¹ * x + -A.coefs.1⁻¹ * A.coefs.2) := by
    ext y
    simp only [mem_preimage, mem_Iic]
    rw [show A.coefs.1⁻¹ * x + -A.coefs.1⁻¹ * A.coefs.2 = (x - A.coefs.2) / A.coefs.1 by
      field_simp; ring, le_div_iff₀ ha]
    constructor <;> intro h <;> linarith
  rw [hpre, StieltjesFunction.measure_Iic _ F.tendsto_atBot, sub_zero, sub_zero]
  congr 1
  change F (A⁻¹ x) = _
  simp

/-- The c.d.f. of the image of a probability measure under `x ↦ a x + b`, `(a, b) = A.coefs`,
is `A • ofMeasure μ`. -/
theorem ofMeasure_map_affine (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : AffineIncrEquiv) :
    ofMeasure (μ.map fun x ↦ A.coefs.1 * x + A.coefs.2) = A • ofMeasure μ := by
  symm
  rw [eq_ofMeasure_iff, measure_smul_eq_map, measure_ofMeasure]

/-! ### Regular variation of the tail -/

/-- Regular variation of `1 - F` is regular variation of the tail `x ↦ P(X > x)` of the law. -/
lemma isRegularlyVarying_one_sub_iff {ρ : ℝ} :
    IsRegularlyVarying (fun x ↦ 1 - F x) ρ ↔
      IsRegularlyVarying (fun x ↦ F.measure.real (Ioi x)) ρ := by
  simp only [measureReal_Ioi]

lemma isRegularlyVarying_one_sub_ofMeasure_iff [IsProbabilityMeasure μ] {ρ : ℝ} :
    IsRegularlyVarying (fun x ↦ 1 - ofMeasure μ x) ρ ↔
      IsRegularlyVarying (fun x ↦ μ.real (Ioi x)) ρ := by
  simp only [one_sub_ofMeasure_apply]

end CumulativeDistributionFunction
