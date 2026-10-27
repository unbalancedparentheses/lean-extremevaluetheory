/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.AffineTransformation
import ExtremeValueTheory.RegularVariation.Basic
import ExtremeValueTheory.WeakConvergenceCDF
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

This file is the single bridge between them. The domains of attraction are transported to laws
and random variables in `ExtremeValueTheory/DomainOfAttraction/OfMeasure.lean`.

## Main definitions and statements

* `CumulativeDistributionFunction.ofStieltjes F hbot htop`: a Stieltjes function with limits `0`
  and `1`, bundled; its law is `F.measure` (`measure_ofStieltjes`, `rfl`).
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
* Evaluation: `measureReal_Iic`, `measureReal_Ioi`, `measureReal_Iio`, `measureReal_Ici`,
  `measureReal_Ioc`, `measureReal_Icc`, `measureReal_Ico`, `measureReal_Ioo`,
  `measureReal_singleton` (left limits `Function.leftLim F` appear for open right ends), and on
  the measure side `ofMeasure_apply`, `one_sub_ofMeasure_apply`, `ofMeasure_sub_ofMeasure`.
* Continuity points are the non-atoms: `continuousAt_iff_measureReal_singleton`,
  `continuousAt_ofMeasure_iff`.
* Weak convergence: `tendsto_ofMeasure_iff` (convergence in distribution of `μₙ` is convergence
  of `ofMeasure μₙ`), `tendsto_probabilityMeasure_iff` (the converse direction for c.d.f.s), and
  `tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto_cdf` (the portmanteau statement
  with Mathlib's `cdf`).
* Degeneracy: `isDegenerate_iff_exists_measure_eq_dirac`, `isDegenerate_ofMeasure_iff`,
  `ofMeasure_dirac`.
* Mathlib's `cdf` of a random variable: `ProbabilityTheory.cdf_map_apply`,
  `ProbabilityTheory.one_sub_cdf_map_apply`.
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

/-! ### From a Stieltjes function to a c.d.f. -/

/-- A Stieltjes function with limits `0` at `-∞` and `1` at `+∞`, bundled as a
`CumulativeDistributionFunction`. -/
def ofStieltjes (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) : CumulativeDistributionFunction where
  toStieltjesFunction := F
  tendsto_atTop := htop
  tendsto_atBot := hbot

section ofStieltjes

variable (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0)) (htop : Tendsto F atTop (𝓝 1))

@[simp] lemma toStieltjesFunction_ofStieltjes :
    (ofStieltjes F hbot htop).toStieltjesFunction = F := rfl

@[simp] lemma coe_ofStieltjes : ⇑(ofStieltjes F hbot htop) = ⇑F := rfl

/-- The law of `ofStieltjes F` is the Lebesgue–Stieltjes measure of `F`. -/
@[simp] lemma measure_ofStieltjes : (ofStieltjes F hbot htop).measure = F.measure := rfl

@[simp] lemma ofStieltjes_toStieltjesFunction (G : CumulativeDistributionFunction) :
    ofStieltjes G.toStieltjesFunction G.tendsto_atBot G.tendsto_atTop = G := rfl

end ofStieltjes

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

/-- Increments of the distribution function are the masses of half-open intervals. -/
lemma ofMeasure_sub_ofMeasure [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    ofMeasure μ b - ofMeasure μ a = μ.real (Ioc a b) := by
  have hset : Ioc a b = Iic b \ Iic a := by
    ext y; simp only [mem_Ioc, Set.mem_sdiff, mem_Iic, not_le]; exact and_comm
  rw [ofMeasure_apply, ofMeasure_apply, hset,
    measureReal_sdiff (Iic_subset_Iic.2 hab) measurableSet_Iic]

/-- `ofMeasure μ` is continuous at `x` iff `μ` has no atom at `x`. -/
lemma continuousAt_ofMeasure_iff [IsProbabilityMeasure μ] (x : ℝ) :
    ContinuousAt (ofMeasure μ) x ↔ μ {x} = 0 := by
  rw [(ofMeasure μ).continuousAt_iff]
  exact Iff.of_eq (congrArg (· {x} = 0) (ProbabilityTheory.measure_cdf μ))

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

lemma measureReal_Ioc_eq_sub (a b : ℝ) : F.measure.real (Ioc a b) = max (F b - F a) 0 := by
  rw [measureReal_def, StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal']

lemma leftLim_nonneg (x : ℝ) : 0 ≤ Function.leftLim F x :=
  (F.apply_nonneg (x - 1)).trans (F.mono'.le_leftLim (by linarith))

lemma leftLim_le (x : ℝ) : Function.leftLim F x ≤ F x := F.mono'.leftLim_le le_rfl

lemma measure_Iio (x : ℝ) : F.measure (Iio x) = ENNReal.ofReal (Function.leftLim F x) := by
  rw [StieltjesFunction.measure_Iio _ F.tendsto_atBot, sub_zero]

/-- The law of `(-∞, x)` is the left limit of `F` at `x`. -/
@[simp] lemma measureReal_Iio (x : ℝ) : F.measure.real (Iio x) = Function.leftLim F x := by
  rw [measureReal_def, measure_Iio, ENNReal.toReal_ofReal (F.leftLim_nonneg x)]

lemma measure_Ici (x : ℝ) : F.measure (Ici x) = ENNReal.ofReal (1 - Function.leftLim F x) := by
  rw [StieltjesFunction.measure_Ici _ F.tendsto_atTop]

@[simp] lemma measureReal_Ici (x : ℝ) : F.measure.real (Ici x) = 1 - Function.leftLim F x := by
  rw [measureReal_def, measure_Ici,
    ENNReal.toReal_ofReal (sub_nonneg.2 ((F.leftLim_le x).trans (F.apply_le_one x)))]

/-- The atom of the law of `F` at `x` is the jump of `F` at `x`. -/
@[simp] lemma measureReal_singleton (x : ℝ) :
    F.measure.real {x} = F x - Function.leftLim F x := by
  rw [measureReal_def, StieltjesFunction.measure_singleton,
    ENNReal.toReal_ofReal (sub_nonneg.2 (F.leftLim_le x))]

lemma measureReal_Icc {a b : ℝ} (hab : a ≤ b) :
    F.measure.real (Icc a b) = F b - Function.leftLim F a := by
  rw [measureReal_def, StieltjesFunction.measure_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.2 ((F.leftLim_le a).trans (F.mono' hab)))]

lemma measureReal_Ico {a b : ℝ} (hab : a ≤ b) :
    F.measure.real (Ico a b) = Function.leftLim F b - Function.leftLim F a := by
  rw [measureReal_def, StieltjesFunction.measure_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono'.leftLim hab))]

lemma measureReal_Ioo {a b : ℝ} (hab : a < b) :
    F.measure.real (Ioo a b) = Function.leftLim F b - F a := by
  rw [measureReal_def, StieltjesFunction.measure_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono'.le_leftLim hab))]

/-- `F` is continuous at `x` iff the law of `F` has no atom at `x`. -/
lemma continuousAt_iff_measureReal_singleton (x : ℝ) :
    ContinuousAt F x ↔ F.measure.real {x} = 0 := by
  rw [F.continuousAt_iff, measureReal_def, ENNReal.toReal_eq_zero_iff]
  simp

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

/-! ### Weak convergence

Convergence in distribution of probability measures on `ℝ` is convergence of their c.d.f.s, in
each of the three representations. -/

/-- `ProbabilityMeasure ℝ ≃ₜ CumulativeDistributionFunction` sends `μ` to `ofMeasure μ`. -/
lemma homeomorph_probabilityMeasure_symm_apply (μ : ProbabilityMeasure ℝ) :
    homeomorph_probabilityMeasure.symm μ = ofMeasure μ := by
  rw [← μ.cdf_eq_ofMeasure, Homeomorph.symm_apply_eq, homeomorph_probabilityMeasure_apply_eq,
    ProbabilityMeasure.cdf_probabilityMeasure_eq_self]

/-- Convergence in distribution is convergence of the c.d.f.s `ofMeasure μₙ` (in the topology of
`CumulativeDistributionFunction`). -/
lemma tendsto_ofMeasure_iff {ι : Type*} {L : Filter ι} {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} :
    Tendsto (fun i ↦ ofMeasure (μs i)) L (𝓝 (ofMeasure μ)) ↔ Tendsto μs L (𝓝 μ) := by
  simp_rw [← homeomorph_probabilityMeasure_symm_apply]
  exact homeomorph_probabilityMeasure.symm.isInducing.tendsto_nhds_iff.symm

/-- Convergence of c.d.f.s is convergence in distribution of their laws. -/
lemma tendsto_probabilityMeasure_iff {ι : Type*} {L : Filter ι}
    {Fs : ι → CumulativeDistributionFunction} {G : CumulativeDistributionFunction} :
    Tendsto (fun i ↦ (Fs i).probabilityMeasure) L (𝓝 G.probabilityMeasure) ↔
      Tendsto Fs L (𝓝 G) := by
  simp_rw [← homeomorph_probabilityMeasure_apply_eq]
  exact homeomorph_probabilityMeasure.isInducing.tendsto_nhds_iff.symm

/-- **Convergence in distribution through Mathlib's `cdf`**: `μₙ → μ` in distribution iff
`cdf μₙ x → cdf μ x` at every continuity point `x` of `cdf μ`. -/
theorem tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto_cdf
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} :
    Tendsto μs atTop (𝓝 μ) ↔ ∀ x, ContinuousAt (cdf (μ : Measure ℝ)) x →
      Tendsto (fun n ↦ cdf (μs n : Measure ℝ) x) atTop (𝓝 (cdf (μ : Measure ℝ) x)) := by
  rw [← tendsto_ofMeasure_iff, tendsto_iff_forall_continuousAt_tendsto]
  rfl

/-! ### Degenerate laws -/

lemma ofMeasure_dirac (x₀ : ℝ) : ofMeasure (Measure.dirac x₀) = (diracProba x₀).cdf := by
  rw [(diracProba x₀).cdf_eq_ofMeasure]; rfl

/-- A c.d.f. is degenerate iff its law is a Dirac mass. -/
theorem isDegenerate_iff_exists_measure_eq_dirac :
    F.IsDegenerate ↔ ∃ x₀, F.measure = Measure.dirac x₀ := by
  constructor
  · intro h
    obtain ⟨x₀, hx₀⟩ := eq_diracProba_of_isDegenerate F.probabilityMeasure (by simpa using h)
    exact ⟨x₀, by rw [← coe_probabilityMeasure, hx₀]; rfl⟩
  · rintro ⟨x₀, hx₀⟩
    have : F = (diracProba x₀).cdf := by
      rw [← ofMeasure_dirac, eq_ofMeasure_iff, hx₀]
    exact this ▸ diracProba_is_degenerate x₀

/-- The c.d.f. of a probability measure is degenerate iff the measure is a Dirac mass. -/
theorem isDegenerate_ofMeasure_iff [IsProbabilityMeasure μ] :
    (ofMeasure μ).IsDegenerate ↔ ∃ x₀, μ = Measure.dirac x₀ := by
  rw [isDegenerate_iff_exists_measure_eq_dirac, measure_ofMeasure]

end CumulativeDistributionFunction

/-! ### Mathlib's `cdf` of a random variable -/

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

/-- Mathlib's `cdf` of the law of a random variable: `cdf (P.map X) x = P(X ≤ x)`. -/
lemma cdf_map_apply (hX : AEMeasurable X P) (x : ℝ) :
    cdf (P.map X) x = P.real {ω | X ω ≤ x} :=
  CumulativeDistributionFunction.ofMeasure_map_apply hX x

/-- The survival function through Mathlib's `cdf`: `1 - cdf (P.map X) x = P(X > x)`. -/
lemma one_sub_cdf_map_apply (hX : AEMeasurable X P) (x : ℝ) :
    1 - cdf (P.map X) x = P.real {ω | x < X ω} :=
  CumulativeDistributionFunction.one_sub_ofMeasure_map_apply hX x

end ProbabilityTheory
