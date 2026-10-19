/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TailProcess
import Mathlib.Topology.Algebra.Module.Cardinality
import ExtremeValueTheory.RegularVariation.Multivariate.Linear

/-!
# Multivariate regular variation

We formalize regular variation of random vectors with values in a normed space `E` (for instance
`ℝ × ℝ` or `EuclideanSpace ℝ (Fin d)`), following Resnick, *Heavy-Tail Phenomena* (Springer, 2007),
Chapter 6 [Res07]; Basrak, Davis and Mikosch, *A characterization of multivariate regular
variation*, Ann. Appl. Probab. 12 (2002) [BDM02]; Hult and Lindskog, *Regular variation for
measures on metric spaces*, Publ. Inst. Math. 80 (2006) [HL06]; and Kulik and Soulier,
*Heavy-Tailed Time Series* (Springer, 2020), Chapter 2 [KS20].

## The definition

`ℝ^d \ {0}` with its usual topology is not the right space for vague convergence (sets bounded
away from the origin are not relatively compact there), so we use the `M₀`-formulation of
[HL06], in the tail-normalized form of [KS20, §2.1]: `X` is regularly varying with index `α`
and exponent (tail) measure `μ` (`IsRegVarVector P X α μ`) if `P(‖X‖ > x)` is regularly varying
with index `-α`, `μ` has no atom at `0` and is finite on `{‖y‖ > r}` for every `r > 0`, and
`E[f(X / x)] / P(‖X‖ > x) → ∫ f dμ` for every bounded continuous `f` vanishing on a neighbourhood
of the origin. Normalizing by `P(‖X‖ > x)` instead of a sequence `aₙ` with `n P(‖X‖ > aₙ) → 1`
is equivalent and fixes the scale `μ {‖y‖ > 1} = 1`. The portmanteau theorem
(`IsRegVarVector.tendsto_measureReal`) recovers `P(X / x ∈ A) / P(‖X‖ > x) → μ(A)` for Borel `A`
bounded away from the origin with `μ(∂A) = 0`.

## Main results

* `ext_of_forall_integral_eq_of_vanishesNearZero`, `tendsto_measureReal_of_vanishesNearZero`,
  `tendsto_integral_indicator_of_vanishesNearZero`: uniqueness and portmanteau for convergence on
  sets bounded away from the origin.
* `IsRegVarVector.unique`: the exponent measure is unique.
* `IsRegVarVector.map_smul`, `IsRegVarVector.measure_smul_set`: homogeneity
  `μ(t • A) = t ^ (-α) μ(A)`; `IsRegVarVector.measure_lt_norm`: `μ {‖y‖ > u} = u ^ (-α)`;
  `IsRegVarVector.measure_norm_eq_zero`: spheres are null.
* `isRegVarVector_iff` (**polar decomposition**): `X` is regularly varying iff `P(‖X‖ > x)` is
  regularly varying and the law of `X / ‖X‖` given `‖X‖ > x` converges weakly
  (`IsRegVarVector.tendstoLawCond_spectralMeasure`, `isRegVarVector_polarMeasure`);
  `IsRegVarVector.eq_polarMeasure`: `μ = (α r ^ (-α - 1) dr) ⊗ S` in polar coordinates, with `S`
  the spectral measure on the unit sphere (`IsRegVarVector.ae_norm_spectralMeasure`).
* `IsRegVarVector.tendsto_linear`, `IsRegVarVector.tendsto_inner`,
  `IsRegVarVector.tendsto_linear_spectral` (**linear combinations**, the "⇒" half of the
  Cramér–Wold device of [BDM02]): `P(L X > x) / P(‖X‖ > x) → μ {L > 1} = ∫ (L θ)₊ ^ α dS(θ)`.
* Examples: `IsRegVarVector.measure_compl_eq_zero` (support in closed cones);
  `isRegVarVector_diag` and `IsRegVarVector.measure_offDiag_eq_zero` (full dependence:
  `X = (Z, Z)` has its exponent measure on the diagonal); `isRegVarVector_of_indepFun` and
  `IsRegVarVector.measure_ne_zero_ne_zero_eq_zero` (asymptotic independence: independent
  components give an exponent measure concentrated on the axes).

The converse Cramér–Wold device (regular variation of every `L X`, with a common normalization,
implies regular variation of `X` when `α` is not an integer [BDM02]; it fails for integer `α`) is
in `RegularVariation/CramerWold.lean` (uniqueness of the exponent measure given the half-space
values) and `RegularVariation/CramerWoldConverse.lean` (existence).

The polar decomposition reuses the single-vector Basrak–Segers machinery of
`Dependence/TailProcess.lean` (`tendstoLawCond_smul`, `tendstoLawCond_spectral_of_tendstoLawCond`).

## File layout

This file holds the final part of the development and imports the others:

* `ExtremeValueTheory.RegularVariation.Multivariate.Basic`: convergence on sets bounded away from
  the origin, the definition `IsRegVarVector`, uniqueness and homogeneity of the exponent measure.
* `ExtremeValueTheory.RegularVariation.Multivariate.Polar`: the spectral measure and the polar
  decomposition `μ = (α r ^ (-α - 1) dr) ⊗ S`.
* `ExtremeValueTheory.RegularVariation.Multivariate.Linear`: linear combinations (the "⇒" half of
  the Cramér–Wold device), support in closed cones and the fully dependent example `X = (Z, Z)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal Pointwise

namespace ExtremeValueTheory

section Independent

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {α : ℝ}

omit [IsProbabilityMeasure P] in
theorem measureReal_lt_inter_lt_eq_mul {U V : Ω → ℝ} (hind : IndepFun U V P) (a b : ℝ) :
    P.real ({ω | a < U ω} ∩ {ω | b < V ω}) = P.real {ω | a < U ω} * P.real {ω | b < V ω} := by
  have := hind.measure_inter_preimage_eq_mul (Ioi a) (Ioi b) measurableSet_Ioi measurableSet_Ioi
  simp only [measureReal_def]
  change (P (U ⁻¹' Ioi a ∩ V ⁻¹' Ioi b)).toReal =
    (P (U ⁻¹' Ioi a)).toReal * (P (V ⁻¹' Ioi b)).toReal
  rw [this, ENNReal.toReal_mul]

/-- The direction of a large value of the first of two independent nonnegative variables is
close to the first axis: a quantitative estimate. -/
theorem abs_setIntegral_dir_sub_le {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hV0 : ∀ ω, 0 ≤ V ω) (hind : IndepFun U V P) (f : ℝ × ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x > 0,
      |∫ ω in {ω | x < U ω}, f ((max (U ω) (V ω))⁻¹ • (U ω, V ω)) ∂P -
          P.real {ω | x < U ω} * f (1, 0)| ≤
        P.real {ω | x < U ω} * (ε + 2 * ‖f‖ * P.real {ω | δ * x < V ω}) := by
  obtain ⟨δ0, hδ0, hcont⟩ := Metric.continuous_iff.1 f.continuous ((1 : ℝ), (0 : ℝ)) ε hε
  refine ⟨min (δ0 / 2) (1 / 2), by positivity, fun x hx => ?_⟩
  set δ := min (δ0 / 2) (1 / 2) with hδdef
  set s := {ω | x < U ω} with hsdef
  have hs : MeasurableSet s := measurableSet_lt measurable_const hU
  set t := {ω | δ * x < V ω} with htdef
  have ht : MeasurableSet t := measurableSet_lt measurable_const hV
  set D : Ω → ℝ := fun ω => f ((max (U ω) (V ω))⁻¹ • (U ω, V ω)) with hDdef
  have hDm : Measurable D :=
    f.continuous.measurable.comp (((hU.max hV).inv).smul (hU.prodMk hV))
  have hpt : ∀ ω ∈ s, |D ω - f (1, 0)| ≤ ε + 2 * ‖f‖ * t.indicator 1 ω := by
    intro ω hω
    by_cases hωt : ω ∈ t
    · rw [indicator_of_mem hωt, Pi.one_apply, mul_one]
      have h2 := f.dist_le_two_norm ((max (U ω) (V ω))⁻¹ • (U ω, V ω)) (1, 0)
      rw [Real.dist_eq] at h2
      linarith
    · rw [indicator_of_notMem hωt, mul_zero, add_zero]
      have hUx : x < U ω := hω
      have hVle : V ω ≤ δ * x := not_lt.1 hωt
      have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
      have hδ2 : δ ≤ δ0 / 2 := min_le_left _ _
      have hU0' : 0 < U ω := hx.trans hUx
      have hVU : V ω ≤ U ω := by nlinarith
      have hdist : dist ((U ω)⁻¹ • (U ω, V ω)) ((1 : ℝ), (0 : ℝ)) < δ0 := by
        rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hU0'.ne', Prod.dist_eq,
          dist_self, Real.dist_eq, sub_zero, max_lt_iff]
        refine ⟨hδ0, ?_⟩
        rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hU0'.le) (hV0 ω)), inv_mul_lt_iff₀ hU0']
        nlinarith
      have := hcont _ hdist
      rw [Real.dist_eq] at this
      simp only [hDdef, max_eq_left hVU]
      exact this.le
  have hDint : Integrable D P := Integrable.of_bound hDm.aestronglyMeasurable ‖f‖
    (ae_of_all _ fun ω => f.norm_coe_le_norm _)
  have hRint : Integrable (fun ω => ε + 2 * ‖f‖ * t.indicator 1 ω) P :=
    (integrable_const ε).add (by exact ((integrable_const (1 : ℝ)).indicator ht).const_mul _)
  calc |∫ ω in s, D ω ∂P - P.real s * f (1, 0)|
      = |∫ ω in s, (D ω - f (1, 0)) ∂P| := by
        rw [integral_sub hDint.integrableOn (integrable_const _), setIntegral_const, smul_eq_mul]
    _ ≤ ∫ ω in s, |D ω - f (1, 0)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω in s, (ε + 2 * ‖f‖ * t.indicator 1 ω) ∂P :=
        setIntegral_mono_on (hDint.sub (integrable_const _)).abs.integrableOn
          hRint.integrableOn hs hpt
    _ = P.real s * ε + 2 * ‖f‖ * P.real (t ∩ s) := by
        rw [integral_add (integrable_const _)
          (by exact ((integrable_const (1 : ℝ)).indicator ht).const_mul _), setIntegral_const,
          integral_const_mul, integral_indicator_one ht, measureReal_restrict_apply ht,
          smul_eq_mul]
    _ = P.real s * (ε + 2 * ‖f‖ * P.real t) := by
        rw [inter_comm, hsdef, htdef, measureReal_lt_inter_lt_eq_mul hind]
        ring

/-- The normalized error in `abs_setIntegral_dir_sub_le` tends to `0`. -/
theorem tendsto_setIntegral_dir_sub_div {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hV0 : ∀ ω, 0 ≤ V ω) (hind : IndepFun U V P) (f : ℝ × ℝ →ᵇ ℝ) {G : ℝ → ℝ} {M : ℝ}
    (hG : ∀ᶠ x in atTop, 0 < G x ∧ P.real {ω | x < U ω} ≤ M * G x) :
    Tendsto (fun x => (∫ ω in {ω | x < U ω}, f ((max (U ω) (V ω))⁻¹ • (U ω, V ω)) ∂P -
      P.real {ω | x < U ω} * f (1, 0)) / G x) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hε : 0 < ε' / (4 * M') := by positivity
  obtain ⟨δ, hδ, hb⟩ := abs_setIntegral_dir_sub_le hU hV hV0 hind f hε
  have hlim : Tendsto (fun x => 2 * ‖f‖ * P.real {ω | δ * x < V ω}) atTop (𝓝 0) := by
    have := ((tendsto_measureReal_lt_atTop (P := P) hV).comp
      (tendsto_id.const_mul_atTop hδ)).const_mul (2 * ‖f‖)
    simpa using this
  filter_upwards [hG, hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with x hGx hsmall
    hx
  obtain ⟨hG0, hGM⟩ := hGx
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hG0, div_lt_iff₀ hG0]
  have hP0 : 0 ≤ P.real {ω | x < U ω} := measureReal_nonneg
  have hGM' : P.real {ω | x < U ω} ≤ M' * G x :=
    hGM.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hG0.le)
  calc _ ≤ P.real {ω | x < U ω} * (ε' / (4 * M') + 2 * ‖f‖ * P.real {ω | δ * x < V ω}) :=
        hb x hx
    _ ≤ (M' * G x) * (ε' / (4 * M') + ε' / (4 * M')) := by
        apply mul_le_mul hGM' (by linarith) (by positivity) (by positivity)
    _ = ε' / 2 * G x := by field_simp; ring
    _ < ε' * G x := by nlinarith

/-- The spectral measure of a vector with independent components and balanced tails:
`((1 + c)⁻¹ (δ_(1,0) + c δ_(0,1)))`, concentrated on the axes. -/
noncomputable def axesSpectralMeasure (c : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 + c)⁻¹ •
    (Measure.dirac ((1 : ℝ), (0 : ℝ)) + ENNReal.ofReal c • Measure.dirac ((0 : ℝ), (1 : ℝ)))

theorem isProbabilityMeasure_axesSpectralMeasure {c : ℝ} (hc : 0 ≤ c) :
    IsProbabilityMeasure (axesSpectralMeasure c) := by
  constructor
  rw [axesSpectralMeasure, Measure.smul_apply, Measure.add_apply, Measure.smul_apply,
    measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one hc, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ (by positivity)]

theorem integral_axesSpectralMeasure {c : ℝ} (hc : 0 ≤ c) (f : ℝ × ℝ →ᵇ ℝ) :
    ∫ y, f y ∂axesSpectralMeasure c = (1 + c)⁻¹ * (f (1, 0) + c * f (0, 1)) := by
  have : IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac ((0 : ℝ), (1 : ℝ))) :=
    ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact ENNReal.ofReal_lt_top⟩
  rw [axesSpectralMeasure, integral_smul_measure,
    integral_add_measure (f.integrable _) (f.integrable _), integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hc, smul_eq_mul, smul_eq_mul]

/-- **Independent components: existence and asymptotic independence** ([Res07, §6.5.1],
[KS20, §2.1]). Let `X₁, X₂ ≥ 0` be independent, with `P(X₁ > x)` regularly varying with
index `-α`, `α > 0`, and tail balance `P(X₂ > x) / P(X₁ > x) → c ≥ 0`. Then `X = (X₁, X₂)` is
regularly varying with spectral measure `(1 + c)⁻¹ (δ_(1,0) + c δ_(0,1))`: its exponent measure
is concentrated on the axes. -/
theorem isRegVarVector_of_indepFun (hα : 0 < α)
    {X₁ X₂ : Ω → ℝ} (h₁ : Measurable X₁) (h₂ : Measurable X₂)
    (h₁0 : ∀ ω, 0 ≤ X₁ ω) (h₂0 : ∀ ω, 0 ≤ X₂ ω) (hind : IndepFun X₁ X₂ P)
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < X₁ ω}) (-α)) {c : ℝ} (hc : 0 ≤ c)
    (hbal : Tendsto (fun x => P.real {ω | x < X₂ ω} / P.real {ω | x < X₁ ω}) atTop (𝓝 c)) :
    IsRegVarVector P (fun ω => (X₁ ω, X₂ ω)) α (polarMeasure α (axesSpectralMeasure c)) := by
  have := isProbabilityMeasure_axesSpectralMeasure hc
  set F₁ : ℝ → ℝ := fun x => P.real {ω | x < X₁ ω} with hF₁
  set F₂ : ℝ → ℝ := fun x => P.real {ω | x < X₂ ω} with hF₂
  have hnorm : ∀ ω, ‖(X₁ ω, X₂ ω)‖ = max (X₁ ω) (X₂ ω) := fun ω => by
    rw [Prod.norm_def, Real.norm_of_nonneg (h₁0 ω), Real.norm_of_nonneg (h₂0 ω)]
  have hset : ∀ x, {ω | x < ‖(X₁ ω, X₂ ω)‖} = {ω | x < X₁ ω} ∪ {ω | x < X₂ ω} := fun x => by
    ext ω; simp [hnorm, lt_max_iff]
  have hN : ∀ x, P.real {ω | x < ‖(X₁ ω, X₂ ω)‖} = F₁ x + F₂ x - F₁ x * F₂ x := fun x => by
    rw [hset, hF₁, hF₂, ← measureReal_lt_inter_lt_eq_mul hind]
    have := measureReal_union_add_inter (μ := P) (s := {ω | x < X₁ ω})
      (measurableSet_lt measurable_const h₂ : MeasurableSet {ω | x < X₂ ω})
    linarith
  have hF₂lim : Tendsto F₂ atTop (𝓝 0) := tendsto_measureReal_lt_atTop h₂
  have hpos := hRV.eventually_pos
  -- `N / F₁ → 1 + c`
  have hNF : Tendsto (fun x => P.real {ω | x < ‖(X₁ ω, X₂ ω)‖} / F₁ x) atTop (𝓝 (1 + c)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add (hbal.sub hF₂lim)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hpos] with x hx
    rw [hN]
    simp only [hF₁, hF₂] at hx ⊢
    field_simp
    ring
  have h1c : (1 + c) ≠ 0 := by positivity
  -- regular variation of the norm
  have hRVN : IsRegularlyVarying (fun x => P.real {ω | x < ‖(X₁ ω, X₂ ω)‖}) (-α) := by
    refine ⟨?_, fun t ht => ?_⟩
    · filter_upwards [hpos] with x hx
      rw [hset]
      exact hx.trans_le (measureReal_mono subset_union_left)
    · have hlim := ((hNF.comp (tendsto_id.const_mul_atTop ht)).mul (hRV.tendsto ht)).mul
        (hNF.inv₀ h1c)
      rw [show (1 + c) * t ^ (-α) * (1 + c)⁻¹ = t ^ (-α) by field_simp] at hlim
      refine hlim.congr' ?_
      filter_upwards [hpos, (tendsto_id.const_mul_atTop ht).eventually hpos] with x hx htx
      simp only [Function.comp_apply, id] at htx ⊢
      have hNx : 0 < P.real {ω | x < ‖(X₁ ω, X₂ ω)‖} := by
        rw [hset]; exact hx.trans_le (measureReal_mono subset_union_left)
      field_simp
  refine isRegVarVector_polarMeasure hα (h₁.prodMk h₂) hRVN ?_
  intro f
  rw [integral_axesSpectralMeasure hc]
  -- the three pieces
  set T : Ω → ℝ × ℝ := fun ω => (max (X₁ ω) (X₂ ω))⁻¹ • (X₁ ω, X₂ ω) with hT
  have hTm : Measurable T := ((h₁.max h₂).inv).smul (h₁.prodMk h₂)
  have hfT : Integrable (fun ω => f (T ω)) P := Integrable.of_bound
    (f.continuous.measurable.comp hTm).aestronglyMeasurable ‖f‖
    (ae_of_all _ fun ω => f.norm_coe_le_norm _)
  set J₁ : ℝ → ℝ := fun x => ∫ ω in {ω | x < X₁ ω}, f (T ω) ∂P
  set J₂ : ℝ → ℝ := fun x => ∫ ω in {ω | x < X₂ ω}, f (T ω) ∂P
  set J₁₂ : ℝ → ℝ := fun x => ∫ ω in {ω | x < X₁ ω} ∩ {ω | x < X₂ ω}, f (T ω) ∂P
  have hJ : ∀ x, ∫ ω in {ω | x < X₁ ω} ∪ {ω | x < X₂ ω}, f (T ω) ∂P = J₁ x + J₂ x - J₁₂ x := by
    intro x
    have hA : MeasurableSet {ω | x < X₁ ω} := measurableSet_lt measurable_const h₁
    have hB : MeasurableSet {ω | x < X₂ ω} := measurableSet_lt measurable_const h₂
    simp only [J₁, J₂, J₁₂]
    have hpt : ({ω | x < X₁ ω} ∪ {ω | x < X₂ ω}).indicator (fun ω => f (T ω)) =
        fun ω => {ω | x < X₁ ω}.indicator (fun ω => f (T ω)) ω +
          {ω | x < X₂ ω}.indicator (fun ω => f (T ω)) ω -
          ({ω | x < X₁ ω} ∩ {ω | x < X₂ ω}).indicator (fun ω => f (T ω)) ω := by
      ext ω
      by_cases ha : ω ∈ {ω | x < X₁ ω} <;> by_cases hb : ω ∈ {ω | x < X₂ ω} <;>
        simp [Set.indicator, ha, hb]
    rw [← integral_indicator (hA.union hB)]
    simp only [hpt]
    have hi : Integrable (fun ω => {ω | x < X₁ ω}.indicator (fun ω => f (T ω)) ω +
        {ω | x < X₂ ω}.indicator (fun ω => f (T ω)) ω) P :=
      (hfT.indicator hA).add (hfT.indicator hB)
    rw [integral_sub hi (hfT.indicator (hA.inter hB)),
      integral_add (hfT.indicator hA) (hfT.indicator hB), integral_indicator hA,
      integral_indicator hB, integral_indicator (hA.inter hB)]
  -- `J₁ / F₁ → f (1, 0)`
  have hJ₁ : Tendsto (fun x => J₁ x / F₁ x) atTop (𝓝 (f (1, 0))) := by
    have key := tendsto_setIntegral_dir_sub_div h₁ h₂ h₂0 hind f (G := F₁) (M := 1)
      (by filter_upwards [hpos] with x hx using ⟨hx, by rw [one_mul]⟩)
    have := key.add (tendsto_const_nhds (x := f (1, 0)))
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hpos] with x hx
    simp only [J₁, T]
    field_simp
    ring
  -- `J₂ / F₁ → c f (0, 1)`
  have hJ₂ : Tendsto (fun x => J₂ x / F₁ x) atTop (𝓝 (c * f (0, 1))) := by
    let f' : ℝ × ℝ →ᵇ ℝ := f.compContinuous ⟨Prod.swap, continuous_swap⟩
    have hbd : ∀ᶠ x in atTop, 0 < F₁ x ∧ F₂ x ≤ (c + 1) * F₁ x := by
      filter_upwards [hpos, hbal.eventually (gt_mem_nhds (lt_add_one c))] with x hx hx'
      exact ⟨hx, by rw [div_lt_iff₀ hx] at hx'; linarith⟩
    have key := tendsto_setIntegral_dir_sub_div h₂ h₁ h₁0 hind.symm f' hbd
    have := key.add (hbal.mul_const (f (0, 1)))
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hpos] with x hx
    have hsw : ∀ ω, f' ((max (X₂ ω) (X₁ ω))⁻¹ • (X₂ ω, X₁ ω)) = f (T ω) := fun ω => by
      simp [f', T, max_comm]
    simp only [hsw, J₂]
    have hf' : f' (1, 0) = f (0, 1) := rfl
    rw [hf']
    simp only [hF₁] at hx ⊢
    field_simp
    ring
  -- `J₁₂ / F₁ → 0`
  have hJ₁₂ : Tendsto (fun x => J₁₂ x / F₁ x) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x => ‖f‖ * F₂ x) atTop (𝓝 0) := by
      simpa using hF₂lim.const_mul ‖f‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hpos] with x hx
    rw [norm_div, Real.norm_of_nonneg hx.le, div_le_iff₀ hx]
    have := norm_setIntegral_le_of_norm_le_const (μ := P) (f := fun ω => f (T ω))
      (s := {ω | x < X₁ ω} ∩ {ω | x < X₂ ω}) (measure_lt_top _ _)
      (fun ω _ => f.norm_coe_le_norm _)
    rw [measureReal_lt_inter_lt_eq_mul hind] at this
    calc ‖J₁₂ x‖ ≤ ‖f‖ * (F₁ x * F₂ x) := this
      _ = ‖f‖ * F₂ x * F₁ x := by ring
  have hI := (hJ₁.add hJ₂).sub hJ₁₂
  rw [sub_zero] at hI
  have hfin := hI.div hNF h1c
  rw [show (f (1, 0) + c * f (0, 1)) / (1 + c) = (1 + c)⁻¹ * (f (1, 0) + c * f (0, 1)) by
    field_simp] at hfin
  refine hfin.congr' ?_
  filter_upwards [hpos] with x hx
  have hNx : 0 < P.real {ω | x < ‖(X₁ ω, X₂ ω)‖} := by
    rw [hset]; exact hx.trans_le (measureReal_mono subset_union_left)
  show (J₁ x / F₁ x + J₂ x / F₁ x - J₁₂ x / F₁ x) /
    (P.real {ω | x < ‖(X₁ ω, X₂ ω)‖} / F₁ x) = _
  rw [integral_cond_eq, smul_eq_mul]
  have hfun : ∀ ω, ‖(X₁ ω, X₂ ω)‖⁻¹ • (X₁ ω, X₂ ω) = T ω := fun ω => by simp only [T, hnorm]
  simp only [hfun]
  rw [hset x] at hNx ⊢
  rw [hJ x]
  field_simp

end Independent

section LinearSpectral

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {X : Ω → E} {α : ℝ} {μ : Measure E}

omit [IsProbabilityMeasure P] in
/-- Half-spaces under the polar measure: `μ {L > 1} = ∫ (L θ)₊ ^ α dS(θ)`. -/
theorem polarMeasure_one_lt_linear (hα : 0 < α) {S : Measure E} [IsProbabilityMeasure S]
    (L : E →L[ℝ] ℝ) :
    polarMeasure α S {y | 1 < L y} = ∫⁻ θ, ENNReal.ofReal (max (L θ) 0 ^ α) ∂S := by
  have hsm : Measurable fun p : ℝ × E => p.1 • p.2 := measurable_fst.smul measurable_snd
  have hm : MeasurableSet {y : E | 1 < L y} := measurableSet_lt measurable_const L.measurable
  rw [polarMeasure, Measure.map_apply hsm hm, Measure.prod_apply_symm (hsm hm)]
  refine lintegral_congr fun θ => ?_
  have hpre : (fun r : ℝ => (r, θ)) ⁻¹' ((fun p : ℝ × E => p.1 • p.2) ⁻¹' {y | 1 < L y}) =
      {r : ℝ | 1 < r * L θ} := by
    ext r; simp [L.map_smul]
  rw [hpre]
  rcases lt_or_ge 0 (L θ) with hL | hL
  · have : {r : ℝ | 1 < r * L θ} = Ioi (L θ)⁻¹ := by
      ext r
      simp only [mem_ofPred_eq, mem_Ioi, inv_eq_one_div, div_lt_iff₀ hL]
    rw [this, radialMeasure_Ioi hα (inv_pos.2 hL), max_eq_left hL.le,
      Real.rpow_neg (inv_nonneg.2 hL.le), Real.inv_rpow hL.le, inv_inv]
  · have hsub : {r : ℝ | 1 < r * L θ} ⊆ Iic 0 := fun r (hr : 1 < r * L θ) => by
      by_contra h'
      simp only [mem_Iic, not_le] at h'
      nlinarith
    rw [measure_mono_null hsub radialMeasure_Iic_zero, max_eq_right hL,
      Real.zero_rpow hα.ne', ENNReal.ofReal_zero]

/-- **Tails of linear combinations through the spectral measure** ([BDM02, (1.3)]): if `X` is
regularly varying with spectral measure `S`, then
`P(L X > x) / P(‖X‖ > x) → ∫ (L θ)₊ ^ α dS(θ)`. -/
theorem IsRegVarVector.tendsto_linear_spectral (hα : 0 < α) (h : IsRegVarVector P X α μ)
    (hX : Measurable X) (L : E →L[ℝ] ℝ) :
    Tendsto (fun x => P.real {ω | x < L (X ω)} / P.real {ω | x < ‖X ω‖}) atTop
      (𝓝 (∫ θ, max (L θ) 0 ^ α ∂spectralMeasure μ)) := by
  have := h.isProbabilityMeasure_spectralMeasure hX
  have key := h.tendsto_linear hX L
  have hg : Continuous fun θ : E => max (L θ) 0 ^ α :=
    (L.continuous.max continuous_const).rpow_const fun _ => Or.inr hα.le
  have hint : Integrable (fun θ => max (L θ) 0 ^ α) (spectralMeasure μ) := by
    refine Integrable.of_bound hg.aestronglyMeasurable (‖L‖ ^ α) ?_
    filter_upwards [h.ae_norm_spectralMeasure hα hX] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
    refine Real.rpow_le_rpow (le_max_right _ _) (max_le ?_ (norm_nonneg _)) hα.le
    have := L.le_opNorm θ
    rw [hθ, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hval : μ.real {y | 1 < L y} = ∫ θ, max (L θ) 0 ^ α ∂spectralMeasure μ := by
    rw [measureReal_def, h.eq_polarMeasure hα hX, polarMeasure_one_lt_linear hα L,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun θ => Real.rpow_nonneg (le_max_right _ _) _),
      ENNReal.toReal_ofReal (integral_nonneg fun θ => Real.rpow_nonneg (le_max_right _ _) _)]
    rw [← h.eq_polarMeasure hα hX]
  rwa [hval] at key

end LinearSpectral

end ExtremeValueTheory
