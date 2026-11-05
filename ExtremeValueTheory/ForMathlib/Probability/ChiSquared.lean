/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import ExtremeValueTheory.ForMathlib.Probability.WaldInterval

/-!
# The chi-squared distribution

Mathlib v4.35.0 has the Gamma laws but no chi-squared law. We define `χ²_k` as what it is in the
theory of the likelihood ratio: the law of `‖Z‖²`, with `Z` standard Gaussian in `ℝᵏ`.

## Main results

* `ProbabilityTheory.chiSquared k`: the law of `‖Z‖²`, `Z ~ N(0, Iₖ)`.
* `ProbabilityTheory.chiSquared_one_eq_map`: `χ²₁` is the law of `Z²`, `Z ~ N(0, 1)`.
* `ProbabilityTheory.chiSquared_one_Iic`: `χ²₁((-∞, c]) = N(0, 1)([-√c, √c])`, `c ≥ 0`.
* `ProbabilityTheory.exists_chiSquared_one_Iic_eq`: the `χ²₁` quantiles exist.
* `ProbabilityTheory.chiSquared_two_eq_map`: `χ²₂` is the law of `Z₁² + Z₂²`.
* `ProbabilityTheory.chiSquared_two_real_Iic`: `χ²₂((-∞, c]) = 1 - e^{-c/2}`, `c ≥ 0`, and
  `chiSquared_two_real_Iic_log`: its quantiles are `-2 log α`.
* Instances: `χ²₁` and `χ²₂` have no atoms.
* `MeasureTheory.TendstoInDistribution.tendsto_measure_le_of_noAtoms`: convergence in
  distribution to a law without atoms gives convergence of the probabilities of `{Yᵢ ≤ c}`.

## References

* [A. W. van der Vaart, *Asymptotic Statistics*, §2.3, §16][vandervaart1998]
-/

public section

open Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

open MeasureTheory

/-- The **chi-squared law with `k` degrees of freedom**: the law of `‖Z‖²`, `Z` standard Gaussian
in `ℝᵏ`. -/
noncomputable def chiSquared (k : ℕ) : Measure ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin k))).map fun z => ‖z‖ ^ 2

instance (k : ℕ) : IsProbabilityMeasure (chiSquared k) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- `‖Z‖²` has law `χ²_k` when `Z ~ N(0, Iₖ)`. -/
lemma HasLaw.norm_sq_chiSquared {k : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Z : Ω → EuclideanSpace ℝ (Fin k)} (hZ : HasLaw Z (stdGaussian _) P) :
    HasLaw (fun ω => ‖Z ω‖ ^ 2) (chiSquared k) P := by
  refine ⟨by have := hZ.aemeasurable; fun_prop, ?_⟩
  rw [chiSquared, ← hZ.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ.aemeasurable]
  rfl

/-- `χ²₁` is the law of `Z²`, `Z ~ N(0, 1)`. -/
theorem chiSquared_one_eq_map : chiSquared 1 = (gaussianReal 0 1).map fun x => x ^ 2 := by
  have h := measurePreserving_eval_multivariateGaussian (ι := Fin 1) (μ := 0)
    (S := 1) Matrix.PosSemidef.one (i := 0)
  rw [multivariateGaussian_zero_one] at h
  simp only [PiLp.zero_apply, Matrix.one_apply_eq, Real.toNNReal_one] at h
  rw [← h.map_eq, Measure.map_map (by fun_prop) (by fun_prop), chiSquared]
  congr 1
  funext z
  simp [EuclideanSpace.real_norm_sq_eq]

/-- `χ²₁((-∞, c]) = N(0, 1)([-√c, √c])`, `c ≥ 0`. -/
theorem chiSquared_one_Iic {c : ℝ} (hc : 0 ≤ c) :
    chiSquared 1 (Iic c) = gaussianReal 0 1 (Icc (-√c) √c) := by
  rw [chiSquared_one_eq_map, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic, mem_Icc]
  exact Real.sq_le hc

/-- The quantiles of `χ²₁` exist: for `α ∈ (0, 1)` there is `c > 0` with `χ²₁((-∞, c]) = 1 - α`,
namely the square of the two-sided standard normal quantile. -/
theorem exists_chiSquared_one_Iic_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ (chiSquared 1).real (Iic c) = 1 - α := by
  obtain ⟨z, hz, h⟩ := exists_gaussianReal_Icc_eq hα0 hα1
  refine ⟨z ^ 2, by positivity, ?_⟩
  rw [measureReal_def, chiSquared_one_Iic (by positivity), Real.sqrt_sq hz.le]
  exact h

instance : NullSingletonClass (chiSquared 1) where
  measure_singleton c := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [chiSquared_one_eq_map, Measure.map_apply (by fun_prop) (measurableSet_singleton c)]
    refine measure_mono_null (t := {√c, -√c}) (fun x hx => ?_) ?_
    · simp only [mem_preimage, mem_singleton_iff] at hx
      simp only [mem_insert_iff, mem_singleton_iff, ← hx]
      rcases le_total 0 x with h | h
      · exact Or.inl (Real.sqrt_sq h).symm
      · exact Or.inr (by rw [Real.sqrt_sq_eq_abs, abs_of_nonpos h, neg_neg])
    · exact (Set.toFinite _).measure_zero _

/-- `χ²₂` is the law of `Z₁² + Z₂²` for independent standard normal `Z₁`, `Z₂`. -/
theorem chiSquared_two_eq_map : chiSquared 2 =
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map fun p => p.1 ^ 2 + p.2 ^ 2 := by
  have hm := (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [chiSquared, ← map_pi_eq_stdGaussian, ← hm,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  congr 1
  funext x
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

instance : NullSingletonClass (chiSquared 2) where
  measure_singleton c := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [chiSquared_two_eq_map,
      Measure.map_apply (by fun_prop) (measurableSet_singleton c)]
    have hms : MeasurableSet ((fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ⁻¹' {c}) :=
      (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (measurableSet_singleton c)
    rw [Measure.measure_prod_null hms]
    refine Eventually.of_forall fun x => ?_
    refine measure_mono_null (t := {√(c - x ^ 2), -√(c - x ^ 2)}) (fun y hy => ?_) ?_
    · simp only [mem_preimage, mem_singleton_iff] at hy
      have hy' : c - x ^ 2 = y ^ 2 := by linarith
      simp only [mem_insert_iff, mem_singleton_iff, hy']
      rcases le_total 0 y with h | h
      · exact Or.inl (Real.sqrt_sq h).symm
      · exact Or.inr (by rw [Real.sqrt_sq_eq_abs, abs_of_nonpos h, neg_neg])
    · exact (Set.toFinite _).measure_zero _

/-- `∫₀^{√c} r e^{-r²/2} dr = 1 - e^{-c/2}`, written over the half-line. -/
lemma integral_Ioi_mul_exp_indicator {c : ℝ} (hc : 0 ≤ c) :
    ∫ r in Ioi (0 : ℝ), (if r ^ 2 ≤ c then r * Real.exp (-(r ^ 2 / 2)) else 0) = 1 - Real.exp (-(c / 2)) := by
  have hset : ∫ r in Ioi (0 : ℝ), (if r ^ 2 ≤ c then r * Real.exp (-(r ^ 2 / 2)) else 0) =
      ∫ r in Ioc (0 : ℝ) √c, r * Real.exp (-(r ^ 2 / 2)) := by
    have hsub : Ioc (0 : ℝ) √c = Ioi 0 ∩ Iic √c := by ext; simp [mem_Ioc]
    rw [hsub, ← integral_indicator (measurableSet_Ioi.inter measurableSet_Iic),
      ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    by_cases hr : 0 < r
    · have : r ^ 2 ≤ c ↔ r ≤ √c := by
        rw [Real.le_sqrt' hr]
      simp [indicator, hr, this]
    · simp [indicator, hr]
  rw [hset, ← intervalIntegral.integral_of_le (Real.sqrt_nonneg c)]
  have hd : ∀ r ∈ uIcc (0 : ℝ) √c, HasDerivAt (fun r => -Real.exp (-(r ^ 2 / 2))) (r * Real.exp (-(r ^ 2 / 2))) r :=
    fun r _ => by
      have h : HasDerivAt (fun r : ℝ => -(r ^ 2 / 2)) (-r) r := by
        have := (((hasDerivAt_id' r).fun_pow 2).div_const 2).fun_neg
        exact this.congr_deriv (by simp)
      have := h.exp.neg
      refine this.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _), Real.sq_sqrt hc]
  simp
  ring

/-- **The `χ²₂` law is exponential** with mean `2`: `χ²₂((-∞, c]) = 1 - e^{-c/2}`, `c ≥ 0`. -/
theorem chiSquared_two_real_Iic {c : ℝ} (hc : 0 ≤ c) :
    (chiSquared 2).real (Iic c) = 1 - Real.exp (-(c / 2)) := by
  set A : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ c} with hA
  have hAm : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hm : Measurable fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  have h1 : (chiSquared 2).real (Iic c) = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real A := by
    rw [chiSquared_two_eq_map, map_measureReal_apply hm measurableSet_Iic]
    rfl
  set f : ℝ × ℝ → ℝ := fun p => A.indicator (fun p => (2 * Real.pi)⁻¹ * Real.exp (-((p.1 ^ 2 + p.2 ^ 2) / 2))) p
    with hf
  have hprod : (gaussianReal 0 1).prod (gaussianReal 0 1) =
      (volume : Measure (ℝ × ℝ)).withDensity
        fun p => ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-((p.1 ^ 2 + p.2 ^ 2) / 2))) := by
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero, Measure.volume_eq_prod,
      prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
    congr 1
    funext p
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 1
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_mul_mul_comm, ← mul_inv, Real.mul_self_sqrt (by positivity), ← Real.exp_add]
    congr 2
    ring
  have hg0 : ∀ p : ℝ × ℝ, 0 ≤ (2 * Real.pi)⁻¹ * Real.exp (-((p.1 ^ 2 + p.2 ^ 2) / 2)) := fun p => by positivity
  have hfm : Measurable f := by
    refine Measurable.indicator (by fun_prop) hAm
  have hf0 : ∀ p, 0 ≤ f p := fun p => indicator_nonneg (fun p _ => hg0 p) p
  have h2 : ((gaussianReal 0 1).prod (gaussianReal 0 1)).real A = ∫ p, f p := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable, hprod,
      measureReal_def, withDensity_apply _ hAm, ← lintegral_indicator hAm]
    congr 1
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ A <;> simp [f, indicator, hp]
  have h3 : ∫ p, f p = (∫ r in Ioi (0 : ℝ), (2 * Real.pi)⁻¹ * (if r ^ 2 ≤ c then r * Real.exp (-(r ^ 2 / 2)) else 0)) *
      ∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [← setIntegral_prod_mul, ← integral_comp_polarCoord_symm]
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    have hsq : (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
      simp only [polarCoord_symm_apply]
      nlinarith [Real.sin_sq_add_cos_sq p.2]
    simp only [f, smul_eq_mul, mul_one, indicator, hA, mem_ofPred_eq, hsq]
    split_ifs <;> ring
  rw [h1, h2, h3, integral_const_mul, integral_Ioi_mul_exp_indicator hc]
  simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
    smul_eq_mul, mul_one, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have := Real.pi_pos
  field_simp
  ring

/-- The quantiles of `χ²₂` are explicit: `χ²₂((-∞, -2 log α]) = 1 - α`, `α ∈ (0, 1]`. -/
theorem chiSquared_two_real_Iic_log {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (chiSquared 2).real (Iic (-2 * Real.log α)) = 1 - α := by
  have hl : Real.log α ≤ 0 := Real.log_nonpos hα0.le hα1
  rw [chiSquared_two_real_Iic (by linarith)]
  rw [show -(-2 * Real.log α / 2) = Real.log α by ring, Real.exp_log hα0]

end ProbabilityTheory

namespace MeasureTheory

variable {ι Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {l : Filter ι}

/-- **Portmanteau for a half-line.** If `Yᵢ ⇒ Z`, and the law `μ` of `Z` has no atoms, then
`P(Yᵢ ≤ c) → μ((-∞, c])`. -/
theorem TendstoInDistribution.tendsto_measure_le_of_noAtoms [l.IsCountablyGenerated]
    {Y : ι → Ω → ℝ} {Z : Ω' → ℝ} {μ : Measure ℝ} [NullSingletonClass μ]
    (hY : TendstoInDistribution Y l Z (fun _ ↦ P) P') (hZ : HasLaw Z μ P') (c : ℝ) :
    Tendsto (fun i ↦ P {ω | Y i ω ≤ c}) l (𝓝 (μ (Iic c))) := by
  have hnull : (P'.map Z) (frontier (Iic c)) = 0 := by
    rw [hZ.map_eq, frontier_Iic]
    exact measure_singleton c
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hY.tendsto
    (E := Iic c) hnull
  simp only [ProbabilityMeasure.coe_mk] at key
  rw [hZ.map_eq] at key
  refine key.congr fun i ↦ ?_
  rw [Measure.map_apply_of_aemeasurable (hY.forall_aemeasurable i) measurableSet_Iic]
  rfl

end MeasureTheory
