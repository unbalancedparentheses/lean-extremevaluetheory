/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import ExtremeValueTheory.ForMathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# The delta method

Let `θ̂ᵢ` be estimators of a parameter `θ` in a normed space `E`, and suppose that they are
asymptotically distributed at rate `rᵢ → ∞`: `rᵢ (θ̂ᵢ - θ) ⇒ Z`. If `g : E → F` is (Fréchet)
differentiable at `θ` with derivative `g'`, then

  `rᵢ (g θ̂ᵢ - g θ) ⇒ g' Z`.

This is the **delta method**. In particular, if `Z` is a centered multivariate Gaussian with
covariance matrix `S` and `g` is real valued with gradient `∇g(θ)`, then the limit is the
centered real Gaussian with variance `∇g(θ)ᵀ S ∇g(θ)`.

The proof is the usual one: `g' (rᵢ (θ̂ᵢ - θ)) ⇒ g' Z` by the continuous mapping theorem, and the
difference `rᵢ (g θ̂ᵢ - g θ - g' (θ̂ᵢ - θ))` tends to `0` in probability because
`rᵢ (θ̂ᵢ - θ)` is tight and `g θ' - g θ - g' (θ' - θ) = o(‖θ' - θ‖)`.

All random variables `θ̂ᵢ` are defined on one probability space, as in Mathlib's Slutsky
theorem `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`.

## Main results

* `TendstoInMeasure.comp_continuousAt`: continuous mapping theorem for convergence in probability
  to a constant.
* `TendstoInDistribution.exists_measure_le_norm_le`: sequences converging in distribution in a
  normed space are tight.
* `TendstoInDistribution.tendstoInMeasure_of_smul`: if `rᵢ Yᵢ` converges in distribution and
  `rᵢ → ∞`, then `Yᵢ → 0` in probability (consistency from asymptotic normality).
* `TendstoInDistribution.delta_method`: the delta method.
* `ProbabilityTheory.map_inner_multivariateGaussian`: the image of `N(0, S)` under `x ↦ ⟪a, x⟫`
  is `N(0, aᵀ S a)`.
* `TendstoInDistribution.delta_method_gaussian`: the delta method with a Gaussian limit.

## References

* [A. W. van der Vaart, *Asymptotic Statistics*, Theorem 3.1][vandervaart1998]
-/

public section

open Filter Topology Set ProbabilityTheory
open scoped ENNReal RealInnerProductSpace Matrix

namespace MeasureTheory

variable {ι Ω Ω' Ω'' E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P''] {l : Filter ι}

omit [IsProbabilityMeasure P] in
/-- **Continuous mapping theorem for convergence in probability to a constant**: if `fᵢ → c` in
probability and `g` is continuous at `c`, then `g ∘ fᵢ → g c` in probability. -/
theorem TendstoInMeasure.comp_continuousAt [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : ι → Ω → E} {c : E} (hf : TendstoInMeasure P f l (fun _ ↦ c)) {g : E → F}
    (hg : ContinuousAt g c) :
    TendstoInMeasure P (fun i ω ↦ g (f i ω)) l (fun _ ↦ g c) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.1 hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf δ hδ)
    (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall fun i ↦ measure_mono ?_)
  intro ω hω
  by_contra h
  exact (not_le.2 (hgδ (not_le.1 h))) hω

variable [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Tightness in a normed space**: if `Xᵢ ⇒ Z`, then for every `ε > 0` there is `M` with
`μᵢ {M ≤ ‖Xᵢ‖} ≤ ε` eventually. -/
theorem TendstoInDistribution.exists_measure_le_norm_le {X : ι → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l Z (fun _ ↦ P) P') {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ᶠ i in l, P {ω | M ≤ ‖X i ω‖} ≤ ε := by
  obtain ⟨M, hM⟩ := (h.continuous_comp continuous_norm).exists_measure_le_abs_le hε
  exact ⟨M, by simpa using hM⟩

variable [NormedSpace ℝ E]

/-- **Consistency from a rate of convergence in distribution**: if `rᵢ Yᵢ ⇒ Z` with `rᵢ → ∞`,
then `Yᵢ → 0` in probability. -/
theorem TendstoInDistribution.tendstoInMeasure_of_smul {Y : ι → Ω → E} {Z : Ω' → E}
    {r : ι → ℝ} (h : TendstoInDistribution (fun i ω ↦ r i • Y i ω) l Z (fun _ ↦ P) P')
    (hr : Tendsto r l atTop) :
    TendstoInMeasure P Y l (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨M, hM⟩ := h.exists_measure_le_norm_le hδ
  filter_upwards [hM, hr.eventually_gt_atTop (max M 1 / ε)] with i hi hri
  refine (measure_mono fun ω hω ↦ ?_).trans hi
  simp only [mem_ofPred_eq, sub_zero] at hω ⊢
  have hM1 : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hr0 : 0 < r i := lt_trans (div_pos hM1 hε) hri
  rw [norm_smul, Real.norm_of_nonneg hr0.le]
  calc M ≤ max M 1 := le_max_left _ _
    _ = max M 1 / ε * ε := by field_simp
    _ ≤ r i * ‖Y i ω‖ := mul_le_mul hri.le hω hε.le hr0.le

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- **The delta method** ([van der Vaart, Theorem 3.1]). Let `θ̂ᵢ` be random elements of a normed
space `E` with `rᵢ (θ̂ᵢ - θ) ⇒ Z` for a rate `rᵢ → ∞`, and let `g : E → F` be differentiable at `θ`
with derivative `g'`. Then `rᵢ (g θ̂ᵢ - g θ) ⇒ g' Z`. -/
theorem TendstoInDistribution.delta_method [l.IsCountablyGenerated] {θh : ι → Ω → E} {θ : E}
    {r : ι → ℝ} {Z : Ω' → E}
    (h : TendstoInDistribution (fun i ω ↦ r i • (θh i ω - θ)) l Z (fun _ ↦ P) P')
    (hr : Tendsto r l atTop) {g : E → F} {g' : E →L[ℝ] F} (hg : HasFDerivAt g g' θ)
    (hgm : ∀ i, AEMeasurable (fun ω ↦ g (θh i ω)) P) :
    TendstoInDistribution (fun i ω ↦ r i • (g (θh i ω) - g θ)) l (fun ω ↦ g' (Z ω))
      (fun _ ↦ P) P' := by
  have hX := h.continuous_comp g'.continuous
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_
    (fun i ↦ (hgm i).const_sub (g θ) |>.neg.const_smul (r i) |>.congr
      (Eventually.of_forall fun ω ↦ by simp [neg_sub]))
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨M, hM⟩ := h.exists_measure_le_norm_le hδ
  set M' := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hη : 0 < ε / M' := div_pos hε hM'0
  obtain ⟨ρ, hρ, hρg⟩ := Metric.eventually_nhds_iff.1 (hg.isLittleO.def hη)
  filter_upwards [hM, hr.eventually_gt_atTop (M' / ρ)] with i hi hri
  refine (measure_mono fun ω hω ↦ ?_).trans hi
  simp only [mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, sub_zero, Function.comp_apply] at hω ⊢
  have hr0 : 0 < r i := lt_trans (div_pos hM'0 hρ) hri
  by_contra hlt
  push Not at hlt
  have hlt' : ‖r i • (θh i ω - θ)‖ < M' := lt_of_lt_of_le hlt (le_max_left _ _)
  rw [norm_smul, Real.norm_of_nonneg hr0.le] at hlt'
  have hdist : dist (θh i ω) θ < ρ := by
    rw [dist_eq_norm]
    rw [div_lt_iff₀ hρ] at hri
    nlinarith [norm_nonneg (θh i ω - θ)]
  have hR := hρg hdist
  have heq : r i • (g (θh i ω) - g θ) - g' (r i • (θh i ω - θ)) =
      r i • (g (θh i ω) - g θ - g' (θh i ω - θ)) := by
    simp only [map_sub, map_smul, smul_sub]
  rw [heq, norm_smul, Real.norm_of_nonneg hr0.le] at hω
  have : r i * ‖g (θh i ω) - g θ - g' (θh i ω - θ)‖ ≤ ε / M' * (r i * ‖θh i ω - θ‖) := by
    calc r i * ‖g (θh i ω) - g θ - g' (θh i ω - θ)‖
        ≤ r i * (ε / M' * ‖θh i ω - θ‖) := mul_le_mul_of_nonneg_left hR hr0.le
      _ = ε / M' * (r i * ‖θh i ω - θ‖) := by ring
  have h2 : ε / M' * (r i * ‖θh i ω - θ‖) < ε / M' * M' := mul_lt_mul_of_pos_left hlt' hη
  rw [div_mul_cancel₀ _ hM'0.ne'] at h2
  linarith

end MeasureTheory

namespace ProbabilityTheory

open MeasureTheory

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The image of the centered multivariate Gaussian `N(0, S)` under the linear form `x ↦ ⟪a, x⟫`
is the centered real Gaussian with variance `aᵀ S a`. -/
lemma map_inner_multivariateGaussian {S : Matrix κ κ ℝ} (hS : S.PosSemidef)
    (a : EuclideanSpace ℝ κ) :
    (multivariateGaussian 0 S).map (fun x ↦ ⟪a, x⟫) =
      gaussianReal 0 (a ⬝ᵥ S *ᵥ a).toNNReal := by
  have h := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) (innerSL ℝ a)
  have hmean : (multivariateGaussian 0 S)[innerSL ℝ a] = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp
    · exact IsGaussian.integrable_id
  have hvar : Var[innerSL ℝ a; multivariateGaussian 0 S] = a ⬝ᵥ S *ᵥ a := by
    rw [← covarianceBilin_multivariateGaussian (μ := 0) hS a a,
      covarianceBilin_self IsGaussian.memLp_two_id]
    rfl
  rw [hmean, hvar] at h
  simpa using h

end ProbabilityTheory

namespace MeasureTheory

variable {ι Ω Ω' Ω'' κ : Type*} [Fintype κ] [DecidableEq κ] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''}
  [IsProbabilityMeasure P''] {l : Filter ι}

/-- **The delta method with a Gaussian limit.** If `rᵢ (θ̂ᵢ - θ) ⇒ N(0, S)` in `ℝ^κ` with
`rᵢ → ∞`, and `g : ℝ^κ → ℝ` has gradient `a` at `θ`, then `rᵢ (g θ̂ᵢ - g θ) ⇒ N(0, aᵀ S a)`. The
limit is expressed as any random variable `W` with that law. -/
theorem TendstoInDistribution.delta_method_gaussian [l.IsCountablyGenerated]
    {θh : ι → Ω → EuclideanSpace ℝ κ} {θ : EuclideanSpace ℝ κ} {r : ι → ℝ}
    {Z : Ω' → EuclideanSpace ℝ κ} {S : Matrix κ κ ℝ} (hS : S.PosSemidef)
    (h : TendstoInDistribution (fun i ω ↦ r i • (θh i ω - θ)) l Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (multivariateGaussian 0 S) P') (hr : Tendsto r l atTop)
    {g : EuclideanSpace ℝ κ → ℝ} {a : EuclideanSpace ℝ κ} (hg : HasGradientAt g a θ)
    (hgm : ∀ i, AEMeasurable (fun ω ↦ g (θh i ω)) P) {W : Ω'' → ℝ}
    (hW : HasLaw W (gaussianReal 0 (a ⬝ᵥ S *ᵥ a).toNNReal) P'') :
    TendstoInDistribution (fun i ω ↦ r i * (g (θh i ω) - g θ)) l W (fun _ ↦ P) P'' := by
  have hd := h.delta_method hr (hasGradientAt_iff_hasFDerivAt.1 hg) hgm
  have hlaw : P''.map W = P'.map (fun ω ↦ (InnerProductSpace.toDual ℝ _ a) (Z ω)) := by
    rw [hW.map_eq, ← map_inner_multivariateGaussian hS a, ← hZ.map_eq,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ.aemeasurable]
    rfl
  have e : (⟨P''.map W, inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨P'.map (fun ω ↦ (InnerProductSpace.toDual ℝ _ a) (Z ω)),
        inferInstance⟩ := Subtype.ext hlaw
  refine ⟨hd.forall_aemeasurable, hW.aemeasurable, ?_⟩
  rw [e]
  exact hd.tendsto

end MeasureTheory
