/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.Uniqueness

/-!
# Spectral measures on the simplex

The spectral measure of a simple max-stable law depends on the choice of the norm whose unit
sphere carries it. The library builds it on the sphere `{w | max_i w i = 1}` of the sup norm
(`IsSimpleMaxStable.exists_hasSpectralMeasure`); most of the statistical literature uses the unit
simplex `{w | ∑_i w i = 1}` of the sum norm ([dHF, §6.1.4]; [BGST04, §8.2.3]). The two are
related by a change of norm in polar coordinates: for a positively homogeneous `N` the transport

  `T_N H = image of N(w) dH(w) under w ↦ w / N(w)`

(`normTransport N H`) preserves `∫ g dH` for every positively homogeneous `g`
(`lintegral_normTransport_of_isHomogeneous`), in particular the spectral integrals
`∫ max_i w i / y i dH` and the normalizations `∫ w i dH`, and it carries `H` onto the sphere
`{N = 1}`. Transporting back recovers `H` (`normTransport_normTransport`).

With `N = ∑` this gives the simplex spectral measure `H_Δ = simplexSpectralMeasure H`: it lives on
the simplex, `∫ v i dH_Δ = 1`, its total mass is `|ι|`, and `P(Y ≤ y) = exp (-∫ max_i v i / y i dH_Δ)`.
The probability normalization `Q = H_Δ / |ι|` (`simplexSpectralProb`) has `∫ v i dQ = 1 / |ι|`
and `V(y) = |ι| ∫ max_i v i / y i dQ`. The simplex spectral measure is unique as well
(`eq_of_lintegral_iSup_div_eq_of_simplex`).

In the bivariate case the simplex is parametrized by `q = v 0 ∈ [0, 1]`. The image `Q₂` of `H_Δ`
under `v ↦ v 0` (`pickandsAngularMeasure`) is a measure on `[0, 1]` of mass `2` and mean `1`, and
the Pickands function takes the classical form

  `A(t) = ∫ max(t q, (1 - t)(1 - q)) dQ₂(q)`

(`HasSpectralMeasure.pickandsDependence_eq_angular`). The library's `A(t) = V(1 / t, 1 / (1 - t))`
puts the weight `t` on the coordinate `0`; the convention `A(t) = ∫ max((1 - t) q, t (1 - q)) dQ₂`
of [BGST04, (8.48)], [GS10] is the mirror image `t ↦ 1 - t`
(`HasSpectralMeasure.pickandsDependence_one_sub_eq_angular`).

## Main definitions and results

* `normTransport N H`, `lintegral_normTransport_of_isHomogeneous`, `ae_normTransport`,
  `normTransport_normTransport`: change of norm in polar coordinates.
* `simplexSpectralMeasure H`, `HasSpectralMeasure.simplex`, `ae_sum_simplexSpectralMeasure`,
  `lintegral_apply_simplexSpectralMeasure`, `simplexSpectralMeasure_univ`: the simplex spectral
  measure and its normalization.
* `simplexSpectralProb H`, `isProbabilityMeasure_simplexSpectralProb`,
  `maxStableExponent_eq_card_mul_simplexSpectralProb`: the probability normalization.
* `eq_of_lintegral_iSup_div_eq_of_simplex`: uniqueness on the simplex.
* `pickandsSpectral_simplexSpectralMeasure`, `pickandsAngularMeasure`,
  `HasSpectralMeasure.pickandsDependence_eq_angular`: the Pickands function on the simplex.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  §6.1 [dHF].
* J. Beirlant, Y. Goegebeur, J. Segers, J. Teugels, *Statistics of Extremes*, Wiley (2004),
  §8.2 [BGST04].
* G. Gudendorf and J. Segers, *Extreme-value copulas*, in Copula Theory and Its Applications,
  Springer (2010) [GS10].
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ExtremeValueTheory

variable {ι : Type*}

/-! ### Change of norm in polar coordinates -/

section Transport

/-- A function on `[0, ∞]^ι` is **positively homogeneous** if `g (c • w) = c * g w` for finite
`c`. -/
def IsHomogeneous (g : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  ∀ (c : ℝ≥0∞) (w : ι → ℝ≥0∞), c ≠ ∞ → g (c • w) = c * g w

/-- The **transport of `H` to the unit sphere of `N`**: the image of `N(w) dH(w)` under
`w ↦ w / N(w)`. -/
noncomputable def normTransport (N : (ι → ℝ≥0∞) → ℝ≥0∞) (H : Measure (ι → ℝ≥0∞)) :
    Measure (ι → ℝ≥0∞) :=
  (H.withDensity N).map fun w ↦ (N w)⁻¹ • w

variable {N N' : (ι → ℝ≥0∞) → ℝ≥0∞} {H : Measure (ι → ℝ≥0∞)}

lemma measurable_normalize (hN : Measurable N) : Measurable fun w : ι → ℝ≥0∞ ↦ (N w)⁻¹ • w :=
  Measurable.of_eval fun i ↦ hN.inv.mul (measurable_pi_apply i)

lemma lintegral_normTransport (hN : Measurable N) {g : (ι → ℝ≥0∞) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ v, g v ∂normTransport N H = ∫⁻ w, N w * g ((N w)⁻¹ • w) ∂H := by
  rw [normTransport, lintegral_map hg (measurable_normalize hN)]
  exact lintegral_withDensity_eq_lintegral_mul _ hN (hg.comp (measurable_normalize hN))

lemma normTransport_univ (hN : Measurable N) : normTransport N H univ = ∫⁻ w, N w ∂H := by
  rw [normTransport, Measure.map_apply (measurable_normalize hN) MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- **Change of norm preserves homogeneous integrals**: `∫ g dT_N H = ∫ g dH` for every
positively homogeneous `g`, when `N ∈ (0, ∞)` `H`-a.e. -/
theorem lintegral_normTransport_of_isHomogeneous (hN : Measurable N)
    (hH : ∀ᵐ w ∂H, N w ≠ 0 ∧ N w ≠ ∞) {g : (ι → ℝ≥0∞) → ℝ≥0∞} (hg : Measurable g)
    (hhom : IsHomogeneous g) : ∫⁻ v, g v ∂normTransport N H = ∫⁻ w, g w ∂H := by
  rw [lintegral_normTransport hN hg]
  refine lintegral_congr_ae (hH.mono fun w ⟨h0, htop⟩ ↦ ?_)
  dsimp only
  rw [hhom _ _ (ENNReal.inv_ne_top.2 h0), ENNReal.mul_inv_cancel_left h0 htop]

/-- The transport of `H` lives on the unit sphere `{N = 1}`. -/
theorem ae_normTransport (hN : Measurable N) (hNhom : IsHomogeneous N)
    (hH : ∀ᵐ w ∂H, N w ≠ 0 ∧ N w ≠ ∞) : ∀ᵐ v ∂normTransport N H, N v = 1 := by
  rw [normTransport, ae_map_iff (measurable_normalize hN).aemeasurable
    (measurableSet_eq_fun hN measurable_const)]
  refine (withDensity_absolutelyContinuous H N).ae_le (hH.mono fun w ⟨h0, htop⟩ ↦ ?_)
  rw [hNhom _ _ (ENNReal.inv_ne_top.2 h0), ENNReal.inv_mul_cancel h0 htop]

lemma isHomogeneous_mul_indicator (hNhom : IsHomogeneous N) (B : Set (ι → ℝ≥0∞)) :
    IsHomogeneous fun v ↦ N v * B.indicator 1 ((N v)⁻¹ • v) := by
  intro c v hc
  rcases eq_or_ne c 0 with rfl | hc0
  · have : N 0 = 0 := by simpa using hNhom 0 v ENNReal.zero_ne_top
    simp [this]
  dsimp only
  rw [hNhom c v hc, smul_smul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), mul_comm c⁻¹ (N v)⁻¹,
    mul_assoc (N v)⁻¹, ENNReal.inv_mul_cancel hc0 hc, mul_one, mul_assoc]

/-- **Transporting back recovers `H`**: if `H` lives on the sphere `{N' = 1}` and `N ∈ (0, ∞)`
`H`-a.e., then `T_{N'} (T_N H) = H`. -/
theorem normTransport_normTransport (hN : Measurable N) (hN' : Measurable N')
    (hN'hom : IsHomogeneous N') (hH : ∀ᵐ w ∂H, N w ≠ 0 ∧ N w ≠ ∞)
    (hH' : ∀ᵐ w ∂H, N' w = 1) : normTransport N' (normTransport N H) = H := by
  ext B hB
  have hg : Measurable fun v : ι → ℝ≥0∞ ↦ N' v * B.indicator 1 ((N' v)⁻¹ • v) :=
    hN'.mul ((measurable_one.indicator hB).comp (measurable_normalize hN'))
  rw [← lintegral_indicator_one hB, ← lintegral_indicator_one hB,
    lintegral_normTransport hN' (measurable_one.indicator hB),
    lintegral_normTransport_of_isHomogeneous hN hH hg (isHomogeneous_mul_indicator hN'hom B)]
  refine lintegral_congr_ae (hH'.mono fun w hw ↦ ?_)
  simp [hw]

end Transport

/-! ### The simplex spectral measure -/

section Simplex

variable [Fintype ι] {H : Measure (ι → ℝ≥0∞)}

lemma measurable_sum_apply : Measurable fun w : ι → ℝ≥0∞ ↦ ∑ i, w i :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

lemma measurable_iSup_apply : Measurable fun w : ι → ℝ≥0∞ ↦ ⨆ i, w i :=
  Measurable.iSup fun i ↦ measurable_pi_apply i

lemma isHomogeneous_sum : IsHomogeneous fun w : ι → ℝ≥0∞ ↦ ∑ i, w i := fun c w _ ↦ by
  simp [Finset.mul_sum]

omit [Fintype ι] in
lemma isHomogeneous_iSup : IsHomogeneous fun w : ι → ℝ≥0∞ ↦ ⨆ i, w i := fun c w _ ↦ by
  simp [ENNReal.mul_iSup]

omit [Fintype ι] in
lemma isHomogeneous_apply (i : ι) : IsHomogeneous fun w : ι → ℝ≥0∞ ↦ w i := fun c w _ ↦ by
  simp

omit [Fintype ι] in
lemma isHomogeneous_iSup_div (d : ι → ℝ≥0∞) :
    IsHomogeneous fun w : ι → ℝ≥0∞ ↦ ⨆ i, w i / d i := fun c w _ ↦ by
  simp [mul_div_assoc, ENNReal.mul_iSup]

/-- On the sup-norm sphere the sum norm is in `[1, |ι|]`, in particular in `(0, ∞)`. -/
lemma sum_ne_zero_ne_top_of_iSup_eq_one {w : ι → ℝ≥0∞} (hw : ⨆ i, w i = 1) :
    ∑ i, w i ≠ 0 ∧ ∑ i, w i ≠ ∞ := by
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · have : ⨆ i, w i ≤ ∑ i, w i :=
      iSup_le fun i ↦ Finset.single_le_sum (f := w) (fun _ _ ↦ zero_le) (Finset.mem_univ i)
    rw [hw, h0] at this
    exact absurd this (by simp)
  · exact ENNReal.sum_ne_top.2 fun i _ ↦
      ne_top_of_le_ne_top ENNReal.one_ne_top (hw ▸ le_iSup w i)

/-- On the simplex the sup norm is in `[1 / |ι|, 1]`, in particular in `(0, ∞)`. -/
lemma iSup_ne_zero_ne_top_of_sum_eq_one {v : ι → ℝ≥0∞} (hv : ∑ i, v i = 1) :
    ⨆ i, v i ≠ 0 ∧ ⨆ i, v i ≠ ∞ := by
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · have : ∀ i, v i = 0 := fun i ↦ le_antisymm (h0 ▸ le_iSup v i) zero_le
    simp [this] at hv
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun i ↦ ?_)
    rw [← hv]
    exact Finset.single_le_sum (f := v) (fun _ _ ↦ zero_le) (Finset.mem_univ i)

/-- The **simplex spectral measure**: the transport of `H` to the unit simplex
`{v | ∑_i v i = 1}`, i.e. the image of `(∑_i w i) dH(w)` under `w ↦ w / ∑_i w i`. -/
noncomputable def simplexSpectralMeasure (H : Measure (ι → ℝ≥0∞)) : Measure (ι → ℝ≥0∞) :=
  normTransport (fun w ↦ ∑ i, w i) H

/-- The transport of a measure on the simplex to the sup-norm sphere. -/
noncomputable def sphereSpectralMeasure (G : Measure (ι → ℝ≥0∞)) : Measure (ι → ℝ≥0∞) :=
  normTransport (fun w ↦ ⨆ i, w i) G

lemma ae_sum_ne_zero_ne_top (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    ∀ᵐ w ∂H, ∑ i, w i ≠ 0 ∧ ∑ i, w i ≠ ∞ :=
  hH.mono fun _ hw ↦ sum_ne_zero_ne_top_of_iSup_eq_one hw

/-- For `H` on the sup-norm sphere, `∫ g dH_Δ = ∫ g dH` for every positively homogeneous `g`. -/
theorem lintegral_simplexSpectralMeasure (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    {g : (ι → ℝ≥0∞) → ℝ≥0∞} (hg : Measurable g) (hhom : IsHomogeneous g) :
    ∫⁻ v, g v ∂simplexSpectralMeasure H = ∫⁻ w, g w ∂H :=
  lintegral_normTransport_of_isHomogeneous measurable_sum_apply (ae_sum_ne_zero_ne_top hH) hg hhom

/-- The simplex spectral measure lives on the simplex `{v | ∑_i v i = 1}`. -/
theorem ae_sum_simplexSpectralMeasure (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    ∀ᵐ v ∂simplexSpectralMeasure H, ∑ i, v i = 1 :=
  ae_normTransport measurable_sum_apply isHomogeneous_sum (ae_sum_ne_zero_ne_top hH)

/-- The marginal normalization is preserved: `∫ v i dH_Δ = ∫ w i dH`. -/
theorem lintegral_apply_simplexSpectralMeasure (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) (i : ι) :
    ∫⁻ v, v i ∂simplexSpectralMeasure H = ∫⁻ w, w i ∂H :=
  lintegral_simplexSpectralMeasure hH (measurable_pi_apply i) (isHomogeneous_apply i)

/-- The spectral integrals are preserved: `∫ max_i v i / d i dH_Δ = ∫ max_i w i / d i dH`. -/
theorem lintegral_iSup_div_simplexSpectralMeasure (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (d : ι → ℝ≥0∞) :
    ∫⁻ v, ⨆ i, v i / d i ∂simplexSpectralMeasure H = ∫⁻ w, ⨆ i, w i / d i ∂H :=
  lintegral_simplexSpectralMeasure hH (Measurable.iSup fun i ↦ (measurable_pi_apply i).div_const _)
    (isHomogeneous_iSup_div d)

/-- The total mass of the simplex spectral measure is `∑_i ∫ w i dH`; it is `|ι|` for a
normalized `H`. -/
theorem simplexSpectralMeasure_univ (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    simplexSpectralMeasure H univ = ∑ i, ∫⁻ w, w i ∂H := by
  have h1 : simplexSpectralMeasure H univ = ∫⁻ v, ∑ i, v i ∂simplexSpectralMeasure H := by
    rw [← lintegral_one]
    refine (lintegral_congr_ae ((ae_sum_simplexSpectralMeasure hH).mono fun v hv ↦ ?_)).symm
    exact hv
  rw [h1, lintegral_simplexSpectralMeasure hH measurable_sum_apply isHomogeneous_sum,
    lintegral_finsetSum _ fun i _ ↦ measurable_pi_apply i]

theorem simplexSpectralMeasure_univ_of_normalized (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hnorm : ∀ i, ∫⁻ w, w i ∂H = 1) : simplexSpectralMeasure H univ = Fintype.card ι := by
  simp [simplexSpectralMeasure_univ hH, hnorm]

theorem isFiniteMeasure_simplexSpectralMeasure [IsFiniteMeasure H]
    (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) : IsFiniteMeasure (simplexSpectralMeasure H) := by
  refine ⟨?_⟩
  rw [simplexSpectralMeasure_univ hH]
  exact ENNReal.sum_lt_top.2 fun i _ ↦
    (lintegral_apply_ne_top_of_le_one (ae_le_one_of_ae_iSup_eq_one hH) i).lt_top

/-- **The simplex spectral measure is a spectral measure**: if `ν` has spectral measure `H` on
the sup-norm sphere, then `P(Y ≤ y) = exp (-∫ max_i v i / y i dH_Δ(v))`. -/
theorem HasSpectralMeasure.simplex {ν : Measure (ι → ℝ)} (hν : HasSpectralMeasure ν H)
    (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) : HasSpectralMeasure ν (simplexSpectralMeasure H) := by
  intro y hy
  rw [hν y hy, lintegral_iSup_div_simplexSpectralMeasure hH]

/-- **Uniqueness on the simplex**: two finite measures on the simplex `{v | ∑_i v i = 1}` with the
same spectral integrals `∫ max_i v i / y i`, `y ∈ (0, ∞)^ι`, are equal. -/
theorem eq_of_lintegral_iSup_div_eq_of_simplex {G G' : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure G]
    [IsFiniteMeasure G'] (hG : ∀ᵐ v ∂G, ∑ i, v i = 1) (hG' : ∀ᵐ v ∂G', ∑ i, v i = 1)
    (heq : ∀ y : ι → ℝ, (∀ i, 0 < y i) →
      ∫⁻ v, ⨆ i, v i / ENNReal.ofReal (y i) ∂G = ∫⁻ v, ⨆ i, v i / ENNReal.ofReal (y i) ∂G') :
    G = G' := by
  have hs := hG.mono fun _ hv ↦ iSup_ne_zero_ne_top_of_sum_eq_one hv
  have hs' := hG'.mono fun _ hv ↦ iSup_ne_zero_ne_top_of_sum_eq_one hv
  have hfin {F : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure F] (hF : ∀ᵐ v ∂F, ∑ i, v i = 1) :
      IsFiniteMeasure (sphereSpectralMeasure F) := by
    refine ⟨?_⟩
    rw [sphereSpectralMeasure, normTransport_univ measurable_iSup_apply]
    refine lt_of_le_of_lt (lintegral_mono_ae (g := fun _ ↦ 1) (hF.mono fun v hv ↦ ?_)) ?_
    · exact iSup_le fun i ↦
        hv ▸ Finset.single_le_sum (f := v) (fun _ _ ↦ zero_le) (Finset.mem_univ i)
    · rw [lintegral_one]; exact measure_lt_top F univ
  have := hfin hG
  have := hfin hG'
  have hS : sphereSpectralMeasure G = sphereSpectralMeasure G' := by
    refine eq_of_lintegral_iSup_div_eq
      (ae_normTransport measurable_iSup_apply isHomogeneous_iSup hs)
      (ae_normTransport measurable_iSup_apply isHomogeneous_iSup hs') fun y hy ↦ ?_
    have hmeas : Measurable fun w : ι → ℝ≥0∞ ↦ ⨆ i, w i / ENNReal.ofReal (y i) :=
      Measurable.iSup fun i ↦ (measurable_pi_apply i).div_const _
    rw [sphereSpectralMeasure, sphereSpectralMeasure,
      lintegral_normTransport_of_isHomogeneous measurable_iSup_apply hs hmeas
        (isHomogeneous_iSup_div _),
      lintegral_normTransport_of_isHomogeneous measurable_iSup_apply hs' hmeas
        (isHomogeneous_iSup_div _), heq y hy]
  rw [← normTransport_normTransport measurable_iSup_apply measurable_sum_apply isHomogeneous_sum
      hs hG, ← normTransport_normTransport measurable_iSup_apply measurable_sum_apply
      isHomogeneous_sum hs' hG']
  exact congrArg (normTransport _) hS

/-- The **probability-normalized simplex spectral measure** `Q = H_Δ / |ι|`. -/
noncomputable def simplexSpectralProb (H : Measure (ι → ℝ≥0∞)) : Measure (ι → ℝ≥0∞) :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • simplexSpectralMeasure H

theorem isProbabilityMeasure_simplexSpectralProb [Nonempty ι] (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hnorm : ∀ i, ∫⁻ w, w i ∂H = 1) : IsProbabilityMeasure (simplexSpectralProb H) := by
  refine ⟨?_⟩
  rw [simplexSpectralProb, Measure.smul_apply, simplexSpectralMeasure_univ_of_normalized hH hnorm,
    smul_eq_mul, ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _)]

theorem lintegral_apply_simplexSpectralProb (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hnorm : ∀ i, ∫⁻ w, w i ∂H = 1) (i : ι) :
    ∫⁻ v, v i ∂simplexSpectralProb H = (Fintype.card ι : ℝ≥0∞)⁻¹ := by
  rw [simplexSpectralProb, lintegral_smul_measure, lintegral_apply_simplexSpectralMeasure hH,
    hnorm, smul_eq_mul, mul_one]

/-- With the probability normalization, `V(y) = |ι| ∫ max_i v i / y i dQ(v)`. -/
theorem maxStableExponent_eq_card_mul_simplexSpectralProb {ν : Measure (ι → ℝ)} [Nonempty ι]
    (hν : HasSpectralMeasure ν H) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    maxStableExponent ν y =
      Fintype.card ι * (∫⁻ v, ⨆ i, v i / ENNReal.ofReal (y i) ∂simplexSpectralProb H).toReal := by
  rw [hν.simplex hH |>.maxStableExponent_eq hy, simplexSpectralProb, lintegral_smul_measure,
    smul_eq_mul, ENNReal.toReal_mul, ← mul_assoc, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_inv_cancel₀ (by simp), one_mul]

end Simplex

/-! ### The Pickands function on the simplex -/

section Pickands

variable {H : Measure (Fin 2 → ℝ≥0∞)}

lemma isHomogeneous_pickandsIntegrand (s r : ℝ) :
    IsHomogeneous fun w : Fin 2 → ℝ≥0∞ ↦ max (ENNReal.ofReal s * w 0) (ENNReal.ofReal r * w 1) :=
  fun c w _ ↦ by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, mul_left_comm (ENNReal.ofReal r)]
    exact (Monotone.map_max (f := (c * ·)) fun _ _ h ↦ mul_le_mul_right h c).symm

/-- The spectral Pickands function is the same on the sphere and on the simplex. -/
theorem pickandsSpectral_simplexSpectralMeasure (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) (t : ℝ) :
    pickandsSpectral (simplexSpectralMeasure H) t = pickandsSpectral H t := by
  rw [pickandsSpectral, pickandsSpectral, lintegral_simplexSpectralMeasure hH
    (measurable_pickandsIntegrand t (1 - t)) (isHomogeneous_pickandsIntegrand t (1 - t))]

/-- The **angular measure on `[0, 1]`** of a bivariate spectral measure: the image of the simplex
spectral measure under `v ↦ v 0`. -/
noncomputable def pickandsAngularMeasure (H : Measure (Fin 2 → ℝ≥0∞)) : Measure ℝ :=
  (simplexSpectralMeasure H).map fun v ↦ (v 0).toReal

lemma measurable_toReal_apply_zero : Measurable fun v : Fin 2 → ℝ≥0∞ ↦ (v 0).toReal :=
  ENNReal.measurable_toReal.comp (measurable_pi_apply 0)

/-- On the simplex, `v 0 = q` and `v 1 = 1 - q` with `q = (v 0).toReal ∈ [0, 1]`. -/
lemma simplex_coord {v : Fin 2 → ℝ≥0∞} (hv : ∑ i, v i = 1) :
    ENNReal.ofReal (v 0).toReal = v 0 ∧ ENNReal.ofReal (1 - (v 0).toReal) = v 1 ∧
      (v 0).toReal ∈ Icc (0 : ℝ) 1 := by
  rw [Fin.sum_univ_two] at hv
  have h0 : v 0 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hv ▸ le_self_add)
  have h1 : v 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hv ▸ le_add_self)
  have hr : (v 0).toReal + (v 1).toReal = 1 := by
    rw [← ENNReal.toReal_add h0 h1, hv, ENNReal.toReal_one]
  refine ⟨ENNReal.ofReal_toReal h0, ?_, ENNReal.toReal_nonneg, ?_⟩
  · rw [show 1 - (v 0).toReal = (v 1).toReal by linarith, ENNReal.ofReal_toReal h1]
  · linarith [ENNReal.toReal_nonneg (a := v 1)]

theorem ae_pickandsAngularMeasure (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    ∀ᵐ q ∂pickandsAngularMeasure H, q ∈ Icc (0 : ℝ) 1 := by
  rw [pickandsAngularMeasure]
  refine (ae_map_iff measurable_toReal_apply_zero.aemeasurable (p := fun q ↦ q ∈ Icc (0 : ℝ) 1)
    measurableSet_Icc).2 ?_
  exact (ae_sum_simplexSpectralMeasure hH).mono fun v hv ↦ (simplex_coord hv).2.2

/-- The angular measure has mass `2` and mean `1` for a normalized `H`. -/
theorem pickandsAngularMeasure_univ (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hnorm : ∀ i, ∫⁻ w, w i ∂H = 1) : pickandsAngularMeasure H univ = 2 := by
  rw [pickandsAngularMeasure, Measure.map_apply measurable_toReal_apply_zero MeasurableSet.univ,
    preimage_univ, simplexSpectralMeasure_univ_of_normalized hH hnorm]
  simp

theorem lintegral_pickandsAngularMeasure (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hnorm : ∀ i, ∫⁻ w, w i ∂H = 1) :
    ∫⁻ q, ENNReal.ofReal q ∂pickandsAngularMeasure H = 1 := by
  rw [pickandsAngularMeasure, lintegral_map ENNReal.measurable_ofReal
    measurable_toReal_apply_zero, ← hnorm 0, ← lintegral_apply_simplexSpectralMeasure hH 0]
  exact lintegral_congr_ae ((ae_sum_simplexSpectralMeasure hH).mono fun v hv ↦
    (simplex_coord hv).1)

/-- **The Pickands function in the simplex parametrization**: for a law with a normalized spectral
measure `H` on the sup-norm sphere, `A(t) = ∫ max(t q, (1 - t)(1 - q)) dQ₂(q)` on `[0, 1]`, where
`Q₂ = pickandsAngularMeasure H` has mass `2` and mean `1`. -/
theorem HasSpectralMeasure.pickandsDependence_eq_angular {ν : Measure (Fin 2 → ℝ)}
    (hν : HasSpectralMeasure ν H) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hnorm : ∀ i, ∫⁻ w, w i ∂H = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pickandsDependence ν t = (∫⁻ q, max (ENNReal.ofReal t * ENNReal.ofReal q)
      (ENNReal.ofReal (1 - t) * ENNReal.ofReal (1 - q)) ∂pickandsAngularMeasure H).toReal := by
  rw [hν.pickandsDependence_eq hnorm ht, ← pickandsSpectral_simplexSpectralMeasure hH,
    pickandsSpectral, pickandsAngularMeasure, lintegral_map _ measurable_toReal_apply_zero]
  · congr 1
    refine lintegral_congr_ae ((ae_sum_simplexSpectralMeasure hH).mono fun v hv ↦ ?_)
    obtain ⟨h0, h1, -⟩ := simplex_coord hv
    dsimp only
    rw [h0, h1]
  · exact (measurable_const.mul ENNReal.measurable_ofReal).max
      (measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)))

/-- The mirrored convention of [BGST04, (8.48)] and [GS10], with the weight `t` on the second
coordinate: `A(1 - t) = ∫ max((1 - t) q, t (1 - q)) dQ₂(q)`. -/
theorem HasSpectralMeasure.pickandsDependence_one_sub_eq_angular {ν : Measure (Fin 2 → ℝ)}
    (hν : HasSpectralMeasure ν H) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    (hnorm : ∀ i, ∫⁻ w, w i ∂H = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pickandsDependence ν (1 - t) = (∫⁻ q, max (ENNReal.ofReal (1 - t) * ENNReal.ofReal q)
      (ENNReal.ofReal t * ENNReal.ofReal (1 - q)) ∂pickandsAngularMeasure H).toReal := by
  rw [hν.pickandsDependence_eq_angular hH hnorm ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    sub_sub_cancel]

end Pickands

end ExtremeValueTheory
