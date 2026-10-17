/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.Dependence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Probability.CDF

/-!
# The upper tail dependence coefficient

For a random vector `(X, Y)` with distribution functions `F` and `G`, the **upper tail dependence
coefficient** is

  `λ_U = lim_{u ↑ 1} P(G(Y) > u | F(X) > u)`

when the limit exists ([BGST04, §9.2]; [Col01, §8.4]; Sibuya 1960; Joe 1997). `λ_U = 0` is
asymptotic independence, `λ_U > 0` asymptotic dependence.

For a bivariate simple max-stable law (unit Fréchet margins) with extremal coefficient
`θ = V(1, 1)` and Pickands function `A`,

  `λ_U = 2 - θ = 2 (1 - A(1 / 2))`,

since `P(F(X) > u, G(Y) > u) = 1 - 2 u + u ^ θ` and `(1 - 2 u + u ^ θ) / (1 - u) → 2 - θ`.
Independence gives `λ_U = 0`, complete dependence `λ_U = 1`.

For a regularly varying vector `(X₁, X₂)` with exponent measure `μ` (`IsRegVarVector`, with the
sup norm of `ℝ × ℝ`), the threshold form of the coefficient is

  `P(X₂ > x | X₁ > x) → μ {y₁ > 1, y₂ > 1} / μ {y₁ > 1}`,

and when the margins are tail-equivalent (`P(X₂ > x) / P(X₁ > x) → 1`) one has
`μ {y₂ > 1} = μ {y₁ > 1}`, so that the limit is symmetric in the two coordinates
([Res07, §6.5]; [BGST04, §9.2]).

## Main definitions and results

* `tailDependenceRatio P X Y u = P(F(X) > u, G(Y) > u) / P(F(X) > u)`, with `F, G` the
  distribution functions (`ProbabilityTheory.cdf`) of `X, Y`.
* `HasUpperTailDependence P X Y l`: `tailDependenceRatio P X Y u → l` as `u ↑ 1`;
  `HasUpperTailDependence.unique`.
* `IsSimpleMaxStable.tailDependenceRatio_eq`: `(1 - 2 u + u ^ θ) / (1 - u)`.
* `IsSimpleMaxStable.hasUpperTailDependence`: `λ_U = 2 - θ`;
  `IsSimpleMaxStable.hasUpperTailDependence_pickands`: `λ_U = 2 (1 - A(1 / 2))`;
  `IsSimpleMaxStable.two_sub_extremalCoefficient_mem_Icc`: `λ_U ∈ [0, 1]`.
* `IsSimpleMaxStable.hasUpperTailDependence_zero_of_measure_Iic_eq_mul`,
  `IsSimpleMaxStable.hasUpperTailDependence_one_of_measure_Iic_eq_min`, and the spectral examples
  `hasUpperTailDependence_map_spectralVector_independent`,
  `hasUpperTailDependence_map_spectralVector_comonotone`: `λ_U = 0` and `λ_U = 1`.
* `IsRegVarVector.tendsto_condProb_gt_gt`: the regularly varying case.
* `IsRegVarVector.measureReal_snd_eq_fst_of_tailEquiv`: tail-equivalent margins have equal
  marginal exponent masses.

The quantile form `λ_U` of a regularly varying vector with tail-equivalent margins (rather than
the threshold form above) would need the asymptotic inversion of the marginal distribution
functions, which is not formalized.

## References

* J. Beirlant, Y. Goegebeur, J. Segers, J. Teugels, *Statistics of Extremes*, Wiley (2004),
  Chapters 8–9 [BGST04].
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 8 [Col01].
* S. I. Resnick, *Heavy-Tail Phenomena*, Springer (2007), Chapter 6 [Res07].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Definition -/

section Definition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The ratio `P(F(X) > u, G(Y) > u) / P(F(X) > u) = P(G(Y) > u | F(X) > u)`, where `F` and `G`
are the distribution functions of `X` and `Y`. -/
noncomputable def tailDependenceRatio (P : Measure Ω) (X Y : Ω → ℝ) (u : ℝ) : ℝ :=
  P.real {ω | u < cdf (P.map X) (X ω) ∧ u < cdf (P.map Y) (Y ω)} /
    P.real {ω | u < cdf (P.map X) (X ω)}

/-- `(X, Y)` has **upper tail dependence coefficient** `l`:
`P(G(Y) > u | F(X) > u) → l` as `u ↑ 1`. -/
def HasUpperTailDependence (P : Measure Ω) (X Y : Ω → ℝ) (l : ℝ) : Prop :=
  Tendsto (tailDependenceRatio P X Y) (𝓝[<] 1) (𝓝 l)

/-- The upper tail dependence coefficient is unique. -/
theorem HasUpperTailDependence.unique {P : Measure Ω} {X Y : Ω → ℝ} {l l' : ℝ}
    (h : HasUpperTailDependence P X Y l) (h' : HasUpperTailDependence P X Y l') : l = l' :=
  tendsto_nhds_unique h h'

end Definition

/-! ### Max-stable laws -/

/-- `(1 - 2 u + u ^ θ) / (1 - u) → 2 - θ` as `u ↑ 1`. -/
lemma tendsto_one_sub_two_mul_add_rpow_div (θ : ℝ) :
    Tendsto (fun u : ℝ ↦ (1 - 2 * u + u ^ θ) / (1 - u)) (𝓝[<] 1) (𝓝 (2 - θ)) := by
  have hd := Real.hasDerivAt_rpow_const (x := 1) (p := θ) (Or.inl one_ne_zero)
  rw [Real.one_rpow, mul_one] at hd
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono _ fun x (hx : x < 1) ↦ hx.ne)
  refine (tendsto_const_nhds (x := (2 : ℝ))).sub hs |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : u < 1)
  have h1 : u - 1 ≠ 0 := sub_ne_zero.2 hu.ne
  have h2 : 1 - u ≠ 0 := sub_ne_zero.2 hu.ne'
  rw [slope_def_field, Real.one_rpow]
  field_simp
  ring

namespace IsSimpleMaxStable

variable {μ : Measure (Fin 2 → ℝ)}

/-- The marginal distribution functions of a simple max-stable law are unit Fréchet. -/
lemma cdf_map_apply (h : IsSimpleMaxStable μ) (i : Fin 2) {x : ℝ} (hx : 0 < x) :
    cdf (μ.map fun z ↦ z i) x = Real.exp (-x⁻¹) := by
  have := h.isProbabilityMeasure
  rw [cdf_eq_real, measureReal_def, Measure.map_apply (measurable_pi_apply i) measurableSet_Iic]
  rw [show (fun z : Fin 2 → ℝ ↦ z i) ⁻¹' Iic x = {z | z i ≤ x} from rfl, h.measure_le i x hx,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- The quantile of unit Fréchet: `exp (-1 / z) = u` for `z = -1 / log u`. -/
lemma exp_neg_inv_neg_inv_log {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Real.exp (-(-(Real.log u)⁻¹)⁻¹) = u := by
  rw [inv_neg, inv_inv, neg_neg, Real.exp_log hu.1]

lemma neg_inv_log_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < -(Real.log u)⁻¹ :=
  neg_pos.2 (inv_lt_zero.2 (Real.log_neg hu.1 hu.2))

/-- `F(x) > u` iff `x > -1 / log u` for unit Fréchet margins. -/
lemma lt_cdf_map_iff (h : IsSimpleMaxStable μ) (i : Fin 2) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (x : ℝ) : u < cdf (μ.map fun z ↦ z i) x ↔ -(Real.log u)⁻¹ < x := by
  set z := -(Real.log u)⁻¹ with hz
  have hz0 : 0 < z := neg_inv_log_pos hu
  have hcz : cdf (μ.map fun z ↦ z i) z = u := by
    rw [h.cdf_map_apply i hz0, hz, exp_neg_inv_neg_inv_log hu]
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    exact absurd ((monotone_cdf _ hle).trans_eq hcz) (not_le.2 hlt)
  · intro hzx
    have hx : 0 < x := hz0.trans hzx
    rw [h.cdf_map_apply i hx, ← hcz, h.cdf_map_apply i hz0]
    exact Real.exp_lt_exp.2 (neg_lt_neg ((inv_lt_inv₀ hx hz0).2 hzx))

/-- **Joint exceedances of a max-stable law**:
`P(G(Y) > u | F(X) > u) = (1 - 2 u + u ^ θ) / (1 - u)` for `0 < u < 1`. -/
theorem tailDependenceRatio_eq (h : IsSimpleMaxStable μ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    tailDependenceRatio μ (fun z ↦ z 0) (fun z ↦ z 1) u =
      (1 - 2 * u + u ^ extremalCoefficient μ) / (1 - u) := by
  have := h.isProbabilityMeasure
  set z := -(Real.log u)⁻¹ with hz
  have hz0 : 0 < z := neg_inv_log_pos hu
  have hm (i : Fin 2) : MeasurableSet {x : Fin 2 → ℝ | x i ≤ z} :=
    measurableSet_le (measurable_pi_apply i) measurable_const
  have hA (i : Fin 2) : μ.real {x : Fin 2 → ℝ | x i ≤ z} = u := by
    rw [measureReal_def, h.measure_le i z hz0, ENNReal.toReal_ofReal (Real.exp_pos _).le, hz,
      exp_neg_inv_neg_inv_log hu]
  have hinter : {x : Fin 2 → ℝ | x 0 ≤ z} ∩ {x | x 1 ≤ z} = Iic fun _ ↦ z := by
    ext x; simp [Pi.le_def, Fin.forall_fin_two]
  have hnum : {x : Fin 2 → ℝ | u < cdf (μ.map fun z ↦ z 0) (x 0) ∧
      u < cdf (μ.map fun z ↦ z 1) (x 1)} = ({x | x 0 ≤ z} ∪ {x | x 1 ≤ z})ᶜ := by
    ext x
    simp only [mem_ofPred_eq, h.lt_cdf_map_iff 0 hu, h.lt_cdf_map_iff 1 hu, ← hz, mem_compl_iff,
      mem_union, not_or, not_le]
  have hden : {x : Fin 2 → ℝ | u < cdf (μ.map fun z ↦ z 0) (x 0)} = {x | x 0 ≤ z}ᶜ := by
    ext x
    simp only [mem_ofPred_eq, h.lt_cdf_map_iff 0 hu, ← hz, mem_compl_iff, not_le]
  have hunion := measureReal_union_add_inter (μ := μ) (s := {x : Fin 2 → ℝ | x 0 ≤ z}) (hm 1)
  rw [hinter, h.measureReal_Iic_const hz0, hz, exp_neg_inv_neg_inv_log hu, ← hz, hA, hA] at hunion
  rw [tailDependenceRatio, hnum, hden, probReal_compl_eq_one_sub ((hm 0).union (hm 1)),
    probReal_compl_eq_one_sub (hm 0), hA]
  congr 1
  linarith

/-- **Tail dependence of max-stable laws**: `λ_U = 2 - θ`, with `θ = V(1, 1)` the extremal
coefficient. -/
theorem hasUpperTailDependence (h : IsSimpleMaxStable μ) :
    HasUpperTailDependence μ (fun z ↦ z 0) (fun z ↦ z 1) (2 - extremalCoefficient μ) :=
  (tendsto_one_sub_two_mul_add_rpow_div _).congr' <| by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with u hu
    exact (h.tailDependenceRatio_eq hu).symm

/-- **Tail dependence and the Pickands function**: `λ_U = 2 (1 - A(1 / 2))`. -/
theorem hasUpperTailDependence_pickands (h : IsSimpleMaxStable μ) :
    HasUpperTailDependence μ (fun z ↦ z 0) (fun z ↦ z 1)
      (2 * (1 - pickandsDependence μ (1 / 2))) := by
  have := h.hasUpperTailDependence
  rwa [h.extremalCoefficient_eq_two_mul_pickands, show 2 - 2 * pickandsDependence μ (1 / 2) =
    2 * (1 - pickandsDependence μ (1 / 2)) by ring] at this

/-- `λ_U = 2 - θ ∈ [0, 1]`. -/
theorem two_sub_extremalCoefficient_mem_Icc (h : IsSimpleMaxStable μ) :
    2 - extremalCoefficient μ ∈ Icc (0 : ℝ) 1 := by
  have h1 := h.one_le_extremalCoefficient
  have h2 := h.extremalCoefficient_le_card
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h2
  constructor <;> linarith

/-- **Independence**: `λ_U = 0`. -/
theorem hasUpperTailDependence_zero_of_measure_Iic_eq_mul (h : IsSimpleMaxStable μ)
    (hind : ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
      μ (Iic y) = ENNReal.ofReal (Real.exp (-(y 0)⁻¹)) * ENNReal.ofReal (Real.exp (-(y 1)⁻¹))) :
    HasUpperTailDependence μ (fun z ↦ z 0) (fun z ↦ z 1) 0 := by
  have := h.hasUpperTailDependence_pickands
  rwa [pickandsDependence_eq_one_of_measure_Iic_eq_mul hind, sub_self, mul_zero] at this

/-- **Complete dependence**: `λ_U = 1`. -/
theorem hasUpperTailDependence_one_of_measure_Iic_eq_min (h : IsSimpleMaxStable μ)
    (hcom : ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
      μ (Iic y) = min (ENNReal.ofReal (Real.exp (-(y 0)⁻¹)))
        (ENNReal.ofReal (Real.exp (-(y 1)⁻¹)))) :
    HasUpperTailDependence μ (fun z ↦ z 0) (fun z ↦ z 1) 1 := by
  have := h.hasUpperTailDependence_pickands
  rw [pickandsDependence_eq_max_of_measure_Iic_eq_min hcom (by norm_num)] at this
  convert this using 2
  norm_num

end IsSimpleMaxStable

section Examples

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {N : Ω → Measure (ℝ × (Fin 2 → ℝ≥0∞))}

/-- The independent spectral example has `λ_U = 0`. -/
theorem hasUpperTailDependence_map_spectralVector_independent
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod independentSpectralMeasure) P) :
    HasUpperTailDependence (P.map fun ω ↦ spectralVector (fun i w ↦ w i) (N ω))
      (fun z ↦ z 0) (fun z ↦ z 1) 0 := by
  have h := hN.isSimpleMaxStable_map_spectralVector (fun i ↦ measurable_pi_apply i)
    lintegral_apply_independentSpectralMeasure
  have := h.hasUpperTailDependence_pickands
  rwa [pickandsDependence_map_spectralVector_independent hN, sub_self, mul_zero] at this

/-- The comonotone spectral example has `λ_U = 1`. -/
theorem hasUpperTailDependence_map_spectralVector_comonotone
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod comonotoneSpectralMeasure) P) :
    HasUpperTailDependence (P.map fun ω ↦ spectralVector (fun i w ↦ w i) (N ω))
      (fun z ↦ z 0) (fun z ↦ z 1) 1 := by
  have h := hN.isSimpleMaxStable_map_spectralVector (fun i ↦ measurable_pi_apply i)
    lintegral_apply_comonotoneSpectralMeasure
  have := h.hasUpperTailDependence_pickands
  rw [pickandsDependence_map_spectralVector_comonotone hN (by norm_num)] at this
  convert this using 2
  norm_num

end Examples

/-! ### Regularly varying vectors -/

section RegVar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X₁ X₂ : Ω → ℝ} {α : ℝ} {μ : Measure (ℝ × ℝ)}

omit [IsFiniteMeasure P] in
lemma IsRegVarVector.measure_fst_eq (h : IsRegVarVector P (fun ω ↦ (X₁ ω, X₂ ω)) α μ) :
    μ {y : ℝ × ℝ | 1 = y.1} = 0 := by
  simpa [eq_comm] using h.measure_level_eq_zero (ψ := Prod.fst) measurable_fst
    (fun _ _ y ↦ by simp) one_pos (by norm_num : (0 : ℝ) < 1 / 4) fun y hy ↦ by
      have := norm_fst_le y
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self y.1]

omit [IsFiniteMeasure P] in
lemma IsRegVarVector.measure_snd_eq (h : IsRegVarVector P (fun ω ↦ (X₁ ω, X₂ ω)) α μ) :
    μ {y : ℝ × ℝ | 1 = y.2} = 0 := by
  simpa [eq_comm] using h.measure_level_eq_zero (ψ := Prod.snd) measurable_snd
    (fun _ _ y ↦ by simp) one_pos (by norm_num : (0 : ℝ) < 1 / 4) fun y hy ↦ by
      have := norm_snd_le y
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self y.2]

lemma one_lt_inv_mul_iff {x a : ℝ} (hx : 0 < x) : 1 < x⁻¹ * a ↔ x < a := by
  rw [lt_inv_mul_iff₀ hx, mul_one]

/-- The marginal limits `P(X i > x) / P(‖X‖ > x) → μ {y i > 1}`. -/
lemma IsRegVarVector.tendsto_fst (h : IsRegVarVector P (fun ω ↦ (X₁ ω, X₂ ω)) α μ)
    (h₁ : Measurable X₁) (h₂ : Measurable X₂) :
    Tendsto (fun x ↦ P.real {ω | x < X₁ ω} / P.real {ω | x < ‖(X₁ ω, X₂ ω)‖}) atTop
      (𝓝 (μ.real {y | 1 < y.1})) := by
  have key := h.tendsto_measureReal (h₁.prodMk h₂) (A := {y : ℝ × ℝ | 1 < y.1})
    (measurableSet_lt measurable_const measurable_fst) one_pos
    (fun y (hy : 1 < y.1) ↦ (hy.le.trans (le_abs_self _)).trans
      (Real.norm_eq_abs y.1 ▸ norm_fst_le y))
    (measure_mono_null (frontier_lt_subset_eq continuous_const continuous_fst) h.measure_fst_eq)
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Prod.smul_fst, smul_eq_mul, one_lt_inv_mul_iff hx]

lemma IsRegVarVector.tendsto_snd (h : IsRegVarVector P (fun ω ↦ (X₁ ω, X₂ ω)) α μ)
    (h₁ : Measurable X₁) (h₂ : Measurable X₂) :
    Tendsto (fun x ↦ P.real {ω | x < X₂ ω} / P.real {ω | x < ‖(X₁ ω, X₂ ω)‖}) atTop
      (𝓝 (μ.real {y | 1 < y.2})) := by
  have key := h.tendsto_measureReal (h₁.prodMk h₂) (A := {y : ℝ × ℝ | 1 < y.2})
    (measurableSet_lt measurable_const measurable_snd) one_pos
    (fun y (hy : 1 < y.2) ↦ (hy.le.trans (le_abs_self _)).trans
      (Real.norm_eq_abs y.2 ▸ norm_snd_le y))
    (measure_mono_null (frontier_lt_subset_eq continuous_const continuous_snd) h.measure_snd_eq)
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Prod.smul_snd, smul_eq_mul, one_lt_inv_mul_iff hx]

lemma IsRegVarVector.tendsto_fst_snd (h : IsRegVarVector P (fun ω ↦ (X₁ ω, X₂ ω)) α μ)
    (h₁ : Measurable X₁) (h₂ : Measurable X₂) :
    Tendsto (fun x ↦ P.real {ω | x < X₁ ω ∧ x < X₂ ω} / P.real {ω | x < ‖(X₁ ω, X₂ ω)‖})
      atTop (𝓝 (μ.real {y | 1 < y.1 ∧ 1 < y.2})) := by
  have hfr : frontier {y : ℝ × ℝ | 1 < y.1 ∧ 1 < y.2} ⊆ {y | 1 = y.1} ∪ {y | 1 = y.2} := by
    rw [show {y : ℝ × ℝ | 1 < y.1 ∧ 1 < y.2} = {y | 1 < y.1} ∩ {y | 1 < y.2} from rfl]
    refine (frontier_inter_subset _ _).trans (union_subset_union ?_ ?_)
    · exact inter_subset_left.trans (frontier_lt_subset_eq continuous_const continuous_fst)
    · exact inter_subset_right.trans (frontier_lt_subset_eq continuous_const continuous_snd)
  have key := h.tendsto_measureReal (h₁.prodMk h₂) (A := {y : ℝ × ℝ | 1 < y.1 ∧ 1 < y.2})
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)) one_pos
    (fun y (hy : 1 < y.1 ∧ 1 < y.2) ↦ (hy.1.le.trans (le_abs_self _)).trans
      (Real.norm_eq_abs y.1 ▸ norm_fst_le y))
    (measure_mono_null hfr (measure_union_null h.measure_fst_eq h.measure_snd_eq))
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, one_lt_inv_mul_iff hx]

/-- **Tail dependence of regularly varying vectors** (threshold form): if `X = (X₁, X₂)` is
regularly varying with exponent measure `μ` and `μ {y₁ > 1} ≠ 0`, then
`P(X₂ > x | X₁ > x) → μ {y₁ > 1, y₂ > 1} / μ {y₁ > 1}`. -/
theorem IsRegVarVector.tendsto_condProb_gt_gt
    (h : IsRegVarVector P (fun ω ↦ (X₁ ω, X₂ ω)) α μ) (h₁ : Measurable X₁) (h₂ : Measurable X₂)
    (hμ : μ.real {y | 1 < y.1} ≠ 0) :
    Tendsto (fun x ↦ P.real {ω | x < X₁ ω ∧ x < X₂ ω} / P.real {ω | x < X₁ ω}) atTop
      (𝓝 (μ.real {y | 1 < y.1 ∧ 1 < y.2} / μ.real {y | 1 < y.1})) := by
  refine ((h.tendsto_fst_snd h₁ h₂).div (h.tendsto_fst h₁ h₂) hμ).congr' ?_
  filter_upwards [h.isRegularlyVarying.eventually_pos] with x hx
  exact div_div_div_cancel_right₀ hx.ne' _ _

/-- **Tail-equivalent margins**: if `P(X₂ > x) / P(X₁ > x) → 1`, then the marginal exponent
masses agree, `μ {y₂ > 1} = μ {y₁ > 1}`. -/
theorem IsRegVarVector.measureReal_snd_eq_fst_of_tailEquiv
    (h : IsRegVarVector P (fun ω ↦ (X₁ ω, X₂ ω)) α μ) (h₁ : Measurable X₁) (h₂ : Measurable X₂)
    (hμ : μ.real {y | 1 < y.1} ≠ 0)
    (heq : Tendsto (fun x ↦ P.real {ω | x < X₂ ω} / P.real {ω | x < X₁ ω}) atTop (𝓝 1)) :
    μ.real {y | 1 < y.2} = μ.real {y | 1 < y.1} := by
  have hlim : Tendsto (fun x ↦ P.real {ω | x < X₂ ω} / P.real {ω | x < X₁ ω}) atTop
      (𝓝 (μ.real {y | 1 < y.2} / μ.real {y | 1 < y.1})) := by
    refine ((h.tendsto_snd h₁ h₂).div (h.tendsto_fst h₁ h₂) hμ).congr' ?_
    filter_upwards [h.isRegularlyVarying.eventually_pos] with x hx
    exact div_div_div_cancel_right₀ hx.ne' _ _
  have := tendsto_nhds_unique hlim heq
  rwa [div_eq_one_iff_eq hμ] at this

end RegVar

end ExtremeValueTheory
