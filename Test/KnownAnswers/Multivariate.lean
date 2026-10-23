import ExtremeValueTheory

/-! # Known answers: multivariate extremes

The Pickands dependence function, the exponent function, the extremal coefficient, the upper tail
dependence coefficient and the unit Fréchet standardization of
`ExtremeValueTheory/Multivariate` and `ExtremeValueTheory/MaxStable`, evaluated at the two
boundary cases of bivariate extreme value dependence: **independence** (spectral measure on the
axes) and **complete dependence** (spectral measure at the diagonal).

References: [dHF] de Haan, Ferreira, *Extreme Value Theory* (2006), Chapter 6; [Col] Coles,
*An Introduction to Statistical Modeling of Extreme Values* (2001), Chapter 8; [BGST] Beirlant,
Goegebeur, Segers, Teugels, *Statistics of Extremes* (2004), Chapters 8–9; [Pic81] Pickands,
*Multivariate extreme value distributions* (1981).
-/

open ExtremeValueTheory MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace Test.KnownAnswers.Multivariate

/-! ### The spectral Pickands function `A(t) = ∫ max(t w₀, (1 - t) w₁) dH(w)` -/

/-- **Independence**: `A ≡ 1` on `[0, 1]` ([Col, §8.2.1], [BGST, §8.2.3]). -/
theorem test_pickandsSpectral_independent {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pickandsSpectral independentSpectralMeasure t = 1 := by
  rw [pickandsSpectral, lintegral_independentSpectralMeasure (measurable_pickandsIntegrand _ _)]
  simp [Fin.sum_univ_two, Pi.single_apply]
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal ht.1, ENNReal.toReal_ofReal (by linarith [ht.2])]
  ring

/-- **Complete dependence**: `A(t) = max(t, 1 - t)` ([Col, §8.2.1], [BGST, §8.2.3]). -/
theorem test_pickandsSpectral_comonotone {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pickandsSpectral comonotoneSpectralMeasure t = max t (1 - t) := by
  rw [pickandsSpectral, comonotoneSpectralMeasure,
    lintegral_dirac' _ (measurable_pickandsIntegrand _ _)]
  simp only [mul_one]
  rw [← ENNReal.ofReal_max, ENNReal.toReal_ofReal (le_max_of_le_left ht.1)]

/-- Both spectral measures satisfy the moment constraints `∫ w_i dH = 1` (unit Fréchet margins). -/
example (i : Fin 2) : ∫⁻ w, w i ∂independentSpectralMeasure = 1 ∧
    ∫⁻ w, w i ∂(comonotoneSpectralMeasure (ι := Fin 2)) = 1 :=
  ⟨lintegral_apply_independentSpectralMeasure i, lintegral_apply_comonotoneSpectralMeasure i⟩

/-! ### Laws with these spectral measures -/

/-- Test-specific: Measurability of the integrand `w ↦ max_i w_i / c_i` of the exponent function. -/
private lemma measurable_iSup_div (c : Fin 2 → ℝ≥0∞) :
    Measurable fun w : Fin 2 → ℝ≥0∞ => ⨆ i, w i / c i :=
  Measurable.iSup fun i => (measurable_pi_apply i).div_const _

/-- **Independence**: the exponent function is `V(y) = 1/y₀ + 1/y₁` ([Col, §8.2], [BGST, §8.2]), i.e. `P(Y ≤ y) = e^{-1/y₀} e^{-1/y₁}`. -/
theorem test_maxStableExponent_independent {ν : Measure (Fin 2 → ℝ)}
    (hν : HasSpectralMeasure ν independentSpectralMeasure) {y : Fin 2 → ℝ} (hy : ∀ i, 0 < y i) :
    maxStableExponent ν y = (y 0)⁻¹ + (y 1)⁻¹ := by
  rw [hν.maxStableExponent_eq hy, lintegral_independentSpectralMeasure (measurable_iSup_div _)]
  simp only [iSup_single_div, Fin.sum_univ_two]
  rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hy 0)).ne')
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hy 1)).ne'), ENNReal.toReal_inv,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (hy 0).le, ENNReal.toReal_ofReal (hy 1).le]

/-- **Complete dependence**: `V(y) = max(1/y₀, 1/y₁)`, i.e. `P(Y ≤ y) = e^{-1/min(y₀, y₁)}`. -/
theorem test_maxStableExponent_comonotone {ν : Measure (Fin 2 → ℝ)}
    (hν : HasSpectralMeasure ν comonotoneSpectralMeasure) {y : Fin 2 → ℝ} (hy : ∀ i, 0 < y i) :
    maxStableExponent ν y = max (y 0)⁻¹ (y 1)⁻¹ := by
  rw [hν.maxStableExponent_eq hy, comonotoneSpectralMeasure,
    lintegral_dirac' _ (measurable_iSup_div _), iSup_fin_two]
  simp only [one_div]
  rw [ENNReal.toReal_max (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hy 0)).ne')
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hy 1)).ne'), ENNReal.toReal_inv,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (hy 0).le, ENNReal.toReal_ofReal (hy 1).le]

/-- **Extremal coefficient** `θ = V(1, 1)`: `2` under independence ([Col, §8.4], [BGST, §8.2]). -/
theorem test_extremalCoefficient_independent {ν : Measure (Fin 2 → ℝ)}
    (hν : HasSpectralMeasure ν independentSpectralMeasure) : extremalCoefficient ν = 2 := by
  rw [extremalCoefficient, test_maxStableExponent_independent hν fun _ => one_pos]
  norm_num

/-- **Extremal coefficient** `θ = 1` under complete dependence. -/
theorem test_extremalCoefficient_comonotone {ν : Measure (Fin 2 → ℝ)}
    (hν : HasSpectralMeasure ν comonotoneSpectralMeasure) : extremalCoefficient ν = 1 := by
  rw [extremalCoefficient, test_maxStableExponent_comonotone hν fun _ => one_pos]
  norm_num

/-- **Upper tail dependence** `χ = lim P(F₁(Y₁) > u | F₀(Y₀) > u) = 2 - θ` is `0` under
independence and `1` under complete dependence ([Col, §8.4], [BGST, §9.5.1]). The laws are
obtained from the library's existence theorem for a given spectral measure. -/
theorem test_upperTailDependence :
    (∃ ν : Measure (Fin 2 → ℝ), IsSimpleMaxStable ν ∧
      HasUpperTailDependence ν (fun z => z 0) (fun z => z 1) 0) ∧
    (∃ ν : Measure (Fin 2 → ℝ), IsSimpleMaxStable ν ∧
      HasUpperTailDependence ν (fun z => z 0) (fun z => z 1) 1) := by
  constructor
  · obtain ⟨ν, hms, hν⟩ := exists_isSimpleMaxStable_hasSpectralMeasure
      (independentSpectralMeasure (ι := Fin 2)) lintegral_apply_independentSpectralMeasure
    refine ⟨ν, hms, ?_⟩
    have := hms.hasUpperTailDependence
    rwa [test_extremalCoefficient_independent hν, sub_self] at this
  · obtain ⟨ν, hms, hν⟩ := exists_isSimpleMaxStable_hasSpectralMeasure
      (comonotoneSpectralMeasure (ι := Fin 2)) lintegral_apply_comonotoneSpectralMeasure
    refine ⟨ν, hms, ?_⟩
    have := hms.hasUpperTailDependence
    rw [test_extremalCoefficient_comonotone hν] at this
    norm_num at this
    exact this

/-- The Pickands function of a law with the independent spectral measure is `A ≡ 1`; with the
comonotone one, `A(1/4) = 3/4`. -/
example {ν ν' : Measure (Fin 2 → ℝ)} (hν : HasSpectralMeasure ν independentSpectralMeasure)
    (hν' : HasSpectralMeasure ν' comonotoneSpectralMeasure) :
    pickandsDependence ν (1 / 3) = 1 ∧ pickandsDependence ν' (1 / 4) = 3 / 4 := by
  have hI : (1 / 3 : ℝ) ∈ Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have hI' : (1 / 4 : ℝ) ∈ Icc 0 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rw [hν.pickandsDependence_eq lintegral_apply_independentSpectralMeasure hI,
      test_pickandsSpectral_independent hI]
  · rw [hν'.pickandsDependence_eq lintegral_apply_comonotoneSpectralMeasure hI',
      test_pickandsSpectral_comonotone hI']
    norm_num

/-! ### Unit Fréchet standardization -/

/-- The unit Fréchet transform `x ↦ -1 / log F_i(x_i)` is the identity on positive points when
the margins are already unit Fréchet `F_i(x) = e^{-1/x}` ([dHF, §6.1.2], [BGST, §8.2.1]). -/
theorem test_frechetTransform_id {ι : Type*} {μ : Measure (ι → ℝ)} (h : IsSimpleMaxStable μ)
    [IsProbabilityMeasure μ] {y : ι → ℝ} (hy : ∀ i, 0 < y i) (i : ι) :
    frechetTransform μ y i = y i := by
  have hm : marginal μ i (y i) = Real.exp (-(y i)⁻¹) := by
    change cdf (μ.map fun x => x i) (y i) = _
    rw [cdf_eq_real, map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic,
      measureReal_def]
    change (μ {x | x i ≤ y i}).toReal = _
    rw [h.measure_le i (y i) (hy i), ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [frechetTransform, hm, Real.log_exp]
  field_simp

/-! ### Pickands' nonparametric estimator -/

/-- Pickands' estimator `Âₙ(t) = n / ∑ min(1/(t y₀), 1/((1-t) y₁))` on a perfectly dependent
sample `yᵢ = (1, 1)` returns `max(t, 1 - t)`, the complete-dependence value ([Pic81], [BGST,
(9.39)]); at `t = 1/4` it is `3/4`. -/
theorem test_pickandsDependenceEstimator_comonotone (n : ℕ) (hn : 0 < n) :
    pickandsDependenceEstimator (1 / 4) (fun _ => ![1, 1]) n = 3 / 4 := by
  simp [pickandsDependenceEstimator, pickandsVar]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  norm_num

end Test.KnownAnswers.Multivariate
