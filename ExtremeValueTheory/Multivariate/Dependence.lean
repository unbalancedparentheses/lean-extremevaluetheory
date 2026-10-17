/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.Spectral

/-!
# Bivariate extremes: the Pickands dependence function and the extremal coefficient

For a bivariate simple max-stable law `μ` (unit Fréchet margins) with exponent function
`V(x, y) = -log P(Y₁ ≤ x, Y₂ ≤ y)`, homogeneity `V(c x, c y) = V(x, y) / c` shows that `V` is
determined by its values on the line `1 / x + 1 / y = 1`:

  `V(x, y) = (1 / x + 1 / y) A(y / (x + y))`,

where the **Pickands dependence function** is `A(t) = V(1 / t, 1 / (1 - t))` for `0 < t < 1` and
`A(0) = A(1) = 1` ([Pickands 1981]; [dHF, §6.1.5]; [BGST04, §8.2.3]; [Col01, §8.2.1]). It satisfies
`max(t, 1 - t) ≤ A(t) ≤ 1`, and for a law with spectral measure `H`,
`F(x, y) = exp (-∫ max(w₁ / x, w₂ / y) dH(w))`, it has the spectral form

  `A(t) = ∫ max(t w₁, (1 - t) w₂) dH(w)`,

which is convex in `t` as an integral of maxima of linear functions. Independence corresponds to
`A ≡ 1`, complete dependence to `A(t) = max(t, 1 - t)`.

The **extremal coefficient** of a simple max-stable law on `ℝ^ι` is `θ = V(1, …, 1)`; it
satisfies `1 ≤ θ ≤ |ι|` and `P(max_i Y_i ≤ z) = P(Y_i ≤ z) ^ θ` ([BGST04, §8.2.7]; [Col01, §8.2.5]).
In the bivariate case `θ = 2 A(1 / 2)`.

## Conventions

Coordinates are indexed by `Fin 2`, so `w₁, w₂` above are `w 0, w 1`. With `t = y / (x + y)` the
weight of the first coordinate is `t`; some references use the mirrored convention `t ↦ 1 - t`
(which exchanges the roles of the coordinates in the spectral formula).

## Main definitions and results

* `pickandsDependence μ t`: the Pickands dependence function.
* `IsSimpleMaxStable.maxStableExponent_eq_pickands`: `V(x, y) = (1 / x + 1 / y) A(y / (x + y))`.
* `IsSimpleMaxStable.max_le_pickands`, `IsSimpleMaxStable.pickandsDependence_le_one`,
  `IsSimpleMaxStable.half_le_pickands`: `1 / 2 ≤ max(t, 1 - t) ≤ A(t) ≤ 1` on `[0, 1]`.
* `HasSpectralMeasure ν H`: `ν (Iic y) = exp (-∫ max_i w i / y i dH(w))`;
  `exists_isSimpleMaxStable_hasSpectralMeasure`: every normalized `H` arises.
* `pickandsSpectral H t = ∫ max(t w 0, (1 - t) w 1) dH`, `convexOn_pickandsSpectral`.
* `HasSpectralMeasure.pickandsDependence_eq`, `HasSpectralMeasure.convexOn_pickands`,
  `exists_isSimpleMaxStable_pickands`: for laws with a spectral measure,
  `A = pickandsSpectral H` on `[0, 1]`, hence `A` is convex.
* `pickandsDependence_eq_one_of_measure_Iic_eq_mul`,
  `pickandsDependence_eq_max_of_measure_Iic_eq_min`: the extreme cases, and their instances
  `pickandsDependence_map_spectralVector_independent`,
  `pickandsDependence_map_spectralVector_comonotone` for the spectral examples of
  `MaxStable/Spectral.lean`.
* `extremalCoefficient μ`, `IsSimpleMaxStable.one_le_extremalCoefficient`,
  `IsSimpleMaxStable.extremalCoefficient_le_card`,
  `IsSimpleMaxStable.measureReal_Iic_const`: `P(max_i Y_i ≤ z) = exp (-1 / z) ^ θ`;
  `IsSimpleMaxStable.extremalCoefficient_eq_two_mul_pickands`: `θ = 2 A(1 / 2)`.

The convexity of `A` for an arbitrary bivariate simple max-stable law (not given by a spectral
measure) would follow from the converse spectral representation, which is not formalized (see
`MaxStable/Basic.lean`).

## References

* J. Pickands III, *Multivariate extreme value distributions*, Bull. Int. Statist. Inst. 49
  (1981).
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 6 [dHF].
* J. Beirlant, Y. Goegebeur, J. Segers, J. Teugels, *Statistics of Extremes*, Wiley (2004),
  Chapters 8–9 [BGST04].
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 8 [Col01].
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### The Pickands dependence function -/

/-- The **Pickands dependence function** of a law `μ` on `ℝ²`:
`A(t) = V(1 / t, 1 / (1 - t))` for `0 < t < 1`, and `A(t) = 1` otherwise. -/
noncomputable def pickandsDependence (μ : Measure (Fin 2 → ℝ)) (t : ℝ) : ℝ :=
  if t ∈ Ioo (0 : ℝ) 1 then maxStableExponent μ ![t⁻¹, (1 - t)⁻¹] else 1

lemma pickandsDependence_of_mem_Ioo (μ : Measure (Fin 2 → ℝ)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    pickandsDependence μ t = maxStableExponent μ ![t⁻¹, (1 - t)⁻¹] := by
  simp [pickandsDependence, ht]

lemma pickandsDependence_of_notMem_Ioo (μ : Measure (Fin 2 → ℝ)) {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) :
    pickandsDependence μ t = 1 := by
  simp only [pickandsDependence, ht, ↓reduceIte]

@[simp] lemma pickandsDependence_zero (μ : Measure (Fin 2 → ℝ)) : pickandsDependence μ 0 = 1 := by
  simp [pickandsDependence]

@[simp] lemma pickandsDependence_one (μ : Measure (Fin 2 → ℝ)) : pickandsDependence μ 1 = 1 := by
  simp [pickandsDependence]

lemma eq_zero_or_eq_one_of_mem_Icc_of_notMem_Ioo {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hI : t ∉ Ioo (0 : ℝ) 1) : t = 0 ∨ t = 1 := by
  by_contra hc
  push Not at hc
  exact hI ⟨lt_of_le_of_ne ht.1 (Ne.symm hc.1), lt_of_le_of_ne ht.2 hc.2⟩

lemma pos_vec_inv {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ i, 0 < (![t⁻¹, (1 - t)⁻¹] : Fin 2 → ℝ) i := by
  intro i
  fin_cases i
  · simpa using ht.1
  · simpa using ht.2

lemma iSup_fin_two {α : Type*} [CompleteLinearOrder α] (f : Fin 2 → α) :
    ⨆ i, f i = max (f 0) (f 1) := by
  refine le_antisymm (iSup_le fun i ↦ ?_) (max_le (le_iSup f 0) (le_iSup f 1))
  fin_cases i
  exacts [le_max_left _ _, le_max_right _ _]

lemma iInf_fin_two {α : Type*} [CompleteLinearOrder α] (f : Fin 2 → α) :
    ⨅ i, f i = min (f 0) (f 1) := by
  refine le_antisymm (le_min (iInf_le f 0) (iInf_le f 1)) (le_iInf fun i ↦ ?_)
  fin_cases i
  exacts [min_le_left _ _, min_le_right _ _]

namespace IsSimpleMaxStable

variable {μ : Measure (Fin 2 → ℝ)}

/-- **The Pickands representation** ([Pickands 1981]; [dHF, §6.1.5]):
`V(x, y) = (1 / x + 1 / y) A(y / (x + y))` for `x, y > 0`. -/
theorem maxStableExponent_eq_pickands (h : IsSimpleMaxStable μ) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    maxStableExponent μ ![x, y] = (x⁻¹ + y⁻¹) * pickandsDependence μ (y / (x + y)) := by
  have hxy : 0 < x + y := add_pos hx hy
  have ht : y / (x + y) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hy hxy, (div_lt_one hxy).2 (by linarith)⟩
  have hc : 0 < x⁻¹ + y⁻¹ := by positivity
  have h1t : 1 - y / (x + y) = x / (x + y) := by field_simp; ring
  have hv : (![(y / (x + y))⁻¹, (1 - y / (x + y))⁻¹] : Fin 2 → ℝ) = (x⁻¹ + y⁻¹) • ![x, y] := by
    rw [h1t]
    ext i
    fin_cases i
    · simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
      field_simp
      ring
    · simp only [Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, Fin.mk_one,
        Matrix.cons_val_zero]
      field_simp
      ring
  have hpos : ∀ i, 0 < (![x, y] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · simpa using hx
    · simpa using hy
  rw [pickandsDependence_of_mem_Ioo μ ht, hv, h.maxStableExponent_smul hc hpos, ← mul_assoc,
    mul_inv_cancel₀ hc.ne', one_mul]

/-- **Bounds on the Pickands function**: `max(t, 1 - t) ≤ A(t)` on `[0, 1]`. -/
theorem max_le_pickands (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    max t (1 - t) ≤ pickandsDependence μ t := by
  by_cases hI : t ∈ Ioo (0 : ℝ) 1
  · rw [pickandsDependence_of_mem_Ioo μ hI]
    have h0 := h.inv_le_maxStableExponent (pos_vec_inv hI) 0
    have h1 := h.inv_le_maxStableExponent (pos_vec_inv hI) 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, inv_inv] at h0 h1
    exact max_le h0 h1
  · rw [pickandsDependence_of_notMem_Ioo μ hI]
    rcases eq_zero_or_eq_one_of_mem_Icc_of_notMem_Ioo ht hI with rfl | rfl <;> simp

/-- **Bounds on the Pickands function**: `A(t) ≤ 1` (the value for independence). -/
theorem pickandsDependence_le_one (h : IsSimpleMaxStable μ) (t : ℝ) :
    pickandsDependence μ t ≤ 1 := by
  by_cases hI : t ∈ Ioo (0 : ℝ) 1
  · rw [pickandsDependence_of_mem_Ioo μ hI]
    refine (h.maxStableExponent_le_sum_inv (pos_vec_inv hI)).trans (le_of_eq ?_)
    simp [Fin.sum_univ_two]
  · rw [pickandsDependence_of_notMem_Ioo μ hI]

theorem half_le_pickands (h : IsSimpleMaxStable μ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 2 ≤ pickandsDependence μ t := by
  refine le_trans ?_ (h.max_le_pickands ht)
  rcases le_total t (1 / 2) with h' | h'
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left h'

end IsSimpleMaxStable

/-! ### Spectral measures and convexity -/

section Spectral

variable {ι : Type*}

/-- A law `ν` on `ℝ^ι` has **spectral measure** `H` (a measure on `[0, ∞]^ι`) if
`ν (Iic y) = exp (-∫ max_i w i / y i dH(w))` for every `y` with positive coordinates. -/
def HasSpectralMeasure (ν : Measure (ι → ℝ)) (H : Measure (ι → ℝ≥0∞)) : Prop :=
  ∀ y : ι → ℝ, (∀ i, 0 < y i) →
    ν (Iic y) = ENNReal.ofReal (Real.exp (-(∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H).toReal))

/-- Every normalized spectral measure is the spectral measure of a simple max-stable law. -/
theorem exists_isSimpleMaxStable_hasSpectralMeasure [Fintype ι] (H : Measure (ι → ℝ≥0∞))
    [SFinite H] (hH : ∀ i, ∫⁻ w, w i ∂H = 1) :
    ∃ ν : Measure (ι → ℝ), IsSimpleMaxStable ν ∧ HasSpectralMeasure ν H :=
  exists_isSimpleMaxStable_of_spectralMeasure H hH

/-- For a law with spectral measure `H`, `V(y) = ∫ max_i w i / y i dH(w)`. -/
theorem HasSpectralMeasure.maxStableExponent_eq {ν : Measure (ι → ℝ)} {H : Measure (ι → ℝ≥0∞)}
    (hν : HasSpectralMeasure ν H) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    maxStableExponent ν y = (∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H).toReal := by
  rw [maxStableExponent, measureReal_def, hν y hy, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_exp, neg_neg]

/-- The spectral form of the Pickands function: `∫ max(t w 0, (1 - t) w 1) dH(w)`. -/
noncomputable def pickandsSpectral (H : Measure (Fin 2 → ℝ≥0∞)) (t : ℝ) : ℝ :=
  (∫⁻ w, max (ENNReal.ofReal t * w 0) (ENNReal.ofReal (1 - t) * w 1) ∂H).toReal

lemma measurable_pickandsIntegrand (s r : ℝ) :
    Measurable fun w : Fin 2 → ℝ≥0∞ ↦ max (ENNReal.ofReal s * w 0) (ENNReal.ofReal r * w 1) :=
  (measurable_const.mul (measurable_pi_apply 0)).max (measurable_const.mul (measurable_pi_apply 1))

lemma lintegral_pickandsIntegrand_ne_top {H : Measure (Fin 2 → ℝ≥0∞)}
    (hH : ∀ i, ∫⁻ w, w i ∂H ≠ ∞) (s r : ℝ) :
    ∫⁻ w, max (ENNReal.ofReal s * w 0) (ENNReal.ofReal r * w 1) ∂H ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ w, (ENNReal.ofReal s * w 0 + ENNReal.ofReal r * w 1) ∂H) ?_
    (lintegral_mono fun w ↦ max_le le_self_add le_add_self)
  rw [lintegral_add_left ((measurable_pi_apply 0).const_mul _),
    lintegral_const_mul _ (measurable_pi_apply 0), lintegral_const_mul _ (measurable_pi_apply 1)]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hH 0),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hH 1)⟩

/-- **Convexity of the spectral Pickands function**: `t ↦ ∫ max(t w 0, (1 - t) w 1) dH` is
convex on `[0, 1]`, as an integral of maxima of linear functions. -/
theorem convexOn_pickandsSpectral {H : Measure (Fin 2 → ℝ≥0∞)} (hH : ∀ i, ∫⁻ w, w i ∂H ≠ ∞) :
    ConvexOn ℝ (Icc 0 1) (pickandsSpectral H) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul, pickandsSpectral]
  set F := fun w : Fin 2 → ℝ≥0∞ ↦ max (ENNReal.ofReal x * w 0) (ENNReal.ofReal (1 - x) * w 1)
    with hFdef
  set G := fun w : Fin 2 → ℝ≥0∞ ↦ max (ENNReal.ofReal y * w 0) (ENNReal.ofReal (1 - y) * w 1)
    with hGdef
  have hpt : ∀ w : Fin 2 → ℝ≥0∞, max (ENNReal.ofReal (a * x + b * y) * w 0)
      (ENNReal.ofReal (1 - (a * x + b * y)) * w 1) ≤
        ENNReal.ofReal a * F w + ENNReal.ofReal b * G w := by
    intro w
    have e1 : ENNReal.ofReal (a * x + b * y) =
        ENNReal.ofReal a * ENNReal.ofReal x + ENNReal.ofReal b * ENNReal.ofReal y := by
      rw [ENNReal.ofReal_add (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ENNReal.ofReal_mul ha,
        ENNReal.ofReal_mul hb]
    have e2 : ENNReal.ofReal (1 - (a * x + b * y)) =
        ENNReal.ofReal a * ENNReal.ofReal (1 - x) + ENNReal.ofReal b * ENNReal.ofReal (1 - y) := by
      rw [show 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) by linear_combination (-1 : ℝ) * hab,
        ENNReal.ofReal_add (mul_nonneg ha (by linarith [hx.2]))
          (mul_nonneg hb (by linarith [hy.2])),
        ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
    rw [e1, e2, add_mul, add_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    exact max_le (add_le_add (mul_le_mul_right (le_max_left _ _) _)
        (mul_le_mul_right (le_max_left _ _) _))
      (add_le_add (mul_le_mul_right (le_max_right _ _) _)
        (mul_le_mul_right (le_max_right _ _) _))
  have hF := lintegral_pickandsIntegrand_ne_top hH x (1 - x)
  have hG := lintegral_pickandsIntegrand_ne_top hH y (1 - y)
  have hint : ∫⁻ w, (ENNReal.ofReal a * F w + ENNReal.ofReal b * G w) ∂H =
      ENNReal.ofReal a * ∫⁻ w, F w ∂H + ENNReal.ofReal b * ∫⁻ w, G w ∂H := by
    rw [lintegral_add_left ((measurable_pickandsIntegrand x (1 - x)).const_mul _),
      lintegral_const_mul _ (measurable_pickandsIntegrand x (1 - x)),
      lintegral_const_mul _ (measurable_pickandsIntegrand y (1 - y))]
  have hfin : ENNReal.ofReal a * ∫⁻ w, F w ∂H + ENNReal.ofReal b * ∫⁻ w, G w ∂H ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG⟩
  calc _ ≤ (ENNReal.ofReal a * ∫⁻ w, F w ∂H + ENNReal.ofReal b * ∫⁻ w, G w ∂H).toReal :=
        ENNReal.toReal_mono hfin (hint ▸ lintegral_mono hpt)
    _ = _ := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG), ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

variable {ν : Measure (Fin 2 → ℝ)} {H : Measure (Fin 2 → ℝ≥0∞)}

/-- **Spectral form of the Pickands function**: for a law with spectral measure `H` normalized
by `∫ w i dH = 1`, `A(t) = ∫ max(t w 0, (1 - t) w 1) dH(w)` on `[0, 1]`. -/
theorem HasSpectralMeasure.pickandsDependence_eq (hν : HasSpectralMeasure ν H)
    (hH : ∀ i, ∫⁻ w, w i ∂H = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pickandsDependence ν t = pickandsSpectral H t := by
  by_cases hI : t ∈ Ioo (0 : ℝ) 1
  · rw [pickandsDependence_of_mem_Ioo ν hI, hν.maxStableExponent_eq (pos_vec_inv hI),
      pickandsSpectral]
    congr 1
    refine lintegral_congr fun w ↦ ?_
    rw [iSup_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ENNReal.ofReal_inv_of_pos hI.1, ENNReal.ofReal_inv_of_pos (by linarith [hI.2]),
      div_eq_mul_inv, div_eq_mul_inv, inv_inv, inv_inv, mul_comm (w 0), mul_comm (w 1)]
  · rw [pickandsDependence_of_notMem_Ioo ν hI, pickandsSpectral]
    rcases eq_zero_or_eq_one_of_mem_Icc_of_notMem_Ioo ht hI with rfl | rfl
    · simp [hH 1]
    · simp [hH 0]

/-- **Convexity of the Pickands function** ([Pickands 1981]; [dHF, §6.1.5]) for a law with a
normalized spectral measure. -/
theorem HasSpectralMeasure.convexOn_pickands (hν : HasSpectralMeasure ν H)
    (hH : ∀ i, ∫⁻ w, w i ∂H = 1) : ConvexOn ℝ (Icc 0 1) (pickandsDependence ν) :=
  (convexOn_pickandsSpectral fun i ↦ by simp [hH i]).congr fun _ ht ↦
    (hν.pickandsDependence_eq hH ht).symm

/-- Every normalized spectral measure `H` gives a simple max-stable law whose Pickands function is
`∫ max(t w 0, (1 - t) w 1) dH` on `[0, 1]`, and is convex there. -/
theorem exists_isSimpleMaxStable_pickands (H : Measure (Fin 2 → ℝ≥0∞)) [SFinite H]
    (hH : ∀ i, ∫⁻ w, w i ∂H = 1) :
    ∃ ν : Measure (Fin 2 → ℝ), IsSimpleMaxStable ν ∧ HasSpectralMeasure ν H ∧
      EqOn (pickandsDependence ν) (pickandsSpectral H) (Icc 0 1) ∧
        ConvexOn ℝ (Icc 0 1) (pickandsDependence ν) := by
  obtain ⟨ν, hms, hν⟩ := exists_isSimpleMaxStable_hasSpectralMeasure H hH
  exact ⟨ν, hms, hν, fun _ ht ↦ hν.pickandsDependence_eq hH ht, hν.convexOn_pickands hH⟩

end Spectral

/-! ### The extreme cases -/

section Extreme

variable {μ : Measure (Fin 2 → ℝ)}

/-- **Independence**: if `P(Y ≤ y) = exp (-1 / y₀) exp (-1 / y₁)`, then `A ≡ 1`. -/
theorem pickandsDependence_eq_one_of_measure_Iic_eq_mul
    (hind : ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
      μ (Iic y) = ENNReal.ofReal (Real.exp (-(y 0)⁻¹)) * ENNReal.ofReal (Real.exp (-(y 1)⁻¹)))
    (t : ℝ) : pickandsDependence μ t = 1 := by
  by_cases hI : t ∈ Ioo (0 : ℝ) 1
  · rw [pickandsDependence_of_mem_Ioo μ hI, maxStableExponent, measureReal_def,
      hind _ (pos_vec_inv hI)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, inv_inv]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Real.exp_add, Real.log_exp]
    ring
  · rw [pickandsDependence_of_notMem_Ioo μ hI]

/-- **Complete dependence**: if `P(Y ≤ y) = min (exp (-1 / y₀)) (exp (-1 / y₁))`, then
`A(t) = max(t, 1 - t)` on `[0, 1]`. -/
theorem pickandsDependence_eq_max_of_measure_Iic_eq_min
    (hcom : ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
      μ (Iic y) = min (ENNReal.ofReal (Real.exp (-(y 0)⁻¹)))
        (ENNReal.ofReal (Real.exp (-(y 1)⁻¹))))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : pickandsDependence μ t = max t (1 - t) := by
  by_cases hI : t ∈ Ioo (0 : ℝ) 1
  · rw [pickandsDependence_of_mem_Ioo μ hI, maxStableExponent, measureReal_def,
      hcom _ (pos_vec_inv hI)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, inv_inv]
    rw [← ENNReal.ofReal_min, ENNReal.toReal_ofReal (le_min (Real.exp_pos _).le
      (Real.exp_pos _).le), ← Real.exp_monotone.map_min, Real.log_exp, min_neg_neg, neg_neg]
  · rw [pickandsDependence_of_notMem_Ioo μ hI]
    rcases eq_zero_or_eq_one_of_mem_Icc_of_notMem_Ioo ht hI with rfl | rfl <;> simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {N : Ω → Measure (ℝ × (Fin 2 → ℝ≥0∞))}

lemma measure_map_spectralVector_Iic {S : Type*} [MeasurableSpace S]
    {N : Ω → Measure (ℝ × S)} (hN : Measurable N) {f : Fin 2 → S → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (y : Fin 2 → ℝ) :
    (P.map fun ω ↦ spectralVector f (N ω)) (Iic y) = P {ω | spectralVector f (N ω) ≤ y} :=
  Measure.map_apply (measurable_spectralVector hN hf) measurableSet_Iic

/-- The independent spectral example (vertex masses) has `A ≡ 1`. -/
theorem pickandsDependence_map_spectralVector_independent
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod independentSpectralMeasure) P)
    (t : ℝ) : pickandsDependence (P.map fun ω ↦ spectralVector (fun i w ↦ w i) (N ω)) t = 1 :=
  pickandsDependence_eq_one_of_measure_Iic_eq_mul (fun y hy ↦ by
    rw [measure_map_spectralVector_Iic hN.measurable (fun i ↦ measurable_pi_apply i),
      hN.measure_spectralVector_le_independent hy, Fin.prod_univ_two]) t

/-- The comonotone spectral example (a unit mass at `(1, 1)`) has `A(t) = max(t, 1 - t)`. -/
theorem pickandsDependence_map_spectralVector_comonotone
    (hN : IsPoissonRandomMeasure N ((radialMeasure 1).prod comonotoneSpectralMeasure) P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pickandsDependence (P.map fun ω ↦ spectralVector (fun i w ↦ w i) (N ω)) t = max t (1 - t) :=
  pickandsDependence_eq_max_of_measure_Iic_eq_min (fun y hy ↦ by
    rw [measure_map_spectralVector_Iic hN.measurable (fun i ↦ measurable_pi_apply i),
      hN.measure_spectralVector_le_comonotone hy, iInf_fin_two]) ht

end Extreme

/-! ### The extremal coefficient -/

section Extremal

variable {ι : Type*} {μ : Measure (ι → ℝ)}

/-- The **extremal coefficient** `θ = V(1, …, 1)` of a law on `ℝ^ι`. -/
noncomputable def extremalCoefficient (μ : Measure (ι → ℝ)) : ℝ :=
  maxStableExponent μ fun _ ↦ 1

namespace IsSimpleMaxStable

variable [Finite ι]

/-- The exponent function on the diagonal: `V(z, …, z) = θ / z`. -/
theorem maxStableExponent_const (h : IsSimpleMaxStable μ) {z : ℝ} (hz : 0 < z) :
    maxStableExponent μ (fun _ ↦ z) = z⁻¹ * extremalCoefficient μ := by
  rw [extremalCoefficient, ← h.maxStableExponent_smul hz (fun _ ↦ one_pos)]
  congr 1
  ext; simp

/-- **The extremal coefficient and the law of the maximum**:
`P(max_i Y_i ≤ z) = P(Y ≤ (z, …, z)) = exp (-1 / z) ^ θ = P(Y_j ≤ z) ^ θ`. -/
theorem measureReal_Iic_const (h : IsSimpleMaxStable μ) {z : ℝ} (hz : 0 < z) :
    μ.real (Iic fun _ ↦ z) = Real.exp (-z⁻¹) ^ extremalCoefficient μ := by
  rw [← h.exp_neg_maxStableExponent (fun _ ↦ hz), h.maxStableExponent_const hz, ← Real.exp_mul,
    neg_mul]

theorem one_le_extremalCoefficient [Nonempty ι] (h : IsSimpleMaxStable μ) :
    1 ≤ extremalCoefficient μ := by
  simpa [extremalCoefficient] using
    h.inv_le_maxStableExponent (y := fun _ ↦ (1 : ℝ)) (fun _ ↦ one_pos)
    (Classical.arbitrary ι)

theorem extremalCoefficient_le_card [Fintype ι] (h : IsSimpleMaxStable μ) :
    extremalCoefficient μ ≤ Fintype.card ι := by
  simpa [extremalCoefficient] using
    h.maxStableExponent_le_sum_inv (y := fun _ ↦ (1 : ℝ)) (fun _ ↦ one_pos)

end IsSimpleMaxStable

/-- In the bivariate case, `θ = 2 A(1 / 2)`; hence `1 ≤ θ ≤ 2`. -/
theorem IsSimpleMaxStable.extremalCoefficient_eq_two_mul_pickands {μ : Measure (Fin 2 → ℝ)}
    (h : IsSimpleMaxStable μ) : extremalCoefficient μ = 2 * pickandsDependence μ (1 / 2) := by
  have := h.maxStableExponent_eq_pickands one_pos one_pos
  rw [show (![1, 1] : Fin 2 → ℝ) = fun _ ↦ 1 by ext i; fin_cases i <;> rfl] at this
  rw [extremalCoefficient, this]
  norm_num

end Extremal

end ExtremeValueTheory
