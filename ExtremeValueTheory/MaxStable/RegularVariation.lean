/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.RegularVariation.Tails

/-!
# Simple max-stable vectors are regularly varying

Let `X` be a random vector in `ℝ^ι` (`ι` finite and nonempty, with the sup norm) whose law is
simple max-stable, with spectral measure `H` on the sup-norm sphere `{w | max_i w i = 1}`
(`IsSimpleMaxStable.exists_hasSpectralMeasure`). Then `X` is **regularly varying with index `1`**
in the sense of `RegularVariation/Multivariate.lean` (`IsRegVarVector P X 1 μ`), with exponent
measure `μ = ν_H / H(univ)`, where `ν_H` is the image of `r ^ (-2) dr ⊗ H` under `(r, w) ↦ r w`
(`spectralExponentMeasure`, `MaxStable/Uniqueness.lean`), and its spectral measure, the law of
`Y / ‖Y‖` under `μ` restricted to `{‖y‖ > 1}`, is `H / H(univ)`: the max-stable spectral measure up
to normalization. For a normalized `H` (`∫ w i dH = 1`) the normalizing constant `H(univ)` is the
extremal coefficient `θ = V(1, …, 1)` ([Res87, Proposition 5.15 and Corollary 5.18]; [dHF, §6.1]).

## The proof

* **Tails.** `P(∃ i, X i / x > d i) = 1 - exp (-Φ(d) / x)` with `Φ(d) = ∫ max_i w i / d i dH`, for
  thresholds `d ∈ (0, ∞]^ι` (`measureReal_exceedSet`; infinite thresholds by monotone limits). In
  particular `P(‖X‖ > x) = 1 - exp (-θ / x)` (`measureReal_lt_norm`), which is regularly varying
  with index `-1`, and the scaled laws `m_x = x P(X / x ∈ ·)` satisfy
  `m_x {∃ i, y i > d i} → ν_H {∃ i, y i > d i} = Φ(d)` (`tendsto_scaledLaw_exceedSet`).
* **Boxes.** By inclusion–exclusion the convergence propagates to the boxes
  `{c < y ≤ b} ∩ {∃ i, y i > δ i}` and their finite unions (`tendsto_measureReal_iUnion_boxSet`).
* **Open sets.** The trace on the orthant of an open set `G` bounded away from the origin is a
  countable union of rational boxes (`exists_ratBox`), so `ν_H(G | O) ≤ liminf m_x(G | O)` for the
  region `O = {∃ i, y i > δ}` (`le_liminf_cond_scaledLaw`). By the portmanteau theorem the
  conditional laws converge weakly, which gives `∫ f dm_x → ∫ f dν_H` for every bounded continuous
  `f` vanishing near the origin (`tendsto_integral_scaledLaw`).

## Main results


## File layout

* `ExtremeValueTheory.MaxStable.RegularVariation.Tails`: boxes, coordinates, the tails and the
  scaled laws on the regions `{∃ i, y i > d i}`.
* this file: rational boxes, weak convergence, integrals and the regular variation.
* `IsSimpleMaxStable.isRegVarVector`: `X` is regularly varying with index `1` and exponent measure
  `maxStableTailMeasure H = ν_H / H(univ)`.
* `spectralMeasure_maxStableTailMeasure`: its spectral measure is `H / H(univ)`.
* `IsSimpleMaxStable.exists_isRegVarVector`: the combined statement for the normalized spectral
  measure, with `H(univ)` the extremal coefficient.

## References

* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  §5.4 [Res87].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  §6.1 [dHF].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace ExtremeValueTheory

variable {ι : Type*}


/-! ### Open sets are exhausted by rational boxes -/

section Geometry

/-- The box with rational lower corner `p.1` and upper corner `p.2` (lower coordinates `≤ 0` are
unconstrained), intersected with `{x | ∃ i, δ i < x i}`. -/
noncomputable def ratBox (δ : ι → ℝ≥0∞) (p : (ι → ℚ) × (ι → ℚ)) : Set (ι → ℝ≥0∞) :=
  boxSet δ (fun i ↦ ENNReal.ofReal (p.1 i)) (fun i ↦ ENNReal.ofReal (p.2 i))

variable [Fintype ι]

/-- Every point of an open set `G` in the nonnegative orthant lies in a rational box whose trace on
the orthant is contained in `G`. -/
lemma exists_ratBox {G : Set (ι → ℝ)} (hG : IsOpen G) (δ : ι → ℝ≥0∞) {y : ι → ℝ} (hyG : y ∈ G)
    (hyQ : y ∈ posOrthant) (hyO : ofRealVec y ∈ exceedSet δ) :
    ∃ p : (ι → ℚ) × (ι → ℚ), (∀ i, 0 < (p.2 i : ℝ)) ∧ ofRealVec y ∈ ratBox δ p ∧
      ∀ z ∈ posOrthant, ofRealVec z ∈ ratBox δ p → z ∈ G := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hG y hyG
  choose q₁ hq₁ using fun i ↦ exists_rat_btwn (show y i - ε / 2 < y i by linarith)
  choose q₂ hq₂ using fun i ↦ exists_rat_btwn (show y i < y i + ε / 2 by linarith)
  have hq₂pos : ∀ i, 0 < (q₂ i : ℝ) := fun i ↦ (hyQ i).trans_lt (hq₂ i).1
  refine ⟨(q₁, q₂), hq₂pos, ⟨⟨fun i hi ↦ ?_, fun i ↦ ?_⟩, hyO⟩, ?_⟩
  · have hq : 0 < (q₁ i : ℝ) := ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hi)
    exact (ENNReal.ofReal_lt_ofReal_iff (hq.trans (hq₁ i).2)).2 (hq₁ i).2
  · exact ENNReal.ofReal_le_ofReal (hq₂ i).1.le
  · rintro z hzQ ⟨⟨hzU, hzL⟩, -⟩
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_lt]
    have hup : z i ≤ q₂ i := (ENNReal.ofReal_le_ofReal_iff (hq₂pos i).le).1 (hzL i)
    have hlow : (q₁ i : ℝ) ≤ z i := by
      by_cases hq : 0 < (q₁ i : ℝ)
      · exact (ENNReal.ofReal_lt_ofReal_iff'.1 (hzU i (ENNReal.ofReal_pos.2 hq).ne')).1.le
      · exact (not_lt.1 hq).trans (hzQ i)
    constructor <;> linarith [(hq₁ i).1, (hq₂ i).2]

end Geometry

/-! ### Weak convergence of the scaled laws -/

section Weak

variable [Fintype ι] {H : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure H]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ι → ℝ}

/-- `b⁻¹ a = (a / b)` as a real ratio, for `a ≤ b < ∞`. -/
lemma inv_mul_eq_ofReal_div {a b : ℝ≥0∞} (hab : a ≤ b) (hb : b ≠ ∞) :
    b⁻¹ * a = ENNReal.ofReal (a.toReal / b.toReal) := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [nonpos_iff_eq_zero.1 hab]
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hb0 hb),
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top hb hab), ENNReal.ofReal_toReal hb, div_eq_mul_inv,
    mul_comm]

variable (hX : Measurable X) (hS : HasSpectralMeasure (P.map X) H)
  (h : IsSimpleMaxStable (P.map X)) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
include hX hS h hH

/-- **The liminf condition on open sets** for the scaled laws conditioned on
`O = {x | ∃ i, δ i < x i}`: `ν_H(G | O) ≤ liminf_x P(X / x ∈ G | X / x ∈ O)`. -/
theorem le_liminf_cond_scaledLaw {δ : ι → ℝ≥0∞} (hδ : ∀ i, δ i ≠ 0) {G : Set (ι → ℝ)}
    (hG : IsOpen G) :
    (spectralExponentMeasureReal H (ofRealVec ⁻¹' exceedSet δ))⁻¹ *
        spectralExponentMeasureReal H (ofRealVec ⁻¹' exceedSet δ ∩ G) ≤
      liminf (fun x ↦ (scaledLaw P X x (ofRealVec ⁻¹' exceedSet δ))⁻¹ *
        scaledLaw P X x (ofRealVec ⁻¹' exceedSet δ ∩ G)) atTop := by
  have hle := ae_le_one_of_ae_iSup_eq_one hH
  have hnt := ae_ne_top_of_ae_le_one hle
  set ν := spectralExponentMeasure H with hν
  set νE := spectralExponentMeasureReal H with hνE
  set O := ofRealVec ⁻¹' exceedSet δ with hO
  have hνfin : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) ≠ ∞ :=
    fun d hd ↦ spectralExponentMeasure_exceedSet_ne_top hle hd
  have hνEO : νE O ≠ ∞ := by
    rw [hO, spectralExponentMeasureReal_preimage hnt (measurableSet_exceedSet δ)]
    exact hνfin δ hδ
  rcases eq_or_ne (νE O) 0 with h0 | hνEO0'
  · rw [measure_mono_null inter_subset_left h0, mul_zero]
    exact zero_le
  have hνEO0 : νE.real O ≠ 0 := (ENNReal.toReal_pos hνEO0' hνEO).ne'
  -- the countable family of rational boxes inside `G`
  set T : Set ((ι → ℚ) × (ι → ℚ)) := {p | (∀ i, 0 < (p.2 i : ℝ)) ∧
    ∀ z ∈ posOrthant, ofRealVec z ∈ ratBox δ p → z ∈ G} with hT
  have hcover : ∀ y ∈ O ∩ G, y ∈ posOrthant → ∃ p ∈ T, ofRealVec y ∈ ratBox δ p := by
    rintro y ⟨hyO, hyG⟩ hyQ
    obtain ⟨p, hp, hyp, hpG⟩ := exists_ratBox hG δ hyG hyQ hyO
    exact ⟨p, ⟨hp, hpG⟩, hyp⟩
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · have : νE (O ∩ G) = 0 := by
      refine measure_mono_null (t := posOrthantᶜ) ?_ spectralExponentMeasureReal_compl_posOrthant
      intro y hy hyQ
      obtain ⟨p, hp, -⟩ := hcover y hy hyQ
      rw [hTe] at hp
      exact hp
    rw [this, mul_zero]
    exact zero_le
  obtain ⟨e, he⟩ := (Set.to_countable T).exists_eq_range hTne
  have heT : ∀ k, e k ∈ T := fun k ↦ he ▸ mem_range_self k
  set s : ℕ → (ι → ℝ≥0∞) × (ι → ℝ≥0∞) :=
    fun k ↦ (fun i ↦ ENNReal.ofReal ((e k).1 i), fun i ↦ ENNReal.ofReal ((e k).2 i)) with hs_def
  have hs : ∀ k i, (s k).2 i ≠ 0 := fun k i ↦ (ENNReal.ofReal_pos.2 ((heT k).1 i)).ne'
  set F : ℕ → Set (ι → ℝ≥0∞) := fun n ↦ ⋃ k ∈ Finset.range n, boxSet δ (s k).1 (s k).2
    with hF
  have hFm : ∀ n, MeasurableSet (F n) := fun n ↦
    Finset.measurableSet_biUnion _ fun k _ ↦ measurableSet_boxSet _ _ _
  set FE : ℕ → Set (ι → ℝ) := fun n ↦ ofRealVec ⁻¹' F n with hFE
  have hFEm : ∀ n, MeasurableSet (FE n) := fun n ↦ measurable_ofRealVec (hFm n)
  have hFE_O : ∀ n, FE n ⊆ O := fun n y hy ↦ by
    simp only [hFE, hF, mem_preimage, mem_iUnion] at hy
    obtain ⟨k, -, hk⟩ := hy
    exact hk.2
  have hFE_G : ∀ n, FE n ∩ posOrthant ⊆ O ∩ G := fun n y ⟨hy, hyQ⟩ ↦ by
    refine ⟨hFE_O n hy, ?_⟩
    simp only [hFE, hF, mem_preimage, mem_iUnion] at hy
    obtain ⟨k, -, hk⟩ := hy
    exact (heT k).2 y hyQ hk
  have hmono : Monotone fun n ↦ FE n ∩ posOrthant := by
    intro m n hmn y ⟨hy, hyQ⟩
    refine ⟨?_, hyQ⟩
    simp only [hFE, hF, mem_preimage, mem_iUnion, Finset.mem_range] at hy ⊢
    obtain ⟨k, hk, hk'⟩ := hy
    exact ⟨k, hk.trans_le hmn, hk'⟩
  have hunion : ⋃ n, FE n ∩ posOrthant = O ∩ G ∩ posOrthant := by
    refine subset_antisymm (iUnion_subset fun n ↦ subset_inter (hFE_G n) inter_subset_right) ?_
    rintro y ⟨hy, hyQ⟩
    obtain ⟨p, hp, hyp⟩ := hcover y hy hyQ
    obtain ⟨k, rfl⟩ := he ▸ hp
    refine mem_iUnion.2 ⟨k + 1, ?_, hyQ⟩
    simp only [hFE, hF, mem_preimage, mem_iUnion]
    exact ⟨k, Finset.mem_range.2 k.lt_succ_self, hyp⟩
  have hνsup : νE (O ∩ G) = ⨆ n, νE (FE n) := by
    rw [← measure_inter_conull (t := posOrthant) (by
      simpa using spectralExponentMeasureReal_compl_posOrthant (H := H)), ← hunion,
      hmono.measure_iUnion]
    exact iSup_congr fun n ↦ measure_inter_conull (by
      simpa using spectralExponentMeasureReal_compl_posOrthant (H := H))
  rw [hνsup, ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  -- convergence of the conditional mass of `FE n`
  set μs : ℝ → Measure (ι → ℝ≥0∞) := fun x ↦ (scaledLaw P X x).map ofRealVec with hμs
  have hμsfin : ∀ x (d : ι → ℝ≥0∞), (∀ i, d i ≠ 0) → μs x (exceedSet d) ≠ ∞ :=
    fun x d _ ↦ measure_ne_top _ _
  have hconv := fun d hd ↦ tendsto_scaledLaw_exceedSet hX hS hH (d := d) hd
  have hR1 : Tendsto (fun x ↦ (scaledLaw P X x).real (FE n)) atTop (𝓝 (νE.real (FE n))) := by
    have hlim : νE.real (FE n) = ν.real (F n) := by
      rw [measureReal_def, measureReal_def, hFE, spectralExponentMeasureReal_preimage hnt (hFm n)]
    rw [hlim]
    refine (tendsto_measureReal_iUnion_boxSet (μs := μs) hμsfin hνfin hconv hδ s hs n).congr
      fun x ↦ ?_
    simp only [hμs]
    exact map_measureReal_apply measurable_ofRealVec (hFm n)
  have hR2 : Tendsto (fun x ↦ (scaledLaw P X x).real O) atTop (𝓝 (νE.real O)) := by
    have hlim : νE.real O = ν.real (exceedSet δ) := by
      rw [measureReal_def, measureReal_def, hO,
        spectralExponentMeasureReal_preimage hnt (measurableSet_exceedSet δ)]
    rw [hlim]
    refine (hconv δ hδ).congr fun x ↦ ?_
    exact map_measureReal_apply measurable_ofRealVec (measurableSet_exceedSet δ)

  have htend : Tendsto (fun x ↦ (scaledLaw P X x O)⁻¹ * scaledLaw P X x (FE n)) atTop
      (𝓝 ((νE O)⁻¹ * νE (FE n))) := by
    rw [inv_mul_eq_ofReal_div (measure_mono (hFE_O n)) hνEO]
    refine (ENNReal.tendsto_ofReal (hR1.div hR2 hνEO0)).congr fun x ↦ ?_
    rw [inv_mul_eq_ofReal_div (measure_mono (hFE_O n)) (measure_ne_top _ _)]
    rfl
  rw [← htend.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  calc scaledLaw P X x (FE n) = scaledLaw P X x (FE n ∩ posOrthant) :=
        (measure_inter_conull (by simpa using scaledLaw_compl_posOrthant hX h hx)).symm
    _ ≤ _ := measure_mono (hFE_G n)

end Weak

/-! ### Convergence of integrals -/

section Integrals

variable [Fintype ι] {H : Measure (ι → ℝ≥0∞)}

omit [Fintype ι] in
/-- `∫ f dm = m(O) ∫ f dm[|O]`
 when `m` lives on the orthant and `f` vanishes on the orthant
outside `O`. -/
lemma integral_eq_measureReal_mul_integral_cond {m : Measure (ι → ℝ)} {O : Set (ι → ℝ)}
    (hOfin : m O ≠ ∞) (hm : m posOrthantᶜ = 0) {f : (ι → ℝ) → ℝ}
    (hf : ∀ y ∈ posOrthant, y ∉ O → f y = 0) :
    ∫ y, f y ∂m = m.real O * ∫ y, f y ∂m[|O] := by
  have hae : ∀ᵐ y ∂m, y ∈ posOrthant :=
    (measure_eq_zero_iff_ae_notMem.1 hm).mono fun y hy ↦ not_not.1 hy
  have h1 : ∫ y in O, f y ∂m = ∫ y, f y ∂m :=
    setIntegral_eq_integral_of_ae_compl_eq_zero (hae.mono fun y hy hyO ↦ hf y hy hyO)
  rw [← h1, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.toReal_inv]
  rcases eq_or_ne (m O) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  · rw [measureReal_def, mul_inv_cancel₀ (ENNReal.toReal_pos h0 hOfin).ne', one_mul]

/-- The exponent measure of `{x | ∃ i, c < x i}` is `H(univ) / c` for `H` on the sphere. -/
lemma spectralExponentMeasure_exceedSet_const [SFinite H]
    (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) {c : ℝ≥0∞} (hc0 : c ≠ 0) :
    spectralExponentMeasure H (exceedSet fun _ ↦ c) = c⁻¹ * H univ := by
  rw [spectralExponentMeasure_exceedSet fun _ ↦ hc0, ← lintegral_const]
  exact lintegral_congr_ae (hH.mono fun w hw ↦ by dsimp only; rw [← ENNReal.iSup_div, hw, one_div])

lemma measure_univ_ne_zero_of_hasSpectralMeasure [Nonempty ι] {μ : Measure (ι → ℝ)}
    (h : IsSimpleMaxStable μ) (hS : HasSpectralMeasure μ H) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    H univ ≠ 0 := by
  intro h0
  haveI : IsFiniteMeasure H := ⟨by rw [h0]; exact ENNReal.zero_lt_top⟩
  have := hS.measure_univ_toReal hH
  rw [h0, ENNReal.toReal_zero] at this
  linarith [h.one_le_extremalCoefficient]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ι → ℝ} [IsFiniteMeasure H]
  (hX : Measurable X) (hS : HasSpectralMeasure (P.map X) H)
  (h : IsSimpleMaxStable (P.map X)) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
include hX hS h hH

/-- **Vague convergence of the scaled laws to the exponent measure**: `∫ f d(x P(X / x ∈ ·)) →
∫ f dν_H` for every bounded continuous `f` vanishing near the origin. -/
theorem tendsto_integral_scaledLaw [Nonempty ι] {f : (ι → ℝ) →ᵇ ℝ} (hf : VanishesNearZero f) :
    Tendsto (fun x ↦ ∫ y, f y ∂scaledLaw P X x) atTop
      (𝓝 (∫ y, f y ∂spectralExponentMeasureReal H)) := by
  have hle := ae_le_one_of_ae_iSup_eq_one hH
  have hnt := ae_ne_top_of_ae_le_one hle
  obtain ⟨r, hr, hfr⟩ := hf
  set δ : ι → ℝ≥0∞ := fun _ ↦ ENNReal.ofReal (r / 2) with hδdef
  have hδ0 : ENNReal.ofReal (r / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (half_pos hr)).ne'
  have hδ : ∀ i, δ i ≠ 0 := fun _ ↦ hδ0
  set O := ofRealVec ⁻¹' exceedSet δ with hO
  have hOm : MeasurableSet O := measurable_ofRealVec (measurableSet_exceedSet δ)
  set νE := spectralExponentMeasureReal H with hνE
  have hνEOeq : νE O = spectralExponentMeasure H (exceedSet δ) :=
    spectralExponentMeasureReal_preimage hnt (measurableSet_exceedSet δ)
  have hνEO : νE O ≠ ∞ := hνEOeq ▸ spectralExponentMeasure_exceedSet_ne_top hle hδ
  have hνEO0 : νE O ≠ 0 := by
    rw [hνEOeq, spectralExponentMeasure_exceedSet_const hH hδ0]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
      (measure_univ_ne_zero_of_hasSpectralMeasure h hS hH)
  have hf0 : ∀ y ∈ posOrthant, y ∉ O → f y = 0 := by
    intro y hyQ hyO
    refine hfr y ?_
    have hy : ∀ i, y i ≤ r / 2 := fun i ↦ by
      by_contra hc
      exact hyO ⟨i, (ENNReal.ofReal_lt_ofReal_iff (by linarith [not_le.1 hc])).2 (not_le.1 hc)⟩
    calc ‖y‖ ≤ r / 2 := (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hyQ i)]; exact hy i
      _ < r := half_lt_self hr
  -- the masses of `O`
  have hR2 : Tendsto (fun x ↦ (scaledLaw P X x).real O) atTop (𝓝 (νE.real O)) := by
    have hlim : νE.real O = (spectralExponentMeasure H).real (exceedSet δ) := by
      rw [measureReal_def, measureReal_def, hνEOeq]
    rw [hlim]
    refine (tendsto_scaledLaw_exceedSet hX hS hH hδ).congr fun x ↦ ?_
    exact map_measureReal_apply measurable_ofRealVec (measurableSet_exceedSet δ)
  have hev : ∀ᶠ x in atTop, scaledLaw P X x O ≠ 0 := by
    filter_upwards [hR2.eventually (lt_mem_nhds (ENNReal.toReal_pos hνEO0 hνEO))] with x hx
    exact fun h0 ↦ by simp [measureReal_def, h0] at hx
  -- weak convergence of the conditional laws
  let PM : ℝ → ProbabilityMeasure (ι → ℝ) := fun x ↦
    if hx : scaledLaw P X x O ≠ 0 then ⟨(scaledLaw P X x)[|O], cond_isProbabilityMeasure hx⟩
    else ⟨Measure.dirac 0, inferInstance⟩
  let PMlim : ProbabilityMeasure (ι → ℝ) :=
    ⟨νE[|O], cond_isProbabilityMeasure_of_finite hνEO0 hνEO⟩
  have hPMeq : ∀ᶠ x in atTop, (PM x : Measure (ι → ℝ)) = (scaledLaw P X x)[|O] :=
    hev.mono fun x hx ↦ by simp [PM, hx]
  have hT : Tendsto PM atTop (𝓝 PMlim) := by
    refine tendsto_of_forall_isOpen_le_liminf' fun G hG ↦ ?_
    have key := le_liminf_cond_scaledLaw hX hS h hH hδ hG
    have e1 : ((PMlim : ProbabilityMeasure (ι → ℝ)) : Measure (ι → ℝ)) G =
        (νE O)⁻¹ * νE (O ∩ G) := cond_apply hOm _ G
    rw [e1]
    refine key.trans (le_of_eq (liminf_congr ?_))
    filter_upwards [hPMeq] with x hx
    rw [hx, cond_apply hOm]
  have hI := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT f
  rw [integral_eq_measureReal_mul_integral_cond hνEO
    spectralExponentMeasureReal_compl_posOrthant hf0]
  have hI' : Tendsto (fun x ↦ ∫ y, f y ∂(scaledLaw P X x)[|O]) atTop
      (𝓝 (∫ y, f y ∂νE[|O])) := by
    refine hI.congr' ?_
    filter_upwards [hPMeq] with x hx
    rw [hx]
  refine (hR2.mul hI').congr' ?_
  · filter_upwards
 [eventually_gt_atTop 0] with x hx
    exact (integral_eq_measureReal_mul_integral_cond (measure_ne_top _ _)
      (scaledLaw_compl_posOrthant hX h hx) hf0).symm

end Integrals

/-! ### Simple max-stable vectors are regularly varying -/

section RegVar

variable [Fintype ι] {H : Measure (ι → ℝ≥0∞)}

/-- The exponent measure has no atom at the origin. -/
lemma spectralExponentMeasure_singleton_zero [SFinite H] (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    spectralExponentMeasure H {0} = 0 := by
  rw [spectralExponentMeasure, Measure.map_apply measurable_coneMap (measurableSet_singleton 0),
    Measure.prod_apply_symm (measurable_coneMap (measurableSet_singleton 0))]
  refine (lintegral_congr_ae (hH.mono fun w hw ↦ ?_)).trans lintegral_zero
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hw
  refine measure_mono_null (fun r hr ↦ ?_) (radialMeasure_Iic_zero (α := 1))
  simp only [mem_preimage, mem_singleton_iff] at hr
  have := congrFun hr i
  simp only [coneMap, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h0 | h0
  · exact ENNReal.ofReal_eq_zero.1 h0
  · exact absurd h0 hi

/-- On the sup-norm sphere, `‖w‖ = 1` in real coordinates. -/
lemma norm_toRealVec [Nonempty ι] {w : ι → ℝ≥0∞} (hw : ⨆ i, w i = 1) : ‖toRealVec w‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_) ?_
  · simp only [toRealVec]
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one, ← hw]; exact le_iSup w i)
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := w)
    have h1 : w i = 1 := hi.trans hw
    calc (1 : ℝ) = ‖toRealVec w i‖ := by simp [toRealVec, h1]
      _ ≤ _ := norm_le_pi_norm _ i

/-- The **normalized exponent measure** `ν_H / H(univ)` in real coordinates; for a normalized
spectral measure `H(univ)` is the extremal coefficient. -/
noncomputable def maxStableTailMeasure (H : Measure (ι → ℝ≥0∞)) : Measure (ι → ℝ) :=
  (H univ)⁻¹ • spectralExponentMeasureReal H

/-- **The spectral measure of the normalized exponent measure** (in the sense of
`RegularVariation/Multivariate.lean`, the law of `Y / ‖Y‖` under `μ` restricted to `{‖y‖ > 1}`) is
the normalized spectral measure `H / H(univ)` of the max-stable law. -/
theorem spectralMeasure_maxStableTailMeasure [Nonempty ι] [SFinite H]
    (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    spectralMeasure (maxStableTailMeasure H) = (H univ)⁻¹ • H.map toRealVec := by
  have hg : Measurable fun y : ι → ℝ ↦ ‖y‖⁻¹ • y := (measurable_norm.inv).smul measurable_id
  have hA : MeasurableSet {y : ι → ℝ | 1 < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  rw [maxStableTailMeasure, spectralMeasure, Measure.restrict_smul, Measure.map_smul]
  congr 1
  ext B hB
  have hset : MeasurableSet ((fun y : ι → ℝ ↦ ‖y‖⁻¹ • y) ⁻¹' B ∩ {y | 1 < ‖y‖}) := hg hB |>.inter hA
  rw [Measure.map_apply hg hB, Measure.restrict_apply (hg hB),
    Measure.map_apply measurable_toRealVec hB, spectralExponentMeasureReal,
    Measure.map_apply measurable_toRealVec hset, spectralExponentMeasure,
    Measure.map_apply measurable_coneMap (measurable_toRealVec hset),
    Measure.prod_apply_symm (measurable_coneMap (measurable_toRealVec hset)),
    ← lintegral_indicator_one (measurable_toRealVec hB)]
  refine lintegral_congr_ae (hH.mono fun w hw ↦ ?_)
  dsimp only
  have hcone (r : ℝ) : toRealVec (coneMap (r, w)) = max r 0 • toRealVec w := by
    funext i
    simp [toRealVec, coneMap, ENNReal.toReal_mul, ENNReal.toReal_ofReal']
  have hpre : (fun r : ℝ ↦ (r, w)) ⁻¹' (coneMap ⁻¹' (toRealVec ⁻¹'
      ((fun y : ι → ℝ ↦ ‖y‖⁻¹ • y) ⁻¹' B ∩ {y | 1 < ‖y‖}))) = {r | 1 < r ∧ toRealVec w ∈ B} := by
    ext r
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hcone, norm_smul, norm_toRealVec hw,
      mul_one, Real.norm_eq_abs, abs_of_nonneg (le_max_right r 0)]
    constructor
    · rintro ⟨hB', h1⟩
      have hr : 1 < r := by
        rcases lt_max_iff.1 h1 with h | h
        · exact h
        · linarith
      rw [max_eq_left (by linarith), smul_smul, inv_mul_cancel₀ (by linarith), one_smul] at hB'
      exact ⟨hr, hB'⟩
    · rintro ⟨hr, hB'⟩
      rw [max_eq_left (by linarith), smul_smul, inv_mul_cancel₀ (by linarith), one_smul]
      exact ⟨hB', by simpa using hr⟩
  rw [hpre]
  by_cases hwB : toRealVec w ∈ B
  · simp only [hwB, and_true, indicator_of_mem (show w ∈ toRealVec ⁻¹' B from hwB),
      Pi.one_apply]
    rw [show {r : ℝ | 1 < r} = Ioi 1 from rfl, radialMeasure_Ioi one_pos one_pos]
    simp
  · simp [hwB]
  · exact hg.aemeasurable

variable [IsFiniteMeasure H] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {X : Ω → ι → ℝ}
  (hX : Measurable X) (hS : HasSpectralMeasure (P.map X) H)
  (h : IsSimpleMaxStable (P.map X)) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
include hX hS h hH

/-- **The tail of the norm**: `P(‖X‖ > x) = 1 - exp (-θ / x)`, `θ = H(univ)`. -/
theorem measureReal_lt_norm {x : ℝ} (hx : 0 < x) :
    P.real {ω | x < ‖X ω‖} = 1 - Real.exp (-(x⁻¹ * (H univ).toReal)) := by
  have hpos := ae_of_ae_map hX.aemeasurable h.ae_forall_pos
  have hint : ∫⁻ w, ⨆ i, w i / (1 : ι → ℝ≥0∞) i ∂H = H univ := by
    rw [← lintegral_one]
    exact lintegral_congr_ae (hH.mono fun w hw ↦ by simp [hw])
  rw [measureReal_congr (t := {ω | ofRealVec (x⁻¹ • X ω) ∈ exceedSet 1}) ?_,
    measureReal_exceedSet (d := (1 : ι → ℝ≥0∞)) hX hS hH hx (fun _ ↦ one_ne_zero), hint]
  refine Filter.eventuallyEqSet_iff.2 (hpos.mono fun ω hω ↦ ?_)
  simp only [mem_ofPred_eq, exceedSet, ofRealVec, Pi.one_apply, Pi.smul_apply, smul_eq_mul,
    ENNReal.one_lt_ofReal]
  rw [← not_le, pi_norm_le_iff_of_nonneg hx.le]
  push Not
  refine exists_congr fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_of_pos (hω i), inv_mul_eq_div, one_lt_div hx]

/-- **Simple max-stable vectors are regularly varying** ([Res87, Proposition 5.15]; [dHF, §6.1]):
a random vector `X` whose law is simple max-stable with spectral measure `H` on the sup-norm
sphere is regularly varying with index `1`, and its exponent measure is the normalized exponent
measure `ν_H / H(univ)` of the max-stable law. -/
theorem IsSimpleMaxStable.isRegVarVector [Nonempty ι] :
    IsRegVarVector P X 1 (maxStableTailMeasure H) := by
  have hle := ae_le_one_of_ae_iSup_eq_one hH
  have hnt := ae_ne_top_of_ae_le_one hle
  have hH0 := measure_univ_ne_zero_of_hasSpectralMeasure h hS hH
  set θ := (H univ).toReal with hθdef
  have hθ : 0 < θ := ENNReal.toReal_pos hH0 (measure_ne_top _ _)
  set T : ℝ → ℝ := fun x ↦ P.real {ω | x < ‖X ω‖} with hTdef
  have hT : ∀ x, 0 < x → T x = 1 - Real.exp (-(x⁻¹ * θ)) := fun x hx ↦
    measureReal_lt_norm hX hS h hH hx
  have hxT : Tendsto (fun x ↦ x * T x) atTop (𝓝 θ) := by
    refine (tendsto_mul_one_sub_exp hθ.le).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [hT x hx]
  have hinv : (H univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hH0
  refine ⟨⟨?_, fun c hc ↦ ?_⟩, ?_, fun r hr ↦ ?_, fun f hf ↦ ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with x hx
    show 0 < T x
    rw [hT x hx, sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (neg_lt_zero.2 (by positivity))
  · -- `T(c x) / T(x) → 1 / c`
    have h1 := hxT.comp (tendsto_id.const_mul_atTop hc)
    have h2 := (tendsto_const_nhds (x := c)).mul hxT
    have := h1.div h2 (mul_pos hc hθ).ne'
    rw [show θ / (c * θ) = c ^ (-(1 : ℝ)) by rw [Real.rpow_neg_one]; field_simp] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 := hx.ne'
    have hc0 := hc.ne'
    simp only [Function.comp_apply, id, Pi.div_apply]
    field_simp
    rfl

  · rw [maxStableTailMeasure, Measure.smul_apply, smul_eq_mul]
    refine mul_eq_zero_of_right _ (measure_mono_null (t := ofRealVec ⁻¹' {0}) ?_ ?_)
    · intro y hy
      rw [mem_singleton_iff.1 hy, mem_preimage, mem_singleton_iff]
      funext i
      simp [ofRealVec]

    · rw [spectralExponentMeasureReal_preimage hnt (measurableSet_singleton 0)]
      exact spectralExponentMeasure_singleton_zero hH
  · rw [maxStableTailMeasure, Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top hinv.lt_top ?_
    have hsub : {y : ι → ℝ | r < ‖y‖} ⊆
        posOrthantᶜ ∪ ofRealVec ⁻¹' exceedSet fun _ ↦ ENNReal.ofReal r := by
      intro y hy
      by_cases hyQ : y ∈ posOrthant
      · right
        have : ¬ ‖y‖ ≤ r := not_le.2 hy
        rw [pi_norm_le_iff_of_nonneg hr.le] at this
        push Not at this
        obtain ⟨i, hi⟩ := this
        rw [Real.norm_eq_abs, abs_of_nonneg (hyQ i)] at hi
        exact ⟨i, (ENNReal.ofReal_lt_ofReal_iff (hr.trans hi)).2 hi⟩
      · exact Or.inl hyQ
    refine (measure_mono hsub).trans_lt ((measure_union_le _ _).trans_lt ?_)
    rw [spectralExponentMeasureReal_compl_posOrthant, zero_add,
      spectralExponentMeasureReal_preimage hnt (measurableSet_exceedSet _)]
    exact (spectralExponentMeasure_exceedSet_ne_top hle
      fun _ ↦ (ENNReal.ofReal_pos.2 hr).ne').lt_top
  · -- `E[f(X / x)] / P(‖X‖ > x) → ∫ f dμ`
    have hlim : ∫ y, f y ∂maxStableTailMeasure H =
        θ⁻¹ * ∫ y, f y ∂spectralExponentMeasureReal H := by
      rw [maxStableTailMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
    rw [hlim]
    refine ((hxT.inv₀ hθ.ne').mul (tendsto_integral_scaledLaw hX hS h hH hf)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hXs : Measurable fun ω ↦ x⁻¹ • X ω := hX.const_smul x⁻¹
    have hI : ∫ y, f y ∂scaledLaw P X x = x * ∫ ω, f (x⁻¹ • X ω) ∂P := by
      rw [scaledLaw, integral_smul_measure, ENNReal.toReal_ofReal hx.le, smul_eq_mul,
        integral_map hXs.aemeasurable f.continuous.aestronglyMeasurable]
    rw [hI, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hx.ne', one_mul]

/-- The spectral measure of `X` in the sense of multivariate regular variation is the normalized
spectral measure of its max-stable law: `S = H / H(univ)`. -/
theorem IsSimpleMaxStable.spectralMeasure_eq [Nonempty ι] :
    IsRegVarVector P X 1 (maxStableTailMeasure H) ∧
      spectralMeasure (maxStableTailMeasure H) = (H univ)⁻¹ • H.map toRealVec :=
  ⟨IsSimpleMaxStable.isRegVarVector hX hS h hH, spectralMeasure_maxStableTailMeasure hH⟩

omit hS hH in
/-- **Simple max-stable vectors are regularly varying, with the max-stable spectral measure**:
for a random vector `X` with simple max-stable law, there is a finite measure `H` on the
sup-norm sphere, normalized by `∫ w i dH = 1` and with total mass the extremal coefficient `θ`,
such that `P(X ≤ y) = exp (-∫ max_i w i / y i dH)`, `X` is regularly varying with index `1`, and
its spectral measure (`RegularVariation/Multivariate.lean`) is `H / θ`. -/
theorem IsSimpleMaxStable.exists_isRegVarVector [Nonempty ι] :
    ∃ H : Measure (ι → ℝ≥0∞), IsFiniteMeasure H ∧ (∀ᵐ w ∂H, ⨆ i, w i = 1) ∧
      (∀ i, ∫⁻ w, w i ∂H = 1) ∧ HasSpectralMeasure (P.map X) H ∧
      (H univ).toReal = extremalCoefficient (P.map X) ∧
      IsRegVarVector P X 1 (maxStableTailMeasure H) ∧
      spectralMeasure (maxStableTailMeasure H) = (H univ)⁻¹ • H.map toRealVec := by
  obtain ⟨H, hfin, -, hsph, hnorm, hS⟩ := h.exists_hasSpectralMeasure
  exact ⟨H, hfin, hsph, hnorm, hS, hS.measure_univ_toReal hsph,
    IsSimpleMaxStable.isRegVarVector hX hS h hsph, spectralMeasure_maxStableTailMeasure hsph⟩

end RegVar

end ExtremeValueTheory
