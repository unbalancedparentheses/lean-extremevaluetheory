/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.MaxLinearCI.Graph
import ExtremeValueTheory.MaxStable.Uniqueness
import Mathlib.Probability.Independence.Conditional

/-!
# Extremal Conditional Independence for Finite-Ray and Recursive Max-Linear Models

This file formalizes Engelke–Ivanovs–Strokorb (`arXiv:2211.15769`, Definition 3.1) extremal
conditional independence `A ⊥ B | C [Λ]` using Mathlib's `ProbabilityTheory.CondIndepFun` (`⟂ᵢ`),
connects finite-ray exponent measures to `ExtremeValueTheory.MaxStable.Spectral` and
`ExtremeValueTheory.MaxStable.Uniqueness`, and proves:

1. **Theorem 1 (`extremalCondIndep_rayExponentMeasure_iff`)**: For any finite-ray exponent measure
   `Λ = ∑ k, (radialMeasure 1).map (r ↦ r • b k)` with `b k i ≥ 0` and pairwise disjoint
   `A, B, C : Finset V`,
   `ExtremalCondIndep Λ A B C ↔ RayCICondition b A B C`.
2. **Theorem 2 (`MaxLinearModel.isStarSeparated_imp_extremalCondIndep` and
   `MaxLinearModel.isDSeparated_imp_extremalCondIndep`)**: For every finite DAG `G`, every positive
   recursive max-linear model `M` on `G`, and every pairwise disjoint `A, B, C : Finset V`,
   `d-separation → *-separation → footprint separation → extremal conditional independence`.

## References

* S. Engelke, J. Ivanovs, and K. Strokorb, *Graphical models for infinite measures with
  applications to extremes*, arXiv:2211.15769 (2022), Definition 3.1.
* S. Engelke, M. Hentschel, M. Lalancette, and F. Röttger, *Graphical models for multivariate
  extremes*, arXiv:2402.02187 (2024).
* C. Améndola, C. Klüppelberg, S. Lauritzen, and N. M. Tran, *Conditional independence in
  max-linear Bayesian networks*, Ann. Appl. Probab. 32 (2022), arXiv:2002.09233.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace ExtremeValueTheory

namespace MaxLinearCI

/-! ### Scaling of `radialMeasure 1` -/

/-- Exact scaling invariance of `r ^ (-2) dr`: the pushforward of `radialMeasure 1` under `r ↦ c * r`
(`c > 0`) equals `c • radialMeasure 1`. -/
lemma radialMeasure_one_map_mul {c : ℝ} (hc : 0 < c) :
    (radialMeasure 1).map (fun r : ℝ ↦ c * r) = ENNReal.ofReal c • radialMeasure 1 := by
  have hm : Measurable fun r : ℝ ↦ c * r := measurable_const.mul measurable_id
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul,
    radialMeasure, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    Measure.restrict_restrict (hm hs), Measure.restrict_restrict hs]
  have hpre : (fun r : ℝ ↦ c * r) ⁻¹' s ∩ Ioi 0 = (fun r : ℝ ↦ c * r) ⁻¹' (s ∩ Ioi 0) := by
    ext r; simp [mul_pos_iff_of_pos_left hc]
  rw [hpre]
  have hmeas_s0 : MeasurableSet (s ∩ Ioi 0) := hs.inter measurableSet_Ioi
  rw [← lintegral_indicator (hm hmeas_s0), ← lintegral_indicator hmeas_s0]
  have hcomp :
      ∫⁻ r, ((fun r : ℝ ↦ c * r) ⁻¹' (s ∩ Ioi 0)).indicator
          (fun r ↦ ENNReal.ofReal (1 * r ^ (-1 - 1 : ℝ))) r =
      ∫⁻ r, (s ∩ Ioi 0).indicator
          (fun t ↦ ENNReal.ofReal (c ^ (2 : ℝ) * (1 * t ^ (-1 - 1 : ℝ)))) (c * r) := by
    refine lintegral_congr fun r ↦ ?_
    by_cases hr : c * r ∈ s ∩ Ioi 0
    · have hr0 : 0 < r := (mul_pos_iff_of_pos_left hc).1 hr.2
      rw [indicator_of_mem hr, indicator_of_mem (show r ∈ (fun r ↦ c * r) ⁻¹' (s ∩ Ioi 0) from hr)]
      congr 1
      have hpow : (c * r) ^ (-1 - 1 : ℝ) = c ^ (-2 : ℝ) * r ^ (-2 : ℝ) := by
        rw [show (-1 - 1 : ℝ) = -2 by norm_num, Real.mul_rpow hc.le hr0.le]
      rw [one_mul, one_mul, hpow, show (-1 - 1 : ℝ) = -2 by norm_num, ← mul_assoc,
        ← Real.rpow_add hc]
      norm_num
    · rw [indicator_of_notMem hr, indicator_of_notMem (show r ∉ (fun r ↦ c * r) ⁻¹' (s ∩ Ioi 0) from hr)]
  have hpos_inv : 0 < c⁻¹ := inv_pos.2 hc
  have hg_meas : Measurable ((s ∩ Ioi 0).indicator
      (fun t : ℝ ↦ ENNReal.ofReal (c ^ (2 : ℝ) * (1 * t ^ (-1 - 1 : ℝ))))) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_const.mul (measurable_id.pow_const _)))).indicator hmeas_s0
  rw [hcomp, ← lintegral_map hg_meas hm, Real.map_volume_mul_left hc.ne', lintegral_smul_measure,
    smul_eq_mul, abs_of_pos hpos_inv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun t ↦ ?_
  by_cases ht : t ∈ s ∩ Ioi 0
  · rw [indicator_of_mem ht, indicator_of_mem ht, ← ENNReal.ofReal_mul hpos_inv.le,
      ← ENNReal.ofReal_mul hc.le]
    congr 1
    have hsq : c⁻¹ * c ^ (2 : ℝ) = c := by
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq, ← mul_assoc,
        inv_mul_cancel₀ hc.ne', one_mul]
    rw [← mul_assoc, hsq]
  · simp [indicator_of_notMem ht]

/-- Change of variables `t = c * r` for `lintegral` with respect to `radialMeasure 1`. -/
lemma lintegral_radialMeasure_one_comp_mul {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ r, f (c * r) ∂(radialMeasure 1) = ENNReal.ofReal c * ∫⁻ t, f t ∂(radialMeasure 1) := by
  have hm : Measurable fun r : ℝ ↦ c * r := measurable_const.mul measurable_id
  rw [← lintegral_map hf hm, radialMeasure_one_map_mul hc, lintegral_smul_measure, smul_eq_mul]

/-- Change of variables `t = c * r` for Bochner `integral` with respect to `radialMeasure 1`. -/
lemma integral_radialMeasure_one_comp_mul {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∫ r, f (c * r) ∂(radialMeasure 1) = c * ∫ t, f t ∂(radialMeasure 1) := by
  have hm : Measurable fun r : ℝ ↦ c * r := measurable_const.mul measurable_id
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, radialMeasure_one_map_mul hc,
    integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul]

lemma ae_pos_radialMeasure_one : ∀ᵐ r ∂(radialMeasure 1), 0 < r := by
  rw [ae_iff]
  have h : {r : ℝ | ¬ 0 < r} = Iic 0 := by ext; simp
  rw [h]
  exact radialMeasure_Iic_zero

/-! ### Finite-ray exponent measures and bridge to `MaxStable.Spectral` -/

/-- The **finite-ray exponent measure** generated by ray vectors `b : κ → V → ℝ`:
`Λ(E) = ∑ k, ∫_{0}^{∞} 1_E(r • b k) r ^ (-2) dr`. -/
noncomputable def rayExponentMeasure {V κ : Type*} [Fintype κ] (b : κ → V → ℝ) :
    Measure (V → ℝ) :=
  ∑ k : κ, (radialMeasure 1).map (fun r : ℝ ↦ fun i : V ↦ r * b k i)

/-- The **exponent measure** of a recursive max-linear model `M` on a finite DAG `G`. -/
noncomputable def MaxLinearModel.exponentMeasure {V : Type*} [Fintype V] [DecidableEq V]
    {G : DAG V} (M : MaxLinearModel G) : Measure (V → ℝ) :=
  rayExponentMeasure (fun k i ↦ M.coeff i k)

lemma map_finset_sum_measure {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) (s : Finset ι) (m : ι → Measure α) :
    (∑ i ∈ s, m i).map f = ∑ i ∈ s, (m i).map f := by
  ext A hA
  simp [Measure.map_apply hf hA]

lemma restrict_finsetSum {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (m : ι → Measure α) (t : Set α) :
    (∑ i ∈ s, m i).restrict t = ∑ i ∈ s, (m i).restrict t := by
  ext A hA
  simp [Measure.restrict_apply hA, Measure.finsetSum_apply]

lemma ae_finsetSum_measure_iff {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (m : ι → Measure α) {p : α → Prop} :
    (∀ᵐ x ∂(∑ i ∈ s, m i), p x) ↔ ∀ i ∈ s, ∀ᵐ x ∂(m i), p x := by
  simp only [ae_iff, Measure.finsetSum_apply, Finset.sum_eq_zero_iff]

/-- Bridge to `MaxStable.Uniqueness.spectralExponentMeasure`: pushing `rayExponentMeasure b`
forward to `V → ℝ≥0∞` via `ENNReal.ofReal` equals `spectralExponentMeasure` of the discrete
spectral measure `∑ k, δ_{ENNReal.ofReal ∘ b k}`. -/
theorem rayExponentMeasure_map_ofReal {V κ : Type*} [Fintype κ] (b : κ → V → ℝ)
    (_hb : ∀ k i, 0 ≤ b k i) :
    (rayExponentMeasure b).map (fun x i ↦ ENNReal.ofReal (x i)) =
      spectralExponentMeasure (∑ k : κ, Measure.dirac (fun i : V ↦ ENNReal.ofReal (b k i))) := by
  classical
  have hofReal : Measurable (fun x : V → ℝ ↦ fun i : V ↦ ENNReal.ofReal (x i)) :=
    Measurable.of_eval fun i ↦ ENNReal.measurable_ofReal.comp (measurable_pi_apply i)
  have hray (k : κ) : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k i) :=
    Measurable.of_eval fun i ↦ measurable_id.mul_const (b k i)
  let H : Measure (V → ℝ≥0∞) := ∑ k : κ, Measure.dirac (fun i : V ↦ ENNReal.ofReal (b k i))
  have : IsFiniteMeasure H := by unfold H; infer_instance
  ext s hs
  rw [rayExponentMeasure, map_finset_sum_measure hofReal, Measure.finsetSum_apply,
    spectralExponentMeasure, Measure.map_apply measurable_coneMap hs,
    Measure.prod_apply_symm (measurable_coneMap hs),
    show (∑ k : κ, Measure.dirac (fun i : V ↦ ENNReal.ofReal (b k i))) = H from rfl,
    lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Measure.map_map hofReal (hray k), Measure.map_apply (hofReal.comp (hray k)) hs,
    lintegral_dirac' _ (measurable_measure_prodMk_right (measurable_coneMap hs))]
  have hpre : ((fun x : V → ℝ ↦ fun i : V ↦ ENNReal.ofReal (x i)) ∘ fun r i ↦ r * b k i) ⁻¹' s =ᵐ[radialMeasure 1]
      (fun r ↦ (r, fun i : V ↦ ENNReal.ofReal (b k i))) ⁻¹' (coneMap ⁻¹' s) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [ae_pos_radialMeasure_one] with r hr
    simp only [mem_preimage, Function.comp_apply]
    have heq : (fun i : V ↦ ENNReal.ofReal (r * b k i)) =
        fun i : V ↦ ENNReal.ofReal r * ENNReal.ofReal (b k i) := by
      funext i; exact ENNReal.ofReal_mul hr.le
    rw [heq]; rfl
  exact measure_congr hpre

/-- **Bridge to `MaxStable.Spectral`:** every normalized recursive max-linear model (`∑ k, coeff i k = 1`)
induces a simple max-stable probability distribution `ν` on `V → ℝ` with CDF
`F(y) = exp (-∑ k, max_i coeff i k / y i)`. -/
theorem exists_isSimpleMaxStable_maxLinear {V : Type*} [Fintype V] [DecidableEq V]
    {G : DAG V} (M : MaxLinearModel G) (hnorm : ∀ i, ∑ k : V, M.coeff i k = 1) :
    ∃ ν : Measure (V → ℝ), IsSimpleMaxStable ν ∧ ∀ y : V → ℝ, (∀ i, 0 < y i) →
      ν (Iic y) = ENNReal.ofReal (Real.exp
        (-(∑ k : V, ⨆ i : V, ENNReal.ofReal (M.coeff i k) / ENNReal.ofReal (y i)).toReal)) := by
  let H : Measure (V → ℝ≥0∞) := ∑ k : V, Measure.dirac (fun i : V ↦ ENNReal.ofReal (M.coeff i k))
  have : IsFiniteMeasure H := by unfold H; infer_instance
  have hH : ∀ i : V, ∫⁻ w, w i ∂H = 1 := by
    intro i
    rw [lintegral_finsetSum_measure]
    have hsum : ∑ k : V, ∫⁻ w, w i ∂Measure.dirac (fun j : V ↦ ENNReal.ofReal (M.coeff j k)) =
        ∑ k : V, ENNReal.ofReal (M.coeff i k) :=
      Finset.sum_congr rfl fun k _ ↦ lintegral_dirac' _ (measurable_pi_apply i)
    rw [hsum, ← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ M.coeff_nonneg i k), hnorm i,
      ENNReal.ofReal_one]
  obtain ⟨ν, hν, hcdf⟩ := exists_isSimpleMaxStable_of_spectralMeasure H hH
  refine ⟨ν, hν, fun y hy ↦ ?_⟩
  rw [hcdf y hy]
  have hsum_eq : (∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H) =
      ∑ k : V, ⨆ i : V, ENNReal.ofReal (M.coeff i k) / ENNReal.ofReal (y i) := by
    rw [lintegral_finsetSum_measure]
    exact Finset.sum_congr rfl fun k _ ↦
      lintegral_dirac' _ (Measurable.iSup fun i ↦ (measurable_pi_apply i).div_const _)
  rw [hsum_eq]

/-! ### Engelke–Ivanovs–Strokorb Definition 3.1 (`ExtremalCondIndep`) -/

/-- Coordinate projection `x ↦ x|_S` onto a finite subset `S ⊆ V`. -/
def coordProj {V : Type*} (S : Finset V) (x : V → ℝ) : S → ℝ := fun s ↦ x s.1

/-- Coordinate sub-projection `y ↦ y|_S` from `M → ℝ` to `S → ℝ` when `S ⊆ M`. -/
def subProj {V : Type*} {S M : Finset V} (hS : S ⊆ M) (y : M → ℝ) : S → ℝ :=
  fun s ↦ y ⟨s.1, hS s.2⟩

lemma measurable_coordProj {V : Type*} (S : Finset V) : Measurable (coordProj S) :=
  Measurable.of_eval fun s ↦ measurable_pi_apply s.1

lemma measurable_subProj {V : Type*} {S M : Finset V} (hS : S ⊆ M) : Measurable (subProj hS) :=
  Measurable.of_eval fun s ↦ measurable_pi_apply (⟨s.1, hS s.2⟩ : M)

/-- A valid product test set `R ∈ R(Λ_M)` in the sense of Engelke–Ivanovs–Strokorb
(`arXiv:2211.15769`, Definition 3.1): a Borel Cartesian product `R = ∏_{i ∈ M} R_i` with
`0 ∉ closure R` and `0 < Λ_M(R) < ∞`. -/
structure IsProductTestSet {V : Type*} (Λ : Measure (V → ℝ)) (M : Finset V)
    (R : Set (M → ℝ)) : Prop where
  isProd : ∃ Rc : M → Set ℝ, (∀ i, MeasurableSet (Rc i)) ∧ R = Set.univ.pi Rc
  zero_notMem_closure : (0 : M → ℝ) ∉ closure R
  measure_pos : 0 < Λ.map (coordProj M) R
  measure_ne_top : Λ.map (coordProj M) R ≠ ∞

lemma IsProductTestSet.measurableSet {V : Type*} {Λ : Measure (V → ℝ)} {M : Finset V}
    {R : Set (M → ℝ)} (hR : IsProductTestSet Λ M R) : MeasurableSet R := by
  rcases hR.isProd with ⟨Rc, hRc, rfl⟩
  exact MeasurableSet.univ_pi hRc

/-- Normalized conditional probability measure `P_R(·) = Λ_M(· ∩ R) / Λ_M(R)` on `M → ℝ`. -/
noncomputable def condProbMeasure {V : Type*} (Λ : Measure (V → ℝ)) (M : Finset V)
    (R : Set (M → ℝ)) : Measure (M → ℝ) :=
  (Λ.map (coordProj M) R)⁻¹ • ((Λ.map (coordProj M)).restrict R)

lemma isProbabilityMeasure_condProbMeasure {V : Type*} {Λ : Measure (V → ℝ)} {M : Finset V}
    {R : Set (M → ℝ)} (hpos : 0 < Λ.map (coordProj M) R) (htop : Λ.map (coordProj M) R ≠ ∞) :
    IsProbabilityMeasure (condProbMeasure Λ M R) := by
  constructor
  rw [condProbMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel hpos.ne' htop]

/-- **Extremal conditional independence `A ⊥ B | C [Λ]`** (Engelke–Ivanovs–Strokorb,
`arXiv:2211.15769`, Definition 3.1): for every product test set `R ∈ R(Λ_{A ∪ B ∪ C})`, the
coordinate projections `Y_A` and `Y_B` are conditionally independent given `Y_C` under the
probability measure `P_R = Λ_M(· ∩ R) / Λ_M(R)`. -/
def ExtremalCondIndep {V : Type*} [DecidableEq V] (Λ : Measure (V → ℝ))
    (A B C : Finset V) : Prop :=
  let M : Finset V := A ∪ B ∪ C
  have hA : A ⊆ M := Finset.subset_union_left.trans Finset.subset_union_left
  have hB : B ⊆ M := Finset.subset_union_right.trans Finset.subset_union_left
  have hC : C ⊆ M := Finset.subset_union_right
  ∀ (R : Set (M → ℝ)) (hR : IsProductTestSet Λ M R),
    haveI : IsProbabilityMeasure (condProbMeasure Λ M R) :=
      isProbabilityMeasure_condProbMeasure hR.measure_pos hR.measure_ne_top
    (subProj hA) ⟂ᵢ[subProj hC, measurable_subProj hC; condProbMeasure Λ M R] (subProj hB)

/-- **Multivariate Pareto conditional independence** (Engelke–Hitz 2020): conditional independence
`Y_A ⟂ᵢ[Y_C] Y_B` under the multivariate Pareto law `Λ_M(· ∩ {∃ i, y i > 1}) / Λ_M({∃ i, y i > 1})`. -/
def ParetoCondIndep {V : Type*} [DecidableEq V] (Λ : Measure (V → ℝ))
    (A B C : Finset V) : Prop :=
  let M : Finset V := A ∪ B ∪ C
  let PSet : Set (M → ℝ) := {y : M → ℝ | ∃ i : M, 1 < y i}
  have hA : A ⊆ M := Finset.subset_union_left.trans Finset.subset_union_left
  have hB : B ⊆ M := Finset.subset_union_right.trans Finset.subset_union_left
  have hC : C ⊆ M := Finset.subset_union_right
  ∀ (hpos : 0 < Λ.map (coordProj M) PSet) (htop : Λ.map (coordProj M) PSet ≠ ∞),
    haveI : IsProbabilityMeasure (condProbMeasure Λ M PSet) :=
      isProbabilityMeasure_condProbMeasure hpos htop
    (subProj hA) ⟂ᵢ[subProj hC, measurable_subProj hC; condProbMeasure Λ M PSet] (subProj hB)

/-- **Deterministic-function criterion for conditional independence:** if `f =ᵐ[μ] φ ∘ h` for a
measurable function `φ`, then `f` is conditionally independent of EVERY measurable `g` given `h`. -/
theorem condIndepFun_of_ae_eq_comp {Ω β γ δ : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → β} {g : Ω → γ} {h : Ω → δ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {φ : δ → β} (hφ : Measurable φ) (hae : f =ᵐ[μ] φ ∘ h) :
    f ⟂ᵢ[h, hh; μ] g := by
  rw [condIndepFun_iff _ _ f g hf hg μ]
  rintro t1 t2 ⟨s1, hs1, rfl⟩ ⟨s2, hs2, rfl⟩
  let m' := MeasurableSpace.comap h inferInstance
  have hm' : m' ≤ mΩ := hh.comap_le
  let u1 : Set Ω := h ⁻¹' (φ ⁻¹' s1)
  have hu1_m' : MeasurableSet[m'] u1 := ⟨φ ⁻¹' s1, hφ hs1, rfl⟩
  have hu1_eq : (f ⁻¹' s1).indicator (1 : Ω → ℝ) =ᵐ[μ] u1.indicator 1 := by
    filter_upwards [hae] with ω hω
    by_cases hmem : f ω ∈ s1
    · have hu : ω ∈ u1 := by simpa [u1, hω] using hmem
      simp only [Set.indicator, Set.mem_preimage, hmem, hu, ↓reduceIte]
    · have hu : ω ∉ u1 := by simpa [u1, hω] using hmem
      simp only [Set.indicator, Set.mem_preimage, hmem, hu, ↓reduceIte]
  have hinter_eq : (f ⁻¹' s1 ∩ g ⁻¹' s2).indicator (1 : Ω → ℝ) =ᵐ[μ]
      u1.indicator ((g ⁻¹' s2).indicator 1) := by
    filter_upwards [hae] with ω hω
    by_cases hmem : f ω ∈ s1
    · have hu : ω ∈ u1 := by simpa [u1, hω] using hmem
      by_cases hmem2 : g ω ∈ s2
      · simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, hmem, hmem2, hu, and_self,
          ↓reduceIte]
      · simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, hmem, hmem2, hu, and_false,
          ↓reduceIte]
    · have hu : ω ∉ u1 := by simpa [u1, hω] using hmem
      simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, hmem, hu, false_and, ↓reduceIte]
  have hc1 : μ⟦f ⁻¹' s1 | m'⟧ =ᵐ[μ] u1.indicator 1 := by
    refine (condExp_congr_ae hu1_eq).trans ?_
    exact (condExp_of_stronglyMeasurable hm'
      (stronglyMeasurable_const.indicator hu1_m')
      (integrable_const (1 : ℝ) |>.indicator (hm' _ hu1_m'))).eventuallyEq
  have hc12 : μ⟦f ⁻¹' s1 ∩ g ⁻¹' s2 | m'⟧ =ᵐ[μ] u1.indicator (μ⟦g ⁻¹' s2 | m'⟧) := by
    refine (condExp_congr_ae hinter_eq).trans ?_
    exact condExp_indicator (integrable_const (1 : ℝ) |>.indicator (hg hs2)) hu1_m'
  filter_upwards [hc1, hc12] with ω h1 h12
  rw [h12, Pi.mul_apply, h1]
  by_cases hu : ω ∈ u1
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]

/-! ### Explicit conditional expectation formula for finite-ray measures -/

section RayCondExp

variable {V κ : Type*} [Fintype κ] [DecidableEq V]

omit [Fintype κ] [DecidableEq V] in
/-- Helper: `0 ∉ closure R` for `R ⊆ M → ℝ` implies `R` is bounded away from `0` in sup-norm. -/
lemma exists_pos_of_zero_notMem_closure {M : Finset V} {R : Set (M → ℝ)}
    (h0 : (0 : M → ℝ) ∉ closure R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ R, ∃ i : M, ε ≤ |y i| := by
  rw [Metric.mem_closure_iff] at h0
  push Not at h0
  rcases h0 with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun y hy ↦ ?_⟩
  have hge : ε ≤ dist (0 : M → ℝ) y := hball y hy
  rw [dist_zero_left] at hge
  by_contra h
  push Not at h
  have hlt : ‖y‖ < ε := by
    rw [pi_norm_lt_iff hε]
    intro i; simpa [Real.norm_eq_abs] using h i
  linarith

omit [DecidableEq V] in
/-- For any finite-ray measure `Λ = rayExponentMeasure b` and any set `R` bounded away from `0`,
`Λ_M(R) < ∞` automatically! -/
lemma rayExponentMeasure_map_lt_top_of_zero_notMem_closure (b : κ → V → ℝ)
    (hb : ∀ k i, 0 ≤ b k i) {M : Finset V} {R : Set (M → ℝ)} (h0 : (0 : M → ℝ) ∉ closure R) :
    (rayExponentMeasure b).map (coordProj M) R < ∞ := by
  have h0' : (0 : M → ℝ) ∉ closure (closure R) := by rwa [closure_closure]
  obtain ⟨ε, hε, hR⟩ := exists_pos_of_zero_notMem_closure h0'
  have hproj : Measurable (coordProj M) := measurable_coordProj M
  refine lt_of_le_of_lt (measure_mono subset_closure) ?_
  rw [rayExponentMeasure, map_finset_sum_measure hproj]
  simp only [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun k _ ↦ ?_
  have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k i) :=
    Measurable.of_eval fun i ↦ measurable_id.mul_const (b k i)
  rw [Measure.map_map hproj hray, Measure.map_apply (hproj.comp hray) isClosed_closure.measurableSet]
  by_cases hzero : ∀ i : M, b k i.1 = 0
  · have hpre : ((coordProj M) ∘ fun r i ↦ r * b k i) ⁻¹' closure R = ∅ := by
      ext r; simp only [mem_preimage, Function.comp_apply, mem_empty_iff_false, iff_false]
      intro hr
      obtain ⟨i, hi⟩ := hR _ hr
      simp [coordProj, hzero i] at hi
      linarith
    rw [hpre, measure_empty]; exact ENNReal.zero_lt_top
  · push Not at hzero
    let Bmax : ℝ := Finset.univ.sup' ⟨hzero.choose, Finset.mem_univ _⟩ fun i : M ↦ b k i.1
    have hBpos : 0 < Bmax := by
      rcases hzero with ⟨i₀, hi₀⟩
      have hpos0 : 0 < b k i₀.1 := lt_of_le_of_ne (hb k i₀.1) (Ne.symm hi₀)
      exact lt_of_lt_of_le hpos0 (Finset.le_sup' (fun i : M ↦ b k i.1) (Finset.mem_univ i₀))
    have hsub : ((coordProj M) ∘ fun r i ↦ r * b k i) ⁻¹' closure R ∩ Ioi 0 ⊆ Ioi (ε / (2 * Bmax)) := by
      intro r ⟨hrR, hr0⟩
      obtain ⟨i, hi⟩ := hR _ hrR
      simp only [coordProj, Function.comp_apply] at hi
      rw [abs_of_nonneg (mul_nonneg hr0.le (hb k i.1))] at hi
      have hle : r * b k i.1 ≤ r * Bmax :=
        mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j : M ↦ b k j.1) (Finset.mem_univ i)) hr0.le
      have h1 : ε / (2 * Bmax) < ε / Bmax := by
        rw [div_lt_div_iff₀ (by positivity) hBpos]; nlinarith
      exact lt_of_lt_of_le h1 ((div_le_iff₀ hBpos).2 (hi.trans hle))
    calc (radialMeasure 1) (((coordProj M) ∘ fun r i ↦ r * b k i) ⁻¹' closure R)
        ≤ (radialMeasure 1) ((((coordProj M) ∘ fun r i ↦ r * b k i) ⁻¹' closure R ∩ Ioi 0) ∪ Iic 0) :=
          measure_mono fun r hr ↦ by
            by_cases hr0 : 0 < r
            · exact Or.inl ⟨hr, hr0⟩
            · exact Or.inr (not_lt.1 hr0)
      _ ≤ (radialMeasure 1) (((coordProj M) ∘ fun r i ↦ r * b k i) ⁻¹' closure R ∩ Ioi 0) +
            (radialMeasure 1) (Iic 0) := measure_union_le _ _
      _ ≤ (radialMeasure 1) (Ioi (ε / (2 * Bmax))) + 0 := by
          rw [radialMeasure_Iic_zero]
          exact add_le_add_left (measure_mono hsub) 0
      _ < ∞ := by
          rw [add_zero, radialMeasure_Ioi one_pos (by positivity)]
          exact ENNReal.ofReal_lt_top

/-- Helper: splitting a product set `R = Set.univ.pi Rc` on `M = A ∪ B ∪ C` into its `A, B, C`
factors. -/
lemma mem_pi_iff_subProj {A B C : Finset V} {Rc : (A ∪ B ∪ C : Finset V) → Set ℝ}
    (y : (A ∪ B ∪ C : Finset V) → ℝ) :
    y ∈ Set.univ.pi Rc ↔
      subProj (Finset.subset_union_left.trans Finset.subset_union_left : A ⊆ A ∪ B ∪ C) y ∈
        Set.univ.pi (fun a : A ↦ Rc ⟨a.1, (Finset.subset_union_left.trans Finset.subset_union_left) a.2⟩) ∧
      subProj (Finset.subset_union_right.trans Finset.subset_union_left : B ⊆ A ∪ B ∪ C) y ∈
        Set.univ.pi (fun b : B ↦ Rc ⟨b.1, (Finset.subset_union_right.trans Finset.subset_union_left) b.2⟩) ∧
      subProj (Finset.subset_union_right : C ⊆ A ∪ B ∪ C) y ∈
        Set.univ.pi (fun c : C ↦ Rc ⟨c.1, Finset.subset_union_right c.2⟩) := by
  simp only [Set.mem_univ_pi, subProj]
  constructor
  · intro hy
    exact ⟨fun a ↦ hy _, fun b ↦ hy _, fun c ↦ hy _⟩
  · rintro ⟨hyA, hyB, hyC⟩ ⟨i, hi⟩
    rcases Finset.mem_union.1 hi with hiAB | hiC
    · rcases Finset.mem_union.1 hiAB with hiA | hiB
      · exact hyA ⟨i, hiA⟩
      · exact hyB ⟨i, hiB⟩
    · exact hyC ⟨i, hiC⟩

omit [Fintype κ] [DecidableEq V] in
/-- Helper: sum of `rayDir` coordinates equals `1` when `rayL1Norm > 0`. -/
lemma sum_rayDir {b : V → ℝ} {C : Finset V} (hpos : 0 < rayL1Norm b C) :
    ∑ c : C, rayDir b C c = 1 := by
  simp only [rayDir, ← Finset.sum_div, Finset.sum_coe_sort C b]
  exact div_self hpos.ne'

/-- Explicit measurable conditional probability function `pE : (C → ℝ) → ℝ` for the event
`(Y_A, Y_B) ∈ E` given `Y_C = yC` under `(rayExponentMeasure b)_M` restricted to a product box
`R = R_A × R_B × R_C`. -/
noncomputable def rayCondProb (b : κ → V → ℝ) (A B C : Finset V)
    (RA : Set (A → ℝ)) (RB : Set (B → ℝ)) (E : Set ((A → ℝ) × (B → ℝ)))
    (c₀ : ℝ) (yC : C → ℝ) : ℝ :=
  open Classical in
  if yC = 0 then c₀
  else
    let t : ℝ := ∑ c : C, yC c
    (∑ k : κ,
      if 0 < rayL1Norm (b k) C ∧ 0 < t ∧ yC = t • rayDir (b k) C ∧
         t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB ∧
         (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ E
      then rayL1Norm (b k) C else 0) /
    (∑ k : κ,
      if 0 < rayL1Norm (b k) C ∧ 0 < t ∧ yC = t • rayDir (b k) C ∧
         t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB
      then rayL1Norm (b k) C else 0)

omit [DecidableEq V] in
lemma measurable_rayCondProb (b : κ → V → ℝ) (A B C : Finset V)
    {RA : Set (A → ℝ)} {RB : Set (B → ℝ)} {E : Set ((A → ℝ) × (B → ℝ))}
    (hRA : MeasurableSet RA) (hRB : MeasurableSet RB) (hE : MeasurableSet E) (c₀ : ℝ) :
    Measurable (rayCondProb b A B C RA RB E c₀) := by
  classical
  unfold rayCondProb
  have ht : Measurable (fun yC : C → ℝ ↦ ∑ c : C, yC c) :=
    Finset.measurable_sum _ fun c _ ↦ measurable_pi_apply c
  refine Measurable.ite (measurableSet_singleton 0) measurable_const (Measurable.div ?_ ?_)
  · refine Finset.measurable_sum _ fun k _ ↦ Measurable.ite ?_ measurable_const measurable_const
    have h1 : MeasurableSet {yC : C → ℝ | 0 < rayL1Norm (b k) C} := MeasurableSet.const _
    have h2 : MeasurableSet {yC : C → ℝ | 0 < ∑ c : C, yC c} :=
      measurableSet_lt measurable_const ht
    have h3 : MeasurableSet {yC : C → ℝ | yC = (∑ c : C, yC c) • rayDir (b k) C} :=
      measurableSet_eq_fun measurable_id (ht.smul_const _)
    have h4 : MeasurableSet {yC : C → ℝ | (∑ c : C, yC c) • rayScaled (b k) C A ∈ RA} :=
      (ht.smul_const _) hRA
    have h5 : MeasurableSet {yC : C → ℝ | (∑ c : C, yC c) • rayScaled (b k) C B ∈ RB} :=
      (ht.smul_const _) hRB
    have h6 : MeasurableSet {yC : C → ℝ |
        ((∑ c : C, yC c) • rayScaled (b k) C A, (∑ c : C, yC c) • rayScaled (b k) C B) ∈ E} :=
      ((ht.smul_const _).prodMk (ht.smul_const _)) hE
    exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6))))
  · refine Finset.measurable_sum _ fun k _ ↦ Measurable.ite ?_ measurable_const measurable_const
    have h1 : MeasurableSet {yC : C → ℝ | 0 < rayL1Norm (b k) C} := MeasurableSet.const _
    have h2 : MeasurableSet {yC : C → ℝ | 0 < ∑ c : C, yC c} :=
      measurableSet_lt measurable_const ht
    have h3 : MeasurableSet {yC : C → ℝ | yC = (∑ c : C, yC c) • rayDir (b k) C} :=
      measurableSet_eq_fun measurable_id (ht.smul_const _)
    have h4 : MeasurableSet {yC : C → ℝ | (∑ c : C, yC c) • rayScaled (b k) C A ∈ RA} :=
      (ht.smul_const _) hRA
    have h5 : MeasurableSet {yC : C → ℝ | (∑ c : C, yC c) • rayScaled (b k) C B ∈ RB} :=
      (ht.smul_const _) hRB
    exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

omit [DecidableEq V] in
lemma rayCondProb_nonneg (b : κ → V → ℝ) (A B C : Finset V)
    (RA : Set (A → ℝ)) (RB : Set (B → ℝ)) (E : Set ((A → ℝ) × (B → ℝ)))
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (yC : C → ℝ) :
    0 ≤ rayCondProb b A B C RA RB E c₀ yC := by
  classical
  unfold rayCondProb
  split_ifs
  · exact hc₀
  · refine div_nonneg (Finset.sum_nonneg fun k _ ↦ ?_) (Finset.sum_nonneg fun k _ ↦ ?_)
    · split_ifs with h
      · exact h.1.le
      · exact le_rfl
    · split_ifs with h
      · exact h.1.le
      · exact le_rfl

omit [DecidableEq V] in
lemma rayCondProb_le_one (b : κ → V → ℝ) (A B C : Finset V)
    (RA : Set (A → ℝ)) (RB : Set (B → ℝ)) (E : Set ((A → ℝ) × (B → ℝ)))
    {c₀ : ℝ} (hc₀ : c₀ ≤ 1) (yC : C → ℝ) :
    rayCondProb b A B C RA RB E c₀ yC ≤ 1 := by
  unfold rayCondProb
  split_ifs
  · exact hc₀
  · refine div_le_one_of_le₀ ?_ (Finset.sum_nonneg fun k _ ↦ by
      split_ifs with h
      · exact h.1.le
      · exact le_rfl)
    refine Finset.sum_le_sum fun k _ ↦ ?_
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso; exact h2 ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1⟩
    · exact h2.1.le
    · exact le_rfl

/-- **Fundamental conditional expectation identity for finite-ray measures:**
for any product test set `R = R_A × R_B × R_C` of `Λ = rayExponentMeasure b` and any measurable
event `E ⊆ (A → ℝ) × (B → ℝ)`, the function `rayCondProb` is an explicit version of
`P_R[(Y_A, Y_B) ∈ E | σ(Y_C)]`. -/
lemma condExp_rayExponentMeasure_eq (b : κ → V → ℝ) (hb : ∀ k i, 0 ≤ b k i)
    {A B C : Finset V}
    {Rc : (A ∪ B ∪ C : Finset V) → Set ℝ} (hRc : ∀ i, MeasurableSet (Rc i))
    (hR : IsProductTestSet (rayExponentMeasure b) (A ∪ B ∪ C) (Set.univ.pi Rc))
    {E : Set ((A → ℝ) × (B → ℝ))} (hE : MeasurableSet E) :
    let M : Finset V := A ∪ B ∪ C
    let hA : A ⊆ M := Finset.subset_union_left.trans Finset.subset_union_left
    let hB : B ⊆ M := Finset.subset_union_right.trans Finset.subset_union_left
    let hC : C ⊆ M := Finset.subset_union_right
    let R : Set (M → ℝ) := Set.univ.pi Rc
    let RA : Set (A → ℝ) := Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩
    let RB : Set (B → ℝ) := Set.univ.pi fun b : B ↦ Rc ⟨b.1, hB b.2⟩
    let ΛM : Measure (M → ℝ) := (rayExponentMeasure b).map (coordProj M)
    let μR : Measure (M → ℝ) := condProbMeasure (rayExponentMeasure b) M R
    let S_E : Set (M → ℝ) := (fun y ↦ (subProj hA y, subProj hB y)) ⁻¹' E
    let c₀ : ℝ := (ΛM (R ∩ subProj hC ⁻¹' {0} ∩ S_E)).toReal /
        (ΛM (R ∩ subProj hC ⁻¹' {0})).toReal
    haveI : IsProbabilityMeasure μR :=
      isProbabilityMeasure_condProbMeasure hR.measure_pos hR.measure_ne_top
    (fun y ↦ rayCondProb b A B C RA RB E c₀ (subProj hC y)) =ᵐ[μR]
      μR⟦S_E | MeasurableSpace.comap (subProj hC) inferInstance⟧ := by
  classical
  intro M hA hB hC R RA RB ΛM μR S_E c₀
  have : IsProbabilityMeasure μR :=
    isProbabilityMeasure_condProbMeasure hR.measure_pos hR.measure_ne_top
  have hRA : MeasurableSet RA := MeasurableSet.univ_pi fun a ↦ hRc ⟨a.1, hA a.2⟩
  have hRB : MeasurableSet RB := MeasurableSet.univ_pi fun b ↦ hRc ⟨b.1, hB b.2⟩
  have hRC_m : MeasurableSet (Set.univ.pi fun c : C ↦ Rc ⟨c.1, hC c.2⟩) :=
    MeasurableSet.univ_pi fun c ↦ hRc ⟨c.1, hC c.2⟩
  let RC : Set (C → ℝ) := Set.univ.pi fun c : C ↦ Rc ⟨c.1, hC c.2⟩
  have hRm : MeasurableSet R := MeasurableSet.univ_pi hRc
  have hS_E_m : MeasurableSet S_E := ((measurable_subProj hA).prodMk (measurable_subProj hB)) hE
  have hp_meas : Measurable (rayCondProb b A B C RA RB E c₀) :=
    measurable_rayCondProb b A B C hRA hRB hE c₀
  have hc₀_nonneg : 0 ≤ c₀ := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hc₀_le_one : c₀ ≤ 1 := by
    have hfin : ΛM (R ∩ subProj hC ⁻¹' {0}) ≠ ∞ :=
      ne_top_of_le_ne_top hR.measure_ne_top (measure_mono inter_subset_left)
    have hle : (ΛM (R ∩ subProj hC ⁻¹' {0} ∩ S_E)).toReal ≤ (ΛM (R ∩ subProj hC ⁻¹' {0})).toReal :=
      ENNReal.toReal_mono hfin (measure_mono inter_subset_left)
    rcases (ENNReal.toReal_nonneg (a := ΛM (R ∩ subProj hC ⁻¹' {0}))).eq_or_lt with h0 | hpos
    · dsimp only [c₀]; rw [← h0, div_zero]; norm_num
    · exact (div_le_one hpos).2 hle
  have hbound : ∀ y : M → ℝ, ‖rayCondProb b A B C RA RB E c₀ (subProj hC y)‖ ≤ 1 := fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (rayCondProb_nonneg _ _ _ _ _ _ _ hc₀_nonneg _)]
    exact rayCondProb_le_one _ _ _ _ _ _ _ hc₀_le_one _
  have hint_g : Integrable (fun y ↦ rayCondProb b A B C RA RB E c₀ (subProj hC y)) μR :=
    Integrable.of_bound (hp_meas.comp (measurable_subProj hC)).aestronglyMeasurable 1
      (Eventually.of_forall hbound)
  -- Apply uniqueness of conditional expectation
  refine ae_eq_condExp_of_forall_setIntegral_eq (measurable_subProj hC).comap_le
    ((integrable_const (1 : ℝ)).indicator hS_E_m)
    (fun s _ _ ↦ hint_g.integrableOn)
    (fun s hs _ ↦ ?_)
    ((hp_meas.stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable)
  -- Unpack `s = subProj hC ⁻¹' EC`
  rcases hs with ⟨EC, hEC, rfl⟩
  have hs_m : MeasurableSet (subProj hC ⁻¹' EC) := (measurable_subProj hC) hEC
  rw [show (fun x ↦ S_E.indicator (fun _ ↦ (1 : ℝ)) x) = S_E.indicator 1 from rfl,
    integral_indicator_one hS_E_m, measureReal_def, Measure.restrict_apply hS_E_m]
  -- Unfold `μR = (ΛM R)⁻¹ • ΛM.restrict R` and cancel the positive scalar `(ΛM R)⁻¹.toReal`!
  have hscale_ne : (ΛM R)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hR.measure_pos.ne'
  rw [show μR = (ΛM R)⁻¹ • (ΛM.restrict R) from rfl,
    Measure.restrict_smul, integral_smul_measure, smul_eq_mul,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  congr 1
  -- Now prove the unnormalized identity on `ΛM.restrict R`:
  -- `∫ y in subProj hC ⁻¹' EC, pE (subProj hC y) ∂(ΛM.restrict R) = (ΛM (R ∩ subProj hC ⁻¹' EC ∩ S_E)).toReal`
  rw [Measure.restrict_apply (hS_E_m.inter hs_m), Measure.restrict_restrict hs_m]
  have hfin_R : IsFiniteMeasure (ΛM.restrict R) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hR.measure_ne_top.lt_top⟩
  -- Express `ΛM` as the finite sum of individual ray measures `μk k` on `M → ℝ`
  let rayM (k : κ) (r : ℝ) : M → ℝ := fun i ↦ r * b k i.1
  have hrayM (k : κ) : Measurable (rayM k) :=
    Measurable.of_eval fun i ↦ measurable_id.mul_const (b k i.1)
  let μk (k : κ) : Measure (M → ℝ) := (radialMeasure 1).map (rayM k)
  have hΛM_eq : ΛM = ∑ k : κ, μk k := by
    rw [show ΛM = (rayExponentMeasure b).map (coordProj M) from rfl,
      rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k i) :=
      Measurable.of_eval fun i ↦ measurable_id.mul_const (b k i)
    rw [Measure.map_map (measurable_coordProj M) hray]
    rfl
  have hμk_fin (k : κ) : (μk k) R ≠ ∞ := by
    have hle : (μk k) R ≤ ΛM R := by
      rw [hΛM_eq, Measure.finsetSum_apply]
      exact Finset.single_le_sum (f := fun j ↦ (μk j) R) (fun _ _ ↦ zero_le) (Finset.mem_univ k)
    exact ne_top_of_le_ne_top hR.measure_ne_top hle
  have hμk_restrict_fin (k : κ) : IsFiniteMeasure ((μk k).restrict R) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (hμk_fin k).lt_top⟩
  have hrestrict_sum : (ΛM.restrict R).restrict (subProj hC ⁻¹' EC) =
      ∑ k : κ, ((μk k).restrict R).restrict (subProj hC ⁻¹' EC) := by
    rw [hΛM_eq, restrict_finsetSum, restrict_finsetSum]
  have hint_k (k : κ) : Integrable (fun y ↦ rayCondProb b A B C RA RB E c₀ (subProj hC y))
      (((μk k).restrict R).restrict (subProj hC ⁻¹' EC)) :=
    Integrable.of_bound (hp_meas.comp (measurable_subProj hC)).aestronglyMeasurable 1
      (Eventually.of_forall hbound)
  -- Split LHS and RHS into `k` with `rayL1Norm (b k) C = 0` (`I₀`) vs `0 < rayL1Norm (b k) C` (`I₊`)
  have hLHS_sum :
      ∫ y in subProj hC ⁻¹' EC ∩ R, rayCondProb b A B C RA RB E c₀ (subProj hC y) ∂ΛM =
      ∑ k : κ, ∫ y in subProj hC ⁻¹' EC ∩ R, rayCondProb b A B C RA RB E c₀ (subProj hC y) ∂(μk k) := by
    have h1 : ΛM.restrict (subProj hC ⁻¹' EC ∩ R) = ∑ k : κ, (μk k).restrict (subProj hC ⁻¹' EC ∩ R) := by
      rw [hΛM_eq, restrict_finsetSum]
    rw [h1, integral_finsetSum_measure fun k _ ↦ ?_]
    rw [← Measure.restrict_restrict hs_m]
    exact hint_k k
  have hRHS_sum :
      (ΛM ((S_E ∩ subProj hC ⁻¹' EC) ∩ R)).toReal =
      ∑ k : κ, ((μk k) ((S_E ∩ subProj hC ⁻¹' EC) ∩ R)).toReal := by
    rw [hΛM_eq, Measure.finsetSum_apply,
      ENNReal.toReal_sum fun k _ ↦ ne_top_of_le_ne_top (hμk_fin k) (measure_mono inter_subset_right)]
  rw [hLHS_sum, hRHS_sum]
  -- Partition `Finset.univ : Finset κ` into `K0 = {k | rayL1Norm (b k) C = 0}` and `Kp = {k | 0 < rayL1Norm (b k) C}`.
  have hnorm_nonneg (k : κ) : 0 ≤ rayL1Norm (b k) C :=
    Finset.sum_nonneg fun c _ ↦ hb k c
  let K0 : Finset κ := Finset.univ.filter fun k ↦ rayL1Norm (b k) C = 0
  let Kp : Finset κ := Finset.univ.filter fun k ↦ 0 < rayL1Norm (b k) C
  have hpart : ∀ f : κ → ℝ, ∑ k : κ, f k = (∑ k ∈ K0, f k) + (∑ k ∈ Kp, f k) := by
    intro f
    rw [← Finset.sum_union]
    · congr 1; ext k
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, K0, Kp]
      rcases (hnorm_nonneg k).eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · rw [Finset.disjoint_left]; intro k hk0 hkp
      simp only [Finset.mem_filter, K0, Kp] at hk0 hkp; linarith
  rw [hpart, hpart]
  congr 1
  · -- Part 1: rays `k ∈ K0` (where `subProj hC (rayM k r) = 0` for all `r`)
    have hzeroC : ∀ k ∈ K0, ∀ r : ℝ, subProj hC (rayM k r) = 0 := by
      intro k hk r
      have hsum0 : ∑ c ∈ C, b k c = 0 := (Finset.mem_filter.1 hk).2
      have hbc : ∀ c ∈ C, b k c = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun c _ ↦ hb k c).1 hsum0
      funext c; simp [subProj, rayM, hbc c.1 c.2]
    have hpos_not_zero : ∀ k ∈ Kp, ∀ᵐ r ∂(radialMeasure 1), subProj hC (rayM k r) ≠ 0 := by
      intro k hk
      have hpos : 0 < ∑ c ∈ C, b k c := (Finset.mem_filter.1 hk).2
      have hex : ∃ c ∈ C, 0 < b k c := by
        by_contra h; push Not at h
        have : ∑ c ∈ C, b k c = 0 := Finset.sum_eq_zero fun c hc ↦ le_antisymm (h c hc) (hb k c)
        linarith
      rcases hex with ⟨c, hcC, hcpos⟩
      filter_upwards [ae_pos_radialMeasure_one] with r hr hEq
      have hval := congrFun hEq ⟨c, hcC⟩
      simp only [subProj, rayM, Pi.zero_apply] at hval
      linarith [mul_pos hr hcpos]
    have hμk_zero_of_Kp : ∀ k ∈ Kp, (μk k) (R ∩ subProj hC ⁻¹' {0}) = 0 := by
      intro k hk
      rw [Measure.map_apply (hrayM k) (hRm.inter ((measurable_subProj hC) (measurableSet_singleton 0)))]
      refine measure_mono_null (fun r hr ↦ ?_) (ae_iff.1 (hpos_not_zero k hk))
      simp only [mem_preimage, mem_inter_iff, mem_singleton_iff] at hr
      simpa using hr.2
    have hμk_zero_E_of_Kp : ∀ k ∈ Kp, (μk k) (R ∩ subProj hC ⁻¹' {0} ∩ S_E) = 0 :=
      fun k hk ↦ measure_mono_null inter_subset_left (hμk_zero_of_Kp k hk)
    by_cases h0EC : (0 : C → ℝ) ∈ EC
    · -- Both sums equal `ΛM (R ∩ {yC = 0} ∩ S_E)`!
      have hLHS0 : ∑ k ∈ K0, ∫ y in subProj hC ⁻¹' EC ∩ R,
          rayCondProb b A B C RA RB E c₀ (subProj hC y) ∂(μk k) =
          c₀ * ∑ k ∈ K0, ((μk k) (R ∩ subProj hC ⁻¹' {0})).toReal := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hconst : ∀ᵐ y ∂((μk k).restrict (subProj hC ⁻¹' EC ∩ R)),
            rayCondProb b A B C RA RB E c₀ (subProj hC y) = c₀ := by
          refine ae_restrict_of_ae ?_
          change ∀ᵐ y ∂((radialMeasure 1).map (rayM k)),
            (rayCondProb b A B C RA RB E c₀ ∘ subProj hC) y = c₀
          rw [ae_map_iff (hrayM k).aemeasurable (measurableSet_eq_fun (hp_meas.comp (measurable_subProj hC)) measurable_const)]
          exact Eventually.of_forall fun r ↦ by simp [hzeroC k hk r, rayCondProb]
        rw [integral_congr_ae hconst, integral_const, smul_eq_mul, mul_comm, measureReal_def,
          Measure.restrict_apply_univ]
        congr 2
        rw [Measure.map_apply (hrayM k) (hs_m.inter hRm),
          Measure.map_apply (hrayM k) (hRm.inter ((measurable_subProj hC) (measurableSet_singleton 0)))]
        congr 1; ext r; simp [hzeroC k hk r, h0EC, and_comm]
      have hRHS0 : ∑ k ∈ K0, ((μk k) ((S_E ∩ subProj hC ⁻¹' EC) ∩ R)).toReal =
          ∑ k ∈ K0, ((μk k) (R ∩ subProj hC ⁻¹' {0} ∩ S_E)).toReal := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        congr 1
        rw [Measure.map_apply (hrayM k) ((hS_E_m.inter hs_m).inter hRm),
          Measure.map_apply (hrayM k) ((hRm.inter ((measurable_subProj hC) (measurableSet_singleton 0))).inter hS_E_m)]
        congr 1; ext r; simp [hzeroC k hk r, h0EC]; tauto
      have hden_eq : (ΛM (R ∩ subProj hC ⁻¹' {0})).toReal =
          ∑ k ∈ K0, ((μk k) (R ∩ subProj hC ⁻¹' {0})).toReal := by
        rw [hΛM_eq, Measure.finsetSum_apply,
          ENNReal.toReal_sum fun k _ ↦ ne_top_of_le_ne_top (hμk_fin k) (measure_mono inter_subset_left),
          hpart]
        have hKp0 : ∑ k ∈ Kp, ((μk k) (R ∩ subProj hC ⁻¹' {0})).toReal = 0 :=
          Finset.sum_eq_zero fun k hk ↦ by simp [hμk_zero_of_Kp k hk]
        rw [hKp0, add_zero]
      have hnum_eq : (ΛM (R ∩ subProj hC ⁻¹' {0} ∩ S_E)).toReal =
          ∑ k ∈ K0, ((μk k) (R ∩ subProj hC ⁻¹' {0} ∩ S_E)).toReal := by
        rw [hΛM_eq, Measure.finsetSum_apply,
          ENNReal.toReal_sum fun k _ ↦ ne_top_of_le_ne_top (hμk_fin k)
            (measure_mono (inter_subset_left.trans inter_subset_left)),
          hpart]
        have hKp0 : ∑ k ∈ Kp, ((μk k) (R ∩ subProj hC ⁻¹' {0} ∩ S_E)).toReal = 0 :=
          Finset.sum_eq_zero fun k hk ↦ by simp [hμk_zero_E_of_Kp k hk]
        rw [hKp0, add_zero]
      rw [hLHS0, hRHS0, ← hden_eq, ← hnum_eq]
      rcases (ENNReal.toReal_nonneg (a := ΛM (R ∩ subProj hC ⁻¹' {0}))).eq_or_lt with h0 | hpos
      · have hnum0 : (ΛM (R ∩ subProj hC ⁻¹' {0} ∩ S_E)).toReal = 0 := by
          have hfin : ΛM (R ∩ subProj hC ⁻¹' {0}) ≠ ∞ :=
            ne_top_of_le_ne_top hR.measure_ne_top (measure_mono inter_subset_left)
          exact le_antisymm (by rw [h0]; exact ENNReal.toReal_mono hfin (measure_mono inter_subset_left))
            ENNReal.toReal_nonneg
        rw [← h0, hnum0, mul_zero]
      · exact div_mul_cancel₀ _ hpos.ne'
    · -- `0 ∉ EC`: both sums over `K0` vanish!
      have hLHS0 : ∑ k ∈ K0, ∫ y in subProj hC ⁻¹' EC ∩ R,
          rayCondProb b A B C RA RB E c₀ (subProj hC y) ∂(μk k) = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        have hnull : (μk k) (subProj hC ⁻¹' EC ∩ R) = 0 := by
          rw [Measure.map_apply (hrayM k) (hs_m.inter hRm)]
          have : rayM k ⁻¹' (subProj hC ⁻¹' EC ∩ R) = ∅ := by
            ext r; simp [hzeroC k hk r, h0EC]
          rw [this, measure_empty]
        rw [Measure.restrict_eq_zero.2 hnull, integral_zero_measure]
      have hRHS0 : ∑ k ∈ K0, ((μk k) ((S_E ∩ subProj hC ⁻¹' EC) ∩ R)).toReal = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        have hnull : (μk k) ((S_E ∩ subProj hC ⁻¹' EC) ∩ R) = 0 := by
          rw [Measure.map_apply (hrayM k) ((hS_E_m.inter hs_m).inter hRm)]
          have : rayM k ⁻¹' ((S_E ∩ subProj hC ⁻¹' EC) ∩ R) = ∅ := by
            ext r; simp [hzeroC k hk r, h0EC]
          rw [this, measure_empty]
        simp [hnull]
      rw [hLHS0, hRHS0]
  · -- Part 2: rays `k ∈ Kp` (where `lam_k = rayL1Norm (b k) C > 0`)
    -- Rewrite each `k ∈ Kp` integral via change of variables `t = lam_k * r`!
    have hray_subA (k : κ) (hk : k ∈ Kp) (r : ℝ) :
        subProj hA (rayM k r) = (rayL1Norm (b k) C * r) • rayScaled (b k) C A := by
      have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
      funext a; simp only [subProj, rayM, Pi.smul_apply, smul_eq_mul, rayScaled]
      field_simp [hpos.ne']
    have hray_subB (k : κ) (hk : k ∈ Kp) (r : ℝ) :
        subProj hB (rayM k r) = (rayL1Norm (b k) C * r) • rayScaled (b k) C B := by
      have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
      funext b'; simp only [subProj, rayM, Pi.smul_apply, smul_eq_mul, rayScaled]
      field_simp [hpos.ne']
    have hray_subC (k : κ) (hk : k ∈ Kp) (r : ℝ) :
        subProj hC (rayM k r) = (rayL1Norm (b k) C * r) • rayDir (b k) C := by
      have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
      funext c; simp only [subProj, rayM, Pi.smul_apply, smul_eq_mul, rayDir]
      field_simp [hpos.ne']
    -- For each `k ∈ Kp`, define the integrable 1D functions on `ℝ` (in the rescaled coordinate `t`):
    let fL (k : κ) (t : ℝ) : ℝ :=
      if 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
         t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB
      then rayL1Norm (b k) C * rayCondProb b A B C RA RB E c₀ (t • rayDir (b k) C) else 0
    let fR (k : κ) (t : ℝ) : ℝ :=
      if 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
         t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB ∧
         (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ E
      then rayL1Norm (b k) C else 0
    -- Compute the LHS and RHS for each `k ∈ Kp` in terms of `fL k` and `fR k`:
    have hfL_meas (k : κ) : Measurable (fL k) := by
      refine Measurable.ite ?_ (measurable_const.mul (hp_meas.comp (measurable_id.smul_const _)))
        measurable_const
      exact (measurableSet_lt measurable_const measurable_id).inter
        (((measurable_id.smul_const _) (hEC.inter hRC_m)).inter
          (((measurable_id.smul_const _) hRA).inter ((measurable_id.smul_const _) hRB)))
    have hfR_meas (k : κ) : Measurable (fR k) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_lt measurable_const measurable_id).inter
        (((measurable_id.smul_const _) (hEC.inter hRC_m)).inter
          (((measurable_id.smul_const _) hRA).inter
            (((measurable_id.smul_const _) hRB).inter
              (((measurable_id.smul_const _).prodMk (measurable_id.smul_const _)) hE))))
    have hset_t_fin (k : κ) (hk : k ∈ Kp) :
        (radialMeasure 1) {t : ℝ | 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
          t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB} ≠ ∞ := by
      have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
      have hsub : {t : ℝ | 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
          t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB} ⊆
          (fun r ↦ rayL1Norm (b k) C * r) '' (rayM k ⁻¹' R) := by
        intro t ⟨ht, hEC', hA', hB'⟩
        refine ⟨t / rayL1Norm (b k) C, ?_, mul_div_cancel₀ t hpos.ne'⟩
        rw [mem_preimage, mem_pi_iff_subProj]
        rw [hray_subA k hk, hray_subB k hk, hray_subC k hk, mul_div_cancel₀ t hpos.ne']
        exact ⟨hA', hB', hEC'.2⟩
      have hle : (radialMeasure 1) {t : ℝ | 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
          t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB} ≤
          ENNReal.ofReal (rayL1Norm (b k) C)⁻¹ * (μk k) R := by
        have himg : (fun r ↦ rayL1Norm (b k) C * r) ⁻¹'
            ((fun r ↦ rayL1Norm (b k) C * r) '' (rayM k ⁻¹' R)) = rayM k ⁻¹' R := by
          ext r; simp [mul_right_inj' hpos.ne']
        have hm : Measurable fun r : ℝ ↦ rayL1Norm (b k) C * r := measurable_const.mul measurable_id
        have himg_m : MeasurableSet ((fun r ↦ rayL1Norm (b k) C * r) '' (rayM k ⁻¹' R)) := by
          have heq : (fun r ↦ rayL1Norm (b k) C * r) '' (rayM k ⁻¹' R) =
              (fun t ↦ (rayL1Norm (b k) C)⁻¹ * t) ⁻¹' (rayM k ⁻¹' R) := by
            ext t; constructor
            · rintro ⟨r, hr, rfl⟩; simpa [inv_mul_cancel_left₀ hpos.ne'] using hr
            · intro ht; exact ⟨(rayL1Norm (b k) C)⁻¹ * t, ht, mul_inv_cancel_left₀ hpos.ne' t⟩
          rw [heq]; exact (measurable_const.mul measurable_id) ((hrayM k) hRm)
        have hmap : ENNReal.ofReal (rayL1Norm (b k) C) *
            (radialMeasure 1) ((fun r ↦ rayL1Norm (b k) C * r) '' (rayM k ⁻¹' R)) =
            (μk k) R := by
          have h1 := congrArg (fun ν : Measure ℝ ↦ ν ((fun r ↦ rayL1Norm (b k) C * r) '' (rayM k ⁻¹' R)))
            (radialMeasure_one_map_mul hpos)
          simp only [Measure.map_apply hm himg_m, himg, Measure.smul_apply, smul_eq_mul] at h1
          rw [← h1, Measure.map_apply (hrayM k) hRm]
        calc (radialMeasure 1) {t : ℝ | _}
            ≤ (radialMeasure 1) ((fun r ↦ rayL1Norm (b k) C * r) '' (rayM k ⁻¹' R)) := measure_mono hsub
          _ = ENNReal.ofReal (rayL1Norm (b k) C)⁻¹ * (μk k) R := by
              rw [← hmap, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hpos).le,
                inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hμk_fin k)) hle
    have hfL_int (k : κ) (hk : k ∈ Kp) : Integrable (fL k) (radialMeasure 1) := by
      let S_t : Set ℝ := {t : ℝ | 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
        t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB}
      have hS_t_m : MeasurableSet S_t :=
        (measurableSet_lt measurable_const measurable_id).inter
          (((measurable_id.smul_const _) (hEC.inter hRC_m)).inter
            (((measurable_id.smul_const _) hRA).inter ((measurable_id.smul_const _) hRB)))
      have hle : ∀ t, ‖fL k t‖ ≤ S_t.indicator (fun _ ↦ rayL1Norm (b k) C) t := by
        intro t
        by_cases ht : t ∈ S_t
        · have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
          rw [indicator_of_mem ht]
          have hcond : 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
              t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB := ht
          have hfL_val : fL k t = rayL1Norm (b k) C * rayCondProb b A B C RA RB E c₀ (t • rayDir (b k) C) := by
            dsimp only [fL]; exact ite_eq_left_of_eq_true _ _ (eq_true hcond)
          rw [hfL_val, Real.norm_eq_abs, abs_mul, abs_of_pos hpos,
            abs_of_nonneg (rayCondProb_nonneg _ _ _ _ _ _ _ hc₀_nonneg _)]
          exact mul_le_of_le_one_right hpos.le (rayCondProb_le_one _ _ _ _ _ _ _ hc₀_le_one _)
        · have hfL_val : fL k t = 0 := by
            dsimp only [fL]; exact ite_eq_right_of_eq_false _ _ (eq_false ht)
          rw [hfL_val, norm_zero, indicator_of_notMem ht]
      exact ((integrableOn_const (hset_t_fin k hk)).integrable_indicator hS_t_m).mono'
        (hfL_meas k).aestronglyMeasurable (Eventually.of_forall hle)
    have hfR_int (k : κ) (hk : k ∈ Kp) : Integrable (fR k) (radialMeasure 1) := by
      let S_t : Set ℝ := {t : ℝ | 0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
        t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB}
      have hS_t_m : MeasurableSet S_t :=
        (measurableSet_lt measurable_const measurable_id).inter
          (((measurable_id.smul_const _) (hEC.inter hRC_m)).inter
            (((measurable_id.smul_const _) hRA).inter ((measurable_id.smul_const _) hRB)))
      have hle : ∀ t, ‖fR k t‖ ≤ S_t.indicator (fun _ ↦ rayL1Norm (b k) C) t := by
        intro t
        by_cases ht : t ∈ S_t
        · have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
          rw [indicator_of_mem ht]
          simp only [fR]; split_ifs
          · rw [Real.norm_eq_abs, abs_of_pos hpos]
          · simp [hpos.le]
        · have hnot : ¬ (0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
              t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB ∧
              (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ E) :=
            fun h ↦ ht ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
          have hfR_val : fR k t = 0 := by
            dsimp only [fR]; exact ite_eq_right_of_eq_false _ _ (eq_false hnot)
          rw [hfR_val, norm_zero, indicator_of_notMem ht]
      exact ((integrableOn_const (hset_t_fin k hk)).integrable_indicator hS_t_m).mono'
        (hfR_meas k).aestronglyMeasurable (Eventually.of_forall hle)
    have hLHS_k (k : κ) (hk : k ∈ Kp) :
        ∫ y in subProj hC ⁻¹' EC ∩ R, rayCondProb b A B C RA RB E c₀ (subProj hC y) ∂(μk k) =
        ∫ t, fL k t ∂(radialMeasure 1) := by
      have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
      rw [← integral_indicator (hs_m.inter hRm)]
      change ∫ y, (subProj hC ⁻¹' EC ∩ R).indicator (rayCondProb b A B C RA RB E c₀ ∘ subProj hC) y ∂
        ((radialMeasure 1).map (rayM k)) = _
      rw [integral_map (hrayM k).aemeasurable
        ((hp_meas.comp (measurable_subProj hC)).indicator (hs_m.inter hRm)).aestronglyMeasurable]
      have hcomp : (fun r ↦ (subProj hC ⁻¹' EC ∩ R).indicator
          (rayCondProb b A B C RA RB E c₀ ∘ subProj hC) (rayM k r)) =ᵐ[radialMeasure 1]
          (fun r ↦ (rayL1Norm (b k) C)⁻¹ * fL k (rayL1Norm (b k) C * r)) := by
        filter_upwards [ae_pos_radialMeasure_one] with r hr
        have ht : 0 < rayL1Norm (b k) C * r := mul_pos hpos hr
        have hmem : rayM k r ∈ subProj hC ⁻¹' EC ∩ R ↔
            (rayL1Norm (b k) C * r) • rayDir (b k) C ∈ EC ∩ RC ∧
            (rayL1Norm (b k) C * r) • rayScaled (b k) C A ∈ RA ∧
            (rayL1Norm (b k) C * r) • rayScaled (b k) C B ∈ RB := by
          change (subProj hC (rayM k r) ∈ EC ∧ rayM k r ∈ Set.univ.pi Rc) ↔ _
          rw [mem_pi_iff_subProj]
          change (subProj hC (rayM k r) ∈ EC ∧
            subProj hA (rayM k r) ∈ RA ∧ subProj hB (rayM k r) ∈ RB ∧ subProj hC (rayM k r) ∈ RC) ↔ _
          rw [hray_subA k hk, hray_subB k hk, hray_subC k hk]
          simp only [mem_inter_iff]; tauto
        by_cases h : rayM k r ∈ subProj hC ⁻¹' EC ∩ R
        · have h' := hmem.1 h
          rw [indicator_of_mem h, Function.comp_apply, hray_subC k hk]
          have hcond : 0 < rayL1Norm (b k) C * r ∧
              (rayL1Norm (b k) C * r) • rayDir (b k) C ∈ EC ∩ RC ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C A ∈ RA ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C B ∈ RB := ⟨ht, h'⟩
          dsimp only [fL]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), inv_mul_cancel_left₀ hpos.ne']
        · have h' : ¬ (0 < rayL1Norm (b k) C * r ∧
              (rayL1Norm (b k) C * r) • rayDir (b k) C ∈ EC ∩ RC ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C A ∈ RA ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C B ∈ RB) :=
            fun hx ↦ h (hmem.2 ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩)
          rw [indicator_of_notMem h]
          dsimp only [fL]
          rw [ite_eq_right_of_eq_false _ _ (eq_false h'), mul_zero]
      rw [integral_congr_ae hcomp, integral_const_mul,
        integral_radialMeasure_one_comp_mul hpos (hfL_meas k), inv_mul_cancel_left₀ hpos.ne']
    have hRHS_k (k : κ) (hk : k ∈ Kp) :
        ((μk k) ((S_E ∩ subProj hC ⁻¹' EC) ∩ R)).toReal =
        ∫ t, fR k t ∂(radialMeasure 1) := by
      have hpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 hk).2
      have hmeas_set : MeasurableSet ((S_E ∩ subProj hC ⁻¹' EC) ∩ R) :=
        (hS_E_m.inter hs_m).inter hRm
      have h1 : ((μk k) ((S_E ∩ subProj hC ⁻¹' EC) ∩ R)).toReal =
          ∫ y, ((S_E ∩ subProj hC ⁻¹' EC) ∩ R).indicator (fun _ ↦ (1 : ℝ)) y ∂(μk k) := by
        rw [show (fun y ↦ ((S_E ∩ subProj hC ⁻¹' EC) ∩ R).indicator (fun _ ↦ (1 : ℝ)) y) =
          ((S_E ∩ subProj hC ⁻¹' EC) ∩ R).indicator 1 from rfl,
          integral_indicator_one hmeas_set, measureReal_def]
      rw [h1, integral_map (hrayM k).aemeasurable
        (measurable_const.indicator hmeas_set).aestronglyMeasurable]
      have hcomp : (fun r ↦ ((S_E ∩ subProj hC ⁻¹' EC) ∩ R).indicator (fun _ ↦ (1 : ℝ)) (rayM k r)) =ᵐ[radialMeasure 1]
          (fun r ↦ (rayL1Norm (b k) C)⁻¹ * fR k (rayL1Norm (b k) C * r)) := by
        filter_upwards [ae_pos_radialMeasure_one] with r hr
        have ht : 0 < rayL1Norm (b k) C * r := mul_pos hpos hr
        have hmem : rayM k r ∈ (S_E ∩ subProj hC ⁻¹' EC) ∩ R ↔
            (rayL1Norm (b k) C * r) • rayDir (b k) C ∈ EC ∩ RC ∧
            (rayL1Norm (b k) C * r) • rayScaled (b k) C A ∈ RA ∧
            (rayL1Norm (b k) C * r) • rayScaled (b k) C B ∈ RB ∧
            ((rayL1Norm (b k) C * r) • rayScaled (b k) C A,
             (rayL1Norm (b k) C * r) • rayScaled (b k) C B) ∈ E := by
          change (((subProj hA (rayM k r), subProj hB (rayM k r)) ∈ E ∧ subProj hC (rayM k r) ∈ EC) ∧
            rayM k r ∈ Set.univ.pi Rc) ↔ _
          rw [mem_pi_iff_subProj]
          change (((subProj hA (rayM k r), subProj hB (rayM k r)) ∈ E ∧ subProj hC (rayM k r) ∈ EC) ∧
            subProj hA (rayM k r) ∈ RA ∧ subProj hB (rayM k r) ∈ RB ∧ subProj hC (rayM k r) ∈ RC) ↔ _
          rw [hray_subA k hk, hray_subB k hk, hray_subC k hk]
          simp only [mem_inter_iff]; tauto
        by_cases h : rayM k r ∈ (S_E ∩ subProj hC ⁻¹' EC) ∩ R
        · have h' := hmem.1 h
          rw [indicator_of_mem h]
          have hcond : 0 < rayL1Norm (b k) C * r ∧
              (rayL1Norm (b k) C * r) • rayDir (b k) C ∈ EC ∩ RC ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C A ∈ RA ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C B ∈ RB ∧
              ((rayL1Norm (b k) C * r) • rayScaled (b k) C A,
               (rayL1Norm (b k) C * r) • rayScaled (b k) C B) ∈ E := ⟨ht, h'⟩
          dsimp only [fR]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), inv_mul_cancel₀ hpos.ne']
        · have h' : ¬ (0 < rayL1Norm (b k) C * r ∧
              (rayL1Norm (b k) C * r) • rayDir (b k) C ∈ EC ∩ RC ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C A ∈ RA ∧
              (rayL1Norm (b k) C * r) • rayScaled (b k) C B ∈ RB ∧
              ((rayL1Norm (b k) C * r) • rayScaled (b k) C A,
               (rayL1Norm (b k) C * r) • rayScaled (b k) C B) ∈ E) :=
            fun hx ↦ h (hmem.2 ⟨hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩)
          rw [indicator_of_notMem h]
          dsimp only [fR]
          rw [ite_eq_right_of_eq_false _ _ (eq_false h'), mul_zero]
      rw [integral_congr_ae hcomp, integral_const_mul,
        integral_radialMeasure_one_comp_mul hpos (hfR_meas k), inv_mul_cancel_left₀ hpos.ne']
    -- Now sum `fL k` and `fR k` inside the integral and check pointwise equality for every `t`!
    rw [Finset.sum_congr rfl hLHS_k, Finset.sum_congr rfl hRHS_k,
      ← integral_finsetSum Kp hfL_int, ← integral_finsetSum Kp hfR_int]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    -- Group `Kp` by direction `v = rayDir (b k) C`!
    let dirs : Finset (C → ℝ) := Kp.image fun k ↦ rayDir (b k) C
    rw [← Finset.sum_fiberwise_of_maps_to (s := Kp) (t := dirs) (g := fun k ↦ rayDir (b k) C)
      (f := fun k ↦ fL k t) (fun k hk ↦ Finset.mem_image_of_mem _ hk),
      ← Finset.sum_fiberwise_of_maps_to (s := Kp) (t := dirs) (g := fun k ↦ rayDir (b k) C)
      (f := fun k ↦ fR k t) (fun k hk ↦ Finset.mem_image_of_mem _ hk)]
    refine Finset.sum_congr rfl fun v hv ↦ ?_
    -- Fix a direction `v ∈ dirs`: all `k` in the fiber have `rayDir (b k) C = v` and `0 < rayL1Norm (b k) C`.
    rcases Finset.mem_image.1 hv with ⟨k₀, hk₀, hvk₀⟩
    have hv_sum : ∑ c : C, v c = 1 := hvk₀ ▸ sum_rayDir (Finset.mem_filter.1 hk₀).2
    by_cases ht_ok : 0 < t ∧ t • v ∈ EC ∩ RC
    · -- Since `0 < t` and `∑ c, v c = 1`, we have `t • v ≠ 0` and `∑ c, (t • v) c = t`!
      have htv_sum : ∑ c : C, (t • v) c = t := by
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv_sum, mul_one]
      have htv_ne : t • v ≠ 0 := by
        intro h0; rw [h0] at htv_sum; simp at htv_sum; linarith [ht_ok.1]
      -- On the fiber `k ∈ Kp` with `rayDir (b k) C = v`, `rayCondProb` is CONSTANT (`= num / den`)!
      have hp_eq : rayCondProb b A B C RA RB E c₀ (t • v) =
          (∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v), fR k t) /
          (∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v),
            if t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB
            then rayL1Norm (b k) C else 0) := by
        simp only [rayCondProb, htv_ne, ↓reduceIte, htv_sum]
        congr 1
        · rw [Finset.sum_filter, show Kp = Finset.univ.filter (fun k ↦ 0 < rayL1Norm (b k) C) from rfl,
            Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
          · simp only [fR, hk.1, hk.2, ↓reduceIte, ht_ok.1, ht_ok.2, true_and]
          · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB ∧
                (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ E) := by
              rintro ⟨h1, _, h3, _⟩
              exact hk ⟨h1, (smul_right_injective _ ht_ok.1.ne' h3).symm⟩
            simp only [h1, ↓reduceIte]
            by_cases hkp : 0 < rayL1Norm (b k) C
            · have hne : rayDir (b k) C ≠ v := fun h ↦ hk ⟨hkp, h⟩
              simp [hkp, hne]
            · simp [hkp]
        · rw [Finset.sum_filter, show Kp = Finset.univ.filter (fun k ↦ 0 < rayL1Norm (b k) C) from rfl,
            Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
          · have heq : t • v = t • rayDir (b k) C := by rw [hk.2]
            simp only [hk.1, hk.2, ↓reduceIte, ht_ok.1, heq, true_and]
          · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB) := by
              rintro ⟨h1, _, h3, _⟩
              exact hk ⟨h1, (smul_right_injective _ ht_ok.1.ne' h3).symm⟩
            simp only [h1, ↓reduceIte]
            by_cases hkp : 0 < rayL1Norm (b k) C
            · have hne : rayDir (b k) C ≠ v := fun h ↦ hk ⟨hkp, h⟩
              simp [hkp, hne]
            · simp [hkp]
      have hLHS_fib : ∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v), fL k t =
          (∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v),
            if t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB
            then rayL1Norm (b k) C else 0) *
          rayCondProb b A B C RA RB E c₀ (t • v) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hvk : rayDir (b k) C = v := (Finset.mem_filter.1 hk).2
        simp only [fL, hvk, ht_ok.1, ht_ok.2, true_and]
        split_ifs <;> ring
      rw [hLHS_fib, hp_eq]
      set den := ∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v),
        if t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB
        then rayL1Norm (b k) C else 0
      set num := ∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v), fR k t
      have hden_nonneg : 0 ≤ den := Finset.sum_nonneg fun k hk ↦ by
        split_ifs
        · exact (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2.le
        · exact le_rfl
      rcases hden_nonneg.eq_or_lt with hden0 | hden_pos
      · have hnum0 : num = 0 := by
          have hle : num ≤ den := Finset.sum_le_sum fun k hk ↦ by
            have hvk : rayDir (b k) C = v := (Finset.mem_filter.1 hk).2
            have hkpos : 0 < rayL1Norm (b k) C := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2
            simp only [fR, hvk, ht_ok.1, ht_ok.2, true_and]
            split_ifs with h1 h2
            · exact le_rfl
            · exfalso; exact h2 ⟨h1.1, h1.2.1⟩
            · exact hkpos.le
            · exact le_rfl
          have hnn : 0 ≤ num := Finset.sum_nonneg fun k hk ↦ by
            simp only [fR]; split_ifs
            · exact (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2.le
            · exact le_rfl
          linarith
        rw [← hden0, zero_mul, hnum0]
      · exact mul_div_cancel₀ num hden_pos.ne'
    · -- `¬ (0 < t ∧ t • v ∈ EC ∩ RC)`: every term in both fiber sums is `0`!
      have hL0 : ∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v), fL k t = 0 :=
        Finset.sum_eq_zero fun k hk ↦ by
          have hvk : rayDir (b k) C = v := (Finset.mem_filter.1 hk).2
          have hnot : ¬ (0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
              t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB) :=
            fun h ↦ ht_ok ⟨h.1, hvk ▸ h.2.1⟩
          simp only [fL, hnot, ↓reduceIte]
      have hR0 : ∑ k ∈ Kp.filter (fun k ↦ rayDir (b k) C = v), fR k t = 0 :=
        Finset.sum_eq_zero fun k hk ↦ by
          have hvk : rayDir (b k) C = v := (Finset.mem_filter.1 hk).2
          have hnot : ¬ (0 < t ∧ t • rayDir (b k) C ∈ EC ∩ RC ∧
              t • rayScaled (b k) C A ∈ RA ∧ t • rayScaled (b k) C B ∈ RB ∧
              (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ E) :=
            fun h ↦ ht_ok ⟨h.1, hvk ▸ h.2.1⟩
          simp only [fR, hnot, ↓reduceIte]
      rw [hL0, hR0]

end RayCondExp

/-! ### Theorem 1: Exact Ray Characterization of Extremal Conditional Independence -/

/-- Helper: Condition (II) of `RayCICondition` implies factorization for arbitrary indicator
sets `E_A ⊆ (A → ℝ)` and `E_B ⊆ (B → ℝ)`. -/
lemma rayDirMass_prod_of_rayCICondition {V κ : Type*} [Fintype κ]
    {b : κ → V → ℝ} {A B C : Finset V}
    (hII : ∀ v : C → ℝ, ∀ x : A → ℝ, ∀ y : B → ℝ,
      rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y) *
        rayDirMass b C v (fun _ ↦ True) =
      rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x) *
        rayDirMass b C v (fun k ↦ rayScaled (b k) C B = y))
    (v : C → ℝ) (SA : Set (A → ℝ)) (SB : Set (B → ℝ)) :
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA ∧ rayScaled (b k) C B ∈ SB) *
      rayDirMass b C v (fun _ ↦ True) =
    rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA) *
      rayDirMass b C v (fun k ↦ rayScaled (b k) C B ∈ SB) := by
  classical
  let xs : Finset (A → ℝ) := (Finset.univ.image fun k : κ ↦ rayScaled (b k) C A).filter (· ∈ SA)
  let ys : Finset (B → ℝ) := (Finset.univ.image fun k : κ ↦ rayScaled (b k) C B).filter (· ∈ SB)
  have hAB : rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA ∧ rayScaled (b k) C B ∈ SB) =
      ∑ x ∈ xs, ∑ y ∈ ys,
        rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y) := by
    unfold rayDirMass
    have h1 : ∀ k : κ,
        (if 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
            rayScaled (b k) C A ∈ SA ∧ rayScaled (b k) C B ∈ SB
         then rayL1Norm (b k) C else 0) =
        ∑ x ∈ xs, ∑ y ∈ ys,
          (if 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
              rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y
           then rayL1Norm (b k) C else 0) := by
      intro k
      by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
      · by_cases hA : rayScaled (b k) C A ∈ SA
        · have hxmem : rayScaled (b k) C A ∈ xs :=
            Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ k), hA⟩
          by_cases hB : rayScaled (b k) C B ∈ SB
          · have hymem : rayScaled (b k) C B ∈ ys :=
              Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ k), hB⟩
            rw [Finset.sum_eq_single (rayScaled (b k) C A)
              (fun x _ hx ↦ Finset.sum_eq_zero fun y _ ↦ by simp [Ne.symm hx])
              (fun h ↦ (h hxmem).elim)]
            rw [Finset.sum_eq_single (rayScaled (b k) C B)
              (fun y _ hy ↦ by simp [Ne.symm hy])
              (fun h ↦ (h hymem).elim)]
            simp [hk.1, hk.2, hA, hB]
          · simp only [hk.1, hk.2, hA, hB, and_false, ↓reduceIte]
            exact (Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y hy ↦ by
              have hne : rayScaled (b k) C B ≠ y := fun h ↦ hB (h ▸ (Finset.mem_filter.1 hy).2)
              simp [hne]).symm
        · simp only [hk.1, hk.2, hA, false_and, and_false, ↓reduceIte]
          exact (Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y _ ↦ by
            have hne : rayScaled (b k) C A ≠ x := fun h ↦ hA (h ▸ (Finset.mem_filter.1 hx).2)
            simp [hne]).symm
      · simp only [show ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
            rayScaled (b k) C A ∈ SA ∧ rayScaled (b k) C B ∈ SB) from fun ⟨a, b', _⟩ ↦ hk ⟨a, b'⟩,
          ↓reduceIte]
        exact (Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y _ ↦ by
          simp [show ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
            rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y) from fun ⟨a, b', _⟩ ↦ hk ⟨a, b'⟩]).symm
    trans (∑ k : κ, ∑ x ∈ xs, ∑ y ∈ ys,
        if 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
            rayScaled (b k) C A = x ∧ rayScaled (b k) C B = y
        then rayL1Norm (b k) C else 0)
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      convert h1 k
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun k _ ↦ by congr 1
  have hA_eq : rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA) =
      ∑ x ∈ xs, rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x) := by
    unfold rayDirMass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
    · by_cases hA : rayScaled (b k) C A ∈ SA
      · have hxmem : rayScaled (b k) C A ∈ xs :=
          Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ k), hA⟩
        rw [Finset.sum_eq_single (rayScaled (b k) C A)
          (fun x _ hx ↦ by simp [Ne.symm hx]) (fun h ↦ (h hxmem).elim)]
        simp [hk.1, hk.2, hA]
      · simp only [hk.1, hk.2, hA, and_false, ↓reduceIte]
        exact (Finset.sum_eq_zero fun x hx ↦ by
          have hne : rayScaled (b k) C A ≠ x := fun h ↦ hA (h ▸ (Finset.mem_filter.1 hx).2)
          simp [hne]).symm
    · simp only [show ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C A ∈ SA)
        from fun ⟨a, b', _⟩ ↦ hk ⟨a, b'⟩, ↓reduceIte]
      exact (Finset.sum_eq_zero fun x _ ↦ by
        simp [show ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C A = x)
          from fun ⟨a, b', _⟩ ↦ hk ⟨a, b'⟩]).symm
  have hB_eq : rayDirMass b C v (fun k ↦ rayScaled (b k) C B ∈ SB) =
      ∑ y ∈ ys, rayDirMass b C v (fun k ↦ rayScaled (b k) C B = y) := by
    unfold rayDirMass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
    · by_cases hB : rayScaled (b k) C B ∈ SB
      · have hymem : rayScaled (b k) C B ∈ ys :=
          Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ k), hB⟩
        rw [Finset.sum_eq_single (rayScaled (b k) C B)
          (fun y _ hy ↦ by simp [Ne.symm hy]) (fun h ↦ (h hymem).elim)]
        simp [hk.1, hk.2, hB]
      · simp only [hk.1, hk.2, hB, and_false, ↓reduceIte]
        exact (Finset.sum_eq_zero fun y hy ↦ by
          have hne : rayScaled (b k) C B ≠ y := fun h ↦ hB (h ▸ (Finset.mem_filter.1 hy).2)
          simp [hne]).symm
    · simp only [show ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C B ∈ SB)
        from fun ⟨a, b', _⟩ ↦ hk ⟨a, b'⟩, ↓reduceIte]
      exact (Finset.sum_eq_zero fun y _ ↦ by
        simp [show ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C B = y)
          from fun ⟨a, b', _⟩ ↦ hk ⟨a, b'⟩]).symm
  rw [hAB, hA_eq, hB_eq, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ ↦ hII v x y

/-- **Theorem 1 (Exact Ray Characterization of Extremal Conditional Independence):**
For any finite family of nonnegative ray vectors `b : κ → V → ℝ` and pairwise disjoint
`A, B, C : Finset V`, extremal conditional independence `A ⊥ B | C [rayExponentMeasure b]`
(Engelke–Ivanovs–Strokorb Definition 3.1) holds if and only if `RayCICondition b A B C` holds. -/
theorem extremalCondIndep_rayExponentMeasure_iff {V κ : Type*} [Fintype κ] [DecidableEq V]
    (b : κ → V → ℝ) (hb : ∀ k i, 0 ≤ b k i)
    {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    ExtremalCondIndep (rayExponentMeasure b) A B C ↔ RayCICondition b A B C := by
  classical
  let M : Finset V := A ∪ B ∪ C
  have hA : A ⊆ M := Finset.subset_union_left.trans Finset.subset_union_left
  have hB : B ⊆ M := Finset.subset_union_right.trans Finset.subset_union_left
  have hC : C ⊆ M := Finset.subset_union_right
  constructor
  · -- Necessity (`→`)
    intro hECI
    constructor
    · -- Necessity of Condition (I)
      intro k₀ hk₀C
      by_contra h
      push Not at h
      rcases h with ⟨⟨a₀, ha₀A, ha₀_ne⟩, ⟨b₀, hb₀B, hb₀_ne⟩⟩
      have ha₀_pos : 0 < b k₀ a₀ := lt_of_le_of_ne (hb k₀ a₀) (Ne.symm ha₀_ne)
      have hb₀_pos : 0 < b k₀ b₀ := lt_of_le_of_ne (hb k₀ b₀) (Ne.symm hb₀_ne)
      -- Choose the product test set `R`: `R_{a₀} = [1, 2]`, `R_c = {0}` for `c ∈ C`, `R_i = [0, ∞)` elsewhere.
      let Rc : M → Set ℝ := fun i ↦
        if i.1 = a₀ then Icc 1 2
        else if i.1 ∈ C then {0}
        else Ici 0
      have hRc_m : ∀ i, MeasurableSet (Rc i) := fun i ↦ by
        simp only [Rc]; split_ifs
        · exact measurableSet_Icc
        · exact measurableSet_singleton 0
        · exact measurableSet_Ici
      let R : Set (M → ℝ) := Set.univ.pi Rc
      have ha₀_not_C : a₀ ∉ C := Finset.disjoint_left.1 hAC ha₀A
      have hb₀_not_C : b₀ ∉ C := Finset.disjoint_left.1 hBC hb₀B
      have hb₀_ne_a₀ : b₀ ≠ a₀ := fun h ↦ Finset.disjoint_left.1 hAB ha₀A (h ▸ hb₀B)
      have h0_not_cl : (0 : M → ℝ) ∉ closure R := by
        intro h0
        have hcl : closure R = Set.univ.pi (fun i ↦ closure (Rc i)) := closure_pi_set Set.univ Rc
        rw [hcl, mem_univ_pi] at h0
        have h0a := h0 ⟨a₀, hA ha₀A⟩
        simp only [Rc, ↓reduceIte, closure_Icc, Pi.zero_apply, mem_Icc] at h0a
        linarith
      -- Show `(rayExponentMeasure b).map (coordProj M) R > 0` using ray `k₀`:
      have hray_k₀_pos : 0 < ((radialMeasure 1).map (fun r : ℝ ↦ fun i : M ↦ r * b k₀ i.1)) R := by
        have hray : Measurable (fun r : ℝ ↦ fun i : M ↦ r * b k₀ i.1) :=
          Measurable.of_eval fun i ↦ measurable_id.mul_const (b k₀ i.1)
        rw [Measure.map_apply hray (MeasurableSet.univ_pi hRc_m)]
        have hsub : Ioc (1 / b k₀ a₀) (2 / b k₀ a₀) ⊆ (fun r : ℝ ↦ fun i : M ↦ r * b k₀ i.1) ⁻¹' R := by
          intro r ⟨hr1, hr2⟩
          rw [mem_preimage, mem_univ_pi]
          intro i
          simp only [Rc]
          split_ifs with h1 h2
          · rw [h1]; exact ⟨(div_le_iff₀ ha₀_pos).1 hr1.le, (le_div_iff₀ ha₀_pos).1 hr2⟩
          · simp [hk₀C i.1 h2]
          · exact mul_nonneg (le_trans (div_nonneg zero_le_one ha₀_pos.le) hr1.le) (hb k₀ i.1)
        have hIoc_pos : 0 < radialMeasure 1 (Ioc (1 / b k₀ a₀) (2 / b k₀ a₀)) := by
          have h1 : 0 < 1 / b k₀ a₀ := div_pos one_pos ha₀_pos
          have h2 : 0 < 2 / b k₀ a₀ := div_pos (by norm_num) ha₀_pos
          have hle : 1 / b k₀ a₀ < 2 / b k₀ a₀ := by
            rw [div_lt_div_iff₀ ha₀_pos ha₀_pos]; linarith
          have hdiff : Ioi (1 / b k₀ a₀) = Ioc (1 / b k₀ a₀) (2 / b k₀ a₀) ∪ Ioi (2 / b k₀ a₀) :=
            (Ioc_union_Ioi_eq_Ioi hle.le).symm
          have hdisj : Disjoint (Ioc (1 / b k₀ a₀) (2 / b k₀ a₀)) (Ioi (2 / b k₀ a₀)) :=
            Ioc_disjoint_Ioi_same
          have hm1 := radialMeasure_Ioi one_pos h1
          have hm2 := radialMeasure_Ioi one_pos h2
          have hadd : radialMeasure 1 (Ioi (1 / b k₀ a₀)) =
              radialMeasure 1 (Ioc (1 / b k₀ a₀) (2 / b k₀ a₀)) + radialMeasure 1 (Ioi (2 / b k₀ a₀)) := by
            rw [hdiff, measure_union hdisj measurableSet_Ioi]
          by_contra h0
          have heq0 : radialMeasure 1 (Ioc (1 / b k₀ a₀) (2 / b k₀ a₀)) = 0 :=
            le_antisymm (not_lt.1 h0) bot_le
          rw [heq0, zero_add, hm1, hm2, Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div,
            div_one] at hadd
          have hgt : b k₀ a₀ / 2 < b k₀ a₀ := by linarith
          have hne : ENNReal.ofReal (b k₀ a₀) ≠ ENNReal.ofReal (b k₀ a₀ / 2) :=
            (ENNReal.ofReal_lt_ofReal_iff ha₀_pos).2 hgt |>.ne'
          exact hne hadd
        exact lt_of_lt_of_le hIoc_pos (measure_mono hsub)
      have hΛ_pos : 0 < (rayExponentMeasure b).map (coordProj M) R := by
        rw [rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
          Measure.finsetSum_apply]
        have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k₀ i) :=
          Measurable.of_eval fun i ↦ measurable_id.mul_const (b k₀ i)
        calc 0 < ((radialMeasure 1).map (fun r : ℝ ↦ fun i : M ↦ r * b k₀ i.1)) R := hray_k₀_pos
          _ = (((radialMeasure 1).map (fun r : ℝ ↦ fun i : V ↦ r * b k₀ i)).map (coordProj M)) R := by
              rw [Measure.map_map (measurable_coordProj M) hray]; rfl
          _ ≤ _ := Finset.single_le_sum
              (f := fun k ↦ (((radialMeasure 1).map (fun r : ℝ ↦ fun i : V ↦ r * b k i)).map (coordProj M)) R)
              (fun _ _ ↦ zero_le) (Finset.mem_univ k₀)
      have hΛ_top : (rayExponentMeasure b).map (coordProj M) R ≠ ∞ :=
        (rayExponentMeasure_map_lt_top_of_zero_notMem_closure b hb h0_not_cl).ne
      have hR_test : IsProductTestSet (rayExponentMeasure b) M R :=
        ⟨⟨Rc, hRc_m, rfl⟩, h0_not_cl, hΛ_pos, hΛ_top⟩
      -- Under `μR = condProbMeasure ...`, `Y_C = 0` everywhere on `R`, so `Y_A` and `Y_B` are
      -- unconditionally independent!
      let μR := condProbMeasure (rayExponentMeasure b) M R
      have : IsProbabilityMeasure μR := isProbabilityMeasure_condProbMeasure hΛ_pos hΛ_top
      have hCI := hECI R hR_test
      rw [condIndepFun_iff _ _ (subProj hA) (subProj hB) (measurable_subProj hA)
        (measurable_subProj hB) μR] at hCI
      -- Choose max slope `αmax = max {b k b₀ / b k a₀ | k ∈ K_active}` (at least `b k₀ b₀ / b k₀ a₀ > 0`).
      let Kact : Finset κ := Finset.univ.filter fun k ↦ (∀ c ∈ C, b k c = 0) ∧ 0 < b k a₀
      have hk₀_act : k₀ ∈ Kact := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk₀C, ha₀_pos⟩
      let α : κ → ℝ := fun k ↦ b k b₀ / b k a₀
      obtain ⟨kstar, hkstar, hkstar_max⟩ := Kact.exists_max_image α ⟨k₀, hk₀_act⟩
      have hα_pos : 0 < α kstar := lt_of_lt_of_le (div_pos hb₀_pos ha₀_pos) (hkstar_max k₀ hk₀_act)
      have hks_C : ∀ c ∈ C, b kstar c = 0 := (Finset.mem_filter.1 hkstar).2.1
      have hks_a : 0 < b kstar a₀ := (Finset.mem_filter.1 hkstar).2.2
      -- Test events: `t1 = {y | y a₀ ∈ [1, 4/3]}` and `t2 = {y | y b₀ ∈ (4/3 * αmax, 2 * αmax]}`!
      let s1 : Set (A → ℝ) := {yA | yA ⟨a₀, ha₀A⟩ ∈ Icc (1 : ℝ) (4 / 3)}
      let s2 : Set (B → ℝ) := {yB | yB ⟨b₀, hb₀B⟩ ∈ Ioc (4 / 3 * α kstar) (2 * α kstar)}
      have hs1_m : MeasurableSet s1 := (measurable_pi_apply (⟨a₀, ha₀A⟩ : A)) measurableSet_Icc
      have hs2_m : MeasurableSet s2 := (measurable_pi_apply (⟨b₀, hb₀B⟩ : B)) measurableSet_Ioc
      have ht1_m : MeasurableSet[MeasurableSpace.comap (subProj hA) inferInstance] (subProj hA ⁻¹' s1) :=
        ⟨s1, hs1_m, rfl⟩
      have ht2_m : MeasurableSet[MeasurableSpace.comap (subProj hB) inferInstance] (subProj hB ⁻¹' s2) :=
        ⟨s2, hs2_m, rfl⟩
      have hfac := hCI (subProj hA ⁻¹' s1) (subProj hB ⁻¹' s2) ht1_m ht2_m
      -- Since `subProj hC y = 0` for all `y ∈ R`, `μR⟦t | comap (subProj hC)⟧ =ᵐ const (μR t).toReal`!
      have hYC0 : ∀ᵐ y ∂μR, subProj hC y = 0 := by
        rw [show μR = (rayExponentMeasure b |>.map (coordProj M) R)⁻¹ •
            ((rayExponentMeasure b |>.map (coordProj M)).restrict R) from rfl]
        refine Measure.ae_smul_measure ?_ _
        refine ae_restrict_of_forall_mem (MeasurableSet.univ_pi hRc_m) fun y hy ↦ ?_
        funext c
        have hmem' := hy ⟨c.1, hC c.2⟩ (mem_univ _)
        have hc_ne_a₀ : c.1 ≠ a₀ := fun h ↦ ha₀_not_C (h ▸ c.2)
        simp only [Rc, hc_ne_a₀, c.2, ↓reduceIte, mem_singleton_iff] at hmem'
        exact hmem'
      have hconst_ce : ∀ {t : Set (M → ℝ)}, MeasurableSet t →
          μR⟦t | MeasurableSpace.comap (subProj hC) inferInstance⟧ =ᵐ[μR]
            fun _ ↦ (μR t).toReal := by
        intro t ht
        refine (ae_eq_condExp_of_forall_setIntegral_eq (measurable_subProj hC).comap_le
          ((integrable_const (1 : ℝ)).indicator ht)
          (fun _ _ _ ↦ (integrable_const _).integrableOn)
          (fun s hs _ ↦ ?_)
          stronglyMeasurable_const.aestronglyMeasurable).symm
        rcases hs with ⟨EC, hEC, rfl⟩
        rw [show (fun x ↦ t.indicator (fun _ ↦ (1 : ℝ)) x) = t.indicator 1 from rfl,
          integral_indicator_one ht, integral_const, smul_eq_mul]
        by_cases h0 : (0 : C → ℝ) ∈ EC
        · have hfull : subProj hC ⁻¹' EC =ᵐ[μR] (univ : Set (M → ℝ)) := by
            refine Filter.eventuallyEqSet_iff.2 ?_
            filter_upwards [hYC0] with y hy
            simp [hy, h0]
          have h1 : (μR.restrict (subProj hC ⁻¹' EC)).real univ = 1 := by
            rw [measureReal_def, Measure.restrict_apply_univ, measure_congr hfull, measure_univ,
              ENNReal.toReal_one]
          have h2 : μR.restrict (subProj hC ⁻¹' EC) t = μR t := by
            rw [Measure.restrict_apply ht]
            refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
            filter_upwards [hYC0] with y hy
            simp [hy, h0]
          rw [h1, one_mul, measureReal_def, h2]
        · have hnull : μR (subProj hC ⁻¹' EC) = 0 := by
            refine measure_mono_null (fun y hy ↦ ?_) (ae_iff.1 hYC0)
            intro hy0; exact h0 (hy0 ▸ hy)
          rw [Measure.restrict_eq_zero.2 hnull]
          simp [measureReal_def]
      have hce1 := hconst_ce ((measurable_subProj hA) hs1_m)
      have hce2 := hconst_ce ((measurable_subProj hB) hs2_m)
      have hce12 := hconst_ce (((measurable_subProj hA) hs1_m).inter ((measurable_subProj hB) hs2_m))
      have hprod_eq : (μR (subProj hA ⁻¹' s1 ∩ subProj hB ⁻¹' s2)).toReal =
          (μR (subProj hA ⁻¹' s1)).toReal * (μR (subProj hB ⁻¹' s2)).toReal := by
        have hae : ∀ᵐ y ∂μR, (μR (subProj hA ⁻¹' s1 ∩ subProj hB ⁻¹' s2)).toReal =
            (μR (subProj hA ⁻¹' s1)).toReal * (μR (subProj hB ⁻¹' s2)).toReal := by
          filter_upwards [hfac, hce1, hce2, hce12] with y hy h1 h2 h12
          rw [← h12, hy, Pi.mul_apply, h1, h2]
        obtain ⟨y, hy⟩ := hae.exists
        exact hy
      -- Show `μR(t1 ∩ t2) = 0`, while `μR(t1) > 0` and `μR(t2) > 0`!
      have hinter0 : μR (subProj hA ⁻¹' s1 ∩ subProj hB ⁻¹' s2) = 0 := by
        rw [show μR = (rayExponentMeasure b |>.map (coordProj M) R)⁻¹ •
            ((rayExponentMeasure b |>.map (coordProj M)).restrict R) from rfl,
          Measure.smul_apply, smul_eq_mul, Measure.restrict_apply
            (((measurable_subProj hA) hs1_m).inter ((measurable_subProj hB) hs2_m))]
        suffices h0 : (rayExponentMeasure b).map (coordProj M)
            ((subProj hA ⁻¹' s1 ∩ subProj hB ⁻¹' s2) ∩ R) = 0 by rw [h0, mul_zero]
        rw [rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
          Measure.finsetSum_apply]
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k i) :=
          Measurable.of_eval fun i ↦ measurable_id.mul_const (b k i)
        rw [Measure.map_map (measurable_coordProj M) hray,
          Measure.map_apply ((measurable_coordProj M).comp hray)
            ((((measurable_subProj hA) hs1_m).inter ((measurable_subProj hB) hs2_m)).inter
              (MeasurableSet.univ_pi hRc_m))]
        refine measure_mono_null (fun r hr ↦ ?_) radialMeasure_Iic_zero
        -- If `r > 0` and `r • b k ∈ t1 ∩ t2 ∩ R`, then `k ∈ Kact` and `y_{b₀} ≤ αmax * y_{a₀} ≤ 4/3 * αmax`, contradiction!
        by_contra hr0
        have hr_pos : 0 < r := not_le.1 hr0
        rcases hr with ⟨⟨hr1, hr2⟩, hrR⟩
        have hra_mem : r * b k a₀ ∈ Icc (1 : ℝ) (4 / 3) := hr1
        have hrb_mem : r * b k b₀ ∈ Ioc (4 / 3 * α kstar) (2 * α kstar) := hr2
        have hka_pos : 0 < b k a₀ := by
          have : 0 < r * b k a₀ := lt_of_lt_of_le zero_lt_one hra_mem.1
          exact (mul_pos_iff_of_pos_left hr_pos).1 this
        have hkC : ∀ c ∈ C, b k c = 0 := by
          intro c hc
          have hmem := hrR ⟨c, hC hc⟩ (mem_univ _)
          have hne : c ≠ a₀ := fun h ↦ ha₀_not_C (h ▸ hc)
          simp only [Rc, hne, hc, ↓reduceIte, mem_singleton_iff, Function.comp_apply,
            coordProj] at hmem
          exact (mul_eq_zero.1 hmem).resolve_left hr_pos.ne'
        have hk_act : k ∈ Kact := Finset.mem_filter.2 ⟨Finset.mem_univ _, hkC, hka_pos⟩
        have hα_le : b k b₀ / b k a₀ ≤ α kstar := hkstar_max k hk_act
        have hle_b : r * b k b₀ ≤ (r * b k a₀) * α kstar := by
          have h1 : b k b₀ ≤ α kstar * b k a₀ := (div_le_iff₀ hka_pos).1 hα_le
          have h2 := mul_le_mul_of_nonneg_left h1 hr_pos.le
          linarith
        have hle2 : (r * b k a₀) * α kstar ≤ 4 / 3 * α kstar :=
          mul_le_mul_of_nonneg_right hra_mem.2 hα_pos.le
        linarith [hrb_mem.1]
      have ht1_pos : 0 < μR (subProj hA ⁻¹' s1) := by
        rw [show μR = (rayExponentMeasure b |>.map (coordProj M) R)⁻¹ •
            ((rayExponentMeasure b |>.map (coordProj M)).restrict R) from rfl,
          Measure.smul_apply, smul_eq_mul,
          Measure.restrict_apply ((measurable_subProj hA) hs1_m)]
        refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hΛ_top) ?_
        rw [rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
          Measure.finsetSum_apply]
        refine (lt_of_lt_of_le ?_ (Finset.single_le_sum
          (f := fun k ↦ (((radialMeasure 1).map (fun r : ℝ ↦ fun i : V ↦ r * b k i)).map (coordProj M))
            (subProj hA ⁻¹' s1 ∩ R)) (fun _ _ ↦ zero_le) (Finset.mem_univ kstar))).ne'
        have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b kstar i) :=
          Measurable.of_eval fun i ↦ measurable_id.mul_const (b kstar i)
        rw [Measure.map_map (measurable_coordProj M) hray,
          Measure.map_apply ((measurable_coordProj M).comp hray)
            (((measurable_subProj hA) hs1_m).inter (MeasurableSet.univ_pi hRc_m))]
        have hsub : Ioc (1 / b kstar a₀) (4 / 3 / b kstar a₀) ⊆
            (coordProj M ∘ fun r i ↦ r * b kstar i) ⁻¹' (subProj hA ⁻¹' s1 ∩ R) := by
          intro r ⟨hr1, hr2⟩
          have hr_pos : 0 < r := lt_of_le_of_lt (div_nonneg zero_le_one hks_a.le) hr1
          have ha_lo : 1 ≤ r * b kstar a₀ := (div_le_iff₀ hks_a).1 hr1.le
          have ha_hi : r * b kstar a₀ ≤ 4 / 3 := (le_div_iff₀ hks_a).1 hr2
          refine ⟨⟨ha_lo, ha_hi⟩, fun i _ ↦ ?_⟩
          simp only [Rc, Function.comp_apply, coordProj]
          split_ifs with h1 h2
          · rw [h1]; exact ⟨ha_lo, by linarith⟩
          · simp [hks_C i.1 h2]
          · exact mul_nonneg hr_pos.le (hb kstar i.1)
        have hpos_int : 0 < radialMeasure 1 (Ioc (1 / b kstar a₀) (4 / 3 / b kstar a₀)) := by
          have h1 : 0 < 1 / b kstar a₀ := div_pos one_pos hks_a
          have h2 : 0 < 4 / 3 / b kstar a₀ := div_pos (by norm_num) hks_a
          have hle : 1 / b kstar a₀ < 4 / 3 / b kstar a₀ := by
            rw [div_lt_div_iff₀ hks_a hks_a]; linarith
          have hadd : radialMeasure 1 (Ioi (1 / b kstar a₀)) =
              radialMeasure 1 (Ioc (1 / b kstar a₀) (4 / 3 / b kstar a₀)) +
              radialMeasure 1 (Ioi (4 / 3 / b kstar a₀)) := by
            rw [← measure_union Ioc_disjoint_Ioi_same measurableSet_Ioi, Ioc_union_Ioi_eq_Ioi hle.le]
          by_contra h0
          rw [le_antisymm (not_lt.1 h0) bot_le, zero_add, radialMeasure_Ioi one_pos h1,
            radialMeasure_Ioi one_pos h2, Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div,
            div_one] at hadd
          have hlt : b kstar a₀ / (4 / 3) < b kstar a₀ := by linarith
          exact ((ENNReal.ofReal_lt_ofReal_iff hks_a).2 hlt).ne' hadd
        exact lt_of_lt_of_le hpos_int (measure_mono hsub)
      have ht2_pos : 0 < μR (subProj hB ⁻¹' s2) := by
        rw [show μR = (rayExponentMeasure b |>.map (coordProj M) R)⁻¹ •
            ((rayExponentMeasure b |>.map (coordProj M)).restrict R) from rfl,
          Measure.smul_apply, smul_eq_mul,
          Measure.restrict_apply ((measurable_subProj hB) hs2_m)]
        refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hΛ_top) ?_
        rw [rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
          Measure.finsetSum_apply]
        refine (lt_of_lt_of_le ?_ (Finset.single_le_sum
          (f := fun k ↦ (((radialMeasure 1).map (fun r : ℝ ↦ fun i : V ↦ r * b k i)).map (coordProj M))
            (subProj hB ⁻¹' s2 ∩ R)) (fun _ _ ↦ zero_le) (Finset.mem_univ kstar))).ne'
        have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b kstar i) :=
          Measurable.of_eval fun i ↦ measurable_id.mul_const (b kstar i)
        rw [Measure.map_map (measurable_coordProj M) hray,
          Measure.map_apply ((measurable_coordProj M).comp hray)
            (((measurable_subProj hB) hs2_m).inter (MeasurableSet.univ_pi hRc_m))]
        have hsub : Ioc (4 / 3 / b kstar a₀) (2 / b kstar a₀) ⊆
            (coordProj M ∘ fun r i ↦ r * b kstar i) ⁻¹' (subProj hB ⁻¹' s2 ∩ R) := by
          intro r ⟨hr1, hr2⟩
          have hr_pos : 0 < r := lt_of_le_of_lt (div_nonneg (by norm_num) hks_a.le) hr1
          have ha_lo : 4 / 3 < r * b kstar a₀ := (div_lt_iff₀ hks_a).1 hr1
          have ha_hi : r * b kstar a₀ ≤ 2 := (le_div_iff₀ hks_a).1 hr2
          have hb_eq : r * b kstar b₀ = (r * b kstar a₀) * α kstar := by
            simp only [α]; field_simp [hks_a.ne']
          refine ⟨⟨by change 4 / 3 * α kstar < r * b kstar b₀; rw [hb_eq]; exact mul_lt_mul_of_pos_right ha_lo hα_pos,
            by change r * b kstar b₀ ≤ 2 * α kstar; rw [hb_eq]; exact mul_le_mul_of_nonneg_right ha_hi hα_pos.le⟩,
            fun i _ ↦ ?_⟩
          simp only [Rc, Function.comp_apply, coordProj]
          split_ifs with h1 h2
          · rw [h1]; exact ⟨by linarith, ha_hi⟩
          · simp [hks_C i.1 h2]
          · exact mul_nonneg hr_pos.le (hb kstar i.1)
        have hpos_int : 0 < radialMeasure 1 (Ioc (4 / 3 / b kstar a₀) (2 / b kstar a₀)) := by
          have h1 : 0 < 4 / 3 / b kstar a₀ := div_pos (by norm_num) hks_a
          have h2 : 0 < 2 / b kstar a₀ := div_pos (by norm_num) hks_a
          have hle : 4 / 3 / b kstar a₀ < 2 / b kstar a₀ := by
            rw [div_lt_div_iff₀ hks_a hks_a]; linarith
          have hadd : radialMeasure 1 (Ioi (4 / 3 / b kstar a₀)) =
              radialMeasure 1 (Ioc (4 / 3 / b kstar a₀) (2 / b kstar a₀)) +
              radialMeasure 1 (Ioi (2 / b kstar a₀)) := by
            rw [← measure_union Ioc_disjoint_Ioi_same measurableSet_Ioi, Ioc_union_Ioi_eq_Ioi hle.le]
          by_contra h0
          rw [le_antisymm (not_lt.1 h0) bot_le, zero_add, radialMeasure_Ioi one_pos h1,
            radialMeasure_Ioi one_pos h2, Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div] at hadd
          have hlt : b kstar a₀ / 2 < b kstar a₀ / (4 / 3) := by linarith
          exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt).ne' hadd
        exact lt_of_lt_of_le hpos_int (measure_mono hsub)
      rw [hinter0, ENNReal.toReal_zero] at hprod_eq
      have h1_pos : 0 < (μR (subProj hA ⁻¹' s1)).toReal :=
        ENNReal.toReal_pos ht1_pos.ne' (measure_ne_top _ _)
      have h2_pos : 0 < (μR (subProj hB ⁻¹' s2)).toReal :=
        ENNReal.toReal_pos ht2_pos.ne' (measure_ne_top _ _)
      linarith [mul_pos h1_pos h2_pos]
    · -- Necessity of Condition (II)
      intro v x₀ y₀
      let Iv := Finset.univ.filter fun k : κ ↦ 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
      by_cases hIv : Iv.Nonempty
      · obtain ⟨k₀, hk₀⟩ := hIv
        have hk₀_pos : 0 < rayL1Norm (b k₀) C := (Finset.mem_filter.1 hk₀).2.1
        have hk₀_dir : rayDir (b k₀) C = v := (Finset.mem_filter.1 hk₀).2.2
        have hv_nonneg : ∀ c : C, 0 ≤ v c := fun c ↦ by
          rw [← hk₀_dir, rayDir]; exact div_nonneg (hb k₀ c.1) hk₀_pos.le
        have hv_sum : ∑ c : C, v c = 1 := hk₀_dir ▸ sum_rayDir hk₀_pos
        have hex_c : ∃ c₀ : C, 0 < v c₀ := by
          by_contra h; push Not at h
          have : ∑ c : C, v c = 0 := Finset.sum_eq_zero fun c _ ↦ le_antisymm (h c) (hv_nonneg c)
          linarith
        rcases hex_c with ⟨c₀, hc₀_pos⟩
        -- Product test set `R`: `R_c = [v c, 2 * v c]` for `c ∈ C` with `v c > 0`, `{0}` if `v c = 0`, `[0, ∞)` on `A ∪ B`.
        let Rc : M → Set ℝ := fun i ↦
          if hiC : i.1 ∈ C then
            if 0 < v ⟨i.1, hiC⟩ then Icc (v ⟨i.1, hiC⟩) (2 * v ⟨i.1, hiC⟩) else {0}
          else Ici 0
        have hRc_m : ∀ i, MeasurableSet (Rc i) := fun i ↦ by
          simp only [Rc]; split_ifs
          · exact measurableSet_Icc
          · exact measurableSet_singleton 0
          · exact measurableSet_Ici
        let R : Set (M → ℝ) := Set.univ.pi Rc
        have h0_not_cl : (0 : M → ℝ) ∉ closure R := by
          intro h0
          rw [closure_pi_set, mem_univ_pi] at h0
          have h0c := h0 ⟨c₀.1, hC c₀.2⟩
          simp only [Rc, c₀.2, ↓reduceDIte, hc₀_pos, ↓reduceIte, closure_Icc, Pi.zero_apply, mem_Icc] at h0c
          linarith
        -- Show `ΛM R > 0` via `k₀` (for `t ∈ (1, 2]`, `r = t / lam_{k₀}` lies in `R`)!
        have hΛ_pos : 0 < (rayExponentMeasure b).map (coordProj M) R := by
          rw [rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
            Measure.finsetSum_apply]
          refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ k₀))
          have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k₀ i) :=
            Measurable.of_eval fun i ↦ measurable_id.mul_const (b k₀ i)
          rw [Measure.map_map (measurable_coordProj M) hray,
            Measure.map_apply ((measurable_coordProj M).comp hray) (MeasurableSet.univ_pi hRc_m)]
          have hsub : Ioc (1 / rayL1Norm (b k₀) C) (2 / rayL1Norm (b k₀) C) ⊆
              (coordProj M ∘ fun r i ↦ r * b k₀ i) ⁻¹' R := by
            intro r ⟨hr1, hr2⟩
            have hr_pos : 0 < r := lt_of_le_of_lt (div_nonneg zero_le_one hk₀_pos.le) hr1
            have ht1 : 1 ≤ r * rayL1Norm (b k₀) C := (div_le_iff₀ hk₀_pos).1 hr1.le
            have ht2 : r * rayL1Norm (b k₀) C ≤ 2 := (le_div_iff₀ hk₀_pos).1 hr2
            intro i _
            simp only [Rc, Function.comp_apply, coordProj]
            split_ifs with hiC hvc
            · have hval : r * b k₀ i.1 = (r * rayL1Norm (b k₀) C) * v ⟨i.1, hiC⟩ := by
                rw [← hk₀_dir, rayDir]; field_simp [hk₀_pos.ne']
              rw [hval]; exact ⟨by nlinarith, by nlinarith⟩
            · have hv0 : v ⟨i.1, hiC⟩ = 0 := le_antisymm (not_lt.1 hvc) (hv_nonneg ⟨i.1, hiC⟩)
              have hval : r * b k₀ i.1 = (r * rayL1Norm (b k₀) C) * v ⟨i.1, hiC⟩ := by
                rw [← hk₀_dir, rayDir]; field_simp [hk₀_pos.ne']
              simp [hval, hv0]
            · exact mul_nonneg hr_pos.le (hb k₀ i.1)
          have hpos_int : 0 < radialMeasure 1 (Ioc (1 / rayL1Norm (b k₀) C) (2 / rayL1Norm (b k₀) C)) := by
            have h1 : 0 < 1 / rayL1Norm (b k₀) C := div_pos one_pos hk₀_pos
            have h2 : 0 < 2 / rayL1Norm (b k₀) C := div_pos (by norm_num) hk₀_pos
            have hle : 1 / rayL1Norm (b k₀) C < 2 / rayL1Norm (b k₀) C := by
              rw [div_lt_div_iff₀ hk₀_pos hk₀_pos]; linarith
            have hadd : radialMeasure 1 (Ioi (1 / rayL1Norm (b k₀) C)) =
                radialMeasure 1 (Ioc (1 / rayL1Norm (b k₀) C) (2 / rayL1Norm (b k₀) C)) +
                radialMeasure 1 (Ioi (2 / rayL1Norm (b k₀) C)) := by
              rw [← measure_union Ioc_disjoint_Ioi_same measurableSet_Ioi, Ioc_union_Ioi_eq_Ioi hle.le]
            by_contra h0
            rw [le_antisymm (not_lt.1 h0) bot_le, zero_add, radialMeasure_Ioi one_pos h1,
              radialMeasure_Ioi one_pos h2, Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div,
              div_one] at hadd
            exact ((ENNReal.ofReal_lt_ofReal_iff hk₀_pos).2 (by linarith)).ne' hadd
          exact lt_of_lt_of_le hpos_int (measure_mono hsub)
        have hΛ_top : (rayExponentMeasure b).map (coordProj M) R ≠ ∞ :=
          (rayExponentMeasure_map_lt_top_of_zero_notMem_closure b hb h0_not_cl).ne
        have hR_test : IsProductTestSet (rayExponentMeasure b) M R :=
          ⟨⟨Rc, hRc_m, rfl⟩, h0_not_cl, hΛ_pos, hΛ_top⟩
        -- Choose `δ ∈ (0, 1]` small enough that for every `k ∈ Iv`:
        -- `t • rayScaled (b k) C A ∈ {s • x₀ | s ∈ [1, 1 + δ]} ↔ rayScaled (b k) C A = x₀` (for `t ∈ [1, 1 + δ]`),
        -- and similarly for `y₀`!
        have hex_δ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            (∀ k ∈ Iv, rayScaled (b k) C A ≠ x₀ → ∀ t ∈ Icc (1 : ℝ) (1 + δ), ∀ s ∈ Icc (1 : ℝ) (1 + δ),
              t • rayScaled (b k) C A ≠ s • x₀) ∧
            (∀ k ∈ Iv, rayScaled (b k) C B ≠ y₀ → ∀ t ∈ Icc (1 : ℝ) (1 + δ), ∀ s ∈ Icc (1 : ℝ) (1 + δ),
              t • rayScaled (b k) C B ≠ s • y₀) := by
          -- For any fixed `u ≠ w`, there is `δ_uw ∈ (0, 1]` avoiding `t • u = s • w` on `[1, 1 + δ]`:
          have hpair : ∀ {ι : Type _} (u w : ι → ℝ), u ≠ w →
              ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t ∈ Icc (1 : ℝ) (1 + δ), ∀ s ∈ Icc (1 : ℝ) (1 + δ),
                t • u ≠ s • w := by
            intro ι u w hne
            by_cases hratio : ∃ α : ℝ, α ≠ 1 ∧ 0 < α ∧ u = α • w
            · rcases hratio with ⟨α, hα1, hαpos, huw⟩
              have hmax_gt : 1 < max α α⁻¹ := by
                rcases lt_or_gt_of_ne hα1 with hlt | hgt
                · exact lt_max_of_lt_right ((one_lt_inv₀ hαpos).2 hlt)
                · exact lt_max_of_lt_left hgt
              let δ0 : ℝ := min 1 ((max α α⁻¹ - 1) / 2)
              have hδ0_pos : 0 < δ0 := lt_min one_pos (by linarith)
              have hδ0_le1 : δ0 ≤ 1 := min_le_left _ _
              have hbound : 1 + δ0 < max α α⁻¹ := by
                have : δ0 ≤ (max α α⁻¹ - 1) / 2 := min_le_right _ _
                linarith
              refine ⟨δ0, hδ0_pos, hδ0_le1, fun t ht s hs heq ↦ ?_⟩
              have h1 : (t * α) • w = s • w := by simpa [huw, smul_smul] using heq
              have hw0 : w ≠ 0 := by
                intro hw0; subst hw0; simp at huw; exact hne huw
              have hta : t * α = s := smul_left_injective ℝ hw0 h1
              rcases lt_or_gt_of_ne hα1 with hlt | hgt
              · have hmax_eq : max α α⁻¹ = α⁻¹ := max_eq_right (le_trans hlt.le ((one_lt_inv₀ hαpos).2 hlt).le)
                rw [hmax_eq] at hbound
                have hst : s * α⁻¹ = t := by rw [← hta, mul_assoc, mul_inv_cancel₀ hαpos.ne', mul_one]
                have h2' : s * (1 + δ0) < s * α⁻¹ :=
                  mul_lt_mul_of_pos_left hbound (lt_of_lt_of_le one_pos hs.1)
                have h4' : 1 + δ0 ≤ s * (1 + δ0) := le_mul_of_one_le_left (by linarith) hs.1
                linarith [ht.2]
              · have hmax_eq : max α α⁻¹ = α := max_eq_left (le_trans ((inv_lt_one_of_one_lt₀ hgt).le) hgt.le)
                rw [hmax_eq] at hbound
                have h2' : t * (1 + δ0) < t * α :=
                  mul_lt_mul_of_pos_left hbound (lt_of_lt_of_le one_pos ht.1)
                have h4' : 1 + δ0 ≤ t * (1 + δ0) := le_mul_of_one_le_left (by linarith) ht.1
                linarith [hs.2]
            · refine ⟨1, one_pos, le_rfl, fun t ht s hs heq ↦ ?_⟩
              have htpos : 0 < t := lt_of_lt_of_le one_pos ht.1
              have hspos : 0 < s := lt_of_lt_of_le one_pos hs.1
              have huw : u = (s / t) • w := by
                rw [div_eq_inv_mul, mul_smul, ← heq, inv_smul_smul₀ htpos.ne']
              by_cases hst : s / t = 1
              · rw [hst, one_smul] at huw; exact hne huw
              · exact hratio ⟨s / t, hst, div_pos hspos htpos, huw⟩
          -- Take the finite minimum of `δ` over all `k ∈ Iv` for both `A` and `B`!
          have hchooseA : ∀ k : κ, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
              (k ∈ Iv → rayScaled (b k) C A ≠ x₀ →
                ∀ t ∈ Icc (1 : ℝ) (1 + δ), ∀ s ∈ Icc (1 : ℝ) (1 + δ),
                t • rayScaled (b k) C A ≠ s • x₀) := by
            intro k
            by_cases h : k ∈ Iv ∧ rayScaled (b k) C A ≠ x₀
            · obtain ⟨δ, hδ0, hδ1, hδ⟩ := hpair (rayScaled (b k) C A) x₀ h.2
              exact ⟨δ, hδ0, hδ1, fun _ _ ↦ hδ⟩
            · exact ⟨1, one_pos, le_rfl, fun hk hne ↦ (h ⟨hk, hne⟩).elim⟩
          have hchooseB : ∀ k : κ, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
              (k ∈ Iv → rayScaled (b k) C B ≠ y₀ →
                ∀ t ∈ Icc (1 : ℝ) (1 + δ), ∀ s ∈ Icc (1 : ℝ) (1 + δ),
                t • rayScaled (b k) C B ≠ s • y₀) := by
            intro k
            by_cases h : k ∈ Iv ∧ rayScaled (b k) C B ≠ y₀
            · obtain ⟨δ, hδ0, hδ1, hδ⟩ := hpair (rayScaled (b k) C B) y₀ h.2
              exact ⟨δ, hδ0, hδ1, fun _ _ ↦ hδ⟩
            · exact ⟨1, one_pos, le_rfl, fun hk hne ↦ (h ⟨hk, hne⟩).elim⟩
          choose δA hδA0 hδA1 hδA using hchooseA
          choose δB hδB0 hδB1 hδB using hchooseB
          let δmin : ℝ := min
            (Finset.univ.inf' ⟨k₀, Finset.mem_univ k₀⟩ δA)
            (Finset.univ.inf' ⟨k₀, Finset.mem_univ k₀⟩ δB)
          have hδmin_pos : 0 < δmin := by
            refine lt_min ?_ ?_
            · exact (Finset.lt_inf'_iff ⟨k₀, Finset.mem_univ k₀⟩).2 fun k _ ↦ hδA0 k
            · exact (Finset.lt_inf'_iff ⟨k₀, Finset.mem_univ k₀⟩).2 fun k _ ↦ hδB0 k
          have hδmin_le1 : δmin ≤ 1 :=
            le_trans (min_le_left _ _) (le_trans (Finset.inf'_le δA (Finset.mem_univ k₀)) (hδA1 k₀))
          refine ⟨δmin, hδmin_pos, hδmin_le1, fun k hk hne t ht s hs ↦ ?_, fun k hk hne t ht s hs ↦ ?_⟩
          · have hle : δmin ≤ δA k := le_trans (min_le_left _ _) (Finset.inf'_le δA (Finset.mem_univ k))
            exact hδA k hk hne t ⟨ht.1, ht.2.trans (by linarith)⟩ s ⟨hs.1, hs.2.trans (by linarith)⟩
          · have hle : δmin ≤ δB k := le_trans (min_le_right _ _) (Finset.inf'_le δB (Finset.mem_univ k))
            exact hδB k hk hne t ⟨ht.1, ht.2.trans (by linarith)⟩ s ⟨hs.1, hs.2.trans (by linarith)⟩
        rcases hex_δ with ⟨δ, hδ0, hδ1, hsepA, hsepB⟩
        -- Define compact (hence Borel measurable!) ray-segment test sets `EA, EB, EC`:
        let EA : Set (A → ℝ) := (fun s : ℝ ↦ s • x₀) '' Icc 1 (1 + δ)
        let EB : Set (B → ℝ) := (fun s : ℝ ↦ s • y₀) '' Icc 1 (1 + δ)
        let EC : Set (C → ℝ) := (fun t : ℝ ↦ t • v) '' Icc 1 (1 + δ)
        have hEA_m : MeasurableSet EA :=
          (isCompact_Icc.image (continuous_id.smul continuous_const)).isClosed.measurableSet
        have hEB_m : MeasurableSet EB :=
          (isCompact_Icc.image (continuous_id.smul continuous_const)).isClosed.measurableSet
        have hEC_m : MeasurableSet EC :=
          (isCompact_Icc.image (continuous_id.smul continuous_const)).isClosed.measurableSet
        -- Apply `hECI` and `condExp_rayExponentMeasure_eq`!
        let μR := condProbMeasure (rayExponentMeasure b) M R
        have : IsProbabilityMeasure μR := isProbabilityMeasure_condProbMeasure hΛ_pos hΛ_top
        have hCI := hECI R hR_test
        rw [condIndepFun_iff _ _ (subProj hA) (subProj hB) (measurable_subProj hA)
          (measurable_subProj hB) μR] at hCI
        have hfac := hCI (subProj hA ⁻¹' EA) (subProj hB ⁻¹' EB) ⟨EA, hEA_m, rfl⟩ ⟨EB, hEB_m, rfl⟩
        have hceA := condExp_rayExponentMeasure_eq b hb hRc_m hR_test (hEA_m.prod MeasurableSet.univ)
        have hceB := condExp_rayExponentMeasure_eq b hb hRc_m hR_test (MeasurableSet.univ.prod hEB_m)
        have hceAB := condExp_rayExponentMeasure_eq b hb hRc_m hR_test (hEA_m.prod hEB_m)
        -- Notice `subProj hC ⁻¹' EC` has POSITIVE `μR`-measure (from ray `k₀` for `t ∈ (1, 1 + δ]`)!
        have hEC_pos : 0 < μR (subProj hC ⁻¹' EC) := by
          rw [show μR = (rayExponentMeasure b |>.map (coordProj M) R)⁻¹ •
              ((rayExponentMeasure b |>.map (coordProj M)).restrict R) from rfl,
            Measure.smul_apply, smul_eq_mul, Measure.restrict_apply ((measurable_subProj hC) hEC_m)]
          refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hΛ_top) ?_
          rw [rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
            Measure.finsetSum_apply]
          refine (lt_of_lt_of_le ?_ (Finset.single_le_sum
            (f := fun k ↦ (((radialMeasure 1).map (fun r : ℝ ↦ fun i : V ↦ r * b k i)).map (coordProj M))
              (subProj hC ⁻¹' EC ∩ R)) (fun _ _ ↦ zero_le) (Finset.mem_univ k₀))).ne'
          have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k₀ i) :=
            Measurable.of_eval fun i ↦ measurable_id.mul_const (b k₀ i)
          rw [Measure.map_map (measurable_coordProj M) hray,
            Measure.map_apply ((measurable_coordProj M).comp hray)
              (((measurable_subProj hC) hEC_m).inter (MeasurableSet.univ_pi hRc_m))]
          have hsub : Ioc (1 / rayL1Norm (b k₀) C) ((1 + δ) / rayL1Norm (b k₀) C) ⊆
              (coordProj M ∘ fun r i ↦ r * b k₀ i) ⁻¹' (subProj hC ⁻¹' EC ∩ R) := by
            intro r ⟨hr1, hr2⟩
            have hr_pos : 0 < r := lt_of_le_of_lt (div_nonneg zero_le_one hk₀_pos.le) hr1
            have ht1 : 1 ≤ r * rayL1Norm (b k₀) C := (div_le_iff₀ hk₀_pos).1 hr1.le
            have ht2 : r * rayL1Norm (b k₀) C ≤ 1 + δ := (le_div_iff₀ hk₀_pos).1 hr2
            refine ⟨⟨r * rayL1Norm (b k₀) C, ⟨ht1, ht2⟩, ?_⟩, fun i _ ↦ ?_⟩
            · funext c; simp only [Function.comp_apply, subProj, coordProj, Pi.smul_apply,
                smul_eq_mul, ← hk₀_dir, rayDir]
              field_simp [hk₀_pos.ne']
            · simp only [Rc, Function.comp_apply, coordProj]
              split_ifs with hiC hvc
              · have hval : r * b k₀ i.1 = (r * rayL1Norm (b k₀) C) * v ⟨i.1, hiC⟩ := by
                  rw [← hk₀_dir, rayDir]; field_simp [hk₀_pos.ne']
                rw [hval]; exact ⟨by nlinarith, by nlinarith⟩
              · have hv0 : v ⟨i.1, hiC⟩ = 0 := le_antisymm (not_lt.1 hvc) (hv_nonneg ⟨i.1, hiC⟩)
                have hval : r * b k₀ i.1 = (r * rayL1Norm (b k₀) C) * v ⟨i.1, hiC⟩ := by
                  rw [← hk₀_dir, rayDir]; field_simp [hk₀_pos.ne']
                simp [hval, hv0]
              · exact mul_nonneg hr_pos.le (hb k₀ i.1)
          have hpos_int : 0 < radialMeasure 1 (Ioc (1 / rayL1Norm (b k₀) C) ((1 + δ) / rayL1Norm (b k₀) C)) := by
            have h1 : 0 < 1 / rayL1Norm (b k₀) C := div_pos one_pos hk₀_pos
            have h2 : 0 < (1 + δ) / rayL1Norm (b k₀) C := div_pos (by linarith) hk₀_pos
            have hle : 1 / rayL1Norm (b k₀) C < (1 + δ) / rayL1Norm (b k₀) C := by
              rw [div_lt_div_iff₀ hk₀_pos hk₀_pos]; nlinarith
            have hadd : radialMeasure 1 (Ioi (1 / rayL1Norm (b k₀) C)) =
                radialMeasure 1 (Ioc (1 / rayL1Norm (b k₀) C) ((1 + δ) / rayL1Norm (b k₀) C)) +
                radialMeasure 1 (Ioi ((1 + δ) / rayL1Norm (b k₀) C)) := by
              rw [← measure_union Ioc_disjoint_Ioi_same measurableSet_Ioi, Ioc_union_Ioi_eq_Ioi hle.le]
            by_contra h0
            rw [le_antisymm (not_lt.1 h0) bot_le, zero_add, radialMeasure_Ioi one_pos h1,
              radialMeasure_Ioi one_pos h2, Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div,
              div_one] at hadd
            have hlt : rayL1Norm (b k₀) C / (1 + δ) < rayL1Norm (b k₀) C :=
              div_lt_self hk₀_pos (by linarith)
            exact ((ENNReal.ofReal_lt_ofReal_iff hk₀_pos).2 hlt).ne' hadd
          exact lt_of_lt_of_le hpos_int (measure_mono hsub)
        -- Extract a witness point `y ∈ subProj hC ⁻¹' EC` where `pAB = pA * pB`!
        let cAB := ((rayExponentMeasure b).map (coordProj M)
            (R ∩ subProj hC ⁻¹' {0} ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB))).toReal /
          ((rayExponentMeasure b).map (coordProj M) (R ∩ subProj hC ⁻¹' {0})).toReal
        let cA := ((rayExponentMeasure b).map (coordProj M)
            (R ∩ subProj hC ⁻¹' {0} ∩ subProj hA ⁻¹' EA)).toReal /
          ((rayExponentMeasure b).map (coordProj M) (R ∩ subProj hC ⁻¹' {0})).toReal
        let cB := ((rayExponentMeasure b).map (coordProj M)
            (R ∩ subProj hC ⁻¹' {0} ∩ subProj hB ⁻¹' EB)).toReal /
          ((rayExponentMeasure b).map (coordProj M) (R ∩ subProj hC ⁻¹' {0})).toReal
        have hae_eq : ∀ᵐ y ∂μR,
            rayCondProb b A B C (Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩)
              (Set.univ.pi fun b : B ↦ Rc ⟨b.1, hB b.2⟩) (EA ×ˢ EB) cAB (subProj hC y) =
            rayCondProb b A B C (Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩)
              (Set.univ.pi fun b : B ↦ Rc ⟨b.1, hB b.2⟩) (EA ×ˢ univ) cA (subProj hC y) *
            rayCondProb b A B C (Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩)
              (Set.univ.pi fun b : B ↦ Rc ⟨b.1, hB b.2⟩) (univ ×ˢ EB) cB (subProj hC y) := by
          filter_upwards [hfac, hceA, hceB, hceAB] with y hy h1 h2 h12
          have hpreA : (fun y : M → ℝ ↦ (subProj hA y, subProj hB y)) ⁻¹' (EA ×ˢ univ) =
              subProj hA ⁻¹' EA := by ext z; simp
          have hpreB : (fun y : M → ℝ ↦ (subProj hA y, subProj hB y)) ⁻¹' (univ ×ˢ EB) =
              subProj hB ⁻¹' EB := by ext z; simp
          have hpreAB : (fun y : M → ℝ ↦ (subProj hA y, subProj hB y)) ⁻¹' (EA ×ˢ EB) =
              subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB := by ext z; simp
          rw [hpreA] at h1; rw [hpreB] at h2; rw [hpreAB] at h12
          rw [h12, hy, Pi.mul_apply, ← h1, ← h2]
        have hex_y : ∃ y ∈ subProj hC ⁻¹' EC,
            rayCondProb b A B C (Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩)
              (Set.univ.pi fun b : B ↦ Rc ⟨b.1, hB b.2⟩) (EA ×ˢ EB) cAB (subProj hC y) =
            rayCondProb b A B C (Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩)
              (Set.univ.pi fun b : B ↦ Rc ⟨b.1, hB b.2⟩) (EA ×ˢ univ) cA (subProj hC y) *
            rayCondProb b A B C (Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩)
              (Set.univ.pi fun b : B ↦ Rc ⟨b.1, hB b.2⟩) (univ ×ˢ EB) cB (subProj hC y) := by
          by_contra hno
          push Not at hno
          have hnull : μR (subProj hC ⁻¹' EC) = 0 :=
            measure_mono_null (fun y hy ↦ hno y hy) (ae_iff.1 hae_eq)
          exact hEC_pos.ne' hnull
        rcases hex_y with ⟨y, ⟨t, ht_mem, htv⟩, hEq_y⟩
        have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht_mem.1
        have htv_sum : ∑ c : C, (t • v) c = t := by
          simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv_sum, mul_one]
        have htv_ne : t • v ≠ 0 := by
          intro h0; rw [h0] at htv_sum; simp at htv_sum; linarith
        -- Evaluate the three `rayCondProb` terms at `subProj hC y = t • v`:
        -- Every `k` with `0 < lam_k` and `t • v = t • rayDir (b k) C` has `k ∈ Iv`, `t • rayScaled ∈ RA/RB`
        -- (since `Rc` on `A ∪ B` is `Ici 0`), and `t • rayScaled ∈ EA ↔ rayScaled = x₀`!
        have hRA_mem (k : κ) (hk : 0 < rayL1Norm (b k) C) :
            t • rayScaled (b k) C A ∈ Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩ := by
          intro a _
          have ha_not_C : a.1 ∉ C := Finset.disjoint_left.1 hAC a.2
          simp only [Rc, ha_not_C, ↓reduceDIte, mem_Ici, Pi.smul_apply, smul_eq_mul, rayScaled]
          exact mul_nonneg ht_pos.le (div_nonneg (hb k a.1) hk.le)
        have hRB_mem (k : κ) (hk : 0 < rayL1Norm (b k) C) :
            t • rayScaled (b k) C B ∈ Set.univ.pi fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩ := by
          intro b' _
          have hb_not_C : b'.1 ∉ C := Finset.disjoint_left.1 hBC b'.2
          simp only [Rc, hb_not_C, ↓reduceDIte, mem_Ici, Pi.smul_apply, smul_eq_mul, rayScaled]
          exact mul_nonneg ht_pos.le (div_nonneg (hb k b'.1) hk.le)
        have hEA_iff (k : κ) (hk : k ∈ Iv) : t • rayScaled (b k) C A ∈ EA ↔ rayScaled (b k) C A = x₀ := by
          constructor
          · rintro ⟨s, hs, hEq⟩
            by_contra hne
            exact hsepA k hk hne t ht_mem s hs hEq.symm
          · intro hEq; exact ⟨t, ht_mem, by rw [hEq]⟩
        have hEB_iff (k : κ) (hk : k ∈ Iv) : t • rayScaled (b k) C B ∈ EB ↔ rayScaled (b k) C B = y₀ := by
          constructor
          · rintro ⟨s, hs, hEq⟩
            by_contra hne
            exact hsepB k hk hne t ht_mem s hs hEq.symm
          · intro hEq; exact ⟨t, ht_mem, by rw [hEq]⟩
        have hden_eq :
            (∑ k : κ, if 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
              t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
              t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩)
              then rayL1Norm (b k) C else 0) = rayDirMass b C v (fun _ ↦ True) := by
          unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
          · have h1 : 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) :=
              ⟨hk.1, ht_pos, by rw [hk.2], hRA_mem k hk.1, hRB_mem k hk.1⟩
            have h2 : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ True := ⟨hk.1, hk.2, trivial⟩
            rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
          · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩)) := by
              rintro ⟨h1, _, h3, _⟩; exact hk ⟨h1, (smul_right_injective _ ht_pos.ne' h3).symm⟩
            have h2 : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ True) :=
              fun ⟨h1, h2, _⟩ ↦ hk ⟨h1, h2⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
        have hnumA_eq :
            (∑ k : κ, if 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
              t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
              t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
              (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ univ
              then rayL1Norm (b k) C else 0) =
            rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x₀) := by
          unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
          · have hkIv : k ∈ Iv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk.1, hk.2⟩
            by_cases hx : rayScaled (b k) C A = x₀
            · have h1 : 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                  t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                  t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                  (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ univ :=
                ⟨hk.1, ht_pos, by rw [hk.2], hRA_mem k hk.1, hRB_mem k hk.1, (hEA_iff k hkIv).2 hx, mem_univ _⟩
              have h2 : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C A = x₀ := ⟨hk.1, hk.2, hx⟩
              rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
            · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                  t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                  t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                  (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ univ) := by
                rintro ⟨_, _, _, _, _, hEA, _⟩; exact hx ((hEA_iff k hkIv).1 hEA)
              have h2 : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C A = x₀) :=
                fun ⟨_, _, h⟩ ↦ hx h
              rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
          · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ univ) := by
              rintro ⟨h1, _, h3, _⟩; exact hk ⟨h1, (smul_right_injective _ ht_pos.ne' h3).symm⟩
            have h2 : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C A = x₀) :=
              fun ⟨h1, h2, _⟩ ↦ hk ⟨h1, h2⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
        have hnumB_eq :
            (∑ k : κ, if 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
              t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
              t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
              (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ univ ×ˢ EB
              then rayL1Norm (b k) C else 0) =
            rayDirMass b C v (fun k ↦ rayScaled (b k) C B = y₀) := by
          unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
          · have hkIv : k ∈ Iv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk.1, hk.2⟩
            by_cases hy : rayScaled (b k) C B = y₀
            · have h1 : 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                  t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                  t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                  (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ univ ×ˢ EB :=
                ⟨hk.1, ht_pos, by rw [hk.2], hRA_mem k hk.1, hRB_mem k hk.1, mem_univ _, (hEB_iff k hkIv).2 hy⟩
              have h2 : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C B = y₀ := ⟨hk.1, hk.2, hy⟩
              rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
            · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                  t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                  t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                  (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ univ ×ˢ EB) := by
                rintro ⟨_, _, _, _, _, _, hEB⟩; exact hy ((hEB_iff k hkIv).1 hEB)
              have h2 : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C B = y₀) :=
                fun ⟨_, _, h⟩ ↦ hy h
              rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
          · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ univ ×ˢ EB) := by
              rintro ⟨h1, _, h3, _⟩; exact hk ⟨h1, (smul_right_injective _ ht_pos.ne' h3).symm⟩
            have h2 : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ rayScaled (b k) C B = y₀) :=
              fun ⟨h1, h2, _⟩ ↦ hk ⟨h1, h2⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
        have hnumAB_eq :
            (∑ k : κ, if 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
              t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
              t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
              (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ EB
              then rayL1Norm (b k) C else 0) =
            rayDirMass b C v (fun k ↦ rayScaled (b k) C A = x₀ ∧ rayScaled (b k) C B = y₀) := by
          unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v
          · have hkIv : k ∈ Iv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk.1, hk.2⟩
            by_cases hxy : rayScaled (b k) C A = x₀ ∧ rayScaled (b k) C B = y₀
            · have h1 : 0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                  t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                  t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                  (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ EB :=
                ⟨hk.1, ht_pos, by rw [hk.2], hRA_mem k hk.1, hRB_mem k hk.1,
                  (hEA_iff k hkIv).2 hxy.1, (hEB_iff k hkIv).2 hxy.2⟩
              have h2 : 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
                  rayScaled (b k) C A = x₀ ∧ rayScaled (b k) C B = y₀ := ⟨hk.1, hk.2, hxy⟩
              rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
            · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                  t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                  t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                  (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ EB) := by
                rintro ⟨_, _, _, _, _, hEA, hEB⟩
                exact hxy ⟨(hEA_iff k hkIv).1 hEA, (hEB_iff k hkIv).1 hEB⟩
              have h2 : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
                  rayScaled (b k) C A = x₀ ∧ rayScaled (b k) C B = y₀) :=
                fun ⟨_, _, h⟩ ↦ hxy h
              rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
          · have h1 : ¬ (0 < rayL1Norm (b k) C ∧ 0 < t ∧ t • v = t • rayDir (b k) C ∧
                t • rayScaled (b k) C A ∈ Set.univ.pi (fun a : A ↦ Rc ⟨a.1, hA a.2⟩) ∧
                t • rayScaled (b k) C B ∈ Set.univ.pi (fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩) ∧
                (t • rayScaled (b k) C A, t • rayScaled (b k) C B) ∈ EA ×ˢ EB) := by
              rintro ⟨h1, _, h3, _⟩; exact hk ⟨h1, (smul_right_injective _ ht_pos.ne' h3).symm⟩
            have h2 : ¬ (0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧
                rayScaled (b k) C A = x₀ ∧ rayScaled (b k) C B = y₀) :=
              fun ⟨h1, h2, _⟩ ↦ hk ⟨h1, h2⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
        rw [← htv] at hEq_y
        simp only [rayCondProb, htv_ne, ↓reduceIte, htv_sum, hden_eq, hnumA_eq, hnumB_eq, hnumAB_eq] at hEq_y
        have htot_pos : 0 < rayDirMass b C v (fun _ ↦ True) := by
          unfold rayDirMass
          refine lt_of_lt_of_le hk₀_pos ?_
          have hle := Finset.single_le_sum
            (f := fun k ↦ if 0 < rayL1Norm (b k) C ∧ rayDir (b k) C = v ∧ (fun _ ↦ True) k then rayL1Norm (b k) C else 0)
            (fun k _ ↦ by split_ifs with h; exact h.1.le; exact le_rfl)
            (Finset.mem_univ k₀)
          have hval : (if 0 < rayL1Norm (b k₀) C ∧ rayDir (b k₀) C = v ∧ (fun _ ↦ True) k₀
              then rayL1Norm (b k₀) C else 0) = rayL1Norm (b k₀) C := by
            simp [hk₀_pos, hk₀_dir]
          rw [hval] at hle
          refine hle.trans (le_of_eq (Finset.sum_congr rfl fun k _ ↦ ?_))
          split_ifs <;> rfl
        have htot_ne : rayDirMass b C v (fun _ ↦ True) ≠ 0 := htot_pos.ne'
        have hmul := congrArg (· * (rayDirMass b C v (fun _ ↦ True) * rayDirMass b C v (fun _ ↦ True))) hEq_y
        field_simp [htot_ne] at hmul
        linarith
      · -- `Iv = ∅`: every `rayDirMass` at `v` is `0`!
        have hempty : ∀ k : κ, 0 < rayL1Norm (b k) C → rayDir (b k) C = v → False := fun k h1 h2 ↦
          hIv ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩⟩
        rw [rayDirMass_eq_zero (fun k h1 h2 _ ↦ hempty k h1 h2),
          rayDirMass_eq_zero (fun k h1 h2 _ ↦ hempty k h1 h2),
          rayDirMass_eq_zero (fun k h1 h2 _ ↦ hempty k h1 h2),
          rayDirMass_eq_zero (fun k h1 h2 _ ↦ hempty k h1 h2)]
  · -- Sufficiency (`←`)
    rintro ⟨hI, hII⟩ R hR
    rcases hR.isProd with ⟨Rc, hRc_m, rfl⟩
    let μR := condProbMeasure (rayExponentMeasure b) M (Set.univ.pi Rc)
    have : IsProbabilityMeasure μR := isProbabilityMeasure_condProbMeasure hR.measure_pos hR.measure_ne_top
    rw [condIndepFun_iff _ _ (subProj hA) (subProj hB) (measurable_subProj hA)
      (measurable_subProj hB) μR]
    rintro t1 t2 ⟨EA, hEA_m, rfl⟩ ⟨EB, hEB_m, rfl⟩
    have hceA := condExp_rayExponentMeasure_eq b hb hRc_m hR (hEA_m.prod MeasurableSet.univ)
    have hceB := condExp_rayExponentMeasure_eq b hb hRc_m hR (MeasurableSet.univ.prod hEB_m)
    have hceAB := condExp_rayExponentMeasure_eq b hb hRc_m hR (hEA_m.prod hEB_m)
    let RA : Set (A → ℝ) := Set.univ.pi fun a : A ↦ Rc ⟨a.1, hA a.2⟩
    let RB : Set (B → ℝ) := Set.univ.pi fun b' : B ↦ Rc ⟨b'.1, hB b'.2⟩
    let ΛM : Measure (M → ℝ) := (rayExponentMeasure b).map (coordProj M)
    let Rset : Set (M → ℝ) := Set.univ.pi Rc
    -- Check that at `yC = 0`, the constant `c₀(EA × EB) = c₀(EA × univ) * c₀(univ × EB)` (from Condition I + `0 ∉ cl(R)`!)
    have hc₀_fac :
        (ΛM (Rset ∩ subProj hC ⁻¹' {0} ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB))).toReal /
          (ΛM (Rset ∩ subProj hC ⁻¹' {0})).toReal =
        ((ΛM (Rset ∩ subProj hC ⁻¹' {0} ∩ subProj hA ⁻¹' EA)).toReal /
          (ΛM (Rset ∩ subProj hC ⁻¹' {0})).toReal) *
        ((ΛM (Rset ∩ subProj hC ⁻¹' {0} ∩ subProj hB ⁻¹' EB)).toReal /
          (ΛM (Rset ∩ subProj hC ⁻¹' {0})).toReal) := by
      have hfin0 : ΛM (Rset ∩ subProj hC ⁻¹' {0}) ≠ ∞ :=
        ne_top_of_le_ne_top hR.measure_ne_top (measure_mono inter_subset_left)
      by_cases h0R : ΛM (Rset ∩ subProj hC ⁻¹' {0}) = 0
      · have h0A : ΛM (Rset ∩ subProj hC ⁻¹' {0} ∩ subProj hA ⁻¹' EA) = 0 :=
          measure_mono_null inter_subset_left h0R
        have h0B : ΛM (Rset ∩ subProj hC ⁻¹' {0} ∩ subProj hB ⁻¹' EB) = 0 :=
          measure_mono_null inter_subset_left h0R
        have h0AB : ΛM (Rset ∩ subProj hC ⁻¹' {0} ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB)) = 0 :=
          measure_mono_null inter_subset_left h0R
        simp [h0R, h0A, h0B, h0AB]
      · -- Since `ΛM (Rset ∩ {yC = 0}) > 0`, we must have `0 ∈ closure (RC)`.
        -- Since `0_M ∉ closure Rset = closure RA × closure RB × closure RC`, either `0_A ∉ RA` or `0_B ∉ RB`!
        have h0C_mem : (0 : C → ℝ) ∈ Set.univ.pi fun c : C ↦ Rc ⟨c.1, hC c.2⟩ := by
          by_contra hnot
          have hzero : ΛM (Rset ∩ subProj hC ⁻¹' {0}) = 0 := by
            have hempty : Rset ∩ subProj hC ⁻¹' {0} = ∅ := by
              ext y; simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
                iff_false, not_and]
              intro hyR hyC
              exact hnot (hyC ▸ (mem_pi_iff_subProj y).1 hyR |>.2.2)
            rw [hempty, measure_empty]
          exact h0R hzero
        have h0_either : (0 : A → ℝ) ∉ RA ∨ (0 : B → ℝ) ∉ RB := by
          by_contra hboth
          push Not at hboth
          have h0in : (0 : M → ℝ) ∈ Rset := by
            rw [mem_pi_iff_subProj]
            exact ⟨hboth.1, hboth.2, h0C_mem⟩
          exact hR.zero_notMem_closure (subset_closure h0in)
        -- On `Rset ∩ {yC = 0}`, every ray entering it has `b k c = 0` for all `c ∈ C`;
        -- if `0_A ∉ RA` then `subProj hB = 0` a.e. on `Rset ∩ {yC = 0}`, else `subProj hA = 0` a.e.!
        have hpos0 : 0 < (ΛM (Rset ∩ subProj hC ⁻¹' {0})).toReal :=
          ENNReal.toReal_pos h0R hfin0
        have hconst_zero_B (h0A : (0 : A → ℝ) ∉ RA) :
            ∀ᵐ y ∂(ΛM.restrict (Rset ∩ subProj hC ⁻¹' {0})), subProj hB y = 0 := by
          rw [show ΛM = (rayExponentMeasure b).map (coordProj M) from rfl,
            rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
            restrict_finsetSum, ae_finsetSum_measure_iff]
          intro k _
          have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k i) :=
            Measurable.of_eval fun i ↦ measurable_id.mul_const (b k i)
          rw [Measure.map_map (measurable_coordProj M) hray,
            ae_restrict_iff' ((MeasurableSet.univ_pi hRc_m).inter ((measurable_subProj hC) (measurableSet_singleton 0)))]
          have hmeas_imp : MeasurableSet {y : M → ℝ | y ∈ Rset ∩ subProj hC ⁻¹' {0} → subProj hB y = 0} := by
            simp_rw [imp_iff_not_or]
            exact ((MeasurableSet.univ_pi hRc_m).inter ((measurable_subProj hC) (measurableSet_singleton 0))).compl.union
              (measurableSet_eq_fun (measurable_subProj hB) measurable_const)
          rw [ae_map_iff ((measurable_coordProj M).comp hray).aemeasurable hmeas_imp]
          filter_upwards [ae_pos_radialMeasure_one] with r hr ⟨hrR, hrC⟩
          have hkC : ∀ c ∈ C, b k c = 0 := by
            intro c hc
            have hval := congrFun hrC ⟨c, hc⟩
            simp only [Function.comp_apply, subProj, coordProj, Pi.zero_apply] at hval
            exact (mul_eq_zero.1 hval).resolve_left hr.ne'
          rcases hI k hkC with hkA | hkB
          · exfalso
            have hA0 : subProj hA ((coordProj M ∘ fun r i ↦ r * b k i) r) = 0 := by
              funext a; simp [subProj, coordProj, hkA a.1 a.2]
            exact h0A (hA0 ▸ (mem_pi_iff_subProj _).1 hrR |>.1)
          · funext b'; simp [subProj, coordProj, hkB b'.1 b'.2]
        have hconst_zero_A (h0B : (0 : B → ℝ) ∉ RB) :
            ∀ᵐ y ∂(ΛM.restrict (Rset ∩ subProj hC ⁻¹' {0})), subProj hA y = 0 := by
          rw [show ΛM = (rayExponentMeasure b).map (coordProj M) from rfl,
            rayExponentMeasure, map_finset_sum_measure (measurable_coordProj M),
            restrict_finsetSum, ae_finsetSum_measure_iff]
          intro k _
          have hray : Measurable (fun r : ℝ ↦ fun i : V ↦ r * b k i) :=
            Measurable.of_eval fun i ↦ measurable_id.mul_const (b k i)
          rw [Measure.map_map (measurable_coordProj M) hray,
            ae_restrict_iff' ((MeasurableSet.univ_pi hRc_m).inter ((measurable_subProj hC) (measurableSet_singleton 0)))]
          have hmeas_imp : MeasurableSet {y : M → ℝ | y ∈ Rset ∩ subProj hC ⁻¹' {0} → subProj hA y = 0} := by
            simp_rw [imp_iff_not_or]
            exact ((MeasurableSet.univ_pi hRc_m).inter ((measurable_subProj hC) (measurableSet_singleton 0))).compl.union
              (measurableSet_eq_fun (measurable_subProj hA) measurable_const)
          rw [ae_map_iff ((measurable_coordProj M).comp hray).aemeasurable hmeas_imp]
          filter_upwards [ae_pos_radialMeasure_one] with r hr ⟨hrR, hrC⟩
          have hkC : ∀ c ∈ C, b k c = 0 := by
            intro c hc
            have hval := congrFun hrC ⟨c, hc⟩
            simp only [Function.comp_apply, subProj, coordProj, Pi.zero_apply] at hval
            exact (mul_eq_zero.1 hval).resolve_left hr.ne'
          rcases hI k hkC with hkA | hkB
          · funext a; simp [subProj, coordProj, hkA a.1 a.2]
          · exfalso
            have hB0 : subProj hB ((coordProj M ∘ fun r i ↦ r * b k i) r) = 0 := by
              funext b'; simp [subProj, coordProj, hkB b'.1 b'.2]
            exact h0B (hB0 ▸ (mem_pi_iff_subProj _).1 hrR |>.2.1)
        let S0 : Set (M → ℝ) := Rset ∩ subProj hC ⁻¹' {0}
        rcases h0_either with h0A | h0B
        · have haeB := hconst_zero_B h0A
          by_cases h0EB : (0 : B → ℝ) ∈ EB
          · have hB_full : ΛM (S0 ∩ subProj hB ⁻¹' EB) = ΛM S0 := by
              rw [inter_comm, ← Measure.restrict_apply ((measurable_subProj hB) hEB_m)]
              have heq : subProj hB ⁻¹' EB =ᵐ[ΛM.restrict S0] (univ : Set (M → ℝ)) :=
                Filter.eventuallyEqSet_iff.2 (haeB.mono fun y hy ↦ by simp only [mem_preimage, hy, h0EB, mem_univ])
              rw [measure_congr heq, Measure.restrict_apply_univ]
            have hAB_eq : ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB)) = ΛM (S0 ∩ subProj hA ⁻¹' EA) := by
              have h1 : (ΛM.restrict S0) (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB) =
                  ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB)) := by
                rw [Measure.restrict_apply (((measurable_subProj hA) hEA_m).inter ((measurable_subProj hB) hEB_m)),
                  inter_comm]
              have h2 : (ΛM.restrict S0) (subProj hA ⁻¹' EA) = ΛM (S0 ∩ subProj hA ⁻¹' EA) := by
                rw [Measure.restrict_apply ((measurable_subProj hA) hEA_m), inter_comm]
              rw [← h1, ← h2]
              refine measure_congr (Filter.eventuallyEqSet_iff.2 (haeB.mono fun y hy ↦ ?_))
              exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by simpa [hy] using h0EB⟩⟩
            change (ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB))).toReal / (ΛM S0).toReal =
              ((ΛM (S0 ∩ subProj hA ⁻¹' EA)).toReal / (ΛM S0).toReal) *
              ((ΛM (S0 ∩ subProj hB ⁻¹' EB)).toReal / (ΛM S0).toReal)
            rw [hB_full, hAB_eq, div_self hpos0.ne', mul_one]
          · have hB_null : ΛM (S0 ∩ subProj hB ⁻¹' EB) = 0 := by
              rw [inter_comm, ← Measure.restrict_apply ((measurable_subProj hB) hEB_m)]
              have heq : subProj hB ⁻¹' EB =ᵐ[ΛM.restrict S0] (∅ : Set (M → ℝ)) :=
                Filter.eventuallyEqSet_iff.2 (haeB.mono fun y hy ↦ by simp only [mem_preimage, hy, h0EB, mem_empty_iff_false])
              rw [measure_congr heq, measure_empty]
            have hAB_null : ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB)) = 0 :=
              measure_mono_null (fun y hy ↦ (⟨hy.1, hy.2.2⟩ : y ∈ S0 ∩ subProj hB ⁻¹' EB)) hB_null
            change (ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB))).toReal / (ΛM S0).toReal =
              ((ΛM (S0 ∩ subProj hA ⁻¹' EA)).toReal / (ΛM S0).toReal) *
              ((ΛM (S0 ∩ subProj hB ⁻¹' EB)).toReal / (ΛM S0).toReal)
            simp [hB_null, hAB_null]
        · have haeA := hconst_zero_A h0B
          by_cases h0EA : (0 : A → ℝ) ∈ EA
          · have hA_full : ΛM (S0 ∩ subProj hA ⁻¹' EA) = ΛM S0 := by
              rw [inter_comm, ← Measure.restrict_apply ((measurable_subProj hA) hEA_m)]
              have heq : subProj hA ⁻¹' EA =ᵐ[ΛM.restrict S0] (univ : Set (M → ℝ)) :=
                Filter.eventuallyEqSet_iff.2 (haeA.mono fun y hy ↦ by simp only [mem_preimage, hy, h0EA, mem_univ])
              rw [measure_congr heq, Measure.restrict_apply_univ]
            have hAB_eq : ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB)) = ΛM (S0 ∩ subProj hB ⁻¹' EB) := by
              have h1 : (ΛM.restrict S0) (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB) =
                  ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB)) := by
                rw [Measure.restrict_apply (((measurable_subProj hA) hEA_m).inter ((measurable_subProj hB) hEB_m)),
                  inter_comm]
              have h2 : (ΛM.restrict S0) (subProj hB ⁻¹' EB) = ΛM (S0 ∩ subProj hB ⁻¹' EB) := by
                rw [Measure.restrict_apply ((measurable_subProj hB) hEB_m), inter_comm]
              rw [← h1, ← h2]
              refine measure_congr (Filter.eventuallyEqSet_iff.2 (haeA.mono fun y hy ↦ ?_))
              exact ⟨fun h ↦ h.2, fun h ↦ ⟨by simpa [hy] using h0EA, h⟩⟩
            change (ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB))).toReal / (ΛM S0).toReal =
              ((ΛM (S0 ∩ subProj hA ⁻¹' EA)).toReal / (ΛM S0).toReal) *
              ((ΛM (S0 ∩ subProj hB ⁻¹' EB)).toReal / (ΛM S0).toReal)
            rw [hA_full, hAB_eq, div_self hpos0.ne', one_mul]
          · have hA_null : ΛM (S0 ∩ subProj hA ⁻¹' EA) = 0 := by
              rw [inter_comm, ← Measure.restrict_apply ((measurable_subProj hA) hEA_m)]
              have heq : subProj hA ⁻¹' EA =ᵐ[ΛM.restrict S0] (∅ : Set (M → ℝ)) :=
                Filter.eventuallyEqSet_iff.2 (haeA.mono fun y hy ↦ by simp only [mem_preimage, hy, h0EA, mem_empty_iff_false])
              rw [measure_congr heq, measure_empty]
            have hAB_null : ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB)) = 0 :=
              measure_mono_null (fun y hy ↦ (⟨hy.1, hy.2.1⟩ : y ∈ S0 ∩ subProj hA ⁻¹' EA)) hA_null
            change (ΛM (S0 ∩ (subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB))).toReal / (ΛM S0).toReal =
              ((ΛM (S0 ∩ subProj hA ⁻¹' EA)).toReal / (ΛM S0).toReal) *
              ((ΛM (S0 ∩ subProj hB ⁻¹' EB)).toReal / (ΛM S0).toReal)
            simp [hA_null, hAB_null]
    -- Now combine `hceA`, `hceB`, `hceAB` and check pointwise factorization of `rayCondProb`!
    filter_upwards [hceA, hceB, hceAB] with y h1 h2 h12
    have hpreA : (fun y : M → ℝ ↦ (subProj hA y, subProj hB y)) ⁻¹' (EA ×ˢ univ) =
        subProj hA ⁻¹' EA := by ext z; simp
    have hpreB : (fun y : M → ℝ ↦ (subProj hA y, subProj hB y)) ⁻¹' (univ ×ˢ EB) =
        subProj hB ⁻¹' EB := by ext z; simp
    have hpreAB : (fun y : M → ℝ ↦ (subProj hA y, subProj hB y)) ⁻¹' (EA ×ˢ EB) =
        subProj hA ⁻¹' EA ∩ subProj hB ⁻¹' EB := by ext z; simp
    rw [hpreA] at h1; rw [hpreB] at h2; rw [hpreAB] at h12
    rw [← h12, Pi.mul_apply, ← h1, ← h2]
    set yC := subProj hC y
    by_cases hyC : yC = 0
    · simp only [rayCondProb, hyC, ↓reduceIte]
      simpa only [hpreA, hpreB, hpreAB] using hc₀_fac
    · -- Non-zero `yC`: let `t = ∑ c, yC c`, `v = t⁻¹ • yC`, and apply `rayDirMass_prod_of_rayCICondition`!
      simp only [rayCondProb, hyC, ↓reduceIte]
      set t : ℝ := ∑ c : C, yC c
      by_cases ht : 0 < t
      · let v : C → ℝ := t⁻¹ • yC
        let SA_R : Set (A → ℝ) := {x | t • x ∈ RA}
        let SB_R : Set (B → ℝ) := {x | t • x ∈ RB}
        let SA_E : Set (A → ℝ) := {x | t • x ∈ RA ∩ EA}
        let SB_E : Set (B → ℝ) := {x | t • x ∈ RB ∩ EB}
        have hdir_iff (k : κ) : yC = t • rayDir (b k) C ↔ rayDir (b k) C = v := by
          constructor
          · intro h; simp only [v, h, inv_smul_smul₀ ht.ne']
          · intro h; simp only [h, v, smul_inv_smul₀ ht.ne']
        have halg : ∀ (nAB nA nB dAB dA dB : ℝ),
            nAB = rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_E) →
            nA = rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_R) →
            nB = rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_E) →
            dAB = rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) →
            dA = rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) →
            dB = rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) →
            nAB / dAB = (nA / dA) * (nB / dB) := by
          rintro _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
          set T := rayDirMass b C v (fun _ ↦ True)
          have hfac_R := rayDirMass_prod_of_rayCICondition hII v SA_R SB_R
          have hfac_A := rayDirMass_prod_of_rayCICondition hII v SA_E SB_R
          have hfac_B := rayDirMass_prod_of_rayCICondition hII v SA_R SB_E
          have hfac_AB := rayDirMass_prod_of_rayCICondition hII v SA_E SB_E
          by_cases hD0 : rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) = 0
          · simp [hD0]
          · have hT0 : T ≠ 0 := by
              intro h0
              have hle : rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) ≤ T := by
                unfold rayDirMass T
                refine Finset.sum_le_sum fun k _ ↦ by
                  split_ifs with hca hcb hcb
                  · exact le_rfl
                  · exfalso; exact hcb ⟨hca.1, hca.2.1, trivial⟩
                  · exact hcb.1.le
                  · exact le_rfl
              have hnn : 0 ≤ rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) :=
                Finset.sum_nonneg fun k _ ↦ by split_ifs with h; exact h.1.le; exact le_rfl
              exact hD0 (le_antisymm (h0 ▸ hle) hnn)
            have h1 : rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_E) *
                rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) * (T * T) =
                rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_R) *
                rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_E) * (T * T) := by
              calc _ = (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_E) * T) *
                       (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) * T) := by ring
                _ = (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E) *
                     rayDirMass b C v (fun k ↦ rayScaled (b k) C B ∈ SB_E)) *
                    (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R) *
                     rayDirMass b C v (fun k ↦ rayScaled (b k) C B ∈ SB_R)) := by rw [hfac_AB, hfac_R]
                _ = (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E) *
                     rayDirMass b C v (fun k ↦ rayScaled (b k) C B ∈ SB_R)) *
                    (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R) *
                     rayDirMass b C v (fun k ↦ rayScaled (b k) C B ∈ SB_E)) := by ring
                _ = (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_R) * T) *
                    (rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_E) * T) := by
                    rw [hfac_A, hfac_B]
                _ = _ := by ring
            have h2 : rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_E) *
                rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_R) =
                rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_E ∧ rayScaled (b k) C B ∈ SB_R) *
                rayDirMass b C v (fun k ↦ rayScaled (b k) C A ∈ SA_R ∧ rayScaled (b k) C B ∈ SB_E) :=
              mul_right_cancel₀ (mul_ne_zero hT0 hT0) h1
            field_simp [hD0]
            linarith
        apply halg
        · unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          split_ifs with ha hb hb
          · rfl
          · exfalso; exact hb ⟨ha.1, (hdir_iff k).1 ha.2.2.1, ⟨ha.2.2.2.1, ha.2.2.2.2.2.1⟩, ⟨ha.2.2.2.2.1, ha.2.2.2.2.2.2⟩⟩
          · exfalso; exact ha ⟨hb.1, ht, (hdir_iff k).2 hb.2.1, hb.2.2.1.1, hb.2.2.2.1, hb.2.2.1.2, hb.2.2.2.2⟩
          · rfl
        · unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          split_ifs with ha hb hb
          · rfl
          · exfalso; exact hb ⟨ha.1, (hdir_iff k).1 ha.2.2.1, ⟨ha.2.2.2.1, ha.2.2.2.2.2.1⟩, ha.2.2.2.2.1⟩
          · exfalso; exact ha ⟨hb.1, ht, (hdir_iff k).2 hb.2.1, hb.2.2.1.1, hb.2.2.2, hb.2.2.1.2, mem_univ _⟩
          · rfl
        · unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          split_ifs with ha hb hb
          · rfl
          · exfalso; exact hb ⟨ha.1, (hdir_iff k).1 ha.2.2.1, ha.2.2.2.1, ⟨ha.2.2.2.2.1, ha.2.2.2.2.2.2⟩⟩
          · exfalso; exact ha ⟨hb.1, ht, (hdir_iff k).2 hb.2.1, hb.2.2.1, hb.2.2.2.1, mem_univ _, hb.2.2.2.2⟩
          · rfl
        · unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          split_ifs with ha hb hb
          · rfl
          · exfalso; exact hb ⟨ha.1, (hdir_iff k).1 ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
          · exfalso; exact ha ⟨hb.1, ht, (hdir_iff k).2 hb.2.1, hb.2.2.1, hb.2.2.2⟩
          · rfl
        · unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          split_ifs with ha hb hb
          · rfl
          · exfalso; exact hb ⟨ha.1, (hdir_iff k).1 ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
          · exfalso; exact ha ⟨hb.1, ht, (hdir_iff k).2 hb.2.1, hb.2.2.1, hb.2.2.2⟩
          · rfl
        · unfold rayDirMass
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          split_ifs with ha hb hb
          · rfl
          · exfalso; exact hb ⟨ha.1, (hdir_iff k).1 ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
          · exfalso; exact ha ⟨hb.1, ht, (hdir_iff k).2 hb.2.1, hb.2.2.1, hb.2.2.2⟩
          · rfl
      · -- `¬ 0 < t`: all sums vanish, `0 / 0 = (0 / 0) * (0 / 0)`!
        simp only [ht, false_and, and_false, ↓reduceIte, Finset.sum_const_zero, div_zero, zero_mul]

/-! ### Theorem 2: Graphical Separation Implies Extremal Conditional Independence -/

/-- **Footprint separation implies extremal conditional independence** for every positive recursive
max-linear model on `G`. -/
theorem MaxLinearModel.isFootprintSeparated_imp_extremalCondIndep
    {V : Type*} [Fintype V] [DecidableEq V] {G : DAG V} (M : MaxLinearModel G)
    {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hfp : G.IsFootprintSeparated (A : Set V) (B : Set V) (C : Set V)) :
    ExtremalCondIndep M.exponentMeasure A B C :=
  (extremalCondIndep_rayExponentMeasure_iff (fun k i ↦ M.coeff i k)
    (fun k i ↦ M.coeff_nonneg i k) hAB hAC hBC).2
    (M.isFootprintSeparated_imp_rayCICondition hfp)

/-- **Theorem 2a (Positive resolution of Engelke et al. 2024 for $*$-separation):**
In EVERY finite DAG `G` and for EVERY positive recursive max-linear model `M` on `G`,
$*$-separation implies extremal conditional independence `A ⊥ B | C [Λ_M]`. -/
theorem MaxLinearModel.isStarSeparated_imp_extremalCondIndep
    {V : Type*} [Fintype V] [DecidableEq V] {G : DAG V} (M : MaxLinearModel G)
    {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hstar : G.IsStarSeparated (A : Set V) (B : Set V) (C : Set V)) :
    ExtremalCondIndep M.exponentMeasure A B C :=
  M.isFootprintSeparated_imp_extremalCondIndep hAB hAC hBC
    (G.isStarSeparated_imp_isFootprintSeparated hstar)

/-- **Theorem 2b (Positive resolution of Engelke et al. 2024 for $d$-separation):**
In EVERY finite DAG `G` and for EVERY positive recursive max-linear model `M` on `G`,
$d$-separation implies extremal conditional independence `A ⊥ B | C [Λ_M]`. -/
theorem MaxLinearModel.isDSeparated_imp_extremalCondIndep
    {V : Type*} [Fintype V] [DecidableEq V] {G : DAG V} (M : MaxLinearModel G)
    {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hd : G.IsDSeparated (A : Set V) (B : Set V) (C : Set V)) :
    ExtremalCondIndep M.exponentMeasure A B C :=
  M.isStarSeparated_imp_extremalCondIndep hAB hAC hBC
    (G.isDSeparated_imp_isStarSeparated hd)

end MaxLinearCI

end ExtremeValueTheory
