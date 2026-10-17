/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Half-spaces determine homogeneous measures (converse Cramér–Wold, uniqueness part)
-/

open MeasureTheory Filter Topology Set Complex
open scoped ENNReal NNReal

namespace ExtremeValueTheory

namespace CramerWold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ ν : Measure E}

omit [MeasurableSpace E] [BorelSpace E] in
theorem setOf_lt_apply_eq {s : ℝ} (hs : 0 < s) (M : StrongDual ℝ E) :
    {y : E | s < M y} = {y | 1 < (s⁻¹ • M) y} := by
  ext y
  simp only [mem_ofPred_eq, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [lt_inv_mul_iff₀ hs, mul_one]

/-- If `μ` and `ν` agree (with finite values) on all half-spaces `{L > 1}`, the images of `μ` and
`ν` under any continuous linear functional agree on `(0, ∞)`. -/
theorem map_restrict_Ioi_eq (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) (M : StrongDual ℝ E) :
    (μ.map M).restrict (Ioi 0) = (ν.map M).restrict (Ioi 0) := by
  have hIoi : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1)) := by
    ext s
    simp only [mem_Ioi, mem_iUnion]
    refine ⟨fun hs => ?_, fun ⟨n, hn⟩ => lt_trans (by positivity) hn⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
    exact ⟨n, hn⟩
  have hval : ∀ (ρ : Measure E) {s : ℝ}, 0 < s → (ρ.map M) (Ioi s) = ρ {y | 1 < (s⁻¹ • M) y} :=
    fun ρ s hs => by
      rw [Measure.map_apply M.measurable measurableSet_Ioi, ← setOf_lt_apply_eq hs]; rfl
  rw [hIoi, Measure.restrict_iUnion_congr]
  intro n
  set c : ℝ := 1 / ((n : ℝ) + 1)
  have hc : 0 < c := by positivity
  have hval' : ∀ (ρ : Measure E) (a : ℝ), ((ρ.map M).restrict (Ioi c)) (Ioi a) =
      ρ {y | 1 < ((max a c)⁻¹ • M) y} := fun ρ a => by
    rw [Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi, hval ρ (lt_max_of_lt_right hc)]
  have : IsFiniteMeasure ((μ.map M).restrict (Ioi c)) :=
    ⟨by rw [Measure.restrict_apply_univ, hval μ hc]; exact hfin _⟩
  have : IsFiniteMeasure ((ν.map M).restrict (Ioi c)) :=
    ⟨by rw [Measure.restrict_apply_univ, hval ν hc, ← h]; exact hfin _⟩
  refine measure_ext_of_Ioi ?_ fun a => by rw [hval', hval', h]
  rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, hval μ hc, hval ν hc, h]

/-- Integrals over a half-space `{M > 0}` of functions of `M y` agree. -/
theorem setIntegral_pos_eq (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) (M : StrongDual ℝ E)
    {G : ℝ → ℂ} (hG : Measurable G) :
    ∫ y in {y | 0 < M y}, G (M y) ∂μ = ∫ y in {y | 0 < M y}, G (M y) ∂ν := by
  have h1 : ∀ ρ : Measure E, ∫ y in {y | 0 < M y}, G (M y) ∂ρ = ∫ s in Ioi 0, G s ∂(ρ.map M) :=
    fun ρ => (setIntegral_map measurableSet_Ioi hG.aestronglyMeasurable
      M.measurable.aemeasurable).symm
  rw [h1, h1, map_restrict_Ioi_eq hfin h M]

/-- **Integrals of functions of linear functionals agree**: if `μ` and `ν` agree on all
half-spaces `{L > 1}`, then `∫ G (M y) dμ = ∫ G (M y) dν` for every continuous linear `M` and
every measurable `G` with `G 0 = 0` such that `G ∘ M` is integrable for both measures. -/
theorem integral_comp_eq (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) (M : StrongDual ℝ E)
    {G : ℝ → ℂ} (hG : Measurable G) (hG0 : G 0 = 0)
    (hμ : Integrable (fun y => G (M y)) μ) (hν : Integrable (fun y => G (M y)) ν) :
    ∫ y, G (M y) ∂μ = ∫ y, G (M y) ∂ν := by
  have key : ∀ ρ : Measure E, Integrable (fun y => G (M y)) ρ → ∫ y, G (M y) ∂ρ =
      ∫ y in {y | 0 < M y}, G (M y) ∂ρ +
        ∫ y in {y | 0 < (-M) y}, (fun s => G (-s)) ((-M) y) ∂ρ := fun ρ hρ => by
    have hm : MeasurableSet {y : E | 0 < M y} := measurableSet_lt measurable_const M.measurable
    rw [← integral_add_compl hm hρ]
    congr 1
    have hsub : {y : E | 0 < (-M) y} ⊆ {y | 0 < M y}ᶜ := fun y hy => by
      simp only [neg_apply, mem_ofPred_eq, Left.neg_pos_iff] at hy
      simp only [mem_compl_iff, mem_ofPred_eq, not_lt]; exact hy.le
    simp only [neg_apply, neg_neg]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hm.compl hsub ?_
    intro y ⟨hy1, hy2⟩
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt, Left.neg_pos_iff] at hy1 hy2
    rw [le_antisymm hy1 hy2, hG0]
  rw [key μ hμ, key ν hν, setIntegral_pos_eq hfin h M hG,
    setIntegral_pos_eq hfin h (-M) (G := fun s => G (-s)) (hG.comp measurable_neg)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] in
/-- If `f μ = f ν` for a finite measurable density `f`, then `μ` and `ν` agree on `{f ≠ 0}`. -/
theorem restrict_ne_zero_eq_of_withDensity_eq {f : E → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∀ y, f y ≠ ∞) (h : μ.withDensity f = ν.withDensity f) :
    μ.restrict {y | f y ≠ 0} = ν.restrict {y | f y ≠ 0} := by
  have hset : MeasurableSet {y | f y ≠ 0} := (hf (measurableSet_singleton 0)).compl
  have key : ∀ ρ : Measure E, ρ.restrict {y | f y ≠ 0} = (ρ.withDensity f).withDensity f⁻¹ :=
    fun ρ => by
      rw [← withDensity_mul ρ hf hf.inv, ← withDensity_indicator_one hset]
      congr 1
      funext y
      by_cases hy : f y = 0
      · simp [hy]
      · simp [hy, ENNReal.mul_inv_cancel hy (hfin y)]
  rw [key, key, h]

omit [MeasurableSpace E] [BorelSpace E] in
theorem cos_ne_one_or_cos_sqrt_two_ne_one {t : ℝ} (ht : t ≠ 0) :
    Real.cos t ≠ 1 ∨ Real.cos (√2 * t) ≠ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff t).1 hc.1
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).1 hc.2
  have hn0 : (n : ℝ) ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hn; exact ht hn.symm
  refine irrational_sqrt_two.ne_rational m n ?_
  rw [eq_div_iff hn0]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpi
  rw [mul_assoc, hn, hm]

variable [FiniteDimensional ℝ E]

/-- The coordinate functionals of a basis and their `√2`-multiples. -/
noncomputable def coordFamily (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : Fin (Module.finrank ℝ E) × Bool) : StrongDual ℝ E :=
  (if p.2 then √2 else 1) • LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord p.1)

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_coordFamily_cos_ne_one {y : E} (hy : y ≠ 0) :
    ∃ p, Real.cos (coordFamily E p y) ≠ 1 := by
  set b := Module.finBasis ℝ E
  have : b.repr y ≠ 0 := by
    rwa [Ne, LinearEquiv.map_eq_zero_iff]
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 this
  have hc : ∀ q : Bool, coordFamily E (i, q) y = (if q then √2 else 1) * b.repr y i := fun q => by
    simp only [coordFamily, b]
    split_ifs <;> simp [Module.Basis.coord_apply]
  rcases cos_ne_one_or_cos_sqrt_two_ne_one hi with h1 | h2
  · exact ⟨(i, false), by rw [hc]; simpa using h1⟩
  · exact ⟨(i, true), by rw [hc]; simpa using h2⟩

/-- **Half-spaces determine a measure** (abstract form). Let `g : ℝ → ℂ` be measurable with
`g 0 = 0` and `e^{ia} (1 - cos b) = g a - g (a + b) / 2 - g (a - b) / 2`, and suppose
`g ∘ M` is integrable for `μ` and `ν` for every continuous linear `M`. If `μ` and `ν` have no
atom at the origin and agree (with finite values) on all half-spaces `{L > 1}`, then `μ = ν`.

The proof: the integrals `∫ g (M y)` agree (`integral_comp_eq`), hence the characteristic
functions of the finite measures `(1 - cos (v y)) μ(dy)` and `(1 - cos (v y)) ν(dy)` agree, so
these measures are equal; `μ` and `ν` therefore agree on `{cos (v y) ≠ 1}` for every `v`, and
finitely many such sets cover `E \ {0}`. -/
theorem ext_of_halfSpace {g : ℝ → ℂ} (hgm : Measurable g) (hg0 : g 0 = 0)
    (hid : ∀ a b : ℝ, cexp (a * I) * ((1 - Real.cos b : ℝ) : ℂ) =
      g a - g (a + b) / 2 - g (a - b) / 2)
    (hμg : ∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) μ)
    (hνg : ∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ν)
    (hμ0 : μ {0} = 0) (hν0 : ν {0} = 0)
    (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) : μ = ν := by
  let w : StrongDual ℝ E → E → ℝ≥0 := fun v y => Real.toNNReal (1 - Real.cos (v y))
  have hw_meas : ∀ v, Measurable (w v) := fun v =>
    (continuous_real_toNNReal.comp (continuous_const.sub
      (Real.continuous_cos.comp v.continuous))).measurable
  have hcos : ∀ b : ℝ, ((1 - Real.cos b : ℝ) : ℂ) = -(g b / 2) - g (-b) / 2 := fun b => by
    have := hid 0 b
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, one_mul, zero_add, zero_sub, hg0] at this
    rw [this]
  have hcos_int : ∀ ρ : Measure E, (∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ρ) →
      ∀ v : StrongDual ℝ E, Integrable (fun y => 1 - Real.cos (v y)) ρ := fun ρ hρ v => by
    have hC : Integrable (fun y => -(g (v y) / 2) - g ((-v) y) / 2) ρ :=
      ((hρ v).div_const 2).neg.sub ((hρ (-v)).div_const 2)
    refine (hC.re).congr (Eventually.of_forall fun y => ?_)
    simp only [neg_apply]
    rw [← hcos]; simp [Complex.cos_ofReal_re]
  have hfinite : ∀ ρ : Measure E, (∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ρ) →
      ∀ v, IsFiniteMeasure (ρ.withDensity fun y => (w v y : ℝ≥0∞)) := fun ρ hρ v =>
    isFiniteMeasure_withDensity_ofReal (hcos_int ρ hρ v).2
  have hchar : ∀ ρ : Measure E, ∀ v L : StrongDual ℝ E,
      charFunDual (ρ.withDensity fun y => (w v y : ℝ≥0∞)) L =
        ∫ y, (g (L y) - g ((L + v) y) / 2 - g ((L - v) y) / 2) ∂ρ := fun ρ v L => by
    rw [charFunDual_apply, integral_withDensity_eq_integral_smul (hw_meas v)]
    congr 1
    funext y
    have hnn : 0 ≤ 1 - Real.cos (v y) := sub_nonneg.2 (Real.cos_le_one _)
    simp only [w, add_apply, sub_apply]
    rw [NNReal.smul_def, Real.coe_toNNReal _ hnn, Complex.real_smul, mul_comm, hid]
  have hint_eq : ∀ v L : StrongDual ℝ E,
      ∫ y, (g (L y) - g ((L + v) y) / 2 - g ((L - v) y) / 2) ∂μ =
        ∫ y, (g (L y) - g ((L + v) y) / 2 - g ((L - v) y) / 2) ∂ν := fun v L => by
    have hI : ∀ ρ : Measure E, (∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ρ) →
        ∫ y, (g (L y) - g ((L + v) y) / 2 - g ((L - v) y) / 2) ∂ρ =
          ∫ y, g (L y) ∂ρ - (∫ y, g ((L + v) y) ∂ρ) / 2 - (∫ y, g ((L - v) y) ∂ρ) / 2 :=
      fun ρ hρ => by
        rw [integral_sub (f := fun y => g (L y) - g ((L + v) y) / 2)
          (g := fun y => g ((L - v) y) / 2) ((hρ L).sub ((hρ _).div_const 2))
          ((hρ _).div_const 2), integral_sub (f := fun y => g (L y))
          (g := fun y => g ((L + v) y) / 2) (hρ L) ((hρ _).div_const 2), integral_div,
          integral_div]
    rw [hI μ hμg, hI ν hνg]
    simp only [fun M => integral_comp_eq hfin h M hgm hg0 (hμg M) (hνg M)]
  have hdens : ∀ v : StrongDual ℝ E, μ.restrict {y | (w v y : ℝ≥0∞) ≠ 0} =
      ν.restrict {y | (w v y : ℝ≥0∞) ≠ 0} := fun v => by
    have := hfinite μ hμg v
    have := hfinite ν hνg v
    refine restrict_ne_zero_eq_of_withDensity_eq (hw_meas v).coe_nnreal_ennreal
      (fun y => ENNReal.coe_ne_top) (Measure.ext_of_charFunDual (funext fun L => ?_))
    rw [hchar, hchar, hint_eq]
  set U : Set E := ⋃ p, {y | (w (coordFamily E p) y : ℝ≥0∞) ≠ 0}
  have hU : Uᶜ ⊆ {0} := fun y hy => by
    by_contra hy0
    obtain ⟨p, hp⟩ := exists_coordFamily_cos_ne_one hy0
    simp only [U, mem_compl_iff, mem_iUnion, not_exists, mem_ofPred_eq, not_not,
      ENNReal.coe_eq_zero, w, Real.toNNReal_eq_zero, tsub_le_iff_right] at hy
    exact hp (le_antisymm (Real.cos_le_one _) (by linarith [hy p]))
  have hself : ∀ ρ : Measure E, ρ {0} = 0 → ρ.restrict U = ρ := fun ρ hρ =>
    Measure.restrict_eq_self_of_ae_mem (measure_mono_null (fun y hy => hU hy) hρ)
  rw [← hself μ hμ0, ← hself ν hν0, Measure.restrict_iUnion_congr]
  exact fun p => hdens _

end CramerWold

end ExtremeValueTheory
