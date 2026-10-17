/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

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

end CramerWold

end ExtremeValueTheory
