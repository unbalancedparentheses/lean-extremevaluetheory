/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
Modified by Federico Carrone, 2026, from kkytola/ExtremeValueProject (commit f7c9a8ce260d):
ported to Lean/Mathlib v4.35.0 and renamed `ExtremeValueProject` to `ExtremeValueTheory`.
-/
import ExtremeValueTheory.CumulativeDistributionFunction
import ExtremeValueTheory.AffineTransformation
import Mathlib

section weak_convergence_cdf

open Filter Topology NNReal ENNReal Set

/-- The continuity points of a c.d.f. form a dense set. -/
lemma CumulativeDistributionFunction.dense_setOf_continuousAt
    (F : CumulativeDistributionFunction) : Dense {x | ContinuousAt F x} := by
  simpa [compl] using Set.Countable.dense_compl (𝕜 := ℝ) (Monotone.countable_not_continuousAt F.mono')

/-- Lemma 4.3 (cdf-tight) in blueprint. -/
lemma CumulativeDistributionFunction.forall_pos_exists_lt_gt_continuousAt
    (F : CumulativeDistributionFunction) {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (a b : ℝ), a < b ∧ F a < ε ∧ 1 - ε < F b ∧ ContinuousAt F a ∧ ContinuousAt F b := by
  obtain ⟨x', hx'⟩ := (F.tendsto_atBot.eventually (eventually_lt_nhds ε_pos)).exists
  obtain ⟨y', hy'⟩ :=
    (F.tendsto_atTop.eventually (eventually_gt_nhds (show 1 - ε < 1 by linarith))).exists
  obtain ⟨a, ha_cont, ha⟩ := F.dense_setOf_continuousAt.exists_between (show x' - 1 < x' by linarith)
  obtain ⟨b, hb_cont, hb⟩ := F.dense_setOf_continuousAt.exists_between
    (show max a y' < max a y' + 1 by linarith)
  refine ⟨a, b, ?_, ?_, ?_, ha_cont, hb_cont⟩
  · exact (le_max_left a y').trans_lt hb.1
  · exact (F.mono ha.2.le).trans_lt hx'
  · exact lt_of_lt_of_le hy' (F.mono ((le_max_right a y').trans hb.1.le))

/-- Lemma 4.4 (subdivision-dense) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that the consecutive
differences are smaller than a given `δ > 0`. -/
lemma forall_exists_subdivision_diff_lt_of_dense {D : Set ℝ} (D_dense : Dense D)
    {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b) {δ : ℝ} (δ_pos : 0 < δ) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), cs j.succ - cs (Fin.castAdd _ j) < δ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (b - a) / δ)
  have N_pos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have N_pos' : 0 < N := by exact_mod_cast N_pos
  set h := (b - a) / N with h_def
  have h_pos : 0 < h := div_pos (by linarith) N_pos
  have Nh : (N : ℝ) * h = b - a := by rw [h_def]; field_simp
  have two_h : 2 * h < δ := by
    rw [div_lt_iff₀ δ_pos] at hN
    have : 2 * (b - a) < N * δ := by linarith
    nlinarith
  have hg : ∀ j : ℕ, ∃ c ∈ D, a + j * h < c ∧ c < a + j * h + h / 2 :=
    fun j ↦ D_dense.exists_between (by linarith)
  choose g gD g_gt g_lt using hg
  let f : ℕ → ℝ := fun j ↦ if j = 0 then a else if N ≤ j then b else g j
  have f_bounds : ∀ n, n ≤ N → a + n * h ≤ f n ∧ f n ≤ a + n * h + h / 2 := by
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [f]; linarith
    · by_cases hNn : N ≤ n
      · have : n = N := le_antisymm hn hNn
        subst this
        simp only [f, h0, ite_false, le_refl, ite_true]
        constructor <;> linarith
      · simp only [f, h0, hNn, ite_false]
        exact ⟨(g_gt n).le, (g_lt n).le⟩
  refine ⟨N, fun j ↦ f j, ?_, ?_, ?_, ?_, ?_⟩
  · simp [f]
  · simp [f, N_pos'.ne']
  · rw [Fin.monotone_iff_le_succ]
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h1 := f_bounds i (by omega)
    have h2 := f_bounds (i + 1) (by omega)
    push_cast at h2
    linarith [h1.2, h2.1]
  · intro j
    simp only [f]
    split_ifs
    · exact ha
    · exact hb
    · exact gD _
  · intro j
    simp only [Fin.val_succ, Fin.val_castAdd]
    have h1 := f_bounds j (by omega)
    have h2 := f_bounds (j + 1) (by omega)
    push_cast at h2
    linarith [h1.1, h2.2]

/-- Lemma 4.5 (continuous-function-approximation-subdivision) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that for a given
continuous function `f` the function values on the parts of the subdivision are smaller than
a given `ε > 0`. -/
lemma forall_exists_subdivision_dist_apply_lt_of_dense_of_continuous {D : Set ℝ} (D_dense : Dense D)
    {f : ℝ → ℝ} (f_cont : Continuous f) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b)
    {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), ∀ x ∈ Icc (cs (Fin.castAdd _ j)) (cs j.succ),
        ∀ y ∈ Icc (cs (Fin.castAdd _ j)) (cs j.succ), dist (f x) (f y) < ε) := by
  let I : Set ℝ := Icc a b
  have hI_compact : IsCompact I := isCompact_Icc
  have hI_nonempty : I.Nonempty := nonempty_Icc.mpr (le_of_lt a_lt_b)
  have hf_cont_I : ContinuousOn f I := f_cont.continuousOn
  have hf_unif_cont : UniformContinuousOn f I :=
    hI_compact.uniformContinuousOn_of_continuous hf_cont_I
  have h_δ : ∃ δ > 0, ∀ x ∈ I, ∀ y ∈ I, dist x y < δ → dist (f x) (f y) < ε := by
    rw [Metric.uniformContinuousOn_iff] at hf_unif_cont
    exact hf_unif_cont ε ε_pos
  obtain ⟨δ, hδ_pos, hδ⟩ := h_δ
  obtain ⟨k, cs, h_cs_0, h_cs_last, h_cs_mono, h_cs_D, h_cs_diff⟩ :=
    forall_exists_subdivision_diff_lt_of_dense D_dense ha hb a_lt_b hδ_pos
  have h_cs_bound : ∀ i : Fin k, ∀ x ∈ Icc (cs (Fin.castAdd _ i)) (cs i.succ), ∀ y ∈ Icc (cs (Fin.castAdd _ i)) (cs i.succ), dist (f x) (f y) < ε := by
    intro i x hx y hy
    have hx_I : x ∈ I := by
      have h_lower : a ≤ cs (Fin.castAdd _ i) := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hx
    have hy_I : y ∈ I := by
      have h_lower : a ≤ cs (Fin.castAdd _ i) := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hy
    have h_dist_xy : dist x y < δ := by
      have h_bound : dist x y ≤ cs i.succ - cs (Fin.castAdd _ i) := by exact Real.dist_le_of_mem_Icc hx hy
      exact lt_of_le_of_lt h_bound (h_cs_diff i)
    exact hδ x hx_I y hy_I h_dist_xy
  exact ⟨k, cs, h_cs_0, h_cs_last, h_cs_mono, h_cs_D, h_cs_bound⟩

open MeasureTheory in
/-- Preliminary to Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (a_le_b : a ≤ b) (α : E) :
    ∫ x, (indicator (Ioc a b) (fun _ ↦ α)) x ∂ F.measure =
      (F b - F a) • α := by
  simp only [integral_indicator (show MeasurableSet (Ioc a b) from measurableSet_Ioc),
             integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter]
  congr
  simp [Measure.real, F.toStieltjesFunction.measure_Ioc a b,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono a_le_b))]

/-- Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_sum_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {κ : Type*} {s : Finset κ} (as : κ → ℝ) (bs : κ → ℝ) (h : ∀ j, as j ≤ bs j) (α : κ → E) :
    ∫ x, ((∑ j ∈ s, indicator (Ioc (as j) (bs j)) (fun _ ↦ α j)) x) ∂ F.measure =
      ∑ j ∈ s, (F (bs j) - F (as j)) • α j := by
  -- It may be worthwhile to think about an improved phrasing of this.
  -- The previous lemma `CumulativeDistributionFunction.integral_indicator_eq` should be
  -- the key anyway.
  have h_int_sum_change : ∫ (x : ℝ), (∑ j ∈ s, (Ioc (as j) (bs j)).indicator (fun x => α j)) x ∂F.measure  = ∑ j ∈ s, ∫ (x : ℝ), (Ioc (as j) (bs j)).indicator (fun x => α j) x ∂F.measure  := by
    rw [← MeasureTheory.integral_finsetSum]
    simp_all only [Finset.sum_apply]
    intro j _
    exact (MeasureTheory.integrable_const (α j)).indicator measurableSet_Ioc
  rw [h_int_sum_change]
  congr
  ext j
  exact F.integral_indicator_eq (h j) _

open MeasureTheory Topology

/-- Theorem 4.8 (convergence-in-distribution-with-cdf) in blueprint:
Convergence of a sequence of c.d.f.s pointwise at all continuity points of the limit c.d.f. imply
convergence in distribution of the corresponding Borel probability measures on `ℝ`. -/
theorem tendsto_of_forall_continuousAt_tendsto_cdf
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (h : ∀ x, ContinuousAt μ.cdf x → Tendsto (fun n ↦ (μs n).cdf x) atTop (𝓝 (μ.cdf x))) :
    Tendsto μs atTop (𝓝 μ) := by
  -- The measure of `Ioc c d` in terms of the c.d.f.
  have key (ν : ProbabilityMeasure ℝ) {c d : ℝ} (hcd : c ≤ d) :
      (ν (Ioc c d) : ℝ) = ν.cdf d - ν.cdf c := by
    rw [ProbabilityMeasure.cdf_apply_eq, ProbabilityMeasure.cdf_apply_eq]
    have hset : Ioc c d = Iic d \ Iic c := by
      ext y; simp only [mem_Ioc, Set.mem_sdiff, mem_Iic, not_le]; exact and_comm
    change (ν : Measure ℝ).real (Ioc c d) = (ν : Measure ℝ).real (Iic d) - (ν : Measure ℝ).real (Iic c)
    rw [hset, measureReal_sdiff (Iic_subset_Iic.mpr hcd) measurableSet_Iic]
  let S : Set (Set ℝ) :=
    {s | ∃ c d, ContinuousAt μ.cdf c ∧ ContinuousAt μ.cdf d ∧ s = Ioc c d}
  have max_mem {c c' : ℝ} (hc : ContinuousAt μ.cdf c) (hc' : ContinuousAt μ.cdf c') :
      ContinuousAt μ.cdf (max c c') := by
    rcases le_total c c' with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have min_mem {c c' : ℝ} (hc : ContinuousAt μ.cdf c) (hc' : ContinuousAt μ.cdf c') :
      ContinuousAt μ.cdf (min c c') := by
    rcases le_total c c' with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have S_pi : IsPiSystem S := by
    rintro s ⟨c, d, hc, hd, rfl⟩ t ⟨c', d', hc', hd', rfl⟩ _
    exact ⟨max c c', min d d', max_mem hc hc', min_mem hd hd', Ioc_inter_Ioc⟩
  apply S_pi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨c, d, -, -, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.mp hu x hx
    obtain ⟨c, hc, hc'⟩ :=
      μ.cdf.dense_setOf_continuousAt.exists_between (show x - ε < x by linarith)
    obtain ⟨d, hd, hd'⟩ :=
      μ.cdf.dense_setOf_continuousAt.exists_between (show x < x + ε by linarith)
    refine ⟨Ioc c d, ⟨c, d, hc, hd, rfl⟩, Ioc_mem_nhds hc'.2 hd'.1, ?_⟩
    intro y hy
    apply hε
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hy.1, hy.2, hc'.1, hd'.2]
  · rintro s ⟨c, d, hc, hd, rfl⟩
    rcases le_total d c with hdc | hcd
    · simp [Ioc_eq_empty_of_le hdc]
    rw [← NNReal.tendsto_coe]
    simp_rw [key _ hcd]
    exact (h d hd).sub (h c hc)

end weak_convergence_cdf



section levy_prokhorov_metric

open MeasureTheory Filter Topology

variable (F G :CumulativeDistributionFunction)

namespace CumulativeDistributionFunction

lemma tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto (fun i ↦ (Fs i).probabilityMeasure) atTop (𝓝 G.probabilityMeasure)
      ↔ ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  constructor
  · intro h x hGx
    have key := @tendsto_apply_of_tendsto_of_continuousAt ℕ atTop
                (fun i ↦ (Fs i).probabilityMeasure) G.probabilityMeasure h x
    simp_all
  · intro h
    apply tendsto_of_forall_continuousAt_tendsto_cdf
    simpa using h

noncomputable def equiv_levyProkhorov :
    CumulativeDistributionFunction ≃ LevyProkhorov (ProbabilityMeasure ℝ) :=
  equiv_probabilityMeasure.trans LevyProkhorov.toMeasureEquiv.symm

noncomputable instance : MetricSpace CumulativeDistributionFunction := by
  apply MetricSpace.induced equiv_levyProkhorov
  · intro F G h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using h
  · exact LevyProkhorov.levyProkhorovDist_metricSpace_probabilityMeasure

noncomputable def homeomorph_levyProkhorov :
    CumulativeDistributionFunction ≃ₜ LevyProkhorov (ProbabilityMeasure ℝ) :=
  Equiv.toHomeomorphOfIsInducing equiv_levyProkhorov ⟨rfl⟩

noncomputable def homeomorph_probabilityMeasure :
    CumulativeDistributionFunction ≃ₜ ProbabilityMeasure ℝ :=
  homeomorph_levyProkhorov.trans LevyProkhorov.probabilityMeasureHomeomorph.symm

lemma homeomorph_probabilityMeasure_apply_eq (F : CumulativeDistributionFunction) :
    homeomorph_probabilityMeasure F = F.probabilityMeasure :=
  rfl

/-- The standard characterization of convergence of cumulative distribution functions. -/
lemma tendsto_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto Fs atTop (𝓝 G) ↔
      ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  rw [← tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto]
  constructor
  · intro h
    simp_rw [← homeomorph_probabilityMeasure_apply_eq]
    apply homeomorph_probabilityMeasure.continuous.continuousAt.tendsto.comp h
  · intro h
    convert homeomorph_probabilityMeasure.symm.continuous.continuousAt.tendsto.comp h
    · ext1 i; simp [← homeomorph_probabilityMeasure_apply_eq]
    · simp [← homeomorph_probabilityMeasure_apply_eq]

end CumulativeDistributionFunction

end levy_prokhorov_metric



section continuous_mulAction

namespace CumulativeDistributionFunction

open Filter Topology

lemma continuous_mulAction :
    Continuous fun (⟨A, F⟩ : AffineIncrEquiv × CumulativeDistributionFunction) ↦ A • F := by
  rw [continuous_iff_seqContinuous]
  intro AFs BG h_lim
  rw [tendsto_iff_forall_continuousAt_tendsto]
  intro x hBGx
  simp only [Function.comp_apply, mulAction_apply_eq]
  have A_lim : Filter.Tendsto (fun i ↦ (AFs i).1) Filter.atTop (nhds BG.1) :=
    (continuous_fst.tendsto _).comp h_lim
  have F_lim : Filter.Tendsto (fun i ↦ (AFs i).2) Filter.atTop (nhds BG.2) :=
    (continuous_snd.tendsto _).comp h_lim
  rw [tendsto_iff_forall_continuousAt_tendsto] at F_lim
  have Ainv_lim : Filter.Tendsto (fun i ↦ (AFs i).1⁻¹ x) Filter.atTop (nhds (BG.1⁻¹ x)) := by
    have := (AffineIncrEquiv.continuous_inv.tendsto _).comp A_lim
    exact (AffineIncrEquiv.tendsto_nhds_iff_forall_tendsto_apply _ _).mp this x
  set y := BG.1⁻¹ x with hy
  have G_cont : ContinuousAt BG.2 y := (affine_continuousAt_iff BG.2 BG.1 x).mp hBGx
  rw [tendsto_order]
  constructor
  · intro r hr
    obtain ⟨δ, δ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (G_cont.eventually (eventually_gt_nhds hr))
    obtain ⟨z, z_cont, hz⟩ :=
      BG.2.dense_setOf_continuousAt.exists_between (show y - δ < y by linarith)
    have Gz : r < BG.2 z := by
      apply hδ
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hz.1, hz.2]
    filter_upwards [(F_lim z z_cont).eventually (eventually_gt_nhds Gz),
      Ainv_lim.eventually (eventually_gt_nhds hz.2)] with n hn hn'
    exact hn.trans_le ((AFs n).2.mono hn'.le)
  · intro r hr
    obtain ⟨δ, δ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (G_cont.eventually (eventually_lt_nhds hr))
    obtain ⟨z, z_cont, hz⟩ :=
      BG.2.dense_setOf_continuousAt.exists_between (show y < y + δ by linarith)
    have Gz : BG.2 z < r := by
      apply hδ
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hz.1, hz.2]
    filter_upwards [(F_lim z z_cont).eventually (eventually_lt_nhds Gz),
      Ainv_lim.eventually (eventually_lt_nhds hz.1)] with n hn hn'
    exact ((AFs n).2.mono hn'.le).trans_lt hn

end CumulativeDistributionFunction

end continuous_mulAction
