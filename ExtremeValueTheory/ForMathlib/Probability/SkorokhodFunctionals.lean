/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Probability.SkorokhodLaw
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous functionals on the Skorokhod space

Functionals of paths that are continuous for the Skorokhod `J₁` topology on `D([0, 1], E)`, to be
used with the continuous mapping theorem
(`MeasureTheory.ProbabilityMeasure.tendsto_map_of_ae_continuousAt`):

* the **supremum norm** `x ↦ sup_t ‖x t‖` is `1`-Lipschitz, because a time change does not change
  the range of a path;
* the **evaluation** `x ↦ x t` is continuous at every path continuous at `t`, and at every path
  when `t = 0` or `t = 1`;
* the **integral functionals** `x ↦ ∫ g(t) x(t) dμ(t)`, for a measure `μ` without atoms and an
  integrable weight `g`, are continuous: if `x_n → x` in `D`, then `x_n(t) → x(t)` at every
  continuity point `t` of `x`, i.e. off a countable set, and the `x_n` are uniformly bounded, so
  dominated convergence applies. For instance `x ↦ ∫_ε^1 x(t) dt / t` is continuous for
  `ε > 0`.

## Main statements

* `SkorokhodSpace.lipschitzWith_supNorm`, `SkorokhodSpace.continuous_supNorm`.
* `SkorokhodSpace.continuousAt_apply`.
* `SkorokhodSpace.continuous_integral_mul`.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999], §12
-/

@[expose] public section

open Filter Set Topology MeasureTheory unitInterval
open scoped ENNReal

namespace SkorokhodSpace

variable {E : Type*}

section SupNorm

variable [SeminormedAddCommGroup E]

/-- The supremum norm `sup_t ‖x t‖` of a càdlàg path. -/
noncomputable def supNorm (x : SkorokhodSpace E) : ℝ := ⨆ t, ‖x t‖

lemma bddAbove_range_norm (x : SkorokhodSpace E) : BddAbove (range fun t ↦ ‖x t‖) := by
  obtain ⟨C, hC⟩ := x.isBounded_range.exists_norm_le
  exact ⟨C, by rintro _ ⟨t, rfl⟩; exact hC _ ⟨t, rfl⟩⟩

lemma norm_le_supNorm (x : SkorokhodSpace E) (t : I) : ‖x t‖ ≤ supNorm x :=
  le_ciSup (bddAbove_range_norm x) t

lemma supNorm_nonneg (x : SkorokhodSpace E) : 0 ≤ supNorm x :=
  (norm_nonneg _).trans (norm_le_supNorm x 0)

lemma supNorm_le_add_dist (x y : SkorokhodSpace E) : supNorm x ≤ supNorm y + dist x y := by
  refine ciSup_le fun t ↦ le_of_forall_pos_lt_add fun r hr ↦ ?_
  have hlt : edist x y < ENNReal.ofReal (dist x y + r) := by
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  obtain ⟨φ, -, hxy⟩ := exists_timeChange_of_edist_lt hlt
  have h := hxy t
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h
  have h1 : ‖x t‖ ≤ ‖y (φ t)‖ + dist (x t) (y (φ t)) := by
    rw [dist_eq_norm]
    exact norm_le_norm_add_norm_sub' _ _
  have h2 := norm_le_supNorm y (φ t)
  linarith

/-- The supremum norm is `1`-Lipschitz for the Skorokhod metric. -/
lemma lipschitzWith_supNorm : LipschitzWith 1 (supNorm : SkorokhodSpace E → ℝ) :=
  LipschitzWith.of_le_add supNorm_le_add_dist

lemma continuous_supNorm : Continuous (supNorm : SkorokhodSpace E → ℝ) :=
  lipschitzWith_supNorm.continuous

end SupNorm

section Evaluation

variable [PseudoEMetricSpace E]

/-- The evaluation `y ↦ y t` is continuous at every path continuous at `t`. -/
lemma continuousAt_apply {x : SkorokhodSpace E} {t : I} (hx : ContinuousAt x t) :
    ContinuousAt (fun y : SkorokhodSpace E ↦ y t) x :=
  tendsto_apply_of_continuousAt tendsto_id hx

/-- For a path `x` and a time `t ∈ [0, 1]`, either the evaluation at `t` is continuous at `x`,
or `t` is an interior time at which `x` jumps. -/
lemma tendsto_apply_of_edist_leftLim_eq_zero {E : Type*} [EMetricSpace E] {x : SkorokhodSpace E}
    {t : I} (ht : edist (Function.leftLim x t) (x t) = 0 ∨ t = 0 ∨ t = 1) :
    Tendsto (fun y : SkorokhodSpace E ↦ y t) (𝓝 x) (𝓝 (x t)) := by
  rcases ht with h | rfl | rfl
  · exact continuousAt_apply (continuousAt_of_edist_leftLim_eq_zero x h)
  · exact tendsto_apply_zero tendsto_id
  · exact tendsto_apply_one tendsto_id

end Evaluation

section Integral

/-- **Integral functionals are continuous on `D`**: for a measure `μ` on `ℝ` without atoms and an
integrable weight `g`, the functional `x ↦ ∫ g(t) x(t) dμ(t)` (with `x` extended to `ℝ` by
`x (projIcc 0 1 t)`) is continuous for the Skorokhod topology. -/
theorem continuous_integral_mul {μ : Measure ℝ} [NullSingletonClass μ] {g : ℝ → ℝ}
    (hg : Integrable g μ) :
    Continuous fun x : SkorokhodSpace ℝ ↦ ∫ t, g t * x (projIcc 0 1 zero_le_one t) ∂μ := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun t ↦ |g t| * (supNorm x + 1))
    (Eventually.of_forall fun y ↦ hg.aestronglyMeasurable.mul
      (y.isCadlag.measurable.comp continuous_projIcc.measurable).aestronglyMeasurable) ?_
    (hg.abs.mul_const _) ?_
  · filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    refine ae_of_all _ fun t ↦ ?_
    rw [norm_mul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 := norm_le_supNorm y (projIcc 0 1 zero_le_one t)
    have h2 := supNorm_le_add_dist y x
    rw [Metric.mem_ball] at hy
    linarith
  · -- outside a countable set of times, the evaluation is continuous at `x`
    set D := {s : I | edist (Function.leftLim x s) (x s) ≠ 0}
    have hD : ((↑) '' D : Set ℝ).Countable :=
      (x.isCadlag.countable_setOf_edist_leftLim_ne_zero).image _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hD.measure_zero μ)] with t ht
    refine tendsto_const_nhds.mul (tendsto_apply_of_edist_leftLim_eq_zero ?_)
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h0, h1'⟩ := hcon
    apply ht
    refine ⟨projIcc 0 1 zero_le_one t, h1, ?_⟩
    have h0' : (0 : ℝ) < projIcc (0 : ℝ) 1 zero_le_one t := by
      rw [← Subtype.coe_ne_coe] at h0
      exact lt_of_le_of_ne (projIcc 0 1 zero_le_one t).2.1 (Ne.symm h0)
    have h1'' : (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) < 1 := by
      rw [← Subtype.coe_ne_coe] at h1'
      exact lt_of_le_of_ne (projIcc 0 1 zero_le_one t).2.2 h1'
    rcases le_or_gt t 0 with h | h
    · rw [projIcc_of_le_left _ h] at h0'; simp at h0'
    rcases le_or_gt 1 t with h' | h'
    · rw [projIcc_of_right_le _ h'] at h1''; simp at h1''
    rw [projIcc_of_mem _ ⟨h.le, h'.le⟩]

end Integral

end SkorokhodSpace
