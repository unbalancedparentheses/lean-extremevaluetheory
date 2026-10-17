/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.ThetaGap
import ExtremeValueTheory.Dependence.MDependentExamples

/-!
# The echo process: `θ < ϑ`

TODO
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Asymptotic independence gives the trivial spectral tail process -/

section AsymptoticIndependence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℤ → Ω → ℝ} {α : ℝ}

/-- The spectral tail process `Θ_t = 1{t = 0}` of an asymptotically independent nonnegative
series, on the one-point space. -/
def unitSpectral (t : ℤ) (_ : Unit) : ℝ := if t = 0 then 1 else 0

theorem measurable_unitSpectral (t : ℤ) : Measurable (unitSpectral t) := measurable_const

/-- **Asymptotic independence gives `Θ = (…, 0, 1, 0, …)`.** If `X_0 ≥ 0`, `P(|X_0| > x)` is
regularly varying with index `-α`, and for every `t ≠ 0` and `ε > 0`,
`P(|X_t| > ε x | |X_0| > x) → 0`, then the spectral tail process is `Θ_t = 1{t = 0}`. -/
theorem hasSpectralTailProcess_of_asymptoticIndependence (hX : ∀ t, Measurable (X t))
    (hX0 : ∀ ω, 0 ≤ X 0 ω) (hRV : IsRegularlyVarying (fun x => P.real {ω | x < |X 0 ω|}) (-α))
    (hai : ∀ t : ℤ, t ≠ 0 → ∀ ε : ℝ, 0 < ε → Tendsto (fun x =>
      P.real {ω | x < |X 0 ω| ∧ ε * x < |X t ω|} / P.real {ω | x < |X 0 ω|}) atTop (𝓝 0)) :
    HasSpectralTailProcess P X α (Measure.dirac ()) unitSpectral := by
  classical
  refine ⟨hRV, fun S f => ?_⟩
  set e : S → ℝ := fun t => if (t : ℤ) = 0 then 1 else 0
  have hmap : (Measure.dirac ()).map (fun ω' (t : S) => unitSpectral t ω') = Measure.dirac e := by
    rw [Measure.map_dirac' (measurable_pi_iff.2 fun t => measurable_unitSpectral _)]
    rfl
  rw [hmap, integral_dirac]
  set s : ℝ → Set Ω := fun x => {ω | x < |X 0 ω|}
  have hZ : Measurable fun ω => |X 0 ω| := continuous_abs.measurable.comp (hX 0)
  have hs : ∀ x, MeasurableSet (s x) := fun x => measurableSet_lt measurable_const hZ
  set w : Ω → (S → ℝ) := fun ω t => X t ω / |X 0 ω|
  have hw : Measurable w := measurable_pi_iff.2 fun t => (hX t).div hZ
  have hpos : ∀ᶠ x in atTop, 0 < P.real (s x) := hRV.eventually_pos
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.1 f.continuous e (η / 2) (half_pos hη)
  set C := ‖f‖
  have hC : 0 ≤ C := norm_nonneg _
  set T : Finset ℤ := S.filter fun t => t ≠ 0
  set B : ℝ → Set Ω := fun x => ⋃ t ∈ T, {ω | δ * x < |X t ω|}
  have hB : ∀ x, MeasurableSet (B x) := fun x =>
    Finset.measurableSet_biUnion _ fun t _ =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX t))
  -- the conditional probability of `B` vanishes
  have hBlim : Tendsto (fun x => ∑ t ∈ T,
      P.real {ω | x < |X 0 ω| ∧ δ * x < |X t ω|} / P.real {ω | x < |X 0 ω|}) atTop (𝓝 0) := by
    have := tendsto_finsetSum T fun t ht => hai t (Finset.mem_filter.1 ht).2 δ hδ
    simpa using this
  have hκ : 0 < η / (2 * (2 * C + 1)) := by positivity
  filter_upwards [hpos, eventually_gt_atTop 0, hBlim.eventually (gt_mem_nhds hκ)] with x hx hx0 hxB
  have hP : P (s x) ≠ 0 := fun h0 => by simp [measureReal_def, h0] at hx
  have := cond_isProbabilityMeasure (μ := P) hP
  set μ := P[|s x]
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂μ, |f (w ω) - f e| ≤ η / 2 + 2 * C * (B x).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [ae_cond_mem (hs x)] with ω hω
    have hω' : x < |X 0 ω| := hω
    by_cases hωB : ω ∈ B x
    · rw [indicator_of_mem hωB, mul_one]
      have := f.dist_le_two_norm (w ω) e
      rw [Real.dist_eq] at this
      linarith
    · rw [indicator_of_notMem hωB, mul_zero, add_zero]
      have hlt : dist (w ω) e < δ := by
        rw [dist_pi_lt_iff hδ]
        intro t
        by_cases ht : (t : ℤ) = 0
        · have hX0pos : 0 < X 0 ω := by
            have := hx0.trans hω'
            rwa [abs_of_nonneg (hX0 ω)] at this
          have h1 : w ω t = 1 := by
            simp only [w, ht, abs_of_nonneg (hX0 ω)]
            exact div_self hX0pos.ne'
          have h2 : e t = 1 := by simp [e, ht]
          rw [h1, h2, dist_self]
          exact hδ
        · have hnB : ¬ δ * x < |X t ω| := fun hcon =>
            hωB (mem_iUnion₂.2 ⟨t, Finset.mem_filter.2 ⟨t.2, ht⟩, hcon⟩)
          simp only [w, e, ht, ite_false, Real.dist_eq, sub_zero, abs_div, abs_abs]
          rw [div_lt_iff₀ (hx0.trans hω')]
          calc |X t ω| ≤ δ * x := not_lt.1 hnB
            _ < δ * |X 0 ω| := mul_lt_mul_of_pos_left hω' hδ
      have := hfδ (w ω) hlt
      rw [Real.dist_eq] at this
      exact this.le
  have hfw : Integrable (fun ω => f (w ω)) μ :=
    integrable_of_abs_le (f.continuous.measurable.comp hw) fun ω => by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (w ω)
  have hint : Integrable (fun ω => η / 2 + 2 * C * (B x).indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator (hB x) |>.const_mul _)
  have hμB : μ.real (B x) ≤ η / (2 * (2 * C + 1)) := by
    rw [measureReal_def, cond_toReal_eq (hs x)]
    refine le_trans ?_ hxB.le
    rw [← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ measureReal_nonneg
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le T _)
    intro ω ⟨h0, h1⟩
    obtain ⟨t, ht, hlt⟩ := mem_iUnion₂.1 h1
    exact mem_iUnion₂.2 ⟨t, ht, h0, hlt⟩
  rw [Real.dist_eq, show f e = ∫ _, f e ∂μ by simp, ← integral_sub hfw (integrable_const _)]
  calc |∫ ω, (f (w ω) - f e) ∂μ| ≤ ∫ ω, |f (w ω) - f e| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (η / 2 + 2 * C * (B x).indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
        integral_mono_ae (hfw.sub (integrable_const _)).abs hint hpt
    _ = η / 2 + 2 * C * μ.real (B x) := by
        rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator (hB x)
          |>.const_mul _), integral_const_mul, integral_indicator_const _ (hB x)]
        simp
    _ ≤ η / 2 + 2 * C * (η / (2 * (2 * C + 1))) := by gcongr
    _ < η := by
        have : 2 * C * (η / (2 * (2 * C + 1))) < η / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

end AsymptoticIndependence

end ExtremeValueTheory
