import ExtremeValueTheory

/-!
# Non-vacuity: Wilks' theorem and profile likelihood intervals for the GPD

Each test builds an iid `GPD(1/4, 3/2)` sample (via Mathlib's `exists_iid`) and the compact
parameter set `K = [1/8, 1/2] × [1, 2]`, discharges every hypothesis of a headline theorem of
`ExtremeValueTheory.Statistics.GPDWilks`, and obtains its conclusion for that sample.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace ExtremeValueTheory.Test.NonVacuity.ProfileLikelihood

/-- The compact parameter set `K = [1/8, 1/2] × [1, 2]` for `(ξ, σ)`. -/
private def K : Set (ℝ × ℝ) := Icc (1 / 8 : ℝ) (1 / 2) ×ˢ Icc (1 : ℝ) 2

private theorem isCompact_K : IsCompact K := isCompact_Icc.prod isCompact_Icc

private theorem K_sub : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2 := fun p hp => by
  have h1 := hp.1.1
  have h2 := hp.2.1
  exact ⟨by linarith, by linarith⟩

private theorem mem_interior_K : ((1 / 4 : ℝ), (3 / 2 : ℝ)) ∈ interior K := by
  rw [K, interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- Exercises `tendstoInDistribution_gpdDeviance` (Wilks' theorem) with measurable maximizers from
`exists_measurable_gpdMLE`: the deviance of an iid `GPD(1/4, 3/2)` sample converges to `χ²₂`. -/
theorem test_nonvacuous_tendstoInDistribution_gpdDeviance :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (θh : ℕ → Ω → ℝ × ℝ),
      (∀ n ω, θh n ω ∈ K) ∧
      (∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K (θh n ω)) ∧
      TendstoInDistribution (fun (n : ℕ) ω =>
          2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
            gpdLogLikN (1 / 4) (3 / 2) (fun i => X i ω) n))
        atTop (id : ℝ → ℝ) (fun _ => P) (chiSquared 2) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  choose G hGm hG using exists_measurable_gpdMLE isCompact_K K_sub
    ⟨_, interior_subset mem_interior_K⟩
  refine ⟨Ω, _, P, hP, X, fun n ω => G n fun i : Fin n => X i ω, fun n ω => (hG n _).1,
    fun n ω => (hG n _).2, ?_⟩
  exact tendstoInDistribution_gpdDeviance isCompact_K K_sub mem_interior_K (by norm_num)
    (by norm_num) hlaw hind
    (fun n => (hGm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hlaw i).aemeasurable))
    (fun n ω => (hG n _).1) (fun n ω => (hG n _).2) HasLaw.id

/-- Exercises `tendsto_measure_mem_gpdShapeProfileInterval`: the coverage of the profile likelihood
set for the shape converges to `χ²₁((-∞, c])`, for every `c`. -/
theorem test_nonvacuous_shape (c : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      Tendsto (fun n : ℕ =>
          P {ω | (1 / 4 : ℝ) ∈ gpdProfileInterval K Prod.fst c (fun i : Fin n => X i ω)})
        atTop (𝓝 (chiSquared 1 (Iic c))) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  exact ⟨Ω, _, P, hP, X, tendsto_measure_mem_gpdShapeProfileInterval isCompact_K K_sub
    mem_interior_K (by norm_num) (by norm_num) hlaw hind c⟩

/-- Exercises `tendsto_measure_mem_gpdScaleProfileInterval`. -/
theorem test_nonvacuous_scale (c : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      Tendsto (fun n : ℕ =>
          P {ω | (3 / 2 : ℝ) ∈ gpdProfileInterval K Prod.snd c (fun i : Fin n => X i ω)})
        atTop (𝓝 (chiSquared 1 (Iic c))) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  exact ⟨Ω, _, P, hP, X, tendsto_measure_mem_gpdScaleProfileInterval isCompact_K K_sub
    mem_interior_K (by norm_num) (by norm_num) hlaw hind c⟩

/-- Exercises `tendsto_measure_mem_gpdReturnLevelProfileInterval`: threshold `u = 5`, exceedance
probability `ζ = 1/2`, return period `N = 10`, so `N ζ = 5 > 1`. -/
theorem test_nonvacuous_returnLevel (c : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      Tendsto (fun n : ℕ => P {ω | gpdReturnLevel 5 (1 / 4) (3 / 2) (1 / 2) 10 ∈
          gpdProfileInterval K (fun p => gpdReturnLevel 5 p.1 p.2 (1 / 2) 10) c
            (fun i : Fin n => X i ω)})
        atTop (𝓝 (chiSquared 1 (Iic c))) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  exact ⟨Ω, _, P, hP, X, tendsto_measure_mem_gpdReturnLevelProfileInterval isCompact_K K_sub
    mem_interior_K (by norm_num) (by norm_num) hlaw hind (by norm_num) c⟩

/-- A 95% interval for the return level: exercises `exists_tendsto_measure_mem_gpdProfileInterval`
with `α = 1/20` and the chart `isGPDProfileChart_returnLevel`. -/
theorem test_nonvacuous_returnLevel_95 :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (c : ℝ), 0 < c ∧ (chiSquared 1).real (Iic c) = 1 - 1 / 20 ∧
      Tendsto (fun n : ℕ => P {ω | gpdReturnLevel 5 (1 / 4) (3 / 2) (1 / 2) 10 ∈
          gpdProfileInterval K (fun p => gpdReturnLevel 5 p.1 p.2 (1 / 2) 10) c
            (fun i : Fin n => X i ω)})
        atTop (𝓝 (ENNReal.ofReal (1 - 1 / 20))) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  have hcont : Continuous fun p : ℝ × ℝ => gpdReturnLevel 5 p.1 p.2 (1 / 2) 10 := by
    unfold gpdReturnLevel
    exact continuous_const.add (continuous_snd.mul
      ((continuous_boxCox_shape (by norm_num)).comp continuous_fst))
  obtain ⟨c, h0, hq, h⟩ := exists_tendsto_measure_mem_gpdProfileInterval isCompact_K K_sub
    mem_interior_K (by norm_num) (by norm_num) hlaw hind hcont.continuousOn
    (isGPDProfileChart_returnLevel (by norm_num) (by norm_num))
    (α := 1 / 20) (by norm_num) (by norm_num)
  exact ⟨Ω, _, P, hP, X, c, h0, hq, h⟩

/-- Exercises `tendsto_measure_mem_gpdDevianceRegion_of_alpha`: the region at
`c = -2 log(1/20)` for the full parameter has asymptotic coverage `95%`. -/
theorem test_nonvacuous_region_95 :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      Tendsto (fun n : ℕ => P {ω | ((1 / 4 : ℝ), (3 / 2 : ℝ)) ∈
          gpdDevianceRegion K (-2 * Real.log (1 / 20)) (fun i : Fin n => X i ω)})
        atTop (𝓝 (ENNReal.ofReal (1 - 1 / 20))) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  exact ⟨Ω, _, P, hP, X, tendsto_measure_mem_gpdDevianceRegion_of_alpha isCompact_K K_sub
    mem_interior_K (by norm_num) (by norm_num) hlaw hind (by norm_num) (by norm_num)⟩

end ExtremeValueTheory.Test.NonVacuity.ProfileLikelihood
