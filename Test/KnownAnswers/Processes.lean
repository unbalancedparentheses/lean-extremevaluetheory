import ExtremeValueTheory

/-! # Known answers: point processes

The Poisson random measure, the radial (Pareto) measure and the exceedance intensity measure of
`ExtremeValueTheory/PointProcess` and `ExtremeValueTheory/ForMathlib/Probability`, evaluated on
cases with a textbook answer.

References: [EKM] Embrechts, Klüppelberg, Mikosch, *Modelling Extremal Events* (1997), §5.1–5.3;
[Res87] Resnick, *Extreme Values, Regular Variation, and Point Processes* (1987), Chapter 3;
[Kin93] Kingman, *Poisson Processes* (1993).
-/

open ExtremeValueTheory MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Test.KnownAnswers.Processes

/-- **The mean measure of a Poisson random measure is its intensity**: `E N(A) = ν(A)` for every
measurable `A` of finite intensity ([Kin93, §2.1], [Res87, §3.3]). -/
theorem test_lintegral_poissonRandomMeasure {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {N : Ω → Measure E} {ν : Measure E} {P : Measure Ω} (hN : IsPoissonRandomMeasure N ν P)
    {A : Set E} (hA : MeasurableSet A) (hνA : ν A ≠ ∞) :
    ∫⁻ ω, N ω A ∂P = ν A := by
  have hL := hN.hasLaw hA hνA
  have h1 : ∫⁻ ω, N ω A ∂P = ∫⁻ x, x ∂(P.map fun ω => N ω A) :=
    (lintegral_map measurable_id (hN.measurable_apply hA)).symm
  rw [h1, hL.map_eq]
  change ∫⁻ x, x ∂((poissonMeasure (ν A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) = _
  rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id measurable_from_top]
  rw [lintegral_natCast_poissonMeasure, ENNReal.coe_toNNReal hνA]

/-- The zero random measure is Poisson with intensity `0`. -/
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω}
    [IsProbabilityMeasure P] : IsPoissonRandomMeasure (fun _ : Ω => (0 : Measure E)) 0 P :=
  isPoissonRandomMeasure_zero

/-- The radial measure `α r^{-α-1} dr` on `(0, ∞)` has Pareto tail `ν(u, ∞) = u^{-α}`
([Res87, §5.4]); at `α = 2`, `u = 2`: `1/4`. -/
theorem test_radialMeasure_Ioi : radialMeasure 2 (Ioi 2) = ENNReal.ofReal (1 / 4) := by
  rw [radialMeasure_Ioi two_pos two_pos]
  congr 1
  rw [Real.rpow_neg (by norm_num), Real.rpow_two]
  norm_num

/-- The radial measure of the unit Fréchet case `α = 1` is infinite near the origin. -/
example : radialMeasure 1 (Ioi 0) = ∞ := radialMeasure_one_Ioi_zero

/-- **Gumbel exceedances**: the limiting Poisson process of exceedances for the Gumbel law
`Λ(x) = exp(-e^{-x})` has intensity `μ(a, ∞) = -log Λ(a) = e^{-a}` ([EKM, §5.3],
[Res87, §4.4]). Threshold `u = 0`. -/
theorem test_exceedanceMeasure_gumbel_Ioi {a : ℝ} (ha : 0 ≤ a) :
    exceedanceMeasure standardGumbelCDF (u := 0) (by simp [standardGumbelCDF_apply_eq]; positivity)
      (Ioi a) = ENNReal.ofReal (Real.exp (-a)) := by
  rw [exceedanceMeasure_Ioi _ ha, standardGumbelCDF_apply_eq, Real.log_exp, neg_neg]

/-- On `(a, b]` the Gumbel exceedance intensity is `e^{-a} - e^{-b}`. -/
theorem test_exceedanceMeasure_gumbel_Ioc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    exceedanceMeasure standardGumbelCDF (u := 0) (by simp [standardGumbelCDF_apply_eq]; positivity)
      (Ioc a b) = ENNReal.ofReal (Real.exp (-a) - Real.exp (-b)) := by
  rw [exceedanceMeasure_Ioc _ ha hab, standardGumbelCDF_apply_eq, standardGumbelCDF_apply_eq,
    Real.log_exp, Real.log_exp]
  ring_nf

end Test.KnownAnswers.Processes
