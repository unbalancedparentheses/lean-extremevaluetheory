import ExtremeValueTheory.DomainOfAttraction.GEVDomain

/-!
# Known answers and non-vacuity: `IsInMDAGEV` against `gevCDF`, and the standard laws

Checks that `IsInMDAGEV ξ` is the textbook domain of attraction of `gevCDF ξ`, on the textbook
examples.

References: [EKM] Embrechts, Klüppelberg, Mikosch, *Modelling Extremal Events* (1997), §3.3;
[dHF] de Haan, Ferreira, *Extreme Value Theory* (2006), §1.1.
-/

open Real Filter Topology Set MeasureTheory ProbabilityTheory
open CumulativeDistributionFunction ExtremeValueTheory

namespace Test.KnownAnswers.DomainExamples

/-! ### The link with `gevCDF` -/

/-- Pareto(`α`): `IsInMDAGEV (1 / α)` gives convergence to `gevCDF (1 / α)` itself, with `ξ = 1/α`
in the Jenkinson–von Mises sign ([EKM, Table 3.4.2]). -/
theorem test_exists_tendsto_gevCDF_pareto {α : ℝ} (hα : 0 < α) :
    ∃ As : ℕ → AffineIncrEquiv, ∀ x,
      Tendsto (fun n : ℕ ↦ ((As n • paretoCDF hα) x) ^ n) atTop (𝓝 (gevCDF (1 / α) x)) :=
  (isInMDAGEV_iff_exists_tendsto_gevCDF _).1 (isInMDAGEV_paretoCDF hα)

/-- `1 - (1 - x)^α` on `[0, 1]`: convergence to `gevCDF (-1 / α)`, the sign `ξ < 0` of the bounded
side ([EKM, Table 3.4.3]). -/
theorem test_exists_tendsto_gevCDF_power {α : ℝ} (hα : 0 < α) :
    ∃ As : ℕ → AffineIncrEquiv, ∀ x,
      Tendsto (fun n : ℕ ↦ ((As n • powerCDF hα) x) ^ n) atTop (𝓝 (gevCDF (-1 / α) x)) :=
  (isInMDAGEV_iff_exists_tendsto_gevCDF _).1 (isInMDAGEV_powerCDF hα)

/-- The converse direction: exponential maxima converge to `gevCDF 0`, so the law is in `MDA(H_0)`
([EKM, Table 3.4.4]). -/
theorem test_isInMDAGEV_of_exists_tendsto_gevCDF_exponential :
    standardExponentialCDF.IsInMDAGEV 0 :=
  (isInMDAGEV_iff_exists_tendsto_gevCDF 0).2
    ((isInMDAGEV_iff_exists_tendsto_gevCDF 0).1 isInMDAGEV_standardExponentialCDF)

/-- Exercises `exists_isInMDAGEV_of_tendsto` on the Gumbel limit of exponential maxima: a
nondegenerate limit at continuity points gives a domain of attraction. -/
theorem test_exists_isInMDAGEV_of_tendsto_exponential :
    ∃ ξ, standardExponentialCDF.IsInMDAGEV ξ := by
  obtain ⟨As, hAs⟩ := isInMDAGumbel_standardExponentialCDF
  exact exists_isInMDAGEV_of_tendsto isExtremeValueDistr_standardGumbelCDF.1 fun x _ => hAs x

end Test.KnownAnswers.DomainExamples
