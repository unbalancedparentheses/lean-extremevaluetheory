/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Minimality.ClassicalKaramata
import ExtremeValueTheory.Minimality.ClassicalBreiman
import ExtremeValueTheory.Minimality.ClassicalVonMises
import ExtremeValueTheory.Minimality.ClassicalGeneralizedCLT
import ExtremeValueTheory.Minimality.ClassicalHill

/-!
# Minimal hypotheses for classical and statistical results: summary

This file holds no declarations. It indexes the machine-checked minimality results for the
classical (regular variation, domains of attraction, stable laws) and statistical (Hill) parts
of the library. For each hypothesis there are three possible outcomes: it is **dropped** (a
stronger theorem is proved), it is **necessary** (a `not_…`/`…_counterexample` theorem gives an
explicit construction where it fails and the conclusion fails), or it is **open**.

| theorem | hypothesis | status |
|---|---|---|
| `IsRegularlyVarying.tendsto_integral_Ioi_div` (Karamata) | `α > 1` | necessary: `α < 1` fails for every `F` (`not_tendsto_integral_Ioi_div_of_lt_one`, `max_rpow_karamata_counterexample`); `α = 1` fails for every integrable `F` (`tendsto_integral_Ioi_div_atTop_of_neg_one`, `logTail_two_karamata_counterexample`) |
| same | `Antitone F` | dropped to measurable + locally bounded (`tendsto_integral_Ioi_div_of_measurable`, existing) |
| `tendsto_measure_mul_div_measure` (Breiman) | `E[Y^(α+ε)] < ∞` | not weakenable to `E[Y^α] < ∞` in general (`breiman_counterexample`, `not_integrable_breimanY_rpow`) |
| same | same, if `x^α P(X > x) → c > 0` | dropped to `E[Y^α] < ∞` (`tendsto_measure_mul_div_measure_of_tendsto_rpow_mul`) |
| same | Denisov–Zwart sharp condition | open |
| `isInMDAGumbel_of_vonMises_nhdsLT` | `F t → 1` as `t ↑ x_F` (no atom) | necessary (`atomCDF_vonMises_counterexample`; general: `not_isInMDAGumbel_of_gap`) |
| `tendsto_map_convPow_of_isRegularlyVarying_of_lt_one` and companions (GCLT) | tail balance `P(X > x)/P(\|X\| > x) → p` | necessary for any non-degenerate limit (`not_tendsto_of_not_tailBalance`, `signedPareto_gclt_counterexample`) |
| `tendstoInMeasure_hill` | `k(n) → ∞` | necessary, even for exact Pareto (`not_tendstoInMeasure_hill_pareto_of_not_tendsto`; iff: `tendstoInMeasure_hill_pareto_iff`) |
| same | `k(n)/n → 0` | necessary (`not_tendstoInMeasure_hill_of_le_mul`, `exists_hill_k_linear_counterexample`) |

The dependence results are summarized in the `Minimality/Dependence*.lean` files.
-/
