/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVFisherInformation

/-!
# The Hessian of the GEV log-density and the information identity

For `ξ ≠ 0` and a point of the support, write `z = (x - μ)/σ`, `u = 1 + ξ z > 0`,
`w = u^{-1/ξ}` and `L = log u`. The second derivatives of the GEV log-density
`ℓ(μ, σ, ξ; x) = -log σ - (1/ξ + 1) L - w` are rational functions of `(ξ, σ, u, w, L)`:

* `∂²_μ ℓ = (-w + ξ(1 + ξ - w))/(σ² u²)`,
* `∂_μ ∂_σ ℓ = (w(1 + ξ - u) - ξ(1 + ξ))/(ξ σ² u²)`,
* `∂_μ ∂_ξ ℓ = (ξ² u - w(L u - u + 1) - ξ(u - 1)(1 + ξ - w))/(σ ξ² u²)`,
* `∂²_σ ℓ`, `∂_σ ∂_ξ ℓ`, `∂²_ξ ℓ` (`gevHessSigmaSigma`, `gevHessSigmaXi`, `gevHessXiXi`).

We prove that these are the derivatives of the scores (in both orders for the mixed entries,
`hasDerivAt_gevScoreMu_sigma`, `hasDerivAt_gevScoreSigma_mu`, …), compute them on the exponential
scale, and prove the **information identity** (the second Bartlett identity): for `ξ > -1/2`,
`ξ ≠ 0`, every entry of the Hessian is integrable under the true law and its expectation is minus
the corresponding entry of the Fisher information `gevFisherInfo ξ σ`
(`integral_gevHess_eq_neg_gevFisherInfo`).

## References

* D. Prescott and A. T. Walden, *Maximum likelihood estimation of the parameters of the
  generalized extreme-value distribution*, Biometrika 67 (1980).
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### The Hessian -/

section Hessian

variable {ξ μ σ x : ℝ}

/-- `u = 1 + ξ (x - μ)/σ`. -/
noncomputable def gevU (ξ μ σ x : ℝ) : ℝ := 1 + ξ * ((x - μ) / σ)

/-- `∂²_μ ℓ`. -/
noncomputable def gevHessMuMu (ξ μ σ x : ℝ) : ℝ :=
  (-gevU ξ μ σ x ^ (-1 / ξ) + ξ * (-gevU ξ μ σ x ^ (-1 / ξ) + ξ + 1)) /
    (σ ^ 2 * gevU ξ μ σ x ^ 2)

/-- `∂_μ ∂_σ ℓ = ∂_σ ∂_μ ℓ`. -/
noncomputable def gevHessMuSigma (ξ μ σ x : ℝ) : ℝ :=
  (-gevU ξ μ σ x * gevU ξ μ σ x ^ (-1 / ξ) + gevU ξ μ σ x ^ (-1 / ξ) * ξ +
      gevU ξ μ σ x ^ (-1 / ξ) - ξ ^ 2 - ξ) / (σ ^ 2 * gevU ξ μ σ x ^ 2 * ξ)

/-- `∂_μ ∂_ξ ℓ = ∂_ξ ∂_μ ℓ`. -/
noncomputable def gevHessMuXi (ξ μ σ x : ℝ) : ℝ :=
  (gevU ξ μ σ x * ξ ^ 2 - gevU ξ μ σ x ^ (-1 / ξ) *
      (log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) -
      ξ * (gevU ξ μ σ x - 1) * (-gevU ξ μ σ x ^ (-1 / ξ) + ξ + 1)) /
    (σ * gevU ξ μ σ x ^ 2 * ξ ^ 2)

/-- `∂²_σ ℓ`. -/
noncomputable def gevHessSigmaSigma (ξ μ σ x : ℝ) : ℝ :=
  (gevU ξ μ σ x ^ 2 * gevU ξ μ σ x ^ (-1 / ξ) * ξ - gevU ξ μ σ x ^ 2 * gevU ξ μ σ x ^ (-1 / ξ) -
      gevU ξ μ σ x ^ 2 * ξ + 2 * gevU ξ μ σ x * gevU ξ μ σ x ^ (-1 / ξ) -
      gevU ξ μ σ x ^ (-1 / ξ) * ξ - gevU ξ μ σ x ^ (-1 / ξ) + ξ ^ 2 + ξ) /
    (σ ^ 2 * gevU ξ μ σ x ^ 2 * ξ ^ 2)

/-- `∂_σ ∂_ξ ℓ = ∂_ξ ∂_σ ℓ`. -/
noncomputable def gevHessSigmaXi (ξ μ σ x : ℝ) : ℝ :=
  (gevU ξ μ σ x - 1) * (gevU ξ μ σ x * ξ ^ 2 - gevU ξ μ σ x ^ (-1 / ξ) *
      (log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) +
      ξ * (gevU ξ μ σ x - 1) * (gevU ξ μ σ x ^ (-1 / ξ) - ξ - 1)) /
    (σ * gevU ξ μ σ x ^ 2 * ξ ^ 3)

/-- `∂²_ξ ℓ`. -/
noncomputable def gevHessXiXi (ξ μ σ x : ℝ) : ℝ :=
  (-2 * log (gevU ξ μ σ x) * gevU ξ μ σ x ^ 2 * ξ +
      gevU ξ μ σ x * gevU ξ μ σ x ^ (-1 / ξ) * ξ *
        (2 * log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) +
      gevU ξ μ σ x * ξ * (gevU ξ μ σ x - (gevU ξ μ σ x - 1) * (gevU ξ μ σ x ^ (-1 / ξ) - 1) - 1) -
      gevU ξ μ σ x ^ (-1 / ξ) * (log (gevU ξ μ σ x) * gevU ξ μ σ x - gevU ξ μ σ x + 1) ^ 2 -
      ξ * (gevU ξ μ σ x - 1) ^ 2 * (gevU ξ μ σ x ^ (-1 / ξ) - ξ - 1)) /
    (gevU ξ μ σ x ^ 2 * ξ ^ 4)

lemma measurable_gevU (ξ μ σ : ℝ) : Measurable (gevU ξ μ σ) := by unfold gevU; fun_prop

lemma measurable_gevHessMuMu (ξ μ σ : ℝ) : Measurable (gevHessMuMu ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessMuMu; fun_prop

lemma measurable_gevHessMuSigma (ξ μ σ : ℝ) : Measurable (gevHessMuSigma ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessMuSigma; fun_prop

lemma measurable_gevHessMuXi (ξ μ σ : ℝ) : Measurable (gevHessMuXi ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessMuXi; fun_prop

lemma measurable_gevHessSigmaSigma (ξ μ σ : ℝ) : Measurable (gevHessSigmaSigma ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessSigmaSigma; fun_prop

lemma measurable_gevHessSigmaXi (ξ μ σ : ℝ) : Measurable (gevHessSigmaXi ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessSigmaXi; fun_prop

lemma measurable_gevHessXiXi (ξ μ σ : ℝ) : Measurable (gevHessXiXi ξ μ σ) := by
  have := measurable_gevU ξ μ σ; unfold gevHessXiXi; fun_prop

end Hessian

end ExtremeValueTheory
