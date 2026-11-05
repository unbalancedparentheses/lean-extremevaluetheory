/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDWilks.Deviance
import ExtremeValueTheory.Statistics.GPDWilks.Profile
import ExtremeValueTheory.Statistics.GPDWilks.Coverage

/-!
# Wilks' theorem and profile likelihood intervals for the GPD, `ξ₀ > 0`

Let `X₀, X₁, …` be iid `GPD(ξ₀, σ₀)` with `ξ₀ > 0`, and let the likelihood be maximized over a
compact set `K ⊂ {ξ > -1, σ > 0}` with `θ₀` in its interior. We prove the results of [Coles,
§2.6.5–2.6.6]:

* **Wilks' theorem.** `2 (sup_K ℓₙ - ℓₙ(θ₀)) ⇒ χ²₂` (`tendstoInDistribution_gpdDeviance`).
* **Profile deviance.** For an interest parameter `ψ = g(θ)` with a chart of its level set,
  `2 (sup_K ℓₙ - sup_{K ∩ {g = ψ₀}} ℓₙ) ⇒ χ²₁` (`tendstoInDistribution_gpdProfileDeviance`).
* **Coverage.** `P(ψ₀ ∈ {ψ : D_p(ψ) ≤ c}) → χ²₁((-∞, c])`
  (`tendsto_measure_mem_gpdProfileInterval`), for the shape, the scale and the POT return level.

## Proof

Write `Sₙ` for the normalized score at `θ₀` and `I` for the Fisher information.

* The Taylor expansion of the log-likelihood *around the estimator*, with the Hessian at `θ₀`
  (`abs_gpdLogLikN_expansion_le`), reduces a deviance to `Tₙᵀ I Tₙ` plus the first-order term at the
  estimator plus `o_P(1)`, where `Tₙ = √n (θ - θ₀)`.
* At a full root, the first-order term vanishes, and `Tₙ = I⁻¹ Sₙ + o_P(1)`.
* A restricted maximizer `γ(sₙ)` on a curve is stationary along the curve: `γ'(sₙ) · ∇ℓₙ = 0`. The
  first-order term is the score against the chord minus the tangent, hence `o_P(1)`, though the
  curve may be curved (it is, for the return level); and `Tₙ` is the tangent `t` times
  `(t · Sₙ)/(tᵀ I t) + o_P(1)`.
* The profile deviance is the difference `Sₙᵀ I⁻¹ Sₙ - (t · Sₙ)²/(tᵀ I t) + o_P(1)`, which is the
  square of one standardized linear combination of `Sₙ`: the scalar CLT gives `χ²₁`.

All the probabilistic work is in one lemma (`tendstoInMeasure_zero_of_ae_isLittleO`): the expansions
hold along each fixed `ω`, as `o` of a power of `1 + |S₁| + |S₂|`, which is bounded in probability.

## Limits of this formalization

* `ξ₀ > 0` is assumed, because the Lipschitz control of the Hessian
  (`exists_gpdHess_lipschitz`) is available only there. Coles' regular range is `ξ₀ > -1/2`.
* The likelihood is maximized over a compact `K`, as in all the MLE results of the library.
* The law of the sample is exactly GPD: no threshold selection or approximation error.
* In the return level the threshold `u` and the exceedance probability `ζ` are known constants, as in
  `tendstoInDistribution_gpdReturnLevel`. Uncertainty in `ζ` is not included.
* `gpdProfileInterval` is a confidence *set*. That it is an interval is not proved.
* GEV profile likelihood is not covered.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §2.6.5–2.6.6, §4.3.3.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §16.
-/
