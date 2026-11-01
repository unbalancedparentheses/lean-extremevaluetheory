/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDJointNormality

/-!
# Second-order expansion of the GPD log-likelihood, `ξ₀ > 0`

For the likelihood-ratio (deviance) statistic we need the log-likelihood itself, not only the
score, to second order around the true parameter `θ₀ = (ξ₀, σ₀)`, `ξ₀ > 0`. We prove:

* `hasDerivAt_log_gpdDensity_line`: along a line `s ↦ (ξ + s a, σ + s b)` in parameter space
  the derivative of the log-density is `a ∂_ξ ℓ + b ∂_σ ℓ`.
* `abs_log_gpdDensity_expansion_le`: **the second-order Taylor expansion with an explicit
  remainder.** For `θ ∈ gpdNbhd ξ₀ σ₀` and `x ≥ 0`, with `Δ = θ₀ - θ`,

    `|ℓ(θ₀, x) - ℓ(θ, x) - ∇ℓ(θ, x)·Δ - ½ Δᵀ H(θ₀, x) Δ| ≤ K ρ(θ)³ (1 + log(1 + ξ₀ x/σ₀))`,

  where `ρ(θ) = |ξ - ξ₀| + |σ - σ₀|` and `K` is the Lipschitz constant of the Hessian from
  `exists_gpdHess_lipschitz`. The expansion is taken *around `θ`*, so the first-order term
  vanishes at a root of the likelihood equations, while the quadratic term uses the Hessian at
  the fixed point `θ₀`, whose empirical means obey the strong law.
* `abs_gpdLogLikN_expansion_le`: the same for the log-likelihood of a sample.

The proof applies the mean value inequality twice to
`g(s) = f(s) - f(0) - s f'(0) - s² Q/2`, `f(s) = ℓ(θ + sΔ, x)`, using
`|f''(s) - Q| ≤ K ρ³ (1 + log(1 + ξ₀ x/σ₀))` on `[0, 1]`.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §2.6.5–2.6.6.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §16.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### The log-likelihood of the first `n` observations -/

/-- The log-likelihood `∑_{i<n} log g_{ξ,σ}(xᵢ)` of the first `n` observations of a sequence. -/
noncomputable def gpdLogLikN (ξ σ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, log (gpdDensity ξ σ (x i))

/-- The GPD density is jointly measurable in the parameters and the observation. -/
lemma measurable_gpdDensity₃ :
    Measurable fun q : ℝ × ℝ × ℝ => gpdDensity q.1 q.2.1 q.2.2 := by
  unfold gpdDensity
  refine Measurable.ite ?_ (Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    (by fun_prop) (by fun_prop)) measurable_const
  exact (measurableSet_le measurable_const (by fun_prop)).inter
    (measurableSet_lt measurable_const (by fun_prop))

/-- The log-likelihood of the first `n` observations is jointly measurable. -/
lemma measurable_gpdLogLikN (n : ℕ) :
    Measurable fun q : (ℝ × ℝ) × (ℕ → ℝ) => gpdLogLikN q.1.1 q.1.2 q.2 n := by
  unfold gpdLogLikN
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_gpdDensity₃.comp (f := fun q : (ℝ × ℝ) × (ℕ → ℝ) => (q.1.1, q.1.2, q.2 i))
    (by fun_prop)).log

/-! ### The log-density along a line -/

section Line

variable {ξ σ a b x s : ℝ}

/-- The derivative of the log-density along the line `s ↦ (ξ + s a, σ + s b)` is
`a ∂_ξ ℓ + b ∂_σ ℓ`. -/
theorem hasDerivAt_log_gpdDensity_line (hξ : ξ + s * a ≠ 0) (hσ : 0 < σ + s * b) (hx : 0 ≤ x)
    (hu : 0 < (σ + s * b) + (ξ + s * a) * x) :
    HasDerivAt (fun s => log (gpdDensity (ξ + s * a) (σ + s * b) x))
      (a * gpdScoreXi (ξ + s * a) (σ + s * b) x + b * gpdScoreSigma (ξ + s * a) (σ + s * b) x)
      s := by
  have hu' := one_add_mul_div_pos hσ hu
  have hev : (fun t => log (gpdDensity (ξ + t * a) (σ + t * b) x)) =ᶠ[𝓝 s]
      fun t => -log (σ + t * b) -
        (1 / (ξ + t * a) + 1) * log (1 + (ξ + t * a) * x / (σ + t * b)) := by
    have hc1 : Continuous fun t : ℝ => ξ + t * a := by fun_prop
    have hc2 : Continuous fun t : ℝ => σ + t * b := by fun_prop
    have hc3 : Continuous fun t : ℝ => (σ + t * b) + (ξ + t * a) * x := by fun_prop
    filter_upwards [hc1.continuousAt.eventually (isOpen_ne.mem_nhds hξ),
      hc2.continuousAt.eventually (lt_mem_nhds hσ),
      hc3.continuousAt.eventually (lt_mem_nhds hu)] with t h1 h2 h3
    exact log_gpdDensity h2 h1 hx (one_add_mul_div_pos h2 h3)
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hA : HasDerivAt (fun s => ξ + s * a) a s := by
    simpa using ((hasDerivAt_id s).mul_const a).const_add ξ
  have hB : HasDerivAt (fun s => σ + s * b) b s := by
    simpa using ((hasDerivAt_id s).mul_const b).const_add σ
  have hR : HasDerivAt (fun s => (ξ + s * a) * x / (σ + s * b))
      ((a * x * (σ + s * b) - (ξ + s * a) * x * b) / (σ + s * b) ^ 2) s :=
    (hA.mul_const x).div hB hσ.ne'
  have hL := (hR.const_add 1).log hu'.ne'
  have hI : HasDerivAt (fun s => 1 / (ξ + s * a) + 1) (-(a / (ξ + s * a) ^ 2)) s := by
    have := (hA.inv hξ).add_const 1
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => by simp [one_div])
  have := ((hB.log hσ.ne').neg).sub (hI.mul hL)
  refine this.congr_deriv ?_
  unfold gpdScoreXi gpdScoreSigma
  generalize ξ + s * a = p at hξ hu hu' ⊢
  generalize σ + s * b = q at hσ hu hu' ⊢
  generalize log (1 + p * x / q) = L
  have := hσ.ne'
  have h1 : q + p * x ≠ 0 := hu.ne'
  have h2 : x * p + q ≠ 0 := by rw [add_comm, mul_comm]; exact h1
  have h3 : p * x + q ≠ 0 := by rw [add_comm]; exact h1
  have h4 : q + x * p ≠ 0 := by rw [mul_comm]; exact h1
  field_simp
  ring

end Line

/-! ### The second-order expansion -/

section Expansion

variable {ξ₀ σ₀ : ℝ}

/-- The Hessian quadratic form `Δᵀ H(ξ, σ; x) Δ`, `Δ = (a, b)`. -/
noncomputable def gpdHessQuad (ξ σ a b x : ℝ) : ℝ :=
  a ^ 2 * gpdHessXiXi ξ σ x + 2 * a * b * gpdHessXiSigma ξ σ x +
    b ^ 2 * gpdHessSigmaSigma ξ σ x

lemma abs_quad_le {a b e₁ e₂ e₃ E : ℝ} (h₁ : |e₁| ≤ E) (h₂ : |e₂| ≤ E) (h₃ : |e₃| ≤ E) :
    |a ^ 2 * e₁ + 2 * a * b * e₂ + b ^ 2 * e₃| ≤ (|a| + |b|) ^ 2 * E := by
  have hE : 0 ≤ E := (abs_nonneg _).trans h₁
  calc |a ^ 2 * e₁ + 2 * a * b * e₂ + b ^ 2 * e₃|
      ≤ |a ^ 2 * e₁| + |2 * a * b * e₂| + |b ^ 2 * e₃| := abs_add_three _ _ _
    _ = |a| ^ 2 * |e₁| + 2 * |a| * |b| * |e₂| + |b| ^ 2 * |e₃| := by
        simp only [abs_mul, abs_pow, abs_two]
    _ ≤ |a| ^ 2 * E + 2 * |a| * |b| * E + |b| ^ 2 * E := by gcongr
    _ = (|a| + |b|) ^ 2 * E := by ring

variable (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
include hξ₀ hσ₀

/-- **Second-order expansion of the GPD log-density around `θ`, with the Hessian at `θ₀`.**
Given the Lipschitz control `hK` of the Hessian (`exists_gpdHess_lipschitz`), for
`θ ∈ gpdNbhd ξ₀ σ₀`, `x ≥ 0` and `Δ = θ₀ - θ = (a, b)`,

  `|ℓ(θ₀, x) - ℓ(θ, x) - (a ∂_ξ ℓ(θ, x) + b ∂_σ ℓ(θ, x)) - ½ Δᵀ H(θ₀, x) Δ|`
  `  ≤ K ρ(θ)³ (1 + log(1 + ξ₀ x/σ₀))`. -/
theorem abs_log_gpdDensity_expansion_le {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x →
      |gpdHessXiXi θ.1 θ.2 x - gpdHessXiXi ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessXiSigma θ.1 θ.2 x - gpdHessXiSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessSigmaSigma θ.1 θ.2 x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)))
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) :
    |log (gpdDensity ξ₀ σ₀ x) - log (gpdDensity θ.1 θ.2 x) -
        ((ξ₀ - θ.1) * gpdScoreXi θ.1 θ.2 x + (σ₀ - θ.2) * gpdScoreSigma θ.1 θ.2 x) -
        gpdHessQuad ξ₀ σ₀ (ξ₀ - θ.1) (σ₀ - θ.2) x / 2| ≤
      K * gpdDist ξ₀ σ₀ θ ^ 3 * (1 + log (1 + ξ₀ * x / σ₀)) := by
  set a := ξ₀ - θ.1 with ha
  set b := σ₀ - θ.2 with hb
  set L := 1 + log (1 + ξ₀ * x / σ₀) with hL
  set ρ := gpdDist ξ₀ σ₀ θ with hρ
  have hL0 : 0 ≤ L := by have := log_one_add_nonneg hξ₀ hσ₀ hx; linarith
  have hρab : ρ = |a| + |b| := by
    simp only [hρ, gpdDist, ha, hb, abs_sub_comm]
  -- the segment from `θ` to `θ₀`
  have hpt : ∀ s : ℝ, (θ.1 + s * a, θ.2 + s * b) =
      (ξ₀ + (1 - s) * (θ.1 - ξ₀), σ₀ + (1 - s) * (θ.2 - σ₀)) := fun s => by
    simp only [ha, hb]; ext <;> ring
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, (θ.1 + s * a, θ.2 + s * b) ∈ gpdNbhd ξ₀ σ₀ := fun s hs => by
    rw [hpt]
    exact segment_mem_gpdNbhd hξ₀ hσ₀ hθ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hdist : ∀ s ∈ Icc (0 : ℝ) 1, gpdDist ξ₀ σ₀ (θ.1 + s * a, θ.2 + s * b) ≤ ρ := fun s hs => by
    rw [hpt]
    exact gpdDist_segment θ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < θ.1 + s * a ∧ 0 < θ.2 + s * b ∧
      0 < (θ.2 + s * b) + (θ.1 + s * a) * x := fun s hs => by
    obtain ⟨h1, -, h3, -⟩ := pos_of_mem_gpdNbhd (hmem s hs)
    simp only at h1 h3
    have h5 : 0 < θ.1 + s * a := by linarith
    have h6 : 0 < θ.2 + s * b := by linarith
    exact ⟨h5, h6, by positivity⟩
  -- the derivatives
  set F : ℝ → ℝ := fun s => log (gpdDensity (θ.1 + s * a) (θ.2 + s * b) x)
  set F' : ℝ → ℝ := fun s => a * gpdScoreXi (θ.1 + s * a) (θ.2 + s * b) x +
    b * gpdScoreSigma (θ.1 + s * a) (θ.2 + s * b) x
  set F'' : ℝ → ℝ := fun s => gpdHessQuad (θ.1 + s * a) (θ.2 + s * b) a b x
  set Q := gpdHessQuad ξ₀ σ₀ a b x
  have hF : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' s) s := fun s hs => by
    obtain ⟨h1, h2, h3⟩ := hpos s hs
    exact hasDerivAt_log_gpdDensity_line h1.ne' h2 hx h3
  have hF' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F' (F'' s) s := fun s hs => by
    obtain ⟨h1, h2, h3⟩ := hpos s hs
    have := ((hasDerivAt_gpdScoreXi_line h1.ne' h2 h3).const_mul a).add
      ((hasDerivAt_gpdScoreSigma_line (ξ := θ.1) (a := a) h2 h3).const_mul b)
    refine this.congr_deriv ?_
    simp only [F'', gpdHessQuad]
    ring
  set M := K * ρ ^ 3 * L
  have hF''Q : ∀ s ∈ Icc (0 : ℝ) 1, |F'' s - Q| ≤ M := fun s hs => by
    obtain ⟨h1, h2, h3⟩ := hK _ (hmem s hs) x hx
    have hmono : K * gpdDist ξ₀ σ₀ (θ.1 + s * a, θ.2 + s * b) * L ≤ K * ρ * L := by
      gcongr
      exact hdist s hs
    have e : F'' s - Q = a ^ 2 * (gpdHessXiXi (θ.1 + s * a) (θ.2 + s * b) x -
        gpdHessXiXi ξ₀ σ₀ x) + 2 * a * b * (gpdHessXiSigma (θ.1 + s * a) (θ.2 + s * b) x -
        gpdHessXiSigma ξ₀ σ₀ x) + b ^ 2 * (gpdHessSigmaSigma (θ.1 + s * a) (θ.2 + s * b) x -
        gpdHessSigmaSigma ξ₀ σ₀ x) := by
      simp only [F'', Q, gpdHessQuad]; ring
    rw [e]
    refine (abs_quad_le (h₁.trans hmono) (h₂.trans hmono) (h₃.trans hmono)).trans (le_of_eq ?_)
    rw [← hρab]; ring
  -- first mean value inequality: `|F'(s) - F'(0) - s Q| ≤ M s`
  set G' : ℝ → ℝ := fun s => F' s - F' 0 - s * Q
  have hG'd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt G' (F'' s - Q) (Icc 0 1) s := fun s hs => by
    have := (((hF' s hs).sub_const (F' 0)).sub ((hasDerivAt_id s).mul_const Q))
    refine (this.congr_deriv (by simp)).hasDerivWithinAt
  have hG' := norm_image_sub_le_of_norm_deriv_le_segment' hG'd
    (fun s hs => by rw [Real.norm_eq_abs]; exact hF''Q s (Ico_subset_Icc_self hs))
  have hG'0 : G' 0 = 0 := by simp [G']
  -- second mean value inequality
  set G : ℝ → ℝ := fun s => F s - F 0 - s * F' 0 - s ^ 2 / 2 * Q
  have hGd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt G (G' s) (Icc 0 1) s := fun s hs => by
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * Q) (s * Q) s := by
      have := (((hasDerivAt_id s).pow 2).div_const 2).mul_const Q
      refine this.congr_deriv ?_
      simp; ring
    have := (((hF s hs).sub_const (F 0)).sub ((hasDerivAt_id s).mul_const (F' 0))).sub h2
    exact (this.congr_deriv (by simp [G'])).hasDerivWithinAt
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hF''Q 0 ⟨le_rfl, zero_le_one⟩)
  have hG := norm_image_sub_le_of_norm_deriv_le_segment' hGd
    (C := M) (fun s hs => by
      have := hG' s (Ico_subset_Icc_self hs)
      rw [hG'0, sub_zero, sub_zero] at this
      rw [Real.norm_eq_abs] at this ⊢
      exact this.trans (by nlinarith [hs.1, hs.2]))
    1 ⟨zero_le_one, le_rfl⟩
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0, sub_zero, sub_zero, mul_one, Real.norm_eq_abs] at hG
  have e1 : F 1 = log (gpdDensity ξ₀ σ₀ x) := by simp [F, ha, hb]
  have e0 : F 0 = log (gpdDensity θ.1 θ.2 x) := by simp [F]
  have e' : F' 0 = a * gpdScoreXi θ.1 θ.2 x + b * gpdScoreSigma θ.1 θ.2 x := by simp [F']
  simp only [G, e1, e0, e', one_pow, one_mul] at hG
  convert hG using 2
  ring

end Expansion

end ExtremeValueTheory
