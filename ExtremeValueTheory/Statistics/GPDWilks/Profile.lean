/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDWilks.Deviance

/-!
# Wilks' theorem for the GPD, `ξ₀ > 0`

The deviance at the true parameter converges to `χ²₂`, and the profile deviance at the true value
of a one-dimensional interest parameter converges to `χ²₁` ([Coles, §2.6.5–2.6.6]).

The score form `Sₙᵀ I⁻¹ Sₙ` is whitened with an explicit square root of `I⁻¹`, which gives `χ²₂`
from the bivariate score CLT, while the difference `Sₙᵀ I⁻¹ Sₙ - (t · Sₙ)²/(tᵀ I t)` is the square
of one standardized linear combination of the score, which gives `χ²₁` from the scalar score CLT.

## Main results

* `tendstoInDistribution_gpdDeviance`: `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₂`.
* `tendstoInDistribution_gpdProfileDeviance`: `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ̃ₙ)) ⇒ χ²₁`, with `θ̃ₙ` the
  maximizer on the level set of the interest parameter.
* `IsGPDProfileChart`, with the explicit charts `isGPDProfileChart_shape`,
  `isGPDProfileChart_scale`, `isGPDProfileChart_returnLevel`.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §2.6.5–2.6.6, §4.3.3.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §16.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Asymptotics

namespace ExtremeValueTheory

/-! ### Wilks' theorem -/

section Wilks

open RealInnerProductSpace Matrix

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {ξ₀ σ₀ : ℝ}

/-- Convergence in distribution depends on the limit only through its law. -/
lemma tendstoInDistribution_congr_limit {E Ω₁ : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {mΩ₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {Y : ℕ → Ω → E} {W : Ω₁ → E} {Z : Ω' → E} {μ : Measure E}
    (h : TendstoInDistribution Y atTop W (fun _ => P) P₁) (hW : HasLaw W μ P₁)
    (hZ : HasLaw Z μ P') : TendstoInDistribution Y atTop Z (fun _ => P) P' := by
  refine ⟨h.forall_aemeasurable, hZ.aemeasurable, ?_⟩
  have := h.tendsto
  simp only [hW.map_eq] at this
  simpa only [hZ.map_eq] using this

/-- `n^{-1/2} ∑ (c₁ ∂_ξ ℓ + c₂ ∂_σ ℓ)(Xᵢ) = c₁ S₁ + c₂ S₂`. -/
private lemma lin_score_eq (c₁ c₂ : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (c₁ * gpdScoreXi ξ₀ σ₀ (x i) + c₂ * gpdScoreSigma ξ₀ σ₀ (x i)) =
      c₁ * gpdNormScoreXi ξ₀ σ₀ x n + c₂ * gpdNormScoreSigma ξ₀ σ₀ x n := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, gpdNormScoreXi, gpdNormScoreSigma]
  ring

/-- The squared score statistic: `Sₙᵀ I(θ₀)⁻¹ Sₙ ⇒ χ²₂`, by whitening the bivariate CLT for the
score with an explicit square root of `I(θ₀)⁻¹`. -/
theorem tendstoInDistribution_gpdInfoInvQuad (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (chiSquared 2) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        gpdInfoInvQuad ξ₀ σ₀ (gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n)
          (gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n)) atTop Z (fun _ => P) P' := by
  have hξ : -1 / 2 < ξ₀ := by linarith
  have h2 : 0 < 1 + 2 * ξ₀ := by linarith
  set w := √(1 + 2 * ξ₀) with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 h2
  have hw2 : w ^ 2 = 1 + 2 * ξ₀ := Real.sq_sqrt h2.le
  have hQ : ∀ t : Fin 2 → ℝ, gpdInfoQuad ξ₀ σ₀ (t 0 * (1 + ξ₀) + t 1 * 0)
      (t 0 * -σ₀ + t 1 * (σ₀ * w)) = t ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ t := fun t => by
    have h1 : 1 + ξ₀ ≠ 0 := by linarith
    simp only [gpdInfoQuad, Matrix.one_mulVec, dotProduct, Fin.sum_univ_two, ← hw2]
    have := hσ₀.ne'
    field_simp
    have hw2' : ξ₀ = (w ^ 2 - 1) / 2 := by linarith
    rw [hw2']
    ring
  set E2 := EuclideanSpace ℝ (Fin 2)
  have hW : HasLaw (id : E2 → E2) (multivariateGaussian 0 1) (multivariateGaussian 0 1) := HasLaw.id
  have hV := tendstoInDistribution_gpdScoreLin hξ hξ₀.ne' hσ₀ hX hind (1 + ξ₀) (-σ₀) 0 (σ₀ * w)
    Matrix.PosSemidef.one hQ hW
  have hsq := hV.continuous_comp (g := fun v : E2 => ‖v‖ ^ 2) (by fun_prop)
  have hsqL : HasLaw ((fun v : E2 => ‖v‖ ^ 2) ∘ id) (chiSquared 2) (multivariateGaussian (0 : E2) 1) := by
    have : HasLaw (id : E2 → E2) (stdGaussian E2) (multivariateGaussian (0 : E2) 1) := by
      rw [multivariateGaussian_zero_one]; exact HasLaw.id
    exact this.norm_sq_chiSquared
  have hfin := tendstoInDistribution_congr_limit hsq hsqL hZ
  convert hfin using 2 with n
  funext ω
  have e0 : ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
      gpdScoreLin (1 + ξ₀) (-σ₀) 0 (σ₀ * w) ξ₀ σ₀ (X i ω)) 0 =
      (1 + ξ₀) * gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n +
        -σ₀ * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n := by
    rw [← lin_score_eq]
    simp [gpdScoreLin, Finset.sum_apply]
  have e1 : ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
      gpdScoreLin (1 + ξ₀) (-σ₀) 0 (σ₀ * w) ξ₀ σ₀ (X i ω)) 1 =
      0 * gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n +
        (σ₀ * w) * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n := by
    rw [← lin_score_eq]
    simp [gpdScoreLin, Finset.sum_apply]
  simp only [Function.comp_apply]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, e0, e1, gpdInfoInvQuad]
  have hξw : ξ₀ = (w ^ 2 - 1) / 2 := by linarith
  generalize gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n = S₁
  generalize gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n = S₂
  rw [hξw]
  ring

/-- **Wilks' theorem for the GPD, full parameter, roots of the likelihood equations** ([Coles,
§2.6.5]; [van der Vaart, §16]). For iid `GPD(ξ₀, σ₀)`, `ξ₀ > 0`, and measurable,
strongly consistent roots `θ̂ₙ` of the likelihood equations,

  `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₂`. -/
theorem tendstoInDistribution_gpdDeviance_of_root (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 2) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n)) atTop Z (fun _ => P) P' := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z
    (tendstoInDistribution_gpdInfoInvQuad hξ₀ hσ₀ hX hind hZ)
    (tendstoInMeasure_gpdDeviance_sub hξ₀ hσ₀ hX hind hθm hcons hroot) fun n => ?_
  have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
  have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (ξ₀, σ₀)) hX aemeasurable_const n
  simp only at h2
  fun_prop

/-- The `2 × 2` identity behind the profile: for `d = A C - B²`, `c = A t₁² + 2 B t₁ t₂ + C t₂²`,
the score form `SᵀI⁻¹S` minus its part along `t` is a perfect square. -/
private lemma quad_sub_eq_sq {A B C t₁ t₂ S₁ S₂ : ℝ} (hd : A * C - B ^ 2 ≠ 0)
    (hc : A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2 ≠ 0) :
    (C * S₁ ^ 2 - 2 * B * S₁ * S₂ + A * S₂ ^ 2) / (A * C - B ^ 2) -
        (t₁ * S₁ + t₂ * S₂) ^ 2 / (A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2) =
      ((B * t₁ + C * t₂) * S₁ - (A * t₁ + B * t₂) * S₂) ^ 2 /
        ((A * C - B ^ 2) * (A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2)) := by
  rw [div_sub_div _ _ hd hc]
  congr 1
  ring

/-- **The profile score statistic.** With `t ≠ 0` and `Sₙ` the normalized score at `θ₀`, there is
a pair of coefficients `(c₁, c₂)` with `c₁ S₁ + c₂ S₂ ⇒ N(0, 1)` and

  `Sₙᵀ I⁻¹ Sₙ - (t · Sₙ)² / (tᵀ I t) = (c₁ S₁ + c₂ S₂)²`,

so this difference converges in distribution to `χ²₁`. -/
theorem tendstoInDistribution_gpdInfoInvQuad_sub (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) {t₁ t₂ : ℝ}
    (ht : t₁ ≠ 0 ∨ t₂ ≠ 0) {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        gpdInfoInvQuad ξ₀ σ₀ (gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n)
            (gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) -
          (t₁ * gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n +
            t₂ * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) ^ 2 / gpdInfoQuad ξ₀ σ₀ t₁ t₂)
      atTop Z (fun _ => P) P' := by
  have hξ : -1 / 2 < ξ₀ := by linarith
  obtain ⟨hd, hJ₁₁, hJ₁₂, hJ₂₂⟩ := gpdFisherInfo_det_adj hξ hσ₀
  have hc := gpdInfoQuad_pos hξ hσ₀ ht
  set A := 2 / ((1 + ξ₀) * (1 + 2 * ξ₀)) with hA
  set B := 1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀)) with hB
  set C := 1 / (σ₀ ^ 2 * (1 + 2 * ξ₀)) with hC
  have hd' : 0 < A * C - B ^ 2 := hd
  have hq : gpdInfoQuad ξ₀ σ₀ t₁ t₂ = A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2 := by
    unfold gpdInfoQuad; ring
  rw [hq] at hc
  set c := A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2 with hcdef
  set u := √((A * C - B ^ 2) * c) with hu
  have hu2 : u ^ 2 = (A * C - B ^ 2) * c := Real.sq_sqrt (mul_pos hd' hc).le
  have hu0 : 0 < u := Real.sqrt_pos.2 (mul_pos hd' hc)
  set c₁ := (B * t₁ + C * t₂) / u with hc₁
  set c₂ := -(A * t₁ + B * t₂) / u with hc₂
  have hvar : gpdInfoQuad ξ₀ σ₀ c₁ c₂ = 1 := by
    have : gpdInfoQuad ξ₀ σ₀ c₁ c₂ =
        (A * (B * t₁ + C * t₂) ^ 2 - 2 * B * (B * t₁ + C * t₂) * (A * t₁ + B * t₂) +
          C * (A * t₁ + B * t₂) ^ 2) / u ^ 2 := by
      unfold gpdInfoQuad
      simp only [hc₁, hc₂, ← hA, ← hB, ← hC]
      field_simp
      ring
    rw [this, hu2, div_eq_one_iff_eq (mul_pos hd' hc).ne', hcdef]
    ring
  have hN : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (gpdInfoQuad ξ₀ σ₀ c₁ c₂).toNNReal)
      (gaussianReal 0 1) := by
    rw [hvar, Real.toNNReal_one]; exact HasLaw.id
  have hclt := tendstoInDistribution_lin_score hξ hξ₀.ne' hσ₀ hX hind c₁ c₂ hN
  have hsq := hclt.continuous_comp (g := fun x : ℝ => x ^ 2) (by fun_prop)
  have hsqL : HasLaw ((fun x : ℝ => x ^ 2) ∘ id) (chiSquared 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, by rw [chiSquared_one_eq_map]; rfl⟩
  have hfin := tendstoInDistribution_congr_limit hsq hsqL hZ
  convert hfin using 2 with n
  funext ω
  simp only [Function.comp_apply]
  rw [lin_score_eq, gpdInfoInvQuad, hq]
  generalize gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n = S₁
  generalize gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n = S₂
  have e := quad_sub_eq_sq (A := A) (B := B) (C := C) (t₁ := t₁) (t₂ := t₂) (S₁ := S₁) (S₂ := S₂)
    hd'.ne' hc.ne'
  have e2 := quad_div_eq_of_div_eq (s₁ := S₁) (s₂ := S₂) hJ₁₁ hJ₁₂ hJ₂₂
  have e3 : (1 + ξ₀) * ((1 + ξ₀) * S₁ ^ 2 - 2 * σ₀ * S₁ * S₂ + 2 * σ₀ ^ 2 * S₂ ^ 2) =
      (C * S₁ ^ 2 - 2 * B * S₁ * S₂ + A * S₂ ^ 2) / (A * C - B ^ 2) := by
    rw [show (C * S₁ ^ 2 - 2 * B * S₁ * S₂ + A * S₂ ^ 2) / (A * C - B ^ 2) = _ from e2]
    ring
  rw [e3, e, ← hu2]
  simp only [hc₁, hc₂]
  have := hu0.ne'
  field_simp
  ring

/-- **Wilks' theorem for a one-dimensional interest parameter, along a curve** ([Coles, §2.6.6];
[van der Vaart, §16]). Let `θ̂ₙ` be measurable, strongly consistent
roots of the likelihood equations, and `θ̃ₙ` measurable restricted estimators stationary along a
curve through `θ₀` as in `tendstoInMeasure_gpdCurveDeviance_sub`. Then

  `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ̃ₙ)) ⇒ χ²₁`. -/
theorem tendstoInDistribution_gpdCurveDeviance (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0)
    {γ₁ γ₂ t₁ t₂ : ℝ → ℝ} {s₀ : ℝ} (hγ₁ : HasDerivAt γ₁ (t₁ s₀) s₀) (hγ₂ : HasDerivAt γ₂ (t₂ s₀) s₀)
    (ht₁ : ContinuousAt t₁ s₀) (ht₂ : ContinuousAt t₂ s₀) (hs₁ : γ₁ s₀ = ξ₀) (hs₂ : γ₂ s₀ = σ₀)
    (hne : t₁ s₀ ≠ 0 ∨ t₂ s₀ ≠ 0)
    {θt : ℕ → Ω → ℝ × ℝ} (hθtm : ∀ n, AEMeasurable (θt n) P)
    (hcurve : ∀ᵐ ω ∂P, ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 s₀) ∧ ∀ᶠ n in atTop,
      θt n ω = (γ₁ (s n), γ₂ (s n)) ∧
      t₁ (s n) * ∑ i ∈ Finset.range n, gpdScoreXi (θt n ω).1 (θt n ω).2 (X i ω) +
        t₂ (s n) * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) = 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n)) atTop Z (fun _ => P) P' := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z
    (tendstoInDistribution_gpdInfoInvQuad_sub hξ₀ hσ₀ hX hind hne hZ) ?_ fun n => ?_
  · have h1 := tendstoInMeasure_gpdDeviance_sub hξ₀ hσ₀ hX hind hθm hcons hroot
    have h2 := tendstoInMeasure_gpdCurveDeviance_sub hξ₀ hσ₀ hX hind hγ₁ hγ₂ ht₁ ht₂ hs₁ hs₂ hne
      hθtm hcurve
    have := tendstoInMeasure_comp₂ h1 h2 (φ := fun p => p.1 - p.2) continuous_sub.continuousAt
    simp only [sub_zero] at this
    convert this using 2 with n
    funext ω
    simp only [Pi.sub_apply]
    ring
  · have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
    have h2 := aemeasurable_gpdLogLikN hX (hθtm n) n
    fun_prop

end Wilks

/-! ### Maximum likelihood over a compact set; profile likelihood -/

section Profile

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {ξ₀ σ₀ : ℝ}

omit [IsProbabilityMeasure P] in
/-- `θ̂ₙ` maximizing over `K` are strongly consistent and eventually solve the likelihood equations,
when `θ₀` is interior to `K`. -/
theorem ae_consistent_root_of_isMaxOn {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω)) :
    (∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀))) ∧
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0 := by
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)) := by
    filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
    refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have := hmax n ω (interior_subset hθ₀)
    simp only [mem_ofPred_eq] at this
    simpa using this
  refine ⟨hcons, ?_⟩
  filter_upwards [ae_forall_pos_of_gpd hσ₀ hX, hcons] with ω hω hc
  filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
    hc.eventually (gpdNbhd_mem_nhds hξ₀ hσ₀)] with n h1 h2
  obtain ⟨h3, -, h4, -⟩ := pos_of_mem_gpdNbhd h2
  have := score_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) (fun i => (hω i).le) h1
    (by linarith) (by linarith) (hmax n ω)
  rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω)) n,
    Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n] at this
  exact this

/-- **Wilks' theorem for the GPD, full parameter** ([Coles, §2.6.5]; [van der Vaart, §16]). Let
`K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, σ₀)`, `ξ₀ > 0`, in its interior, let `X₀, X₁, …` be
iid `GPD(θ₀)`, and let `θ̂ₙ` be measurable maximizers of the log-likelihood over `K`. The deviance
converges in distribution to `χ²₂`:

  `D(θ₀) = 2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₂`. -/
theorem tendstoInDistribution_gpdDeviance {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 2) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n)) atTop Z (fun _ => P) P' :=
  have h := ae_consistent_root_of_isMaxOn hK hKS hθ₀ hξ₀ hσ₀ hX hind hθK hmax
  tendstoInDistribution_gpdDeviance_of_root hξ₀ hσ₀ hX hind hθm h.1 h.2 hZ

/-- A **local chart of a level set** of the interest parameter `g` through `θ₀ = (ξ₀, σ₀)`: near
`θ₀` the level set `{g = g θ₀}` is the image of the curve `γ = (γ₁, γ₂)` (with left inverse `φ`,
continuous at `θ₀`), which passes through `θ₀ = γ(s₀)`, stays in the level set near `s₀`, and is
differentiable near `s₀` with derivative `(t₁, t₂)` continuous at `s₀` and nonzero at `s₀`.
This is what "the interest parameter is a smooth function with nonzero gradient" provides through
the implicit function theorem; we do not formalize that step, and instead give explicit charts for
the shape, the scale and the return level. -/
structure IsGPDProfileChart (g : ℝ × ℝ → ℝ) (ξ₀ σ₀ s₀ : ℝ) (φ : ℝ × ℝ → ℝ)
    (γ₁ γ₂ t₁ t₂ : ℝ → ℝ) : Prop where
  map_true : φ (ξ₀, σ₀) = s₀
  continuousAt : ContinuousAt φ (ξ₀, σ₀)
  curve_chart : ∀ᶠ p in 𝓝 (ξ₀, σ₀), g p = g (ξ₀, σ₀) → (γ₁ (φ p), γ₂ (φ p)) = p
  level : ∀ᶠ s in 𝓝 s₀, g (γ₁ s, γ₂ s) = g (ξ₀, σ₀)
  hasDerivAt₁ : ∀ᶠ s in 𝓝 s₀, HasDerivAt γ₁ (t₁ s) s
  hasDerivAt₂ : ∀ᶠ s in 𝓝 s₀, HasDerivAt γ₂ (t₂ s) s
  continuousAt₁ : ContinuousAt t₁ s₀
  continuousAt₂ : ContinuousAt t₂ s₀
  tangent_ne : t₁ s₀ ≠ 0 ∨ t₂ s₀ ≠ 0

/-- The shape as interest parameter: the level set `{ξ = ξ₀}` is parametrized by the scale. -/
theorem isGPDProfileChart_shape (ξ₀ σ₀ : ℝ) :
    IsGPDProfileChart Prod.fst ξ₀ σ₀ σ₀ Prod.snd (fun _ => ξ₀) id (fun _ => 0) (fun _ => 1) where
  map_true := rfl
  continuousAt := continuousAt_snd
  curve_chart := Eventually.of_forall fun _ hp => Prod.ext hp.symm rfl
  level := Eventually.of_forall fun _ => rfl
  hasDerivAt₁ := Eventually.of_forall fun s => hasDerivAt_const s ξ₀
  hasDerivAt₂ := Eventually.of_forall fun s => hasDerivAt_id s
  continuousAt₁ := continuousAt_const
  continuousAt₂ := continuousAt_const
  tangent_ne := Or.inr one_ne_zero

/-- The scale as interest parameter: the level set `{σ = σ₀}` is parametrized by the shape. -/
theorem isGPDProfileChart_scale (ξ₀ σ₀ : ℝ) :
    IsGPDProfileChart Prod.snd ξ₀ σ₀ ξ₀ Prod.fst id (fun _ => σ₀) (fun _ => 1) (fun _ => 0) where
  map_true := rfl
  continuousAt := continuousAt_fst
  curve_chart := Eventually.of_forall fun _ hp => Prod.ext rfl hp.symm
  level := Eventually.of_forall fun _ => rfl
  hasDerivAt₁ := Eventually.of_forall fun s => hasDerivAt_id s
  hasDerivAt₂ := Eventually.of_forall fun s => hasDerivAt_const s σ₀
  continuousAt₁ := continuousAt_const
  continuousAt₂ := continuousAt_const
  tangent_ne := Or.inl one_ne_zero

/-- The POT return level as interest parameter: when `N ζ > 1` the Box–Cox factor is positive, and
the level set `{x_N = ψ₀}` is the graph `σ = (ψ₀ - u)/h_ξ(N ζ)` over the shape ([Coles, §4.3.3]). -/
theorem isGPDProfileChart_returnLevel {ξ₀ σ₀ u ζ N : ℝ} (hξ₀ : ξ₀ ≠ 0) (hNζ : 1 < N * ζ) :
    IsGPDProfileChart (fun p => gpdReturnLevel u p.1 p.2 ζ N) ξ₀ σ₀ ξ₀ Prod.fst id
      (fun s => σ₀ * boxCox ξ₀ (N * ζ) / boxCox s (N * ζ)) (fun _ => 1)
      (fun s => -(σ₀ * boxCox ξ₀ (N * ζ)) * boxCoxShapeDeriv s (N * ζ) / boxCox s (N * ζ) ^ 2) where
  map_true := rfl
  continuousAt := continuousAt_fst
  curve_chart := Eventually.of_forall fun p hp => by
    have hb := boxCox_pos_of_one_lt (ρ := p.1) hNζ
    simp only [gpdReturnLevel, add_right_inj] at hp
    refine Prod.ext rfl ?_
    rw [← hp]
    field_simp
  level := Eventually.of_forall fun s => by
    have hb := boxCox_pos_of_one_lt (ρ := s) hNζ
    simp only [gpdReturnLevel, id, add_right_inj]
    field_simp
  hasDerivAt₁ := Eventually.of_forall fun s => hasDerivAt_id s
  hasDerivAt₂ := by
    filter_upwards [isOpen_ne.mem_nhds hξ₀] with s hs
    have hb := boxCox_pos_of_one_lt (ρ := s) hNζ
    have h := (hasDerivAt_boxCox_shape hs (one_pos.trans hNζ)).inv hb.ne'
    have := h.const_mul (σ₀ * boxCox ξ₀ (N * ζ))
    refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => by simp [div_eq_mul_inv])
  continuousAt₁ := continuousAt_const
  continuousAt₂ := by
    have hb := boxCox_pos_of_one_lt (ρ := ξ₀) hNζ
    refine ContinuousAt.div (continuousAt_const.mul
      (continuousAt_boxCoxShapeDeriv hξ₀ (one_pos.trans hNζ)))
      (((continuous_boxCox_shape (one_pos.trans hNζ)).pow 2).continuousAt) (by positivity)
  tangent_ne := Or.inl one_ne_zero

/-- The likelihood is stationary along a curve at a maximizer over a set containing the curve near
the point. -/
theorem curve_score_eq_zero_of_isMaxOn {K' : Set (ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i) {γ₁ γ₂ : ℝ → ℝ} {a b s : ℝ} (h₁ : HasDerivAt γ₁ a s)
    (h₂ : HasDerivAt γ₂ b s) (hp₁ : 0 < γ₁ s) (hp₂ : 0 < γ₂ s)
    (hmem : ∀ᶠ s' in 𝓝 s, (γ₁ s', γ₂ s') ∈ K')
    (hmax : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K' (γ₁ s, γ₂ s)) :
    a * ∑ i, gpdScoreXi (γ₁ s) (γ₂ s) (x i) + b * ∑ i, gpdScoreSigma (γ₁ s) (γ₂ s) (x i) = 0 := by
  have hd : HasDerivAt (fun s => ∑ i, log (gpdDensity (γ₁ s) (γ₂ s) (x i)))
      (∑ i, (a * gpdScoreXi (γ₁ s) (γ₂ s) (x i) + b * gpdScoreSigma (γ₁ s) (γ₂ s) (x i))) s := by
    have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
      hasDerivAt_log_gpdDensity_curve (x := x i) h₁ h₂ hp₁.ne' hp₂ (hx i)
        (by have := hx i; positivity)
    convert this using 1
    funext ξ; simp
  have hloc : IsLocalMax (fun s => ∑ i, log (gpdDensity (γ₁ s) (γ₂ s) (x i))) s := by
    filter_upwards [hmem, h₁.continuousAt.eventually (lt_mem_nhds hp₁),
      h₂.continuousAt.eventually (lt_mem_nhds hp₂)] with s' hs' h1 h2
    have := hmax hs'
    simp only [mem_ofPred_eq] at this
    rw [gpdLogLikE_eq_coe h1 h2 hx, gpdLogLikE_eq_coe hp₁ hp₂ hx] at this
    exact EReal.coe_le_coe_iff.1 this
  have := hloc.hasDerivAt_eq_zero hd
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  exact this

/-- **Wilks' theorem for the profile likelihood of the GPD** ([Coles, §2.6.6]; [van der Vaart, §16]).
Let `K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, σ₀)`, `ξ₀ > 0`, in its interior, let `g` be
continuous on `K` with a chart of the level set through `θ₀` (`IsGPDProfileChart`), let `X₀, X₁, …`
be iid `GPD(θ₀)`, let `θ̂ₙ` be measurable maximizers of the log-likelihood over `K`, and `θ̃ₙ`
measurable maximizers over `K ∩ {g = g θ₀}`. The profile deviance at the true value of the interest
parameter converges to `χ²₁`:

  `D_p(g θ₀) = 2 (ℓₙ(θ̂ₙ) - ℓₙ(θ̃ₙ)) ⇒ χ²₁`. -/
theorem tendstoInDistribution_gpdProfileDeviance {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) {s₀ : ℝ} {φ : ℝ × ℝ → ℝ} {γ₁ γ₂ t₁ t₂ : ℝ → ℝ}
    (hchart : IsGPDProfileChart g ξ₀ σ₀ s₀ φ γ₁ γ₂ t₁ t₂)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {θt : ℕ → Ω → ℝ × ℝ} (hθtm : ∀ n, AEMeasurable (θt n) P)
    (hθtK : ∀ n ω, θt n ω ∈ K ∩ g ⁻¹' {g (ξ₀, σ₀)})
    (hmaxt : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω))
      (K ∩ g ⁻¹' {g (ξ₀, σ₀)}) (θt n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n)) atTop Z (fun _ => P) P' := by
  obtain ⟨hcons, hroot⟩ := ae_consistent_root_of_isMaxOn hK hKS hθ₀ hξ₀ hσ₀ hX hind hθK hmax
  set K' := K ∩ g ⁻¹' {g (ξ₀, σ₀)} with hK'
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    (hg.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton) inter_subset_left
  have hK'S : ∀ p ∈ K', -1 < p.1 ∧ 0 < p.2 := fun p hp => hKS p hp.1
  have hθ₀K' : (ξ₀, σ₀) ∈ K' := ⟨interior_subset hθ₀, rfl⟩
  have hconst : ∀ᵐ ω ∂P, Tendsto (fun n => θt n ω) atTop (𝓝 (ξ₀, σ₀)) := by
    filter_upwards [ae_tendsto_gpdMLE' (θ₀ := (ξ₀, σ₀)) hK'c hK'S hθ₀K' hX hind] with ω hω
    refine hω (fun n => θt n ω) (fun _ => 0) (fun n => hθtK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have := hmaxt n ω hθ₀K'
    simp only [mem_ofPred_eq] at this
    simpa using this
  have hchart₀ := hchart.curve_chart.self_of_nhds rfl
  rw [hchart.map_true] at hchart₀
  have hs₁ : γ₁ s₀ = ξ₀ := congrArg Prod.fst hchart₀
  have hs₂ : γ₂ s₀ = σ₀ := congrArg Prod.snd hchart₀
  have hγ₁ := hchart.hasDerivAt₁.self_of_nhds
  have hγ₂ := hchart.hasDerivAt₂.self_of_nhds
  refine tendstoInDistribution_gpdCurveDeviance hξ₀ hσ₀ hX hind hθm hcons hroot hγ₁ hγ₂
    hchart.continuousAt₁ hchart.continuousAt₂ hs₁ hs₂ hchart.tangent_ne hθtm ?_ hZ
  filter_upwards [ae_forall_pos_of_gpd hσ₀ hX, hconst] with ω hω hc
  have hs : Tendsto (fun n => φ (θt n ω)) atTop (𝓝 s₀) := by
    rw [← hchart.map_true]
    exact hchart.continuousAt.tendsto.comp hc
  refine ⟨fun n => φ (θt n ω), hs, ?_⟩
  filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
    hc.eventually (gpdNbhd_mem_nhds hξ₀ hσ₀),
    hs.eventually hchart.level.eventually_nhds, hs.eventually hchart.hasDerivAt₁.eventually_nhds,
    hs.eventually hchart.hasDerivAt₂.eventually_nhds, hc.eventually hchart.curve_chart]
    with n hint hnb hlev hd₁ hd₂ hch
  have e : θt n ω = (γ₁ (φ (θt n ω)), γ₂ (φ (θt n ω))) := (hch (hθtK n ω).2).symm
  refine ⟨e, ?_⟩
  obtain ⟨h3, -, h4, -⟩ := pos_of_mem_gpdNbhd hnb
  have d₁ := hd₁.self_of_nhds
  have d₂ := hd₂.self_of_nhds
  have hmem : ∀ᶠ s' in 𝓝 (φ (θt n ω)), (γ₁ s', γ₂ s') ∈ K' := by
    have hcont : ContinuousAt (fun s' => (γ₁ s', γ₂ s')) (φ (θt n ω)) :=
      d₁.continuousAt.prodMk d₂.continuousAt
    have hint' : (γ₁ (φ (θt n ω)), γ₂ (φ (θt n ω))) ∈ interior K := by rw [← e]; exact hint
    filter_upwards [hcont.eventually (isOpen_interior.mem_nhds hint'), hlev] with s' h1 h2
    exact ⟨interior_subset h1, h2⟩
  have hmx := hmaxt n ω
  rw [e] at hmx
  have hp₁ : 0 < γ₁ (φ (θt n ω)) := by
    have : (θt n ω).1 = γ₁ (φ (θt n ω)) := congrArg Prod.fst e
    rw [← this]; linarith
  have hp₂ : 0 < γ₂ (φ (θt n ω)) := by
    have : (θt n ω).2 = γ₂ (φ (θt n ω)) := congrArg Prod.snd e
    rw [← this]; linarith
  have := curve_score_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) (fun i => (hω i).le)
    d₁ d₂ hp₁ hp₂ hmem hmx
  rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXi _ _ (X i ω)) n,
    Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma _ _ (X i ω)) n] at this
  rw [show (θt n ω).1 = γ₁ (φ (θt n ω)) from congrArg Prod.fst e,
    show (θt n ω).2 = γ₂ (φ (θt n ω)) from congrArg Prod.snd e]
  exact this

end Profile

end ExtremeValueTheory
