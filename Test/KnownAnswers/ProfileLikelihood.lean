import ExtremeValueTheory

/-!
# Known answers: the chi-squared laws and the profile likelihood objects

Checks of `chiSquared` against textbook values, and of the objects of
`ExtremeValueTheory.Statistics.GPDWilks` against direct computations.

Reference: [Coles] S. Coles, *An Introduction to Statistical Modeling of Extreme Values* (2001).
-/

open Real MeasureTheory ProbabilityTheory ExtremeValueTheory Set Topology

namespace Test.KnownAnswers.ProfileLikelihood

/-- `χ²₁` lives on `[0, ∞)`: a statistic cannot be covered at a negative critical value. Fails if
`chiSquared` were not the law of a square. -/
theorem test_chiSquared_one_neg {c : ℝ} (hc : c < 0) : chiSquared 1 (Iic c) = 0 := by
  rw [chiSquared_one_eq_map, Measure.map_apply (by fun_prop) measurableSet_Iic]
  convert measure_empty (μ := gaussianReal 0 1)
  ext x
  simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
  nlinarith [sq_nonneg x]

/-- `χ²₁((-∞, z²]) = N(0, 1)([-z, z])` ([Coles, §2.6.6]: the `χ²₁` quantile is the square of the
two-sided normal quantile, so `3.84 ≈ 1.96²`). -/
theorem test_chiSquared_one_sq {z : ℝ} (hz : 0 ≤ z) :
    chiSquared 1 (Iic (z ^ 2)) = gaussianReal 0 1 (Icc (-z) z) := by
  rw [chiSquared_one_Iic (by positivity), Real.sqrt_sq hz]

/-- `χ²₂` is the exponential law with mean `2`: at `c = 2`, `1 - e⁻¹`. -/
theorem test_chiSquared_two_two : (chiSquared 2).real (Iic 2) = 1 - exp (-1) := by
  rw [chiSquared_two_real_Iic (by norm_num)]
  norm_num

/-- The tangent `(1, t₂)` recorded in the chart `isGPDProfileChart_returnLevel` is orthogonal to the
gradient of the return level at the true parameter: `∇x_N · t = 0`. The proof differentiates the
return level along the chart's own curve, using the chart's fields `level`, `hasDerivAt₁` and
`hasDerivAt₂`, and the derivative of `boxCox` in the shape. So this fails if the chart recorded a
derivative with the wrong sign or power, or a curve leaving the level set. -/
theorem test_returnLevel_tangent {ξ₀ σ₀ u ζ N : ℝ} (hξ₀ : ξ₀ ≠ 0) (hNζ : 1 < N * ζ) :
    (σ₀ * boxCoxShapeDeriv ξ₀ (N * ζ)) * 1 +
      boxCox ξ₀ (N * ζ) *
        (-(σ₀ * boxCox ξ₀ (N * ζ)) * boxCoxShapeDeriv ξ₀ (N * ζ) / boxCox ξ₀ (N * ζ) ^ 2) = 0 := by
  have hc := isGPDProfileChart_returnLevel (u := u) (σ₀ := σ₀) hξ₀ hNζ
  have hb := boxCox_pos_of_one_lt (ρ := ξ₀) hNζ
  have h₂ := hc.hasDerivAt₂.self_of_nhds
  have hB := hasDerivAt_boxCox_shape hξ₀ (one_pos.trans hNζ)
  have hval : σ₀ * boxCox ξ₀ (N * ζ) / boxCox ξ₀ (N * ζ) = σ₀ := by field_simp
  have hL := ((h₂.mul hB).const_add u)
  have hconst : (fun s => gpdReturnLevel u (id s)
      (σ₀ * boxCox ξ₀ (N * ζ) / boxCox s (N * ζ)) ζ N) =ᶠ[Filter.atTop.map id ⊓ 𝓝 ξ₀]
      fun _ => gpdReturnLevel u ξ₀ σ₀ ζ N := Filter.Eventually.filter_mono inf_le_right hc.level
  have hL' := (hasDerivAt_const ξ₀ (gpdReturnLevel u ξ₀ σ₀ ζ N)).congr_of_eventuallyEq hc.level
  have huniq := hL.unique (by simpa only [gpdReturnLevel, id, Pi.mul_apply] using hL')
  rw [hval] at huniq
  linear_combination huniq

/-- `Sᵀ I⁻¹ S` at `ξ = 0`, `σ = 1`, the exponential case: `I⁻¹ = [[1, -1], [-1, 2]]`. -/
theorem test_gpdInfoInvQuad_exponential (s₁ s₂ : ℝ) :
    gpdInfoInvQuad 0 1 s₁ s₂ = s₁ ^ 2 - 2 * s₁ * s₂ + 2 * s₂ ^ 2 := by
  simp [gpdInfoInvQuad]

/-- `gpdInfoInvQuad` is the quadratic form of `gpdFisherInfoInv`. -/
theorem test_gpdInfoInvQuad_eq_dotProduct (ξ σ s₁ s₂ : ℝ) :
    gpdInfoInvQuad ξ σ s₁ s₂ =
      ![s₁, s₂] ⬝ᵥ Matrix.mulVec (gpdFisherInfoInv ξ σ) ![s₁, s₂] := by
  simp [gpdInfoInvQuad, gpdFisherInfoInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The maximized log-likelihood over the singleton `{θ}` is the log-likelihood at `θ`, finite or
not. -/
theorem test_gpdMaxLogLik_singleton {n : ℕ} (x : Fin n → ℝ) (θ : ℝ × ℝ) :
    gpdMaxLogLik {θ} x = gpdLogLikE θ.1 θ.2 x := by
  simp [gpdMaxLogLik]

/-- The deviance of a one-point model at its only parameter is zero, when the likelihood there is
finite. -/
theorem test_gpdDeviance_singleton {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ}
    (h : gpdLogLikE θ.1 θ.2 x ≠ ⊥) :
    2 * (gpdMaxLogLik {θ} x - gpdLogLikE θ.1 θ.2 x) = 0 := by
  rw [test_gpdMaxLogLik_singleton, gpdLogLikE_eq_coe_of_ne_bot h, ← EReal.coe_sub, sub_self]
  simp

/-- The qualification in `test_gpdDeviance_singleton` is needed: at a parameter of likelihood zero
the same expression is `-∞` (`⊥ - ⊥ = ⊥` in `EReal`), not `0`. -/
theorem test_gpdDeviance_singleton_of_bot {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ}
    (h : gpdLogLikE θ.1 θ.2 x = ⊥) :
    2 * (gpdMaxLogLik {θ} x - gpdLogLikE θ.1 θ.2 x) = ⊥ := by
  rw [test_gpdMaxLogLik_singleton, h]
  simp [EReal.mul_bot_of_pos]

/-- A parameter of finite likelihood in a one-point model is in its own profile set exactly when the
critical value is nonnegative: the deviance there is `0`. -/
theorem test_mem_gpdProfileInterval_singleton {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ} {g : ℝ × ℝ → ℝ}
    {c : ℝ} (h : gpdLogLikE θ.1 θ.2 x ≠ ⊥) :
    g θ ∈ gpdProfileInterval {θ} g c x ↔ 0 ≤ c := by
  have hK : ({θ} : Set (ℝ × ℝ)) ∩ g ⁻¹' {g θ} = {θ} := by
    ext p
    simp only [mem_inter_iff, mem_singleton_iff, mem_preimage]
    exact ⟨fun hp => hp.1, fun hp => ⟨hp, by rw [hp]⟩⟩
  have hdev := test_gpdDeviance_singleton (x := x) h
  have hmax := test_gpdMaxLogLik_singleton x θ
  rw [hmax] at hdev
  simp only [gpdProfileInterval, mem_ofPred_eq, gpdProfileLogLik, hK]
  have htop : gpdLogLikE θ.1 θ.2 x ≠ ⊤ := by
    rw [gpdLogLikE_eq_coe_of_ne_bot h]
    exact EReal.coe_ne_top _
  rw [hmax, hdev]
  simp [h, htop]

/-- `gpdProfileInterval` on an empty parameter set is empty. It would be all of `ℝ` if the definition
did not require a finite maximum, since `⊥ - ⊥ = ⊥` in `EReal`. -/
theorem test_gpdProfileInterval_empty (g : ℝ × ℝ → ℝ) (c : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    gpdProfileInterval ∅ g c x = ∅ := by
  ext ψ
  simp [gpdProfileInterval, gpdMaxLogLik]

/-- `gpdDevianceRegion` on an empty parameter set is empty. -/
theorem test_gpdDevianceRegion_empty (c : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    gpdDevianceRegion ∅ c x = ∅ := by
  ext θ
  simp [gpdDevianceRegion]

/-- A negative observation is impossible under every GPD. -/
private theorem gpdLogLikE_eq_bot_of_neg {n : ℕ} {x : Fin n → ℝ} {i : Fin n} (hi : x i < 0)
    (ξ σ : ℝ) : gpdLogLikE ξ σ x = ⊥ := by
  have h : gpdLogDensityE ξ σ (x i) = ⊥ := by
    by_contra hne
    exact absurd (gpdLogDensityE_ne_bot_iff.1 hne).1 (not_le.2 hi)
  rw [gpdLogLikE, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), h, EReal.bot_add]

/-- An incompatible sample: with a negative observation the likelihood vanishes on every `K`, so
`gpdProfileInterval` is empty, not all of `ℝ`. -/
theorem test_gpdProfileInterval_of_neg (K : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℝ) (c : ℝ) {n : ℕ}
    {x : Fin n → ℝ} {i : Fin n} (hi : x i < 0) : gpdProfileInterval K g c x = ∅ := by
  have h : gpdMaxLogLik K x = ⊥ := by
    simp [gpdMaxLogLik, gpdLogLikE_eq_bot_of_neg hi]
  ext ψ
  simp [gpdProfileInterval, h]

/-- An incompatible sample on a concrete model: `GPD(-1/2, 1)` has support `[0, 2]`, so the
observation `3` has likelihood zero, and the profile set is empty. -/
theorem test_gpdProfileInterval_beyond_endpoint (g : ℝ × ℝ → ℝ) (c : ℝ) :
    gpdProfileInterval {((-1 / 2 : ℝ), (1 : ℝ))} g c (fun _ : Fin 1 => (3 : ℝ)) = ∅ := by
  have hd : gpdLogDensityE (-1 / 2) 1 3 = ⊥ := by
    by_contra hne
    have := (gpdLogDensityE_ne_bot_iff.1 hne).2
    norm_num at this
  have h : gpdMaxLogLik {((-1 / 2 : ℝ), (1 : ℝ))} (fun _ : Fin 1 => (3 : ℝ)) = ⊥ := by
    simp [gpdMaxLogLik, gpdLogLikE, hd]
  ext ψ
  simp [gpdProfileInterval, h]

/-- `gpdDevianceRegion` lies in `K`: a parameter outside `K` is not in it, whatever its likelihood. -/
theorem test_gpdDevianceRegion_subset (K : Set (ℝ × ℝ)) (c : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    gpdDevianceRegion K c x ⊆ K := fun _ hθ => hθ.1

/-- The profile log-likelihood at an unattained value is `-∞`: a value of the interest parameter
outside the image of `K` has profile likelihood `-∞`. -/
theorem test_gpdProfileLogLik_empty {K : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℝ} {ψ : ℝ}
    (h : ∀ p ∈ K, g p ≠ ψ) {n : ℕ} (x : Fin n → ℝ) : gpdProfileLogLik K g ψ x = ⊥ := by
  have : K ∩ g ⁻¹' {ψ} = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
      not_and]
    exact h p
  simp [gpdProfileLogLik, gpdMaxLogLik, this]

end Test.KnownAnswers.ProfileLikelihood
