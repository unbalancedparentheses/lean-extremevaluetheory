import ExtremeValueTheory

/-!
# Non-vacuity: GPD and GEV maximum likelihood

Each test builds an iid sample with a concrete GPD or GEV law (via Mathlib's `exists_iid`) and a
concrete compact parameter set, discharges every hypothesis of a headline likelihood theorem, and
obtains its conclusion for that sample.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace ExtremeValueTheory.Test.NonVacuity

/-- The compact parameter set `K = [-1/2, 1/2] × [1, 2]` for `(ξ, σ)`. -/
noncomputable def gpdK : Set (ℝ × ℝ) := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (1 : ℝ) 2

theorem isCompact_gpdK : IsCompact gpdK := isCompact_Icc.prod isCompact_Icc

theorem gpdK_sub : ∀ p ∈ gpdK, -1 < p.1 ∧ 0 < p.2 := by
  rintro ⟨a, b⟩ ⟨⟨ha, -⟩, ⟨hb, -⟩⟩
  exact ⟨by simp only at ha ⊢; linarith, by simp only at hb ⊢; linarith⟩

theorem mem_interior_gpdK : ((1 / 4 : ℝ), (3 / 2 : ℝ)) ∈ interior gpdK := by
  rw [gpdK, interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- Exercises `ae_tendsto_gpdMLE'` (strong consistency of the joint GPD MLE): iid `GPD(1/4, 3/2)`
samples, `K = [-1/2, 1/2] × [1, 2]`. All hypotheses discharged. -/
theorem test_nonvacuous_ae_tendsto_gpdMLE' :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, HasLaw (X i) (gpdMeasure (1 / 4) (3 / 2)) P) ∧
      iIndepFun X P ∧
      ∀ᵐ ω ∂P, ∀ (θhat : ℕ → ℝ × ℝ) (ε : ℕ → ℝ), (∀ n, θhat n ∈ gpdK) →
        Tendsto ε atTop (𝓝 0) →
        (∀ᶠ n in atTop, gpdLogLikE (1 / 4) (3 / 2) (fun i : Fin n => X i ω) ≤
          gpdLogLikE (θhat n).1 (θhat n).2 (fun i : Fin n => X i ω) + ((n * ε n : ℝ) : EReal)) →
        Tendsto θhat atTop (𝓝 ((1 / 4 : ℝ), (3 / 2 : ℝ))) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  refine ⟨Ω, _, P, X, hP, hlaw, hind, ?_⟩
  exact ae_tendsto_gpdMLE' (θ₀ := ((1 / 4 : ℝ), (3 / 2 : ℝ))) isCompact_gpdK gpdK_sub
    (interior_subset mem_interior_gpdK) hlaw hind

/-- Exercises `exists_gpdMLE_tendstoInDistribution` (joint asymptotic normality of the GPD MLE):
iid `GPD(1/4, 3/2)` samples (`ξ₀ = 1/4 ∈ (-1/2, ∞) \ {0}`), `θ₀` in the interior of
`K = [-1/2, 1/2] × [1, 2]`, and the limit `W = id` on `EuclideanSpace ℝ (Fin 2)` under the
Gaussian law `N(0, I(θ₀)⁻¹)`. All hypotheses discharged. -/
theorem test_nonvacuous_exists_gpdMLE_tendstoInDistribution :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gpdK ∧ IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) gpdK (g n x)) ∧
        TendstoInDistribution
          (fun (n : ℕ) ω => √(n : ℝ) • !₂[(g n (fun i : Fin n => X i ω)).1 - 1 / 4,
            (g n (fun i : Fin n => X i ω)).2 - 3 / 2])
          atTop (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (fun _ => P)
          (multivariateGaussian 0 (gpdFisherInfoInv (1 / 4) (3 / 2))) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  refine ⟨Ω, _, P, hP, X, ?_⟩
  exact exists_gpdMLE_tendstoInDistribution isCompact_gpdK gpdK_sub mem_interior_gpdK
    (by norm_num) (by norm_num) (by norm_num) hlaw hind (HasLaw.id)

/-- Exercises `tendstoInDistribution_gpdScaleMLE'` (asymptotic normality of the known-shape scale
MLE): iid `GPD(1/4, 3/2)`, limit `Z = id` under `N(0, σ₀² (1 + 2ξ))`. All hypotheses
discharged. -/
theorem test_nonvacuous_tendstoInDistribution_gpdScaleMLE' :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) * (gpdScaleMLE (1 / 4) (fun i : Fin n => X i ω) - 3 / 2))
        atTop (id : ℝ → ℝ) (fun _ => P)
        (gaussianReal 0 (((3 / 2 : ℝ)) ^ 2 * (1 + 2 * (1 / 4 : ℝ))).toNNReal) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  refine ⟨Ω, _, P, hP, X, ?_⟩
  exact tendstoInDistribution_gpdScaleMLE' (by norm_num) (by norm_num) (by norm_num) hlaw hind
    HasLaw.id

/-- The compact parameter set `[-1/2, 1/2] × [0, 1] × [1, 2]` for `(ξ, μ, σ)`. -/
noncomputable def gevK : Set (ℝ × ℝ × ℝ) :=
  Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2)

/-- Exercises `ae_tendsto_gevMLE` (strong consistency of the 3-parameter GEV MLE): iid
`GEV(ξ = 1/4, μ = 1/2, σ = 3/2)` samples, `K = [-1/2, 1/2] × [0, 1] × [1, 2]`. All hypotheses
discharged. -/
theorem test_nonvacuous_ae_tendsto_gevMLE :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧
      ∀ᵐ ω ∂P, ∀ (θhat : ℕ → ℝ × ℝ × ℝ) (ε : ℕ → ℝ), (∀ n, θhat n ∈ gevK) →
        Tendsto ε atTop (𝓝 0) →
        (∀ᶠ n in atTop, gevLogLikE (1 / 4) (1 / 2) (3 / 2) (fun i : Fin n => X i ω) ≤
          gevLogLikE (θhat n).1 (θhat n).2.1 (θhat n).2.2 (fun i : Fin n => X i ω) +
            ((n * ε n : ℝ) : EReal)) →
        Tendsto θhat atTop (𝓝 ((1 / 4 : ℝ), (1 / 2 : ℝ), (3 / 2 : ℝ))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF (1 / 4) (1 / 2) hσ).measure
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  have hK : IsCompact gevK := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKS : ∀ p ∈ gevK, -1 < p.1 ∧ 0 < p.2.2 := by
    rintro ⟨a, b, c⟩ ⟨⟨ha, -⟩, -, ⟨hc, -⟩⟩
    exact ⟨by simp only at ha ⊢; linarith, by simp only at hc ⊢; linarith⟩
  have hθ : ((1 / 4 : ℝ), (1 / 2 : ℝ), (3 / 2 : ℝ)) ∈ gevK :=
    ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  exact ae_tendsto_gevMLE (θ₀ := ((1 / 4 : ℝ), (1 / 2 : ℝ), (3 / 2 : ℝ))) hK hKS hθ hσ hlaw hind

end ExtremeValueTheory.Test.NonVacuity
