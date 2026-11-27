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
private def gpdK : Set (ℝ × ℝ) := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (1 : ℝ) 2

/-- Test-specific: `gpdK` is compact. -/
private theorem isCompact_gpdK : IsCompact gpdK := isCompact_Icc.prod isCompact_Icc

/-- Test-specific: `gpdK` lies in the admissible region `ξ > -1`, `σ > 0`. -/
private theorem gpdK_sub : ∀ p ∈ gpdK, -1 < p.1 ∧ 0 < p.2 := by
  rintro ⟨a, b⟩ ⟨⟨ha, -⟩, ⟨hb, -⟩⟩
  exact ⟨by simp only at ha ⊢; linarith, by simp only at hb ⊢; linarith⟩

/-- Test-specific: The true parameter `(1/4, 3/2)` is interior to `gpdK`. -/
private theorem mem_interior_gpdK : ((1 / 4 : ℝ), (3 / 2 : ℝ)) ∈ interior gpdK := by
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
private def gevK : Set (ℝ × ℝ × ℝ) := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2)

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

/-- Test-specific: `gevK` is compact. -/
private theorem isCompact_gevK : IsCompact gevK :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- Test-specific: `gevK` lies in the admissible region `ξ > -1`, `σ > 0`. -/
private theorem gevK_sub : ∀ p ∈ gevK, -1 < p.1 ∧ 0 < p.2.2 := by
  rintro ⟨a, b, c⟩ ⟨⟨ha, -⟩, -, ⟨hc, -⟩⟩
  exact ⟨by simp only at ha ⊢; linarith, by simp only at hc ⊢; linarith⟩

/-- Test-specific: a parameter with `|ξ| < 1/2`, `0 < μ < 1`, `1 < σ < 2` is interior to `gevK`. -/
private theorem mem_interior_gevK {ξ μ σ : ℝ} (h1 : -1 / 2 < ξ) (h2 : ξ < 1 / 2) (h3 : 0 < μ)
    (h4 : μ < 1) (h5 : 1 < σ) (h6 : σ < 2) : (ξ, μ, σ) ∈ interior gevK := by
  rw [gevK, interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc, interior_Icc]
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩

/-- Exercises `exists_gevMLE_tendstoInDistribution` (joint asymptotic normality of the
three-parameter GEV MLE) for a **positive shape**, the moving lower endpoint: iid
`GEV(ξ = 1/4, μ = 1/2, σ = 3/2)` samples, `K = [-1/2, 1/2] × [0, 1] × [1, 2]`. All hypotheses
discharged: a measurable maximum likelihood estimator exists and is asymptotically normal. -/
theorem test_nonvacuous_exists_gevMLE_tendstoInDistribution_pos :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gevK ∧
          IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) gevK (g n x)) ∧
        TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
            !₂[(g n (fun i : Fin n => X i ω)).1 - 1 / 4,
              (g n (fun i : Fin n => X i ω)).2.1 - 1 / 2,
              (g n (fun i : Fin n => X i ω)).2.2 - 3 / 2])
          atTop (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (fun _ => P)
          (multivariateGaussian 0 (gevMLECov (1 / 4) (3 / 2))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF (1 / 4) (1 / 2) hσ).measure
  have := hP
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gevMLE_tendstoInDistribution isCompact_gevK gevK_sub
    (mem_interior_gevK (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (by norm_num) (by norm_num) hσ hlaw hind HasLaw.id

/-- Exercises `exists_gevMLE_tendstoInDistribution` for a **negative shape** in the regular range,
the moving upper endpoint: iid `GEV(ξ = -2/5, μ = 1/2, σ = 3/2)` samples, `-1/2 < ξ < 0`,
`K = [-1/2, 1/2] × [0, 1] × [1, 2]`. All hypotheses discharged. -/
theorem test_nonvacuous_exists_gevMLE_tendstoInDistribution_neg :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gevK ∧
          IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) gevK (g n x)) ∧
        TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
            !₂[(g n (fun i : Fin n => X i ω)).1 - -(2 / 5),
              (g n (fun i : Fin n => X i ω)).2.1 - 1 / 2,
              (g n (fun i : Fin n => X i ω)).2.2 - 3 / 2])
          atTop (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (fun _ => P)
          (multivariateGaussian 0 (gevMLECov (-(2 / 5)) (3 / 2))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF (-(2 / 5)) (1 / 2) hσ).measure
  have := hP
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gevMLE_tendstoInDistribution isCompact_gevK gevK_sub
    (mem_interior_gevK (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (by norm_num) (by norm_num) hσ hlaw hind HasLaw.id

/-- Exercises `exists_gevMLE_returnLevel_tendstoInDistribution` (the unconditional normality of the
maximum likelihood return level): the `100`-block return level for iid
`GEV(ξ = 1/4, μ = 1/2, σ = 3/2)` samples. The limit is a nondegenerate Gaussian, since
`gevReturnLevelVar_pos`. All hypotheses discharged. -/
theorem test_nonvacuous_exists_gevMLE_returnLevel :
    0 < gevReturnLevelVar (1 / 4) (3 / 2) 100 ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gevK ∧
          IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) gevK (g n x)) ∧
        TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
          (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
            (g n (fun i : Fin n => X i ω)).2.2 100 - gevReturnLevel (1 / 4) (1 / 2) (3 / 2) 100))
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (gevReturnLevelVar (1 / 4) (3 / 2) 100).toNNReal) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  refine ⟨gevReturnLevelVar_pos hσ (by norm_num) (by norm_num) 100, ?_⟩
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF (1 / 4) (1 / 2) hσ).measure
  have := hP
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gevMLE_returnLevel_tendstoInDistribution (m := 100) isCompact_gevK gevK_sub
    (mem_interior_gevK (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (by norm_num) (by norm_num) hσ (by norm_num) hlaw hind HasLaw.id

/-- Exercises `tendsto_measure_mem_gevMLEReturnLevelInterval` (Wald coverage of the maximum likelihood
return level): iid `GEV(ξ = 1/4, μ = 1/2, σ = 3/2)` samples, measurable maximizers from
`exists_measurable_gevMLE`, and the true standard deviation as the consistent standard error, which
is the one hypothesis the theorem does not discharge. -/
theorem test_nonvacuous_tendsto_measure_mem_gevMLEReturnLevelInterval (z : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gevK ∧
          IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) gevK (g n x)) ∧
        Tendsto (fun n : ℕ => P {ω | gevReturnLevel (1 / 4) (1 / 2) (3 / 2) 100 ∈ Icc
          (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
              (g n (fun i : Fin n => X i ω)).2.2 100 -
            z * √(gevReturnLevelVar (1 / 4) (3 / 2) 100) / √(n : ℝ))
          (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
              (g n (fun i : Fin n => X i ω)).2.2 100 +
            z * √(gevReturnLevelVar (1 / 4) (3 / 2) 100) / √(n : ℝ))})
          atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF (1 / 4) (1 / 2) hσ).measure
  have := hP
  have hint := mem_interior_gevK (ξ := 1 / 4) (μ := 1 / 2) (σ := 3 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  choose g hgm hg using exists_measurable_gevMLE isCompact_gevK gevK_sub ⟨_, interior_subset hint⟩
  refine ⟨Ω, _, P, X, hP, hind, g, hgm, hg, ?_⟩
  exact tendsto_measure_mem_gevMLEReturnLevelInterval isCompact_gevK gevK_sub hint
    (by norm_num) (by norm_num) hσ (by norm_num) hlaw hind
    (θh := fun n ω => g n fun i : Fin n => X i ω)
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hlaw i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2)
    (S := fun _ _ => √(gevReturnLevelVar (1 / 4) (3 / 2) 100))
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => tendsto_const_nhds))
    (fun _ => aemeasurable_const) z

/-- Exercises `exists_gevMLE_returnLevelPlugInInterval_tendsto` (computable plug-in Wald coverage
of the maximum likelihood return level): iid `GEV(ξ = 1/4, μ = 1/2, σ = 3/2)` samples, measurable
maximizers over `[-1/2, 1/2] × [0, 1] × [1, 2]`, and the plug-in standard error computed from the
MLE alone. No standard-error hypothesis is assumed; all hypotheses discharged. -/
theorem test_nonvacuous_exists_gevMLE_returnLevelPlugInInterval :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gevK ∧
          IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) gevK (g n x)) ∧
        ∀ z : ℝ, Tendsto (fun n : ℕ => P {ω | gevReturnLevel (1 / 4) (1 / 2) (3 / 2) 100 ∈ Icc
          (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
              (g n (fun i : Fin n => X i ω)).2.2 100 -
            z * √(gevReturnLevelVar (g n (fun i : Fin n => X i ω)).1
              (g n (fun i : Fin n => X i ω)).2.2 100) / √(n : ℝ))
          (gevReturnLevel (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
              (g n (fun i : Fin n => X i ω)).2.2 100 +
            z * √(gevReturnLevelVar (g n (fun i : Fin n => X i ω)).1
              (g n (fun i : Fin n => X i ω)).2.2 100) / √(n : ℝ))})
          atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF (1 / 4) (1 / 2) hσ).measure
  have := hP
  have hint := mem_interior_gevK (ξ := 1 / 4) (μ := 1 / 2) (σ := 3 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gevMLE_returnLevelPlugInInterval_tendsto (m := 100) isCompact_gevK gevK_sub hint
    (by norm_num) (by norm_num) hσ (by norm_num) hlaw hind

/-- The asymptotic covariance is the inverse of the information, in the order `(ξ, μ, σ)`: the
`(ξ, ξ)` entry of `gevMLECov` is the `(ξ, ξ)` entry of the inverse of `gevFisherInfo`, whose order
is `(μ, σ, ξ)`, and likewise for the other coordinates. -/
example (ξ σ : ℝ) :
    gevMLECov ξ σ 0 0 = (gevFisherInfo ξ σ)⁻¹ 2 2 ∧ gevMLECov ξ σ 1 1 = (gevFisherInfo ξ σ)⁻¹ 0 0 ∧
      gevMLECov ξ σ 2 2 = (gevFisherInfo ξ σ)⁻¹ 1 1 ∧ gevMLECov ξ σ 0 1 = (gevFisherInfo ξ σ)⁻¹ 2 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The compact parameter set `[0, 1] × [1, 2]` for the two-parameter Gumbel model `(μ, σ)`. -/
private def gumbelK : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2

/-- Exercises `exists_gumbelMLE_tendstoInDistribution` (joint asymptotic normality of the
two-parameter Gumbel MLE): iid `Gumbel(μ = 1/2, σ = 3/2)` samples, `K = [0, 1] × [1, 2]`.
All hypotheses discharged. -/
theorem test_nonvacuous_exists_gumbelMLE_tendstoInDistribution :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gumbelK ∧
          IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2 x) gumbelK (g n x)) ∧
        TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
            !₂[(g n (fun i : Fin n => X i ω)).1 - 1 / 2,
              (g n (fun i : Fin n => X i ω)).2 - 3 / 2])
          atTop (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (fun _ => P)
          (multivariateGaussian 0 (gumbelFisherInfoInv (3 / 2))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF 0 (1 / 2) hσ).measure
  have := hP
  have hK : IsCompact gumbelK := isCompact_Icc.prod isCompact_Icc
  have hKS : ∀ p ∈ gumbelK, 0 < p.2 := fun p hp => by
    have : 1 ≤ p.2 := hp.2.1; linarith
  have hint : ((1 / 2 : ℝ), (3 / 2 : ℝ)) ∈ interior gumbelK := by
    rw [gumbelK, interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gumbelMLE_tendstoInDistribution hK hKS hint hσ hlaw hind HasLaw.id

/-- Exercises `exists_gumbelMLE_returnLevelPlugInInterval_tendsto` (unconditional computable
plug-in Wald confidence interval for the Gumbel MLE return level): iid `Gumbel(1/2, 3/2)` samples,
`100`-block return level, measurable maximizers over `[0, 1] × [1, 2]`. All hypotheses discharged. -/
theorem test_nonvacuous_exists_gumbelMLE_returnLevelPlugInInterval :
    0 < gumbelReturnLevelVar (3 / 2) 100 ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ gumbelK ∧
          IsMaxOn (fun p : ℝ × ℝ => gevLogLikE 0 p.1 p.2 x) gumbelK (g n x)) ∧
        ∀ z : ℝ, Tendsto (fun n : ℕ => P {ω | gevReturnLevel 0 (1 / 2) (3 / 2) 100 ∈ Icc
          (gevReturnLevel 0 (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2 100 -
            z * √(gumbelReturnLevelVar (g n (fun i : Fin n => X i ω)).2 100) / √(n : ℝ))
          (gevReturnLevel 0 (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2 100 +
            z * √(gumbelReturnLevelVar (g n (fun i : Fin n => X i ω)).2 100) / √(n : ℝ))})
          atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  refine ⟨gumbelReturnLevelVar_pos hσ 100, ?_⟩
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF 0 (1 / 2) hσ).measure
  have := hP
  have hK : IsCompact gumbelK := isCompact_Icc.prod isCompact_Icc
  have hKS : ∀ p ∈ gumbelK, 0 < p.2 := fun p hp => by
    have : 1 ≤ p.2 := hp.2.1; linarith
  have hint : ((1 / 2 : ℝ), (3 / 2 : ℝ)) ∈ interior gumbelK := by
    rw [gumbelK, interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gumbelMLE_returnLevelPlugInInterval_tendsto (m := 100) hK hKS hint hσ hlaw hind

/-- Exercises `posDef_gevFisherInfoZero` and `tendstoInDistribution_gumbelScoreVec3` (the full
`3 × 3` positive definite GEV Fisher information and trivariate score CLT at `ξ = 0`): iid
`GEV(0, 1/2, 3/2)` samples. All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInDistribution_gumbelScoreVec3 :
    (gevFisherInfoZero (3 / 2)).PosDef ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gumbelScoreVec3 (1 / 2) (3 / 2) (X i ω))
        atTop (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (fun _ => P)
        (multivariateGaussian 0 (gevFisherInfoZero (3 / 2))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  refine ⟨posDef_gevFisherInfoZero hσ, ?_⟩
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF 0 (1 / 2) hσ).measure
  have := hP
  exact ⟨Ω, _, P, X, hP, hind, tendstoInDistribution_gumbelScoreVec3 hσ hlaw hind HasLaw.id⟩

/-- Exercises `exists_gpdMLE_tendstoInDistribution_reg` at the Gumbel boundary `ξ₀ = 0`:
iid `GPD(0, 3/2)` (= `Exponential(3/2)`) samples, `K = [-1/2, 1/2] × [1, 2]`.
All hypotheses discharged. -/
theorem test_nonvacuous_exists_gpdMLE_tendstoInDistribution_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (1 : ℝ) 2 ∧
          IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x)
            (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (1 : ℝ) 2) (g n x)) ∧
        TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
            !₂[(g n (fun i : Fin n => X i ω)).1 - 0,
              (g n (fun i : Fin n => X i ω)).2 - 3 / 2])
          atTop (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (fun _ => P)
          (multivariateGaussian 0 (gpdFisherInfoInv 0 (3 / 2))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure 0 (3 / 2))
  have := hP
  set K : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (1 : ℝ) 2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2 := fun p hp => ⟨by linarith [hp.1.1], by linarith [hp.2.1]⟩
  have hint : ((0 : ℝ), (3 / 2 : ℝ)) ∈ interior K := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gpdMLE_tendstoInDistribution_reg hK hKS hint (by norm_num) hσ hlaw hind HasLaw.id

/-- Exercises `exists_gevLocalMLE_tendstoInDistribution_zero` (unconditional existence and
joint asymptotic normality of a data-driven measurable three-parameter GEV local MLE at `ξ₀ = 0`):
iid `GEV(0, 1/2, 3/2)` samples, `K₂ = [0, 1] × [1, 2]`. All hypotheses discharged. -/
theorem test_nonvacuous_exists_gevLocalMLE_tendstoInDistribution_zero :
    0 < gevReturnLevelVarZero (3 / 2) 100 ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ)
      (_ : IsProbabilityMeasure P), iIndepFun X P ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
          (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω))
          (g n (fun i : Fin n => X i ω))}) atTop (𝓝 0) ∧
        TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
            !₂[(g n (fun i : Fin n => X i ω)).1,
              (g n (fun i : Fin n => X i ω)).2.1 - 1 / 2,
              (g n (fun i : Fin n => X i ω)).2.2 - 3 / 2])
          atTop (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (fun _ => P)
          (multivariateGaussian 0 (gevMLECovZero (3 / 2))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  refine ⟨gevReturnLevelVarZero_pos hσ 100, ?_⟩
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
    exists_iid ℕ (gevLocScaleCDF 0 (1 / 2) hσ).measure
  have := hP
  have hK : IsCompact gumbelK := isCompact_Icc.prod isCompact_Icc
  have hKS : ∀ p ∈ gumbelK, 0 < p.2 := fun p hp => by have : 1 ≤ p.2 := hp.2.1; linarith
  have hint : ((1 / 2 : ℝ), (3 / 2 : ℝ)) ∈ interior gumbelK := by
    rw [gumbelK, interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  refine ⟨Ω, _, P, X, hP, hind, ?_⟩
  exact exists_gevLocalMLE_tendstoInDistribution_zero hK hKS hint hσ hlaw hind HasLaw.id

/-- Exercises `exists_potReturnLevelPlugInInterval_tendsto` (random-count POT return-level plug-in
CI at `ξ₀ = 0`, Coles §4.3.3): independent iid `Bernoulli(1/2)` exceedance indicators and iid
`GPD(0, 3/2)` excesses on a product probability space, `N = 100`. All hypotheses discharged. -/
theorem test_nonvacuous_exists_potReturnLevelPlugInInterval (z : ℝ) :
    0 < potReturnLevelVar (1 / 2) 0 (3 / 2) 100 ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (I : ℕ → Ω → Bool) (E : ℕ → Ω → ℝ),
      (∀ i, Measurable (I i)) ∧ iIndepFun I P ∧
      (∀ i, P {ω | I i ω = true} = ENNReal.ofReal (1 / 2)) ∧
      (∀ j, HasLaw (E j) (gpdMeasure 0 (3 / 2)) P) ∧ iIndepFun E P ∧
      IndepFun (fun ω i => I i ω) (fun ω j => E j ω) P ∧
      ∃ g : (m : ℕ) → (Fin m → ℝ) → ℝ × ℝ, (∀ m, Measurable (g m)) ∧
        Tendsto (fun n : ℕ => P {ω | gpdReturnLevel 0 0 (3 / 2) (1 / 2) 100 ∈ Icc
          (gpdReturnLevel 0 (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
              (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 (potRate I n ω) 100 -
            z * √(potReturnLevelVar (potRate I n ω)
              (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
              (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 100) / √(n : ℝ))
          (gpdReturnLevel 0 (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
              (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 (potRate I n ω) 100 +
            z * √(potReturnLevelVar (potRate I n ω)
              (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
              (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 100) / √(n : ℝ))})
          atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  refine ⟨potReturnLevelVar_pos (by norm_num) (by norm_num) (by norm_num) hσ (by norm_num), ?_⟩
  let μB : Measure Bool := (ENNReal.ofReal (1 / 2)) • Measure.dirac true +
    (ENNReal.ofReal (1 / 2)) • Measure.dirac false
  have hμB : IsProbabilityMeasure μB := ⟨by
    simp only [μB, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num⟩
  obtain ⟨Ω₁, _, P₁, I₁, hI₁m, hI₁law, hI₁ind, hP₁⟩ := exists_iid ℕ μB
  obtain ⟨Ω₂, _, P₂, E₂, hE₂m, hE₂law, hE₂ind, hP₂⟩ := exists_iid ℕ (gpdMeasure 0 (3 / 2))
  have := hP₁; have := hP₂
  let P : Measure (Ω₁ × Ω₂) := P₁.prod P₂
  let I : ℕ → Ω₁ × Ω₂ → Bool := fun i p => I₁ i p.1
  let E : ℕ → Ω₁ × Ω₂ → ℝ := fun j p => E₂ j p.2
  have hIm : ∀ i, Measurable (I i) := fun i => (hI₁m i).comp measurable_fst
  have hEm : ∀ j, Measurable (E j) := fun j => (hE₂m j).comp measurable_snd
  have hIprob : ∀ i, P {ω | I i ω = true} = ENNReal.ofReal (1 / 2) := fun i => by
    have heq : {ω : Ω₁ × Ω₂ | I i ω = true} = (I₁ i ⁻¹' {true}) ×ˢ univ := by ext ⟨a, b⟩; simp [I]
    rw [heq, Measure.prod_prod, measure_univ, mul_one]
    have hpre : P₁ (I₁ i ⁻¹' {true}) = μB {true} := by
      rw [← (hI₁law i).map_eq, Measure.map_apply (hI₁m i) (measurableSet_singleton true)]
    rw [hpre]
    simp [μB]
  have hindI : iIndepFun I P := by
    have h := hI₁ind.comp (fun _ => id) (fun _ => measurable_id)
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hI₁ind ⊢
    intro S sets hsets
    have heq : ⋂ i ∈ S, I i ⁻¹' sets i = (⋂ i ∈ S, I₁ i ⁻¹' sets i) ×ˢ univ := by
      ext ⟨a, b⟩; simp [I]
    rw [heq, Measure.prod_prod, measure_univ, mul_one, hI₁ind S hsets]
    refine Finset.prod_congr rfl fun i _ => ?_
    have heqi : I i ⁻¹' sets i = (I₁ i ⁻¹' sets i) ×ˢ univ := by ext ⟨a, b⟩; simp [I]
    rw [heqi, Measure.prod_prod, measure_univ, mul_one]
  have hElaw : ∀ j, HasLaw (E j) (gpdMeasure 0 (3 / 2)) P := fun j =>
    ⟨(hEm j).aemeasurable, by
      change (P₁.prod P₂).map (E₂ j ∘ Prod.snd) = gpdMeasure 0 (3 / 2)
      rw [← Measure.map_map (hE₂m j) measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
        (hE₂law j).map_eq]⟩
  have hindE : iIndepFun E P := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hE₂ind ⊢
    intro S sets hsets
    have heq : ⋂ j ∈ S, E j ⁻¹' sets j = univ ×ˢ (⋂ j ∈ S, E₂ j ⁻¹' sets j) := by
      ext ⟨a, b⟩; simp [E]
    rw [heq, Measure.prod_prod, measure_univ, one_mul, hE₂ind S hsets]
    refine Finset.prod_congr rfl fun j _ => ?_
    have heqj : E j ⁻¹' sets j = univ ×ˢ (E₂ j ⁻¹' sets j) := by ext ⟨a, b⟩; simp [E]
    rw [heqj, Measure.prod_prod, measure_univ, one_mul]
  have hindIE : IndepFun (fun ω i => I i ω) (fun ω j => E j ω) P := by
    have hfst_snd : IndepFun (Prod.fst : Ω₁ × Ω₂ → Ω₁) (Prod.snd : Ω₁ × Ω₂ → Ω₂) P := by
      rw [indepFun_iff_measure_inter_preimage_eq_mul]
      intro s t _ _
      have h1 : Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t = s ×ˢ t := by ext ⟨a, b⟩; simp
      have h2 : Prod.fst ⁻¹' s = s ×ˢ (univ : Set Ω₂) := by ext ⟨a, b⟩; simp
      have h3 : Prod.snd ⁻¹' t = (univ : Set Ω₁) ×ˢ t := by ext ⟨a, b⟩; simp
      rw [h1, h2, h3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
        measure_univ, measure_univ, mul_one, one_mul]
    exact hfst_snd.comp (Measurable.of_eval hI₁m) (Measurable.of_eval hE₂m)
  set K : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (1 : ℝ) 2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2 := fun p hp => ⟨by linarith [hp.1.1], by linarith [hp.2.1]⟩
  have hint : ((0 : ℝ), (3 / 2 : ℝ)) ∈ interior K := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  obtain ⟨g, hgm, _, hcov⟩ := exists_potReturnLevelPlugInInterval_tendsto (u := 0) (N := 100)
    (by norm_num) (by norm_num) (by norm_num) hσ (by norm_num) hIm hindI hIprob hElaw hindE hindIE
    hK hKS hint z
  exact ⟨Ω₁ × Ω₂, inferInstance, P, inferInstance, I, E, hIm, hindI, hIprob, hElaw, hindE, hindIE,
    g, hgm, hcov⟩

/-- Exercises `tendsto_measure_mem_gpdReturnLevelProfileInterval_reg` and
`tendsto_measure_mem_gpdDevianceRegion_reg` at negative regular shape `ξ₀ = -1/4` and at the
Gumbel boundary `ξ₀ = 0` (`GPDWilks.Regular`, #44). All hypotheses discharged. -/
theorem test_nonvacuous_gpdWilks_regular (c : ℝ) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X : ℕ → Ω → ℝ), iIndepFun X P ∧
        Tendsto (fun n : ℕ => P {ω | gpdReturnLevel 0 (-(1 / 4 : ℝ)) (3 / 2) (1 / 2) 100 ∈
            gpdProfileInterval gpdK (fun p => gpdReturnLevel 0 p.1 p.2 (1 / 2) 100) c
              (fun i : Fin n => X i ω)})
          atTop (𝓝 (chiSquared 1 (Iic c))) ∧
        Tendsto (fun n : ℕ => P {ω | (-(1 / 4 : ℝ), (3 / 2 : ℝ)) ∈
            gpdDevianceRegion gpdK c (fun i : Fin n => X i ω)})
          atTop (𝓝 (chiSquared 2 (Iic c)))) ∧
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X : ℕ → Ω → ℝ), iIndepFun X P ∧
        Tendsto (fun n : ℕ => P {ω | gpdReturnLevel 0 0 (3 / 2) (1 / 2) 100 ∈
            gpdProfileInterval gpdK (fun p => gpdReturnLevel 0 p.1 p.2 (1 / 2) 100) c
              (fun i : Fin n => X i ω)})
          atTop (𝓝 (chiSquared 1 (Iic c))) ∧
        Tendsto (fun n : ℕ => P {ω | ((0 : ℝ), (3 / 2 : ℝ)) ∈
            gpdDevianceRegion gpdK c (fun i : Fin n => X i ω)})
          atTop (𝓝 (chiSquared 2 (Iic c)))) := by
  constructor
  · obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (-(1 / 4)) (3 / 2))
    have := hP
    have hint : (-(1 / 4 : ℝ), (3 / 2 : ℝ)) ∈ interior gpdK := by
      rw [gpdK, interior_prod_eq, interior_Icc, interior_Icc]
      exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
    exact ⟨Ω, _, P, hP, X, hind,
      tendsto_measure_mem_gpdReturnLevelProfileInterval_reg isCompact_gpdK gpdK_sub hint
        (by norm_num) (by norm_num) hlaw hind (by norm_num) c,
      tendsto_measure_mem_gpdDevianceRegion_reg isCompact_gpdK gpdK_sub hint
        (by norm_num) (by norm_num) hlaw hind c⟩
  · obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure 0 (3 / 2))
    have := hP
    have hint : ((0 : ℝ), (3 / 2 : ℝ)) ∈ interior gpdK := by
      rw [gpdK, interior_prod_eq, interior_Icc, interior_Icc]
      exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
    exact ⟨Ω, _, P, hP, X, hind,
      tendsto_measure_mem_gpdReturnLevelProfileInterval_reg isCompact_gpdK gpdK_sub hint
        (by norm_num) (by norm_num) hlaw hind (by norm_num) c,
      tendsto_measure_mem_gpdDevianceRegion_reg isCompact_gpdK gpdK_sub hint
        (by norm_num) (by norm_num) hlaw hind c⟩

/-- Exercises `tendsto_measure_mem_gevDevianceRegion` (`ξ₀ = 1/4`) and
`exists_gevLocalMLE_deviance_tendstoInDistribution_zero` (`ξ₀ = 0`) (`GEVWilks`, #44).
All hypotheses discharged. -/
theorem test_nonvacuous_gevWilks (c : ℝ) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X : ℕ → Ω → ℝ), iIndepFun X P ∧
        Tendsto (fun n : ℕ => P {ω | ((1 / 4 : ℝ), (1 / 2 : ℝ), (3 / 2 : ℝ)) ∈
            gevDevianceRegion gevK c (fun i : Fin n => X i ω)})
          atTop (𝓝 (chiSquared 3 (Iic c)))) ∧
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X : ℕ → Ω → ℝ), iIndepFun X P ∧
        ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
          Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
            (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω))
            (g n (fun i : Fin n => X i ω))}) atTop (𝓝 0) ∧
          TendstoInDistribution
            (fun (n : ℕ) ω =>
              2 * (gevLogLikN (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
                  (g n (fun i : Fin n => X i ω)).2.2 (fun i => X i ω) n -
                gevLogLikN 0 (1 / 2) (3 / 2) (fun i => X i ω) n))
            atTop (id : ℝ → ℝ) (fun _ => P) (chiSquared 3)) := by
  have hσ : (0 : ℝ) < 3 / 2 := by norm_num
  constructor
  · obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
      exists_iid ℕ (gevLocScaleCDF (1 / 4) (1 / 2) hσ).measure
    have := hP
    exact ⟨Ω, _, P, hP, X, hind,
      tendsto_measure_mem_gevDevianceRegion isCompact_gevK gevK_sub
        (mem_interior_gevK (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)) (by norm_num) (by norm_num) hσ hlaw hind c⟩
  · obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ :=
      exists_iid ℕ (gevLocScaleCDF 0 (1 / 2) hσ).measure
    have := hP
    have hK : IsCompact gumbelK := isCompact_Icc.prod isCompact_Icc
    have hKS : ∀ p ∈ gumbelK, 0 < p.2 := fun p hp => by have : 1 ≤ p.2 := hp.2.1; linarith
    have hint : ((1 / 2 : ℝ), (3 / 2 : ℝ)) ∈ interior gumbelK := by
      rw [gumbelK, interior_prod_eq, interior_Icc, interior_Icc]
      exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
    exact ⟨Ω, _, P, hP, X, hind,
      exists_gevLocalMLE_deviance_tendstoInDistribution_zero hK hKS hint hσ hlaw hind HasLaw.id⟩

end ExtremeValueTheory.Test.NonVacuity
