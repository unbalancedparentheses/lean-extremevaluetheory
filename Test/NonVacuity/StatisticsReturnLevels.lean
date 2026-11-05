import ExtremeValueTheory

/-!
# Non-vacuity: return levels and Wald intervals

* The POT return level and its interval: an iid `GPD(1/4, 3/2)` sample, the compact set
  `[-1/2, 1/2] × [1, 2]`, the library's measurable maximizers (`exists_measurable_gpdMLE`), threshold
  `u = 10`, `ζ = 1/10`, `N = 100`, so `N ζ = 10`.
* The GEV, Gumbel and three-parameter POT return levels have **no data in their statements**: their
  estimators are arbitrary, and asymptotic normality is a hypothesis. There is nothing to exercise
  but the delta method, so a synthetic estimator `θ̂ₙ = θ₀ + Z / √n`, `Z ∼ N(0, V)`, satisfies the
  hypotheses, for every positive semidefinite `V`. These tests show that the hypotheses are jointly
  satisfiable; they do not show that any statistical estimator satisfies them.
* The Hill interval is in `Test/NonVacuity/Statistics.lean`, next to the sample it uses.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Matrix

namespace ExtremeValueTheory.Test.NonVacuity.ReturnLevels

/-! ### The GPD maximum likelihood sample -/

/-- Test-specific: the compact parameter set `K = [-1/2, 1/2] × [1, 2]` for `(ξ, σ)`. -/
private def gpdK : Set (ℝ × ℝ) := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (1 : ℝ) 2

/-- Test-specific: `gpdK` is compact. -/
private theorem isCompact_gpdK : IsCompact gpdK := isCompact_Icc.prod isCompact_Icc

/-- Test-specific: `gpdK` lies in the admissible region `ξ > -1`, `σ > 0`. -/
private theorem gpdK_sub : ∀ p ∈ gpdK, -1 < p.1 ∧ 0 < p.2 := by
  rintro ⟨a, b⟩ ⟨⟨ha, -⟩, ⟨hb, -⟩⟩
  exact ⟨by simp only at ha ⊢; linarith, by simp only at hb ⊢; linarith⟩

/-- Test-specific: the true parameter `(1/4, 3/2)` is interior to `gpdK`. -/
private theorem mem_interior_gpdK : ((1 / 4 : ℝ), (3 / 2 : ℝ)) ∈ interior gpdK := by
  rw [gpdK, interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- Test-specific: an iid `GPD(1/4, 3/2)` sample with its measurable maximum likelihood estimator
over `gpdK`, from `exists_iid` and `exists_measurable_gpdMLE`. -/
private theorem exists_gpdSample :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (θh : ℕ → Ω → ℝ × ℝ),
      (∀ i, HasLaw (X i) (gpdMeasure (1 / 4) (3 / 2)) P) ∧ iIndepFun X P ∧
      (∀ n, AEMeasurable (θh n) P) ∧ (∀ n ω, θh n ω ∈ gpdK) ∧
      ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) gpdK
        (θh n ω) := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) (3 / 2))
  choose g hgm hg using exists_measurable_gpdMLE isCompact_gpdK gpdK_sub
    ⟨_, interior_subset mem_interior_gpdK⟩
  exact ⟨Ω, _, P, hP, X, fun n ω => g n (fun i : Fin n => X i ω), hlaw, hind,
    fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hlaw i).aemeasurable),
    fun n ω => (hg n _).1, fun n ω => (hg n _).2⟩

/-- **Non-vacuity of `tendstoInDistribution_gpdReturnLevel`** ([Coles, §4.3.3]): an iid
`GPD(1/4, 3/2)` sample, maximizers over `[-1/2, 1/2] × [1, 2]`, `u = 10`, `ζ = 1/10`, `N = 100`. All
hypotheses discharged; the limit is `N(0, gpdReturnLevelVar (1/4) (3/2) (1/10) 100)`. -/
theorem test_nonvacuous_tendstoInDistribution_gpdReturnLevel :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (θh : ℕ → Ω → ℝ × ℝ),
      (∀ i, HasLaw (X i) (gpdMeasure (1 / 4) (3 / 2)) P) ∧ iIndepFun X P ∧
      (∀ n ω, θh n ω ∈ gpdK ∧
        IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) gpdK (θh n ω)) ∧
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
        (gpdReturnLevel 10 (θh n ω).1 (θh n ω).2 (1 / 10) 100 -
          gpdReturnLevel 10 (1 / 4) (3 / 2) (1 / 10) 100))
        atTop (id : ℝ → ℝ) (fun _ => P)
        (gaussianReal 0 (gpdReturnLevelVar (1 / 4) (3 / 2) (1 / 10) 100).toNNReal) := by
  obtain ⟨Ω, _, P, hP, X, θh, hlaw, hind, hθm, hθK, hmax⟩ := exists_gpdSample
  refine ⟨Ω, _, P, hP, X, θh, hlaw, hind, fun n ω => ⟨hθK n ω, hmax n ω⟩, ?_⟩
  exact tendstoInDistribution_gpdReturnLevel isCompact_gpdK gpdK_sub mem_interior_gpdK
    (by norm_num) (by norm_num) (by norm_num) hlaw hind hθm hθK hmax (by norm_num) HasLaw.id

/-- **Non-vacuity of `tendsto_measure_mem_gpdReturnLevelInterval`** ([Coles, §4.3.3]): the same
sample, `N ζ = 10 > 1`; the coverage of the plug-in Wald interval tends to `N(0, 1)[-z, z]`, for every
`z`. All hypotheses discharged. -/
theorem test_nonvacuous_tendsto_measure_mem_gpdReturnLevelInterval :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (θh : ℕ → Ω → ℝ × ℝ),
      (∀ i, HasLaw (X i) (gpdMeasure (1 / 4) (3 / 2)) P) ∧ iIndepFun X P ∧
      (∀ n ω, θh n ω ∈ gpdK ∧
        IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) gpdK (θh n ω)) ∧
      ∀ z : ℝ, Tendsto (fun n : ℕ => P {ω | gpdReturnLevel 10 (1 / 4) (3 / 2) (1 / 10) 100 ∈ Icc
        (gpdReturnLevel 10 (θh n ω).1 (θh n ω).2 (1 / 10) 100 -
          z * √(gpdReturnLevelVar (θh n ω).1 (θh n ω).2 (1 / 10) 100) / √(n : ℝ))
        (gpdReturnLevel 10 (θh n ω).1 (θh n ω).2 (1 / 10) 100 +
          z * √(gpdReturnLevelVar (θh n ω).1 (θh n ω).2 (1 / 10) 100) / √(n : ℝ))})
        atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  obtain ⟨Ω, _, P, hP, X, θh, hlaw, hind, hθm, hθK, hmax⟩ := exists_gpdSample
  refine ⟨Ω, _, P, hP, X, θh, hlaw, hind, fun n ω => ⟨hθK n ω, hmax n ω⟩, fun z => ?_⟩
  exact tendsto_measure_mem_gpdReturnLevelInterval isCompact_gpdK gpdK_sub mem_interior_gpdK
    (by norm_num) (by norm_num) (by norm_num) hlaw hind hθm hθK hmax (by norm_num) z

/-! ### A synthetic estimator

`θ̂ₙ = θ₀ + Z / √n`, so that `√n (θ̂ₙ - θ₀) = Z` for `n ≥ 1`. -/

section Synthetic

variable {κ : Type} [Fintype κ]

/-- Test-specific: a sequence equal to `Z` for `n ≥ 1` tends in distribution to `Z`. -/
private theorem tendstoInDistribution_of_eventually_eq {E Ω : Type} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → E} {Z : Ω → E} (hZ : AEMeasurable Z P)
    (hX : ∀ n, AEMeasurable (X n) P) (h : ∀ n, 1 ≤ n → X n = Z) :
    TendstoInDistribution X atTop Z (fun _ => P) P where
  forall_aemeasurable := hX
  aemeasurable_limit := hZ
  tendsto := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Subtype.ext (by simp [h n hn])

/-- Test-specific: `√n (ω / √n) = ω` for `n ≥ 1`. -/
private theorem sqrt_mul_div_sqrt {n : ℕ} (hn : 1 ≤ n) (x : ℝ) : √(n : ℝ) * (x / √(n : ℝ)) = x := by
  have h : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp

/-- Test-specific: the synthetic estimator of three parameters. -/
private noncomputable def est₃ (a b c : ℝ) (n : ℕ) (ω : EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ × ℝ :=
  (a + ω 0 / √(n : ℝ), b + ω 1 / √(n : ℝ), c + ω 2 / √(n : ℝ))

/-- Test-specific: `est₃` is measurable. -/
private theorem measurable_est₃ (a b c : ℝ) (n : ℕ) : Measurable (est₃ a b c n) := by
  unfold est₃
  fun_prop

/-- Test-specific: `√n (est₃ - θ₀) ⇒ N(0, V)`, exactly, for `n ≥ 1`. -/
private theorem tendstoInDistribution_est₃ (a b c : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      !₂[(est₃ a b c n ω).1 - a, (est₃ a b c n ω).2.1 - b, (est₃ a b c n ω).2.2 - c]) atTop
      (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (fun _ => multivariateGaussian 0 V) (multivariateGaussian 0 V) := by
  refine tendstoInDistribution_of_eventually_eq aemeasurable_id (fun n => ?_) fun n hn => ?_
  · refine Measurable.aemeasurable ?_
    simp only [est₃]
    fun_prop
  · funext ω
    ext i
    fin_cases i <;> simp [est₃, sqrt_mul_div_sqrt hn]

/-- **Non-vacuity of `tendstoInDistribution_gevReturnLevel`** ([Coles, §3.3.3]): `ξ₀ = 1/4`,
`μ₀ = 1/2`, `σ₀ = 3/2`, `m = 100`, for **every** positive semidefinite `V`, with the synthetic
estimator `θ₀ + Z / √n`, `Z ∼ N(0, V)`. All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInDistribution_gevReturnLevel (V : Matrix (Fin 3) (Fin 3) ℝ)
    (hV : V.PosSemidef) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).1 (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).2.1
        (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).2.2 100 - gevReturnLevel (1 / 4) (1 / 2) (3 / 2) 100))
      atTop (id : ℝ → ℝ) (fun _ => multivariateGaussian 0 V)
      (gaussianReal 0 (gevReturnLevelGrad (1 / 4) (3 / 2) 100 ⬝ᵥ
        V *ᵥ gevReturnLevelGrad (1 / 4) (3 / 2) 100).toNNReal) :=
  tendstoInDistribution_gevReturnLevel (by norm_num) (by norm_num)
    (fun n => (measurable_est₃ _ _ _ n).aemeasurable) hV
    (tendstoInDistribution_est₃ _ _ _ V) HasLaw.id HasLaw.id

/-- **Non-vacuity of `tendsto_measure_mem_gevReturnLevelInterval`** ([Coles, §3.3.3]): the synthetic
estimator with `V = I`, so that `s² = ‖∇z‖² ≥ 1 > 0` (the middle gradient coordinate is `1`), and
the constant standard error `Ŝₙ = s`. All hypotheses discharged. -/
theorem test_nonvacuous_tendsto_measure_mem_gevReturnLevelInterval (z : ℝ) :
    ∃ s : ℝ, 0 < s ∧ Tendsto (fun n : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) 1)
      {ω | gevReturnLevel (1 / 4) (1 / 2) (3 / 2) 100 ∈ Icc
        (gevReturnLevel (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).1 (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).2.1
          (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).2.2 100 - z * s / √(n : ℝ))
        (gevReturnLevel (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).1 (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).2.1
          (est₃ (1 / 4) (1 / 2) (3 / 2) n ω).2.2 100 + z * s / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  set g := gevReturnLevelGrad (1 / 4) (3 / 2) 100
  have hq : g ⬝ᵥ (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ g = (g 0) ^ 2 + 1 + (g 2) ^ 2 := by
    have h1 : g 1 = 1 := by simp [g, gevReturnLevelGrad]
    simp [dotProduct, Fin.sum_univ_three, Matrix.one_mulVec, h1]
    ring
  have hpos : 0 < g ⬝ᵥ (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ g := by rw [hq]; positivity
  refine ⟨√(g ⬝ᵥ (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ g), Real.sqrt_pos.2 hpos, ?_⟩
  exact tendsto_measure_mem_gevReturnLevelInterval (by norm_num) (by norm_num)
    (fun n => (measurable_est₃ _ _ _ n).aemeasurable) Matrix.PosSemidef.one
    (tendstoInDistribution_est₃ _ _ _ 1) HasLaw.id (Real.sqrt_pos.2 hpos)
    (Real.sq_sqrt hpos.le)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => tendsto_const_nhds))
    (fun _ => aemeasurable_const) z

/-- **Non-vacuity of `tendstoInDistribution_gpdReturnLevel₃`** ([Coles, §4.3.3]): `ζ₀ = 1/10`,
`ξ₀ = 1/4`, `σ₀ = 3/2`, `N = 100`, for every positive semidefinite `V`, with the synthetic estimator.
All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInDistribution_gpdReturnLevel₃ (V : Matrix (Fin 3) (Fin 3) ℝ)
    (hV : V.PosSemidef) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gpdReturnLevel 10 (est₃ (1 / 10) (1 / 4) (3 / 2) n ω).2.1
        (est₃ (1 / 10) (1 / 4) (3 / 2) n ω).2.2 (est₃ (1 / 10) (1 / 4) (3 / 2) n ω).1 100 -
        gpdReturnLevel 10 (1 / 4) (3 / 2) (1 / 10) 100))
      atTop (id : ℝ → ℝ) (fun _ => multivariateGaussian 0 V)
      (gaussianReal 0 (gpdReturnLevelGrad₃ (1 / 10) (1 / 4) (3 / 2) 100 ⬝ᵥ
        V *ᵥ gpdReturnLevelGrad₃ (1 / 10) (1 / 4) (3 / 2) 100).toNNReal) :=
  tendstoInDistribution_gpdReturnLevel₃ (by norm_num) (by norm_num)
    (fun n => (measurable_est₃ _ _ _ n).aemeasurable) hV
    (tendstoInDistribution_est₃ _ _ _ V) HasLaw.id HasLaw.id

/-- Test-specific: the synthetic estimator of two parameters. -/
private noncomputable def est₂ (a b : ℝ) (n : ℕ) (ω : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  (a + ω 0 / √(n : ℝ), b + ω 1 / √(n : ℝ))

/-- Test-specific: `est₂` is measurable. -/
private theorem measurable_est₂ (a b : ℝ) (n : ℕ) : Measurable (est₂ a b n) := by
  unfold est₂
  fun_prop

/-- Test-specific: `√n (est₂ - θ₀) ⇒ N(0, V)`, exactly, for `n ≥ 1`. -/
private theorem tendstoInDistribution_est₂ (a b : ℝ) (V : Matrix (Fin 2) (Fin 2) ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
      !₂[(est₂ a b n ω).1 - a, (est₂ a b n ω).2 - b]) atTop
      (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (fun _ => multivariateGaussian 0 V) (multivariateGaussian 0 V) := by
  refine tendstoInDistribution_of_eventually_eq aemeasurable_id (fun n => ?_) fun n hn => ?_
  · refine Measurable.aemeasurable ?_
    simp only [est₂]
    fun_prop
  · funext ω
    ext i
    fin_cases i <;> simp [est₂, sqrt_mul_div_sqrt hn]

/-- **Non-vacuity of `tendstoInDistribution_gumbelReturnLevel`** ([Coles, §3.3.3]): `μ₀ = 1/2`,
`σ₀ = 3/2`, `m = 100`, for every positive semidefinite `V`, with the synthetic estimator. All
hypotheses discharged. The statement does not assume `m > 1`; for the junk value at `m ≤ 1` see
`test_gevReturnLevel_zero_of_le_one` in `Test/JunkValues.lean`. -/
theorem test_nonvacuous_tendstoInDistribution_gumbelReturnLevel (V : Matrix (Fin 2) (Fin 2) ℝ)
    (hV : V.PosSemidef) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel 0 (est₂ (1 / 2) (3 / 2) n ω).1 (est₂ (1 / 2) (3 / 2) n ω).2 100 -
        gevReturnLevel 0 (1 / 2) (3 / 2) 100))
      atTop (id : ℝ → ℝ) (fun _ => multivariateGaussian 0 V)
      (gaussianReal 0 ((!₂[1, -Real.log (-Real.log (1 - 1 / 100))] : EuclideanSpace ℝ (Fin 2)) ⬝ᵥ
        V *ᵥ (!₂[1, -Real.log (-Real.log (1 - 1 / 100))] : EuclideanSpace ℝ (Fin 2))).toNNReal) :=
  tendstoInDistribution_gumbelReturnLevel
    (fun n => (measurable_est₂ _ _ n).aemeasurable) hV
    (tendstoInDistribution_est₂ _ _ V) HasLaw.id HasLaw.id

/-- **Non-vacuity of `tendstoInDistribution_gpdReturnLevel_of_tendstoInDistribution`**: `ξ₀ = 1/4`,
`σ₀ = 3/2`, `ζ = 1/10`, `N = 100`, for every positive semidefinite `V`, with the synthetic estimator.
All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInDistribution_gpdReturnLevel_of_tendstoInDistribution
    (V : Matrix (Fin 2) (Fin 2) ℝ) (hV : V.PosSemidef) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gpdReturnLevel 10 (est₂ (1 / 4) (3 / 2) n ω).1 (est₂ (1 / 4) (3 / 2) n ω).2 (1 / 10) 100 -
        gpdReturnLevel 10 (1 / 4) (3 / 2) (1 / 10) 100))
      atTop (id : ℝ → ℝ) (fun _ => multivariateGaussian 0 V)
      (gaussianReal 0 (gpdReturnLevelGrad (1 / 4) (3 / 2) (1 / 10) 100 ⬝ᵥ
        V *ᵥ gpdReturnLevelGrad (1 / 4) (3 / 2) (1 / 10) 100).toNNReal) :=
  tendstoInDistribution_gpdReturnLevel_of_tendstoInDistribution (by norm_num) (by norm_num)
    (fun n => (measurable_est₂ _ _ n).aemeasurable) hV
    (tendstoInDistribution_est₂ _ _ V) HasLaw.id HasLaw.id

end Synthetic

end ExtremeValueTheory.Test.NonVacuity.ReturnLevels
