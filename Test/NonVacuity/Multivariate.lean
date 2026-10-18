import ExtremeValueTheory

/-! # Non-vacuity tests: multivariate extremes and max-stable laws

Each test builds a concrete object satisfying every hypothesis of a headline theorem and applies
the theorem to it.

Concrete objects used:
* the Pareto(`α`) law `paretoMeasure 1 α` on `ℝ` (Mathlib), and the vectors `(|Z|, |Z|)`
  (complete dependence) and `(|Z₁|, |Z₂|)` with `Z₁, Z₂` independent Pareto (independence);
* simple max-stable laws obtained from de Haan's construction with the library's
  `independentSpectralMeasure` and `comonotoneSpectralMeasure`, and the Smith model;
* the comonotone and independent bivariate laws with standard Gumbel margins, which are in their
  own multivariate domain of attraction with `aₙ = 1`, `bₙ = log n`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory.Test.Multivariate

/-! ### Pareto helpers -/

section Pareto

variable {α : ℝ}

/-- `P(x < |Z|) = P(Z > x)` for Pareto `Z` and `x ≥ 0`. -/
theorem pareto_real_lt_abs (x : ℝ) :
    (paretoMeasure 1 α).real {ω | x < |ω|} = tail (paretoMeasure 1 α) x := by
  rw [tail]
  refine measureReal_congr ?_
  filter_upwards [ae_one_lt_paretoMeasure (α := α)] with ω hω
  have : |ω| = ω := abs_of_pos (one_pos.trans hω)
  simp [this, Set.mem_Ioi]

/-- The tail `x ↦ P(x < |Z|)` of a Pareto law is regularly varying with index `-α`. -/
theorem isRegularlyVarying_pareto_abs (hα : 0 < α) :
    IsRegularlyVarying (fun x => (paretoMeasure 1 α).real {ω | x < |ω|}) (-α) :=
  (isRegularlyVarying_tail_paretoMeasure one_pos hα).congr
    (Eventually.of_forall fun x => (pareto_real_lt_abs x).symm)

end Pareto

/-! ### Multivariate regular variation -/

section RegVar

/-- The completely dependent vector `(|Z|, |Z|)`, `Z` Pareto(`α`), on `Ω = ℝ`. -/
noncomputable def diagVec (ω : ℝ) : ℝ × ℝ := (|ω|, |ω|)

theorem measurable_diagVec : Measurable diagVec := by
  unfold diagVec; fun_prop

/-- `(|Z|, |Z|)` is regularly varying (library example `isRegVarVector_diag`, whose hypotheses
are discharged here for an explicit Pareto law). -/
theorem isRegVarVector_diagVec {α : ℝ} (hα : 0 < α) :
    haveI := isProbabilityMeasure_paretoMeasure one_pos hα
    IsRegVarVector (paretoMeasure 1 α) diagVec α
      (polarMeasure α (Measure.dirac ((1 : ℝ), (1 : ℝ)))) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  exact isRegVarVector_diag hα continuous_abs.measurable (fun ω => abs_nonneg ω)
    (isRegularlyVarying_pareto_abs hα)

/-- Non-vacuity of `isRegVarVector_iff` (polar decomposition), both directions, on the
completely dependent Pareto vector `(|Z|, |Z|)`, `α = 2`. -/
theorem test_nonvacuous_isRegVarVector_iff :
    ∃ μ : Measure (ℝ × ℝ), IsRegVarVector (paretoMeasure 1 2) diagVec 2 μ := by
  have := isProbabilityMeasure_paretoMeasure (one_pos (α := ℝ)) (two_pos (α := ℝ))
  -- forward direction: regularly varying norm and a spectral measure
  have h := (isRegVarVector_iff (P := paretoMeasure 1 2) two_pos measurable_diagVec).1
    ⟨_, isRegVarVector_diagVec two_pos⟩
  -- backward direction: rebuild the exponent measure from the polar data
  exact (isRegVarVector_iff two_pos measurable_diagVec).2 h

/-- Non-vacuity of `IsRegVarVector.eq_polarMeasure`: the exponent measure of `(|Z|, |Z|)`
is the polar measure of its spectral measure. -/
theorem test_nonvacuous_eq_polarMeasure :
    polarMeasure 2 (Measure.dirac ((1 : ℝ), (1 : ℝ))) =
      polarMeasure 2 (spectralMeasure (polarMeasure 2 (Measure.dirac ((1 : ℝ), (1 : ℝ))))) := by
  have := isProbabilityMeasure_paretoMeasure (one_pos (α := ℝ)) (two_pos (α := ℝ))
  exact (isRegVarVector_diagVec two_pos).eq_polarMeasure two_pos measurable_diagVec

/-- The independent vector `(|Z₁|, |Z₂|)`, `Z₁, Z₂` iid Pareto, on `Ω = ℝ × ℝ`. -/
noncomputable def indepVec (ω : ℝ × ℝ) : ℝ × ℝ := (|ω.1|, |ω.2|)

theorem prod_real_fst {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ((paretoMeasure 1 α).prod (paretoMeasure 1 α)).real {ω | x < |ω.1|} =
      (paretoMeasure 1 α).real {ω | x < |ω|} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hm : MeasurableSet {ω : ℝ | x < |ω|} := measurableSet_lt measurable_const (by fun_prop)
  have h := Measure.map_apply (μ := (paretoMeasure 1 α).prod (paretoMeasure 1 α))
    measurable_fst hm
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  rw [measureReal_def, measureReal_def, h]
  rfl

theorem prod_real_snd {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ((paretoMeasure 1 α).prod (paretoMeasure 1 α)).real {ω | x < |ω.2|} =
      (paretoMeasure 1 α).real {ω | x < |ω|} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hm : MeasurableSet {ω : ℝ | x < |ω|} := measurableSet_lt measurable_const (by fun_prop)
  have h := Measure.map_apply (μ := (paretoMeasure 1 α).prod (paretoMeasure 1 α))
    measurable_snd hm
  rw [Measure.map_snd_prod, measure_univ, one_smul] at h
  rw [measureReal_def, measureReal_def, h]
  rfl

/-- Non-vacuity of `isRegVarVector_of_indepFun` (asymptotic independence) and, through it, of
`isRegVarVector_iff`: independent Pareto(`2`) coordinates, tail balance `c = 1`. -/
theorem test_nonvacuous_isRegVarVector_of_indepFun :
    IsRegVarVector ((paretoMeasure 1 2).prod (paretoMeasure 1 2)) indepVec 2
      (polarMeasure 2 (axesSpectralMeasure 1)) := by
  have := isProbabilityMeasure_paretoMeasure (one_pos (α := ℝ)) (two_pos (α := ℝ))
  have hRV := isRegularlyVarying_pareto_abs (α := 2) two_pos
  have hRV₁ : IsRegularlyVarying (fun x =>
      ((paretoMeasure 1 2).prod (paretoMeasure 1 2)).real {ω : ℝ × ℝ | x < |ω.1|}) (-2) :=
    hRV.congr (Eventually.of_forall fun x => (prod_real_fst two_pos x).symm)
  refine isRegVarVector_of_indepFun two_pos (by fun_prop) (by fun_prop)
    (fun ω => abs_nonneg _) (fun ω => abs_nonneg _)
    (indepFun_prod (X := fun ω : ℝ => |ω|) (Y := fun ω : ℝ => |ω|) (by fun_prop) (by fun_prop))
    hRV₁ zero_le_one ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hRV.eventually_pos] with x hx
  rw [prod_real_fst two_pos, prod_real_snd two_pos, div_self hx.ne']

end RegVar

/-! ### Converse Cramér–Wold device -/

section CramerWold

theorem half_ne_int : ∀ k : ℤ, (1 / 2 : ℝ) ≠ k := by
  intro k h
  rcases le_or_gt k 0 with hk | hk
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    linarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith

/-- Non-vacuity of `CramerWold.isRegVarVector_of_tendsto_linear` (Basrak–Davis–Mikosch, the
non-integer case): `X = (|Z|, |Z|)` with `Z` Pareto(`1/2`), `α = 1/2 ∉ ℤ`. The hypotheses on
linear functionals (`P(L X > x) / V(x) → w(L)` for every `L`) are discharged with
`V(x) = P(‖X‖ > x)` through the forward direction `IsRegVarVector.tendsto_linear`; the
nondegeneracy `w L ≠ 0` is checked on `L = fst`, where `w(fst) = 1`. -/
theorem test_nonvacuous_isRegVarVector_of_tendsto_linear :
    ∃ μ : Measure (ℝ × ℝ), IsRegVarVector (paretoMeasure 1 (1 / 2)) diagVec (1 / 2) μ := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have h := isRegVarVector_diagVec hα
  refine CramerWold.isRegVarVector_of_tendsto_linear measurable_diagVec hα half_ne_int
    h.isRegularlyVarying (fun L => h.tendsto_linear measurable_diagVec L)
    ⟨ContinuousLinearMap.fst ℝ ℝ ℝ, ?_⟩
  rw [measureReal_def, polarMeasure_one_lt_linear hα, lintegral_dirac]
  norm_num

end CramerWold

/-! ### Max-stable laws: spectral construction, existence and uniqueness -/

section MaxStable

/-- Non-vacuity of `exists_isSimpleMaxStable_of_spectralMeasure` (de Haan's construction, "⇐"):
the vertex spectral measure `independentSpectralMeasure` on `[0, ∞]²` (independence) is
normalized, so it yields a simple max-stable law. -/
theorem test_nonvacuous_exists_isSimpleMaxStable_independent :
    ∃ ν : Measure (Fin 2 → ℝ), IsSimpleMaxStable ν ∧ ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
      ν (Iic y) = ENNReal.ofReal (Real.exp (-(∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i)
        ∂(independentSpectralMeasure (ι := Fin 2))).toReal)) :=
  exists_isSimpleMaxStable_of_spectralMeasure _ lintegral_apply_independentSpectralMeasure

/-- Same, for complete dependence (`comonotoneSpectralMeasure`, a unit mass at `(1, 1)`). -/
theorem test_nonvacuous_exists_isSimpleMaxStable_comonotone :
    ∃ ν : Measure (Fin 2 → ℝ), IsSimpleMaxStable ν ∧ ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
      ν (Iic y) = ENNReal.ofReal (Real.exp (-(∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i)
        ∂(comonotoneSpectralMeasure (ι := Fin 2))).toReal)) :=
  exists_isSimpleMaxStable_of_spectralMeasure _ lintegral_apply_comonotoneSpectralMeasure

/-- Non-vacuity of `IsSimpleMaxStable.exists_hasSpectralMeasure` (de Haan–Resnick, "⇒") and
`IsSimpleMaxStable.existsUnique_hasSpectralMeasure`, on the simple max-stable law with
independent unit Fréchet margins built above. -/
theorem test_nonvacuous_existsUnique_hasSpectralMeasure :
    ∃ ν : Measure (Fin 2 → ℝ), IsSimpleMaxStable ν ∧
      (∃ H : Measure (Fin 2 → ℝ≥0∞), IsFiniteMeasure H ∧ (∀ᵐ w ∂H, ∀ i, w i ≤ 1) ∧
        (∀ᵐ w ∂H, ⨆ i, w i = 1) ∧ (∀ i, ∫⁻ w, w i ∂H = 1) ∧ HasSpectralMeasure ν H) ∧
      ∃! H : Measure (Fin 2 → ℝ≥0∞), IsFiniteMeasure H ∧ (∀ᵐ w ∂H, ⨆ i, w i = 1) ∧
        HasSpectralMeasure ν H := by
  obtain ⟨ν, hν, -⟩ := test_nonvacuous_exists_isSimpleMaxStable_independent
  exact ⟨ν, hν, hν.exists_hasSpectralMeasure, hν.existsUnique_hasSpectralMeasure⟩

/-- Non-vacuity of `IsSimpleMaxStable.isRegVarVector` (max-stable vectors are regularly varying
with index 1): `X = id` on `(ℝ², ν)` with `ν` the independent simple max-stable law, and `H` its
spectral measure on the sup-norm sphere supplied by `exists_hasSpectralMeasure`. -/
theorem test_nonvacuous_isSimpleMaxStable_isRegVarVector :
    ∃ (ν : Measure (Fin 2 → ℝ)) (H : Measure (Fin 2 → ℝ≥0∞)),
      IsRegVarVector ν id 1 (maxStableTailMeasure H) := by
  obtain ⟨ν, hν, -⟩ := test_nonvacuous_exists_isSimpleMaxStable_independent
  have := hν.isProbabilityMeasure
  obtain ⟨H, hfin, -, hsph, -, hS⟩ := hν.exists_hasSpectralMeasure
  have hS' : HasSpectralMeasure (ν.map id) H := by rwa [Measure.map_id]
  have hν' : IsSimpleMaxStable (ν.map id) := by rwa [Measure.map_id]
  exact ⟨ν, H, IsSimpleMaxStable.isRegVarVector measurable_id hS' hν' hsph⟩

/-- Non-vacuity of `IsSimpleMaxStable.convexOn_pickandsDependence` (Pickands' convexity) on the
comonotone bivariate simple max-stable law. -/
theorem test_nonvacuous_convexOn_pickandsDependence :
    ∃ ν : Measure (Fin 2 → ℝ), IsSimpleMaxStable ν ∧
      ConvexOn ℝ (Icc 0 1) (pickandsDependence ν) := by
  obtain ⟨ν, hν, -⟩ := test_nonvacuous_exists_isSimpleMaxStable_comonotone
  exact ⟨ν, hν, hν.convexOn_pickandsDependence⟩

/-- Non-vacuity of `IsPoissonRandomMeasure.isSimpleMaxStable_map_process` (de Haan's spectral
representation of max-stable processes) on the **Smith model**: a Poisson random measure with
intensity `ζ⁻² dζ ⊗ du` on `ℝ × ℝ` (existence: `exists_isPoissonRandomMeasure`) and the Gaussian
kernels `W t u = φ(t - u)`, `∫ W t = 1`. The finite-dimensional law at times `0, 1` is simple
max-stable. -/
theorem test_nonvacuous_isSimpleMaxStable_map_process :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure (ℝ × ℝ)),
      IsSimpleMaxStable (P.map fun ω (i : Fin 2) ↦
        spectralVector (smithKernel 1) (N ω) (![0, 1] i)) := by
  obtain ⟨Ω, _, P, N, -, hN⟩ := exists_isPoissonRandomMeasure ((radialMeasure 1).prod (volume : Measure ℝ))
  exact ⟨Ω, _, P, N, hN.isSimpleMaxStable_map_process (measurable_smithKernel 1)
    (lintegral_smithKernel one_ne_zero) _⟩

end MaxStable

/-! ### Multivariate domains of attraction and the multivariate GPD

The multivariate GPD theorem needs `ν(Iic (x ⊓ 0)) > 0` and `ν(Iic 0) < 1`, so the limit law must
put mass on the negative orthant: a simple max-stable law (unit Fréchet margins, supported on the
positive orthant) can never satisfy `ν(Iic (x ⊓ 0)) > 0`. We therefore use **Gumbel margins**,
`G(t) = exp(-e^{-t})`. A law with Gumbel margins that is comonotone or independent satisfies
`F(x + log n)^n = F(x)` exactly, so it is in its own domain of attraction with `aₙ = 1`,
`bₙ = log n`. -/

section MDA

/-- The standard Gumbel law on `ℝ`. -/
noncomputable def gumbelLaw : Measure ℝ := standardGumbelCDF.toStieltjesFunction.measure

instance : IsProbabilityMeasure gumbelLaw :=
  CumulativeDistributionFunction.isProbabilityMeasure_measure_coe _

/-- The Gumbel c.d.f. `G(t) = exp(-e^{-t})`. -/
noncomputable def G (t : ℝ) : ℝ := Real.exp (-Real.exp (-t))

theorem continuous_G : Continuous G := by unfold G; fun_prop

theorem G_pos (t : ℝ) : 0 < G t := Real.exp_pos _

theorem gumbelLaw_real_Iic (t : ℝ) : gumbelLaw.real (Iic t) = G t := by
  rw [measureReal_def, gumbelLaw, ← CumulativeDistributionFunction.apply_eq_measure_Iic,
    standardGumbelCDF_apply_eq, G]

/-- Max-stability of the Gumbel c.d.f.: `G(t + log n)^n = G(t)`. -/
theorem G_add_log_pow (t : ℝ) {n : ℕ} (hn : 1 ≤ n) : G (t + Real.log n) ^ n = G t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [G, G, ← Real.exp_nat_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log n),
    Real.exp_log hn0]
  congr 1
  field_simp

/-- Normalizing constants `aₙ = 1`, `bₙ = log n`. -/
def aN : ℕ → Fin 2 → ℝ := fun _ _ => 1

noncomputable def bN : ℕ → Fin 2 → ℝ := fun n _ => Real.log n

theorem aN_mul_add (n : ℕ) (x : Fin 2 → ℝ) (i : Fin 2) :
    (aN n * x + bN n) i = x i + Real.log n := by
  simp [aN, bN]

/-! #### Comonotone Gumbel vector `(Z, Z)` -/

/-- The law of `(Z, Z)`, `Z` standard Gumbel. -/
noncomputable def comonoGumbel : Measure (Fin 2 → ℝ) := gumbelLaw.map fun z _ => z

theorem measurable_diag2 : Measurable fun z : ℝ => fun _ : Fin 2 => z :=
  Measurable.of_eval fun _ => measurable_id

instance : IsProbabilityMeasure comonoGumbel :=
  (Measure.isProbabilityMeasure_map_iff measurable_diag2.aemeasurable).2 inferInstance

theorem comonoGumbel_real_Iic (y : Fin 2 → ℝ) :
    comonoGumbel.real (Iic y) = G (min (y 0) (y 1)) := by
  rw [comonoGumbel, map_measureReal_apply measurable_diag2 measurableSet_Iic]
  have : (fun z : ℝ => fun _ : Fin 2 => z) ⁻¹' Iic y = Iic (min (y 0) (y 1)) := by
    ext z; simp [Pi.le_def, Fin.forall_fin_two]
  rw [this, gumbelLaw_real_Iic]

theorem marginal_comonoGumbel (i : Fin 2) : ⇑(marginal comonoGumbel i) = G := by
  funext t
  rw [marginal_apply, comonoGumbel, map_measureReal_apply measurable_diag2
    (measurableSet_le (measurable_pi_apply i) measurable_const)]
  exact gumbelLaw_real_Iic t

theorem isMDAWith_comonoGumbel : IsMDAWith comonoGumbel comonoGumbel aN bN := by
  refine ⟨fun _ _ => one_pos, fun x _ => tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [comonoGumbel_real_Iic, comonoGumbel_real_Iic, aN_mul_add, aN_mul_add,
    min_add_add_right, G_add_log_pow _ hn]

/-- Non-vacuity of `isMDAWith_iff` (the multivariate domain of attraction as marginal domains
of attraction plus convergence of the standardized joint tail), forward direction, on the
comonotone Gumbel vector; continuity of all marginals is discharged. -/
theorem test_nonvacuous_isMDAWith_iff_comonotone :
    (∀ i t, Tendsto (fun n ↦ marginal comonoGumbel i (aN n i * t + bN n i) ^ n) atTop
        (𝓝 (marginal comonoGumbel i t))) ∧
      ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) → Tendsto (fun n : ℕ ↦
        n * (1 - comonoGumbel.real (Iic fun i ↦ (marginal comonoGumbel i).tailQuantile (n * y i))))
        atTop (𝓝 (maxStableExponent (frechetStandardization comonoGumbel) y)) := by
  have hc : ∀ i, Continuous (marginal comonoGumbel i) := fun i => by
    rw [marginal_comonoGumbel]; exact continuous_G
  exact (isMDAWith_iff hc hc fun _ _ => one_pos).1 isMDAWith_comonoGumbel

/-- Non-vacuity of `IsMDAWith.tendsto_conditionalExcessCDF` (Rootzén–Tajvidi: the conditional
excess law converges to the multivariate GPD) on the comonotone Gumbel vector, at every `x`:
`ν(Iic (x ⊓ 0)) = G(min) > 0` and `ν(Iic 0) = e⁻¹ < 1`. -/
theorem test_nonvacuous_tendsto_conditionalExcessCDF_comonotone (x : Fin 2 → ℝ) :
    Tendsto (fun n ↦ conditionalExcessCDF comonoGumbel (aN n) (bN n) x) atTop
      (𝓝 (mgpdCDF comonoGumbel x)) := by
  have hc : ∀ i, Continuous (marginal comonoGumbel i) := fun i => by
    rw [marginal_comonoGumbel]; exact continuous_G
  refine isMDAWith_comonoGumbel.tendsto_conditionalExcessCDF hc ?_ ?_
  · rw [comonoGumbel_real_Iic]; exact G_pos _
  · rw [comonoGumbel_real_Iic]
    simp only [Pi.zero_apply, min_self, G, neg_zero, Real.exp_zero]
    rw [Real.exp_lt_one_iff]; norm_num

/-! #### Independent Gumbel vector (independence copula) -/

/-- The law of `(Z₁, Z₂)`, `Z₁, Z₂` iid standard Gumbel. -/
noncomputable def indepGumbel : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gumbelLaw

instance : IsProbabilityMeasure indepGumbel := by unfold indepGumbel; infer_instance

theorem indepGumbel_real_Iic (y : Fin 2 → ℝ) :
    indepGumbel.real (Iic y) = G (y 0) * G (y 1) := by
  rw [indepGumbel, ← Set.pi_univ_Iic, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod,
    Fin.prod_univ_two]
  simp only [← measureReal_def, gumbelLaw_real_Iic]

theorem marginal_indepGumbel (i : Fin 2) : ⇑(marginal indepGumbel i) = G := by
  funext t
  have h := map_measureReal_apply (μ := Measure.pi fun _ : Fin 2 => gumbelLaw)
    (measurable_pi_apply i) (measurableSet_Iic (a := t))
  rw [(measurePreserving_eval (μ := fun _ : Fin 2 => gumbelLaw) i).map_eq] at h
  rw [marginal_apply, ← gumbelLaw_real_Iic t, h]
  rfl

theorem isMDAWith_indepGumbel : IsMDAWith indepGumbel indepGumbel aN bN := by
  refine ⟨fun _ _ => one_pos, fun x _ => tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [indepGumbel_real_Iic, indepGumbel_real_Iic, aN_mul_add, aN_mul_add, mul_pow,
    G_add_log_pow _ hn, G_add_log_pow _ hn]

/-- Non-vacuity of `isMDAWith_iff` on the independence copula with Gumbel margins. -/
theorem test_nonvacuous_isMDAWith_iff_independent :
    (∀ i t, Tendsto (fun n ↦ marginal indepGumbel i (aN n i * t + bN n i) ^ n) atTop
        (𝓝 (marginal indepGumbel i t))) ∧
      ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) → Tendsto (fun n : ℕ ↦
        n * (1 - indepGumbel.real (Iic fun i ↦ (marginal indepGumbel i).tailQuantile (n * y i))))
        atTop (𝓝 (maxStableExponent (frechetStandardization indepGumbel) y)) := by
  have hc : ∀ i, Continuous (marginal indepGumbel i) := fun i => by
    rw [marginal_indepGumbel]; exact continuous_G
  exact (isMDAWith_iff hc hc fun _ _ => one_pos).1 isMDAWith_indepGumbel

/-- Converse direction of `isMDAWith_iff` on the independence copula: the marginal and joint-tail
conditions give back the domain of attraction. -/
theorem test_nonvacuous_isMDAWith_iff_independent_converse :
    IsMDAWith indepGumbel indepGumbel aN bN := by
  have hc : ∀ i, Continuous (marginal indepGumbel i) := fun i => by
    rw [marginal_indepGumbel]; exact continuous_G
  exact (isMDAWith_iff hc hc fun _ _ => one_pos).2 test_nonvacuous_isMDAWith_iff_independent

/-- Non-vacuity of `IsMDAWith.tendsto_conditionalExcessCDF` on the independence copula with
Gumbel margins, at every `x`. -/
theorem test_nonvacuous_tendsto_conditionalExcessCDF_independent (x : Fin 2 → ℝ) :
    Tendsto (fun n ↦ conditionalExcessCDF indepGumbel (aN n) (bN n) x) atTop
      (𝓝 (mgpdCDF indepGumbel x)) := by
  have hc : ∀ i, Continuous (marginal indepGumbel i) := fun i => by
    rw [marginal_indepGumbel]; exact continuous_G
  refine isMDAWith_indepGumbel.tendsto_conditionalExcessCDF hc ?_ ?_
  · rw [indepGumbel_real_Iic]; exact mul_pos (G_pos _) (G_pos _)
  · rw [indepGumbel_real_Iic]
    simp only [Pi.zero_apply, G, neg_zero, Real.exp_zero, ← Real.exp_add]
    rw [Real.exp_lt_one_iff]; norm_num

end MDA

end ExtremeValueTheory.Test.Multivariate
