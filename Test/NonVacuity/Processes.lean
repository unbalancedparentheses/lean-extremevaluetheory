import ExtremeValueTheory

/-!
# Non-vacuity: point processes and the Skorokhod space

Each test builds concrete objects satisfying all hypotheses of a headline theorem about Poisson
random measures, exceedance point processes, the Skorokhod space and the tail empirical process,
and applies the theorem.

Concrete objects:
* Poisson random measures: Lebesgue measure on `ℝ` and the exceedance intensity, through
  `ProbabilityTheory.exists_isPoissonRandomMeasure`.
* iid samples: the canonical product space `ℕ → ℝ` with `Measure.infinitePi`, coordinates as
  observations (`iIndepFun_infinitePi`, `Measure.infinitePi_map_eval`).
* The standard exponential law, in the Gumbel domain of attraction
  (`CumulativeDistributionFunction.isInMDAGumbel_standardExponentialCDF`).
* iid uniform `[0, 1]` samples and the intermediate sequence `k n = ⌊√n⌋`.
-/

open MeasureTheory ProbabilityTheory Filter Topology ENNReal ExtremeValueTheory

noncomputable section

namespace Test.NonVacuity.Processes

/-! ### Canonical iid samples -/

/-- iid sample of the law `μ` on the canonical product space. -/
abbrev iidLaw (μ : Measure ℝ) : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => μ

theorem iidLaw_iIndepFun (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    iIndepFun (fun i (ω : ℕ → ℝ) => ω i) (iidLaw μ) :=
  iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

theorem iidLaw_map (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : ℕ) :
    (iidLaw μ).map (fun ω : ℕ → ℝ => ω i) = μ :=
  Measure.infinitePi_map_eval _ i

/-- The coordinates of an iid sample of `F.measure` have c.d.f. `F`. -/
theorem iidLaw_cdf (F : CumulativeDistributionFunction) (i : ℕ) (x : ℝ) :
    (iidLaw F.measure).real {ω | ω i ≤ x} = F x := by
  have h := congrArg (fun m : Measure ℝ => m (Set.Iic x)) (iidLaw_map F.measure i)
  rw [Measure.map_apply (measurable_pi_apply i) measurableSet_Iic] at h
  rw [F.apply_eq_measure_Iic x, measureReal_def, ← h]
  rfl

/-! ### Poisson random measures -/

/-- `ProbabilityTheory.exists_isPoissonRandomMeasure`: a Poisson random measure with Lebesgue
intensity on `ℝ` (σ-finite, infinite) exists; its count on `[0, 1]` has the Poisson(1) Laplace
transform (`IsPoissonRandomMeasure.integral_exp_neg_apply`) and its Laplace functional at the
indicator of `[0, 1]` is given by `IsPoissonRandomMeasure.lintegral_exp_neg_lintegral`. -/
theorem test_nonvacuous_exists_isPoissonRandomMeasure :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure ℝ),
      IsProbabilityMeasure P ∧ IsPoissonRandomMeasure N volume P ∧
      ∫ ω, Real.exp (-(N ω (Set.Icc 0 1)).toReal) ∂P = Real.exp (-(1 * (1 - Real.exp (-1)))) := by
  obtain ⟨Ω, mΩ, P, N, hP, hN⟩ := exists_isPoissonRandomMeasure (volume : Measure ℝ)
  refine ⟨Ω, mΩ, P, N, hP, hN, ?_⟩
  rw [hN.integral_exp_neg_apply measurableSet_Icc (by simp)]
  simp

/-- `ProbabilityTheory.IsPoissonRandomMeasure.lintegral_exp_neg_lintegral` (Laplace functional
for every measurable `f ≥ 0`), applied to a Lebesgue-intensity Poisson random measure and
`f = 1_{[0,1]}`. -/
theorem test_nonvacuous_lintegral_exp_neg_lintegral :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure ℝ),
      IsPoissonRandomMeasure N volume P ∧
      ∫⁻ ω, EReal.exp (-(∫⁻ x, (Set.Icc (0 : ℝ) 1).indicator 1 x ∂(N ω) : EReal)) ∂P =
        EReal.exp (-(∫⁻ x, (1 - EReal.exp (-(((Set.Icc (0 : ℝ) 1).indicator 1 x : ℝ≥0∞) :
          EReal))) ∂volume : EReal)) := by
  obtain ⟨Ω, mΩ, P, N, -, hN⟩ := exists_isPoissonRandomMeasure (volume : Measure ℝ)
  exact ⟨Ω, mΩ, P, N, hN,
    hN.lintegral_exp_neg_lintegral (measurable_one.indicator measurableSet_Icc)⟩

/-! ### Binomial point processes converge to a Poisson random measure -/

/-- Weight `w n = min 1 (1/n)`: equal to `1/n` for `n ≥ 1`. -/
def wt (n : ℕ) : ℝ := min 1 (1 / (n : ℝ))

theorem wt_nonneg (n : ℕ) : 0 ≤ wt n := le_min zero_le_one (by positivity)

theorem wt_le_one (n : ℕ) : wt n ≤ 1 := min_le_left _ _

/-- The sampling law `μ n = (1/n) Leb|[0,1] + (1 - 1/n) δ_n`: with `n` samples, about one lands
in `[0, 1]` (uniformly) and the rest escape to infinity. -/
def binLaw (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (wt n) • volume.restrict (Set.Icc (0 : ℝ) 1) +
    ENNReal.ofReal (1 - wt n) • Measure.dirac (n : ℝ)

instance (n : ℕ) : IsProbabilityMeasure (binLaw n) := by
  constructor
  simp only [binLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (wt_nonneg n) (by linarith [wt_le_one n])]
  simp

/-- `n • μ n → Leb|[0,1]` vaguely. -/
theorem tendstoVaguely_binLaw :
    Measure.TendstoVaguely (fun n : ℕ ↦ (n : ℝ≥0∞) • binLaw n) atTop
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  intro f hf hfc
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hint : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hf.integrable_of_hasCompactSupport hfc
  have hintd : ∀ x : ℝ, Integrable f (Measure.dirac x) := fun x => integrable_dirac enorm_lt_top
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop ⌈R⌉₊, eventually_ge_atTop 1] with n hn hn1
  have hfn : f n = 0 := by
    by_contra h
    have := hR (subset_tsupport f (Function.mem_support.2 h))
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_natCast] at this
    have : (n : ℝ) ≤ ⌈R⌉₊ := this.trans (Nat.le_ceil R)
    exact absurd (by exact_mod_cast this : n ≤ ⌈R⌉₊) (not_le.2 hn)
  have hw : wt n = 1 / n := by
    unfold wt
    exact min_eq_right (by rw [div_le_one (by exact_mod_cast hn1)]; exact_mod_cast hn1)
  rw [binLaw, integral_smul_measure, integral_add_measure (hint.smul_measure (by simp))
    ((hintd _).smul_measure (by simp)), integral_smul_measure, integral_smul_measure,
    integral_dirac, hfn, hw]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [smul_eq_mul, mul_zero, add_zero, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-- `ProbabilityTheory.tendstoInLawVaguely_sumDiracRange` (binomial point processes converge to a
Poisson random measure), for the sampling laws `binLaw n` with `n • binLaw n → Leb|[0,1]`
vaguely, and a Poisson random measure with intensity `Leb|[0,1]` from
`exists_isPoissonRandomMeasure`. -/
theorem test_nonvacuous_tendstoInLawVaguely_sumDiracRange :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (N' : Ω' → Measure ℝ),
      IsPoissonRandomMeasure N' (volume.restrict (Set.Icc (0 : ℝ) 1)) P' ∧
      TendstoInLawVaguely (fun n z ↦ sumDiracRange n z)
        (fun n ↦ Measure.infinitePi fun _ : ℕ ↦ binLaw n) atTop N' P'
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨Ω', mΩ', P', N', -, hN'⟩ :=
    exists_isPoissonRandomMeasure (volume.restrict (Set.Icc (0 : ℝ) 1))
  exact ⟨Ω', mΩ', P', N', hN', tendstoInLawVaguely_sumDiracRange tendstoVaguely_binLaw hN'⟩

/-! ### Exceedances of iid exponential samples converge to a Poisson process -/

open CumulativeDistributionFunction in
theorem gumbel_zero_pos : 0 < standardGumbelCDF 0 := by
  rw [standardGumbelCDF_apply_eq]; exact Real.exp_pos _

open CumulativeDistributionFunction in
theorem gumbel_mem_Ioo (x : ℝ) : standardGumbelCDF x ∈ Set.Ioo 0 1 := by
  rw [standardGumbelCDF_apply_eq]
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith [Real.exp_pos (-x)])⟩

open CumulativeDistributionFunction in
/-- `ExtremeValueTheory.tendsto_measureReal_sumDiracRange_affine_eq` (space component of the
exceedance point process): iid standard exponential samples on `ℕ → ℝ`, with the Gumbel
normalizations from `isInMDAGumbel_standardExponentialCDF`, threshold `u = 0`, and the two
disjoint exceedance intervals `(0, 1]` and `(1, ∞)`. -/
theorem test_nonvacuous_tendsto_measureReal_sumDiracRange_affine_eq :
    ∃ As : ℕ → AffineIncrEquiv, ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (N' : Ω' → Measure ℝ),
      IsPoissonRandomMeasure N' (exceedanceMeasure standardGumbelCDF gumbel_zero_pos) P' ∧
      ∀ m : Fin 2 → ℕ, Tendsto (fun n ↦ (iidLaw standardExponentialCDF.measure).real
        {ω | ∀ j, sumDiracRange n (fun i ↦ As n (ω i)) (![Set.Ioc 0 1, Set.Ioi 1] j) = m j})
        atTop (𝓝 (P'.real {ω | ∀ j, N' ω (![Set.Ioc 0 1, Set.Ioi 1] j) = m j})) := by
  obtain ⟨As, hlim⟩ := isInMDAGumbel_standardExponentialCDF
  obtain ⟨Ω', mΩ', P', N', -, hN'⟩ :=
    exists_isPoissonRandomMeasure (exceedanceMeasure standardGumbelCDF gumbel_zero_pos)
  refine ⟨As, Ω', mΩ', P', N', hN', fun m => ?_⟩
  refine tendsto_measureReal_sumDiracRange_affine_eq (X := fun i (ω : ℕ → ℝ) => ω i)
    (fun i => measurable_pi_apply i) (iidLaw_iIndepFun _) (iidLaw_cdf _) hlim gumbel_zero_pos hN'
    (fun j => ?_) ?_ m
  · fin_cases j
    · exact Or.inl ⟨0, 1, le_rfl, zero_le_one, gumbel_mem_Ioo 0, gumbel_mem_Ioo 1, rfl⟩
    · exact Or.inr ⟨1, zero_le_one, gumbel_mem_Ioo 1, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Function.onFun]
      exact Set.disjoint_left.2 fun x hx hx' => not_lt.2 hx.2 hx'
    · simp only [Function.onFun]
      exact Set.disjoint_left.2 fun x hx hx' => not_lt.2 hx'.2 hx
    · exact absurd rfl hij

open CumulativeDistributionFunction in
/-- `ExtremeValueTheory.tendsto_measureReal_sumDiracRange_timeSpace_eq` (time-space exceedance
point process → Poisson random measure with intensity `Leb|(0,1] ⊗ μ_G`): iid standard exponential
samples, Gumbel normalizations, threshold `0`, and the two disjoint time-space boxes
`(0, 1/2] × (0, ∞)` and `(1/2, 1] × (0, ∞)`. -/
theorem test_nonvacuous_tendsto_measureReal_sumDiracRange_timeSpace_eq :
    ∃ As : ℕ → AffineIncrEquiv, ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (N' : Ω' → Measure (ℝ × ℝ)),
      IsPoissonRandomMeasure N' ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (exceedanceMeasure standardGumbelCDF gumbel_zero_pos)) P' ∧
      ∀ m : Fin 2 → ℕ, Tendsto (fun n ↦ (iidLaw standardExponentialCDF.measure).real
        {ω | ∀ j, sumDiracRange n (fun i ↦ (((i : ℝ) + 1) / n, As n (ω i)))
          (Set.Ioc (![0, 1/2] j) (![1/2, 1] j) ×ˢ Set.Ioi 0) = m j}) atTop
        (𝓝 (P'.real {ω | ∀ j, N' ω (Set.Ioc (![0, 1/2] j) (![1/2, 1] j) ×ˢ Set.Ioi 0) = m j})) := by
  obtain ⟨As, hlim⟩ := isInMDAGumbel_standardExponentialCDF
  obtain ⟨Ω', mΩ', P', N', -, hN'⟩ := exists_isPoissonRandomMeasure
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (exceedanceMeasure standardGumbelCDF gumbel_zero_pos))
  refine ⟨As, Ω', mΩ', P', N', hN', fun m => ?_⟩
  refine tendsto_measureReal_sumDiracRange_timeSpace_eq (X := fun i (ω : ℕ → ℝ) => ω i)
    (fun i => measurable_pi_apply i) (iidLaw_iIndepFun _) (iidLaw_cdf _) hlim gumbel_zero_pos hN'
    (fun j => ?_) (fun j => ?_) (fun j => ?_) (fun _ => Or.inr ⟨0, le_rfl, gumbel_mem_Ioo 0, rfl⟩)
    ?_ m
  · fin_cases j <;> norm_num
  · fin_cases j <;> norm_num
  · fin_cases j <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Function.onFun]
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      simp only [Set.mem_prod, Set.mem_Ioc] at hx hx'
      norm_num at hx hx'
      linarith [hx.1.2, hx'.1.1]
    · simp only [Function.onFun]
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      simp only [Set.mem_prod, Set.mem_Ioc] at hx hx'
      norm_num at hx hx'
      linarith [hx'.1.2, hx.1.1]
    · exact absurd rfl hij

/-! ### The Skorokhod space -/

/-- `SkorokhodSpace.instPolishSpace`: `D([0,1], ℝ)` is Polish, hence (e.g.) its Borel σ-algebra
is standard Borel and it is second countable. -/
example : PolishSpace (SkorokhodSpace ℝ) := inferInstance

example : SecondCountableTopology (SkorokhodSpace ℝ) := inferInstance

/-- `SkorokhodSpace.instPolishSpace` also covers `D([0,1], ℝ²)` (any complete separable metric
target). -/
example : PolishSpace (SkorokhodSpace (EuclideanSpace ℝ (Fin 2))) := inferInstance

/-! ### The tail empirical process converges to Brownian motion -/

local instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- The intermediate sequence `k n = ⌊√n⌋`: `k n → ∞`, `k n / n → 0`. -/
theorem tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b * b, fun n hn => ?_⟩
  exact Nat.le_sqrt.2 hn

theorem tendsto_sqrt_div : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ 2 / ((Nat.sqrt n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp tendsto_sqrt_atTop))
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by exact_mod_cast Nat.sqrt_le n
  have h3 : (Nat.sqrt n : ℝ) ≤ n := by exact_mod_cast Nat.sqrt_le_self n
  rw [div_le_div_iff₀ hn' (by positivity)]
  linarith

/-- `ExtremeValueTheory.tendstoInDistribution_tailEmpiricalPath` (dHF Thm 5.1.4): for iid uniform
`[0, 1]` samples on `ℕ → ℝ` and `k n = ⌊√n⌋`, the tail empirical process converges in `D[0,1]` to
a Brownian motion. The Brownian motion `B` (a measurable `D[0,1]`-valued map with Brownian
finite-dimensional laws) is the identity on `D[0,1]` under the limit law supplied by
`exists_tendsto_tailEmpiricalPath`. -/
theorem test_nonvacuous_tendstoInDistribution_tailEmpiricalPath :
    ∃ P' : ProbabilityMeasure (SkorokhodSpace ℝ),
      (∀ J : Finset unitInterval,
        ((P' : Measure (SkorokhodSpace ℝ)).map id).map (fun x : SkorokhodSpace ℝ ↦ fun t : J ↦ x t) =
          brownianFdd (fun t : J ↦ unitInterval.toNNReal' t)) ∧
      TendstoInDistribution
        (fun n ↦ tailEmpiricalPath (fun i (ω : ℕ → ℝ) => ω i) n (Nat.sqrt n)) atTop id
        (fun _ ↦ iidLaw (volume.restrict (Set.Icc (0 : ℝ) 1))) (P' : Measure (SkorokhodSpace ℝ)) := by
  have hU : ∀ i, Measurable fun ω : ℕ → ℝ => ω i := fun i => measurable_pi_apply i
  obtain ⟨μ, -, hμ⟩ := exists_tendsto_tailEmpiricalPath (P := iidLaw (volume.restrict
    (Set.Icc (0 : ℝ) 1))) hU (iidLaw_iIndepFun _) (iidLaw_map _) tendsto_sqrt_atTop
    tendsto_sqrt_div
  have hfdd : ∀ J : Finset unitInterval,
      ((μ : Measure (SkorokhodSpace ℝ)).map id).map
        (fun x : SkorokhodSpace ℝ ↦ fun t : J ↦ x t) =
        brownianFdd (fun t : J ↦ unitInterval.toNNReal' t) := fun J => by
    rw [Measure.map_id]
    exact hμ (fun t : J => (t : unitInterval))
  exact ⟨μ, hfdd, tendstoInDistribution_tailEmpiricalPath hU (iidLaw_iIndepFun _)
    (iidLaw_map _) tendsto_sqrt_atTop tendsto_sqrt_div measurable_id hfdd⟩

end Test.NonVacuity.Processes
