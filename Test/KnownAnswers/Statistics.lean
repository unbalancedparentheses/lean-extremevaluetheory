import ExtremeValueTheory

/-! # Known answers: statistics

Each test evaluates an estimator, density, likelihood or information matrix of
`ExtremeValueTheory/Statistics` at a point where the textbook value is known, so that a slip in
the sign, the parametrization or the indexing convention of the definition breaks the build.

References: [EKM] Embrechts, Klüppelberg, Mikosch, *Modelling Extremal Events* (1997);
[dHF] de Haan, Ferreira, *Extreme Value Theory* (2006); [Col] Coles, *An Introduction to
Statistical Modeling of Extreme Values* (2001); [BGST] Beirlant, Goegebeur, Segers, Teugels,
*Statistics of Extremes* (2004); [FS03] Ferro, Segers, *Inference for clusters of extreme values*,
JRSS B 65 (2003); [Smi85] Smith, *Maximum likelihood estimation in a class of nonregular cases*,
Biometrika 72 (1985).
-/

open ExtremeValueTheory Real MeasureTheory ProbabilityTheory Finset Filter

namespace Test.KnownAnswers.Statistics

/-! ### Order statistics -/

/-- For an ascending sample the descending order statistics are the sample read backwards. -/
theorem orderStat_of_monotone {n : ℕ} {x : Fin n → ℝ} (hx : Monotone x) {j : ℕ} (hj : j < n) :
    orderStat x j = x (Fin.rev ⟨j, hj⟩) := by
  rw [orderStat_of_lt x hj, Tuple.sort_eq_refl_iff_monotone.2 hx]
  rfl

/-- For a sample `x` and a permutation `σ` sorting it in ascending order,
`orderStat x j = x (σ (rev j))`. -/
theorem orderStat_of_sorting {n : ℕ} {x : Fin n → ℝ} (σ : Equiv.Perm (Fin n))
    (hσ : Monotone (x ∘ σ)) {j : ℕ} (hj : j < n) :
    orderStat x j = x (σ (Fin.rev ⟨j, hj⟩)) := by
  rw [orderStat_of_lt x hj]
  exact (congrFun (Tuple.comp_sort_eq_comp_iff_monotone.2 hσ) _).symm

/-- The sample `(1, e, e²)`, used for the Hill, Weissman and moment estimators. -/
noncomputable def expSample : Fin 3 → ℝ := ![1, exp 1, exp 2]

theorem expSample_monotone : Monotone expSample := by
  refine Fin.monotone_iff_le_succ.2 fun i => ?_
  fin_cases i
  · simp [expSample]
  · simp [expSample]

@[simp] theorem orderStat_expSample_0 : orderStat expSample 0 = exp 2 := by
  rw [orderStat_of_monotone expSample_monotone (by norm_num)]; rfl

@[simp] theorem orderStat_expSample_1 : orderStat expSample 1 = exp 1 := by
  rw [orderStat_of_monotone expSample_monotone (by norm_num)]; rfl

@[simp] theorem orderStat_expSample_2 : orderStat expSample 2 = 1 := by
  rw [orderStat_of_monotone expSample_monotone (by norm_num)]; rfl

/-- Convention ([EKM, §4.1] writes `X_{n,n} ≤ ⋯ ≤ X_{1,n}`): `orderStat x 0` is the sample
**maximum** and `orderStat x (n - 1)` the sample **minimum**, on an unsorted sample. -/
theorem test_orderStat_max_min :
    orderStat ![(3 : ℝ), 1, 2] 0 = 3 ∧ orderStat ![(3 : ℝ), 1, 2] 2 = 1 := by
  -- the permutation `0 ↦ 1, 1 ↦ 2, 2 ↦ 0` sorts `(3, 1, 2)` into `(1, 2, 3)`
  let σ : Equiv.Perm (Fin 3) := finRotate 3
  have hσ : Monotone (![(3 : ℝ), 1, 2] ∘ σ) := by
    refine Fin.monotone_iff_le_succ.2 fun i => ?_
    have h0 : σ 0 = 1 := by decide
    have h1 : σ 1 = 2 := by decide
    have h2 : σ 2 = 0 := by decide
    fin_cases i <;> norm_num [h0, h1, h2]
  constructor
  · rw [orderStat_of_sorting σ hσ (by norm_num)]; rfl
  · rw [orderStat_of_sorting σ hσ (by norm_num)]; rfl

/-- Out-of-range order statistics take the junk value `0`. -/
example : orderStat ![(3 : ℝ), 1, 2] 3 = 0 := orderStat_of_le _ le_rfl

/-! ### The Hill estimator -/

/-- `H_{2,3}` on `(1, e, e²)`: `(1/2) ((2 - 0) + (1 - 0)) = 3/2` ([EKM, (6.36)], [dHF, (3.2.4)]):
the average of the log-excesses of the top `k` over the `(k+1)`-th largest observation. -/
theorem test_hill_two : hill expSample 2 = 3 / 2 := by
  simp [hill, Finset.sum_range_succ]
  norm_num

/-- `H_{1,3}` on `(1, e, e²)`: `log e² - log e = 1`. -/
theorem test_hill_one : hill expSample 1 = 1 := by
  simp [hill]
  norm_num

/-- **The Hill estimator targets `γ = 1/α`, not `α`** ([EKM, Theorem 6.4.6], [dHF, Theorem
3.2.2]): for an exact `Pareto(2)` sample the limit is `1/2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-(2 : ℝ))) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (nhds 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => (1 / 2 : ℝ)) :=
  tendstoInMeasure_hill_pareto hX hindep hident two_pos hPar hk hkn

/-! ### The moment estimator -/

/-- The moment estimator of Dekkers–Einmahl–de Haan on `(1, e, e²)` with `k = 2` ([dHF, (3.5.2)]):
`M¹ = 3/2`, `M² = (2² + 1²)/2 = 5/2`, `γ̂ = M¹ + 1 - (1/2)(1 - (M¹)²/M²)⁻¹ = 5/2 - 5 = -5/2`. -/
theorem test_momentEstimator : momentEstimator expSample 2 = -5 / 2 := by
  simp [momentEstimator, logMoment, Finset.sum_range_succ]
  norm_num

/-- The moment estimator, like the Hill estimator, targets `γ = 1/α` on a Pareto sample. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-(4 : ℝ))) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (nhds 0)) :
    TendstoInMeasure P (fun n ω => momentEstimator (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => (1 / 4 : ℝ)) :=
  tendstoInMeasure_momentEstimator_pareto hX hindep hident (by norm_num) hPar hk hkn

/-! ### Weissman quantile and tail probability estimators -/

/-- Weissman's estimator ([EKM, (6.41)], [dHF, (4.3.4)]) `x̂_p = X_{(k+1)} (k/(np))^{γ̂}` on
`(1, e, e²)` with `k = 1` (`X_{(2)} = e`, `γ̂ = 1`) and `p = 1/30`: `e · (1/(3/30)) = 10 e`. -/
theorem test_weissman : weissman expSample 1 (1 / 30) = 10 * exp 1 := by
  simp [weissman, test_hill_one]
  norm_num
  ring

/-- The tail probability estimator ([dHF, (4.4.2)]) `p̂(y) = (k/n) (y/X_{(k+1)})^{-1/γ̂}` inverts
Weissman's: at `y = 10 e` it returns `p = 1/30`. -/
theorem test_tailProbEstimator : tailProbEstimator expSample 1 (10 * exp 1) = 1 / 30 := by
  simp [tailProbEstimator, test_hill_one, (exp_pos 1).ne']
  norm_num

/-! ### The Pickands estimator -/

/-- Pickands' estimator ([EKM, (6.29)], [dHF, (3.3.4)])
`ξ̂ = (log 2)⁻¹ log ((X_{(k+1)} - X_{(2k+1)}) / (X_{(2k+1)} - X_{(4k+1)}))` on the exact
`GPD(1)` quantiles `U(t) = t - 1` at `t = 1, 2, 4` (`k = 1`, `n = 5`): `log 2 / log 2 = 1`. -/
theorem test_pickands_frechet : pickands ![(0 : ℝ), 1 / 2, 1, 3, 5] 1 = 1 := by
  have hm : Monotone ![(0 : ℝ), 1 / 2, 1, 3, 5] := by
    refine Fin.monotone_iff_le_succ.2 fun i => ?_
    fin_cases i <;> simp <;> norm_num
  simp only [pickands, orderStat_of_monotone hm (show 1 < 5 by norm_num),
    orderStat_of_monotone hm (show 2 * 1 < 5 by norm_num),
    orderStat_of_monotone hm (show 4 * 1 < 5 by norm_num)]
  have h2 : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  simp [Fin.rev]
  norm_num [h2]

/-- Pickands' estimator on the exact `GPD(-1)` quantiles `U(t) = 1 - 1/t` at `t = 1, 2, 4`:
`log (1/2) / log 2 = -1` (a short-tailed, Weibull-type sample). -/
theorem test_pickands_weibull : pickands ![(0 : ℝ), 1 / 4, 1 / 2, 3 / 4, 1] 1 = -1 := by
  have hm : Monotone ![(0 : ℝ), 1 / 4, 1 / 2, 3 / 4, 1] := by
    refine Fin.monotone_iff_le_succ.2 fun i => ?_
    fin_cases i <;> simp <;> norm_num
  simp only [pickands, orderStat_of_monotone hm (show 1 < 5 by norm_num),
    orderStat_of_monotone hm (show 2 * 1 < 5 by norm_num),
    orderStat_of_monotone hm (show 4 * 1 < 5 by norm_num)]
  have h2 : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  simp [Fin.rev]
  norm_num
  rw [one_div, log_inv, neg_div, div_self h2]

/-! ### The generalized Pareto law -/

/-- `GPD(0, 1)` is the standard exponential: density `e^{-x}` ([EKM, Definition 3.4.9]). -/
theorem test_gpdDensity_exp {x : ℝ} (hx : 0 ≤ x) : gpdDensity 0 1 x = exp (-x) := by
  simp [gpdDensity, hx]

/-- `GPD(1, 1)` is the Pareto law `P(X > x) = (1 + x)⁻¹`, density `(1 + x)⁻²`; at `x = 1`: `1/4`. -/
theorem test_gpdDensity_pareto : gpdDensity 1 1 1 = 1 / 4 := by
  simp [gpdDensity]
  norm_num

/-- `GPD(-1, 1)` is the uniform law on `[0, 1]`: density `1` inside, `0` beyond the endpoint
`-σ/ξ = 1` ([EKM, §3.4], [Col, §4.2.2]). -/
theorem test_gpdDensity_uniform : gpdDensity (-1) 1 (1 / 2) = 1 ∧ gpdDensity (-1) 1 2 = 0 := by
  constructor <;> norm_num [gpdDensity]

/-- The GPD density vanishes on the negative half-line. -/
theorem test_gpdDensity_neg : gpdDensity 1 1 (-1) = 0 := by
  simp [gpdDensity]

/-- `GPD(1, 1)`: `G(1) = 1 - (1 + 1)⁻¹ = 1/2`. -/
theorem test_gpdCDF_pareto : gpdCDF 1 1 1 = 1 / 2 := by
  simp [gpdCDF, gpdSurvival]
  norm_num

/-- The median of `GPD(0, 1) = Exp(1)` is `log 2`. -/
theorem test_gpdCDF_exp_median : gpdCDF 0 1 (log 2) = 1 / 2 := by
  have : 0 ≤ log 2 := (log_pos one_lt_two).le
  simp [gpdCDF, gpdSurvival, max_eq_left this, exp_neg, exp_log two_pos]
  norm_num

/-- `GPD(-1, 1)` is uniform: `G(x) = x` on `[0, 1]`. -/
theorem test_gpdCDF_uniform {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : gpdCDF (-1) 1 x = x := by
  simp [gpdCDF, gpdSurvival, max_eq_left hx0, max_eq_left (show 0 ≤ 1 + -x by linarith)]

/-- The law `gpdMeasure` has the GPD tail: `GPD(1/2, 1)` at `x = 2` gives `(1 + 1)^{-2} = 1/4`. -/
theorem test_gpdMeasure_Ioi : gpdMeasure (1 / 2) 1 (Set.Ioi 2) = ENNReal.ofReal (1 / 4) := by
  rw [gpdMeasure_Ioi one_pos (by norm_num)]
  congr 1
  simp [gpdSurvival]
  norm_num

/-- The log-likelihood of `GPD(0, 1)` at the sample `(1, 2)`: `-1 - 2 = -3`. -/
theorem test_gpdLogLik : gpdLogLik 0 1 ![(1 : ℝ), 2] = -3 := by
  simp [gpdLogLik, gpdDensity, Fin.sum_univ_two]
  norm_num

/-! ### The generalized extreme value law -/

/-- All standard GEV densities take the value `e⁻¹` at `0` (there `1 + ξ x = 1`): Gumbel. -/
theorem test_gevDensity_gumbel_zero : gevDensity 0 0 = exp (-1) := by
  simp [gevDensity]

/-- Fréchet-type `ξ = 1` at `0`: `e⁻¹`. -/
theorem test_gevDensity_frechet_zero : gevDensity 1 0 = exp (-1) := by
  simp [gevDensity]

/-- `ξ = 1` at `x = 1`: `h(x) = (1 + x)^{-2} exp(-(1 + x)⁻¹) = e^{-1/2} / 4` ([Col, (3.2)]). -/
theorem test_gevDensity_frechet_one : gevDensity 1 1 = exp (-(1 / 2)) / 4 := by
  simp [gevDensity]
  norm_num
  ring

/-- Support conventions: for `ξ = 1` the support is `x > -1`; for `ξ = -1` it is `x < 1`. -/
theorem test_gevDensity_support : gevDensity 1 (-2) = 0 ∧ gevDensity (-1) 2 = 0 := by
  constructor <;> norm_num [gevDensity]

/-- The Gumbel location-scale log-likelihood at the single point `x = μ` is `-log σ - 1`. -/
theorem test_gevLogLik_gumbel {μ σ : ℝ} (hσ : 0 < σ) : gevLogLik 0 μ σ ![μ] = -log σ - 1 := by
  simp [gevLogLik, gevLocScaleDensity, gevDensity]
  rw [log_mul (inv_ne_zero hσ.ne') (exp_pos _).ne', log_inv, log_exp]
  ring

/-- The `m`-block return level of the Gumbel law ([Col, (3.4)]): `z_m = -log(-log(1 - 1/m))`;
at `m = 2` this is the Gumbel median `-log log 2`. -/
theorem test_returnLevel_gumbel_median : returnLevel 0 2 = -log (log 2) := by
  norm_num [returnLevel]
  rw [one_div, log_inv, log_neg_eq_log]

/-- Return level for `ξ = 1` at `m = 2`: `((log 2)⁻¹ - 1)/1`. -/
theorem test_returnLevel_frechet : returnLevel 1 2 = (log 2)⁻¹ - 1 := by
  norm_num [returnLevel, rpow_neg_one]
  rw [one_div, log_inv, inv_neg, neg_neg]

/-! ### Fisher information of the GPD -/

/-- At `ξ = 0`, `σ = 1`: `I = [[2, 1], [1, 1]]` ([Smi85], [dHF, (3.4.11)]). -/
theorem test_gpdFisherInfo_exp : gpdFisherInfo 0 1 = !![2, 1; 1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gpdFisherInfo]

/-- The asymptotic covariance of the GPD MLE at `ξ = 0`, `σ = 1` ([Smi85]; [Col, §4.3.4]):
`Var ξ̂ = (1 + ξ)² = 1`, `Cov(ξ̂, σ̂) = -σ(1 + ξ) = -1`, `Var σ̂ = 2σ²(1 + ξ) = 2`. -/
theorem test_gpdFisherInfoInv_exp : gpdFisherInfoInv 0 1 = !![1, -1; -1, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gpdFisherInfoInv]

/-- The two separately written matrices are inverse to each other for every `ξ > -1/2`. -/
theorem test_gpdFisherInfo_mul_inv {ξ σ : ℝ} (hξ : -1 / 2 < ξ) (hσ : 0 < σ) :
    gpdFisherInfo ξ σ * gpdFisherInfoInv ξ σ = 1 := by
  have h1 : 1 + ξ ≠ 0 := by linarith
  have h2 : 1 + 2 * ξ ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gpdFisherInfo, gpdFisherInfoInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The GEV Fisher information in `(μ, σ)` at `ξ = 1`, `σ = 1` (Prescott and Walden 1980, with
their `k = -ξ`): `p = (1 + ξ)² Γ(1 + 2ξ) = 8`, `Γ(2 + ξ) = 2`, so
`I = [[8, (2 - 8)/1], [(2 - 8)/1, (1 - 4 + 8)/1]] = [[8, -6], [-6, 5]]`. The negative off-diagonal
entry matches the Gumbel limit `I_{μσ} = -(1 - γ)/σ²` as `ξ → 0`. -/
theorem test_gevFisherInfoMuSigma : gevFisherInfoMuSigma 1 1 = !![8, -6; -6, 5] := by
  have h3 : Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [gevFisherInfoMuSigma, h3]

/-! ### Extremal index estimators -/

/-- The Ferro–Segers law with `θ = 1` (no clustering) is the standard exponential law
([FS03, Theorem 1]). -/
theorem test_ferroSegersLaw_one : ferroSegersLaw 1 = expMeasure 1 := by
  simp [ferroSegersLaw]

/-- The normalized inter-exceedance times have mean `1` and `2 (E T)² / E T² = θ`
([FS03, (5)]); at `θ = 1/3`. -/
theorem test_ferroSegers_moments :
    ∫ x, x ∂(ferroSegersLaw (1 / 3)) = 1 ∧ ∫ x, x ^ 2 ∂(ferroSegersLaw (1 / 3)) = 6 ∧
      2 * (∫ x, x ∂(ferroSegersLaw (1 / 3))) ^ 2 / ∫ x, x ^ 2 ∂(ferroSegersLaw (1 / 3)) = 1 / 3 := by
  refine ⟨integral_id_ferroSegersLaw (by norm_num), ?_, ferroSegers_moment_ratio (by norm_num)⟩
  rw [integral_sq_ferroSegersLaw (by norm_num)]
  norm_num

/-- `θ̂₁ = 2 (∑ T)² / (m ∑ T²)` on the times `(1, 2)`: `2 · 9 / (2 · 5) = 9/5` ([FS03, (4)]). -/
theorem test_intervalsEstimator₁ : intervalsEstimator₁ ![(1 : ℝ), 2] = 9 / 5 := by
  simp [intervalsEstimator₁, Fin.sum_univ_two]
  norm_num

/-- The intervals estimator is truncated at `1`: times `(1, 2)` (all `≤ 2`) give `min(1, 9/5)`. -/
theorem test_intervalsEstimator_trunc : intervalsEstimator ![(1 : ℝ), 2] = 1 := by
  have : ∀ i, ![(1 : ℝ), 2] i ≤ 2 := by intro i; fin_cases i <;> norm_num
  simp only [intervalsEstimator, this, implies_true, ↓reduceIte, test_intervalsEstimator₁]
  norm_num

/-- The bias-corrected `θ̂₂ = 2 (∑ (T - 1))² / (m ∑ (T - 1)(T - 2))` on the times `(1, 1, 1, 7)`
(three short gaps within a cluster, one long gap): `2 · 36 / (4 · 30) = 3/5` ([FS03, (4)]). -/
theorem test_intervalsEstimator₂ : intervalsEstimator ![(1 : ℝ), 1, 1, 7] = 3 / 5 := by
  have : ¬ ∀ i, ![(1 : ℝ), 1, 1, 7] i ≤ 2 := fun h => by have := h 3; norm_num at this
  simp only [intervalsEstimator, this, ↓reduceIte]
  simp [intervalsEstimator₂, Fin.sum_univ_four]
  norm_num

/-- A deterministic sample with exceedances of `u = 1` at times `0, 1, 4` among `0, …, 7`: two
clusters, `{0, 1}` and `{4}`. -/
noncomputable def clusterSample (t : ℕ) (_ : Unit) : ℝ := if t = 0 ∨ t = 1 ∨ t = 4 then 5 else 0

theorem clusterSample_le_iff (t : ℕ) : clusterSample t () ≤ 1 ↔ t ∉ ({0, 1, 4} : Finset ℕ) := by
  unfold clusterSample; split_ifs with h <;> simp_all

theorem one_lt_clusterSample_iff (t : ℕ) :
    1 < clusterSample t () ↔ t ∈ ({0, 1, 4} : Finset ℕ) := by
  rw [← not_le, clusterSample_le_iff, not_not]

/-- The blocks estimator ([EKM, (8.6)], [BGST, §10.3.4]) with `n = 8`, block length `r = 4`:
two blocks with an exceedance, three exceedances, `θ̂ = 2/3`. -/
theorem test_blocksEstimator : blocksEstimator clusterSample 8 4 1 () = 2 / 3 := by
  simp only [blocksEstimator, blockCount, blockEvent, maxLE, tailCount, Set.mem_compl_iff,
    Set.mem_ofPred_eq, clusterSample_le_iff, one_lt_clusterSample_iff, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp (config := {decide := true})
  norm_num

/-- The runs estimator ([EKM, (8.8)], [BGST, §10.3.4]) with `n = 8`, run length `r = 2`: the
exceedances at times `1` and `4` end a cluster, `θ̂ = 2/3`. -/
theorem test_runsEstimator : runsEstimator clusterSample 8 2 1 () = 2 / 3 := by
  simp only [runsEstimator, runsCount, runEvent, maxLE, tailCount, Set.mem_inter_iff,
    Set.mem_ofPred_eq, clusterSample_le_iff, one_lt_clusterSample_iff, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp (config := {decide := true})
  norm_num

/-! ### Block maxima and records -/

/-- `M_{2,1} = max(X_2, X_3)`: the `j`-th block of size `n` is `{jn, …, jn + n - 1}`. -/
theorem test_blockMax : blockMax (fun t (_ : Unit) => ((t : ℝ) - 2) ^ 2) 2 1 () = 1 := by
  simp [blockMax, Finset.range_add_one]

/-- Records of `(3, 1, 4, 1, 5)` are at times `0, 2, 4`: the first observation is a record
([EKM, §5.4]). -/
theorem test_recordCount :
    recordCount (fun k => ([3, 1, 4, 1, 5] : List ℝ).getD k 0) 5 = 3 := by
  classical
  have : (range 5).filter (IsRecord (fun k => ([3, 1, 4, 1, 5] : List ℝ).getD k 0)) =
      {0, 2, 4} := by
    ext k
    simp only [mem_filter, mem_range, IsRecord, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hk, h⟩
      interval_cases k <;> simp_all
      have := h 0 (by norm_num); norm_num at this
    · rintro (rfl | rfl | rfl) <;> refine ⟨by norm_num, fun i hi => ?_⟩ <;> interval_cases i <;>
        norm_num
  rw [recordCount, this]; rfl

end Test.KnownAnswers.Statistics
