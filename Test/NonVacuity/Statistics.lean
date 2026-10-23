import ExtremeValueTheory

/-!
# Non-vacuity tests: tail estimators

For each headline consistency / normality theorem for the Hill, Pickands, moment and Weissman
estimators, we build a concrete iid sample (with `ProbabilityTheory.exists_iid`) satisfying all of
its hypotheses and apply the theorem, obtaining its conclusion for that sample.

Objects used:
* iid `Pareto(1, 2)` (`P(X > x) = x⁻²`, `x ≥ 1`) with `k n = ⌊√n⌋` (`Nat.sqrt`);
* iid shifted Pareto `X = Y + 1`, `Y ~ Pareto(1, 1)`: tail quantile `U(t) = t + 1`, second-order
  regularly varying with `γ = 1`, `ρ = -1`, `A(t) = -1/(t + 1)` (Hall class), `k n = ⌊√n⌋`,
  so `√k A(n/k) → 0`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Test.NonVacuity.Statistics

open ExtremeValueTheory

/-! ### The sample fraction `k n = ⌊√n⌋`

`k n → ∞` and `k n / n → 0` are the library's `ExtremeValueTheory.tendsto_sqrt_atTop` and
`ExtremeValueTheory.tendsto_sqrt_div`. -/

/-- Test-specific: `k n² ≤ n` for `k n = ⌊√n⌋`. -/
private theorem sqrt_mul_self_le (n : ℕ) : ((Nat.sqrt n : ℝ)) * Nat.sqrt n ≤ n := by
  exact_mod_cast Nat.sqrt_le n

/-- Test-specific: `k n ≥ 1` for `n ≥ 1`. -/
private theorem one_le_sqrt {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ Nat.sqrt n := by
  exact_mod_cast Nat.le_sqrt.2 (by simpa using hn)

/-- Test-specific: `k n → ∞` in `ℝ`. -/
private theorem tendsto_sqrt_cast : Tendsto (fun n => (Nat.sqrt n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp ExtremeValueTheory.tendsto_sqrt_atTop

/-! ### iid samples -/

/-- Test-specific: Mathlib's `exists_iid`, packaged with the facts used by the estimator
theorems (identical distribution from `HasLaw.identDistrib`). -/
private theorem exists_iid_seq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
      (∀ i, IdentDistrib (X i) (X 0) P P) ∧ (∀ i, HasLaw (X i) μ P) := by
  obtain ⟨Ω, _, P, X, hXm, hlaw, hind, hP⟩ := exists_iid ℕ μ
  exact ⟨Ω, _, P, X, hP, hXm, hind, fun i => (hlaw i).identDistrib (hlaw 0), hlaw⟩

/-! ### Pareto(1, 2) -/

/-- Test-specific: the Pareto law used below, `P(X > x) = x⁻²` for `x ≥ 1`. -/
private noncomputable abbrev par : Measure ℝ := paretoMeasure 1 2

instance : IsProbabilityMeasure par := isProbabilityMeasure_paretoMeasure one_pos two_pos

/-- Test-specific: the tail of `par`. -/
private theorem par_Ioi {x : ℝ} (hx : 1 ≤ x) : (par (Ioi x)).toReal = x ^ (-2 : ℝ) := by
  rw [SymmPareto.pareto_Ioi two_pos hx, ENNReal.toReal_ofReal (by positivity)]

/-- Test-specific: the tail of `par` is regularly varying with index `-2`. -/
private theorem isRegularlyVarying_par :
    IsRegularlyVarying (fun x => (par (Ioi x)).toReal) (-2) :=
  (IsRegularlyVarying.rpow_id (-2)).congr (by
    filter_upwards [eventually_ge_atTop 1] with x hx using (par_Ioi hx).symm)

/-! ### Hill estimator: consistency -/

/-- **Non-vacuity of `ExtremeValueTheory.tendstoInMeasure_hill`** (Hill consistency): for an iid
`Pareto(1, 2)` sample and `k n = ⌊√n⌋`, every hypothesis is discharged and the Hill estimator
converges in probability to `1/2`. -/
theorem test_nonvacuous_tendstoInMeasure_hill :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ (∀ i, HasLaw (X i) par P) ∧
      TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (Nat.sqrt n)) atTop
        (fun _ => 1 / 2) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hind, hid, hlaw⟩ := exists_iid_seq par
  refine ⟨Ω, _, P, X, hP, hind, hlaw, ?_⟩
  have hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-2) := by
    simpa only [fun x => (hlaw 0).measure_eq (p := (x < ·)) measurableSet_Ioi] using
      isRegularlyVarying_par
  exact tendstoInMeasure_hill hXm hind hid two_pos hRV ExtremeValueTheory.tendsto_sqrt_atTop
      ExtremeValueTheory.tendsto_sqrt_div

/-! ### Hill estimator: dependent data (α-mixing) -/

/-- **Non-vacuity of `ExtremeValueTheory.tendstoInMeasure_hill_of_alphaMixing_rate`** (Hill
consistency for stationary α-mixing data): an iid `Pareto(1, 2)` sequence is stationary with
`α(h) = 0` for `h ≥ 1`; with `k n = ⌊√n⌋` and cluster window `r n = 0` the cluster condition is
empty and the mixing condition holds trivially. The Hill estimator converges to `1/2`.
(This only shows the hypotheses are jointly satisfiable; a genuinely dependent example would
need `P(X₀ > u, X_h > u)` estimates.) -/
theorem test_nonvacuous_tendstoInMeasure_hill_of_alphaMixing_rate :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ (∀ i, HasLaw (X i) par P) ∧
      TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (Nat.sqrt n)) atTop
        (fun _ => 1 / 2) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hind, hid, hlaw⟩ := exists_iid_seq par
  refine ⟨Ω, _, P, X, hP, hind, hlaw, ?_⟩
  have hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-2) := by
    simpa only [fun x => (hlaw 0).measure_eq (p := (x < ·)) measurableSet_Ioi] using
      isRegularlyVarying_par
  have hα1 : alphaMixing X P (0 + 1) = 0 :=
    hind.alphaMixing_eq_zero hXm (by norm_num)
  refine tendstoInMeasure_hill_of_alphaMixing_rate hXm (isStationary_of_iIndepFun hXm hind hid)
    two_pos hRV ExtremeValueTheory.tendsto_sqrt_atTop
      ExtremeValueTheory.tendsto_sqrt_div (fun _ => 0) ?_ ?_
  · intro u c _ _ _
    simp
  · simp [hα1]

/-! ### The Pareto c.d.f. and the domain of attraction `MDA(H_{1/2})` -/

/-- Test-specific: the c.d.f. `paretoCDF` is the c.d.f. of the measure `par`. -/
private theorem paretoCDF_eq (x : ℝ) :
    CumulativeDistributionFunction.paretoCDF two_pos x = (par (Iic x)).toReal := by
  rcases le_or_gt 1 x with hx | hx
  · rw [CumulativeDistributionFunction.paretoCDF_apply_of_one_le two_pos hx, ← compl_Ioi,
      prob_compl_eq_one_sub measurableSet_Ioi,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, par_Ioi hx]
  · have h0 : par (Iic x) = 0 :=
      measure_mono_null (Iic_subset_Iio.2 hx) SymmPareto.pareto_Iio_one
    change 1 - (max x 1) ^ (-2 : ℝ) = _
    rw [max_eq_right hx.le, one_rpow, h0]
    simp

/-! ### Pickands estimator -/

/-- **Non-vacuity of `ExtremeValueTheory.tendstoInMeasure_pickands`** (Pickands consistency for
every `ξ`): an iid `Pareto(1, 2)` sample (c.d.f. in `MDA(H_{1/2})`), `k n = ⌊√n⌋`. The Pickands
estimator converges to `ξ = 1/2`. -/
theorem test_nonvacuous_tendstoInMeasure_pickands :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ (∀ i, HasLaw (X i) par P) ∧
      TendstoInMeasure P (fun n ω => pickands (fun i : Fin n => X i ω) (Nat.sqrt n)) atTop
        (fun _ => 1 / 2) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hind, hid, hlaw⟩ := exists_iid_seq par
  refine ⟨Ω, _, P, X, hP, hind, hlaw, ?_⟩
  exact tendstoInMeasure_pickands hXm hind hid
    (fun x => by rw [paretoCDF_eq, (hlaw 0).measure_eq (p := (· ≤ x)) measurableSet_Iic])
    (CumulativeDistributionFunction.isInMDAGEV_paretoCDF two_pos)
    ExtremeValueTheory.tendsto_sqrt_atTop ExtremeValueTheory.tendsto_sqrt_div

/-! ### Moment estimator -/

/-- **Non-vacuity of `ExtremeValueTheory.tendstoInMeasure_momentEstimator_of_isInMDAGEV'`**
(Dekkers–Einmahl–de Haan consistency): an iid `Pareto(1, 2)` sample, `k n = ⌊√n⌋`; the
endpoint condition `∃ y > 0, F y < 1` holds at `y = 1`. The moment estimator converges to
`γ = 1/2`. -/
theorem test_nonvacuous_tendstoInMeasure_momentEstimator :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ (∀ i, HasLaw (X i) par P) ∧
      TendstoInMeasure P (fun n ω => momentEstimator (fun i : Fin n => X i ω) (Nat.sqrt n)) atTop
        (fun _ => 1 / 2) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hind, hid, hlaw⟩ := exists_iid_seq par
  refine ⟨Ω, _, P, X, hP, hind, hlaw, ?_⟩
  refine tendstoInMeasure_momentEstimator_of_isInMDAGEV' hXm hind hid
    (fun x => by rw [paretoCDF_eq, (hlaw 0).measure_eq (p := (· ≤ x)) measurableSet_Iic])
    (CumulativeDistributionFunction.isInMDAGEV_paretoCDF two_pos) ⟨1, one_pos, ?_⟩
    ExtremeValueTheory.tendsto_sqrt_atTop ExtremeValueTheory.tendsto_sqrt_div
  rw [CumulativeDistributionFunction.paretoCDF_apply_of_one_le two_pos le_rfl, one_rpow]
  norm_num

/-! ### A second-order regularly varying law: the shifted Pareto `Y + 1`, `Y ~ Pareto(1, 1)` -/

/-- Test-specific: the law of `Y + 1`, `Y ~ Pareto(1, 1)`: `P(X > x) = (x - 1)⁻¹` for
`x ≥ 2`. -/
private noncomputable abbrev spar : Measure ℝ := (paretoMeasure 1 1).map (· + 1)

instance : IsProbabilityMeasure (paretoMeasure 1 1) :=
  isProbabilityMeasure_paretoMeasure one_pos one_pos

instance : IsProbabilityMeasure spar :=
  (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const 1).aemeasurable).2 inferInstance

/-- Test-specific: tail of the shifted law. -/
private theorem spar_Ioi (x : ℝ) : spar (Ioi x) = paretoMeasure 1 1 (Ioi (x - 1)) := by
  rw [spar, Measure.map_apply (by fun_prop : Measurable fun y : ℝ => y + 1)
    measurableSet_Ioi]
  congr 1
  ext y; simp [sub_lt_iff_lt_add]

/-- Test-specific: tail of the shifted law beyond `2`. -/
private theorem spar_Ioi_of_two_le {x : ℝ} (hx : 2 ≤ x) : (spar (Ioi x)).toReal = (x - 1)⁻¹ := by
  rw [spar_Ioi, SymmPareto.pareto_Ioi one_pos (by linarith),
    ENNReal.toReal_ofReal (by have : 0 < x - 1 := by linarith
                              positivity), rpow_neg_one]

/-- Test-specific: tail of the shifted law below `2`. -/
private theorem spar_Ioi_of_lt_two {x : ℝ} (hx : x < 2) : (spar (Ioi x)).toReal = 1 := by
  have h1 : paretoMeasure 1 1 (Ioi 1) = 1 := by
    rw [SymmPareto.pareto_Ioi one_pos le_rfl, one_rpow, ENNReal.ofReal_one]
  have h2 : paretoMeasure 1 1 (Ioi (x - 1)) = 1 :=
    le_antisymm prob_le_one (h1 ▸ measure_mono (Ioi_subset_Ioi (by linarith)))
  rw [spar_Ioi, h2, ENNReal.toReal_one]

/-- Test-specific: the tail quantile function of the shifted Pareto law is `U(t) = t + 1` for
`t > 1`. -/
private theorem survivalQuantile_eq {F : ℝ → ℝ} (hF2 : ∀ x, 2 ≤ x → F x = (x - 1)⁻¹)
    (hF1 : ∀ x, x < 2 → F x = 1) {t : ℝ} (ht : 1 < t) : survivalQuantile F t = t + 1 := by
  have hS : {x | F x ≤ t⁻¹} = Ici (t + 1) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici]
    rcases le_or_gt 2 x with hx | hx
    · rw [hF2 x hx, inv_le_inv₀ (by linarith) (by linarith)]
      constructor <;> intro h <;> linarith
    · rw [hF1 x hx]
      constructor
      · intro h; exact absurd h (not_le.2 (inv_lt_one_of_one_lt₀ ht))
      · intro h; linarith
  rw [survivalQuantile, ite_eq_left_iff.mpr (fun h => absurd ht h), hS, csInf_Ici]

/-- Test-specific: the auxiliary function `A(t) = -1/(t + 1)` of
`isSecondOrderRegularlyVarying_add_const` with `c = 1`. -/
private noncomputable def auxA (t : ℝ) : ℝ := -(1 / (t + 1))

/-- Test-specific: `√k A(n / k) → 0` for `k n = ⌊√n⌋`. -/
private theorem tendsto_sqrt_mul_auxA :
    Tendsto (fun n : ℕ => √(Nat.sqrt n : ℝ) * auxA (n / Nat.sqrt n)) atTop (𝓝 0) := by
  -- `|√k A(n/k)| ≤ √k / (n / k) ≤ √k / k = (√k)⁻¹`
  have hs : Tendsto (fun n : ℕ => (√(Nat.sqrt n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_sqrt_cast)
  refine squeeze_zero_norm' ?_ hs
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hk := one_le_sqrt hn
  have hkk := sqrt_mul_self_le n
  set k : ℝ := ((Nat.sqrt n : ℕ) : ℝ)
  have hsk : 0 < √k := sqrt_pos.2 (by linarith)
  have hnk : k ≤ (n : ℝ) / k := by rw [le_div_iff₀ (by linarith)]; linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hsk, auxA, abs_neg, one_div, abs_inv,
    abs_of_pos (by positivity), ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have hsq : √k * √k = k := mul_self_sqrt (by linarith)
  calc (√k)⁻¹ * ((n : ℝ) / k + 1) ≥ (√k)⁻¹ * k := by gcongr; linarith
    _ = √k := by rw [eq_comm, eq_inv_mul_iff_mul_eq₀ hsk.ne', hsq]

/-- Test-specific: for the iid shifted Pareto sample the tail quantile function of `X 0` is
second-order regularly varying with `γ = 1`, `ρ = -1`, `A = auxA`
(`isSecondOrderRegularlyVarying_add_const`). -/
private theorem isSecondOrderRegularlyVarying_spar {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (h : HasLaw Y spar P) :
    IsSecondOrderRegularlyVarying (survivalQuantile (survival P Y)) 1 (-1) auxA := by
  refine isSecondOrderRegularlyVarying_add_const one_pos ((eventually_gt_atTop 1).mono
    fun t ht => survivalQuantile_eq (fun x hx => ?_) (fun x hx => ?_) ht)
  · rw [survival, h.measure_eq (p := (x < ·)) measurableSet_Ioi, spar_Ioi_of_two_le hx]
  · rw [survival, h.measure_eq (p := (x < ·)) measurableSet_Ioi, spar_Ioi_of_lt_two hx]

/-! ### Hill estimator: asymptotic normality -/

/-- Test-specific: the limit law `N(λ / (1 - ρ), γ²)` with `λ = 0`, `ρ = -1`, `γ = 1`. -/
private noncomputable abbrev hillLimit : Measure ℝ :=
  gaussianReal (0 / (1 - (-1))) (((1 : ℝ) ^ 2).toNNReal)

/-- **Non-vacuity of `ExtremeValueTheory.tendstoInDistribution_hill`** (Hill asymptotic
normality under second-order regular variation): an iid shifted Pareto sample `X = Y + 1`,
`Y ~ Pareto(1, 1)`, has `U(t) = t + 1`, second-order regularly varying with `γ = 1`, `ρ = -1`,
`A(t) = -(t + 1)⁻¹` (a genuine second-order term, not the exact Pareto case); with
`k n = ⌊√n⌋`, `√k A(n/k) → λ = 0`, and `√k (H_{k,n} - 1) ⇒ N(0, 1)`. -/
theorem test_nonvacuous_tendstoInDistribution_hill :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      ∃ _ : IsProbabilityMeasure P, iIndepFun X P ∧ (∀ i, HasLaw (X i) spar P) ∧
      TendstoInDistribution
        (fun n ω => √(Nat.sqrt n : ℝ) * (hill (fun i : Fin n => X i ω) (Nat.sqrt n) - 1))
        atTop id (fun _ => P) hillLimit := by
  obtain ⟨Ω, _, P, X, hP, hXm, hind, hid, hlaw⟩ := exists_iid_seq spar
  have := hP
  refine ⟨Ω, _, P, X, hP, hind, hlaw, ?_⟩
  exact tendstoInDistribution_hill hXm hind hid one_pos
    (isSecondOrderRegularlyVarying_spar (hlaw 0)) ExtremeValueTheory.tendsto_sqrt_atTop
    ExtremeValueTheory.tendsto_sqrt_div
    tendsto_sqrt_mul_auxA HasLaw.id

/-! ### Weissman estimator: asymptotic normality -/

/-- Test-specific: `log x / √x → 0`. -/
private theorem tendsto_log_div_sqrt :
    Tendsto (fun x : ℝ => Real.log x / √x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [sqrt_eq_rpow]

/-- **Non-vacuity of `ExtremeValueTheory.tendstoInDistribution_weissman`** (asymptotic
normality of the Weissman extreme quantile estimator): the iid shifted Pareto sample above
(`γ = 1`, `ρ = -1 < 0`), `k n = ⌊√n⌋`, and the extreme level `pₙ = 1/n`, so that
`dₙ = k / (n pₙ) = k → ∞` and `log dₙ / √k → 0`. -/
theorem test_nonvacuous_tendstoInDistribution_weissman :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      ∃ _ : IsProbabilityMeasure P, iIndepFun X P ∧ (∀ i, HasLaw (X i) spar P) ∧
      TendstoInDistribution (fun n ω =>
        √(Nat.sqrt n : ℝ) / Real.log ((Nat.sqrt n : ℝ) / (n * (1 / n : ℝ))) *
          (weissman (fun i : Fin n => X i ω) (Nat.sqrt n) (1 / n) /
            tailQuantile P (X 0) (1 / n) - 1))
        atTop id (fun _ => P) hillLimit := by
  obtain ⟨Ω, _, P, X, hP, hXm, hind, hid, hlaw⟩ := exists_iid_seq spar
  have := hP
  refine ⟨Ω, _, P, X, hP, hind, hlaw, ?_⟩
  have hd : ∀ᶠ n : ℕ in atTop, (Nat.sqrt n : ℝ) / (n * (1 / n : ℝ)) = Nat.sqrt n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  refine tendstoInDistribution_weissman hXm hind hid one_pos (by norm_num)
    (isSecondOrderRegularlyVarying_spar (hlaw 0)) ExtremeValueTheory.tendsto_sqrt_atTop
    ExtremeValueTheory.tendsto_sqrt_div
    tendsto_sqrt_mul_auxA ?_ ?_ ?_ HasLaw.id
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  · exact tendsto_sqrt_cast.congr' (hd.mono fun n h => h.symm)
  · exact (tendsto_log_div_sqrt.comp tendsto_sqrt_cast).congr'
      (hd.mono fun n h => by simp only [Function.comp_apply, h])

end Test.NonVacuity.Statistics
