/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ConfidenceIntervals
import ExtremeValueTheory.StableLaws.LevyContinuity

/-!
# Random-count peaks-over-threshold MLE and return-level intervals ([Coles 2001, §4.3.3])

In `ExtremeValueTheory.Statistics.ReturnLevelNormality` and `ConfidenceIntervals`, the GPD POT
return-level normality and plug-in Wald interval assume a deterministic number `n` of excesses and
a known exceedance probability `ζ`. In practice, given `n` observations with threshold `u`, the
number of exceedances `Nₙ = ∑_{i<n} 1_{Xᵢ > u} ~ Binomial(n, ζ₀)` is random, the exceedance rate
is estimated by `ζ̂ₙ = Nₙ / n`, and the GPD parameters `(ξ̂_{Nₙ}, σ̂_{Nₙ})` are estimated by maximum
likelihood on the `Nₙ` excesses.

We formalize the complete joint asymptotic theory ([Coles 2001, §4.3.3], equations (4.14)–(4.15))
across the entire regular range `ξ₀ > -1/2` (including `ξ₀ = 0`):

* `tendstoInDistribution_indep_randomIndex`: general joint convergence in distribution of
  `(Aₙ, B_{Nₙ})` when `(Aₙ, Nₙ)` is independent of `B`, `Aₙ ⇒ Z₁`, `Bₘ ⇒ Z₂`, and `Nₙ → ∞` in
  probability (proved via characteristic functions and Lévy's convergence theorem).
* `potCov`: the `3 × 3` block-diagonal asymptotic covariance matrix
  `blockdiag(ζ₀ (1 - ζ₀), ζ₀⁻¹ I(ξ₀, σ₀)⁻¹)` of `√n (ζ̂ₙ - ζ₀, ξ̂_{Nₙ} - ξ₀, σ̂_{Nₙ} - σ₀)`.
* `tendstoInDistribution_potRandomCountMLE`: **joint asymptotic normality of `(ζ̂ₙ, ξ̂_{Nₙ}, σ̂_{Nₙ})`**
  for iid Bernoulli(`ζ₀`) exceedance indicators and independent iid `GPD(ξ₀, σ₀)` excesses,
  for all `ξ₀ > -1/2` (including `ξ₀ = 0`).
* `potReturnLevelVar`, `potReturnLevelVar_eq`, `potReturnLevelVar_pos`: the full Coles (4.15)
  asymptotic variance `ζ₀ (1 - ζ₀) (σ₀ N (N ζ₀)^{ξ₀ - 1})² + ζ₀⁻¹ gpdReturnLevelVar ξ₀ σ₀ ζ₀ N`.
* `tendstoInDistribution_potReturnLevelRandomCount`: **unconditional asymptotic normality** of the
  random-count POT return level `√n (x̂_N - x_N) ⇒ N(0, potReturnLevelVar ζ₀ ξ₀ σ₀ N)`.
* `tendsto_measure_mem_potReturnLevelPlugInInterval`,
  `exists_potReturnLevelPlugInInterval_tendsto`: **computable plug-in confidence interval** with
  asymptotic coverage `N(0, 1)([-z, z])`, with no known-`ζ` or deterministic-count hypothesis.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §4.3.3.
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72 (1985).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace Complex

namespace ExtremeValueTheory

/-! ### Independent random-index joint convergence in distribution -/

section RandomIndex

variable {Ω Ω₁ Ω₂ Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ₁ : MeasurableSpace Ω₁}
  {mΩ₂ : MeasurableSpace Ω₂} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
  {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- Applying a countable family of measurable maps at a random `ℕ`-valued index is measurable. -/
lemma measurable_apply_randomIndex {E : Type*} [MeasurableSpace E]
    {N : Ω → ℕ} (hN : Measurable N) {B : ℕ → Ω → E} (hB : ∀ m, Measurable (B m)) :
    Measurable fun ω => B (N ω) ω := by
  intro s hs
  have heq : (fun ω => B (N ω) ω) ⁻¹' s = ⋃ m : ℕ, (N ⁻¹' {m}) ∩ (B m ⁻¹' s) := by
    ext ω; simp
  rw [heq]
  exact MeasurableSet.iUnion fun m => (hN (measurableSet_singleton m)).inter (hB m hs)

omit [IsProbabilityMeasure P] in
/-- Applying a countable family of `AEMeasurable` maps at a random `ℕ`-valued index is `AEMeasurable`. -/
lemma aemeasurable_apply_randomIndex {E : Type*} [MeasurableSpace E]
    {N : Ω → ℕ} (hN : Measurable N) {B : ℕ → Ω → E} (hB : ∀ m, AEMeasurable (B m) P) :
    AEMeasurable (fun ω => B (N ω) ω) P := by
  set B' : ℕ → Ω → E := fun m => (hB m).mk (B m)
  have hB'm : ∀ m, Measurable (B' m) := fun m => (hB m).measurable_mk
  have hae : ∀ᵐ ω ∂P, ∀ m, B m ω = B' m ω := ae_all_iff.2 fun m => (hB m).ae_eq_mk
  refine (measurable_apply_randomIndex hN hB'm).aemeasurable.congr ?_
  filter_upwards [hae] with ω hω
  exact (hω (N ω)).symm

/-- **Joint convergence in distribution with an independent random sample size**:
if `(Aₙ, Nₙ)` is independent of `Bₘ` for all `n, m`, `Aₙ ⇒ Z₁`, `Bₘ ⇒ Z₂`, and `Nₙ → ∞` in
probability, then `(Aₙ, B_{Nₙ}) ⇒ Z` where `Z` has the independent product law of `(Z₁, Z₂)`. -/
theorem tendstoInDistribution_indep_randomIndex
    {A : ℕ → Ω → ℝ} (hAm : ∀ n, Measurable (A n))
    {N : ℕ → Ω → ℕ} (hNm : ∀ n, Measurable (N n))
    {B : ℕ → Ω → EuclideanSpace ℝ (Fin 2)} (hBm : ∀ m, AEMeasurable (B m) P)
    (hind : ∀ n m, IndepFun (fun ω => (A n ω, N n ω)) (B m) P)
    {Z₁ : Ω₁ → ℝ} (hA : TendstoInDistribution A atTop Z₁ (fun _ => P) P₁)
    {Z₂ : Ω₂ → EuclideanSpace ℝ (Fin 2)} (hB : TendstoInDistribution B atTop Z₂ (fun _ => P) P₂)
    (hN_top : ∀ M : ℕ, Tendsto (fun n => P {ω | N n ω < M}) atTop (𝓝 0))
    {Z : Ω' → EuclideanSpace ℝ (Fin 3)} (hZm : AEMeasurable Z P')
    (hZ_char : ∀ t : EuclideanSpace ℝ (Fin 3),
      charFun (P'.map Z) t = charFun (P₁.map Z₁) (t 0) * charFun (P₂.map Z₂) !₂[t 1, t 2]) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (!₂[A n ω, B (N n ω) ω 0, B (N n ω) ω 1] : EuclideanSpace ℝ (Fin 3)))
      atTop Z (fun _ => P) P' := by
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
    !₂[A n ω, B (N n ω) ω 0, B (N n ω) ω 1]
  have hYm : ∀ n, AEMeasurable (Y n) P := fun n => by
    have hBN : AEMeasurable (fun ω => B (N n ω) ω) P := aemeasurable_apply_randomIndex (hNm n) hBm
    have h0 : AEMeasurable (fun ω => A n ω) P := (hAm n).aemeasurable
    have h1 : AEMeasurable (fun ω => B (N n ω) ω 0) P :=
      ((continuous_apply (0 : Fin 2)).measurable.comp (WithLp.measurable_ofLp 2 _)).comp_aemeasurable hBN
    have h2 : AEMeasurable (fun ω => B (N n ω) ω 1) P :=
      ((continuous_apply (1 : Fin 2)).measurable.comp (WithLp.measurable_ofLp 2 _)).comp_aemeasurable hBN
    exact (WithLp.measurable_toLp 2 _).comp_aemeasurable (AEMeasurable.of_eval fun i => by
      fin_cases i <;> simpa using ‹_›)
  refine ⟨hYm, hZm, ?_⟩
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  change Tendsto (fun n => charFun (P.map (Y n)) t) atTop (𝓝 (charFun (P'.map Z) t))
  rw [hZ_char t]
  set t' : EuclideanSpace ℝ (Fin 2) := !₂[t 1, t 2]
  -- Convergence of `charFun (P.map (A n)) (t 0)` and `ψ m = charFun (P.map (B m)) t'`
  have hcharA : Tendsto (fun n => charFun (P.map (A n)) (t 0)) atTop (𝓝 (charFun (P₁.map Z₁) (t 0))) := by
    have := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hA.tendsto) (t 0)
    simpa using this
  have hcharB : Tendsto (fun m => charFun (P.map (B m)) t') atTop (𝓝 (charFun (P₂.map Z₂) t')) := by
    have := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hB.tendsto) t'
    simpa using this
  set ψ : ℕ → ℂ := fun m => charFun (P.map (B m)) t'
  set ψlim : ℂ := charFun (P₂.map Z₂) t'
  -- Show `charFun (P.map (Y n)) t - charFun (P.map (A n)) (t 0) * ψlim → 0`
  have hdiff : Tendsto (fun n => charFun (P.map (Y n)) t - charFun (P.map (A n)) (t 0) * ψlim)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM⟩ := (Metric.tendsto_nhds.1 hcharB (ε / 2) (by positivity)).exists_forall_of_atTop
    have hN_ev := (hN_top M).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show (0 : ℝ) < ε / 4 by positivity)))
    filter_upwards [hN_ev] with n hn
    rw [dist_zero_right]
    set S : ℕ → Set Ω := fun m => N n ⁻¹' {m}
    have hSm : ∀ m, MeasurableSet (S m) := fun m => hNm n (measurableSet_singleton m)
    have hSdisj : Pairwise fun m₁ m₂ => Disjoint (S m₁) (S m₂) := fun m₁ m₂ hne =>
      Set.disjoint_left.2 fun ω h1 h2 => hne (h1.symm.trans h2)
    have hSuniv : (⋃ m : ℕ, S m) = univ := by ext ω; simp [S]
    -- Integral of `e^{i ⟪t, Y n ω⟫}` splits over `{N n = m}`
    have hcharY_eq : charFun (P.map (Y n)) t =
        ∫ ω, Complex.exp ((⟪t, Y n ω⟫ : ℝ) * Complex.I) ∂P := by
      rw [charFun_apply]
      rw [integral_map (hYm n)
        (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)).aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      dsimp only
      rw [real_inner_comm]
    have hcharA_eq : charFun (P.map (A n)) (t 0) =
        ∫ ω, Complex.exp ((t 0 * A n ω : ℝ) * Complex.I) ∂P := by
      rw [charFun_apply_real]
      rw [integral_map (hAm n).aemeasurable
        (by fun_prop : Continuous fun x : ℝ => Complex.exp ((t 0 : ℂ) * (x : ℂ) * Complex.I)).aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [Complex.ofReal_mul]
    have hcharB_eq : ∀ m, ψ m = ∫ ω, Complex.exp ((⟪t', B m ω⟫ : ℝ) * Complex.I) ∂P := fun m => by
      simp only [ψ, charFun_apply]
      rw [integral_map (hBm m)
        (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin 2) =>
          Complex.exp ((⟪x, t'⟫ : ℝ) * Complex.I)).aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      dsimp only
      rw [real_inner_comm]
    -- Integrability of bounded complex exponentials
    have hint_Y : Integrable (fun ω => Complex.exp ((⟪t, Y n ω⟫ : ℝ) * Complex.I)) P := by
      refine Integrable.of_bound
        ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_const.prodMk continuous_id))).mul continuous_const)).measurable.comp_aemeasurable
          (hYm n)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
      rw [Complex.norm_exp_ofReal_mul_I]
    have hint_A : Integrable (fun ω => Complex.exp ((t 0 * A n ω : ℝ) * Complex.I)) P := by
      refine Integrable.of_bound
        ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_const.mul continuous_id)).mul continuous_const)).measurable.comp
          (hAm n)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
      rw [Complex.norm_exp_ofReal_mul_I]
    -- Apply `integral_iUnion` to both `charFun Y` and `charFun A`
    have hsumY : charFun (P.map (Y n)) t =
        ∑' m : ℕ, ∫ ω in S m, Complex.exp ((⟪t, Y n ω⟫ : ℝ) * Complex.I) ∂P := by
      rw [hcharY_eq, ← setIntegral_univ, ← hSuniv,
        integral_iUnion hSm hSdisj hint_Y.integrableOn]
    have hsumA : charFun (P.map (A n)) (t 0) =
        ∑' m : ℕ, ∫ ω in S m, Complex.exp ((t 0 * A n ω : ℝ) * Complex.I) ∂P := by
      rw [hcharA_eq, ← setIntegral_univ, ← hSuniv,
        integral_iUnion hSm hSdisj hint_A.integrableOn]
    -- Factorization on each `S m` by independence of `(A n, N n)` and `B m`
    have hfac : ∀ m : ℕ,
        ∫ ω in S m, Complex.exp ((⟪t, Y n ω⟫ : ℝ) * Complex.I) ∂P =
          (∫ ω in S m, Complex.exp ((t 0 * A n ω : ℝ) * Complex.I) ∂P) * ψ m := by
      intro m
      set f₁ : ℝ × ℕ → ℂ := fun p =>
        if p.2 = m then Complex.exp ((t 0 * p.1 : ℝ) * Complex.I) else 0
      set f₂ : EuclideanSpace ℝ (Fin 2) → ℂ := fun v => Complex.exp ((⟪t', v⟫ : ℝ) * Complex.I)
      have hf₁m : Measurable f₁ := by
        unfold f₁
        refine Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) ?_ measurable_const
        have hc : Continuous fun p : ℝ × ℕ => Complex.exp ((t 0 * p.1 : ℝ) * Complex.I) :=
          Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
            (continuous_const.mul continuous_fst)).mul continuous_const)
        exact hc.measurable
      have hf₂m : Measurable f₂ := by
        have hc : Continuous f₂ := Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_const.prodMk continuous_id))).mul continuous_const)
        exact hc.measurable
      have hind_f : IndepFun (f₁ ∘ fun ω => (A n ω, N n ω)) (f₂ ∘ B m) P :=
        (hind n m).comp hf₁m hf₂m
      have hmul := hind_f.integral_fun_mul_eq_mul_integral
        (hf₁m.comp ((hAm n).prodMk (hNm n))).aestronglyMeasurable
        (hf₂m.comp_aemeasurable (hBm m)).aestronglyMeasurable
      have hlhs : ∫ ω in S m, Complex.exp ((⟪t, Y n ω⟫ : ℝ) * Complex.I) ∂P =
          ∫ ω, (f₁ ∘ fun ω => (A n ω, N n ω)) ω * (f₂ ∘ B m) ω ∂P := by
        rw [← integral_indicator (hSm m)]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        by_cases hω : ω ∈ S m
        · have hNm_eq : N n ω = m := hω
          rw [Set.indicator_of_mem hω]
          simp only [Function.comp_apply, f₁, f₂, hNm_eq, ↓reduceIte]
          rw [← Complex.exp_add]
          congr 1
          have hinner : ⟪t, Y n ω⟫ = t 0 * A n ω + ⟪t', B m ω⟫ := by
            simp [Y, t', hNm_eq, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
            ring
          rw [hinner, Complex.ofReal_add, add_mul]
        · have hNm_ne : N n ω ≠ m := hω
          rw [Set.indicator_of_notMem hω]
          simp [Function.comp_apply, f₁, hNm_ne]
      have hrhs1 : ∫ ω, (f₁ ∘ fun ω => (A n ω, N n ω)) ω ∂P =
          ∫ ω in S m, Complex.exp ((t 0 * A n ω : ℝ) * Complex.I) ∂P := by
        rw [← integral_indicator (hSm m)]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        by_cases hω : ω ∈ S m
        · have hNm_eq : N n ω = m := hω
          rw [Set.indicator_of_mem hω]; simp [Function.comp_apply, f₁, hNm_eq]
        · have hNm_ne : N n ω ≠ m := hω
          rw [Set.indicator_of_notMem hω]; simp [Function.comp_apply, f₁, hNm_ne]
      rw [hlhs, hmul, hrhs1, hcharB_eq m]
      rfl
    -- Bound each term `‖a_m * (ψ m - ψlim)‖ ≤ P.real (S m) * ‖ψ m - ψlim‖`
    set a : ℕ → ℂ := fun m => ∫ ω in S m, Complex.exp ((t 0 * A n ω : ℝ) * Complex.I) ∂P
    have ha_norm : ∀ m, ‖a m‖ ≤ P.real (S m) := fun m => by
      have h1 := norm_integral_le_integral_norm
        (f := fun ω => Complex.exp ((t 0 * A n ω : ℝ) * Complex.I)) (μ := P.restrict (S m))
      have h2 : ∫ ω in S m, ‖Complex.exp ((t 0 * A n ω : ℝ) * Complex.I)‖ ∂P = P.real (S m) := by
        simp_rw [Complex.norm_exp_ofReal_mul_I]
        simp [measureReal_def]
      linarith
    have hψ_norm : ∀ m, ‖ψ m‖ ≤ 1 := fun m => by
      rw [hcharB_eq m]
      calc ‖∫ ω, Complex.exp ((⟪t', B m ω⟫ : ℝ) * Complex.I) ∂P‖
          ≤ ∫ ω, ‖Complex.exp ((⟪t', B m ω⟫ : ℝ) * Complex.I)‖ ∂P := norm_integral_le_integral_norm _
        _ = 1 := by simp [Complex.norm_exp_ofReal_mul_I]
    have hψlim_norm : ‖ψlim‖ ≤ 1 := by
      simpa [ψlim] using norm_charFun_le_one (μ := P₂.map Z₂) t'
    have hS_tsum_enn : ∑' m : ℕ, P (S m) = 1 := by
      rw [← measure_iUnion hSdisj hSm, hSuniv, measure_univ]
    have hS_summable : Summable fun m : ℕ => P.real (S m) := by
      have h1 : Summable fun m : ℕ => (P (S m)).toReal :=
        ENNReal.summable_toReal (by rw [hS_tsum_enn]; exact ENNReal.one_ne_top)
      simpa [measureReal_def] using h1
    have hS_tsum : ∑' m : ℕ, P.real (S m) = 1 := by
      have h2 := ENNReal.tsum_toReal_eq (f := fun m => P (S m)) (fun m => measure_ne_top P (S m))
      simp only [measureReal_def, ← h2, hS_tsum_enn, ENNReal.toReal_one]
    have hterm_summable_norm : Summable fun m : ℕ => ‖a m * (ψ m - ψlim)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) (hS_summable.mul_right 2)
      rw [norm_mul]
      have h2 : ‖ψ m - ψlim‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hψ_norm m, hψlim_norm])
      exact mul_le_mul (ha_norm m) h2 (norm_nonneg _) measureReal_nonneg
    have hsum1 : Summable fun m : ℕ => a m * ψ m := by
      refine Summable.of_norm_bounded (g := fun m => P.real (S m)) hS_summable fun m => ?_
      rw [norm_mul]
      calc ‖a m‖ * ‖ψ m‖ ≤ P.real (S m) * 1 := mul_le_mul (ha_norm m) (hψ_norm m) (norm_nonneg _) measureReal_nonneg
        _ = P.real (S m) := mul_one _
    have hsum2 : Summable fun m : ℕ => a m * ψlim := by
      refine Summable.of_norm_bounded (g := fun m => P.real (S m)) hS_summable fun m => ?_
      rw [norm_mul]
      calc ‖a m‖ * ‖ψlim‖ ≤ P.real (S m) * 1 := mul_le_mul (ha_norm m) hψlim_norm (norm_nonneg _) measureReal_nonneg
        _ = P.real (S m) := mul_one _
    have hdiff_eq : charFun (P.map (Y n)) t - charFun (P.map (A n)) (t 0) * ψlim =
        ∑' m : ℕ, a m * (ψ m - ψlim) := by
      rw [hsumY, hsumA, ← tsum_mul_right]
      simp_rw [hfac, mul_sub]
      exact (hsum1.tsum_sub hsum2).symm
    rw [hdiff_eq]
    have hnorm_le : ‖∑' m : ℕ, a m * (ψ m - ψlim)‖ ≤ ∑' m : ℕ, P.real (S m) * ‖ψ m - ψlim‖ := by
      refine (norm_tsum_le_tsum_norm hterm_summable_norm).trans ?_
      refine Summable.tsum_le_tsum (fun m => ?_) hterm_summable_norm
        (Summable.of_nonneg_of_le (fun m => mul_nonneg measureReal_nonneg (norm_nonneg _))
          (fun m => mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hψ_norm m, hψlim_norm])) measureReal_nonneg)
          (hS_summable.mul_right 2))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha_norm m) (norm_nonneg _)
    -- Split `∑' m` at `M`
    have hsplit : ∑' m : ℕ, P.real (S m) * ‖ψ m - ψlim‖ ≤
        2 * P.real {ω | N n ω < M} + ε / 2 := by
      have hsumm_rhs : Summable fun m : ℕ => P.real (S m) * ‖ψ m - ψlim‖ :=
        Summable.of_nonneg_of_le (fun m => mul_nonneg measureReal_nonneg (norm_nonneg _))
          (fun m => mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hψ_norm m, hψlim_norm])) measureReal_nonneg)
          (hS_summable.mul_right 2)
      have hle_ind : ∀ m : ℕ, P.real (S m) * ‖ψ m - ψlim‖ ≤
          (if m < M then 2 * P.real (S m) else 0) + (ε / 2) * P.real (S m) := fun m => by
        by_cases hm : m < M
        · simp only [hm, ↓reduceIte]
          have h2 : ‖ψ m - ψlim‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hψ_norm m, hψlim_norm])
          have : P.real (S m) * ‖ψ m - ψlim‖ ≤ P.real (S m) * 2 :=
            mul_le_mul_of_nonneg_left h2 measureReal_nonneg
          linarith [mul_nonneg (show (0 : ℝ) ≤ ε / 2 by positivity) (measureReal_nonneg (μ := P) (s := S m))]
        · simp only [hm, ↓reduceIte, zero_add]
          have hge : M ≤ m := not_lt.1 hm
          have hε2 : ‖ψ m - ψlim‖ ≤ ε / 2 := by
            have := hM m hge
            rw [dist_eq_norm] at this
            exact this.le
          have := mul_le_mul_of_nonneg_left hε2 (measureReal_nonneg (μ := P) (s := S m))
          linarith
      have hfin_sum : Summable fun m : ℕ => if m < M then 2 * P.real (S m) else 0 :=
        summable_of_ne_finset_zero (s := Finset.range M) fun m hm => by
          simp [Finset.mem_range.not.1 hm]
      have htsum_fin : ∑' m : ℕ, (if m < M then 2 * P.real (S m) else 0) = 2 * P.real {ω | N n ω < M} := by
        rw [tsum_eq_sum (s := Finset.range M) fun m hm => by simp [Finset.mem_range.not.1 hm]]
        have hcongr : ∑ m ∈ Finset.range M, (if m < M then 2 * P.real (S m) else 0) =
            2 * ∑ m ∈ Finset.range M, P.real (S m) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m hm => by simp [Finset.mem_range.1 hm]
        rw [hcongr]
        congr 1
        have heq_set : {ω | N n ω < M} = ⋃ m ∈ Finset.range M, S m := by
          ext ω; simp [S]
        rw [heq_set, measureReal_biUnion_finset (fun a _ b _ hab => hSdisj hab) (fun m _ => hSm m)]
      have htsum_le := Summable.tsum_le_tsum hle_ind hsumm_rhs (hfin_sum.add (hS_summable.mul_left (ε / 2)))
      rw [hfin_sum.tsum_add (hS_summable.mul_left (ε / 2)), htsum_fin, tsum_mul_left, hS_tsum, mul_one]
        at htsum_le
      exact htsum_le
    have hP_lt : P.real {ω | N n ω < M} < ε / 4 := by
      rw [measureReal_def]
      exact (ENNReal.toReal_lt_of_lt_ofReal hn).trans_le le_rfl
    linarith
  have hprod := hcharA.mul_const ψlim
  have hcomb := hdiff.add hprod
  simp only [sub_add_cancel, zero_add] at hcomb
  exact hcomb

end RandomIndex

/-! ### Random-count POT joint MLE normality and return-level intervals ([Coles §4.3.3]) -/

section POTRandomCount

variable {Ω Ω' Ω'' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mΩ'' : MeasurableSpace Ω''} {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {P'' : Measure Ω''} [IsProbabilityMeasure P'']

/-- The `3 × 3` block-diagonal asymptotic covariance matrix of `√n (ζ̂ₙ - ζ₀, ξ̂_{Nₙ} - ξ₀, σ̂_{Nₙ} - σ₀)`
in the random-count POT model ([Coles 2001, §4.3.3, eq. (4.14)]):
`blockdiag(ζ (1 - ζ), ζ⁻¹ I(ξ, σ)⁻¹)`. -/
noncomputable def potCov (ζ ξ σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ζ * (1 - ζ), 0, 0;
     0, ζ⁻¹ * (1 + ξ) ^ 2, -(ζ⁻¹ * σ * (1 + ξ));
     0, -(ζ⁻¹ * σ * (1 + ξ)), 2 * ζ⁻¹ * σ ^ 2 * (1 + ξ)]

/-- `potCov ζ ξ σ` is positive definite for `0 < ζ < 1`, `ξ > -1/2`, `σ > 0`. -/
theorem posDef_potCov {ζ ξ σ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hξ : -1 / 2 < ξ) (hσ : 0 < σ) :
    (potCov ζ ξ σ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [potCov]
  · rw [star_trivial]
    have hq : v ⬝ᵥ potCov ζ ξ σ *ᵥ v =
        ζ * (1 - ζ) * v 0 ^ 2 +
          ζ⁻¹ * ((![v 1, v 2] : Fin 2 → ℝ) ⬝ᵥ gpdFisherInfoInv ξ σ *ᵥ ![v 1, v 2]) := by
      simp [potCov, gpdFisherInfoInv, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two]
      ring
    rw [hq]
    have h1 : 0 ≤ ζ * (1 - ζ) * v 0 ^ 2 :=
      mul_nonneg (mul_nonneg hζ0.le (sub_nonneg.2 hζ1.le)) (sq_nonneg (v 0))
    have h2 : 0 ≤ ζ⁻¹ * ((![v 1, v 2] : Fin 2 → ℝ) ⬝ᵥ gpdFisherInfoInv ξ σ *ᵥ ![v 1, v 2]) :=
      mul_nonneg (inv_nonneg.2 hζ0.le)
        ((Matrix.posSemidef_iff_dotProduct_mulVec.1 (posDef_gpdFisherInfoInv hξ hσ).posSemidef).2 _)
    by_cases hv0 : v 0 = 0
    · have hne2 : (![v 1, v 2] : Fin 2 → ℝ) ≠ 0 := by
        intro h0
        apply hv
        ext i; fin_cases i
        · exact hv0
        · exact congrFun h0 0
        · exact congrFun h0 1
      have hpos2 := (Matrix.posDef_iff_dotProduct_mulVec.1 (posDef_gpdFisherInfoInv hξ hσ)).2 hne2
      have : 0 < ζ⁻¹ * ((![v 1, v 2] : Fin 2 → ℝ) ⬝ᵥ gpdFisherInfoInv ξ σ *ᵥ ![v 1, v 2]) :=
        mul_pos (inv_pos.2 hζ0) hpos2
      linarith
    · have hpos1 : 0 < ζ * (1 - ζ) * v 0 ^ 2 :=
        mul_pos (mul_pos hζ0 (sub_pos.2 hζ1)) (sq_pos_of_ne_zero hv0)
      linarith

/-- The random exceedance count `Nₙ(ω) = #{i < n : Iᵢ(ω) = true}` for Boolean exceedance indicators. -/
def potCount (I : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter fun i => I i ω).card

/-- The empirical exceedance rate `ζ̂ₙ(ω) = Nₙ(ω) / n`. -/
noncomputable def potRate (I : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) : ℝ :=
  (potCount I n ω : ℝ) / (n : ℝ)

lemma potCount_eq_sum_ind (I : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) :
    (potCount I n ω : ℝ) = ∑ i ∈ Finset.range n, if I i ω then (1 : ℝ) else 0 := by
  simp [potCount, Finset.sum_boole]

lemma measurable_potCount {I : ℕ → Ω → Bool} (hI : ∀ i, Measurable (I i)) (n : ℕ) :
    Measurable (potCount I n) := by
  have heq : potCount I n = fun ω => ∑ i ∈ Finset.range n, if I i ω then 1 else 0 := by
    funext ω; simp [potCount]
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (hI i (measurableSet_singleton true)) measurable_const measurable_const

lemma measurable_potRate {I : ℕ → Ω → Bool} (hI : ∀ i, Measurable (I i)) (n : ℕ) :
    Measurable (potRate I n) :=
  (measurable_from_top.comp (measurable_potCount hI n)).div_const _

/-- **Joint asymptotic normality of `(ζ̂ₙ, ξ̂_{Nₙ}, σ̂_{Nₙ})` in the random-count POT model**
([Coles 2001, §4.3.3, eq. (4.14)]), across the entire regular range `ξ₀ > -1/2` (including `ξ₀ = 0`).

Given iid exceedance indicators `Iᵢ` with `P(Iᵢ = true) = ζ₀ ∈ (0, 1)`, independent iid excesses
`Eⱼ ~ GPD(ξ₀, σ₀)`, and measurable GPD MLE maps `gₘ : ℝᵐ → K` maximizing the GPD log-likelihood
over a compact `K ⊂ {ξ > -1, σ > 0}` with `(ξ₀, σ₀) ∈ interior K`, the estimator
`(ζ̂ₙ, θ̂_{Nₙ})` satisfies:

  `√n (ζ̂ₙ - ζ₀, ξ̂_{Nₙ} - ξ₀, σ̂_{Nₙ} - σ₀) ⇒ N(0, potCov ζ₀ ξ₀ σ₀)`. -/
theorem tendstoInDistribution_potRandomCountMLE
    {ζ₀ ξ₀ σ₀ : ℝ} (hζ0 : 0 < ζ₀) (hζ1 : ζ₀ < 1) (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    {I : ℕ → Ω → Bool} (hIm : ∀ i, Measurable (I i)) (hindI : iIndepFun I P)
    (hIprob : ∀ i, P {ω | I i ω = true} = ENNReal.ofReal ζ₀)
    {E : ℕ → Ω → ℝ} (hE : ∀ j, HasLaw (E j) (gpdMeasure ξ₀ σ₀) P) (hindE : iIndepFun E P)
    (hindIE : IndepFun (fun ω i => I i ω) (fun ω j => E j ω) P)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2)
    (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    {g : (m : ℕ) → (Fin m → ℝ) → ℝ × ℝ} (hgm : ∀ m, Measurable (g m))
    (hgK : ∀ m x, g m x ∈ K)
    (hgmax : ∀ m x, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K (g m x))
    {W : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hW : HasLaw W (multivariateGaussian 0 (potCov ζ₀ ξ₀ σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) •
        !₂[potRate I n ω - ζ₀,
           (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1 - ξ₀,
           (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 - σ₀])
      atTop W (fun _ => P) P' := by
  -- Step 1: CLT and LLN for the Bernoulli exceedance indicators `Yᵢ = 1_{Iᵢ = true}`
  set Y : ℕ → Ω → ℝ := fun i ω => if I i ω then 1 else 0
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    Measurable.ite (hIm i (measurableSet_singleton true)) measurable_const measurable_const
  have hindY : iIndepFun Y P :=
    hindI.comp (fun _ b => if b then (1 : ℝ) else 0) (fun _ => measurable_from_top)
  have hYlaw : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i => by
    refine ⟨(hYm i).aemeasurable, (hYm 0).aemeasurable, ?_⟩
    -- Both `I i` and `I 0` are Bool-valued with the same `P(true) = ζ₀`
    have hIeq : P.map (I i) = P.map (I 0) := by
      ext s _
      rw [Measure.map_apply (hIm i) (MeasurableSet.of_discrete),
        Measure.map_apply (hIm 0) (MeasurableSet.of_discrete)]
      have htrue : P (I i ⁻¹' {true}) = P (I 0 ⁻¹' {true}) := by
        simpa [Set.preimage] using (hIprob i).trans (hIprob 0).symm
      have hfalse : P (I i ⁻¹' {false}) = P (I 0 ⁻¹' {false}) := by
        have hci : I i ⁻¹' {false} = (I i ⁻¹' {true})ᶜ := by ext ω; cases I i ω <;> simp
        have hc0 : I 0 ⁻¹' {false} = (I 0 ⁻¹' {true})ᶜ := by ext ω; cases I 0 ω <;> simp
        rw [hci, hc0, measure_compl (hIm i (measurableSet_singleton true)) (measure_ne_top _ _),
          measure_compl (hIm 0 (measurableSet_singleton true)) (measure_ne_top _ _), htrue]
      -- Case split on `s ⊆ Bool`
      classical
      have hsub : s = (if true ∈ s then {true} else ∅) ∪ (if false ∈ s then {false} else ∅) := by
        ext b; cases b <;> simp
      rw [hsub, Set.preimage_union, Set.preimage_union]
      have hdisj : ∀ k, Disjoint (I k ⁻¹' (if true ∈ s then {true} else ∅))
          (I k ⁻¹' (if false ∈ s then {false} else ∅)) := fun k =>
        Set.disjoint_left.2 fun ω h1 h2 => by
          split_ifs at h1 h2
          · simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
            rw [h1] at h2; exact Bool.noConfusion h2
          · exact h2
          · exact h1
          · exact h1
      rw [measure_union (hdisj i) (hIm i MeasurableSet.of_discrete),
        measure_union (hdisj 0) (hIm 0 MeasurableSet.of_discrete)]
      split_ifs
      · rw [htrue, hfalse]
      · simp only [Set.preimage_empty, measure_empty, add_zero]; exact htrue
      · simp only [Set.preimage_empty, measure_empty, zero_add]; exact hfalse
      · simp only [Set.preimage_empty, measure_empty]
    have hcomp : ∀ k, Y k = (fun b : Bool => if b then (1 : ℝ) else 0) ∘ I k := fun _ => rfl
    rw [hcomp i, hcomp 0, ← Measure.map_map measurable_from_top (hIm i),
      ← Measure.map_map measurable_from_top (hIm 0), hIeq]
  have hYmean : P[Y 0] = ζ₀ := by
    have heq : Y 0 = (I 0 ⁻¹' {true}).indicator (fun _ => (1 : ℝ)) := by
      ext ω; by_cases h : I 0 ω = true <;> simp [Y, h]
    rw [heq, integral_indicator_const _ (hIm 0 (measurableSet_singleton true)),
      smul_eq_mul, mul_one, measureReal_def]
    have hpre : P (I 0 ⁻¹' {true}) = ENNReal.ofReal ζ₀ := hIprob 0
    rw [hpre, ENNReal.toReal_ofReal hζ0.le]
  have hYmemLp : MemLp (Y 0) 2 P :=
    MemLp.of_bound (hYm 0).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      simp only [Y]; split_ifs <;> norm_num)
  have hYvar : Var[Y 0; P] = ζ₀ * (1 - ζ₀) := by
    rw [variance_eq_sub hYmemLp, hYmean]
    have hsq : Y 0 ^ 2 = Y 0 := by
      funext ω; simp only [Pi.pow_apply, Y]; split_ifs <;> norm_num
    rw [hsq, hYmean]
    ring
  -- CLT for `A n ω = √n * (potRate I n ω - ζ₀)`
  set A : ℕ → Ω → ℝ := fun n ω => √(n : ℝ) * (potRate I n ω - ζ₀)
  have hAm : ∀ n, Measurable (A n) := fun n =>
    measurable_const.mul ((measurable_potRate hIm n).sub measurable_const)
  have hZ1 : HasLaw id (gaussianReal 0 (ζ₀ * (1 - ζ₀)).toNNReal)
      (gaussianReal 0 (ζ₀ * (1 - ζ₀)).toNNReal) := HasLaw.id
  have hA_clt : TendstoInDistribution A atTop id (fun _ => P)
      (gaussianReal 0 (ζ₀ * (1 - ζ₀)).toNNReal) := by
    have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
      (by rwa [hYvar] : HasLaw id (gaussianReal 0 Var[Y 0; P].toNNReal) _) hYmemLp hindY hYlaw
    rw [hYmean] at hclt
    refine hclt.congr ?_ (ae_of_all _ fun _ => rfl)
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine Eventually.of_forall fun ω => ?_
      simp [A, potRate]
    · refine Eventually.of_forall fun ω => ?_
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsq : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
      simp only [A, potRate, potCount_eq_sum_ind, Y]
      have hsq0 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
      field_simp [hn0.ne', hsq0]
      rw [Real.sq_sqrt hn0.le]
  -- LLN: `potRate I n → ζ₀` in probability, hence `potCount I n → ∞` in probability
  have hrate_cons : TendstoInMeasure P (potRate I) atTop (fun _ => ζ₀) := by
    have hA_smul : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (potRate I n ω - ζ₀))
        atTop id (fun _ => P) (gaussianReal 0 (ζ₀ * (1 - ζ₀)).toNNReal) := by
      simpa only [smul_eq_mul] using hA_clt
    have h0 := TendstoInDistribution.tendstoInMeasure_of_smul (r := fun n : ℕ => √(n : ℝ))
      hA_smul tendsto_sqrt_natCast_atTop
    have := h0.comp_continuousAt (g := fun x : ℝ => x + ζ₀) (continuous_id.add continuous_const).continuousAt
    simpa using this
  have hN_top : ∀ M : ℕ, Tendsto (fun n => P {ω | potCount I n ω < M}) atTop (𝓝 0) := by
    intro M
    have h1 := (tendstoInMeasure_iff_norm.1 hrate_cons) (ζ₀ / 2) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
      (Eventually.of_forall fun _ => bot_le) ?_
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (M : ℝ) / ζ₀)
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnN : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_left _ _).trans hn
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
    have hlt : (potCount I n ω : ℝ) < (M : ℝ) := by exact_mod_cast hω
    have h2M : 2 * (M : ℝ) < ζ₀ * (n : ℝ) := by
      have := (div_lt_iff₀ hζ0).1 hN₀
      nlinarith
    have hrate_lt : potRate I n ω < ζ₀ / 2 := by
      rw [potRate, div_lt_iff₀ hn0]; linarith
    rw [abs_of_neg (by linarith)]
    linarith
  -- Step 2: GPD MLE CLT for `B m ω = √m • (g m (E₀..E_{m-1}) - (ξ₀, σ₀))` (ALL `ξ₀ > -1/2`, including `0`!)
  set B : ℕ → Ω → EuclideanSpace ℝ (Fin 2) := fun m ω =>
    √(m : ℝ) • !₂[(g m (fun j : Fin m => E j ω)).1 - ξ₀, (g m (fun j : Fin m => E j ω)).2 - σ₀]
  have hBm : ∀ m, AEMeasurable (B m) P := fun m => by
    have hgm_eval : AEMeasurable (fun ω => g m (fun j : Fin m => E j ω)) P :=
      (hgm m).comp_aemeasurable (AEMeasurable.of_eval fun j => (hE j).aemeasurable)
    have h1 : AEMeasurable (fun ω => (g m (fun j : Fin m => E j ω)).1 - ξ₀) P :=
      (measurable_fst.comp_aemeasurable hgm_eval).sub_const ξ₀
    have h2 : AEMeasurable (fun ω => (g m (fun j : Fin m => E j ω)).2 - σ₀) P :=
      (measurable_snd.comp_aemeasurable hgm_eval).sub_const σ₀
    exact ((WithLp.measurable_toLp 2 _).comp_aemeasurable
      (AEMeasurable.of_eval fun i => by fin_cases i <;> simpa using ‹_›)).const_smul (√(m : ℝ))
  have hindAB : ∀ n m, IndepFun (fun ω => (A n ω, potCount I n ω)) (B m) P := fun n m => by
    set f₁ : (ℕ → Bool) → ℝ × ℕ := fun b =>
      (√(n : ℝ) * ((((Finset.range n).filter fun i => b i).card : ℝ) / (n : ℝ) - ζ₀),
       ((Finset.range n).filter fun i => b i).card)
    have hf₁m : Measurable f₁ := by
      have hcnt : Measurable fun b : ℕ → Bool => ((Finset.range n).filter fun i => b i).card := by
        have heq : (fun b : ℕ → Bool => ((Finset.range n).filter fun i => b i).card) =
            fun b => ∑ i ∈ Finset.range n, if b i then 1 else 0 := by
          funext b; simp
        rw [heq]
        refine Finset.measurable_sum _ fun i _ => ?_
        have hset : MeasurableSet {b : ℕ → Bool | b i = true} :=
          measurableSet_eq_fun (measurable_pi_apply i) measurable_const
        exact Measurable.ite hset measurable_const measurable_const
      exact (measurable_const.mul (((measurable_from_top.comp hcnt).div_const _).sub_const _)).prodMk hcnt
    set f₂ : (ℕ → ℝ) → EuclideanSpace ℝ (Fin 2) := fun x =>
      √(m : ℝ) • !₂[(g m (fun j : Fin m => x j)).1 - ξ₀, (g m (fun j : Fin m => x j)).2 - σ₀]
    have hf₂m : Measurable f₂ := by
      have hgm_x : Measurable fun x : ℕ → ℝ => g m (fun j : Fin m => x j) :=
        (hgm m).comp (Measurable.of_eval fun j : Fin m => measurable_pi_apply j.1)
      have h1 : Measurable fun x : ℕ → ℝ => (g m (fun j : Fin m => x j)).1 - ξ₀ :=
        (measurable_fst.comp hgm_x).sub_const ξ₀
      have h2 : Measurable fun x : ℕ → ℝ => (g m (fun j : Fin m => x j)).2 - σ₀ :=
        (measurable_snd.comp hgm_x).sub_const σ₀
      exact ((WithLp.measurable_toLp 2 _).comp
        (measurable_pi_iff.2 fun i => by fin_cases i <;> simpa using ‹_›)).const_smul (√(m : ℝ))
    exact hindIE.comp hf₁m hf₂m
  have hB_clt : TendstoInDistribution B atTop id (fun _ => P)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gpdFisherInfoInv ξ₀ σ₀)) :=
    tendstoInDistribution_gpdMLE_reg hK hKS hθ₀ hξ₀ hσ₀ hE hindE
      (θh := fun m ω => g m (fun j : Fin m => E j ω))
      (fun m => (hgm m).comp_aemeasurable (AEMeasurable.of_eval fun j => (hE j).aemeasurable))
      (fun m ω => hgK m _) (fun m ω => hgmax m _) HasLaw.id
  -- Step 3: Joint CLT for `U n ω = (A n ω, B (N n ω) ω 0, B (N n ω) ω 1)` via random-index theorem
  set V₁ : Matrix (Fin 3) (Fin 3) ℝ :=
    !![ζ₀ * (1 - ζ₀), 0, 0;
       0, (1 + ξ₀) ^ 2, -(σ₀ * (1 + ξ₀));
       0, -(σ₀ * (1 + ξ₀)), 2 * σ₀ ^ 2 * (1 + ξ₀)]
  have hV₁_pd : V₁.PosDef := by
    have heq : V₁ = Matrix.diagonal ![1, √ζ₀, √ζ₀] * potCov ζ₀ ξ₀ σ₀ *
        (Matrix.diagonal ![1, √ζ₀, √ζ₀]).transpose := by
      have hsq : √ζ₀ * √ζ₀ = ζ₀ := Real.mul_self_sqrt hζ0.le
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [V₁, potCov, Matrix.mul_apply, Fin.sum_univ_three] <;>
        field_simp [hζ0.ne'] <;>
        nlinarith [hsq]
    rw [heq]
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [potCov, Matrix.mul_apply, Fin.sum_univ_three]
    · rw [star_trivial]
      set D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, √ζ₀, √ζ₀]
      have hne : D.transpose.mulVec v ≠ 0 := by
        intro h0; apply hv; ext i; have hi := congrFun h0 i
        fin_cases i
        · simpa [D, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hi
        · simp [D, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hi
          exact hi.resolve_left (Real.sqrt_pos.2 hζ0).ne'
        · simp [D, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hi
          exact hi.resolve_left (Real.sqrt_pos.2 hζ0).ne'
      have hpos := (Matrix.posDef_iff_dotProduct_mulVec.1 (posDef_potCov hζ0 hζ1 hξ₀ hσ₀)).2 hne
      have heq_q : v ⬝ᵥ (D * potCov ζ₀ ξ₀ σ₀ * D.transpose) *ᵥ v =
          (D.transpose *ᵥ v) ⬝ᵥ potCov ζ₀ ξ₀ σ₀ *ᵥ (D.transpose *ᵥ v) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v D,
          ← Matrix.mulVec_transpose]
      rw [heq_q]; exact hpos
  have hZ_char : ∀ t : EuclideanSpace ℝ (Fin 3),
      charFun ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) V₁).map id) t =
        charFun ((gaussianReal 0 (ζ₀ * (1 - ζ₀)).toNNReal).map id) (t 0) *
        charFun ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gpdFisherInfoInv ξ₀ σ₀)).map id)
          !₂[t 1, t 2] := fun t => by
    rw [Measure.map_id, Measure.map_id, Measure.map_id,
      charFun_multivariateGaussian hV₁_pd.posSemidef,
      charFun_gaussianReal,
      charFun_multivariateGaussian (posDef_gpdFisherInfoInv hξ₀ hσ₀).posSemidef,
      ← Complex.exp_add]
    congr 1
    have hnn : 0 ≤ ζ₀ * (1 - ζ₀) := by nlinarith
    have hq : t.ofLp ⬝ᵥ V₁ *ᵥ t.ofLp =
        ζ₀ * (1 - ζ₀) * (t 0) ^ 2 +
          (!₂[t 1, t 2] : EuclideanSpace ℝ (Fin 2)).ofLp ⬝ᵥ gpdFisherInfoInv ξ₀ σ₀ *ᵥ
            (!₂[t 1, t 2] : EuclideanSpace ℝ (Fin 2)).ofLp := by
      simp [V₁, gpdFisherInfoInv, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two]
      ring
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Real.coe_toNNReal _ hnn,
      hq, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, inner_zero_right]
    ring
  set U : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
    !₂[A n ω, B (potCount I n ω) ω 0, B (potCount I n ω) ω 1]
  have hU_clt : TendstoInDistribution U atTop id (fun _ => P)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) V₁) :=
    tendstoInDistribution_indep_randomIndex hAm (measurable_potCount hIm) hBm hindAB
      hA_clt hB_clt hN_top aemeasurable_id hZ_char
  -- Step 4: Scale coordinates 1 & 2 by `√(n / Nₙ) → √(ζ₀⁻¹)` via Slutsky
  set L : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun v =>
    !₂[v 0, √(ζ₀⁻¹) * v 1, √(ζ₀⁻¹) * v 2]
  have hL_cont : Continuous L := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp (continuous_pi fun i => ?_)
    have hcoord : ∀ j : Fin 3, Continuous fun v : EuclideanSpace ℝ (Fin 3) => v j :=
      fun j => (continuous_apply j).comp (PiLp.continuous_ofLp 2 _)
    fin_cases i
    · exact hcoord 0
    · exact continuous_const.mul (hcoord 1)
    · exact continuous_const.mul (hcoord 2)
  have hLU_clt : TendstoInDistribution (fun n ω => L (U n ω)) atTop W (fun _ => P) P' := by
    have hcomp := hU_clt.continuous_comp hL_cont
    refine ⟨hcomp.forall_aemeasurable, hW.aemeasurable, ?_⟩
    have hmap_eq : P'.map W = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) V₁).map (L ∘ id) := by
      refine Measure.ext_of_charFun ?_
      ext t
      rw [hW.map_eq, Function.comp_id, charFun_multivariateGaussian (posDef_potCov hζ0 hζ1 hξ₀ hσ₀).posSemidef,
        charFun_apply, integral_map hL_cont.measurable.aemeasurable
          (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin 3) =>
            Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)).aestronglyMeasurable]
      set tL : EuclideanSpace ℝ (Fin 3) := !₂[t 0, √(ζ₀⁻¹) * t 1, √(ζ₀⁻¹) * t 2]
      have hinner : ∀ x : EuclideanSpace ℝ (Fin 3), ⟪L x, t⟫ = ⟪x, tL⟫ := fun x => by
        simp [L, tL, PiLp.inner_apply, Fin.sum_univ_three]; ring
      simp_rw [hinner]
      have hcf : ∫ x, Complex.exp ((⟪x, tL⟫ : ℝ) * Complex.I)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) V₁) =
          charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) V₁) tL := by
        rw [charFun_apply]
      rw [hcf, charFun_multivariateGaussian hV₁_pd.posSemidef]
      congr 1
      have hsq : √(ζ₀⁻¹) * √(ζ₀⁻¹) = ζ₀⁻¹ := Real.mul_self_sqrt (inv_nonneg.2 hζ0.le)
      have hq : t.ofLp ⬝ᵥ potCov ζ₀ ξ₀ σ₀ *ᵥ t.ofLp = tL.ofLp ⬝ᵥ V₁ *ᵥ tL.ofLp := by
        simp only [tL, potCov, V₁, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, Matrix.of_apply]
        linear_combination
          (-(1 + ξ₀) ^ 2 * t 1 ^ 2 + 2 * σ₀ * (1 + ξ₀) * t 1 * t 2 -
            2 * σ₀ ^ 2 * (1 + ξ₀) * t 2 ^ 2) * hsq
      simp only [inner_zero_right, Complex.ofReal_zero, hq]
    have hpm : (⟨P'.map W, inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) =
        ⟨(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) V₁).map (L ∘ id), inferInstance⟩ :=
      ProbabilityMeasure.toMeasure_injective hmap_eq
    rw [hpm]
    exact hcomp.tendsto
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
    √(n : ℝ) • !₂[potRate I n ω - ζ₀,
      (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1 - ξ₀,
      (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 - σ₀]
  have hTm : ∀ n, AEMeasurable (T n) P := fun n => by
    have hGN : AEMeasurable (fun ω => g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)) P :=
      aemeasurable_apply_randomIndex (measurable_potCount hIm n) fun m =>
        (hgm m).comp_aemeasurable (AEMeasurable.of_eval fun j => (hE j).aemeasurable)
    have h0 : AEMeasurable (fun ω => potRate I n ω - ζ₀) P :=
      (measurable_potRate hIm n).aemeasurable.sub_const ζ₀
    have h1 : AEMeasurable (fun ω => (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1 - ξ₀) P :=
      (measurable_fst.comp_aemeasurable hGN).sub_const ξ₀
    have h2 : AEMeasurable (fun ω => (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 - σ₀) P :=
      (measurable_snd.comp_aemeasurable hGN).sub_const σ₀
    exact ((WithLp.measurable_toLp 2 _).comp_aemeasurable
      (AEMeasurable.of_eval fun i => by fin_cases i <;> simpa using ‹_›)).const_smul (√(n : ℝ))
  -- Show `T - L ∘ U → 0` in probability
  set s : ℕ → Ω → ℝ := fun n ω =>
    if potCount I n ω = 0 then 0 else √((n : ℝ) / (potCount I n ω : ℝ))
  have hs_lim : TendstoInMeasure P s atTop (fun _ => √(ζ₀⁻¹)) := by
    have hcont : ContinuousAt (fun r : ℝ => √(r⁻¹)) ζ₀ :=
      (continuousAt_inv₀ hζ0.ne').sqrt
    have hrat := hrate_cons.comp_continuousAt hcont
    rw [tendstoInMeasure_iff_norm] at hrat ⊢
    intro ε hε
    have hsum : Tendsto (fun n => P {ω | ε ≤ ‖√((potRate I n ω)⁻¹) - √(ζ₀⁻¹)‖} +
        P {ω | potCount I n ω < 1}) atTop (𝓝 0) := by
      simpa using (hrat ε hε).add (hN_top 1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsub : {ω | ε ≤ ‖s n ω - √(ζ₀⁻¹)‖} ⊆
        {ω | ε ≤ ‖√((potRate I n ω)⁻¹) - √(ζ₀⁻¹)‖} ∪ {ω | potCount I n ω < 1} := by
      intro ω hω
      by_cases h0 : potCount I n ω = 0
      · right; simp [h0]
      · left
        have heq : s n ω = √((potRate I n ω)⁻¹) := by
          simp only [s, h0, ↓reduceIte, potRate, inv_div]
        simp only [mem_ofPred_eq] at hω ⊢
        rwa [heq] at hω
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have hdiff : TendstoInMeasure P (T - fun n ω => L (U n ω)) atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    have hη3 : 0 < η / 3 := ENNReal.div_pos hη.ne' (by norm_num)
    obtain ⟨M, hM⟩ := hU_clt.exists_measure_le_norm_le hη3
    set M' := max M 1
    have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h1 := ((tendstoInMeasure_iff_norm.1 hs_lim) (ε / M') (by positivity)).eventually (gt_mem_nhds hη3)
    have h2 := (hN_top 1).eventually (gt_mem_nhds hη3)
    filter_upwards [hM, h1, h2] with n hMn h1n h2n
    have hsub : {ω | ε ≤ ‖(T - fun n ω => L (U n ω)) n ω - 0‖} ⊆
        {ω | M ≤ ‖U n ω‖} ∪ ({ω | ε / M' ≤ ‖s n ω - √(ζ₀⁻¹)‖} ∪ {ω | potCount I n ω < 1}) := by
      intro ω hω
      by_contra hnot
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot
      obtain ⟨hUlt, hslt, hNge⟩ := hnot
      have hNne : potCount I n ω ≠ 0 := by omega
      have hNpos : (0 : ℝ) < (potCount I n ω : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNne
      have hsqN : √(potCount I n ω : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNpos).ne'
      have hTU : T n ω - L (U n ω) =
          !₂[0, (s n ω - √(ζ₀⁻¹)) * U n ω 1, (s n ω - √(ζ₀⁻¹)) * U n ω 2] := by
        ext i
        have hs_val : s n ω = √(n : ℝ) / √(potCount I n ω : ℝ) := by
          simp only [s, hNne, ↓reduceIte, Real.sqrt_div (Nat.cast_nonneg n)]
        fin_cases i
        · simp [T, L, U, A]
        · simp [T, L, U, B, hs_val]
          field_simp [hsqN]
        · simp [T, L, U, B, hs_val]
          field_simp [hsqN]
      have hnorm_le : ‖T n ω - L (U n ω)‖ ≤ |s n ω - √(ζ₀⁻¹)| * ‖U n ω‖ := by
        rw [hTU, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs,
          abs_zero, zero_pow two_ne_zero, zero_add, abs_mul, mul_pow]
        rw [← mul_add, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (abs_nonneg _)
        linarith [sq_nonneg |U n ω 0|]
      have hU_M' : ‖U n ω‖ < M' := lt_of_lt_of_le hUlt (le_max_left _ _)
      rw [Real.norm_eq_abs] at hslt
      have hlt : |s n ω - √(ζ₀⁻¹)| * ‖U n ω‖ < ε := by
        calc |s n ω - √(ζ₀⁻¹)| * ‖U n ω‖
            ≤ (ε / M') * ‖U n ω‖ := mul_le_mul_of_nonneg_right hslt.le (norm_nonneg _)
          _ < (ε / M') * M' := mul_lt_mul_of_pos_left hU_M' (by positivity)
          _ = ε := div_mul_cancel₀ ε hM'0.ne'
      simp only [mem_ofPred_eq, Pi.sub_apply, sub_zero] at hω
      linarith
    have h3 : η / 3 + (η / 3 + η / 3) = η := by
      have h3ne : (3 : ENNReal) ≠ 0 := by norm_num
      have h3t : (3 : ENNReal) ≠ ⊤ := by norm_num
      have heq : η / 3 + (η / 3 + η / 3) = 3 * (η / 3) := by ring
      rw [heq, mul_comm, ENNReal.div_mul_cancel h3ne h3t]
    refine (measure_mono hsub).trans ?_
    exact ((measure_union_le _ _).trans (add_le_add hMn
      ((measure_union_le _ _).trans (add_le_add h1n.le h2n.le)))).trans h3.le
  exact tendstoInDistribution_of_tendstoInMeasure_sub T W hLU_clt hdiff hTm

/-- The full asymptotic variance of the random-count POT return level `x̂_N` ([Coles 2001, §4.3.3,
eq. (4.15)]): `∇x_Nᵀ potCov(ζ, ξ, σ) ∇x_N`. -/
noncomputable def potReturnLevelVar (ζ ξ σ N : ℝ) : ℝ :=
  gpdReturnLevelGrad₃ ζ ξ σ N ⬝ᵥ potCov ζ ξ σ *ᵥ gpdReturnLevelGrad₃ ζ ξ σ N

/-- Coles' explicit variance decomposition (eq. 4.15):
`potReturnLevelVar ζ ξ σ N = ζ (1 - ζ) (σ N (N ζ)^{ξ - 1})² + ζ⁻¹ gpdReturnLevelVar ξ σ ζ N`. -/
theorem potReturnLevelVar_eq (ζ ξ σ N : ℝ) :
    potReturnLevelVar ζ ξ σ N =
      ζ * (1 - ζ) * (σ * N * (N * ζ) ^ (ξ - 1)) ^ 2 +
        ζ⁻¹ * gpdReturnLevelVar ξ σ ζ N := by
  simp only [potReturnLevelVar, gpdReturnLevelGrad₃, potCov, gpdReturnLevelVar, dotProduct,
    Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- `potReturnLevelVar ζ ξ σ N > 0` for `0 < ζ < 1`, `ξ > -1/2`, `σ > 0`, `N ζ > 1`. -/
theorem potReturnLevelVar_pos {ζ ξ σ N : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hξ : -1 / 2 < ξ)
    (hσ : 0 < σ) (hNζ : 1 < N * ζ) : 0 < potReturnLevelVar ζ ξ σ N := by
  rw [potReturnLevelVar_eq]
  have h1 : 0 ≤ ζ * (1 - ζ) * (σ * N * (N * ζ) ^ (ξ - 1)) ^ 2 := by
    have : 0 < ζ * (1 - ζ) := mul_pos hζ0 (sub_pos.2 hζ1)
    positivity
  have h2 : 0 < ζ⁻¹ * gpdReturnLevelVar ξ σ ζ N :=
    mul_pos (inv_pos.2 hζ0) (gpdReturnLevelVar_pos hξ hσ hNζ)
  linarith

/-- Continuity of `potReturnLevelVar` at `(ζ₀, ξ₀, σ₀)` for ALL `ξ₀ ∈ ℝ` (including `ξ₀ = 0`). -/
lemma continuousAt_potReturnLevelVar {ζ₀ ξ₀ σ₀ N : ℝ} (hζ₀ : 0 < ζ₀) (hNζ : 0 < N * ζ₀) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => potReturnLevelVar p.1 p.2.1 p.2.2 N) (ζ₀, ξ₀, σ₀) := by
  have heq : (fun p : ℝ × ℝ × ℝ => potReturnLevelVar p.1 p.2.1 p.2.2 N) =
      fun p => p.1 * (1 - p.1) * (p.2.2 * N * (N * p.1) ^ (p.2.1 - 1)) ^ 2 +
        p.1⁻¹ * gpdReturnLevelVar p.2.1 p.2.2 p.1 N :=
    funext fun p => potReturnLevelVar_eq p.1 p.2.1 p.2.2 N
  rw [heq]
  have hp1 : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) (ζ₀, ξ₀, σ₀) := by fun_prop
  have hp2 : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) (ζ₀, ξ₀, σ₀) := by fun_prop
  have hp3 : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (ζ₀, ξ₀, σ₀) := by fun_prop
  have hrpow : ContinuousAt (fun p : ℝ × ℝ × ℝ => (N * p.1) ^ (p.2.1 - 1)) (ζ₀, ξ₀, σ₀) :=
    ContinuousAt.rpow (continuousAt_const.mul hp1) (hp2.sub continuousAt_const) (Or.inl hNζ.ne')
  have hterm1 : ContinuousAt
      (fun p : ℝ × ℝ × ℝ => p.1 * (1 - p.1) * (p.2.2 * N * (N * p.1) ^ (p.2.1 - 1)) ^ 2)
      (ζ₀, ξ₀, σ₀) :=
    (hp1.mul (continuousAt_const.sub hp1)).mul (((hp3.mul continuousAt_const).mul hrpow).pow 2)
  have hlog : ContinuousAt (fun p : ℝ × ℝ × ℝ => Real.log (N * p.1)) (ζ₀, ξ₀, σ₀) :=
    (Real.continuousAt_log hNζ.ne').comp (f := fun p : ℝ × ℝ × ℝ => N * p.1) (x := (ζ₀, ξ₀, σ₀))
      (continuousAt_const.mul hp1)
  have hbc : ContinuousAt (fun p : ℝ × ℝ × ℝ => boxCox p.2.1 (N * p.1)) (ζ₀, ξ₀, σ₀) := by
    have hev : (fun p : ℝ × ℝ × ℝ => boxCox p.2.1 (N * p.1)) =ᶠ[𝓝 (ζ₀, ξ₀, σ₀)]
        fun p => Real.log (N * p.1) * expm1Div (p.2.1 * Real.log (N * p.1)) := by
      have hopen : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (ζ₀, ξ₀, σ₀), 0 < N * p.1 :=
        (continuousAt_const.mul hp1).eventually (lt_mem_nhds hNζ)
      filter_upwards [hopen] with p hp
      exact boxCox_eq_log_mul_expm1Div p.2.1 hp
    refine ContinuousAt.congr ?_ hev.symm
    exact hlog.mul ((hasDerivAt_expm1Div (ξ₀ * Real.log (N * ζ₀))).continuousAt.comp
      (f := fun p : ℝ × ℝ × ℝ => p.2.1 * Real.log (N * p.1)) (x := (ζ₀, ξ₀, σ₀)) (hp2.mul hlog))
  have hbcd : ContinuousAt (fun p : ℝ × ℝ × ℝ => boxCoxShapeDeriv p.2.1 (N * p.1)) (ζ₀, ξ₀, σ₀) := by
    have hev : (fun p : ℝ × ℝ × ℝ => boxCoxShapeDeriv p.2.1 (N * p.1)) =ᶠ[𝓝 (ζ₀, ξ₀, σ₀)]
        fun p => (Real.log (N * p.1)) ^ 2 * expm1DivDeriv (p.2.1 * Real.log (N * p.1)) := by
      have hopen : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (ζ₀, ξ₀, σ₀), 0 < N * p.1 :=
        (continuousAt_const.mul hp1).eventually (lt_mem_nhds hNζ)
      filter_upwards [hopen] with p hp
      exact boxCoxShapeDeriv_eq_log_sq_mul_expm1DivDeriv p.2.1 hp
    refine ContinuousAt.congr ?_ hev.symm
    exact (hlog.pow 2).mul (continuous_expm1DivDeriv.continuousAt.comp
      (f := fun p : ℝ × ℝ × ℝ => p.2.1 * Real.log (N * p.1)) (x := (ζ₀, ξ₀, σ₀)) (hp2.mul hlog))
  have hgpd : ContinuousAt (fun p : ℝ × ℝ × ℝ => gpdReturnLevelVar p.2.1 p.2.2 p.1 N) (ζ₀, ξ₀, σ₀) := by
    unfold gpdReturnLevelVar
    exact (continuousAt_const.add hp2).mul
      ((((continuousAt_const.add hp2).mul ((hp3.mul hbcd).pow 2)).sub
        ((((continuousAt_const.mul hp3).mul (hp3.mul hbcd)).mul hbc))).add
        ((continuousAt_const.mul (hp3.pow 2)).mul (hbc.pow 2)))
  exact hterm1.add ((hp1.inv₀ hζ₀.ne').mul hgpd)

/-- Measurability of `potReturnLevelVar` in `(ζ, ξ, σ)`. -/
lemma measurable_potReturnLevelVar (N : ℝ) :
    Measurable fun p : ℝ × ℝ × ℝ => potReturnLevelVar p.1 p.2.1 p.2.2 N := by
  have heq : (fun p : ℝ × ℝ × ℝ => potReturnLevelVar p.1 p.2.1 p.2.2 N) =
      fun p => p.1 * (1 - p.1) * (p.2.2 * N * (N * p.1) ^ (p.2.1 - 1)) ^ 2 +
        p.1⁻¹ * gpdReturnLevelVar p.2.1 p.2.2 p.1 N :=
    funext fun p => potReturnLevelVar_eq p.1 p.2.1 p.2.2 N
  rw [heq]
  have h1 : Measurable fun p : ℝ × ℝ × ℝ => p.1 := measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ × ℝ => p.2.1 := measurable_fst.comp measurable_snd
  have h3 : Measurable fun p : ℝ × ℝ × ℝ => p.2.2 := measurable_snd.comp measurable_snd
  have hbc : Measurable fun p : ℝ × ℝ × ℝ => boxCox p.2.1 (N * p.1) := by
    unfold boxCox
    exact Measurable.ite (measurableSet_eq_fun h2 measurable_const)
      ((measurable_const.mul h1).log)
      ((((measurable_const.mul h1).pow h2).sub_const 1).div h2)
  have hbcd : Measurable fun p : ℝ × ℝ × ℝ => boxCoxShapeDeriv p.2.1 (N * p.1) := by
    unfold boxCoxShapeDeriv
    exact Measurable.ite (measurableSet_eq_fun h2 measurable_const)
      ((((measurable_const.mul h1).log).pow_const 2).div_const 2)
      (((((measurable_const.mul h1).pow h2).mul ((measurable_const.mul h1).log)).div h2).sub
        ((((measurable_const.mul h1).pow h2).sub_const 1).div (h2.pow_const 2)))
  have hgpd : Measurable fun p : ℝ × ℝ × ℝ => gpdReturnLevelVar p.2.1 p.2.2 p.1 N := by
    unfold gpdReturnLevelVar
    exact (measurable_const.add h2).mul
      ((((measurable_const.add h2).mul ((h3.mul hbcd).pow_const 2)).sub
        (((measurable_const.mul h3).mul (h3.mul hbcd)).mul hbc)).add
        ((measurable_const.mul (h3.pow_const 2)).mul (hbc.pow_const 2)))
  exact ((h1.mul (measurable_const.sub h1)).mul
    (((h3.mul measurable_const).mul ((measurable_const.mul h1).pow (h2.sub_const 1))).pow_const 2)).add
    (h1.inv.mul hgpd)

/-- **Unconditional asymptotic normality of the random-count POT return level** ([Coles 2001, §4.3.3]),
across the entire regular range `ξ₀ > -1/2` (including `ξ₀ = 0`):
`√n (x̂_N - x_N) ⇒ N(0, potReturnLevelVar ζ₀ ξ₀ σ₀ N)`. -/
theorem tendstoInDistribution_potReturnLevelRandomCount
    {ζ₀ ξ₀ σ₀ u N : ℝ} (hζ0 : 0 < ζ₀) (hζ1 : ζ₀ < 1) (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hNζ : 0 < N * ζ₀)
    {I : ℕ → Ω → Bool} (hIm : ∀ i, Measurable (I i)) (hindI : iIndepFun I P)
    (hIprob : ∀ i, P {ω | I i ω = true} = ENNReal.ofReal ζ₀)
    {E : ℕ → Ω → ℝ} (hE : ∀ j, HasLaw (E j) (gpdMeasure ξ₀ σ₀) P) (hindE : iIndepFun E P)
    (hindIE : IndepFun (fun ω i => I i ω) (fun ω j => E j ω) P)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2)
    (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    {g : (m : ℕ) → (Fin m → ℝ) → ℝ × ℝ} (hgm : ∀ m, Measurable (g m))
    (hgK : ∀ m x, g m x ∈ K)
    (hgmax : ∀ m x, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K (g m x))
    {W : Ω' → ℝ} (hW : HasLaw W (gaussianReal 0 (potReturnLevelVar ζ₀ ξ₀ σ₀ N).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) *
        (gpdReturnLevel u (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
          (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 (potRate I n ω) N -
          gpdReturnLevel u ξ₀ σ₀ ζ₀ N))
      atTop W (fun _ => P) P' := by
  set θh : ℕ → Ω → ℝ × ℝ × ℝ := fun n ω =>
    (potRate I n ω,
     (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1,
     (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2)
  have hθm : ∀ n, AEMeasurable (θh n) P := fun n => by
    have hGN : AEMeasurable (fun ω => g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)) P :=
      aemeasurable_apply_randomIndex (measurable_potCount hIm n) fun m =>
        (hgm m).comp_aemeasurable (AEMeasurable.of_eval fun j => (hE j).aemeasurable)
    exact (measurable_potRate hIm n).aemeasurable.prodMk
      ((measurable_fst.comp_aemeasurable hGN).prodMk (measurable_snd.comp_aemeasurable hGN))
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (potCov ζ₀ ξ₀ σ₀))
      (multivariateGaussian 0 (potCov ζ₀ ξ₀ σ₀)) := HasLaw.id
  have hjoint := tendstoInDistribution_potRandomCountMLE hζ0 hζ1 hξ₀ hσ₀ hIm hindI hIprob
    hE hindE hindIE hK hKS hθ₀ hgm hgK hgmax hZ
  exact tendstoInDistribution_gpdReturnLevel₃_all hNζ hθm (posDef_potCov hζ0 hζ1 hξ₀ hσ₀).posSemidef
    hjoint hZ hW

/-- **Computable plug-in confidence interval for the random-count POT return level** ([Coles 2001,
§4.3.3]), across the entire regular range `ξ₀ > -1/2` (including `ξ₀ = 0`), with estimated
exceedance rate `ζ̂ₙ = Nₙ / n` and random exceedance count `Nₙ`. -/
theorem tendsto_measure_mem_potReturnLevelPlugInInterval
    {ζ₀ ξ₀ σ₀ u N : ℝ} (hζ0 : 0 < ζ₀) (hζ1 : ζ₀ < 1) (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hNζ : 1 < N * ζ₀)
    {I : ℕ → Ω → Bool} (hIm : ∀ i, Measurable (I i)) (hindI : iIndepFun I P)
    (hIprob : ∀ i, P {ω | I i ω = true} = ENNReal.ofReal ζ₀)
    {E : ℕ → Ω → ℝ} (hE : ∀ j, HasLaw (E j) (gpdMeasure ξ₀ σ₀) P) (hindE : iIndepFun E P)
    (hindIE : IndepFun (fun ω i => I i ω) (fun ω j => E j ω) P)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2)
    (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    {g : (m : ℕ) → (Fin m → ℝ) → ℝ × ℝ} (hgm : ∀ m, Measurable (g m))
    (hgK : ∀ m x, g m x ∈ K)
    (hgmax : ∀ m x, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K (g m x))
    (z : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gpdReturnLevel u ξ₀ σ₀ ζ₀ N ∈ Icc
      (gpdReturnLevel u (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
          (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 (potRate I n ω) N -
        z * √(potReturnLevelVar (potRate I n ω)
          (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
          (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 N) / √(n : ℝ))
      (gpdReturnLevel u (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
          (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 (potRate I n ω) N +
        z * √(potReturnLevelVar (potRate I n ω)
          (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
          (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 N) / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hvpos : 0 < potReturnLevelVar ζ₀ ξ₀ σ₀ N := potReturnLevelVar_pos hζ0 hζ1 hξ₀ hσ₀ hNζ
  have hNζ0 : 0 < N * ζ₀ := lt_trans zero_lt_one hNζ
  set θh : ℕ → Ω → ℝ × ℝ × ℝ := fun n ω =>
    (potRate I n ω,
     (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1,
     (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2)
  have hθm : ∀ n, AEMeasurable (θh n) P := fun n => by
    have hGN : AEMeasurable (fun ω => g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)) P :=
      aemeasurable_apply_randomIndex (measurable_potCount hIm n) fun m =>
        (hgm m).comp_aemeasurable (AEMeasurable.of_eval fun j => (hE j).aemeasurable)
    exact (measurable_potRate hIm n).aemeasurable.prodMk
      ((measurable_fst.comp_aemeasurable hGN).prodMk (measurable_snd.comp_aemeasurable hGN))
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (potCov ζ₀ ξ₀ σ₀))
      (multivariateGaussian 0 (potCov ζ₀ ξ₀ σ₀)) := HasLaw.id
  have hjoint := tendstoInDistribution_potRandomCountMLE hζ0 hζ1 hξ₀ hσ₀ hIm hindI hIprob
    hE hindE hindIE hK hKS hθ₀ hgm hgK hgmax hZ
  have hθcons : TendstoInMeasure P θh atTop (fun _ => (ζ₀, ξ₀, σ₀)) := by
    have h0 := TendstoInDistribution.tendstoInMeasure_of_smul (r := fun n : ℕ => √(n : ℝ))
      hjoint tendsto_sqrt_natCast_atTop
    have hcont : Continuous fun v : EuclideanSpace ℝ (Fin 3) => (v 0 + ζ₀, v 1 + ξ₀, v 2 + σ₀) := by
      have hc : ∀ i : Fin 3, Continuous fun v : EuclideanSpace ℝ (Fin 3) => v i :=
        fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
      exact ((hc 0).add continuous_const).prodMk
        (((hc 1).add continuous_const).prodMk ((hc 2).add continuous_const))
    have hcomp := h0.comp_continuousAt hcont.continuousAt
    simpa [θh] using hcomp
  have hW_rl : HasLaw id (gaussianReal 0 (potReturnLevelVar ζ₀ ξ₀ σ₀ N).toNNReal)
      (gaussianReal 0 (potReturnLevelVar ζ₀ ξ₀ σ₀ N).toNNReal) := HasLaw.id
  have hrl := tendstoInDistribution_potReturnLevelRandomCount (u := u) hζ0 hζ1 hξ₀ hσ₀ hNζ0
    hIm hindI hIprob hE hindE hindIE hK hKS hθ₀ hgm hgK hgmax hW_rl
  have hS : TendstoInMeasure P
      (fun (n : ℕ) ω => √(potReturnLevelVar (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 N))
      atTop (fun _ => √(potReturnLevelVar ζ₀ ξ₀ σ₀ N)) :=
    hθcons.comp_continuousAt (continuousAt_potReturnLevelVar hζ0 hNζ0).sqrt
  have hSm : ∀ n, AEMeasurable
      (fun ω => √(potReturnLevelVar (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 N)) P := fun n =>
    ((measurable_potReturnLevelVar N).comp_aemeasurable (hθm n)).sqrt
  exact hrl.tendsto_measure_mem_waldInterval_gaussian (s := √(potReturnLevelVar ζ₀ ξ₀ σ₀ N))
    (sqrt_pos.2 hvpos) z (by rw [Real.sq_sqrt hvpos.le]; exact hW_rl)
    ((eventually_ge_atTop 1).mono fun n hn => Real.sqrt_pos.2 (by exact_mod_cast hn)) hS hSm

/-- **Unconditional existence of a measurable GPD MLE and asymptotically exact plug-in POT
return-level confidence interval with random exceedance count** across all `ξ₀ > -1/2`
(including `ξ₀ = 0`). -/
theorem exists_potReturnLevelPlugInInterval_tendsto
    {ζ₀ ξ₀ σ₀ u N : ℝ} (hζ0 : 0 < ζ₀) (hζ1 : ζ₀ < 1) (hξ₀ : -1 / 2 < ξ₀) (hσ₀ : 0 < σ₀)
    (hNζ : 1 < N * ζ₀)
    {I : ℕ → Ω → Bool} (hIm : ∀ i, Measurable (I i)) (hindI : iIndepFun I P)
    (hIprob : ∀ i, P {ω | I i ω = true} = ENNReal.ofReal ζ₀)
    {E : ℕ → Ω → ℝ} (hE : ∀ j, HasLaw (E j) (gpdMeasure ξ₀ σ₀) P) (hindE : iIndepFun E P)
    (hindIE : IndepFun (fun ω i => I i ω) (fun ω j => E j ω) P)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2)
    (hθ₀ : (ξ₀, σ₀) ∈ interior K) (z : ℝ) :
    ∃ g : (m : ℕ) → (Fin m → ℝ) → ℝ × ℝ, (∀ m, Measurable (g m)) ∧
      (∀ m x, g m x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K (g m x)) ∧
      Tendsto (fun n : ℕ => P {ω | gpdReturnLevel u ξ₀ σ₀ ζ₀ N ∈ Icc
        (gpdReturnLevel u (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
            (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 (potRate I n ω) N -
          z * √(potReturnLevelVar (potRate I n ω)
            (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
            (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 N) / √(n : ℝ))
        (gpdReturnLevel u (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
            (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 (potRate I n ω) N +
          z * √(potReturnLevelVar (potRate I n ω)
            (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).1
            (g (potCount I n ω) (fun j : Fin (potCount I n ω) => E j ω)).2 N) / √(n : ℝ))})
        atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  choose g hgm hg using exists_measurable_gpdMLE hK hKS ⟨_, interior_subset hθ₀⟩
  exact ⟨g, hgm, hg, tendsto_measure_mem_potReturnLevelPlugInInterval hζ0 hζ1 hξ₀ hσ₀ hNζ
    hIm hindI hIprob hE hindE hindIE hK hKS hθ₀ hgm (fun m x => (hg m x).1) (fun m x => (hg m x).2) z⟩

end POTRandomCount

end ExtremeValueTheory
