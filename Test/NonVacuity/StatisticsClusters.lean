import ExtremeValueTheory

/-!
# Non-vacuity: extremal-index estimators and the tail empirical process

* Blocks and runs estimators: an iid standard exponential sequence (extremal index `θ = 1`), with
  thresholds `uₙ = log sₙ` (`sₙ = ⌊√n⌋`, so `pₙ = P(X₀ > uₙ) = 1 / sₙ`) and block / run lengths
  `rₙ = ⌊√sₙ⌋ ≈ n^{1/4}`. All hypotheses (stationarity, `0`-dependence, `n pₙ → ∞`, `rₙ / n → 0`,
  convergence of the population block cluster ratio and runs ratio to `1`, and for the general
  versions the cluster and mixing conditions) are discharged.
* Intervals estimator: iid inter-exceedance times with the Ferro–Segers law of `θ = 1/2`; the
  moment hypotheses are discharged by the strong law of large numbers.
* Tail empirical process: iid uniform sample, `kₙ = ⌊√n⌋`, and a Brownian limit in `D[0,1]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace ExtremeValueTheory.Test.NonVacuity.Clusters

/-! ### Deterministic sequences -/

theorem tendsto_sqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop.2 fun b => (eventually_ge_atTop (b * b)).mono fun _ hn => Nat.le_sqrt.2 hn

/-- `sₙ = ⌊√n⌋`. -/
def s (n : ℕ) : ℕ := Nat.sqrt n

/-- The block / run length `rₙ = ⌊√sₙ⌋`. -/
def r (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n)

/-- The threshold `uₙ = log sₙ`. -/
noncomputable def u (n : ℕ) : ℝ := Real.log (s n)

theorem tendsto_s : Tendsto s atTop atTop := tendsto_sqrt

theorem tendsto_r : Tendsto r atTop atTop := tendsto_sqrt.comp tendsto_sqrt

theorem tendsto_inv_s : Tendsto (fun n => ((s n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_s)

theorem s_pos : ∀ᶠ n in atTop, 0 < s n := tendsto_s.eventually_gt_atTop 0

theorem r_pos : ∀ᶠ n in atTop, 0 < r n := tendsto_r.eventually_gt_atTop 0

theorem s_mul_le (n : ℕ) : ((s n : ℝ)) * s n ≤ n := by
  exact_mod_cast Nat.sqrt_le n

theorem r_mul_le (n : ℕ) : ((r n : ℝ)) * r n ≤ s n := by
  exact_mod_cast Nat.sqrt_le (Nat.sqrt n)

theorem r_le (n : ℕ) : (r n : ℝ) ≤ s n := by exact_mod_cast Nat.sqrt_le_self _

/-- `n pₙ = n / sₙ → ∞`. -/
theorem tendsto_n_mul_inv_s : Tendsto (fun n : ℕ => (n : ℝ) * ((s n : ℝ))⁻¹) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_natCast_atTop_atTop.comp tendsto_s)
  filter_upwards [s_pos] with n hn
  have hs : (0 : ℝ) < s n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  rw [le_mul_inv_iff₀ hs]
  exact s_mul_le n

/-- `rₙ / n → 0`. -/
theorem tendsto_r_div : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ tendsto_inv_s
  filter_upwards [s_pos] with n hn
  have hs : (0 : ℝ) < s n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := lt_of_lt_of_le (mul_pos hs hs) (s_mul_le n)
  rw [div_le_iff₀ hn']
  calc (r n : ℝ) ≤ s n := r_le n
    _ = (s n : ℝ)⁻¹ * (s n * s n) := by field_simp
    _ ≤ (s n : ℝ)⁻¹ * n := by gcongr; exact s_mul_le n

/-- `rₙ pₙ = rₙ / sₙ → 0`. -/
theorem tendsto_r_mul_inv_s : Tendsto (fun n => (r n : ℝ) * ((s n : ℝ))⁻¹) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_r))
  filter_upwards [r_pos] with n hn
  have hr : (0 : ℝ) < r n := by exact_mod_cast hn
  have hs : (0 : ℝ) < s n := lt_of_lt_of_le (mul_pos hr hr) (r_mul_le n)
  simp only [Function.comp_apply]
  rw [mul_inv_le_iff₀ hs]
  calc (r n : ℝ) = (r n : ℝ)⁻¹ * (r n * r n) := by field_simp
    _ ≤ (r n : ℝ)⁻¹ * s n := by gcongr; exact r_mul_le n

/-- Bernoulli-type bounds: `1 / (1 + q p) ≤ (1 - (1 - p)^q) / (q p) ≤ 1`. -/
theorem block_ratio_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : ℕ} (hqp : 0 < q * p) :
    1 / (1 + q * p) ≤ (1 - (1 - p) ^ q) / (q * p) ∧ (1 - (1 - p) ^ q) / (q * p) ≤ 1 := by
  have hup : 1 + q * (-p) ≤ (1 + -p) ^ q := one_add_mul_le_pow (by linarith) q
  have hlow : 1 + q * p ≤ (1 + p) ^ q := one_add_mul_le_pow (by linarith) q
  have hprod : (1 - p) ^ q * (1 + p) ^ q ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hA : 0 ≤ (1 - p) ^ q := pow_nonneg (by linarith) q
  constructor
  · rw [div_le_div_iff₀ (by linarith) hqp]
    nlinarith
  · rw [div_le_one hqp]
    simp only [← sub_eq_add_neg] at hup
    linarith

/-! ### An iid exponential sequence -/

section Iid

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
theorem isMDependent_zero (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) :
    IsMDependent X 0 P := by
  intro t
  exact indep_iSup_of_disjoint (fun i => (hX i).comap_le) hind.iIndep
    (S := {i : ℕ | i ≤ t}) (T := {i : ℕ | t + 0 + 1 ≤ i})
    (Set.disjoint_left.2 fun i (h1 : i ≤ t) (h2 : t + 0 + 1 ≤ i) => by omega)

theorem measureReal_le_eq (hX : ∀ i, Measurable (X i)) (v : ℝ) :
    P.real {ω | X 0 ω ≤ v} = 1 - P.real {ω | v < X 0 ω} := by
  rw [← probReal_compl_eq_one_sub (measurableSet_lt measurable_const (hX 0))]
  congr 1
  ext ω; simp

theorem measureReal_blockEvent_iid (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (q : ℕ) (v : ℝ) :
    P.real (blockEvent X q 0 v) = 1 - (1 - P.real {ω | v < X 0 ω}) ^ q := by
  rw [blockEvent, probReal_compl_eq_one_sub (measurableSet_maxLE hX _ v),
    measureReal_maxLE_of_iIndepFun hind hid, measureReal_le_eq hX]
  simp

theorem measureReal_runEvent_iid (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (q : ℕ) (v : ℝ) :
    P.real (runEvent X q 0 v) = P.real {ω | v < X 0 ω} * (1 - P.real {ω | v < X 0 ω}) ^ q := by
  set f : ℕ → Set ℝ := fun t => if t = 0 then Ioi v else Iic v
  have e : runEvent X q 0 v = ⋂ t ∈ range (q + 1), X t ⁻¹' f t := by
    ext ω
    simp only [runEvent, maxLE, Set.mem_inter_iff, Finset.mem_Ioc,
      Set.mem_iInter, Finset.mem_range, Set.mem_preimage, f]
    constructor
    · rintro ⟨h0, h⟩ t ht
      split_ifs with h'
      · subst h'; exact h0
      · exact h t ⟨by omega, by omega⟩
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun t ht => ?_⟩
      have := h t (by omega)
      simpa [show t ≠ 0 by omega] using this
  have hmeas : ∀ t ∈ range (q + 1), MeasurableSet (f t) := fun t _ => by
    simp only [f]; split_ifs <;> measurability
  rw [e, measureReal_def, hind.measure_inter_preimage_eq_mul _ hmeas, ENNReal.toReal_prod,
    Finset.prod_range_succ']
  have h1 : ∀ i ∈ range q, (P (X (i + 1) ⁻¹' f (i + 1))).toReal = 1 - P.real {ω | v < X 0 ω} := by
    intro i _
    simp only [f, ite_eq_right_iff.2 (fun h => absurd h (Nat.succ_ne_zero i))]
    rw [(hid (i + 1)).measure_mem_eq measurableSet_Iic, ← measureReal_le_eq hX]
    rfl
  rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_range, mul_comm]
  simp only [f, ↓reduceIte]
  rfl

end Iid

/-- The tail of the standard exponential law at `uₙ = log sₙ` is `1 / sₙ`. -/
theorem measureReal_lt_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (expMeasure 1) P) {n : ℕ} (hn : 0 < s n) :
    P.real {ω | u n < X ω} = ((s n : ℝ))⁻¹ := by
  have hs : (1 : ℝ) ≤ s n := by exact_mod_cast hn
  have hu : 0 ≤ u n := Real.log_nonneg hs
  have : {ω | u n < X ω} = X ⁻¹' Ioi (u n) := rfl
  rw [this, measureReal_def, ← Measure.map_apply_of_aemeasurable hX.aemeasurable measurableSet_Ioi,
    hX.map_eq, expMeasure_Ioi hu, ENNReal.toReal_ofReal (Real.exp_pos _).le, u, Real.exp_neg,
    Real.exp_log (by linarith)]

/-- The iid standard exponential sequence together with every property used below. -/
theorem exists_iid_exp :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) (expMeasure 1) P) ∧
      iIndepFun X P ∧ (∀ i, IdentDistrib (X i) (X 0) P P) := by
  obtain ⟨Ω, _, P, X, hXm, hlaw, hind, hP⟩ := exists_iid ℕ (expMeasure 1)
  exact ⟨Ω, _, P, X, hP, hXm, hlaw, hind, fun i => ⟨(hlaw i).aemeasurable,
    (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩⟩

section Targets

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, HasLaw (X i) (expMeasure 1) P)
  (hind : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
include hX hlaw hind hid

omit [IsProbabilityMeasure P] hX hind hid in
theorem tendsto_hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop := by
  refine tendsto_n_mul_inv_s.congr' ?_
  filter_upwards [s_pos] with n hn
  rw [measureReal_lt_exp (hlaw 0) hn]

/-- The population block cluster ratio tends to `θ = 1`. -/
theorem tendsto_blockRatio :
    Tendsto (fun n => P.real (blockEvent X (r n) 0 (u n)) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n => 1 / (1 + (r n : ℝ) * ((s n : ℝ))⁻¹)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add tendsto_r_mul_inv_s).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  all_goals
    filter_upwards [s_pos, r_pos] with n hn hrn
    have hs : (0 : ℝ) < s n := by exact_mod_cast hn
    have hr : (0 : ℝ) < r n := by exact_mod_cast hrn
    have hp1 : ((s n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
    have hb := block_ratio_bounds (inv_nonneg.2 hs.le) hp1 (q := r n) (by positivity)
    rw [measureReal_blockEvent_iid hX hind hid, measureReal_lt_exp (hlaw 0) hn]
  · exact hb.1
  · exact hb.2

/-- The population runs ratio tends to `θ = 1`. -/
theorem tendsto_runsRatio :
    Tendsto (fun n => P.real (runEvent X (r n) 0 (u n)) / P.real {ω | u n < X 0 ω})
      atTop (𝓝 1) := by
  have hlow : Tendsto (fun n => 1 - (r n : ℝ) * ((s n : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub tendsto_r_mul_inv_s
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  all_goals
    filter_upwards [s_pos] with n hn
    have hs : (0 : ℝ) < s n := by exact_mod_cast hn
    have hp1 : ((s n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
    have hp0 : 0 ≤ ((s n : ℝ))⁻¹ := inv_nonneg.2 hs.le
    rw [measureReal_runEvent_iid hX hind hid, measureReal_lt_exp (hlaw 0) hn,
      mul_div_cancel_left₀ _ (inv_pos.2 hs).ne']
  · have := one_add_mul_le_pow (a := -((s n : ℝ))⁻¹) (by linarith) (r n)
    simp only [← sub_eq_add_neg, mul_neg] at this
    linarith
  · exact pow_le_one₀ (by linarith) (by linarith)

end Targets

/-! ### The tests -/

/-- Exercises `tendstoInMeasure_blocksEstimator_of_isMDependent`: iid `Exp(1)` sequence
(`0`-dependent, stationary), `uₙ = log ⌊√n⌋`, `rₙ = ⌊n^{1/4}⌋`; the blocks estimator tends to
`θ = 1`. All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInMeasure_blocksEstimator_of_isMDependent :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, HasLaw (X i) (expMeasure 1) P) ∧ iIndepFun X P ∧
      TendstoInMeasure P (fun n => blocksEstimator X n (r n) (u n)) atTop (fun _ => 1) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hlaw, hind, hid⟩ := exists_iid_exp
  refine ⟨Ω, _, P, X, hP, hlaw, hind, ?_⟩
  exact tendstoInMeasure_blocksEstimator_of_isMDependent hXm (isStationary_of_iIndepFun hXm hind hid)
    (isMDependent_zero hXm hind) tendsto_r tendsto_r_div (tendsto_hk hlaw)
    (tendsto_blockRatio hXm hlaw hind hid)

/-- Exercises `tendstoInMeasure_runsEstimator_of_isMDependent`: same sequence, thresholds and run
lengths; the runs estimator tends to `θ = 1`. All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInMeasure_runsEstimator_of_isMDependent :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, HasLaw (X i) (expMeasure 1) P) ∧ iIndepFun X P ∧
      TendstoInMeasure P (fun n => runsEstimator X n (r n) (u n)) atTop (fun _ => 1) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hlaw, hind, hid⟩ := exists_iid_exp
  refine ⟨Ω, _, P, X, hP, hlaw, hind, ?_⟩
  exact tendstoInMeasure_runsEstimator_of_isMDependent hXm (isStationary_of_iIndepFun hXm hind hid)
    (isMDependent_zero hXm hind) tendsto_r tendsto_r_div (tendsto_hk hlaw)
    (tendsto_runsRatio hXm hlaw hind hid)

/-- Exercises the general `tendstoInMeasure_blocksEstimator` (cluster and mixing conditions
stated with strong mixing coefficients): same iid sequence, cluster window `sₙ = 0`. All
hypotheses discharged (the mixing coefficients vanish at positive lags by `0`-dependence). -/
theorem test_nonvacuous_tendstoInMeasure_blocksEstimator :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, HasLaw (X i) (expMeasure 1) P) ∧ iIndepFun X P ∧
      TendstoInMeasure P (fun n => blocksEstimator X n (r n) (u n)) atTop (fun _ => 1) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hlaw, hind, hid⟩ := exists_iid_exp
  refine ⟨Ω, _, P, X, hP, hlaw, hind, ?_⟩
  have hm := isMDependent_zero hXm hind
  refine tendstoInMeasure_blocksEstimator hXm (isStationary_of_iIndepFun hXm hind hid) r_pos
    tendsto_r_div (tendsto_hk hlaw) (tendsto_blockRatio hXm hlaw hind hid)
    (fun _ => 0) ?_ (tendsto_sum_alphaMixing_div_of_isMDependent hm
      (Eventually.of_forall fun _ => le_rfl) _) ?_
  · simp
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [hm.alphaMixing_eq_zero (by omega), ENNReal.toReal_zero, zero_div]

/-- Exercises the general `tendstoInMeasure_runsEstimator`: same iid sequence, cluster window
`sₙ = 0` (the cluster condition over `[1, rₙ]` from `tendsto_sum_measureReal_lt_and_lt_div_of_isMDependent`).
All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInMeasure_runsEstimator :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, HasLaw (X i) (expMeasure 1) P) ∧ iIndepFun X P ∧
      TendstoInMeasure P (fun n => runsEstimator X n (r n) (u n)) atTop (fun _ => 1) := by
  obtain ⟨Ω, _, P, X, hP, hXm, hlaw, hind, hid⟩ := exists_iid_exp
  refine ⟨Ω, _, P, X, hP, hlaw, hind, ?_⟩
  have hm := isMDependent_zero hXm hind
  have hs := isStationary_of_iIndepFun hXm hind hid
  exact tendstoInMeasure_runsEstimator hXm hs tendsto_r_div (tendsto_hk hlaw)
    (tendsto_runsRatio hXm hlaw hind hid) (fun _ => 0)
    (tendsto_sum_measureReal_lt_and_lt_div_of_isMDependent hXm hs hm
      (tendsto_hk hlaw) (by simpa using tendsto_r_div))
    (tendsto_sum_alphaMixing_div_of_isMDependent hm (Eventually.of_forall fun _ => le_rfl) _)

/-! ### Intervals estimator -/

/-- Exercises `tendstoInMeasure_intervalsEstimator₁` (Ferro–Segers): `mₙ = n` iid
inter-exceedance times with the Ferro–Segers law of `θ = 1/2`, `cₙ = 1`. The two moment
hypotheses are discharged by the strong law of large numbers (Mathlib `strong_law_ae`); the
estimator tends to `1/2`. All hypotheses discharged. -/
theorem test_nonvacuous_tendstoInMeasure_intervalsEstimator₁ :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (T : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, HasLaw (T i) (ferroSegersLaw (1 / 2)) P) ∧
      iIndepFun T P ∧
      TendstoInMeasure P (fun n ω => intervalsEstimator₁ (fun i : Fin n => T i ω)) atTop
        (fun _ => 1 / 2) := by
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  have := isProbabilityMeasure_ferroSegersLaw hθ (by norm_num)
  obtain ⟨Ω, _, P, T, hTm, hlaw, hind, hP⟩ := exists_iid ℕ (ferroSegersLaw (1 / 2))
  refine ⟨Ω, _, P, T, hP, hlaw, hind, ?_⟩
  have hid : ∀ i, IdentDistrib (T i) (T 0) P P := fun i =>
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
  -- integrability from the nonzero moments
  have hint1 : Integrable (fun x : ℝ => x) (ferroSegersLaw (1 / 2)) :=
    Integrable.of_integral_ne_zero (by rw [integral_id_ferroSegersLaw hθ]; norm_num)
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (ferroSegersLaw (1 / 2)) :=
    Integrable.of_integral_ne_zero (by rw [integral_sq_ferroSegersLaw hθ]; norm_num)
  -- the SLLN for `T` and `T²`
  have hslln : ∀ (g : ℝ → ℝ), Measurable g → Integrable g (ferroSegersLaw (1 / 2)) →
      TendstoInMeasure P (fun n ω => (∑ i : Fin n, g (T i ω)) / n) atTop
        (fun _ => ∫ x, g x ∂(ferroSegersLaw (1 / 2))) := by
    intro g hg hgi
    have hY : ∀ i, Measurable (fun ω => g (T i ω)) := fun i => hg.comp (hTm i)
    have hae := strong_law_ae (fun i ω => g (T i ω))
      ((hlaw 0).integrable_comp hgi)
      (fun i j hij => (hind.indepFun hij).comp hg hg)
      (fun i => (hid i).comp hg)
    have hE : ∫ ω, g (T 0 ω) ∂P = ∫ x, g x ∂(ferroSegersLaw (1 / 2)) :=
      (hlaw 0).integral_comp hg.aestronglyMeasurable
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · exact ((Finset.measurable_sum Finset.univ fun (i : Fin n) _ => hY i).div_const _).aestronglyMeasurable
    · filter_upwards [hae] with ω hω
      rw [← hE]
      refine hω.congr fun n => ?_
      rw [smul_eq_mul, Fin.sum_univ_eq_sum_range (fun i => g (T i ω)) n, inv_mul_eq_div]
  have h1 := hslln (fun x => x) measurable_id hint1
  have h2 := hslln (fun x => x ^ 2) (measurable_id.pow_const 2) hint2
  refine tendstoInMeasure_intervalsEstimator₁ (m := fun n => n) (c := fun _ => 1)
    (eventually_gt_atTop 0) (Eventually.of_forall fun _ => one_ne_zero) hθ ?_ ?_
  · simpa using h1
  · simpa using h2

/-! ### Tail empirical process -/

instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Exercises `tendstoInDistribution_tailEmpiricalPath` (de Haan–Ferreira Thm 5.1.4): iid uniform
sample, `kₙ = ⌊√n⌋`; the limit `B = id` on `D[0,1]` under the law `μ` with Brownian
finite-dimensional distributions supplied by `exists_tendsto_tailEmpiricalPath` (which has the
same hypotheses; Brownian motion in `D[0,1]` is thereby constructed in the library). All
hypotheses discharged. -/
theorem test_nonvacuous_tendstoInDistribution_tailEmpiricalPath :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (U : ℕ → Ω → ℝ) (μ : ProbabilityMeasure (SkorokhodSpace ℝ)),
      (∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) ∧ iIndepFun U P ∧
      TendstoInDistribution (fun n => tailEmpiricalPath U n (Nat.sqrt n)) atTop
        (id : SkorokhodSpace ℝ → SkorokhodSpace ℝ) (fun _ => P) (μ : Measure (SkorokhodSpace ℝ)) := by
  obtain ⟨Ω, _, P, U, hUm, hlaw, hind, hP⟩ := exists_iid ℕ (volume.restrict (Set.Icc (0 : ℝ) 1))
  have hlaw' : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1) := fun i => (hlaw i).map_eq
  have hk : Tendsto Nat.sqrt atTop atTop := tendsto_sqrt
  have hkn : Tendsto (fun n => (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
    simpa [s, r] using
      (show Tendsto (fun n => (s n : ℝ) / n) atTop (𝓝 0) from by
        refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ tendsto_inv_s
        filter_upwards [s_pos] with n hn
        have hs : (0 : ℝ) < s n := by exact_mod_cast hn
        have hn' : (0 : ℝ) < n := lt_of_lt_of_le (mul_pos hs hs) (s_mul_le n)
        rw [div_le_iff₀ hn']
        calc (s n : ℝ) = (s n : ℝ)⁻¹ * (s n * s n) := by field_simp
          _ ≤ (s n : ℝ)⁻¹ * n := by gcongr; exact s_mul_le n)
  obtain ⟨μ, -, hμ⟩ := exists_tendsto_tailEmpiricalPath hUm hind hlaw' hk hkn
  refine ⟨Ω, _, P, hP, U, μ, hlaw', hind, ?_⟩
  exact tendstoInDistribution_tailEmpiricalPath hUm hind hlaw' hk hkn measurable_id
    fun J => by rw [Measure.map_id]; exact hμ (fun t : J => (t : unitInterval))

end ExtremeValueTheory.Test.NonVacuity.Clusters
