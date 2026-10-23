import ExtremeValueTheory

/-!
# Non-vacuity tests: dependence

Each test builds a concrete stationary sequence satisfying *all* hypotheses of a headline theorem
on extremes of dependent sequences and applies the theorem to it.

The concrete object underlying almost every test is **iid Pareto(`α`) noise on `ℤ`**, realized
canonically: `Ω = ℤ → ℝ` with the product law `⊗_t Pareto(1, α)` (`Measure.infinitePi`) and
`Z t ω = |ω t|`. The absolute value makes `Z ≥ 0` hold *pointwise* (several theorems assume
`∀ t ω, 0 ≤ Z t ω` rather than almost surely), without changing the law. From `Z` we build the
iid sequence itself, the moving maximum `max(Z_t, Z_{t+1})`, finite and infinite moving averages,
AR(1), and the echo processes.
-/

open MeasureTheory ProbabilityTheory Filter Topology ExtremeValueTheory
open scoped ENNReal

namespace NonVacuity.Dependence

/-! ### The concrete iid Pareto noise -/

/-- The product law `⊗_{t ∈ ℤ} Pareto(1, α)` on `ℤ → ℝ`. -/
private noncomputable def P (α : ℝ) : Measure (ℤ → ℝ) :=
  Measure.infinitePi fun _ : ℤ => paretoMeasure 1 α

/-- The coordinates, made pointwise nonnegative: `Z t ω = |ω t|`. -/
private def Z (t : ℤ) (ω : ℤ → ℝ) : ℝ := |ω t|

variable {α : ℝ}

/-- Test-specific: `P α` is a probability measure. -/
private theorem isProbabilityMeasure_P (hα : 0 < α) : IsProbabilityMeasure (P α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  unfold P; infer_instance

/-- Test-specific: The noise coordinates are measurable. -/
private theorem measurable_Z (t : ℤ) : Measurable (Z t) :=
  continuous_abs.measurable.comp (measurable_pi_apply t)

/-- Test-specific: The noise is pointwise nonnegative. -/
private theorem Z_nonneg (t : ℤ) (ω : ℤ → ℝ) : 0 ≤ Z t ω := abs_nonneg _

/-- Test-specific: The noise coordinates are independent. -/
private theorem iIndepFun_Z (hα : 0 < α) : iIndepFun Z (P α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  exact iIndepFun_infinitePi (X := fun _ (x : ℝ) => |x|) fun _ => continuous_abs.measurable

/-- Test-specific: Each noise coordinate is Pareto(`1`, `α`). -/
private theorem map_Z (hα : 0 < α) (t : ℤ) : (P α).map (Z t) = paretoMeasure 1 α := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have e : Z t = (fun x : ℝ => |x|) ∘ fun ω : ℤ → ℝ => ω t := rfl
  rw [e, ← Measure.map_map (g := fun x : ℝ => |x|) (f := fun ω : ℤ → ℝ => ω t)
    continuous_abs.measurable (measurable_pi_apply t), P,
    Measure.infinitePi_map_eval]
  have hae : (fun x : ℝ => |x|) =ᵐ[paretoMeasure 1 α] id := by
    filter_upwards [ae_one_lt_paretoMeasure (α := α)] with r hr
    exact abs_of_pos (one_pos.trans hr)
  rw [Measure.map_congr hae, Measure.map_id]

/-- Test-specific: The noise coordinates are identically distributed. -/
private theorem identDistrib_Z (hα : 0 < α) (t : ℤ) : IdentDistrib (Z t) (Z 0) (P α) (P α) :=
  ⟨(measurable_Z t).aemeasurable, (measurable_Z 0).aemeasurable, by rw [map_Z hα, map_Z hα]⟩

/-- `P(Z_t > x) = Pareto(1, α)(x, ∞)`. -/
private theorem measureReal_lt_Z (hα : 0 < α) (t : ℤ) (x : ℝ) :
    (P α).real {ω | x < Z t ω} = tail (paretoMeasure 1 α) x := by
  have := isProbabilityMeasure_P hα
  rw [tail, ← map_Z hα t, map_measureReal_apply (measurable_Z t) measurableSet_Ioi]
  rfl

/-- The tail of the noise is regularly varying with index `-α`. -/
private theorem isRegularlyVarying_Z (hα : 0 < α) :
    IsRegularlyVarying (fun x => (P α).real {ω | x < Z 0 ω}) (-α) := by
  simp_rw [measureReal_lt_Z hα]
  exact isRegularlyVarying_tail_paretoMeasure one_pos hα

/-! ### The `ℕ`-indexed iid sequence -/

/-- The `ℕ`-indexed iid Pareto sequence `X n = Z n`. -/
private def X (n : ℕ) : (ℤ → ℝ) → ℝ := Z n

/-- Test-specific: The `ℕ`-indexed sequence is measurable. -/
private theorem measurable_X (n : ℕ) : Measurable (X n) := measurable_Z n

/-- Test-specific: The `ℕ`-indexed sequence is independent. -/
private theorem iIndepFun_X (hα : 0 < α) : iIndepFun X (P α) :=
  (iIndepFun_Z hα).precomp (g := fun n : ℕ => (n : ℤ)) Nat.cast_injective

/-- Test-specific: The `ℕ`-indexed sequence is identically distributed. -/
private theorem identDistrib_X (hα : 0 < α) (n : ℕ) : IdentDistrib (X n) (X 0) (P α) (P α) :=
  identDistrib_Z hα n

/-- Test-specific: The tail of `X 0` is regularly varying with index `-α`. -/
private theorem isRegularlyVarying_X (hα : 0 < α) :
    IsRegularlyVarying (fun x => (P α).real {ω | x < X 0 ω}) (-α) :=
  isRegularlyVarying_Z hα

/-- Test-specific: The `ℕ`-indexed iid sequence is stationary. -/
private theorem isStationary_X (hα : 0 < α) : IsStationary X (P α) :=
  have := isProbabilityMeasure_P hα
  isStationary_of_iIndepFun measurable_X (iIndepFun_X hα) (identDistrib_X hα)

/-! ### Leadbetter's theorem -/

/-- **Leadbetter's theorem** (`tendsto_measureReal_partialMax_le_exp`), on iid Pareto(`α`) data:
stationarity, `D(uₙ)`, `D'(uₙ)` and `n P(X_0 > uₙ) → τ` are all discharged, for levels `uₙ`
supplied by regular variation. -/
theorem test_nonvacuous_leadbetter (hα : 0 < α) {τ : ℝ} (hτ : 0 < τ) :
    ∃ u : ℕ → ℝ, Tendsto (fun n : ℕ ↦ n * (P α).real {ω | u n < X 0 ω}) atTop (𝓝 τ) ∧
      Tendsto (fun n ↦ (P α).real {ω | partialMax X n ω ≤ u n}) atTop (𝓝 (Real.exp (-τ))) := by
  have := isProbabilityMeasure_P hα
  obtain ⟨u, hu⟩ :=
    hasExceedanceLevels_of_isRegularlyVarying (measurable_X 0) (isRegularlyVarying_X hα) τ hτ
  exact ⟨u, hu, tendsto_measureReal_partialMax_le_exp (isStationary_X hα) measurable_X
    (conditionD_of_iIndepFun (iIndepFun_X hα) (identDistrib_X hα) u)
    (conditionD'_of_iIndepFun (iIndepFun_X hα) (identDistrib_X hα) hu) hu⟩

/-- Explicit levels: for Pareto(1) noise, `uₙ = n / τ` gives `n P(X_0 > uₙ) = τ` for `n ≥ τ`,
so Leadbetter's theorem gives `P(M_n ≤ n / τ) → e^{-τ}`. -/
theorem test_nonvacuous_leadbetter_explicit {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun n : ℕ ↦ (P 1).real {ω | partialMax X n ω ≤ n / τ}) atTop
      (𝓝 (Real.exp (-τ))) := by
  have hα : (0 : ℝ) < 1 := one_pos
  have := isProbabilityMeasure_P hα
  have hu : Tendsto (fun n : ℕ ↦ n * (P 1).real {ω | (n : ℝ) / τ < X 0 ω}) atTop (𝓝 τ) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈τ⌉₊, eventually_gt_atTop 0] with n hn hn0
    have h1 : 1 ≤ (n : ℝ) / τ := by
      rw [le_div_iff₀ hτ, one_mul]; exact (Nat.ceil_le.1 hn)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [show X 0 = Z 0 from rfl, measureReal_lt_Z hα, tail_paretoMeasure one_pos hα h1]
    rw [Real.one_rpow, one_mul, Real.rpow_neg_one]
    field_simp
  exact tendsto_measureReal_partialMax_le_exp (isStationary_X hα) measurable_X
    (conditionD_of_iIndepFun (iIndepFun_X hα) (identDistrib_X hα) _)
    (conditionD'_of_iIndepFun (iIndepFun_X hα) (identDistrib_X hα) hu) hu

/-! ### The extremal index: iid and moving maximum -/

/-- **iid sequences have extremal index `1`** (`hasExtremalIndex_one_of_iIndepFun`, through
`hasExtremalIndex_one`), in the strict sense (exceedance levels exist), so `θ = 1` is the unique
extremal index (`HasExtremalIndexStrict.unique`). -/
theorem test_nonvacuous_hasExtremalIndex_iid (hα : 0 < α) :
    HasExtremalIndexStrict X (P α) 1 ∧ ∀ θ, HasExtremalIndexStrict X (P α) θ → θ = 1 := by
  have := isProbabilityMeasure_P hα
  have h : HasExtremalIndexStrict X (P α) 1 :=
    ⟨hasExtremalIndex_one_of_iIndepFun measurable_X (iIndepFun_X hα) (identDistrib_X hα),
      hasExceedanceLevels_of_isRegularlyVarying (measurable_X 0) (isRegularlyVarying_X hα)⟩
  exact ⟨h, fun θ hθ => hθ.unique h⟩

/-- **The moving maximum `max(X_t, X_{t+1})` has extremal index `1/2`**
(`hasExtremalIndex_movingMax`, direct computation), on iid Pareto noise. -/
theorem test_nonvacuous_hasExtremalIndex_movingMax (hα : 0 < α) :
    HasExtremalIndex (fun t ω ↦ max (X t ω) (X (t + 1) ω)) (P α) (1 / 2) :=
  have := isProbabilityMeasure_P hα
  hasExtremalIndex_movingMax measurable_X (iIndepFun_X hα) (identDistrib_X hα)

/-! ### The `ℤ`-indexed moving maximum and its tail process -/

/-- The moving maximum `M_t = max(Z_t, Z_{t+1})` of the concrete Pareto noise. -/
private noncomputable abbrev M : ℤ → (ℤ → ℝ) → ℝ := movingMax Z

/-- Test-specific: The moving maximum is measurable. -/
private theorem measurable_M (t : ℤ) : Measurable (M t) :=
  (measurable_Z t).max (measurable_Z (t + 1))

/-- Test-specific: The moving maximum is nonnegative. -/
private theorem M_nonneg (t : ℤ) (ω : ℤ → ℝ) : 0 ≤ M t ω := (Z_nonneg t ω).trans (le_max_left _ _)

/-- Test-specific: `|M| = M`. -/
private theorem abs_M : (fun k : ℕ => |M k|) = fun k : ℕ => M k := by
  funext k ω; exact abs_of_nonneg (M_nonneg _ ω)

/-- Test-specific: The moving maximum is stationary (shift-invariant windows). -/
private theorem hasShiftInvariantWindows_M (hα : 0 < α) : HasShiftInvariantWindows (P α) M := by
  have := isProbabilityMeasure_P hα
  rw [M, movingMax_eq_slidingWindow]
  exact (hasShiftInvariantWindows_of_iIndepFun measurable_Z (iIndepFun_Z hα)
    (identDistrib_Z hα)).slidingWindow measurable_Z _
    ((measurable_pi_apply 0).max (measurable_pi_apply 1))

/-- Test-specific: The moving maximum is `1`-dependent. -/
private theorem isMDependent_M (hα : 0 < α) : IsMDependent (fun n : ℕ => M n) 1 (P α) := by
  have := isMDependent_slidingWindow measurable_Z (iIndepFun_Z hα) ![0, 1]
    ((measurable_pi_apply 0).max (measurable_pi_apply 1)) (a := 0) (m := 1) fun j => by
      fin_cases j <;> simp
  rw [M, movingMax_eq_slidingWindow]
  exact this

/-- Test-specific: `|M|` is `1`-dependent. -/
private theorem isMDependent_abs_M (hα : 0 < α) : IsMDependent (fun k : ℕ => |M k|) 1 (P α) := by
  rw [abs_M]; exact isMDependent_M hα

/-- Test-specific: The spectral tail process of the moving maximum (library example). -/
private theorem hasSpectralTailProcess_M (hα : 0 < α) :
    HasSpectralTailProcess (P α) M α fairCoin movingMaxSpectral :=
  have := isProbabilityMeasure_P hα
  hasSpectralTailProcess_movingMax hα measurable_Z (iIndepFun_Z hα) (map_Z hα) Z_nonneg

/-- Test-specific: `M 0` and `M t` are independent for `t > 1`. -/
private theorem indepFun_M (hα : 0 < α) (t : ℤ) (ht : (1 : ℤ) < t) :
    IndepFun (M 0) (M t) (P α) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
  exact (isMDependent_M hα).indepFun (s := 0) (t := k) (by omega)

/-- `Θ_k → 0` for the spectral tail process of the moving maximum (it vanishes for `k ≥ 2`). -/
private theorem tendsto_movingMaxSpectral :
    ∀ᵐ b ∂fairCoin, Tendsto (fun k : ℕ => movingMaxSpectral k b) atTop (𝓝 0) := by
  refine Eventually.of_forall fun b => tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with k hk
  unfold movingMaxSpectral movingMaxPeak
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Levels `uₙ → ∞` with `n P(M_0 > uₙ) → τ` exist. -/
private theorem exists_levels_M (hα : 0 < α) {τ : ℝ} (hτ : 0 < τ) :
    ∃ u : ℕ → ℝ, Tendsto (fun n : ℕ => n * (P α).real {ω | u n < |M 0 ω|}) atTop (𝓝 τ) ∧
      Tendsto u atTop atTop := by
  have := isProbabilityMeasure_P hα
  have h := hasSpectralTailProcess_M hα
  obtain ⟨u, hu⟩ := h.hasExceedanceLevels_abs measurable_M τ hτ
  refine ⟨u, by simpa using hu, ?_⟩
  set F : ℝ → ℝ := fun x => (P α).real {ω | x < |M 0 ω|}
  have hFa : Antitone F := fun x y hxy => measureReal_mono (fun ω (hω : y < _) =>
    show x < _ from hxy.trans_lt hω)
  have hFF : Tendsto (fun x => F x / F x) atTop (𝓝 1) := tendsto_const_nhds.congr'
    (by filter_upwards [h.1.1] with x hx using (div_self hx.ne').symm)
  exact (InfiniteMovingAverage.tendsto_atTop_of_tendsto_natCast_mul (L := F) hFa (fun _ => measureReal_nonneg) h.1.1
    one_pos hFF (by simpa using hu)).1

/-- **Spectral tail process of the moving maximum** (`hasSpectralTailProcess_movingMax`) and its
candidate extremal index (`candidateExtremalIndex_movingMax`): `ϑ = 1/2`. -/
theorem test_nonvacuous_hasSpectralTailProcess_movingMax (hα : 0 < α) :
    HasSpectralTailProcess (P α) M α fairCoin movingMaxSpectral ∧
      candidateExtremalIndex fairCoin movingMaxSpectral α = 2⁻¹ :=
  ⟨hasSpectralTailProcess_M hα, candidateExtremalIndex_movingMax hα⟩

/-- **Spectral tail process ⇒ tail process** (`HasSpectralTailProcess.hasTailProcess`), on the
moving maximum: `Y_t = R Θ_t` with `R` Pareto independent of `Θ`. -/
theorem test_nonvacuous_hasTailProcess (hα : 0 < α) :
    HasTailProcess (P α) M α ((paretoMeasure 1 α).prod fairCoin)
      (fun t p => p.1 * movingMaxSpectral t p.2) :=
  have := isProbabilityMeasure_P hα
  (hasSpectralTailProcess_M hα).hasTailProcess hα measurable_M measurable_movingMaxSpectral

/-- **Tail process ⇒ spectral tail process** (`HasTailProcess.hasSpectralTailProcess`), the
converse direction, applied to the tail process just obtained. -/
theorem test_nonvacuous_hasTailProcess_hasSpectralTailProcess (hα : 0 < α) :
    HasSpectralTailProcess (P α) M α ((paretoMeasure 1 α).prod fairCoin)
      (fun t p => p.1 * movingMaxSpectral t p.2 / |p.1 * movingMaxSpectral 0 p.2|) := by
  have := isProbabilityMeasure_P hα
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  exact (test_nonvacuous_hasTailProcess hα).hasSpectralTailProcess hα measurable_M
    fun t => measurable_fst.mul ((measurable_movingMaxSpectral t).comp measurable_snd)

/-- **The time-change formula** (`HasSpectralTailProcess.lintegral_timeChange`), on the moving
maximum, for every shift `i`, window `S` and measurable `g ≥ 0`. -/
theorem test_nonvacuous_lintegral_timeChange (hα : 0 < α) (i : ℤ) (S : Finset ℤ)
    {g : (S → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, {b | movingMaxSpectral (-i) b ≠ 0}.indicator
        (fun b => g fun t : S => movingMaxSpectral (t - i) b) b ∂fairCoin =
      ∫⁻ b, g (fun t : S => movingMaxSpectral t b / |movingMaxSpectral i b|) *
        ENNReal.ofReal (|movingMaxSpectral i b| ^ α) ∂fairCoin :=
  have := isProbabilityMeasure_P hα
  (hasSpectralTailProcess_M hα).lintegral_timeChange hα measurable_M
    measurable_movingMaxSpectral (hasShiftInvariantWindows_M hα) i S hg

/-- **`ϑ > 0` when `Θ_t → 0`** (`HasSpectralTailProcess.candidateExtremalIndex_pos`), on the
moving maximum. -/
theorem test_nonvacuous_candidateExtremalIndex_pos (hα : 0 < α) :
    0 < candidateExtremalIndex fairCoin movingMaxSpectral α :=
  have := isProbabilityMeasure_P hα
  (hasSpectralTailProcess_M hα).candidateExtremalIndex_pos hα measurable_M
    measurable_movingMaxSpectral (hasShiftInvariantWindows_M hα) tendsto_movingMaxSpectral

/-! ### `θ = ϑ` under anticlustering and the block condition -/

/-- **`θ = ϑ` under anticlustering and `𝒜(uₙ)`** (`HasSpectralTailProcess.hasExtremalIndex_abs`),
on the moving maximum with block lengths `rₙ = ⌊√n⌋`. Both the forward anticlustering condition
and the block condition `𝒜` are discharged for every admissible level sequence (from
`1`-dependence: `antiClusteringAt_of_tendsto_mul`, `conditionA_of_isMDependent`). The conclusion
is `θ = 1/2`. -/
theorem test_nonvacuous_hasExtremalIndex_abs (hα : 0 < α) :
    HasExtremalIndex (fun k : ℕ => M k) (P α) (1 / 2) := by
  have := isProbabilityMeasure_P hα
  have hstat := hasShiftInvariantWindows_M hα
  have hmabs : IsMDependent (fun k : ℕ => |M k|) 1 (P α) :=
    isMDependent_abs_M hα
  have hind : ∀ t : ℤ, ((1 : ℕ) : ℤ) < t → IndepFun (M 0) (M t) (P α) := indepFun_M hα
  have hcond : ∀ τ > 0, ∀ u : ℕ → ℝ,
      Tendsto (fun n : ℕ => n * (P α).real {ω | u n < |M 0 ω|}) atTop (𝓝 τ) →
        ForwardAntiClusteringAt (P α) M u Nat.sqrt ∧
          ConditionA (fun k : ℕ => |M k|) (P α) u Nat.sqrt := by
    intro τ _ u hu
    refine ⟨(antiClusteringAt_of_tendsto_mul measurable_M hstat hind hu tendsto_sqrt_div).forward,
      conditionA_of_isMDependent (hstat.isStationary_abs measurable_M)
        (fun k => continuous_abs.measurable.comp (measurable_M k)) hmabs tendsto_sqrt_atTop
        tendsto_sqrt_div (C := τ + 1) ?_⟩
    filter_upwards [hu.eventually (gt_mem_nhds (lt_add_one τ))] with n hn
    exact hn.le
  have key := (hasSpectralTailProcess_M hα).hasExtremalIndex_abs hα measurable_M
    measurable_movingMaxSpectral hstat tendsto_sqrt_atTop tendsto_sqrt_div hcond
  have e : (2⁻¹ : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  rw [candidateExtremalIndex_movingMax hα, e, abs_M] at key
  exact key

/-- The strict form (`HasSpectralTailProcess.hasExtremalIndex_abs_strict`): `1/2` is the unique
extremal index of the moving maximum. -/
theorem test_nonvacuous_hasExtremalIndex_abs_strict (hα : 0 < α) :
    HasExtremalIndexStrict (fun k : ℕ => M k) (P α) (1 / 2) := by
  have := isProbabilityMeasure_P hα
  have h := hasSpectralTailProcess_M hα
  exact ⟨test_nonvacuous_hasExtremalIndex_abs hα,
    h.hasExceedanceLevels_of_nonneg (measurable_M 0) (M_nonneg 0)⟩

/-- **`θ = ϑ` for `m`-dependent series** (`HasSpectralTailProcess.hasExtremalIndex_of_isMDependent`),
applied directly to the concrete `1`-dependent moving maximum. -/
theorem test_nonvacuous_hasExtremalIndex_of_isMDependent (hα : 0 < α) :
    HasExtremalIndex (fun k : ℕ => |M k|) (P α)
      (candidateExtremalIndex fairCoin movingMaxSpectral α).toReal :=
  have := isProbabilityMeasure_P hα
  (hasSpectralTailProcess_M hα).hasExtremalIndex_of_isMDependent hα measurable_M
    measurable_movingMaxSpectral (hasShiftInvariantWindows_M hα) (isMDependent_M hα)

/-- The library's own instance `hasExtremalIndex_movingMax_of_isMDependent`, on the concrete
noise. -/
theorem test_nonvacuous_hasExtremalIndex_movingMax_of_isMDependent (hα : 0 < α) :
    HasExtremalIndexStrict (fun n : ℕ => movingMax Z n) (P α) 2⁻¹ :=
  have := isProbabilityMeasure_P hα
  hasExtremalIndex_movingMax_of_isMDependent_strict hα measurable_Z (iIndepFun_Z hα) (map_Z hα)
    Z_nonneg

/-- **The cluster ratio tends to `ϑ`** (`HasSpectralTailProcess.tendsto_blockRatio`), on the
moving maximum, with `rₙ = ⌊√n⌋`, levels `uₙ → ∞` from regular variation, and forward
anticlustering discharged. -/
theorem test_nonvacuous_tendsto_blockRatio (hα : 0 < α) :
    ∃ u : ℕ → ℝ, Tendsto (fun n => (P α).real
        {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (Nat.sqrt n), u n < |M t ω|} /
          (Nat.sqrt n * (P α).real {ω | u n < |M 0 ω|})) atTop (𝓝 (1 / 2)) := by
  have := isProbabilityMeasure_P hα
  obtain ⟨u, hu, huinf⟩ := exists_levels_M hα one_pos
  refine ⟨u, ?_⟩
  have key := (hasSpectralTailProcess_M hα).tendsto_blockRatio hα measurable_M
    measurable_movingMaxSpectral (hasShiftInvariantWindows_M hα) huinf tendsto_sqrt_atTop
    (antiClusteringAt_of_tendsto_mul measurable_M (hasShiftInvariantWindows_M hα) (m := 1)
      (indepFun_M hα) hu tendsto_sqrt_div).forward
  rw [candidateExtremalIndex_movingMax hα] at key
  simpa using key

/-- **`θ ≤ ϑ` with no anticlustering, mixing or block condition**
(`HasSpectralTailProcess.le_candidateExtremalIndex'`), on the moving maximum (`θ = 1/2`). -/
theorem test_nonvacuous_le_candidateExtremalIndex' (hα : 0 < α) :
    (1 / 2 : ℝ) ≤ (candidateExtremalIndex fairCoin movingMaxSpectral α).toReal :=
  have := isProbabilityMeasure_P hα
  (hasSpectralTailProcess_M hα).le_candidateExtremalIndex' hα measurable_M
    measurable_movingMaxSpectral (hasShiftInvariantWindows_M hα)
    (by rw [abs_M]; exact test_nonvacuous_hasExtremalIndex_abs hα)

/-- **`θ = ϑ` iff the escape mass vanishes**
(`HasSpectralTailProcess.eq_candidateExtremalIndex_iff_hasEscapeMass_zero`), on the moving
maximum: since `θ = ϑ = 1/2`, the escape mass is `0`. -/
theorem test_nonvacuous_hasEscapeMass_zero (hα : 0 < α) :
    ∃ u : ℕ → ℝ, HasEscapeMass (P α) M u Nat.sqrt 0 := by
  have := isProbabilityMeasure_P hα
  have hstat := hasShiftInvariantWindows_M hα
  obtain ⟨u, hu, -⟩ := exists_levels_M hα one_pos
  have hmabs : IsMDependent (fun k : ℕ => |M k|) 1 (P α) :=
    isMDependent_abs_M hα
  have hA : ConditionA (fun k : ℕ => |M k|) (P α) u Nat.sqrt :=
    conditionA_of_isMDependent (hstat.isStationary_abs measurable_M)
      (fun k => continuous_abs.measurable.comp (measurable_M k)) hmabs tendsto_sqrt_atTop
      tendsto_sqrt_div (C := 2)
      (by filter_upwards [hu.eventually (gt_mem_nhds one_lt_two)] with n hn
          exact hn.le)
  refine ⟨u, ((hasSpectralTailProcess_M hα).eq_candidateExtremalIndex_iff_hasEscapeMass_zero hα
    measurable_M measurable_movingMaxSpectral hstat (θ := 1 / 2)
    (by rw [abs_M]; exact test_nonvacuous_hasExtremalIndex_abs hα) hu one_pos
    tendsto_sqrt_atTop tendsto_sqrt_div hA).1 ?_⟩
  rw [candidateExtremalIndex_movingMax hα]
  norm_num

/-! ### Mixing -/

/-- **α-mixing at a rate implies `𝒜(uₙ)`** (`conditionA_of_alphaMixing`), on the moving maximum:
it is `1`-dependent, so `α(l) = 0` for `l = 2` (`alphaMixing_eq_zero`), and the rate condition
`(n / rₙ) α(lₙ) → 0` holds with `rₙ = ⌊√n⌋`, `lₙ = 2`. -/
theorem test_nonvacuous_conditionA_of_alphaMixing (hα : 0 < α) {u : ℕ → ℝ} {τ : ℝ}
    (hu : Tendsto (fun n : ℕ => n * (P α).real {ω | u n < M 0 ω}) atTop (𝓝 τ)) :
    ConditionA (fun k : ℕ => M k) (P α) u Nat.sqrt := by
  have := isProbabilityMeasure_P hα
  have hstat := hasShiftInvariantWindows_M hα
  have hstatN : IsStationary (fun k : ℕ => M k) (P α) := by
    simpa [abs_M] using hstat.isStationary_abs measurable_M
  have h0 : alphaMixing (fun k : ℕ => M k) (P α) 2 = 0 :=
    (isMDependent_M hα).alphaMixing_eq_zero one_lt_two
  refine conditionA_of_alphaMixing hstatN (fun k => measurable_M k) (l := fun _ => 2)
    tendsto_sqrt_atTop tendsto_sqrt_div ?_ ?_ (C := τ + 1) ?_
  · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp tendsto_sqrt_atTop)
  · simp [h0]
  · filter_upwards [hu.eventually (gt_mem_nhds (lt_add_one τ))] with n hn
    exact hn.le

/-! ### Maxima with an extremal index: `P(M_n ≤ aₙx + bₙ) → H(x)^θ` -/

/-- The marginal c.d.f. of the moving maximum. -/
private noncomputable def cdfM (hα : 0 < α) : CumulativeDistributionFunction :=
  have := isProbabilityMeasure_P hα
  ProbabilityMeasure.cdf ⟨(P α).map (M 0), inferInstance⟩

/-- Test-specific: `cdfM` is the c.d.f. of `M 0`. -/
private theorem cdfM_apply (hα : 0 < α) (x : ℝ) : cdfM hα x = (P α).real {ω | M 0 ω ≤ x} := by
  have := isProbabilityMeasure_P hα
  unfold cdfM
  change ((P α).map (M 0) (Set.Iic x)).toReal = _
  rw [Measure.map_apply (measurable_M 0) measurableSet_Iic]
  rfl

/-- **`P(M_n ≤ Aₙ⁻¹ x) → H(x)^θ`** (`tendsto_measureReal_partialMax_le_pow`), on the moving
maximum (`θ = 1/2`): its marginal is in the Fréchet domain of attraction by Gnedenko's theorem
(`isInMDAFrechet_iff`), since its tail is regularly varying (part of the spectral tail process). -/
theorem test_nonvacuous_partialMax_le_pow (hα : 0 < α) :
    ∃ As : ℕ → AffineIncrEquiv, ∀ x, Tendsto
      (fun n ↦ (P α).real {ω | partialMax (fun k : ℕ => M k) n ω ≤ (As n)⁻¹ x}) atTop
      (𝓝 ((standardFrechetCDF hα).pow (by norm_num : (0 : ℝ) < 1 / 2) x)) := by
  have := isProbabilityMeasure_P hα
  have hRV : IsRegularlyVarying (fun x ↦ 1 - cdfM hα x) (-α) := by
    refine (hasSpectralTailProcess_M hα).1.congr ?_
    refine Eventually.of_forall fun x => ?_
    show (P α).real {ω | x < |M 0 ω|} = 1 - cdfM hα x
    rw [cdfM_apply, ← probReal_compl_eq_one_sub (measurableSet_le (measurable_M 0) measurable_const)]
    congr 1
    ext ω
    simp [abs_of_nonneg (M_nonneg 0 ω)]
  obtain ⟨As, hAs⟩ := ((cdfM hα).isInMDAFrechet_iff hα).2 hRV
  have hstatN : IsStationary (fun k : ℕ => M k) (P α) := by
    simpa [abs_M] using (hasShiftInvariantWindows_M hα).isStationary_abs measurable_M
  exact ⟨As, fun x => tendsto_measureReal_partialMax_le_pow hstatN (fun k => measurable_M k)
    (cdfM_apply hα) (isExtremeValueDistr_standardFrechetCDF hα) As hAs
    (test_nonvacuous_hasExtremalIndex_abs hα) (by norm_num) x⟩

/-! ### Linear processes and AR(1) -/

/-- **Finite moving averages** (`MovingAverage.hasExtremalIndex`): `X_t = Z_t + Z_{t-1}`
(`m = 1`, `ψ = (1, 1)`) on the concrete Pareto noise has extremal index
`max ψ_j^α / Σ ψ_j^α`. -/
theorem test_nonvacuous_movingAverage_hasExtremalIndex (hα : 0 < α) :
    HasExtremalIndexStrict (fun n : ℕ => MovingAverage.process 1 (fun j => if j ≤ 1 then 1 else 0)
      Z n) (P α)
      ((Finset.range 2).sup' Finset.nonempty_range_add_one (fun j : ℕ => if j ≤ 1 then (1 : ℝ) else 0)
        ^ α / ∑ j ∈ Finset.range 2, (fun j : ℕ => if j ≤ 1 then (1 : ℝ) else 0) j ^ α) := by
  have := isProbabilityMeasure_P hα
  refine MovingAverage.hasExtremalIndex_strict measurable_Z (iIndepFun_Z hα) (identDistrib_Z hα)
    Z_nonneg hα (isRegularlyVarying_Z hα) (fun j => by split_ifs <;> norm_num)
    (fun j hj => by simp [show ¬ j ≤ 1 by omega]) ?_
  simp [MovingAverage.weightSum, Finset.sum_range_succ]

/-- **Infinite moving averages** (`InfiniteMovingAverage.hasSpectralTailProcess_and_hasExtremalIndex_of_lt_one`):
`X_t = Σ_j 2^{-j} Z_{t-j}` with Pareto(`α`) noise, `δ = α / 2`. -/
theorem test_nonvacuous_infiniteMovingAverage (hα : 0 < α) :
    HasSpectralTailProcess (P α) (InfiniteMovingAverage.process (fun j => (1 / 2 : ℝ) ^ j) Z) α
        (InfiniteMovingAverage.indexLaw (fun j => (1 / 2 : ℝ) ^ j) α)
        (InfiniteMovingAverage.spectral fun j => (1 / 2 : ℝ) ^ j) ∧
      HasExtremalIndex (fun n : ℕ => InfiniteMovingAverage.process (fun j => (1 / 2 : ℝ) ^ j) Z n)
        (P α) (candidateExtremalIndex (InfiniteMovingAverage.indexLaw (fun j => (1 / 2 : ℝ) ^ j) α)
          (InfiniteMovingAverage.spectral fun j => (1 / 2 : ℝ) ^ j) α).toReal := by
  have := isProbabilityMeasure_P hα
  have hδ : 0 < min (α / 2) (1 / 2) := by positivity
  exact InfiniteMovingAverage.hasSpectralTailProcess_and_hasExtremalIndex_of_lt_one measurable_Z
    (iIndepFun_Z hα) (identDistrib_Z hα) Z_nonneg hδ
    ((min_le_left _ _).trans_lt (by linarith)) ((min_le_right _ _).trans_lt (by norm_num))
    (isRegularlyVarying_Z hα) (fun j => by positivity) (AR1.summable_rpow (by norm_num) (by norm_num) hδ)
    ⟨0, by norm_num⟩

/-- **AR(1) with positive coefficient** (`AR1.hasExtremalIndex_of_pos`,
`AR1.hasSpectralTailProcess_of_pos`): `X_t = Σ_j φ^j Z_{t-j}` with `φ = 1/2` and Pareto(`α`)
noise, every `α > 0`, has extremal index `1 - φ^α`. -/
theorem test_nonvacuous_AR1 (hα : 0 < α) :
    HasExtremalIndex (fun n : ℕ => AR1.process (1 / 2) Z n) (P α) (1 - (1 / 2 : ℝ) ^ α) ∧
      HasSpectralTailProcess (P α) (AR1.process (1 / 2) Z) α
        (InfiniteMovingAverage.indexLaw (fun j => (1 / 2 : ℝ) ^ j) α)
        (InfiniteMovingAverage.spectral fun j => (1 / 2 : ℝ) ^ j) :=
  have := isProbabilityMeasure_P hα
  ⟨AR1.hasExtremalIndex_of_pos measurable_Z (iIndepFun_Z hα) (identDistrib_Z hα) Z_nonneg hα
      (isRegularlyVarying_Z hα) (by norm_num) (by norm_num),
    AR1.hasSpectralTailProcess_of_pos measurable_Z (iIndepFun_Z hα) (identDistrib_Z hα) Z_nonneg
      hα (isRegularlyVarying_Z hα) (by norm_num) (by norm_num)⟩

/-- **AR(1), strict form, `α < 1`** (`AR1.hasExtremalIndex_strict`), at `α = 1/2`. -/
theorem test_nonvacuous_AR1_strict :
    HasExtremalIndexStrict (fun n : ℕ => AR1.process (1 / 2) Z n) (P (1 / 2))
      (1 - (1 / 2 : ℝ) ^ (1 / 2 : ℝ)) :=
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have := isProbabilityMeasure_P hα
  AR1.hasExtremalIndex_strict measurable_Z (iIndepFun_Z hα) (identDistrib_Z hα) Z_nonneg hα
    (by norm_num) (isRegularlyVarying_Z hα) (by norm_num) (by norm_num)

/-! ### Markov chains: ARMAX and stationary chains from kernels -/

section ARMAX

variable {φ : ℝ}

/-- **The canonical stationary ARMAX chain** `X_{t+1} = max(φ X_t, Z_{t+1})`
(`ARMAX.hasExtremalIndexStrict_canonical`, the library's own instance) has `θ = 1 - φ^α`;
specialized to `φ = 1/2`, `α = 1`, so all side conditions are numerical. -/
theorem test_nonvacuous_ARMAX_canonical :
    HasExtremalIndexStrict
      (RandomIteration.chain (ARMAX.step (1 / 2)) Prod.fst fun n (p : ℝ × (ℕ → ℝ)) => p.2 n)
      (RandomIteration.canonicalMeasure (ARMAX.stationaryLaw (1 / 2) 1) (paretoMeasure 1 1))
      (1 - (1 / 2 : ℝ) ^ (1 : ℝ)) :=
  ARMAX.hasExtremalIndexStrict_canonical (by norm_num) (by norm_num) one_pos

/-- **`θ = ϑ` for ARMAX via the tail chain** (`ARMAX.hasExtremalIndex_candidate`) and the tail
chain itself (`ARMAX.tendstoLawCond_tailChain`), on the canonical stationary chain: every
hypothesis (invariance of the initial law, independence, iid Pareto innovations) is discharged. -/
theorem test_nonvacuous_ARMAX_tailChain (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα : 0 < α) :
    HasExtremalIndex
        (RandomIteration.chain (ARMAX.step φ) Prod.fst fun n (p : ℝ × (ℕ → ℝ)) => p.2 n)
        (RandomIteration.canonicalMeasure (ARMAX.stationaryLaw φ α) (paretoMeasure 1 α))
        (candidateExtremalIndex (ARMAX.paretoSeq α)
          (RandomIteration.spectralWalk fun _ : ℝ => φ) α).toReal ∧
      ∀ k : ℕ, TendstoLawCond
        (RandomIteration.canonicalMeasure (ARMAX.stationaryLaw φ α) (paretoMeasure 1 α))
        (fun x => Prod.fst ⁻¹' Set.Ioi x)
        (fun x p (t : Fin (k + 1)) =>
          RandomIteration.chain (ARMAX.step φ) Prod.fst (fun n (p : ℝ × (ℕ → ℝ)) => p.2 n) t p / x)
        atTop ((paretoMeasure 1 α).map fun y (t : Fin (k + 1)) => y * φ ^ (t : ℕ)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have := isProbabilityMeasure_P hα
  have : IsProbabilityMeasure (ARMAX.paretoSeq α) := by unfold ARMAX.paretoSeq; infer_instance
  have : IsProbabilityMeasure (ARMAX.stationaryLaw φ α) := by
    unfold ARMAX.stationaryLaw; infer_instance
  have hinv : (((RandomIteration.canonicalMeasure (ARMAX.stationaryLaw φ α)
      (paretoMeasure 1 α)).map Prod.fst).prod (paretoMeasure 1 α)).map
        (Function.uncurry (ARMAX.step φ)) =
      (RandomIteration.canonicalMeasure (ARMAX.stationaryLaw φ α) (paretoMeasure 1 α)).map
        Prod.fst := by
    rw [RandomIteration.map_fst_canonicalMeasure]
    exact ARMAX.map_stationaryLaw hφ0 hφ1 hα
  exact ⟨ARMAX.hasExtremalIndex_candidate hφ0 hφ1 hα measurable_fst
      (fun n => (measurable_pi_apply n).comp measurable_snd)
      (RandomIteration.indepFun_canonical _ _) (RandomIteration.iIndepFun_canonical _ _)
      (RandomIteration.map_coord_canonicalMeasure _ _) hinv _,
    ARMAX.tendstoLawCond_tailChain hφ0 hφ1 hα measurable_fst
      (fun n => (measurable_pi_apply n).comp measurable_snd)
      (RandomIteration.indepFun_canonical _ _) (RandomIteration.iIndepFun_canonical _ _)
      (RandomIteration.map_coord_canonicalMeasure _ _) hinv⟩

/-- **Every Markov kernel with an invariant law gives a stationary chain**
(`RandomIteration.exists_isStationary_of_kernel`), applied to the ARMAX kernel
`x ↦ law(max(φ x, Z))` (`RandomIteration.noiseKernel`) and its stationary law. -/
theorem test_nonvacuous_exists_isStationary_of_kernel (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα : 0 < α) :
    ∃ g : ℝ → unitInterval → ℝ, Measurable (Function.uncurry g) ∧
      RandomIteration.noiseKernel g volume =
        RandomIteration.noiseKernel (ARMAX.step φ) (paretoMeasure 1 α) ∧
      IsStationary (RandomIteration.chain g Prod.fst fun n (p : ℝ × (ℕ → unitInterval)) => p.2 n)
        (RandomIteration.canonicalMeasure (ARMAX.stationaryLaw φ α) volume) ∧
      (RandomIteration.canonicalMeasure (ARMAX.stationaryLaw φ α)
        (volume : Measure unitInterval)).map Prod.fst = ARMAX.stationaryLaw φ α := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have : IsProbabilityMeasure (ARMAX.paretoSeq α) := by unfold ARMAX.paretoSeq; infer_instance
  have : IsProbabilityMeasure (ARMAX.stationaryLaw φ α) := by
    unfold ARMAX.stationaryLaw; infer_instance
  have := RandomIteration.isMarkovKernel_noiseKernel (f := ARMAX.step φ) ARMAX.measurable_step (paretoMeasure 1 α)
  exact RandomIteration.exists_isStationary_of_kernel _ _ (by
    rw [RandomIteration.noiseKernel_comp_eq ARMAX.measurable_step]
    exact ARMAX.map_stationaryLaw hφ0 hφ1 hα)

end ARMAX

/-! ### The echo processes: `θ < ϑ` and the escape mass -/

/-- `log n / ⌊√n⌋ → 0`. -/
private theorem tendsto_log_div_sqrt :
    Tendsto (fun n : ℕ => Real.log n / Nat.sqrt n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul 2
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : Real.sqrt n < Nat.sqrt n + 1 := by
      rw [Real.sqrt_lt' (by positivity)]
      have := Nat.lt_succ_sqrt n
      have h : (n : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) * ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h
      nlinarith
    have h2s : 2 ≤ Real.sqrt n := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hn'
    have hpos : (0 : ℝ) < Nat.sqrt n := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hsq : (0 : ℝ) < Real.sqrt n := by linarith
    show Real.log n / Nat.sqrt n ≤ 2 * (Real.log n / (n : ℝ) ^ (1 / 2 : ℝ))
    rw [← Real.sqrt_eq_rpow]
    calc Real.log n / Nat.sqrt n = Real.log n * (1 / Nat.sqrt n) := by ring
      _ ≤ Real.log n * (2 / Real.sqrt n) := by
          refine mul_le_mul_of_nonneg_left ?_ hlog
          rw [div_le_div_iff₀ hpos hsq]
          linarith
      _ = 2 * (Real.log n / Real.sqrt n) := by ring

/-- **The logarithmic echo process has `θ = 1/2 < 1 = ϑ`** (`logEchoProcess_theta_lt_vartheta`),
on the concrete Pareto noise. -/
theorem test_nonvacuous_logEchoProcess_theta_lt_vartheta (hα : 0 < α) :
    HasShiftInvariantWindows (P α) (echoProcess logLag Z) ∧
      HasSpectralTailProcess (P α) (echoProcess logLag Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess logLag Z k) (P α) (1 / 2) :=
  have := isProbabilityMeasure_P hα
  logEchoProcess_theta_lt_vartheta hα measurable_Z (iIndepFun_Z hα) (map_Z hα) Z_nonneg

/-- **The power-lag echo process has `θ = 1/2 < 1 = ϑ`** (`powEchoProcess_theta_lt_vartheta`),
with `γ = α / 2`. -/
theorem test_nonvacuous_powEchoProcess_theta_lt_vartheta (hα : 0 < α) :
    HasShiftInvariantWindows (P α) (echoProcess (powLag (α / 2)) Z) ∧
      HasSpectralTailProcess (P α) (echoProcess (powLag (α / 2)) Z) α (Measure.dirac ())
        unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess (powLag (α / 2)) Z k) (P α) (1 / 2) :=
  have := isProbabilityMeasure_P hα
  powEchoProcess_theta_lt_vartheta hα measurable_Z (iIndepFun_Z hα) (map_Z hα) Z_nonneg
    (by positivity) (by linarith)

/-- Levels for the logarithmic echo process. -/
private theorem exists_levels_logEcho (hα : 0 < α) :
    ∃ u : ℕ → ℝ, Tendsto (fun n : ℕ => n * (P α).real {ω | u n < echoProcess logLag Z 0 ω})
      atTop (𝓝 1) := by
  have := isProbabilityMeasure_P hα
  obtain ⟨u, hu⟩ := (test_nonvacuous_logEchoProcess_theta_lt_vartheta hα).2.1.hasExceedanceLevels_abs
    (measurable_echoProcess measurable_Z measurable_logLag) 1 one_pos
  refine ⟨u, ?_⟩
  simpa [abs_of_nonneg (echoProcess_nonneg Z_nonneg _ _)] using hu

/-- **A strict gap `θ < ϑ` is a positive escape mass** (`HasSpectralTailProcess.lt_candidateExtremalIndex_iff`),
on the logarithmic echo process, with `rₙ = ⌊√n⌋`: the block condition `𝒜(uₙ)` is discharged by
`conditionA_logEchoProcess`, and since `θ = 1/2 < 1 = ϑ` the theorem produces `η = 1/2 > 0`. -/
theorem test_nonvacuous_lt_candidateExtremalIndex_iff (hα : 0 < α) :
    ∃ u : ℕ → ℝ, ∃ η > 0, HasEscapeMass (P α) (echoProcess logLag Z) u Nat.sqrt η ∧
      (1 / 2 : ℝ) = 1 - η := by
  have := isProbabilityMeasure_P hα
  obtain ⟨hstat, hT, hϑ, hθ⟩ := test_nonvacuous_logEchoProcess_theta_lt_vartheta hα
  obtain ⟨u, hu⟩ := exists_levels_logEcho hα
  have habs : (fun k : ℕ => |echoProcess logLag Z k|) = fun k : ℕ => echoProcess logLag Z k := by
    funext k ω; exact abs_of_nonneg (echoProcess_nonneg Z_nonneg _ _)
  have hu' : Tendsto (fun n : ℕ => n * (P α).real {ω | u n < |echoProcess logLag Z 0 ω|}) atTop
      (𝓝 1) := by
    simpa [abs_of_nonneg (echoProcess_nonneg Z_nonneg _ _)] using hu
  have hA := conditionA_logEchoProcess hα measurable_Z (iIndepFun_Z hα) (map_Z hα) Z_nonneg hu
    tendsto_sqrt_atTop tendsto_sqrt_div tendsto_log_div_sqrt
  obtain ⟨η, hη, hesc, heq⟩ := (hT.lt_candidateExtremalIndex_iff hα
    (measurable_echoProcess measurable_Z measurable_logLag) (fun t => measurable_unitSpectral t)
    hstat (by rw [habs]; exact hθ) hu' one_pos tendsto_sqrt_atTop tendsto_sqrt_div hA).1
    (by rw [hϑ]; norm_num)
  exact ⟨u, η, hη, hesc, by rw [heq, hϑ]⟩

/-- **The block-length phase transition of the logarithmic echo process**
(`logEchoProcess_phase_transition`), exercised in the critical regime `rₙ = ⌊log n⌋₊`
(`rₙ / log n → c = 1`) and the long-block regime `rₙ = ⌊√n⌋`. -/
theorem test_nonvacuous_logEchoProcess_phase_transition (hα : 0 < α) :
    ∃ u : ℕ → ℝ,
      Tendsto (clusterRatio (P α) (echoProcess logLag Z) u fun n => ⌊Real.log n⌋₊) atTop
          (𝓝 ((1 + min (1 / (1 * α)) 1) / 2)) ∧
        HasEscapeMass (P α) (echoProcess logLag Z) u (fun n => ⌊Real.log n⌋₊)
          ((1 - min (1 / (1 * α)) 1) / 2) ∧
        Tendsto (clusterRatio (P α) (echoProcess logLag Z) u Nat.sqrt) atTop (𝓝 (1 / 2)) ∧
        HasEscapeMass (P α) (echoProcess logLag Z) u Nat.sqrt (1 / 2) := by
  have := isProbabilityMeasure_P hα
  obtain ⟨u, hu⟩ := exists_levels_logEcho hα
  have hcrit : Tendsto (fun n : ℕ => ((⌊Real.log n⌋₊ : ℕ) : ℝ) / Real.log n) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h1 := (logEchoProcess_phase_transition hα measurable_Z (iIndepFun_Z hα) (map_Z hα) Z_nonneg
    one_pos hu (fun n => ⌊Real.log n⌋₊)).2.1 1 one_pos hcrit
  have h2 := (logEchoProcess_phase_transition hα measurable_Z (iIndepFun_Z hα) (map_Z hα) Z_nonneg
    one_pos hu Nat.sqrt).2.2 tendsto_sqrt_atTop tendsto_sqrt_div tendsto_log_div_sqrt
  exact ⟨u, h1.1, h1.2, h2.1, h2.2⟩

/-! ### Stochastic recurrence equations: GARCH(1,1) -/

/-- The innovation law `ζ = (δ_{1/3} + δ_2) / 2`. With `α₀ = 1`, `α₁ = 1`, `β₁ = 0` the
GARCH(1,1) multiplier `A = Z²` takes the values `1/9` and `4`: `E log A = log(4/9)/2 < 0`
(stationarity) and `E A = 37/18 > 1` (a finite tail index `κ ∈ (0, 1)`). -/
private noncomputable def ζ : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac (1 / 3 : ℝ) + Measure.dirac 2)

instance : IsProbabilityMeasure ζ :=
  ⟨by simp [ζ, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- Test-specific: Every function is integrable for the two-point law `ζ`. -/
private theorem integrable_ζ (f : ℝ → ℝ) : Integrable f ζ :=
  ((integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)).smul_measure
    (by simp)

/-- Test-specific: Integrals against `ζ` are averages of two values. -/
private theorem integral_ζ (f : ℝ → ℝ) : ∫ z, f z ∂ζ = (f (1 / 3) + f 2) / 2 := by
  rw [ζ, integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- Test-specific: A property holding at both atoms holds `ζ`-a.e. -/
private theorem ae_ζ {p : ℝ → Prop} (h1 : p (1 / 3)) (h2 : p 2) : ∀ᵐ z ∂ζ, p z := by
  refine Measure.ae_smul_measure (ae_add_measure_iff.2 ⟨?_, ?_⟩) _
  · rw [ae_dirac_eq]; exact h1
  · rw [ae_dirac_eq]; exact h2

/-- Test-specific: The GARCH multiplier at `z = 1/3`. -/
private theorem coeff_one_third : SRE.GARCH.coeff 1 0 (1 / 3) = 1 / 9 := by
  simp [SRE.GARCH.coeff]; norm_num

/-- Test-specific: The GARCH multiplier at `z = 2`. -/
private theorem coeff_two : SRE.GARCH.coeff 1 0 2 = 4 := by
  simp [SRE.GARCH.coeff]; norm_num

/-- Test-specific: Integrability of `log A` under `ζ`. -/
private theorem garch_hlog : Integrable (fun z => Real.log (SRE.GARCH.coeff 1 0 z)) ζ :=
  integrable_ζ _

/-- Test-specific: `E log A < 0` under `ζ`: the stationarity condition. -/
private theorem garch_hneg : ∫ z, Real.log (SRE.GARCH.coeff 1 0 z) ∂ζ < 0 := by
  rw [integral_ζ, coeff_one_third, coeff_two, ← Real.log_mul (by norm_num) (by norm_num)]
  have : Real.log (1 / 9 * 4) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-- **Strict stationarity of GARCH(1,1)** (`SRE.GARCH.isStationary`) for the concrete
innovation law `ζ`. -/
theorem test_nonvacuous_garch_isStationary :
    IsStationary (RandomIteration.chain SRE.affine Prod.fst fun n (p : ℝ × (ℕ → ℝ × ℝ)) => p.2 n)
      (RandomIteration.canonicalMeasure (SRE.stationaryLaw (SRE.GARCH.coeffLaw 1 1 0 ζ))
        (SRE.GARCH.coeffLaw 1 1 0 ζ)) :=
  SRE.GARCH.isStationary garch_hlog garch_hneg

/-- **The GARCH(1,1) tail index** (`SRE.GARCH.exists_tail_index`, with `S = 1`) and **the tail
bounds** (`SRE.GARCH.tail_bounds`) for the concrete innovation law: there is `κ ∈ (0, 1)` with
`E A^κ = 1`, and `P(σ² > x)` is `O(x^{-s})` exactly for `s < κ`. The non-degeneracy hypothesis
`A ≢ 1` holds because `A = 1/9` with probability `1/2`. -/
theorem test_nonvacuous_garch_tail :
    ∃ κ ∈ Set.Ioo (0 : ℝ) 1,
      (∀ s, 0 < s → s < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
        SRE.stationaryLaw (SRE.GARCH.coeffLaw 1 1 0 ζ) {y | x < |y|} ≤
          ENNReal.ofReal (C * x ^ (-s))) ∧
      (∀ s, κ < s → ¬ ∃ C x₀ : ℝ, 0 ≤ C ∧ 0 < x₀ ∧ ∀ x, x₀ ≤ x →
        SRE.stationaryLaw (SRE.GARCH.coeffLaw 1 1 0 ζ) {y | x < |y|} ≤
          ENNReal.ofReal (C * x ^ (-s))) := by
  have hA0 : ∀ᵐ z ∂ζ, SRE.GARCH.coeff 1 0 z ≠ 0 :=
    ae_ζ (by rw [coeff_one_third]; norm_num) (by rw [coeff_two]; norm_num)
  have hS1 : 1 < ∫ z, SRE.GARCH.coeff 1 0 z ^ (1 : ℝ) ∂ζ := by
    rw [integral_ζ, Real.rpow_one, Real.rpow_one, coeff_one_third, coeff_two]; norm_num
  obtain ⟨κ, hκ, hκi, hκ1⟩ := SRE.GARCH.exists_tail_index zero_le_one le_rfl garch_hlog
    garch_hneg hA0 one_pos (integrable_ζ _) hS1
  have hnd : ¬ ∀ᵐ z ∂ζ, SRE.GARCH.coeff 1 0 z = 1 := by
    intro h
    rw [ae_iff] at h
    have hle : (2⁻¹ : ℝ≥0∞) * 1 ≤ ζ {z | ¬ SRE.GARCH.coeff 1 0 z = 1} := by
      rw [ζ, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
      gcongr
      rw [Measure.dirac_apply_of_mem (show ¬ SRE.GARCH.coeff 1 0 (1 / 3) = 1 by rw [coeff_one_third]; norm_num)]
      exact le_self_add
    rw [h] at hle
    simp at hle
  exact ⟨κ, hκ, SRE.GARCH.tail_bounds zero_le_one le_rfl garch_hlog garch_hneg one_pos hκ.1 hκi
    hκ1 hnd⟩


end NonVacuity.Dependence
