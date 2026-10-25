/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.HillCluster
import ExtremeValueTheory.Dependence.Mixing
import ExtremeValueTheory.Statistics.Moment
import ExtremeValueTheory.Dependence.EchoPhaseTransition
import ExtremeValueTheory.Minimality.DependenceMixing

/-!
# Estimators of the extremal index: blocks and runs

Let `X_0, X_1, …` be a stationary sequence, `uₙ` a threshold sequence, `pₙ = P(X_0 > uₙ)` and
`rₙ` a block (run) length. The two classical estimators of the extremal index `θ`
([KS20, Ch. 10], Hsing 1991, Smith and Weissman 1994, Weissman and Novak 1998) are

* the **disjoint blocks estimator**
  `θ̂ᴮ = #{j < ⌊n / rₙ⌋ : max_{j rₙ ≤ t < (j + 1) rₙ} X_t > uₙ} / #{i < n : X_i > uₙ}`;
* the **runs estimator**
  `θ̂ᴿ = #{i < n - rₙ : X_i > uₙ, X_{i+1}, …, X_{i+rₙ} ≤ uₙ} / #{i < n : X_i > uₙ}`.

Both are ratios of two counts. We prove that each count, divided by `n pₙ`, concentrates around
its mean by Chebyshev's inequality, with variances controlled by joint exceedance probabilities
(short lags) and the strong mixing coefficients `α(h)` (long lags). Hence both estimators are
consistent for the *population* index they target:

* the blocks estimator targets the **block cluster ratio** `P(M_{rₙ} > uₙ) / (rₙ pₙ)`;
* the runs estimator targets the **runs ratio** `P(max_{0 < t ≤ rₙ} X_t ≤ uₙ | X_0 > uₙ)`.

## Thresholds

Consistency requires *intermediate* thresholds: `n pₙ → ∞`, so that the number of exceedances
grows. (At the levels `n pₙ → τ` of the definition of `θ` the counts are asymptotically Poisson
and no estimator is consistent.)

## Main results, with the hypotheses each one uses

Standing hypotheses: `X` stationary (`IsStationary`) and measurable.

* `variance_sum_ite_mem_le`: the variance of a sum of indicators whose covariances at lag `h` are
  bounded by `b h` (no stationarity).
* `tendstoInMeasure_tailCount_div`: `#{i < n : X_i > uₙ} / (n pₙ) → 1` in probability, under
  `n pₙ → ∞`, the cluster condition `∑_{1 ≤ h ≤ sₙ} P(X_0 > uₙ, X_h > uₙ) = o(n pₙ²)` and the
  mixing condition `∑_{sₙ < h < n} α(h) = o(n pₙ²)` (through the variance bound
  `variance_tailCount_le_of_isStationary` of `Statistics/HillDependent.lean`).
* `tendstoInMeasure_blockCount_div`: the block count over `n pₙ` tends to `θ` in probability if
  the block cluster ratio tends to `θ`, `rₙ → ∞`, `rₙ / n → 0`, `n pₙ → ∞` and
  `α(rₙ + 1) = o((rₙ pₙ)²)`.
* `tendstoInMeasure_runsCount_div`: the same for the runs count, if the runs ratio tends to `θ`,
  `rₙ / n → 0`, `n pₙ → ∞`, and the cluster and mixing conditions above hold with cluster window
  `rₙ + sₙ`.
* `tendstoInMeasure_blocksEstimator`, `tendstoInMeasure_runsEstimator`: **consistency of the
  blocks and runs estimators** for the population index they target.
* `tendstoInMeasure_blocksEstimator_of_isMDependent`,
  `tendstoInMeasure_runsEstimator_of_isMDependent`: for `m`-dependent sequences the cluster and
  mixing conditions are automatic: only `n pₙ → ∞`, `rₙ → ∞`, `rₙ / n → 0` and the convergence
  of the population ratio remain.
* `HasShiftInvariantWindows.runs_bounds`: `runs ratio(r) ≤ cluster ratio(r)` and
  `runs ratio(r) ≥ 2 cluster ratio(2r) - 1` (stationarity only).
* `HasSpectralTailProcess.tendsto_runsRatio`: under forward anticlustering the runs ratio tends
  to the candidate extremal index `ϑ` (the cluster ratio does so by `tendsto_blockRatio`).
* `HasSpectralTailProcess.tendstoInMeasure_blocksEstimator`,
  `HasSpectralTailProcess.tendstoInMeasure_runsEstimator`: both estimators, applied to `|X|`,
  converge to `ϑ` under anticlustering and the concentration conditions; `ϑ = θ` when the block
  condition `𝒜(uₙ)` holds as well.
* **The echo process** (`θ = 1/2`, `ϑ = 1`, geometrically strongly mixing, no anticlustering):
  - `logEcho_tendstoInMeasure_blocksEstimator`: with `log n = o(rₙ)` (and `rₙ = o(n pₙ)`,
    `log uₙ = o(rₙ)`, `rₙ uₙ^(-α) → 0`) the blocks estimator tends to `1/2 = θ`;
  - `logEcho_tendstoInMeasure_runsEstimator`: with run lengths `rₙ = o(log uₙ)` the runs
    estimator tends to `1 = ϑ`: **short runs are inconsistent** for `θ`.
  The mixing conditions are verified from `alphaMixing_logEchoProcess_le`
  (`logEcho_tendsto_sum_alphaMixing_div`, `logEcho_tendsto_alphaMixing_div`).

The intervals estimator of Ferro and Segers is in `Statistics/ExtremalIndexEstimatorsIntervals.lean`.

## References

* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020), Ch. 10 [KS20].
* T. Hsing, *Estimating the parameters of rare events*, Stoch. Proc. Appl. 37 (1991).
* R. L. Smith and I. Weissman, *Estimating the extremal index*, JRSS B 56 (1994).
* I. Weissman and S. Y. Novak, *On blocks and runs estimators of the extremal index*,
  J. Statist. Plann. Inference 66 (1998).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped Classical

namespace ExtremeValueTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### Sums of indicators -/

section Indicators

theorem measurable_ite_mem {A : Set Ω} (hA : MeasurableSet A) :
    Measurable fun ω => if ω ∈ A then (1 : ℝ) else 0 :=
  Measurable.ite hA measurable_const measurable_const

theorem memLp_sum_ite_mem [IsFiniteMeasure P] {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    (n : ℕ) (q : ENNReal) :
    MemLp (fun ω => ∑ i ∈ range n, if ω ∈ A i then (1 : ℝ) else 0) q P :=
  memLp_finsetSum _ fun i _ => MemLp.of_bound (measurable_ite_mem (hA i)).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by split_ifs <;> norm_num)

theorem integral_sum_ite_mem [IsFiniteMeasure P] {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    (n : ℕ) : ∫ ω, (∑ i ∈ range n, if ω ∈ A i then (1 : ℝ) else 0) ∂P =
      ∑ i ∈ range n, P.real (A i) := by
  rw [integral_finsetSum _ fun i _ => (MemLp.of_bound (p := 1)
    (measurable_ite_mem (hA i)).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by split_ifs <;> norm_num)).integrable le_rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun ω => if ω ∈ A i then (1 : ℝ) else 0) = (A i).indicator 1 := by
    ext ω; simp [Set.indicator]
  rw [this, integral_indicator_one (hA i)]

variable [IsProbabilityMeasure P]

/-- **Variance of a sum of indicators with lag-bounded covariances.** If
`P(A_i ∩ A_{i+h}) - P(A_i) P(A_{i+h}) ≤ b h` for all `i + h < n`, with `b ≥ 0`, then
`Var(∑_{i<n} 1_{A_i}) ≤ n (b 0 + 2 ∑_{1 ≤ h < n} b h)`. No stationarity is assumed. -/
theorem variance_sum_ite_mem_le {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (n : ℕ)
    {b : ℕ → ℝ} (hb0 : ∀ h, 0 ≤ b h)
    (hcov : ∀ i h, i + h < n → P.real (A i ∩ A (i + h)) - P.real (A i) * P.real (A (i + h)) ≤
      b h) :
    variance (fun ω => ∑ i ∈ range n, if ω ∈ A i then (1 : ℝ) else 0) P ≤
      n * (b 0 + 2 * ∑ h ∈ Ico 1 n, b h) := by
  set Y : ℕ → Ω → ℝ := fun i ω => if ω ∈ A i then 1 else 0 with hY
  have hYL2 : ∀ i, MemLp (Y i) 2 P := fun i =>
    MemLp.of_bound (measurable_ite_mem (hA i)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by simp only [hY]; split_ifs <;> norm_num)
  rw [variance_fun_sum' fun i _ => hYL2 i]
  have hc : ∀ i ∈ range n, ∀ j ∈ range n, cov[Y i, Y j; P] ≤ b (i - j + (j - i)) := by
    intro i hi j hj
    rw [mem_range] at hi hj
    rcases le_total i j with hij | hij
    · obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [show i - (i + h) + (i + h - i) = h by omega, hY, covariance_ite_mem (hA i) (hA _)]
      exact hcov i h hj
    · obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [covariance_comm, show j + h - j + (j - (j + h)) = h by omega, hY,
        covariance_ite_mem (hA j) (hA _)]
      exact hcov j h hi
  exact (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hc i hi j hj).trans
    (sum_sum_dist_le hb0 n)

end Indicators

/-! ### The estimators -/

section Defs

/-- The event that the block `{j r, …, j r + r - 1}` contains an exceedance of `u`. -/
def blockEvent (X : ℕ → Ω → ℝ) (r j : ℕ) (u : ℝ) : Set Ω :=
  (maxLE X (Ico (j * r) (j * r + r)) u)ᶜ

/-- The number of the first `k` disjoint blocks of length `r` that contain an exceedance of `u`. -/
noncomputable def blockCount (X : ℕ → Ω → ℝ) (r k : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  ∑ j ∈ range k, if ω ∈ blockEvent X r j u then 1 else 0

/-- The event that `X_i > u` is followed by a run of `r` non-exceedances
`X_{i+1}, …, X_{i+r} ≤ u`. -/
def runEvent (X : ℕ → Ω → ℝ) (r i : ℕ) (u : ℝ) : Set Ω :=
  {ω | u < X i ω} ∩ maxLE X (Ioc i (i + r)) u

/-- The number of times `i < m` at which an exceedance of `u` is followed by `r` non-exceedances. -/
noncomputable def runsCount (X : ℕ → Ω → ℝ) (r m : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ range m, if ω ∈ runEvent X r i u then 1 else 0

/-- **The disjoint blocks estimator** of the extremal index from the sample `X_0, …, X_{n-1}`:
the number of blocks of length `r` with an exceedance of `u`, divided by the number of
exceedances of `u`. -/
noncomputable def blocksEstimator (X : ℕ → Ω → ℝ) (n r : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  blockCount X r (n / r) u ω / tailCount X n u ω

/-- **The runs estimator** of the extremal index from the sample `X_0, …, X_{n-1}`: the number
of exceedances of `u` followed by `r` non-exceedances (among the times `i < n - r`, so that the
run is observed), divided by the number of exceedances of `u`. -/
noncomputable def runsEstimator (X : ℕ → Ω → ℝ) (n r : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  runsCount X r (n - r) u ω / tailCount X n u ω

variable {X : ℕ → Ω → ℝ}

theorem measurableSet_blockEvent (hX : ∀ t, Measurable (X t)) (r j : ℕ) (u : ℝ) :
    MeasurableSet (blockEvent X r j u) :=
  (measurableSet_maxLE hX _ u).compl

theorem measurableSet_runEvent (hX : ∀ t, Measurable (X t)) (r i : ℕ) (u : ℝ) :
    MeasurableSet (runEvent X r i u) :=
  (measurableSet_lt measurable_const (hX i)).inter (measurableSet_maxLE hX _ u)

omit [MeasurableSpace Ω] in
theorem blockEvent_zero (r : ℕ) (u : ℝ) :
    blockEvent X r 0 u = {ω | ∃ t < r, u < X t ω} := by
  ext ω; simp [blockEvent, maxLE]

variable [IsProbabilityMeasure P]

/-- Blocks of a stationary sequence have the same exceedance probability. -/
theorem _root_.ProbabilityTheory.IsStationary.measureReal_blockEvent (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) (r j : ℕ) (u : ℝ) :
    P.real (blockEvent X r j u) = P.real (blockEvent X r 0 u) := by
  simp only [blockEvent]
  rw [probReal_compl_eq_one_sub (measurableSet_maxLE hX _ u),
    probReal_compl_eq_one_sub (measurableSet_maxLE hX _ u), hs.measureReal_maxLE_Ico hX,
    hs.measureReal_maxLE_Ico hX]

/-- The union bound `P(M_r > u) ≤ r P(X_0 > u)` for a stationary sequence. -/
theorem _root_.ProbabilityTheory.IsStationary.measureReal_blockEvent_le (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) (r j : ℕ) (u : ℝ) :
    P.real (blockEvent X r j u) ≤ r * P.real {ω | u < X 0 ω} := by
  rw [hs.measureReal_blockEvent hX, blockEvent,
    probReal_compl_eq_one_sub (measurableSet_maxLE hX _ u)]
  have h := (hs.measureReal_maxLE_sub_le hX (A := ∅) (B := Ico (0 * r) (0 * r + r))
    (S := Ico (0 * r) (0 * r + r)) (empty_subset _) (by simp) u).2
  simpa using h

omit [IsProbabilityMeasure P] in
/-- Runs events of a stationary sequence are shift invariant. -/
theorem _root_.ProbabilityTheory.IsStationary.measureReal_runEvent (hs : IsStationary X P)
    (hX : ∀ t, Measurable (X t)) (r i : ℕ) (u : ℝ) :
    P.real (runEvent X r i u) = P.real (runEvent X r 0 u) := by
  set C : Set (ℕ → ℝ) := {x | u < x 0 ∧ ∀ t ∈ Ioc 0 r, x t ≤ u}
  have hC : MeasurableSet C := by
    have : C = {x | u < x 0} ∩ ⋂ t ∈ Ioc 0 r, {x | x t ≤ u} := by ext; simp [C]
    rw [this]
    exact (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      (Finset.measurableSet_biInter _ fun t _ ↦
        measurableSet_le (measurable_pi_apply t) measurable_const)
  have e1 : runEvent X r i u = (fun ω n ↦ X (n + i) ω) ⁻¹' C := by
    ext ω
    simp only [runEvent, maxLE, mem_Ioc, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_preimage, C, zero_add]
    refine and_congr_right fun _ => ⟨fun h t ht => h (t + i) ⟨by omega, by omega⟩,
      fun h t ht => ?_⟩
    have := h (t - i) ⟨by omega, by omega⟩
    rwa [Nat.sub_add_cancel ht.1.le] at this
  have e2 : runEvent X r 0 u = (fun ω n ↦ X n ω) ⁻¹' C := by
    ext ω; simp [runEvent, maxLE, C]
  rw [e1, e2, hs.measureReal_preimage_shift hX i hC]

end Defs

/-! ### Concentration of the exceedance count -/

section TailCount

variable [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

/-- `n pₙ > 0` forces `n > 0` and `pₙ > 0`. -/
theorem pos_and_pos_of_mul_pos {n : ℕ} {p : ℝ} (h : 0 < (n : ℝ) * p) :
    (0 : ℝ) < n ∧ 0 < p := by
  have hn0 : (0 : ℝ) < n := by
    by_contra h'
    have : (n : ℝ) = 0 := le_antisymm (not_lt.1 h') n.cast_nonneg
    rw [this, zero_mul] at h
    exact lt_irrefl _ h
  exact ⟨hn0, pos_of_mul_pos_right h hn0.le⟩

/-- **The number of exceedances concentrates**: `#{i < n : X_i > uₙ} / (n pₙ) → 1` in
probability, for a stationary sequence with `n pₙ → ∞`, the cluster condition
`∑_{1 ≤ h ≤ sₙ} P(X_0 > uₙ, X_h > uₙ) = o(n pₙ²)` and the mixing condition
`∑_{sₙ < h < n} α(h) = o(n pₙ²)`. -/
theorem tendstoInMeasure_tailCount_div (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (s : ℕ → ℕ)
    (hclus : Tendsto (fun n : ℕ => (∑ h ∈ Icc 1 (s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => tailCount X n (u n) ω / (n * P.real {ω | u n < X 0 ω}))
      atTop (fun _ => 1) := by
  set p : ℕ → ℝ := fun n => P.real {ω | u n < X 0 ω} with hp
  have hpos := hk.eventually_gt_atTop 0
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hident := fun i => hs.identDistrib hX i
  refine (tendsto_measure_abs_tailCount_div_sub (u := u) (c := 1) hX hident hpos ?_ ?_ hε).congr fun n => ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with n hn
    rw [survival, ← measureReal_def, div_self hn.ne']
  · have hlim := ((tendsto_inv_atTop_zero.comp hk).add (hclus.const_mul 2)).add
      (hmix.const_mul 2)
    simp only [mul_zero, add_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun n => by
      have := variance_nonneg (tailCount X n (u n)) P; positivity) ?_ hlim
    filter_upwards [hpos] with n hn
    obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos hn
    have h := variance_tailCount_le_of_isStationary hX hs n (s n) (u n)
    rw [survival, ← measureReal_def] at h
    calc variance (tailCount X n (u n)) P / (n * p n) ^ 2
        ≤ n * (p n + 2 * ∑ h ∈ Icc 1 (s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} +
          2 * ∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) / (n * p n) ^ 2 := by gcongr
      _ = _ := by simp only [Function.comp_apply, hp]; field_simp
  · simp [Real.dist_eq]

end TailCount

/-! ### The blocks estimator -/

section Blocks

variable [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

/-- Covariances of block indicators: neighbouring blocks are bounded by the block exceedance
probability, blocks at distance `≥ 2` by the mixing coefficient `α(r + 1)`. -/
theorem measureReal_blockEvent_inter_sub_le (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {r : ℕ} (hr : 0 < r) (u : ℝ) (i h : ℕ) :
    P.real (blockEvent X r i u ∩ blockEvent X r (i + h) u) -
        P.real (blockEvent X r i u) * P.real (blockEvent X r (i + h) u) ≤
      if h ≤ 1 then P.real (blockEvent X r 0 u) else (alphaMixing X P (r + 1)).toReal := by
  split_ifs with hh
  · rw [← hs.measureReal_blockEvent hX r i u]
    have := mul_nonneg (measureReal_nonneg (μ := P) (s := blockEvent X r i u))
      (measureReal_nonneg (μ := P) (s := blockEvent X r (i + h) u))
    have := measureReal_mono (μ := P) (Set.inter_subset_left (s := blockEvent X r i u)
      (t := blockEvent X r (i + h) u))
    linarith
  · obtain ⟨g, rfl⟩ : ∃ g, h = g + 2 := ⟨h - 2, by omega⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    set S := i * (r' + 1) + r'
    have hA : MeasurableSet[pastMeasurableSpace X S] (blockEvent X (r' + 1) i u) :=
      (measurableSet_maxLE_of_comap_le (fun t ht => comap_le_pastMeasurableSpace (by
        rw [mem_Ico] at ht; omega)) u).compl
    have e : (i + (g + 2)) * (r' + 1) = S + ((g + 1) * (r' + 1) + 1) := by simp only [S]; ring
    have hB : MeasurableSet[futureMeasurableSpace X (S + ((g + 1) * (r' + 1) + 1))]
        (blockEvent X (r' + 1) (i + (g + 2)) u) := by
      rw [← e]
      exact (measurableSet_maxLE_of_comap_le (fun t ht => comap_le_futureMeasurableSpace (by
        rw [mem_Ico] at ht; omega)) u).compl
    refine (le_abs_self _).trans ((abs_measureReal_inter_sub_le_alphaMixing hA hB).trans ?_)
    refine ENNReal.toReal_mono (alphaMixing_ne_top _) (alphaMixing_anti X ?_)
    nlinarith

/-- **Variance of the block count**:
`Var(∑_{j<k} 1{M_j > u}) ≤ k (3 P(M_r > u) + 2 k α(r + 1))`. -/
theorem variance_blockCount_le (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P) {r : ℕ}
    (hr : 0 < r) (k : ℕ) (u : ℝ) :
    variance (blockCount X r k u) P ≤
      k * (3 * P.real (blockEvent X r 0 u) + 2 * (k * (alphaMixing X P (r + 1)).toReal)) := by
  set β := P.real (blockEvent X r 0 u)
  set a := (alphaMixing X P (r + 1)).toReal
  have hβ : 0 ≤ β := measureReal_nonneg
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have h := variance_sum_ite_mem_le (P := P) (fun j => measurableSet_blockEvent hX r j u) k
    (b := fun h => if h ≤ 1 then β else a) (fun h => by split_ifs <;> assumption)
    (fun i h _ => measureReal_blockEvent_inter_sub_le hX hs hr u i h)
  have hsum : ∑ h ∈ Ico 1 k, (if h ≤ 1 then β else a) ≤ β + k * a := by
    calc ∑ h ∈ Ico 1 k, (if h ≤ 1 then β else a)
        ≤ ∑ h ∈ Ico 1 k, ((if h = 1 then β else 0) + a) := by
          refine Finset.sum_le_sum fun h hh => ?_
          rw [mem_Ico] at hh
          by_cases h1 : h = 1
          · simp [h1, ha]
          · have : ¬ h ≤ 1 := by omega
            simp [h1, this]
      _ = (if 1 ∈ Ico 1 k then β else 0) + (k - 1 : ℕ) * a := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ β + k * a := by
          gcongr
          · split_ifs <;> linarith
          · exact_mod_cast Nat.sub_le k 1
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc variance (blockCount X r k u) P
      ≤ k * (β + 2 * ∑ h ∈ Ico 1 k, (if h ≤ 1 then β else a)) := by
        refine h.trans_eq ?_
        simp
    _ ≤ k * (β + 2 * (β + k * a)) := by gcongr
    _ = k * (3 * β + 2 * (k * a)) := by ring

/-- **Concentration of the block count.** For a stationary sequence with `rₙ ≥ 1`, `rₙ / n → 0`,
`n pₙ → ∞`, `α(rₙ + 1) = o((rₙ pₙ)²)` and block cluster ratio `P(M_{rₙ} > uₙ) / (rₙ pₙ) → θ`,
the block count divided by `n pₙ` tends to `θ` in probability. -/
theorem tendstoInMeasure_blockCount_div (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} {r : ℕ → ℕ} {θ : ℝ} (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (blockEvent X (r n) 0 (u n)) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 θ))
    (hmix : Tendsto (fun n => (alphaMixing X P (r n + 1)).toReal /
      (r n * P.real {ω | u n < X 0 ω}) ^ 2) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => blockCount X (r n) (n / r n) (u n) ω /
      (n * P.real {ω | u n < X 0 ω})) atTop (fun _ => θ) := by
  set p : ℕ → ℝ := fun n => P.real {ω | u n < X 0 ω} with hp
  set β : ℕ → ℝ := fun n => P.real (blockEvent X (r n) 0 (u n)) with hβ
  have hpos := hk.eventually_gt_atTop 0
  have hgood : ∀ᶠ n in atTop, 0 < r n ∧ (0 : ℝ) < n ∧ 0 < p n := by
    filter_upwards [hpos, hr] with n hn hrn
    exact ⟨hrn, pos_and_pos_of_mul_pos hn⟩
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine (tendsto_measure_abs_div_sub_of_variance
    (S := fun n => blockCount X (r n) (n / r n) (u n)) (c := θ)
    (fun n => memLp_sum_ite_mem (P := P) (fun j => measurableSet_blockEvent hX (r n) j (u n))
      (n / r n) 2) hpos ?_ ?_ hε).congr fun n => ?_
  · -- the mean
    have h1 := (tendsto_div_mul_div_self hr hrn).mul hθ
    rw [one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [hgood] with n ⟨hr0, hn0, hp0⟩
    have hrR : (0 : ℝ) < r n := by exact_mod_cast hr0
    have hp0' : 0 < P.real {ω | u n < X 0 ω} := hp0
    unfold blockCount
    rw [integral_sum_ite_mem (fun j => measurableSet_blockEvent hX (r n) j (u n))]
    simp only [hs.measureReal_blockEvent hX, sum_const, card_range, nsmul_eq_mul]
    field_simp
  · -- the variance
    have hlim := ((tendsto_inv_atTop_zero.comp hk).const_mul 3).add (hmix.const_mul 2)
    simp only [mul_zero, add_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun n => by
      have := variance_nonneg (blockCount X (r n) (n / r n) (u n)) P; positivity) ?_ hlim
    filter_upwards [hgood] with n ⟨hr0, hn0, hp0⟩
    have hrR : (0 : ℝ) < r n := by exact_mod_cast hr0
    set k := n / r n
    have hkr : (k : ℝ) * r n ≤ n := by exact_mod_cast Nat.div_mul_le_self n (r n)
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    have hβle : β n ≤ r n * p n := hs.measureReal_blockEvent_le hX (r n) 0 (u n)
    have hβ0 : 0 ≤ β n := measureReal_nonneg
    set a := (alphaMixing X P (r n + 1)).toReal
    have ha : 0 ≤ a := ENNReal.toReal_nonneg
    have hV := variance_blockCount_le hX hs hr0 k (u n)
    have hkβ : (k : ℝ) * β n ≤ n * p n := by
      calc (k : ℝ) * β n ≤ k * (r n * p n) := by gcongr
        _ = (k * r n) * p n := by ring
        _ ≤ n * p n := by gcongr
    have hkk : (k : ℝ) * k ≤ (n / r n) ^ 2 := by
      have : (k : ℝ) ≤ n / r n := by rw [le_div_iff₀ hrR]; exact hkr
      nlinarith
    calc variance (blockCount X (r n) k (u n)) P / (n * p n) ^ 2
        ≤ k * (3 * β n + 2 * (k * a)) / (n * p n) ^ 2 := by gcongr
      _ = 3 * (k * β n) / (n * p n) ^ 2 + 2 * (k * k) * a / (n * p n) ^ 2 := by ring
      _ ≤ 3 * (n * p n) / (n * p n) ^ 2 + 2 * (n / r n) ^ 2 * a / (n * p n) ^ 2 := by gcongr
      _ = _ := by simp only [Function.comp_apply, hp]; field_simp
  · simp [Real.dist_eq]

end Blocks

/-! ### The runs estimator -/

section Runs

variable [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

/-- The lag-`h` covariance bound for runs indicators: `P(X_0 > u)` at lag `0`, nothing at lags
`1 ≤ h ≤ r` (two runs events at such lags are disjoint), the joint exceedance probability at lags
`r < h ≤ r + s`, and `α(h - r)` beyond. -/
noncomputable def runsCovBound (X : ℕ → Ω → ℝ) (P : Measure Ω) (r s : ℕ) (u : ℝ) (h : ℕ) : ℝ :=
  if h = 0 then P.real {ω | u < X 0 ω} else if h ≤ r then 0
  else if h ≤ r + s then P.real {ω | u < X 0 ω ∧ u < X h ω} else (alphaMixing X P (h - r)).toReal

omit [IsProbabilityMeasure P] in
theorem runsCovBound_nonneg (r s : ℕ) (u : ℝ) (h : ℕ) : 0 ≤ runsCovBound X P r s u h := by
  unfold runsCovBound
  split_ifs <;> first | exact measureReal_nonneg | exact le_rfl | exact ENNReal.toReal_nonneg

/-- Covariances of runs indicators of a stationary sequence. -/
theorem measureReal_runEvent_inter_sub_le (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    (r s : ℕ) (u : ℝ) (i h : ℕ) :
    P.real (runEvent X r i u ∩ runEvent X r (i + h) u) -
        P.real (runEvent X r i u) * P.real (runEvent X r (i + h) u) ≤
      runsCovBound X P r s u h := by
  have hprod := mul_nonneg (measureReal_nonneg (μ := P) (s := runEvent X r i u))
    (measureReal_nonneg (μ := P) (s := runEvent X r (i + h) u))
  unfold runsCovBound
  split_ifs with h0 h1 h2
  · subst h0
    rw [add_zero, Set.inter_self, ← hs.measureReal_lt_eq hX i u]
    have := measureReal_mono (μ := P) (fun ω (hω : ω ∈ runEvent X r i u) => hω.1)
    nlinarith [mul_self_nonneg (P.real (runEvent X r i u))]
  · have : runEvent X r i u ∩ runEvent X r (i + h) u = ∅ := by
      ext ω
      simp only [runEvent, maxLE, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Ioc,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h3⟩, h4, _⟩
      exact absurd (h3 (i + h) ⟨by omega, by omega⟩) (not_le.2 h4)
    rw [this, measureReal_empty]
    linarith
  · have hsub : runEvent X r i u ∩ runEvent X r (i + h) u ⊆
        {ω | u < X i ω ∧ u < X (i + h) ω} := fun ω hω => ⟨hω.1.1, hω.2.1⟩
    have := (measureReal_mono (μ := P) hsub).trans_eq
      (hs.measureReal_lt_and_lt hX (Nat.le_add_right i h) u)
    rw [Nat.add_sub_cancel_left] at this
    linarith
  · have hA : MeasurableSet[pastMeasurableSpace X (i + r)] (runEvent X r i u) :=
      (comap_le_pastMeasurableSpace (Nat.le_add_right i r) _
        ⟨Set.Ioi u, measurableSet_Ioi, rfl⟩).inter
        (measurableSet_maxLE_of_comap_le (fun t ht => comap_le_pastMeasurableSpace (by
          rw [mem_Ioc] at ht; omega)) u)
    have e : i + h = i + r + (h - r) := by omega
    have hB : MeasurableSet[futureMeasurableSpace X (i + r + (h - r))]
        (runEvent X r (i + h) u) := by
      rw [← e]
      exact (comap_le_futureMeasurableSpace le_rfl _ ⟨Set.Ioi u, measurableSet_Ioi, rfl⟩).inter
        (measurableSet_maxLE_of_comap_le (fun t ht => comap_le_futureMeasurableSpace (by
          rw [mem_Ioc] at ht; omega)) u)
    exact (le_abs_self _).trans (abs_measureReal_inter_sub_le_alphaMixing hA hB)

omit [IsProbabilityMeasure P] in
/-- Summing the runs covariance bound over the lags `1 ≤ h < m`. -/
theorem sum_runsCovBound_le (r s : ℕ) (u : ℝ) (m : ℕ) :
    ∑ h ∈ Ico 1 m, runsCovBound X P r s u h ≤
      ∑ h ∈ Icc 1 (r + s), P.real {ω | u < X 0 ω ∧ u < X h ω} +
        ∑ h ∈ Ico (s + 1) m, (alphaMixing X P h).toReal := by
  set q : ℕ → ℝ := fun h => P.real {ω | u < X 0 ω ∧ u < X h ω}
  set a : ℕ → ℝ := fun h => (alphaMixing X P h).toReal
  have hq : ∀ h, 0 ≤ q h := fun _ => measureReal_nonneg
  have ha : ∀ h, 0 ≤ a h := fun _ => ENNReal.toReal_nonneg
  calc ∑ h ∈ Ico 1 m, runsCovBound X P r s u h
      ≤ ∑ h ∈ Ico 1 m, ((if h ∈ Icc 1 (r + s) then q h else 0) +
          (if r + s < h then a (h - r) else 0)) := by
        refine Finset.sum_le_sum fun h hh => ?_
        rw [mem_Ico] at hh
        unfold runsCovBound
        have h0 : h ≠ 0 := by omega
        simp only [h0, ↓reduceIte, mem_Icc]
        split_ifs <;> first | omega | linarith [hq h, ha (h - r)]
    _ = ∑ h ∈ (Ico 1 m).filter (· ∈ Icc 1 (r + s)), q h +
          ∑ h ∈ (Ico 1 m).filter (r + s < ·), a (h - r) := by
        rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    _ ≤ ∑ h ∈ Icc 1 (r + s), q h + ∑ h ∈ Ico (s + 1) m, a h := by
        refine add_le_add ?_ ?_
        · exact Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => (Finset.mem_filter.1 hh).2)
            fun h _ _ => hq h
        · rw [← Finset.sum_image (g := fun h => h - r) (fun x hx y hy hxy => by
            simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at hx hy hxy
            omega)]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) fun h _ _ => ha h
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico] at hh
          obtain ⟨j, ⟨⟨hj1, hj2⟩, hj3⟩, rfl⟩ := hh
          simp only [Finset.mem_Ico]; omega

/-- **Variance of the runs count**: `Var(∑_{i<m} 1{X_i > u, X_{i+1}, …, X_{i+r} ≤ u}) ≤
m (P(X_0 > u) + 2 ∑_{1 ≤ h ≤ r + s} P(X_0 > u, X_h > u) + 2 ∑_{s < h < m} α(h))`, for every
auxiliary lag `s`. -/
theorem variance_runsCount_le (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    (r s m : ℕ) (u : ℝ) :
    variance (runsCount X r m u) P ≤ m * (P.real {ω | u < X 0 ω} +
      2 * (∑ h ∈ Icc 1 (r + s), P.real {ω | u < X 0 ω ∧ u < X h ω} +
        ∑ h ∈ Ico (s + 1) m, (alphaMixing X P h).toReal)) := by
  have h := variance_sum_ite_mem_le (P := P) (fun i => measurableSet_runEvent hX r i u) m
    (runsCovBound_nonneg r s u) (fun i h _ => measureReal_runEvent_inter_sub_le hX hs r s u i h)
  have h0 : runsCovBound X P r s u 0 = P.real {ω | u < X 0 ω} := by simp [runsCovBound]
  rw [h0] at h
  refine h.trans ?_
  have := sum_runsCovBound_le (X := X) (P := P) r s u m
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  gcongr

/-- **Concentration of the runs count.** For a stationary sequence with `rₙ / n → 0`,
`n pₙ → ∞`, runs ratio `P(X_0 > uₙ, X_1, …, X_{rₙ} ≤ uₙ) / pₙ → θ`, the cluster condition
`∑_{1 ≤ h ≤ rₙ + sₙ} P(X_0 > uₙ, X_h > uₙ) = o(n pₙ²)` and the mixing condition
`∑_{sₙ < h < n} α(h) = o(n pₙ²)`, the runs count over the times `i < n - rₙ`, divided by
`n pₙ`, tends to `θ` in probability. -/
theorem tendstoInMeasure_runsCount_div (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} {r : ℕ → ℕ} {θ : ℝ} (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (runEvent X (r n) 0 (u n)) / P.real {ω | u n < X 0 ω})
      atTop (𝓝 θ))
    (s : ℕ → ℕ)
    (hclus : Tendsto (fun n : ℕ =>
      (∑ h ∈ Icc 1 (r n + s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
        (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => runsCount X (r n) (n - r n) (u n) ω /
      (n * P.real {ω | u n < X 0 ω})) atTop (fun _ => θ) := by
  set p : ℕ → ℝ := fun n => P.real {ω | u n < X 0 ω} with hp
  have hpos := hk.eventually_gt_atTop 0
  have hgood : ∀ᶠ n in atTop, r n ≤ n ∧ (0 : ℝ) < n ∧ 0 < p n := by
    filter_upwards [hpos, hrn.eventually (gt_mem_nhds one_pos)] with n hn hr1
    obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos hn
    refine ⟨?_, hn0, hp0⟩
    rw [div_lt_one hn0] at hr1
    exact_mod_cast hr1.le
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine (tendsto_measure_abs_div_sub_of_variance
    (S := fun n => runsCount X (r n) (n - r n) (u n)) (c := θ)
    (fun n => memLp_sum_ite_mem (P := P) (fun j => measurableSet_runEvent hX (r n) j (u n))
      (n - r n) 2) hpos ?_ ?_ hε).congr fun n => ?_
  · -- the mean
    have h1 := (hrn.const_sub 1).mul hθ
    rw [sub_zero, one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [hgood] with n ⟨hrn', hn0, hp0⟩
    have hp0' : 0 < P.real {ω | u n < X 0 ω} := hp0
    unfold runsCount
    rw [integral_sum_ite_mem (fun j => measurableSet_runEvent hX (r n) j (u n))]
    simp only [hs.measureReal_runEvent hX, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_sub hrn']
    field_simp
  · -- the variance
    have hlim := ((tendsto_inv_atTop_zero.comp hk).add ((hclus.add hmix).const_mul 2))
    simp only [mul_zero, add_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun n => by
      have := variance_nonneg (runsCount X (r n) (n - r n) (u n)) P; positivity) ?_ hlim
    filter_upwards [hgood] with n ⟨hrn', hn0, hp0⟩
    have hp0' : 0 < P.real {ω | u n < X 0 ω} := hp0
    have hV := variance_runsCount_le hX hs (r n) (s n) (n - r n) (u n)
    have hA : ∑ h ∈ Ico (s n + 1) (n - r n), (alphaMixing X P h).toReal ≤
        ∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (Nat.sub_le _ _))
        fun _ _ _ => ENNReal.toReal_nonneg
    have hC : 0 ≤ ∑ h ∈ Icc 1 (r n + s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} :=
      Finset.sum_nonneg fun _ _ => measureReal_nonneg
    have hA0 : 0 ≤ ∑ h ∈ Ico (s n + 1) (n - r n), (alphaMixing X P h).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hm : ((n - r n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le _ _
    calc variance (runsCount X (r n) (n - r n) (u n)) P / (n * p n) ^ 2
        ≤ n * (p n + 2 * (∑ h ∈ Icc 1 (r n + s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} +
          ∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal)) / (n * p n) ^ 2 := by
          gcongr
          refine hV.trans ?_
          gcongr
      _ = _ := by simp only [Function.comp_apply, hp]; field_simp
  · simp [Real.dist_eq]

end Runs

/-! ### Consistency of the estimators -/

section Consistency

variable [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- A ratio of two statistics, each normalized by `n pₙ`, converges to the ratio of the limits. -/
theorem tendstoInMeasure_div_of_div {A N : ℕ → Ω → ℝ} {c : ℕ → ℝ} {θ : ℝ}
    (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (hA : TendstoInMeasure P (fun n ω => A n ω / c n) atTop (fun _ => θ))
    (hN : TendstoInMeasure P (fun n ω => N n ω / c n) atTop (fun _ => 1)) :
    TendstoInMeasure P (fun n ω => A n ω / N n ω) atTop (fun _ => θ) := by
  have h := tendstoInMeasure_comp₂ hA hN (φ := fun q => q.1 / q.2)
    (continuousAt_fst.div continuousAt_snd one_ne_zero)
  simp only [div_one] at h
  refine tendstoInMeasure_of_eventuallyEq h ?_
  filter_upwards [hc] with n hn ω
  by_cases hN0 : N n ω = 0
  · simp [hN0]
  · field_simp

/-- **Consistency of the disjoint blocks estimator** ([KS20, §10.2], Hsing 1991,
Smith–Weissman 1994). Let `X` be stationary, `pₙ = P(X_0 > uₙ)` with `n pₙ → ∞`, `rₙ ≥ 1`,
`rₙ / n → 0`, and assume

* the block cluster ratio converges: `P(M_{rₙ} > uₙ) / (rₙ pₙ) → θ`;
* the cluster condition `∑_{1 ≤ h ≤ sₙ} P(X_0 > uₙ, X_h > uₙ) = o(n pₙ²)` for some `sₙ`;
* the mixing conditions `∑_{sₙ < h < n} α(h) = o(n pₙ²)` and `α(rₙ + 1) = o((rₙ pₙ)²)`.

Then `θ̂ᴮ = #{blocks with an exceedance} / #{exceedances} → θ` in probability. -/
theorem tendstoInMeasure_blocksEstimator (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} {r : ℕ → ℕ} {θ : ℝ} (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (blockEvent X (r n) 0 (u n)) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 θ))
    (s : ℕ → ℕ)
    (hclus : Tendsto (fun n : ℕ => (∑ h ∈ Icc 1 (s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmixB : Tendsto (fun n => (alphaMixing X P (r n + 1)).toReal /
      (r n * P.real {ω | u n < X 0 ω}) ^ 2) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => blocksEstimator X n (r n) (u n)) atTop (fun _ => θ) :=
  tendstoInMeasure_div_of_div ((hk.eventually_gt_atTop 0).mono fun _ h => h.ne')
    (tendstoInMeasure_blockCount_div hX hs hr hrn hk hθ hmixB)
    (tendstoInMeasure_tailCount_div hX hs hk s hclus hmix)

/-- **Consistency of the runs estimator** ([KS20, §10.2], Smith–Weissman 1994, Weissman–Novak
1998). Let `X` be stationary, `pₙ = P(X_0 > uₙ)` with `n pₙ → ∞`, `rₙ / n → 0`, and assume

* the runs ratio converges: `P(X_1, …, X_{rₙ} ≤ uₙ | X_0 > uₙ) → θ`;
* the cluster condition `∑_{1 ≤ h ≤ rₙ + sₙ} P(X_0 > uₙ, X_h > uₙ) = o(n pₙ²)` for some `sₙ`;
* the mixing condition `∑_{sₙ < h < n} α(h) = o(n pₙ²)`.

Then `θ̂ᴿ → θ` in probability. -/
theorem tendstoInMeasure_runsEstimator (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} {r : ℕ → ℕ} {θ : ℝ} (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (runEvent X (r n) 0 (u n)) / P.real {ω | u n < X 0 ω})
      atTop (𝓝 θ))
    (s : ℕ → ℕ)
    (hclus : Tendsto (fun n : ℕ =>
      (∑ h ∈ Icc 1 (r n + s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
        (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => runsEstimator X n (r n) (u n)) atTop (fun _ => θ) := by
  have hclus' : Tendsto (fun n : ℕ =>
      (∑ h ∈ Icc 1 (s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
        (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
      (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (by positivity)) ?_ hclus
    exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (by omega))
        fun _ _ _ => measureReal_nonneg) (by positivity)
  exact tendstoInMeasure_div_of_div ((hk.eventually_gt_atTop 0).mono fun _ h => h.ne')
    (tendstoInMeasure_runsCount_div hX hs hrn hk hθ s hclus hmix)
    (tendstoInMeasure_tailCount_div hX hs hk s hclus' hmix)

end Consistency

/-! ### Sufficient conditions for the cluster and mixing conditions -/

section Conditions

variable [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

/-- **Short cluster windows need no cluster condition**: if `Sₙ = o(n pₙ)`, then
`∑_{1 ≤ h ≤ Sₙ} P(X_0 > uₙ, X_h > uₙ) = o(n pₙ²)` (each term is at most `pₙ`). -/
theorem tendsto_sum_measureReal_lt_and_lt_div_of_div {u : ℕ → ℝ} {S : ℕ → ℕ}
    (hS : Tendsto (fun n : ℕ => (S n : ℝ) / (n * P.real {ω | u n < X 0 ω})) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∑ h ∈ Icc 1 (S n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
    (by positivity)) (fun n => ?_) hS
  set p := P.real {ω | u n < X 0 ω}
  have hsum : ∑ h ∈ Icc 1 (S n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} ≤ S n * p := by
    calc _ ≤ ∑ h ∈ Icc 1 (S n), p := sum_le_sum fun h _ => measureReal_mono fun ω hω => hω.1
      _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  rcases (measureReal_nonneg (μ := P) (s := {ω | u n < X 0 ω})).lt_or_eq with hp | hp
  · rcases (Nat.cast_nonneg (α := ℝ) n).lt_or_eq with hn | hn
    · calc _ ≤ S n * p / (n * p ^ 2) := by gcongr
        _ = _ := by field_simp
    · rw [← hn]; simp
  · have h0 : p = 0 := hp.symm
    simp [h0]

/-- For an `m`-dependent stationary sequence, joint exceedances at lags `h > m` factorize, so
`∑_{1 ≤ h ≤ S} P(X_0 > u, X_h > u) ≤ m P(X_0 > u) + S P(X_0 > u)²`. -/
theorem sum_measureReal_lt_and_lt_le_of_isMDependent (hX : ∀ t, Measurable (X t))
    (hs : IsStationary X P) {m : ℕ} (hm : IsMDependent X m P) (S : ℕ) (u : ℝ) :
    ∑ h ∈ Icc 1 S, P.real {ω | u < X 0 ω ∧ u < X h ω} ≤
      m * P.real {ω | u < X 0 ω} + S * P.real {ω | u < X 0 ω} ^ 2 := by
  set p := P.real {ω | u < X 0 ω}
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hterm : ∀ h ∈ Icc 1 S, P.real {ω | u < X 0 ω ∧ u < X h ω} ≤
      (if h ≤ m then p else 0) + p ^ 2 := by
    intro h _
    split_ifs with hh
    · exact (measureReal_mono fun ω hω => hω.1).trans (le_add_of_nonneg_right (sq_nonneg _))
    · have hind := (hm.indepFun (s := 0) (t := h) (by omega)).measure_inter_preimage_eq_mul
        (Set.Ioi u) (Set.Ioi u) measurableSet_Ioi measurableSet_Ioi
      have e : {ω | u < X 0 ω ∧ u < X h ω} = X 0 ⁻¹' Set.Ioi u ∩ X h ⁻¹' Set.Ioi u := rfl
      rw [zero_add, e, measureReal_def, hind, ENNReal.toReal_mul, ← measureReal_def,
        ← measureReal_def]
      have : P.real (X h ⁻¹' Set.Ioi u) = p := hs.measureReal_lt_eq hX h u
      have h0 : P.real (X 0 ⁻¹' Set.Ioi u) = p := rfl
      rw [this, h0]
      simp [sq]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel,
    ← Finset.sum_filter, sum_const, nsmul_eq_mul]
  have hcard : ((Icc 1 S).filter (· ≤ m)).card ≤ m := by
    refine (Finset.card_le_card (t := Icc 1 m) fun h hh => ?_).trans_eq (by simp)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢; omega
  have : (((Icc 1 S).filter (· ≤ m)).card : ℝ) ≤ m := by exact_mod_cast hcard
  nlinarith

/-- The cluster condition holds for `m`-dependent sequences with `n pₙ → ∞` and `Sₙ / n → 0`. -/
theorem tendsto_sum_measureReal_lt_and_lt_div_of_isMDependent (hX : ∀ t, Measurable (X t))
    (hs : IsStationary X P) {m : ℕ} (hm : IsMDependent X m P) {u : ℕ → ℝ} {S : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hS : Tendsto (fun n => (S n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∑ h ∈ Icc 1 (S n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0) := by
  have hlim := ((tendsto_inv_atTop_zero.comp hk).const_mul (m : ℝ)).add hS
  simp only [mul_zero, zero_add] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
    (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (by positivity)) ?_ hlim
  filter_upwards [hk.eventually_gt_atTop 0] with n hn
  obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos hn
  have h := sum_measureReal_lt_and_lt_le_of_isMDependent hX hs hm (S n) (u n)
  calc _ ≤ (m * P.real {ω | u n < X 0 ω} + S n * P.real {ω | u n < X 0 ω} ^ 2) /
        (n * P.real {ω | u n < X 0 ω} ^ 2) := by gcongr
    _ = _ := by simp only [Function.comp_apply]; field_simp

omit [IsProbabilityMeasure P] in
/-- The mixing condition holds trivially for `m`-dependent sequences once `sₙ ≥ m`. -/
theorem tendsto_sum_alphaMixing_div_of_isMDependent {m : ℕ} (hm : IsMDependent X m P)
    {s : ℕ → ℕ} (hs : ∀ᶠ n in atTop, m ≤ s n) (c : ℕ → ℝ) :
    Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) / c n) atTop
      (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hs] with n hn
  rw [Finset.sum_eq_zero fun h hh => by
    rw [hm.alphaMixing_eq_zero (by rw [Finset.mem_Ico] at hh; omega), ENNReal.toReal_zero],
    zero_div]

/-- **Consistency of the blocks estimator for `m`-dependent sequences.** For a stationary
`m`-dependent sequence, `n pₙ → ∞`, `rₙ → ∞`, `rₙ / n → 0` and block cluster ratio
`P(M_{rₙ} > uₙ) / (rₙ pₙ) → θ`, the blocks estimator tends to `θ` in probability. -/
theorem tendstoInMeasure_blocksEstimator_of_isMDependent (hX : ∀ t, Measurable (X t))
    (hs : IsStationary X P) {m : ℕ} (hm : IsMDependent X m P) {u : ℕ → ℝ} {r : ℕ → ℕ}
    {θ : ℝ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (blockEvent X (r n) 0 (u n)) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 θ)) :
    TendstoInMeasure P (fun n => blocksEstimator X n (r n) (u n)) atTop (fun _ => θ) := by
  refine tendstoInMeasure_blocksEstimator hX hs (hr.eventually_gt_atTop 0) hrn hk hθ r
    (tendsto_sum_measureReal_lt_and_lt_div_of_isMDependent hX hs hm hk hrn)
    (tendsto_sum_alphaMixing_div_of_isMDependent hm (hr.eventually_ge_atTop m) _) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hr.eventually_ge_atTop m] with n hn
  rw [hm.alphaMixing_eq_zero (by omega), ENNReal.toReal_zero, zero_div]

/-- **Consistency of the runs estimator for `m`-dependent sequences.** For a stationary
`m`-dependent sequence, `n pₙ → ∞`, `rₙ → ∞`, `rₙ / n → 0` and runs ratio
`P(X_1, …, X_{rₙ} ≤ uₙ | X_0 > uₙ) → θ`, the runs estimator tends to `θ` in probability. -/
theorem tendstoInMeasure_runsEstimator_of_isMDependent (hX : ∀ t, Measurable (X t))
    (hs : IsStationary X P) {m : ℕ} (hm : IsMDependent X m P) {u : ℕ → ℝ} {r : ℕ → ℕ}
    {θ : ℝ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (runEvent X (r n) 0 (u n)) / P.real {ω | u n < X 0 ω})
      atTop (𝓝 θ)) :
    TendstoInMeasure P (fun n => runsEstimator X n (r n) (u n)) atTop (fun _ => θ) := by
  have h2 : Tendsto (fun n => ((r n + r n : ℕ) : ℝ) / n) atTop (𝓝 0) := by
    simpa [Nat.cast_add, add_div] using hrn.add hrn
  exact tendstoInMeasure_runsEstimator hX hs hrn hk hθ r
    (tendsto_sum_measureReal_lt_and_lt_div_of_isMDependent hX hs hm hk h2)
    (tendsto_sum_alphaMixing_div_of_isMDependent hm (hr.eventually_ge_atTop m) _)

end Conditions

/-! ### Population targets: the cluster ratio and the runs ratio -/

section Targets

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℤ → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The block event of `(|X_k|)_{k ∈ ℕ}` is the event `max_{0 ≤ t < r} |X_t| > u` of the cluster
ratio `clusterRatio` of `Dependence/Anticlustering.lean`. -/
theorem blockEvent_abs (r : ℕ) (u : ℝ) :
    blockEvent (fun k : ℕ => |X k|) r 0 u = {ω | ∃ t ∈ Finset.Ico (0 : ℤ) r, u < |X t ω|} := by
  rw [blockEvent_zero]
  ext ω
  simp only [Set.mem_ofPred_eq, Finset.mem_Ico]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ⟨by omega, by exact_mod_cast ht⟩, h⟩
  · rintro ⟨t, ⟨h0, ht⟩, h⟩
    refine ⟨t.toNat, by omega, ?_⟩
    rwa [Int.toNat_of_nonneg h0]

omit [MeasurableSpace Ω] in
/-- The runs event of `(|X_k|)_{k ∈ ℕ}`. -/
theorem runEvent_abs (r : ℕ) (u : ℝ) :
    runEvent (fun k : ℕ => |X k|) r 0 u =
      {ω | u < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) r, |X t ω| ≤ u} := by
  ext ω
  simp only [runEvent, maxLE, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_Ioc,
    Nat.cast_zero, zero_add]
  refine and_congr_right fun _ => ⟨fun h t ht => ?_, fun h t ht => h t ⟨by omega, by
    exact_mod_cast ht.2⟩⟩
  have := h t.toNat ⟨by omega, by omega⟩
  rwa [Int.toNat_of_nonneg ht.1.le] at this

omit [MeasurableSpace Ω] in
theorem setOf_lt_abs_zero (u : ℝ) :
    {ω | u < (fun k : ℕ => |X k|) 0 ω} = {ω | u < |X 0 ω|} := by
  ext ω; simp

variable [IsFiniteMeasure P]

/-- **Runs ratio versus cluster ratio** (the averaging identity of Segers 2006 and
Weissman–Novak 1998, in inequality form). For a stationary series, with
`D_k = {|X_0| > u, max_{0 < t ≤ k} |X_t| ≤ u}`:
`r P(D_r) ≤ P(max_{0 ≤ t < r} |X_t| > u)` and
`P(max_{0 ≤ t < 2r} |X_t| > u) ≤ r P(|X_0| > u) + r P(D_r)`.
In terms of ratios: `runs ratio(r) ≤ cluster ratio(r)` and
`runs ratio(r) ≥ 2 cluster ratio(2r) - 1`. -/
theorem HasShiftInvariantWindows.runs_bounds (hstat : HasShiftInvariantWindows P X)
    (hX : ∀ t, Measurable (X t)) (r : ℕ) (u : ℝ) :
    r * P.real {ω | u < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) r, |X t ω| ≤ u} ≤
        P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) r, u < |X t ω|} ∧
      P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (2 * r : ℕ), u < |X t ω|} ≤
        r * P.real {ω | u < |X 0 ω|} +
          r * P.real {ω | u < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) r, |X t ω| ≤ u} := by
  set D : ℕ → ℝ := fun k => P.real {ω | u < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) k, |X t ω| ≤ u}
  have hanti : ∀ m k, m ≤ k → D k ≤ D m := fun m k hmk => measureReal_mono fun ω hω =>
    ⟨hω.1, fun t ht => hω.2 t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast hmk) ht)⟩
  have hDp : ∀ k, D k ≤ P.real {ω | u < |X 0 ω|} := fun k => measureReal_mono fun ω hω => hω.1
  constructor
  · rw [hstat.measureReal_exists_lt_eq_sum hX]
    calc (r : ℝ) * D r = ∑ _k ∈ Finset.range r, D r := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range r, D k :=
          Finset.sum_le_sum fun k hk => hanti k r (Finset.mem_range.1 hk).le
  · rw [hstat.measureReal_exists_lt_eq_sum hX, show 2 * r = r + r by ring,
      Finset.sum_range_add]
    gcongr
    · calc ∑ k ∈ Finset.range r, D k ≤ ∑ _k ∈ Finset.range r, P.real {ω | u < |X 0 ω|} :=
            Finset.sum_le_sum fun k _ => hDp k
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
    · calc ∑ k ∈ Finset.range r, D (r + k) ≤ ∑ _k ∈ Finset.range r, D r :=
            Finset.sum_le_sum fun k _ => hanti r (r + k) (Nat.le_add_right r k)
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

end Targets

section TailProcess

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- **The runs ratio converges to the candidate extremal index under anticlustering**
([KS20, §10.2]; the population counterpart of the runs estimator):
`P(max_{0 < t ≤ rₙ} |X_t| ≤ uₙ | |X_0| > uₙ) → ϑ`, for a series with spectral tail process `Θ`,
`uₙ → ∞`, `rₙ → ∞` and the forward anticlustering bound. No stationarity is used. -/
theorem HasSpectralTailProcess.tendsto_runsRatio (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hAC : ForwardAntiClusteringAt P X u r) :
    Tendsto (fun n => P.real {ω | u n < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) (r n), |X t ω| ≤ u n} /
      P.real {ω | u n < |X 0 ω|}) atTop (𝓝 (candidateExtremalIndex Q Θ α).toReal) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q
  set ϑ := (candidateExtremalIndex Q Θ α).toReal
  have hs : ∀ x : ℝ, MeasurableSet {ω | x < |X 0 ω|} := fun x =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX 0))
  set S : ℕ → Set Ω := fun n => {ω | u n < |X 0 ω|}
  set D : ℕ → ℕ → Set Ω := fun n k =>
    {ω | u n < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) k, |X t ω| ≤ u n}
  set q : ℕ → ℕ → ℝ := fun n k => P.real (D n k) / P.real (S n)
  set θk : ℕ → ℝ := fun k => π.real {p | ∀ t ∈ Finset.Ioc (0 : ℤ) k, |p.1 * Θ t p.2| ≤ 1}
  have hS0 : ∀ n, 0 < P.real (S n) := fun n => h.measureReal_lt_abs_pos (u n)
  have hqanti : ∀ n m k, m ≤ k → q n k ≤ q n m := fun n m k hmk =>
    div_le_div_of_nonneg_right (measureReal_mono fun ω hω =>
      ⟨hω.1, fun t ht => hω.2 t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast hmk) ht)⟩)
      measureReal_nonneg
  have hqlim : ∀ k, Tendsto (fun n => q n k) atTop (𝓝 (θk k)) := by
    intro k
    have key := (h.tendsto_cond_forall_le hα hX hΘm (Finset.Ioc (0 : ℤ) k)).comp hu
    have key' := (ENNReal.tendsto_toReal (measure_ne_top π _)).comp key
    refine key'.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [cond_toReal_eq (hs _)]
    rfl
  have hθlim : Tendsto θk atTop (𝓝 ϑ) := tendsto_measureReal_forall_le_candidateExtremalIndex hα
    hΘm (h.ae_abs_eq_one hΘm (hX 0))
  have hθanti : ∀ m k, m ≤ k → θk k ≤ θk m := fun m k hmk => measureReal_mono (fun p hp t ht =>
    hp t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast hmk) ht))
  have hθge : ∀ m, ϑ ≤ θk m := fun m =>
    le_of_tendsto hθlim ((eventually_ge_atTop m).mono fun k hk => hθanti m k hk)
  rw [tendsto_order]
  constructor
  · intro a ha
    set ε := (ϑ - a) / 3 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    obtain ⟨m, hm1, hm⟩ := hAC.exists_ge hε0 1
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    filter_upwards [hm, (hqlim k).eventually (lt_mem_nhds (show θk k - ε < θk k by linarith))]
      with n hn hqk
    have hsub : D n k ⊆ D n (r n) ∪ {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, ((k + 1 : ℕ) : ℤ) ≤ t ∧
        t ≤ r n ∧ u n < |X t ω|} := by
      intro ω hω
      by_cases hc : ω ∈ D n (r n)
      · exact Or.inl hc
      · right
        simp only [D, Set.mem_ofPred_eq, not_and, not_forall, not_le, Finset.mem_Ioc] at hc hω
        obtain ⟨t, ⟨ht0, htr⟩, ht⟩ := hc hω.1
        refine ⟨hω.1, t, ?_, htr, ht⟩
        by_contra hlt
        exact absurd (hω.2 t ⟨ht0, by push_cast at hlt; omega⟩) (not_le.2 ht)
    have h1 := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le (μ := P) _ _)
    have h2 : q n k ≤ q n (r n) + ε := by
      simp only [q]
      rw [div_add' _ _ _ (hS0 n).ne', div_le_div_iff_of_pos_right (hS0 n)]
      linarith
    linarith [hθge k]
  · intro b hb
    obtain ⟨m, hm⟩ := (hθlim.eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hqlim m).eventually (gt_mem_nhds hm), hr.eventually_ge_atTop m] with n hn hrn
    exact (hqanti n m (r n) hrn).trans_lt hn

/-- **The blocks estimator of `|X|` converges to the candidate extremal index** under
anticlustering. For a stationary series with spectral tail process `Θ`, `uₙ → ∞`, `rₙ → ∞`, the
forward anticlustering bound, and the concentration conditions of
`tendstoInMeasure_blocksEstimator` for `|X|`, `θ̂ᴮ → ϑ` in probability. Under the block
condition `𝒜(uₙ)` as well, `ϑ` is the extremal index `θ`
(`HasSpectralTailProcess.hasExtremalIndex_abs`). -/
theorem HasSpectralTailProcess.tendstoInMeasure_blocksEstimator (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hAC : ForwardAntiClusteringAt P X u r)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop atTop) (s : ℕ → ℕ)
    (hclus : Tendsto (fun n : ℕ =>
      (∑ h ∈ Icc 1 (s n), P.real {ω | u n < |X 0 ω| ∧ u n < |X h ω|}) /
        (n * P.real {ω | u n < |X 0 ω|} ^ 2)) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ =>
      (∑ h ∈ Ico (s n + 1) n, (alphaMixing (fun k : ℕ => |X k|) P h).toReal) /
        (n * P.real {ω | u n < |X 0 ω|} ^ 2)) atTop (𝓝 0))
    (hmixB : Tendsto (fun n => (alphaMixing (fun k : ℕ => |X k|) P (r n + 1)).toReal /
      (r n * P.real {ω | u n < |X 0 ω|}) ^ 2) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => blocksEstimator (fun k : ℕ => |X k|) n (r n) (u n)) atTop
      (fun _ => (candidateExtremalIndex Q Θ α).toReal) := by
  have hXa : ∀ t : ℕ, Measurable ((fun k : ℕ => |X k|) t) := fun t =>
    continuous_abs.measurable.comp (hX t)
  refine _root_.ExtremeValueTheory.tendstoInMeasure_blocksEstimator (X := fun k : ℕ => |X k|)
    hXa (hstat.isStationary_abs hX) (hr.eventually_gt_atTop 0) hrn
    (by simpa using hk) ?_ s (by simpa using hclus) (by simpa using hmix) (by simpa using hmixB)
  simp only [blockEvent_abs]
  simpa using h.tendsto_blockRatio hα hX hΘm hstat hu hr hAC

/-- **The runs estimator of `|X|` converges to the candidate extremal index** under
anticlustering, with the concentration conditions of `tendstoInMeasure_runsEstimator` for
`|X|`. -/
theorem HasSpectralTailProcess.tendstoInMeasure_runsEstimator (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hAC : ForwardAntiClusteringAt P X u r)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop atTop) (s : ℕ → ℕ)
    (hclus : Tendsto (fun n : ℕ =>
      (∑ h ∈ Icc 1 (r n + s n), P.real {ω | u n < |X 0 ω| ∧ u n < |X h ω|}) /
        (n * P.real {ω | u n < |X 0 ω|} ^ 2)) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ =>
      (∑ h ∈ Ico (s n + 1) n, (alphaMixing (fun k : ℕ => |X k|) P h).toReal) /
        (n * P.real {ω | u n < |X 0 ω|} ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => runsEstimator (fun k : ℕ => |X k|) n (r n) (u n)) atTop
      (fun _ => (candidateExtremalIndex Q Θ α).toReal) := by
  have hXa : ∀ t : ℕ, Measurable ((fun k : ℕ => |X k|) t) := fun t =>
    continuous_abs.measurable.comp (hX t)
  refine _root_.ExtremeValueTheory.tendstoInMeasure_runsEstimator (X := fun k : ℕ => |X k|)
    hXa (hstat.isStationary_abs hX) hrn (by simpa using hk) ?_ s (by simpa using hclus)
    (by simpa using hmix)
  simp only [runEvent_abs]
  simpa using h.tendsto_runsRatio hα hX hΘm hu hr hAC

end TailProcess

/-! ### The echo process: blocks are consistent, short runs are not -/

section Echo

/-- `2 B / (2 r p) - 1 ≤ D / p` from `B ≤ r p + r D`. -/
theorem two_mul_div_sub_one_le {B D p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (h : B ≤ r * p + r * D) : 2 * (B / (2 * r * p)) - 1 ≤ D / p := by
  rw [show 2 * (B / (2 * r * p)) - 1 = (B - r * p) / (r * p) by field_simp,
    div_le_div_iff₀ (by positivity) hp]
  nlinarith

/-- `n² e^{-α rₙ} → 0` when `log n = o(rₙ)`. -/
theorem tendsto_sq_mul_exp_neg_pow {α : ℝ} (hα : 0 < α) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-α) ^ r n) atTop (𝓝 0) := by
  have hrR : Tendsto (fun n => (r n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hr
  have hin : Tendsto (fun n : ℕ => 2 * (Real.log n / r n) - α) atTop (𝓝 (-α)) := by
    simpa using (hlog.const_mul 2).sub_const α
  have hbot := hrR.atTop_mul_neg (by linarith) hin
  refine (Real.tendsto_exp_atBot.comp hbot).congr' ?_
  filter_upwards [eventually_gt_atTop 0, hr.eventually_gt_atTop 0] with n hn hrn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr' : (0 : ℝ) < r n := by exact_mod_cast hrn
  simp only [Function.comp_apply]
  rw [← Real.exp_nat_mul, ← Real.exp_log hn', ← Real.exp_nat_mul (Real.log n), Real.exp_log hn',
    ← Real.exp_add]
  congr 1
  field_simp
  push_cast
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- The constant of the geometric mixing bound of the logarithmic echo process. -/
noncomputable def echoMixConst (α : ℝ) : ℝ := 2 * (2 ^ α * Real.exp α / (1 - Real.exp (-α)))

theorem echoMixConst_nonneg (hα : 0 < α) : 0 ≤ echoMixConst α := by
  have : Real.exp (-α) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  unfold echoMixConst
  have : 0 < 1 - Real.exp (-α) := by linarith
  positivity

/-- `a / n ≤ a / (n p)` for `0 < n p` and `p ≤ 1`. -/
theorem div_le_div_mul_of_le_one {a : ℝ} {n : ℕ} {p : ℝ} (ha : 0 ≤ a) (hn : 0 < (n : ℝ) * p)
    (hp1 : p ≤ 1) : a / n ≤ a / (n * p) := by
  obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos hn
  exact div_le_div_of_nonneg_left ha hn (by nlinarith)

/-- `n pₙ ≥ 1` gives `n pₙ² ≥ 1 / n`. -/
theorem inv_le_mul_sq {n : ℕ} {p : ℝ} (hn : 1 ≤ (n : ℝ) * p) :
    1 / (n : ℝ) ≤ n * p ^ 2 ∧ 1 / (n : ℝ) ≤ p := by
  obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos (lt_of_lt_of_le one_pos hn)
  have h1 : 1 / (n : ℝ) ≤ p := by rw [div_le_iff₀ hn0]; linarith
  refine ⟨?_, h1⟩
  calc 1 / (n : ℝ) ≤ p := h1
    _ = 1 * p := (one_mul p).symm
    _ ≤ (n * p) * p := by gcongr
    _ = n * p ^ 2 := by ring

/-- **The mixing conditions hold for the logarithmic echo process** at every level with
`n pₙ → ∞`, for gaps `sₙ` with `log n = o(sₙ)`: `∑_{sₙ < h < n} α(h) = o(n pₙ²)`. -/
theorem logEcho_tendsto_sum_alphaMixing_div (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) {u : ℕ → ℝ}
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω}) atTop
      atTop)
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log n / s n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n,
      (alphaMixing (fun k : ℕ => echoProcess logLag Z k) P h).toReal) /
        (n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω} ^ 2)) atTop (𝓝 0) := by
  set q := Real.exp (-α)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hC := echoMixConst_nonneg hα
  have hlim := (tendsto_sq_mul_exp_neg_pow hα hs hlog).const_mul (echoMixConst α / (1 - q))
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (by positivity)) ?_ hlim
  filter_upwards [hk.eventually_ge_atTop 1] with n hn
  set p := P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω}
  obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos (lt_of_lt_of_le one_pos hn)
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    exact_mod_cast this
  obtain ⟨hden, -⟩ := inv_le_mul_sq hn
  have hsum : ∑ h ∈ Ico (s n + 1) n,
      (alphaMixing (fun k : ℕ => echoProcess logLag Z k) P h).toReal ≤
        echoMixConst α / (1 - q) * q ^ s n := by
    calc _ ≤ ∑ h ∈ Ico (s n + 1) n, echoMixConst α * q ^ h :=
          Finset.sum_le_sum fun h hh => alphaMixing_logEchoProcess_le hα hZ hind hlaw
            (by rw [Finset.mem_Ico] at hh; omega)
      _ = echoMixConst α * ∑ h ∈ Ico (s n + 1) n, q ^ h := by rw [Finset.mul_sum]
      _ ≤ echoMixConst α * (q ^ (s n + 1) / (1 - q)) := by
          gcongr; exact geom_sum_Ico_le_of_lt_one hq0 hq1
      _ ≤ echoMixConst α * (q ^ s n / (1 - q)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ _)) (by linarith)) hC
      _ = _ := by ring
  have hpos : 0 < (n : ℝ) * p ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  refine hsum.trans ?_
  have h1q : 0 < 1 - q := by linarith
  have hA : 0 ≤ echoMixConst α / (1 - q) * q ^ s n := by positivity
  calc echoMixConst α / (1 - q) * q ^ s n
      = echoMixConst α / (1 - q) * ((n : ℝ) ^ 2 * q ^ s n) * (1 / n) * (1 / n) := by
        field_simp
    _ ≤ echoMixConst α / (1 - q) * ((n : ℝ) ^ 2 * q ^ s n) * (1 / n) * (n * p ^ 2) := by
        gcongr
    _ ≤ echoMixConst α / (1 - q) * ((n : ℝ) ^ 2 * q ^ s n) * 1 * (n * p ^ 2) := by
        have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact hn1
        gcongr
    _ = _ := by ring

/-- **The block mixing condition holds for the logarithmic echo process**:
`α(rₙ + 1) = o((rₙ pₙ)²)` when `n pₙ → ∞` and `log n = o(rₙ)`. -/
theorem logEcho_tendsto_alphaMixing_div (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) {u : ℕ → ℝ}
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω}) atTop
      atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    Tendsto (fun n => (alphaMixing (fun k : ℕ => echoProcess logLag Z k) P (r n + 1)).toReal /
      (r n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω}) ^ 2) atTop (𝓝 0) := by
  set q := Real.exp (-α)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hC := echoMixConst_nonneg hα
  have hlim := (tendsto_sq_mul_exp_neg_pow hα hr hlog).const_mul (echoMixConst α)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg ENNReal.toReal_nonneg
    (by positivity)) ?_ hlim
  filter_upwards [hk.eventually_ge_atTop 1, hr.eventually_ge_atTop 1] with n hn hr1
  set p := P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω}
  obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos (lt_of_lt_of_le one_pos hn)
  obtain ⟨-, hp⟩ := inv_le_mul_sq hn
  have hr1' : (1 : ℝ) ≤ r n := by exact_mod_cast hr1
  have hα1 := alphaMixing_logEchoProcess_le hα hZ hind hlaw (h := r n + 1) (by omega) (P := P)
  have hpow : q ^ (r n + 1) ≤ q ^ r n := pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ _)
  have hrp : 1 / (n : ℝ) ≤ r n * p := by nlinarith
  have hrp0 : 0 < (r n : ℝ) * p := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc (alphaMixing (fun k : ℕ => echoProcess logLag Z k) P (r n + 1)).toReal
      ≤ echoMixConst α * q ^ r n := hα1.trans (by unfold echoMixConst at *; gcongr)
    _ = echoMixConst α * ((n : ℝ) ^ 2 * q ^ r n) * (1 / n) ^ 2 := by field_simp
    _ ≤ echoMixConst α * ((n : ℝ) ^ 2 * q ^ r n) * (r n * p) ^ 2 := by gcongr

variable (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)

include hpos in
theorem logEcho_eq_abs :
    (fun k : ℕ => echoProcess logLag Z k) = fun k : ℕ => |echoProcess logLag Z k| := by
  funext k ω
  exact (abs_of_nonneg (echoProcess_nonneg hpos _ ω)).symm

include hα hZ hind hlaw hpos in
/-- **The blocks estimator is consistent for the logarithmic echo process** (where `θ = 1/2`,
`ϑ = 1`): with intermediate levels `n pₙ → ∞`, block lengths `rₙ = o(n pₙ)` with
`log n = o(rₙ)` (so that the echo of an exceedance lands in its block), `log uₙ = o(rₙ)` and
`rₙ uₙ^(-α) → 0`, `θ̂ᴮ → 1/2 = θ` in probability. The mixing conditions are verified from the
geometric strong mixing of the echo process. -/
theorem logEcho_tendstoInMeasure_blocksEstimator {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hlogu : Tendsto (fun n => Real.log (u n) / r n) atTop (𝓝 0))
    (hlogn : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω}) atTop
      atTop)
    (hrk : Tendsto (fun n : ℕ => (r n : ℝ) /
      (n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω})) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => blocksEstimator (fun k : ℕ => echoProcess logLag Z k) n (r n)
      (u n)) atTop (fun _ => 1 / 2) := by
  have hX : ∀ t : ℕ, Measurable ((fun k : ℕ => echoProcess logLag Z k) t) := fun t =>
    measurable_echoProcess hZ measurable_logLag _
  have hs : IsStationary (fun k : ℕ => echoProcess logLag Z k) P := by
    rw [logEcho_eq_abs hpos]
    exact (hasShiftInvariantWindows_echoProcess hZ hind hlaw measurable_logLag).isStationary_abs
      (measurable_echoProcess hZ measurable_logLag)
  have hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hrk
    filter_upwards [hk.eventually_gt_atTop 0] with n hn
    exact div_le_div_mul_of_le_one (r n).cast_nonneg hn measureReal_le_one
  refine tendstoInMeasure_blocksEstimator hX hs (hr.eventually_gt_atTop 0) hrn hk ?_ r
    (tendsto_sum_measureReal_lt_and_lt_div_of_div (X := fun k : ℕ => echoProcess logLag Z k) hrk)
    (logEcho_tendsto_sum_alphaMixing_div hα hZ hind hlaw hk hr hlogn)
    (logEcho_tendsto_alphaMixing_div hα hZ hind hlaw hk hr hlogn)
  have h := (logEchoProcess_hasLateReturnMass hα hZ hind hlaw hpos hu hr hrb hlogu).1
  refine h.congr fun n => ?_
  have eB : P.real (blockEvent (fun k : ℕ => echoProcess logLag Z k) (r n) 0 (u n)) =
      P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |echoProcess logLag Z t ω|} := by
    rw [logEcho_eq_abs hpos, blockEvent_abs]
  have eP : P.real {ω | u n < echoProcess logLag Z ((0 : ℕ) : ℤ) ω} =
      P.real {ω | u n < |echoProcess logLag Z 0 ω|} := by
    congr 1; ext ω; simp [abs_of_nonneg (echoProcess_nonneg hpos _ ω)]
  rw [eB, eP]
  rfl

include hα hZ hind hlaw hpos in
/-- **Short runs are inconsistent for the logarithmic echo process** (a verified practitioner
warning). With intermediate levels `n pₙ → ∞` and run lengths `rₙ → ∞`, `rₙ = o(log uₙ)` (shorter
than the echo lag of an exceedance), and auxiliary gaps `sₙ` with `log n = o(sₙ)` and
`rₙ + sₙ = o(n pₙ)`, the runs estimator tends to `1 = ϑ`, not to the extremal index `θ = 1/2`:
each echo is counted as a cluster of its own. -/
theorem logEcho_tendstoInMeasure_runsEstimator {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrlog : Tendsto (fun n => (r n : ℝ) / Real.log (u n)) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω}) atTop
      atTop)
    {s : ℕ → ℕ} (hs' : Tendsto s atTop atTop)
    (hlogn : Tendsto (fun n : ℕ => Real.log n / s n) atTop (𝓝 0))
    (hrsk : Tendsto (fun n : ℕ => ((r n + s n : ℕ) : ℝ) /
      (n * P.real {ω | u n < echoProcess logLag Z (0 : ℕ) ω})) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => runsEstimator (fun k : ℕ => echoProcess logLag Z k) n (r n)
      (u n)) atTop (fun _ => 1) := by
  have hX : ∀ t : ℕ, Measurable ((fun k : ℕ => echoProcess logLag Z k) t) := fun t =>
    measurable_echoProcess hZ measurable_logLag _
  have hstat := hasShiftInvariantWindows_echoProcess hZ hind hlaw measurable_logLag
  have hXm : ∀ t, Measurable (echoProcess logLag Z t) := measurable_echoProcess hZ measurable_logLag
  have hs : IsStationary (fun k : ℕ => echoProcess logLag Z k) P := by
    rw [logEcho_eq_abs hpos]
    exact hstat.isStationary_abs hXm
  have hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hrsk
    filter_upwards [hk.eventually_gt_atTop 0] with n hn
    refine (div_le_div_mul_of_le_one (r n).cast_nonneg hn measureReal_le_one).trans ?_
    gcongr
    exact_mod_cast Nat.le_add_right _ _
  refine tendstoInMeasure_runsEstimator hX hs hrn hk ?_ s
    (tendsto_sum_measureReal_lt_and_lt_div_of_div (X := fun k : ℕ => echoProcess logLag Z k) hrsk)
    (logEcho_tendsto_sum_alphaMixing_div hα hZ hind hlaw hk hs' hlogn)
  -- the runs ratio tends to `1`: it lies between `2 CR(2 rₙ) - 1` and `1`
  have h2 : Tendsto (fun n => ((2 * r n : ℕ) : ℝ) / Real.log (u n)) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using hrlog.const_mul 2
  have hshort : ∀ᶠ n in atTop, ∀ z, u n < z → 2 * r n ≤ logLag z := by
    filter_upwards [h2.eventually (gt_mem_nhds one_pos), hu.eventually_gt_atTop 1]
      with n hn hun z hz
    have hl : 0 < Real.log (u n) := Real.log_pos hun
    rw [div_lt_one hl] at hn
    have h1 : 2 * r n ≤ ⌊Real.log (u n)⌋₊ := Nat.le_floor hn.le
    have h2 := logLag_mono (by linarith) hz.le
    simp only [logLag] at h2 ⊢
    omega
  have hrb : Tendsto (fun n => ((2 * r n : ℕ) : ℝ) * u n ^ (-α)) atTop (𝓝 0) := by
    have hlo := ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).comp hu
    refine squeeze_zero' ((hu.eventually_gt_atTop 0).mono fun n hn =>
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)) ?_ hlo
    filter_upwards [h2.eventually (gt_mem_nhds one_pos), hu.eventually_gt_atTop 1]
      with n hn hun
    have hl : 0 < Real.log (u n) := Real.log_pos hun
    rw [div_lt_one hl] at hn
    have hu0 : 0 < u n := by linarith
    simp only [Function.comp_apply]
    rw [Real.rpow_neg hu0.le, ← div_eq_mul_inv]
    gcongr
  have hCR := tendsto_clusterRatio_echoProcess_short hα hZ hind hlaw hpos measurable_logLag
    one_le_logLag hu ((hr.eventually_gt_atTop 0).mono fun n hn => by omega) hrb hshort
  have hlow := (hCR.const_mul 2).sub_const 1
  norm_num at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hr.eventually_gt_atTop 0] with n hn
    have hb := (hstat.runs_bounds hXm (r n) (u n)).2
    have hp0 : 0 < P.real {ω | u n < |echoProcess logLag Z 0 ω|} :=
      (hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos measurable_logLag one_le_logLag
        tendsto_logLag).measureReal_lt_abs_pos (u n)
    have hrR : (0 : ℝ) < r n := by exact_mod_cast hn
    have eR : P.real (runEvent (fun k : ℕ => echoProcess logLag Z k) (r n) 0 (u n)) =
        P.real {ω | u n < |echoProcess logLag Z 0 ω| ∧
          ∀ t ∈ Finset.Ioc (0 : ℤ) (r n), |echoProcess logLag Z t ω| ≤ u n} := by
      rw [logEcho_eq_abs hpos, runEvent_abs]
    have eP : P.real {ω | u n < echoProcess logLag Z ((0 : ℕ) : ℤ) ω} =
        P.real {ω | u n < |echoProcess logLag Z 0 ω|} := by
      congr 1; ext ω; simp [abs_of_nonneg (echoProcess_nonneg hpos _ ω)]
    rw [eR, eP]
    simp only [clusterRatio]
    have key := two_mul_div_sub_one_le hp0 hrR hb
    convert key using 4
    push_cast; ring
  · filter_upwards with n
    exact div_le_one_of_le₀ (measureReal_mono fun ω hω => hω.1) measureReal_nonneg

end Echo

end ExtremeValueTheory
