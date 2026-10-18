/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.HillCluster
import ExtremeValueTheory.Dependence.Mixing

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

end ExtremeValueTheory
