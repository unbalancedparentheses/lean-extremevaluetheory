/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.HillDependent
import ExtremeValueTheory.Dependence.MDependentExamples

/-!
# Hill consistency under a cluster-size condition, and for sliding-window processes

`tendstoInMeasure_hill_of_alphaMixing` assumes the cluster condition
`(1/k_n) ∑_{1 ≤ h ≤ r_n} P(X_h > u_n | X_0 > u_n) → 0`. Here we derive it from:

* **bounded expected cluster size**: `∑_{1 ≤ h ≤ r_n} P(X_h > u_n | X_0 > u_n) ≤ C` eventually
  (`tendsto_clusterRatio_of_bddClusterSize`);
* in particular the **sum-anticlustering condition** `S(r_n, u_n)` of [KS20, (9.1.6)]:
  `lim_m limsup_n ∑_{m ≤ h ≤ r_n} P(X_h > u_n | X_0 > u_n) = 0`
  (`SumAntiClusteringAt.bddClusterSize`);
* or simply `r_n / k_n → 0` (`tendsto_clusterRatio_of_div`).

## A remark on anticlustering

The anticlustering condition `AC(r_n)` of `Dependence/Anticlustering.lean` controls the
probability `P(max_{m ≤ h ≤ r_n} X_h > u_n | X_0 > u_n)` of *some* late exceedance, whereas the
cluster condition is about the *expected number* `∑_{h ≤ r_n} P(X_h > u_n | X_0 > u_n)` of
exceedances. AC bounds only the probability of the union of the late exceedance events, while
their conditional probabilities can sum to up to `r_n - m` times that bound (when the events
nearly coincide, i.e. one cluster contains many late exceedances). So AC together with a spectral
tail process does not give a bounded expected cluster size, and [KS20, §9.1] assume the sum
condition `S(r_n, u_n)` for the tail empirical process. We therefore state the Hill theorem under `S(r_n, u_n)`; note that
`S(r_n, u_n)` implies the forward anticlustering bound by the union bound
(`SumAntiClusteringAt.max_le`).

## Main results

* `tendstoInMeasure_hill_of_alphaMixing_of_sumAntiClustering`: Hill consistency for stationary
  strongly mixing sequences under `S(r_n, u_n)` and the mixing condition.
* `tendstoInMeasure_hill_of_alphaMixing_of_div`: the same with `r_n / k_n → 0` instead of any
  cluster condition.
* `identDistrib_movingMax`, `isRegularlyVarying_survival_movingMax`,
  `tendstoInMeasure_hill_movingMax`: the moving maximum of iid Pareto noise has identical
  marginals with regularly varying tail, and the Hill estimator is consistent for it.
* `MovingAverage.identDistrib`, `MovingAverage.isRegularlyVarying_survival`,
  `MovingAverage.tendstoInMeasure_hill`: the same for finite moving averages.
-/

open Filter Topology Real MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

section Cluster

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- The **sum-anticlustering condition** `S(rₙ, uₙ)` ([KS20, (9.1.6)], one-sided):
`lim_{m → ∞} limsup_{n → ∞} ∑_{m ≤ h ≤ rₙ} P(X_h > uₙ | X_0 > uₙ) = 0`, in `ε`–`m` form. -/
def SumAntiClusteringAt (P : Measure Ω) (X : ℕ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ᶠ n in atTop,
    ∑ h ∈ Icc m (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} ≤ ε * P.real {ω | u n < X 0 ω}

omit [IsProbabilityMeasure P] in
/-- `S(rₙ, uₙ)` implies the (max-type) forward anticlustering bound, by the union bound. -/
theorem SumAntiClusteringAt.max_le {u : ℕ → ℝ} {r : ℕ → ℕ} (h : SumAntiClusteringAt P X u r)
    {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, ∀ᶠ n in atTop,
      P.real {ω | u n < X 0 ω ∧ ∃ h ∈ Icc m (r n), u n < X h ω} ≤
        ε * P.real {ω | u n < X 0 ω} := by
  obtain ⟨m, hm⟩ := h ε hε
  refine ⟨m, hm.mono fun n hn => le_trans ?_ hn⟩
  have : {ω | u n < X 0 ω ∧ ∃ h ∈ Icc m (r n), u n < X h ω} =
      ⋃ h ∈ Icc m (r n), {ω | u n < X 0 ω ∧ u n < X h ω} := by
    ext ω; simp
  rw [this]
  exact measureReal_biUnion_finset_le _ _

omit [IsProbabilityMeasure P] in
/-- **Bounded expected cluster size implies the cluster condition** of
`tendstoInMeasure_hill_of_alphaMixing`. -/
theorem tendsto_clusterRatio_of_bddClusterSize {u : ℕ → ℝ} {r k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hpos : ∀ n, 0 < P.real {ω | u n < X 0 ω}) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} ≤
      C * P.real {ω | u n < X 0 ω}) :
    Tendsto (fun n => (∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 0) := by
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hb := (tendsto_inv_atTop_zero.comp hkR).const_mul C
  rw [mul_zero] at hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun n => by
      have := hpos n
      have : 0 ≤ ∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} :=
        sum_nonneg fun _ _ => measureReal_nonneg
      positivity) ?_
  filter_upwards [hC, hkR.eventually_gt_atTop 0] with n hn hkn
  have hF := hpos n
  rw [← measureReal_def, div_div, Function.comp_apply, div_le_iff₀ (by positivity)]
  calc _ ≤ C * P.real {ω | u n < X 0 ω} := hn
    _ = _ := by field_simp

/-- `S(rₙ, uₙ)` bounds the expected cluster size. -/
theorem SumAntiClusteringAt.bddClusterSize {u : ℕ → ℝ} {r : ℕ → ℕ}
    (h : SumAntiClusteringAt P X u r) : ∃ C : ℝ, ∀ᶠ n in atTop,
      ∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} ≤
        C * P.real {ω | u n < X 0 ω} := by
  obtain ⟨m, hm⟩ := h 1 one_pos
  refine ⟨m + 1, hm.mono fun n hn => ?_⟩
  set f : ℕ → ℝ := fun h => P.real {ω | u n < X 0 ω ∧ u n < X h ω}
  have hf0 : ∀ h, 0 ≤ f h := fun _ => measureReal_nonneg
  have hfle : ∀ h, f h ≤ P.real {ω | u n < X 0 ω} := fun _ =>
    measureReal_mono fun ω hω => hω.1
  calc ∑ h ∈ Icc 1 (r n), f h ≤ ∑ h ∈ Icc 1 m ∪ Icc m (r n), f h := by
        refine sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) fun h _ _ => hf0 h
        rw [mem_Icc] at hh
        rw [mem_union, mem_Icc, mem_Icc]
        omega
    _ ≤ ∑ h ∈ Icc 1 m, f h + ∑ h ∈ Icc m (r n), f h := by
        rw [← sum_union_inter]
        linarith [sum_nonneg fun h (_ : h ∈ Icc 1 m ∩ Icc m (r n)) => hf0 h]
    _ ≤ ∑ h ∈ Icc 1 m, P.real {ω | u n < X 0 ω} + 1 * P.real {ω | u n < X 0 ω} := by
        gcongr with h
        exact hfle h
    _ = (m + 1) * P.real {ω | u n < X 0 ω} := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

/-- **Block lengths `rₙ = o(kₙ)` need no cluster condition**: the cluster ratio is at most
`rₙ / kₙ`. -/
theorem tendsto_clusterRatio_of_div {u : ℕ → ℝ} {r k : ℕ → ℕ}
    (hpos : ∀ n, 0 < P.real {ω | u n < X 0 ω})
    (hrk : Tendsto (fun n => (r n : ℝ) / k n) atTop (𝓝 0)) :
    Tendsto (fun n => (∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrk
    (fun n => by
      have := hpos n
      have : 0 ≤ ∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} :=
        sum_nonneg fun _ _ => measureReal_nonneg
      positivity) fun n => ?_
  have hF := hpos n
  have hsum : ∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω ∧ u n < X h ω} ≤
      r n * P.real {ω | u n < X 0 ω} := by
    calc _ ≤ ∑ h ∈ Icc 1 (r n), P.real {ω | u n < X 0 ω} :=
          sum_le_sum fun h _ => measureReal_mono fun ω hω => hω.1
      _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  simp only
  rw [← measureReal_def]
  gcongr
  rw [div_le_iff₀ hF]
  exact hsum

/-- **Hill consistency for strongly mixing sequences under `S(rₙ, uₙ)`.** As
`tendstoInMeasure_hill_of_alphaMixing`, with the cluster condition replaced by the
sum-anticlustering condition along every admissible level sequence. -/
theorem tendstoInMeasure_hill_of_alphaMixing_of_sumAntiClustering (hX : ∀ i, Measurable (X i))
    (hstat : IsStationary X P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (r : ℕ → ℕ)
    (hS : ∀ (u : ℕ → ℝ) (c : ℝ), 0 < c → Tendsto u atTop atTop →
      Tendsto (fun n => n * (P {ω | u n < X 0 ω}).toReal / k n) atTop (𝓝 c) →
      SumAntiClusteringAt P X u r)
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) / (k n : ℝ) ^ 2 *
      ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P h).toReal) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  refine tendstoInMeasure_hill_of_alphaMixing hX hstat hα hRV hk hkn r
    (fun u c hc hu hmean => ?_) hmix
  obtain ⟨C, hC⟩ := (hS u c hc hu hmean).bddClusterSize
  exact tendsto_clusterRatio_of_bddClusterSize hk
    (fun n => survival_pos (P := P) (Y := X 0) hRV (u n)) hC

/-- **Hill consistency for strongly mixing sequences with block lengths `rₙ = o(kₙ)`**: no
cluster condition is needed. -/
theorem tendstoInMeasure_hill_of_alphaMixing_of_div (hX : ∀ i, Measurable (X i))
    (hstat : IsStationary X P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (r : ℕ → ℕ) (hrk : Tendsto (fun n => (r n : ℝ) / k n) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) / (k n : ℝ) ^ 2 *
      ∑ h ∈ Ico (r n + 1) n, (alphaMixing X P h).toReal) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) :=
  tendstoInMeasure_hill_of_alphaMixing hX hstat hα hRV hk hkn r
    (fun u _ _ _ _ => tendsto_clusterRatio_of_div
      (fun n => survival_pos (P := P) (Y := X 0) hRV (u n)) hrk) hmix

end Cluster

/-! ### Sliding-window examples -/

section Examples

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℤ → Ω → ℝ} {α : ℝ}

/-- The moving maximum of iid noise has identically distributed marginals. -/
theorem identDistrib_movingMax (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hid : ∀ i, IdentDistrib (Z i) (Z 0) P P) (i : ℕ) :
    IdentDistrib (movingMax Z i) (movingMax Z (0 : ℕ)) P P := by
  have hF : Measurable fun y : Fin 2 → ℝ => max (y 0) (y 1) :=
    (measurable_pi_apply 0).max (measurable_pi_apply 1)
  have hX : ∀ t, Measurable (movingMax Z t) := fun t => (hZ t).max (hZ (t + 1))
  have hstat : HasShiftInvariantWindows P (movingMax Z) := by
    rw [movingMax_eq_slidingWindow]
    exact (hasShiftInvariantWindows_of_iIndepFun hZ hind hid).slidingWindow hZ _ hF
  exact (hstat.isStationary_nat hX).identDistrib (fun n => hX n) i

/-- The moving maximum of iid Pareto noise has a regularly varying marginal tail. -/
theorem isRegularlyVarying_survival_movingMax (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) :
    IsRegularlyVarying (fun x => (P {ω | x < movingMax Z (0 : ℕ) ω}).toReal) (-α) := by
  have := (hasSpectralTailProcess_movingMax hα hZ hind hlaw hpos).1
  have habs : ∀ ω, |movingMax Z 0 ω| = movingMax Z 0 ω := fun ω =>
    abs_of_nonneg ((hpos _ ω).trans (le_max_left _ _))
  simpa [habs, measureReal_def] using this

/-- **Hill consistency for the moving maximum** `X_t = max(Z_t, Z_{t+1})` of iid Pareto(`α`)
noise: `H_{k(n),n} → 1/α` in probability for `k → ∞`, `k/n → 0`. Through
`tendstoInMeasure_hill_of_isMDependent` (`1`-dependence). -/
theorem tendstoInMeasure_hill_movingMax (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => movingMax Z i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  have hF : Measurable fun y : Fin 2 → ℝ => max (y 0) (y 1) :=
    (measurable_pi_apply 0).max (measurable_pi_apply 1)
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have hm : IsMDependent (fun n : ℕ => movingMax Z n) 1 P := by
    have := isMDependent_slidingWindow hZ hind ![0, 1] hF (a := 0) (m := 1) fun j => by
      fin_cases j <;> simp
    rw [movingMax_eq_slidingWindow]
    exact this
  exact tendstoInMeasure_hill_of_isMDependent (X := fun n : ℕ => movingMax Z n)
    (fun n => (hZ _).max (hZ _)) hm (identDistrib_movingMax hZ hind hid) hα
    (isRegularlyVarying_survival_movingMax hα hZ hind hlaw hpos) hk hkn

namespace MovingAverage

variable {m : ℕ} {ψ : ℕ → ℝ}

/-- A finite moving average of iid noise has identically distributed marginals. -/
theorem identDistrib (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (i : ℕ) :
    IdentDistrib (process m ψ Z i) (process m ψ Z (0 : ℕ)) P P := by
  have hF : Measurable fun y : Fin (m + 1) → ℝ => ∑ j : Fin (m + 1), ψ j * y j :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _
  have hstat : HasShiftInvariantWindows P (process m ψ Z) := by
    rw [process_eq_slidingWindow]
    exact (hasShiftInvariantWindows_of_iIndepFun hZ hind hident).slidingWindow hZ _ hF
  exact (hstat.isStationary_nat (measurable_process hZ)).identDistrib
    (fun n => measurable_process hZ n) i

/-- A finite moving average with nonnegative weights of iid nonnegative regularly varying noise
has a regularly varying marginal tail, of the same index. -/
theorem isRegularlyVarying_survival (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψm : ∀ j, m < j → ψ j = 0) (hW : 0 < weightSum m ψ α) :
    IsRegularlyVarying (fun x => (P {ω | x < process m ψ Z (0 : ℕ) ω}).toReal) (-α) := by
  have := (exists_hasSpectralTailProcess_candidateExtremalIndex_eq hZ hind hident hZ0 hα hL
    hψ0 hψm hW).1.1
  simpa [abs_of_nonneg (process_nonneg hψ0 hZ0 _ _), measureReal_def] using this

/-- **Hill consistency for finite moving averages** `X_t = ∑_{i ≤ m} ψ_i Z_{t-i}` with `ψ ≥ 0`
and iid nonnegative noise with regularly varying tail of index `-α`: `H_{k(n),n} → 1/α` in
probability for `k → ∞`, `k/n → 0`. Through `tendstoInMeasure_hill_of_isMDependent`. -/
theorem tendstoInMeasure_hill (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψm : ∀ j, m < j → ψ j = 0) (hW : 0 < weightSum m ψ α) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => process m ψ Z i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  have hF : Measurable fun y : Fin (m + 1) → ℝ => ∑ j : Fin (m + 1), ψ j * y j :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _
  have hm : IsMDependent (fun n : ℕ => process m ψ Z n) m P := by
    have := isMDependent_slidingWindow hZ hind (fun j : Fin (m + 1) => -(j : ℤ)) hF
      (a := -m) (m := m) fun j => by have := j.isLt; constructor <;> omega
    rw [process_eq_slidingWindow]
    exact this
  exact tendstoInMeasure_hill_of_isMDependent (X := fun n : ℕ => process m ψ Z n)
    (fun n => measurable_process hZ n) hm (identDistrib hZ hind hident) hα
    (isRegularlyVarying_survival hZ hind hident hZ0 hα hL hψ0 hψm hW) hk hkn

end MovingAverage

end Examples

end ExtremeValueTheory
