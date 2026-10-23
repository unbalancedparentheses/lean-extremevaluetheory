/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.StationaryWindows
import ExtremeValueTheory.Dependence.ExtremalIndex
import ExtremeValueTheory.Dependence.Anticlustering.Basic

/-!
# The block exceedance ratio converges to the candidate extremal index

The first-exceedance decomposition
`P(M_r > x) = ∑_{k < r} P(|X_0| > x, max_{0 < t ≤ k} |X_t| ≤ x)` of a stationary series, and the
limit `P(M_{rₙ} > uₙ) / (rₙ P(|X_0| > uₙ)) → ϑ` under stationarity, `uₙ → ∞`, `rₙ → ∞` and
forward anticlustering at `uₙ`.

## Main results

* `HasShiftInvariantWindows.measureReal_exists_lt_eq_sum`: **Decomposition of a block exceedance**
  ([BS09, §4], [KS20, §7.5]): for a stationary series, `P(max_{0 ≤ t < r} |X_t| > x) = ∑_{k < r}
  P(|X_0| > x, max_{0 < t ≤ k} |X_t| ≤ x)`.
* `HasSpectralTailProcess.tendsto_blockRatio`: **The cluster ratio converges to the candidate
  extremal index** ([BS09, §4], [KS20, §7.5]): `P(max_{0 ≤ t < rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ))
  → ϑ`.

This file is part of the proof in `ExtremeValueTheory.Dependence.Anticlustering`.

## References

* B. Basrak and J. Segers, *Regularly varying multivariate time series*, Stoch. Proc. Appl. 119
  (2009), §4 [BS09].
* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020), §6.1 and §7.5 [KS20].
* H. Planinić and P. Soulier, *The tail process revisited*, Extremes 21 (2018).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Blocks: the first-exceedance decomposition -/

section Blocks

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ℤ → Ω → ℝ}

/-- **Decomposition of a block exceedance** ([BS09, §4], [KS20, §7.5]): for a stationary series,
`P(max_{0 ≤ t < r} |X_t| > x) = ∑_{k < r} P(|X_0| > x, max_{0 < t ≤ k} |X_t| ≤ x)`.
This is the classical decomposition by the first exceedance in the block, made exact by
stationarity: the event `{max_{0 ≤ t < r + 1} |X_t| > x}` splits into an exceedance in
`{1, …, r}` (probability `P(max_{0 ≤ t < r} |X_t| > x)` after a shift by one) and the event that
`0` is the only exceedance time up to `r`. Uses only stationarity (shift by `1` of the windows
`{0, …, r - 1}`). -/
theorem HasShiftInvariantWindows.measureReal_exists_lt_eq_sum (hstat : HasShiftInvariantWindows P X)
    (hX : ∀ t, Measurable (X t)) (r : ℕ) (x : ℝ) :
    P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) r, x < |X t ω|} =
      ∑ k ∈ Finset.range r,
        P.real {ω | x < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) k, |X t ω| ≤ x} := by
  have hXa : ∀ t, Measurable fun ω => |X t ω| := fun t => continuous_abs.measurable.comp (hX t)
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ← ih]
    set W := Finset.Ico (0 : ℤ) r with hW
    have hB : MeasurableSet {y : W → ℝ | ∃ t, x < |y t|} := by
      simp only [ofPred_exists]
      exact MeasurableSet.iUnion fun t => measurableSet_lt measurable_const
        (continuous_abs.measurable.comp (measurable_pi_apply t))
    have hshift := congrArg (fun μ : Measure (W → ℝ) => μ.real {y | ∃ t, x < |y t|}) (hstat 1 W)
    rw [map_measureReal_apply (measurable_pi_iff.2 fun t => hX _) hB,
      map_measureReal_apply (measurable_pi_iff.2 fun t => hX _) hB] at hshift
    have e1 : (fun ω (t : W) => X (t + 1) ω) ⁻¹' {y | ∃ t, x < |y t|} =
        {ω | ∃ t ∈ W, x < |X (t + 1) ω|} := by
      ext ω; simp
    have e2 : (fun ω (t : W) => X t ω) ⁻¹' {y | ∃ t, x < |y t|} =
        {ω | ∃ t ∈ W, x < |X t ω|} := by
      ext ω; simp
    rw [e1, e2] at hshift
    rw [← hshift]
    have hD : MeasurableSet {ω | x < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) r, |X t ω| ≤ x} := by
      simp only [ofPred_and, ofPred_forall]
      exact (measurableSet_lt measurable_const (hXa 0)).inter (MeasurableSet.iInter fun t =>
        MeasurableSet.iInter fun _ => measurableSet_le (hXa t) measurable_const)
    have hdisj : Disjoint {ω | ∃ t ∈ W, x < |X (t + 1) ω|}
        {ω | x < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) r, |X t ω| ≤ x} := by
      rw [Set.disjoint_left]
      rintro ω ⟨t, ht, hlt⟩ ⟨-, hall⟩
      rw [hW, Finset.mem_Ico] at ht
      have := hall (t + 1) (Finset.mem_Ioc.2 ⟨by omega, by omega⟩)
      linarith
    have hunion : {ω | ∃ t ∈ Finset.Ico (0 : ℤ) ((r + 1 : ℕ) : ℤ), x < |X t ω|} =
        {ω | ∃ t ∈ W, x < |X (t + 1) ω|} ∪
          {ω | x < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) r, |X t ω| ≤ x} := by
      ext ω
      simp only [mem_union, mem_ofPred_eq, hW, Finset.mem_Ico, Finset.mem_Ioc]
      constructor
      · rintro ⟨t, ⟨h0, h1⟩, hlt⟩
        by_cases hex : ∃ s : ℤ, (0 < s ∧ s ≤ r) ∧ x < |X s ω|
        · obtain ⟨s, hs, hlt'⟩ := hex
          left
          exact ⟨s - 1, ⟨by omega, by omega⟩, by simpa using hlt'⟩
        · right
          push Not at hex
          refine ⟨?_, fun s hs => hex s hs⟩
          rcases eq_or_lt_of_le h0 with rfl | hpos
          · exact hlt
          · exact absurd hlt (not_lt.2 (hex t ⟨hpos, by push_cast at h1; omega⟩))
      · rintro (⟨t, ⟨h0, h1⟩, hlt⟩ | ⟨h0, -⟩)
        · exact ⟨t + 1, ⟨by omega, by push_cast; omega⟩, hlt⟩
        · exact ⟨0, ⟨le_rfl, by positivity⟩, h0⟩
    rw [hunion, measureReal_union hdisj hD]

end Blocks

/-! ### The block exceedance ratio converges to `ϑ` -/

section Ratio

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

omit [IsProbabilityMeasure P] in
theorem cond_toReal_eq {s : Set Ω} (hs : MeasurableSet s) (A : Set Ω) :
    (P[|s] A).toReal = P.real (s ∩ A) / P.real s := by
  rw [cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
  rfl

/-- The candidate extremal index is the limit of the finite-horizon probabilities
`ϑ_k = P(|Y_t| ≤ 1 for 0 < t ≤ k)`, `Y_t = R Θ_t` (continuity from above). Uses only `α > 0`,
measurability and `|Θ_0| = 1` almost surely. -/
theorem tendsto_measureReal_forall_le_candidateExtremalIndex (hα : 0 < α)
    (hΘm : ∀ t, Measurable (Θ t)) (h0 : ∀ᵐ ω' ∂Q, |Θ 0 ω'| = 1) :
    Tendsto (fun k : ℕ => ((paretoMeasure 1 α).prod Q).real
        {p | ∀ t ∈ Finset.Ioc (0 : ℤ) k, |p.1 * Θ t p.2| ≤ 1}) atTop
      (𝓝 (candidateExtremalIndex Q Θ α).toReal) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q
  have hπ1 : ∀ᵐ p ∂π, 1 < p.1 := Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure
  have hϑ : candidateExtremalIndex Q Θ α = π {p | ∀ k : ℕ, |p.1 * Θ (k + 1) p.2| ≤ 1} := by
    rw [candidateExtremalIndex_eq_measure hα hΘm h0]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hπ1] with p hp
    simp only [abs_mul, abs_of_pos (one_pos.trans hp)]
  set a : ℕ → Set (ℝ × Ω') := fun k => {p | ∀ t ∈ Finset.Ioc (0 : ℤ) k, |p.1 * Θ t p.2| ≤ 1}
  have hf : ∀ t : ℤ, Measurable fun p : ℝ × Ω' => |p.1 * Θ t p.2| := fun t =>
    continuous_abs.measurable.comp (measurable_radial_mul_spectral hΘm t)
  have hma : ∀ k, MeasurableSet (a k) := fun k => by
    simp only [a, ofPred_forall]
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
      measurableSet_le (hf t) measurable_const
  have hanti : Antitone a := fun m n hmn p hp t ht =>
    hp t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast hmn) ht)
  have hlim := tendsto_measure_iInter_atTop (μ := π) (fun k => (hma k).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hinter : (⋂ k, a k) = {p | ∀ k : ℕ, |p.1 * Θ (k + 1) p.2| ≤ 1} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, a, Finset.mem_Ioc]
    constructor
    · intro hp k
      exact_mod_cast hp (k + 1) ((k : ℤ) + 1) ⟨by omega, by push_cast; omega⟩
    · intro hp n t ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = (k : ℤ) + 1 := ⟨(t - 1).toNat, by omega⟩
      exact_mod_cast hp k
  rw [hinter, ← hϑ] at hlim
  exact (ENNReal.tendsto_toReal (candidateExtremalIndex_le_one hα.le h0 |>.trans_lt
    ENNReal.one_lt_top).ne).comp hlim

/-- **The cluster ratio converges to the candidate extremal index** ([BS09, §4], [KS20, §7.5]):
`P(max_{0 ≤ t < rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ)) → ϑ`.

Hypotheses actually used: stationarity (`HasShiftInvariantWindows`, only for the first-exceedance
decomposition), the spectral tail process, `uₙ → ∞`, `rₙ → ∞`, and the *forward* anticlustering
bound at the single level sequence `uₙ`. Neither `rₙ / n → 0` nor any mixing condition is
needed for this step. -/
theorem HasSpectralTailProcess.tendsto_blockRatio (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (hstat : HasShiftInvariantWindows P X)
    (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hAC : ForwardAntiClusteringAt P X u r) :
    Tendsto (fun n => P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} /
        (r n * P.real {ω | u n < |X 0 ω|})) atTop
      (𝓝 (candidateExtremalIndex Q Θ α).toReal) := by
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
  have hDS : ∀ n k, D n k ⊆ S n := fun n k ω hω => hω.1
  have hq0 : ∀ n k, 0 ≤ q n k := fun n k => div_nonneg measureReal_nonneg measureReal_nonneg
  have hq1 : ∀ n k, q n k ≤ 1 := fun n k =>
    div_le_one_of_le₀ (measureReal_mono (hDS n k)) measureReal_nonneg
  have hqanti : ∀ n m k, m ≤ k → q n k ≤ q n m := fun n m k hmk =>
    div_le_div_of_nonneg_right (measureReal_mono fun ω hω =>
      ⟨hω.1, fun t ht => hω.2 t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast hmk) ht)⟩)
      measureReal_nonneg
  -- the ratio is the average of the `q n k`
  have hratio : ∀ n, P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} /
      (r n * P.real {ω | u n < |X 0 ω|}) = (∑ k ∈ Finset.range (r n), q n k) / r n := by
    intro n
    rw [hstat.measureReal_exists_lt_eq_sum hX, div_mul_eq_div_div_swap, Finset.sum_div]
  -- the limits of the `q n k`
  have hqlim : ∀ k, Tendsto (fun n => q n k) atTop (𝓝 (θk k)) := by
    intro k
    have key := (h.tendsto_cond_forall_le hα hX hΘm (Finset.Ioc (0 : ℤ) k)).comp hu
    have key' := (ENNReal.tendsto_toReal (measure_ne_top π _)).comp key
    refine key'.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [cond_toReal_eq (hs _)]
    rfl
  have hθlim := tendsto_measureReal_forall_le_candidateExtremalIndex hα hΘm
    (h.ae_abs_eq_one hΘm (hX 0))
  -- anticlustering controls the `q n k` uniformly in `m ≤ k ≤ rₙ`
  have hqAC : ∀ ε : ℝ, 0 < ε → ∀ m₀ : ℕ, ∃ m ≥ m₀, ∀ᶠ n in atTop,
      ∀ k, m ≤ k → k ≤ r n → q n m - q n k ≤ ε := by
    intro ε hε m₀
    obtain ⟨m, hm, hev⟩ := hAC.exists_ge hε m₀
    refine ⟨m, hm, hev.mono fun n hn k hmk hkr => ?_⟩
    have hsub : D n m ⊆ D n k ∪ {ω | u n < |X 0 ω| ∧
        ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X t ω|} := by
      intro ω hω
      by_cases hk : ω ∈ D n k
      · exact Or.inl hk
      · right
        refine ⟨hω.1, ?_⟩
        simp only [D, mem_ofPred_eq, not_and, not_forall, not_le] at hk
        obtain ⟨t, ht, hlt⟩ := hk hω.1
        rw [Finset.mem_Ioc] at ht
        refine ⟨t, ?_, ht.2.trans (by exact_mod_cast hkr), hlt⟩
        by_contra hcon
        rw [not_le] at hcon
        exact absurd (hω.2 t (Finset.mem_Ioc.2 ⟨ht.1, by omega⟩)) (not_le.2 hlt)
    have h1 := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
    rw [show q n m - q n k = (P.real (D n m) - P.real (D n k)) / P.real (S n) by ring]
    exact div_le_of_le_mul₀ measureReal_nonneg hε.le (by linarith)
  -- the squeeze
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := δ / 5 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨m₁, hm₁⟩ := (Metric.tendsto_atTop.1 hθlim) ε hε
  obtain ⟨m, hm, hev⟩ := hqAC ε hε m₁
  have hmr : Tendsto (fun n => (m : ℝ) / r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and ((hqlim m).eventually (Metric.ball_mem_nhds _ hε)
    |>.and ((hmr.eventually (gt_mem_nhds hε)).and (hr.eventually_ge_atTop (m + 1)))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hAn, hqn, hmrn, hrn⟩ := hN n hn
  have hr0 : (0 : ℝ) < r n := by exact_mod_cast (show 0 < r n by omega)
  rw [hratio, Real.dist_eq]
  -- `|avg - q n m| ≤ m / rₙ + ε`
  have hsum : ∑ k ∈ Finset.range (r n), |q n k - q n m| ≤ m + r n * ε := by
    rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ r n by omega)]
    have h1 : ∑ k ∈ Finset.range m, |q n k - q n m| ≤ m := by
      calc _ ≤ ∑ _k ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
            rw [abs_le]; constructor <;> linarith [hq0 n k, hq1 n k, hq0 n m, hq1 n m]
        _ = m := by simp
    have h2 : ∑ k ∈ Finset.Ico m (r n), |q n k - q n m| ≤ r n * ε := by
      calc _ ≤ ∑ _k ∈ Finset.Ico m (r n), ε := Finset.sum_le_sum fun k hk => by
            rw [Finset.mem_Ico] at hk
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hqanti n m k hk.1))]
            exact hAn k hk.1 hk.2.le
        _ = (r n - m : ℕ) * ε := by simp
        _ ≤ r n * ε := by gcongr; exact_mod_cast Nat.sub_le _ _
    linarith
  have havg : |(∑ k ∈ Finset.range (r n), q n k) / r n - q n m| ≤ m / r n + ε := by
    have e : (∑ k ∈ Finset.range (r n), q n k) / r n - q n m =
        (∑ k ∈ Finset.range (r n), (q n k - q n m)) / r n := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [e, abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    calc |∑ k ∈ Finset.range (r n), (q n k - q n m)|
        ≤ ∑ k ∈ Finset.range (r n), |q n k - q n m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ m + r n * ε := hsum
      _ = (m / r n + ε) * r n := by field_simp
  have h3 : |q n m - θk m| < ε := by rw [← Real.dist_eq]; exact hqn
  have h4 : |θk m - ϑ| < ε := by rw [← Real.dist_eq]; exact hm₁ m hm
  calc |(∑ k ∈ Finset.range (r n), q n k) / r n - ϑ|
      ≤ |(∑ k ∈ Finset.range (r n), q n k) / r n - q n m| + |q n m - θk m| + |θk m - ϑ| := by
        have := abs_sub_le ((∑ k ∈ Finset.range (r n), q n k) / r n) (q n m) ϑ
        have := abs_sub_le (q n m) (θk m) ϑ
        linarith
    _ < δ := by linarith

end Ratio

end ExtremeValueTheory
