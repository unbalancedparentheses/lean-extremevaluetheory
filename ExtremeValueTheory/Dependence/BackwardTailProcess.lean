/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Anticlustering
import ExtremeValueTheory.Dependence.TimeChange

/-!
# The backward half of the spectral tail process

`Dependence/Anticlustering.lean` only uses the forward half of anticlustering and proves
`Θ_t → 0` as `t → +∞`. Here we treat the backward half.

## Main definitions

* `BackwardAntiClusteringAt P X u r`: the backward half of `AntiClusteringAt`
  (times `-rₙ ≤ t ≤ -m`).

## Main results

* `HasSpectralTailProcess.tendsto_zero_of_backwardAntiClusteringAt`: backward anticlustering at a
  single level sequence `uₙ → ∞` with `rₙ → ∞` gives `Θ_{-t} → 0` almost surely as `t → ∞`
  (no stationarity).
* `HasSpectralTailProcess.tendsto_zero_of_antiClusteringAt`: two-sided anticlustering gives
  `Θ_t → 0` and `Θ_{-t} → 0` almost surely.
* `HasSpectralTailProcess.map_restrict_path_shift`: the tail-process form of the time-change
  formula for the whole path (not only finite windows), by uniqueness of measures on cylinders.
* `HasSpectralTailProcess.measure_firstExceedance_eq_lastExceedance`: for a stationary series
  whose tail process `Y = R Θ` vanishes at `±∞`,
  `P(|Y_k| ≤ 1 for all k ≤ -1) = P(|Y_k| ≤ 1 for all k ≥ 1)`.
* `HasSpectralTailProcess.candidateExtremalIndex_eq_measure_backward`: hence
  `ϑ = P(sup_{k ≤ -1} |Y_k| ≤ 1)`, the backward form of
  `candidateExtremalIndex_eq_measure` ([BS09, §4], [Planinić–Soulier 2018]).
* `HasSpectralTailProcess.candidateExtremalIndex_eq_measure_backward_of_antiClusteringAt`: the same
  under two-sided anticlustering.

The proof of the backward identity is the anchoring argument: a path vanishing at `±∞` with an
exceedance at `0` has a unique first and a unique last exceedance; splitting the event
"first exceedance at `0`" according to the last exceedance `j ≥ 0` and shifting the path by `j`
(the time-change formula) turns it into "last exceedance at `0`, first exceedance at `-j`".
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Backward anticlustering -/

section BackwardAC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℤ → Ω → ℝ} {u : ℕ → ℝ}
  {r : ℕ → ℕ}

/-- The backward half of `AntiClusteringAt`: only the times `-rₙ ≤ t ≤ -m` are controlled. -/
def BackwardAntiClusteringAt (P : Measure Ω) (X : ℤ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ᶠ n in atTop,
    P.real {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X (-t) ω|} ≤
      ε * P.real {ω | u n < |X 0 ω|}

theorem AntiClusteringAt.backward [IsFiniteMeasure P] (h : AntiClusteringAt P X u r) :
    BackwardAntiClusteringAt P X u r := by
  intro ε hε
  obtain ⟨m, hm⟩ := h ε hε
  refine ⟨m, hm.mono fun n hn => le_trans (measureReal_mono fun ω hω => ?_) hn⟩
  obtain ⟨h0, t, h1, h2, h3⟩ := hω
  have ht : 0 ≤ t := le_trans (Int.natCast_nonneg m) h1
  exact ⟨h0, -t, by rwa [abs_neg, abs_of_nonneg ht], by rwa [abs_neg, abs_of_nonneg ht], h3⟩

end BackwardAC

/-! ### Backward anticlustering forces `Θ_{-t} → 0` -/

section BackwardVanishing

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- **Backward anticlustering implies `Θ_{-t} → 0`** ([BS09, Proposition 4.2], [KS20, §6.1]).
The mirror image of `HasSpectralTailProcess.tendsto_zero_of_forwardAntiClusteringAt`: only the
spectral tail process, `uₙ → ∞`, `rₙ → ∞` and the backward anticlustering bound at the single
level sequence `uₙ` are used (no stationarity). -/
theorem HasSpectralTailProcess.tendsto_zero_of_backwardAntiClusteringAt (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hAC : BackwardAntiClusteringAt P X u r) :
    ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ (-(k : ℤ)) ω') atTop (𝓝 0) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q with hπ
  have hs : ∀ x : ℝ, MeasurableSet {ω | x < |X 0 ω|} := fun x =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX 0))
  -- the tail process exceeds `1` before time `-m` with small probability
  have step1 : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
      π {p | ∃ k : ℕ, m ≤ k ∧ 1 < |p.1 * Θ (-(k : ℤ)) p.2|} ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := hAC ε hε
    refine ⟨m, ?_⟩
    have hW : ∀ s : ℕ, π {p | ∃ t ∈ Finset.Icc (-(s : ℤ)) (-(m : ℤ)), 1 < |p.1 * Θ t p.2|} ≤
        ENNReal.ofReal ε := by
      intro s
      have key := (h.tendsto_cond_exists_lt hα hX hΘm (Finset.Icc (-(s : ℤ)) (-(m : ℤ)))).comp hu
      refine le_of_tendsto key ?_
      filter_upwards [hm, hr.eventually_ge_atTop s] with n hn hrn
      refine (measure_mono ?_).trans (cond_le_ofReal_of_measureReal_le (hs _) hε.le
        (A := {ω | ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X (-t) ω|}) hn)
      rintro ω ⟨t, ht, hlt⟩
      rw [Finset.mem_Icc] at ht
      have hrn' : (s : ℤ) ≤ r n := by exact_mod_cast hrn
      exact ⟨-t, by omega, by omega, by rwa [neg_neg]⟩
    have hmono : Monotone fun s : ℕ =>
        {p : ℝ × Ω' | ∃ t ∈ Finset.Icc (-(s : ℤ)) (-(m : ℤ)), 1 < |p.1 * Θ t p.2|} := by
      intro a b hab p ⟨t, ht, h1⟩
      refine ⟨t, ?_, h1⟩
      rw [Finset.mem_Icc] at ht ⊢
      have : (a : ℤ) ≤ b := by exact_mod_cast hab
      omega
    have hU : (⋃ s : ℕ,
        {p : ℝ × Ω' | ∃ t ∈ Finset.Icc (-(s : ℤ)) (-(m : ℤ)), 1 < |p.1 * Θ t p.2|}) =
        {p | ∃ k : ℕ, m ≤ k ∧ 1 < |p.1 * Θ (-(k : ℤ)) p.2|} := by
      ext p
      simp only [mem_iUnion, mem_ofPred_eq, Finset.mem_Icc]
      constructor
      · rintro ⟨s, t, ⟨h1, h2⟩, h3⟩
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = -(k : ℤ) := ⟨(-t).toNat, by omega⟩
        exact ⟨k, by omega, h3⟩
      · rintro ⟨k, hk, h3⟩
        exact ⟨k, -(k : ℤ), ⟨le_rfl, by omega⟩, h3⟩
    rw [← hU]
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hW
  -- scaling by the independent Pareto radius: `Θ` exceeds every level `v` rarely
  have step2 : ∀ v : ℝ, 0 < v → v ≤ 1 →
      Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ (-(k : ℤ)) ω'|}) = 0 := by
    intro v hv hv1
    have hc : paretoMeasure 1 α (Ioi (1 / v)) = ENNReal.ofReal (v ^ α) := by
      rw [paretoMeasure_one_Ioi hα (by rw [le_div_iff₀ hv]; linarith), one_div,
        Real.inv_rpow hv.le, Real.rpow_neg (by positivity), inv_inv]
    have hc0 : ENNReal.ofReal (v ^ α) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hv α)).ne'
    have hbound : ∀ ε : ℝ, 0 < ε →
        Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ (-(k : ℤ)) ω'|}) *
          ENNReal.ofReal (v ^ α) ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨m, hm⟩ := step1 ε hε
      calc Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ (-(k : ℤ)) ω'|}) * ENNReal.ofReal (v ^ α)
          ≤ Q {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ (-(k : ℤ)) ω'|} * ENNReal.ofReal (v ^ α) := by
            gcongr; exact iInter_subset _ m
        _ = π (Ioi (1 / v) ×ˢ {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ (-(k : ℤ)) ω'|}) := by
            rw [hπ, Measure.prod_prod, hc, mul_comm]
        _ ≤ π {p | ∃ k : ℕ, m ≤ k ∧ 1 < |p.1 * Θ (-(k : ℤ)) p.2|} := by
            refine measure_mono ?_
            rintro ⟨r', ω'⟩ ⟨hr', k, hk, hθ⟩
            refine ⟨k, hk, ?_⟩
            have hr' : 1 / v < r' := hr'
            have hr0 : 0 < r' := lt_trans (by positivity) hr'
            rw [abs_mul, abs_of_pos hr0]
            calc (1 : ℝ) = (1 / v) * v := by field_simp
              _ < r' * |Θ (-(k : ℤ)) ω'| := mul_lt_mul hr' hθ.le hv hr0.le
        _ ≤ ENNReal.ofReal ε := hm
    have h0 : Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ (-(k : ℤ)) ω'|}) *
        ENNReal.ofReal (v ^ α) = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
      rw [zero_add]
      simpa using hbound ε (by exact_mod_cast hε)
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact h0
    · exact absurd h0 hc0
  have hae : ∀ᵐ ω' ∂Q, ∀ j : ℕ,
      ω' ∉ ⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ 1 / ((j : ℝ) + 1) < |Θ (-(k : ℤ)) ω'|} := by
    rw [ae_all_iff]
    intro j
    refine measure_eq_zero_iff_ae_notMem.1 (step2 _ (by positivity) ?_)
    rw [div_le_one (by positivity)]
    linarith [j.cast_nonneg (α := ℝ)]
  filter_upwards [hae] with ω' hω'
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  have := hω' j
  simp only [mem_iInter, mem_ofPred_eq, not_forall, not_exists, not_and, not_lt] at this
  obtain ⟨m, hm⟩ := this
  refine ⟨m, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hm k hk).trans_lt hj

/-- **Two-sided anticlustering implies `Θ_t → 0` at both ends**: under `AntiClusteringAt P X u r`
with `uₙ → ∞` and `rₙ → ∞`, almost surely `Θ_t → 0` and `Θ_{-t} → 0` as `t → ∞`. No
stationarity is used. -/
theorem HasSpectralTailProcess.tendsto_zero_of_antiClusteringAt (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hAC : AntiClusteringAt P X u r) :
    ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ k ω') atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ => Θ (-(k : ℤ)) ω') atTop (𝓝 0) := by
  filter_upwards [h.tendsto_zero_of_forwardAntiClusteringAt hα hX hΘm hu hr hAC.forward,
    h.tendsto_zero_of_backwardAntiClusteringAt hα hX hΘm hu hr hAC.backward] with ω' h1 h2
  exact ⟨h1, h2⟩

end BackwardVanishing

/-! ### Anchoring: first and last exceedances of the tail process -/

section Anchoring

/-- Paths `z : ℤ → ℝ` whose last exceedance of the level `1` is at time `0`. -/
def lastExceedanceZero : Set (ℤ → ℝ) := {z | 1 < |z 0| ∧ ∀ k : ℤ, 0 < k → |z k| ≤ 1}

/-- Paths `z : ℤ → ℝ` whose first exceedance of the level `1` is at time `0`. -/
def firstExceedanceZero : Set (ℤ → ℝ) := {z | 1 < |z 0| ∧ ∀ k : ℤ, k < 0 → |z k| ≤ 1}

theorem measurableSet_lastExceedanceZero : MeasurableSet lastExceedanceZero := by
  have hm : ∀ k : ℤ, Measurable fun z : ℤ → ℝ => |z k| := fun k =>
    continuous_abs.measurable.comp (measurable_pi_apply k)
  have : lastExceedanceZero = {z : ℤ → ℝ | 1 < |z 0|} ∩ ⋂ k : ℤ, {z | 0 < k → |z k| ≤ 1} := by
    ext z; simp [lastExceedanceZero]
  rw [this]
  refine (measurableSet_lt measurable_const (hm 0)).inter (MeasurableSet.iInter fun k => ?_)
  by_cases hk : 0 < k
  · simpa [hk] using measurableSet_le (hm k) measurable_const
  · simp [hk]

theorem measurableSet_firstExceedanceZero : MeasurableSet firstExceedanceZero := by
  have hm : ∀ k : ℤ, Measurable fun z : ℤ → ℝ => |z k| := fun k =>
    continuous_abs.measurable.comp (measurable_pi_apply k)
  have : firstExceedanceZero = {z : ℤ → ℝ | 1 < |z 0|} ∩ ⋂ k : ℤ, {z | k < 0 → |z k| ≤ 1} := by
    ext z; simp [firstExceedanceZero]
  rw [this]
  refine (measurableSet_lt measurable_const (hm 0)).inter (MeasurableSet.iInter fun k => ?_)
  by_cases hk : k < 0
  · simpa [hk] using measurableSet_le (hm k) measurable_const
  · simp [hk]

/-- Time reversal exchanges first and last exceedances at `0`. -/
theorem reverse_mem_firstExceedanceZero {z : ℤ → ℝ} :
    (fun t => z (-t)) ∈ firstExceedanceZero ↔ z ∈ lastExceedanceZero := by
  simp only [firstExceedanceZero, lastExceedanceZero, mem_ofPred_eq, neg_zero]
  constructor
  · rintro ⟨h0, hk⟩
    refine ⟨h0, fun k hk' => ?_⟩
    simpa using hk (-k) (by omega)
  · rintro ⟨h0, hk⟩
    exact ⟨h0, fun k hk' => hk (-k) (by omega)⟩

/-- Time reversal of a shifted path. -/
theorem reverse_shift_mem_lastExceedanceZero {z : ℤ → ℝ} (j : ℤ) :
    (fun t => z (-(t + j))) ∈ lastExceedanceZero ↔ (fun t => z (t - j)) ∈ firstExceedanceZero := by
  simp only [firstExceedanceZero, lastExceedanceZero, mem_ofPred_eq, zero_add, zero_sub]
  constructor
  · rintro ⟨h0, hk⟩
    refine ⟨h0, fun k hk' => ?_⟩
    have := hk (-k) (by omega)
    rwa [show -(-k + j) = k - j by ring] at this
  · rintro ⟨h0, hk⟩
    refine ⟨h0, fun k hk' => ?_⟩
    have := hk (-k) (by omega)
    rwa [show -k - j = -(k + j) by ring] at this

/-- **Decomposition according to the last exceedance.** If a family of paths `Z b` is eventually
at most `1` in absolute value (forward in time) for almost every `b`, then every event `A` of
paths with an exceedance at time `0` splits according to the time `j ≥ 0` of the last
exceedance. -/
theorem measure_eq_tsum_lastExceedance {β : Type*} {mβ : MeasurableSpace β} (ν : Measure β)
    {Z : β → ℤ → ℝ} (hZ : Measurable Z) {A : Set (ℤ → ℝ)} (hA : MeasurableSet A)
    (hA0 : A ⊆ {z | 1 < |z 0|})
    (hlim : ∀ᵐ b ∂ν, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → |Z b k| ≤ 1) :
    ν (Z ⁻¹' A) =
      ∑' j : ℕ, ν (Z ⁻¹' A ∩ {b | (fun t => Z b (t + j)) ∈ lastExceedanceZero}) := by
  classical
  set S : ℕ → Set β := fun j => Z ⁻¹' A ∩ {b | (fun t => Z b (t + j)) ∈ lastExceedanceZero}
  have hshift : ∀ j : ℕ, Measurable fun b t => Z b (t + j) := fun j =>
    measurable_pi_iff.2 fun t => (measurable_pi_apply _).comp hZ
  have hmeas : ∀ j, MeasurableSet (S j) := fun j =>
    (hZ hA).inter (hshift j measurableSet_lastExceedanceZero)
  have hkey : ∀ i j : ℕ, i < j → ∀ b, b ∈ S i → b ∈ S j → False := by
    intro i j hij b hi hj
    have h1 : ∀ k : ℤ, 0 < k → |Z b (k + i)| ≤ 1 := hi.2.2
    have h2 : 1 < |Z b (0 + j)| := hj.2.1
    have := h1 ((j : ℤ) - i) (by omega)
    rw [sub_add_cancel] at this
    rw [zero_add] at h2
    linarith
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    refine Set.disjoint_left.2 fun b hi hj => ?_
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkey i j h b hi hj
    · exact hkey j i h b hj hi
  have hcover : Z ⁻¹' A =ᵐ[ν] ⋃ j, S j := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hlim] with b ⟨N, hN⟩
    refine ⟨fun hbA => ?_, fun hb => ?_⟩
    · have h0 : 1 < |Z b 0| := hA0 hbA
      set T := (Finset.range N).filter (fun k : ℕ => 1 < |Z b k|)
      have hN0 : 0 < N := by
        by_contra hc
        have := hN 0 (by omega)
        simp only [Nat.cast_zero] at this
        linarith
      have h0T : 0 ∈ T := Finset.mem_filter.2 ⟨Finset.mem_range.2 hN0, by simpa using h0⟩
      set j := T.max' ⟨0, h0T⟩
      have hjT : j ∈ T := Finset.max'_mem _ _
      refine mem_iUnion.2 ⟨j, hbA, ?_, fun k hk => ?_⟩
      · simpa using (Finset.mem_filter.1 hjT).2
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, by omega⟩
        have hm : ((m : ℤ) + j) = ((m + j : ℕ) : ℤ) := by push_cast; ring
        show |Z b ((m : ℤ) + j)| ≤ 1
        rw [hm]
        by_contra hc
        rw [not_le] at hc
        by_cases hmN : N ≤ m + j
        · exact absurd (hN _ hmN) (not_le.2 hc)
        · have hmT : m + j ∈ T := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hc⟩
          have := T.le_max' _ hmT
          have : (0 : ℤ) < m := hk
          omega
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hb
      exact hj.1
  rw [measure_congr hcover, measure_iUnion hdisj hmeas]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- **Time change for the whole tail process** ([BS09, Theorem 3.1] with `ε = 1`): for a
stationary series, writing `Y_t = R Θ_t`, the law of the shifted path `(Y_{t-i})_{t ∈ ℤ}` on
`{|Y_{-i}| > 1}` equals the law of the path `(Y_t)_{t ∈ ℤ}` on `{|Y_i| > 1}`. Both are finite
measures on `ℝ^ℤ` with the product σ-algebra, agreeing on cylinders by
`HasSpectralTailProcess.map_restrict_tailProcess_shift`. -/
theorem HasSpectralTailProcess.map_restrict_path_shift (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) (i : ℤ) :
    (((paretoMeasure 1 α).prod Q).restrict {p | 1 < |p.1 * Θ (-i) p.2|}).map
        (fun p (t : ℤ) => p.1 * Θ (t - i) p.2) =
      (((paretoMeasure 1 α).prod Q).restrict {p | 1 < |p.1 * Θ i p.2|}).map
        (fun p (t : ℤ) => p.1 * Θ t p.2) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hm1 : Measurable fun p : ℝ × Ω' => fun t : ℤ => p.1 * Θ (t - i) p.2 :=
    measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
  have hm2 : Measurable fun p : ℝ × Ω' => fun t : ℤ => p.1 * Θ t p.2 :=
    measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
  have hcyl : ∀ C ∈ measurableCylinders (fun _ : ℤ => ℝ),
      (((paretoMeasure 1 α).prod Q).restrict {p | 1 < |p.1 * Θ (-i) p.2|}).map
        (fun p (t : ℤ) => p.1 * Θ (t - i) p.2) C =
      (((paretoMeasure 1 α).prod Q).restrict {p | 1 < |p.1 * Θ i p.2|}).map
        (fun p (t : ℤ) => p.1 * Θ t p.2) C := by
    intro C hC
    obtain ⟨S, B, hB, rfl⟩ := (mem_measurableCylinders C).1 hC
    have key := congrArg (fun m : Measure (S → ℝ) => m B)
      (h.map_restrict_tailProcess_shift hα hX hΘm hstat i S one_pos)
    simp only [div_one, Real.one_rpow, Real.toNNReal_one, one_smul, one_mul] at key
    have hw1 : Measurable fun p : ℝ × Ω' => fun t : S => p.1 * Θ (t - i) p.2 :=
      measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
    have hw2 : Measurable fun p : ℝ × Ω' => fun t : S => p.1 * Θ t p.2 :=
      measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
    rw [Measure.map_apply hw1 hB, Measure.map_apply hw2 hB] at key
    rw [Measure.map_apply hm1 hB.cylinder, Measure.map_apply hm2 hB.cylinder]
    exact key
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders hcyl ?_
  have := hcyl _ (cylinder_mem_measurableCylinders (∅ : Finset ℤ) univ MeasurableSet.univ)
  rwa [cylinder_univ] at this

/-- **First and last exceedances have the same probability** (anchoring, [BS09, §4],
[Planinić–Soulier 2018]). For a stationary series whose spectral tail process vanishes at both
ends, the tail process `Y = R Θ` satisfies
`P(|Y_0| > 1, |Y_k| ≤ 1 for all k < 0) = P(|Y_0| > 1, |Y_k| ≤ 1 for all k > 0)`. -/
theorem HasSpectralTailProcess.measure_firstExceedance_eq_lastExceedance (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    (hfwd : ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ k ω') atTop (𝓝 0))
    (hbwd : ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ (-(k : ℤ)) ω') atTop (𝓝 0)) :
    ((paretoMeasure 1 α).prod Q) {p | (fun t => p.1 * Θ t p.2) ∈ firstExceedanceZero} =
      ((paretoMeasure 1 α).prod Q) {p | (fun t => p.1 * Θ t p.2) ∈ lastExceedanceZero} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q with hπ
  have hY : Measurable fun p : ℝ × Ω' => fun t : ℤ => p.1 * Θ t p.2 :=
    measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
  have hYr : Measurable fun p : ℝ × Ω' => fun t : ℤ => p.1 * Θ (-t) p.2 :=
    measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
  have hev : ∀ f : ℕ → ℤ, (∀ᵐ ω' ∂Q, Tendsto (fun k => Θ (f k) ω') atTop (𝓝 0)) →
      ∀ᵐ p ∂π, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → |p.1 * Θ (f k) p.2| ≤ 1 := by
    intro f hf
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hf] with p hp
    have h2 : Tendsto (fun k => |p.1 * Θ (f k) p.2|) atTop (𝓝 0) := by
      simpa using (hp.const_mul p.1).abs
    exact eventually_atTop.1 (h2.eventually (ge_mem_nhds one_pos))
  have hA0 : firstExceedanceZero ⊆ {z : ℤ → ℝ | 1 < |z 0|} := fun z hz => hz.1
  -- split the first exceedance at `0` by the last exceedance `j ≥ 0`
  have hA := measure_eq_tsum_lastExceedance π hY measurableSet_firstExceedanceZero hA0
    (hev (fun k => (k : ℤ)) hfwd)
  -- split the last exceedance at `0` by the first exceedance `-j ≤ 0`, via time reversal
  have hB := measure_eq_tsum_lastExceedance π hYr measurableSet_firstExceedanceZero hA0
    (hev (fun k => -(k : ℤ)) hbwd)
  have e1 : (fun p : ℝ × Ω' => fun t : ℤ => p.1 * Θ (-t) p.2) ⁻¹' firstExceedanceZero =
      {p | (fun t => p.1 * Θ t p.2) ∈ lastExceedanceZero} := by
    ext p
    exact reverse_mem_firstExceedanceZero (z := fun t => p.1 * Θ t p.2)
  have e2 : ∀ j : ℕ, {p : ℝ × Ω' | (fun t => p.1 * Θ (-(t + j)) p.2) ∈ lastExceedanceZero} =
      {p | (fun t => p.1 * Θ (t - j) p.2) ∈ firstExceedanceZero} := fun j => by
    ext p
    exact reverse_shift_mem_lastExceedanceZero (z := fun t => p.1 * Θ t p.2) j
  simp only [e1] at hB
  simp only [e2] at hB
  -- the shift identity term by term
  have hC : ∀ j : ℕ,
      π ({p | (fun t => p.1 * Θ t p.2) ∈ firstExceedanceZero} ∩
          {p | (fun t => p.1 * Θ (t + j) p.2) ∈ lastExceedanceZero}) =
        π ({p | (fun t => p.1 * Θ t p.2) ∈ lastExceedanceZero} ∩
          {p | (fun t => p.1 * Θ (t - j) p.2) ∈ firstExceedanceZero}) := by
    intro j
    set C : Set (ℤ → ℝ) := lastExceedanceZero ∩
      (fun z t => z (t - j)) ⁻¹' firstExceedanceZero
    have hback : Measurable fun (z : ℤ → ℝ) (t : ℤ) => z (t - j) :=
      measurable_pi_iff.2 fun t => measurable_pi_apply _
    have hCm : MeasurableSet C :=
      measurableSet_lastExceedanceZero.inter (hback measurableSet_firstExceedanceZero)
    have hm1 : Measurable fun p : ℝ × Ω' => fun t : ℤ => p.1 * Θ (t - -(j : ℤ)) p.2 :=
      measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
    have key := congrArg (fun m : Measure (ℤ → ℝ) => m C)
      (h.map_restrict_path_shift hα hX hΘm hstat (-(j : ℤ)))
    rw [Measure.map_apply hm1 hCm, Measure.map_apply hY hCm, Measure.restrict_apply (hm1 hCm),
      Measure.restrict_apply (hY hCm)] at key
    calc _ = π ((fun p : ℝ × Ω' => fun t : ℤ => p.1 * Θ (t - -(j : ℤ)) p.2) ⁻¹' C ∩
          {p | 1 < |p.1 * Θ (-(-(j : ℤ))) p.2|}) := by
          congr 1
          ext p
          simp only [C, mem_inter_iff, mem_preimage, mem_ofPred_eq, sub_neg_eq_add, neg_neg,
            sub_add_cancel]
          constructor
          · rintro ⟨hF, hL⟩
            exact ⟨⟨hL, hF⟩, by simpa using hL.1⟩
          · rintro ⟨⟨hL, hF⟩, -⟩
            exact ⟨hF, hL⟩
      _ = _ := key
      _ = _ := by
          congr 1
          ext p
          simp only [C, mem_inter_iff, mem_preimage, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨hL, hF⟩, -⟩
            exact ⟨hL, hF⟩
          · rintro ⟨hL, hF⟩
            exact ⟨⟨hL, hF⟩, by simpa using hF.1⟩
  refine hA.trans ((tsum_congr fun j => ?_).trans hB.symm)
  exact hC j

/-- **The backward form of the candidate extremal index** ([BS09, §4], [Planinić–Soulier 2018]).
For a stationary series whose spectral tail process vanishes at both ends,
`ϑ = P(sup_{k ≤ -1} |Y_k| ≤ 1)` with `Y = R Θ` the tail process; compare
`candidateExtremalIndex_eq_measure` (`ϑ = P(sup_{k ≥ 1} |Y_k| ≤ 1)`, no hypotheses). -/
theorem HasSpectralTailProcess.candidateExtremalIndex_eq_measure_backward (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    (hfwd : ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ k ω') atTop (𝓝 0))
    (hbwd : ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ (-(k : ℤ)) ω') atTop (𝓝 0)) :
    candidateExtremalIndex Q Θ α =
      ((paretoMeasure 1 α).prod Q) {p | ∀ k : ℕ, |p.1 * Θ (-((k : ℤ) + 1)) p.2| ≤ 1} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hgood : ∀ᵐ p ∂((paretoMeasure 1 α).prod Q), 1 < p.1 ∧ |Θ 0 p.2| = 1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure,
      Measure.quasiMeasurePreserving_snd.ae (h.ae_abs_eq_one hΘm (hX 0))] with p h1 h2
    exact ⟨h1, h2⟩
  rw [candidateExtremalIndex_eq_measure hα hΘm (h.ae_abs_eq_one hΘm (hX 0))]
  have hL : ((paretoMeasure 1 α).prod Q) {p | ∀ k : ℕ, p.1 * |Θ (k + 1) p.2| ≤ 1} =
      ((paretoMeasure 1 α).prod Q) {p | (fun t => p.1 * Θ t p.2) ∈ lastExceedanceZero} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hgood] with p ⟨h1, h2⟩
    have hp0 : 0 < p.1 := one_pos.trans h1
    simp only [lastExceedanceZero, mem_ofPred_eq, abs_mul, abs_of_pos hp0, h2, mul_one]
    constructor
    · intro hk
      refine ⟨h1, fun k hk' => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
      exact hk m
    · rintro ⟨-, hk⟩ m
      exact hk _ (by omega)
  have hF : ((paretoMeasure 1 α).prod Q) {p | ∀ k : ℕ, |p.1 * Θ (-((k : ℤ) + 1)) p.2| ≤ 1} =
      ((paretoMeasure 1 α).prod Q) {p | (fun t => p.1 * Θ t p.2) ∈ firstExceedanceZero} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hgood] with p ⟨h1, h2⟩
    have hp0 : 0 < p.1 := one_pos.trans h1
    simp only [firstExceedanceZero, mem_ofPred_eq]
    have h0 : 1 < |p.1 * Θ 0 p.2| := by rw [abs_mul, abs_of_pos hp0, h2, mul_one]; exact h1
    constructor
    · intro hk
      refine ⟨h0, fun k hk' => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -((m : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
      exact hk m
    · rintro ⟨-, hk⟩ m
      exact hk _ (by omega)
  rw [hL, hF, h.measure_firstExceedance_eq_lastExceedance hα hX hΘm hstat hfwd hbwd]

/-- **Two-sided anticlustering gives the backward identity** `ϑ = P(sup_{k ≤ -1} |Y_k| ≤ 1)`
for a stationary series, combining `tendsto_zero_of_antiClusteringAt` with
`candidateExtremalIndex_eq_measure_backward`. -/
theorem HasSpectralTailProcess.candidateExtremalIndex_eq_measure_backward_of_antiClusteringAt
    (hα : 0 < α) (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hAC : AntiClusteringAt P X u r) :
    candidateExtremalIndex Q Θ α =
      ((paretoMeasure 1 α).prod Q) {p | ∀ k : ℕ, |p.1 * Θ (-((k : ℤ) + 1)) p.2| ≤ 1} := by
  have hlim := h.tendsto_zero_of_antiClusteringAt hα hX hΘm hu hr hAC
  exact h.candidateExtremalIndex_eq_measure_backward hα hX hΘm hstat
    (hlim.mono fun _ h => h.1) (hlim.mono fun _ h => h.2)

end Anchoring

end ExtremeValueTheory
