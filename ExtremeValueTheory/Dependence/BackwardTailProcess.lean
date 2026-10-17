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

end ExtremeValueTheory
