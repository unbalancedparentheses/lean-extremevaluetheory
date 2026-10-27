/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.StationaryWindows
import ExtremeValueTheory.Dependence.ExtremalIndex

/-!
# Anticlustering conditions and the vanishing of the tail process

The anticlustering conditions `AntiClusteringAt`, `ForwardAntiClusteringAt` and `AntiClustering`
(the condition `AC(rₙ)` of [BS09, Condition 4.1], [KS20, §6.1]); convergence of conditional
window probabilities to those of the tail process `Y = R Θ`; and forward anticlustering at a
single level sequence forces the spectral tail process to vanish, `Θ_t → 0` a.s., hence `ϑ > 0`.

## Main definitions

* `AntiClusteringAt`: **Anticlustering along a level sequence** `uₙ` with block lengths `rₙ`: the
  conditional probability, given `|X_0| > uₙ`, of an exceedance of `uₙ` at some time `t` with `m ≤
  |t| ≤ rₙ` is eventually at most `ε`, for `m` large.
* `ForwardAntiClusteringAt`: The forward half of `AntiClusteringAt`: only the times `m ≤ t ≤ rₙ` are
  controlled.
* `AntiClustering`: **The anticlustering condition `AC(rₙ)`** ([BS09, Condition 4.1], [KS20, §6.1]):
  for every `x > 0`, `lim_{m → ∞} limsup_{n → ∞} P(max_{m ≤ |t| ≤ rₙ} |X_t| > aₙ x | |X_0| > aₙ x) =
  0`.

## Main results

* `HasSpectralTailProcess.tendsto_cond_forall_le`: **No exceedance in a window** ([BS09, §4]): for
  every finite window `W`, `P(|X_t| ≤ x for all t ∈ W | |X_0| > x) → P(|Y_t| ≤ 1 for all t ∈ W)` as
  `x → ∞`, where `Y_t = R Θ_t` is the tail process.
* `HasSpectralTailProcess.tendsto_cond_exists_lt`: **An exceedance in a window** ([BS09, §4]): for
  every finite window `W`, `P(|X_t| > x for some t ∈ W | |X_0| > x) → P(|Y_t| > 1 for some t ∈ W)`
  as `x → ∞`.
* `HasSpectralTailProcess.tendsto_zero_of_forwardAntiClusteringAt`: **Anticlustering implies `Θ_t →
  0`** ([BS09, Proposition 4.2], [KS20, §6.1]).
* `HasSpectralTailProcess.candidateExtremalIndex_pos_of_antiClustering`: **`AC(rₙ)` implies `Θ_t →
  0` and `ϑ > 0`** in the normalization of [BS09, §4] and [KS20, §6.1]: `n P(|X_0| > aₙ) → 1`, `rₙ →
  ∞`, and `AC(rₙ)`.

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

/-! ### Anticlustering conditions -/

section Defs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℤ → Ω → ℝ} {u : ℕ → ℝ}
  {r : ℕ → ℕ}

/-- **Anticlustering along a level sequence** `uₙ` with block lengths `rₙ`: the conditional
probability, given `|X_0| > uₙ`, of an exceedance of `uₙ` at some time `t` with `m ≤ |t| ≤ rₙ`
is eventually at most `ε`, for `m` large. In conditional form this is
`lim_{m → ∞} limsup_{n → ∞} P(max_{m ≤ |t| ≤ rₙ} |X_t| > uₙ | |X_0| > uₙ) = 0`
([BS09, Condition 4.1], [KS20, §6.1] with `uₙ = aₙ x`). We state it without conditional
probabilities or `limsup`, as an `ε`–`m` bound on `P(|X_0| > uₙ, max_{m ≤ |t| ≤ rₙ} |X_t| > uₙ)`;
the two forms are equivalent since the bound is required for every `ε > 0`. -/
def AntiClusteringAt (P : Measure Ω) (X : ℤ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ᶠ n in atTop,
    P.real {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, (m : ℤ) ≤ |t| ∧ |t| ≤ r n ∧ u n < |X t ω|} ≤
      ε * P.real {ω | u n < |X 0 ω|}

/-- The forward half of `AntiClusteringAt`: only the times `m ≤ t ≤ rₙ` are controlled. This is
all that the results below use. -/
def ForwardAntiClusteringAt (P : Measure Ω) (X : ℤ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ᶠ n in atTop,
    P.real {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X t ω|} ≤
      ε * P.real {ω | u n < |X 0 ω|}

/-- **The anticlustering condition `AC(rₙ)`** ([BS09, Condition 4.1], [KS20, §6.1]): for every
`x > 0`, `lim_{m → ∞} limsup_{n → ∞} P(max_{m ≤ |t| ≤ rₙ} |X_t| > aₙ x | |X_0| > aₙ x) = 0`.
In the literature `aₙ` satisfies `n P(|X_0| > aₙ) → 1` and `rₙ → ∞`, `rₙ / n → 0`; these are
separate hypotheses of the theorems below, assumed only where used. -/
def AntiClustering (P : Measure Ω) (X : ℤ → Ω → ℝ) (a : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  ∀ x : ℝ, 0 < x → AntiClusteringAt P X (fun n => a n * x) r

theorem AntiClusteringAt.forward [IsFiniteMeasure P] (h : AntiClusteringAt P X u r) :
    ForwardAntiClusteringAt P X u r := by
  intro ε hε
  obtain ⟨m, hm⟩ := h ε hε
  refine ⟨m, hm.mono fun n hn => le_trans (measureReal_mono fun ω hω => ?_) hn⟩
  obtain ⟨h0, t, h1, h2, h3⟩ := hω
  have ht : 0 ≤ t := le_trans (Int.natCast_nonneg m) h1
  exact ⟨h0, t, by rwa [abs_of_nonneg ht], by rwa [abs_of_nonneg ht], h3⟩

/-- Increasing `m` preserves the forward anticlustering bound. -/
theorem ForwardAntiClusteringAt.exists_ge [IsFiniteMeasure P] (h : ForwardAntiClusteringAt P X u r)
    {ε : ℝ} (hε : 0 < ε) (m₀ : ℕ) : ∃ m ≥ m₀, ∀ᶠ n in atTop,
      P.real {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X t ω|} ≤
        ε * P.real {ω | u n < |X 0 ω|} := by
  obtain ⟨m, hm⟩ := h ε hε
  refine ⟨max m m₀, le_max_right _ _, hm.mono fun n hn => le_trans (measureReal_mono ?_) hn⟩
  rintro ω ⟨h0, t, h1, h2, h3⟩
  exact ⟨h0, t, le_trans (by exact_mod_cast le_max_left m m₀) h1, h2, h3⟩

end Defs

/-! ### Conditional window probabilities -/

section Windows

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- Conditional probability of a window event under `|X_0| > x`: the portmanteau theorem for a
window event whose frontier is null for the tail process. -/
theorem HasTailProcess.tendsto_cond_window {Y : ℤ → Ω' → ℝ} (hX : ∀ t, Measurable (X t))
    (hYm : ∀ t, Measurable (Y t)) (h : HasTailProcess P X α Q Y) (W : Finset ℤ)
    {E : Set (W → ℝ)} (hE : MeasurableSet E)
    (hfr : Q ((fun ω' (t : W) => Y t ω') ⁻¹' frontier E) = 0) :
    Tendsto (fun x => P[|{ω | x < |X 0 ω|}] ((fun ω (t : W) => X t ω / x) ⁻¹' E)) atTop
      (𝓝 (Q ((fun ω' (t : W) => Y t ω') ⁻¹' E))) := by
  have hYw : Measurable fun ω' (t : W) => Y t ω' := measurable_pi_iff.2 fun t => hYm _
  have hXw : ∀ x : ℝ, Measurable fun ω (t : W) => X t ω / x := fun x =>
    measurable_pi_iff.2 fun t => (hX _).div_const x
  have hconv := h.2 W
  have hprob : ∀ᶠ x in atTop,
      IsProbabilityMeasure ((P[|{ω | x < |X 0 ω|}]).map fun ω (t : W) => X t ω / x) := by
    filter_upwards [hconv.eventually_measure_ne_zero] with x hx
    have := cond_isProbabilityMeasure (μ := P) hx
    infer_instance
  have key := tendsto_measure_of_null_frontier_of_forall_integral_tendsto hprob
    (fun f => (hconv f).congr fun x =>
      (integral_map (hXw x).aemeasurable f.continuous.aestronglyMeasurable).symm) (E := E)
    (by rw [Measure.map_apply hYw isClosed_frontier.measurableSet]; exact hfr)
  rw [Measure.map_apply hYw hE] at key
  exact key.congr fun x => Measure.map_apply (hXw x) hE

/-- The windows of the tail process `Y_t = R Θ_t` put no mass on the unit sphere of the sup
norm, since `R` is continuous and independent of `Θ`. -/
theorem measure_window_norm_eq_one (hα : 0 < α) (hΘm : ∀ t, Measurable (Θ t)) (W : Finset ℤ) :
    ((paretoMeasure 1 α).prod Q) ((fun p (t : W) => p.1 * Θ t p.2) ⁻¹' {y | ‖y‖ = 1}) = 0 := by
  refine measure_mono_null (t := ⋃ t : W, {p | |p.1 * Θ t p.2| = 1}) ?_
    (measure_iUnion_null fun t => prod_abs_mul_eq_null hα (hΘm t) one_ne_zero)
  intro p hp
  set y : W → ℝ := fun t => p.1 * Θ t p.2
  have hp' : ‖y‖ = 1 := hp
  have hne : Nonempty W := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : y = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hp'
    exact zero_ne_one hp'
  obtain ⟨t0, -, ht0⟩ := Finset.exists_max_image Finset.univ (fun t => |y t|) Finset.univ_nonempty
  refine mem_iUnion.2 ⟨t0, ?_⟩
  show |y t0| = 1
  have h1 : ‖y‖ ≤ |y t0| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun t => by
    simpa [Real.norm_eq_abs] using ht0 t (Finset.mem_univ t)
  have h2 : |y t0| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm y t0
  linarith

omit [IsProbabilityMeasure Q] in
/-- The tail process `(r, ω) ↦ r Θ_t(ω)` is jointly measurable. -/
theorem measurable_radial_mul_spectral (hΘm : ∀ t, Measurable (Θ t)) (t : ℤ) :
    Measurable fun p : ℝ × Ω' => p.1 * Θ t p.2 :=
  measurable_fst.mul ((hΘm t).comp measurable_snd)

/-- **No exceedance in a window** ([BS09, §4]): for every finite window `W`,
`P(|X_t| ≤ x for all t ∈ W | |X_0| > x) → P(|Y_t| ≤ 1 for all t ∈ W)` as `x → ∞`, where
`Y_t = R Θ_t` is the tail process. Uses only the spectral tail process (no stationarity). -/
theorem HasSpectralTailProcess.tendsto_cond_forall_le (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (h : HasSpectralTailProcess P X α Q Θ) (W : Finset ℤ) :
    Tendsto (fun x => P[|{ω | x < |X 0 ω|}] {ω | ∀ t ∈ W, |X t ω| ≤ x}) atTop
      (𝓝 (((paretoMeasure 1 α).prod Q) {p | ∀ t ∈ W, |p.1 * Θ t p.2| ≤ 1})) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hE : MeasurableSet {y : W → ℝ | ‖y‖ ≤ 1} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have key := (h.hasTailProcess hα hX hΘm).tendsto_cond_window hX
    (measurable_radial_mul_spectral hΘm) W hE
    (measure_mono_null (preimage_mono (frontier_le_subset_eq continuous_norm continuous_const))
      (measure_window_norm_eq_one hα hΘm W))
  have hset : ((fun p : ℝ × Ω' => fun t : W => p.1 * Θ t p.2) ⁻¹' {y | ‖y‖ ≤ 1}) =
      {p | ∀ t ∈ W, |p.1 * Θ t p.2| ≤ 1} := by
    ext p
    simp only [mem_preimage, mem_ofPred_eq, pi_norm_le_iff_of_nonneg zero_le_one,
      Real.norm_eq_abs, Subtype.forall]
  rw [hset] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  congr 1
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, pi_norm_le_iff_of_nonneg zero_le_one,
    Real.norm_eq_abs, Subtype.forall, abs_div, abs_of_pos hx, div_le_one hx]

/-- **An exceedance in a window** ([BS09, §4]): for every finite window `W`,
`P(|X_t| > x for some t ∈ W | |X_0| > x) → P(|Y_t| > 1 for some t ∈ W)` as `x → ∞`. -/
theorem HasSpectralTailProcess.tendsto_cond_exists_lt (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (h : HasSpectralTailProcess P X α Q Θ) (W : Finset ℤ) :
    Tendsto (fun x => P[|{ω | x < |X 0 ω|}] {ω | ∃ t ∈ W, x < |X t ω|}) atTop
      (𝓝 (((paretoMeasure 1 α).prod Q) {p | ∃ t ∈ W, 1 < |p.1 * Θ t p.2|})) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hE : MeasurableSet {y : W → ℝ | 1 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have key := (h.hasTailProcess hα hX hΘm).tendsto_cond_window hX
    (measurable_radial_mul_spectral hΘm) W hE
    (measure_mono_null (preimage_mono ((frontier_lt_subset_eq continuous_const
      continuous_norm).trans fun y hy => Eq.symm hy)) (measure_window_norm_eq_one hα hΘm W))
  have hiff : ∀ y : W → ℝ, 1 < ‖y‖ ↔ ∃ t : W, 1 < |y t| := fun y => by
    rw [← not_iff_not, not_lt, pi_norm_le_iff_of_nonneg zero_le_one]
    simp [Real.norm_eq_abs]
  have hset : ((fun p : ℝ × Ω' => fun t : W => p.1 * Θ t p.2) ⁻¹' {y | 1 < ‖y‖}) =
      {p | ∃ t ∈ W, 1 < |p.1 * Θ t p.2|} := by
    ext p
    simp only [mem_preimage, mem_ofPred_eq, hiff, Subtype.exists, exists_prop]
  rw [hset] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  congr 1
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, hiff, Subtype.exists, exists_prop, abs_div,
    abs_of_pos hx, one_lt_div hx]

end Windows

/-! ### Anticlustering forces the spectral tail process to vanish -/

section Vanishing

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- A bound `P(s ∩ A) ≤ ε P(s)` is a bound `P(A | s) ≤ ε`. -/
theorem cond_le_ofReal_of_measureReal_le [IsFiniteMeasure P] {s A : Set Ω} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0 ≤ ε) (h : P.real (s ∩ A) ≤ ε * P.real s) : P[|s] A ≤ ENNReal.ofReal ε := by
  rw [cond_apply hs]
  rcases eq_or_ne (P s) 0 with h0 | h0
  · simp [measure_mono_null inter_subset_left h0]
  · have h1 : P (s ∩ A) ≤ ENNReal.ofReal ε * P s := by
      have := ENNReal.ofReal_le_ofReal h
      rwa [ENNReal.ofReal_mul hε, measureReal_def, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_toReal (measure_ne_top _ _)] at this
    calc (P s)⁻¹ * P (s ∩ A) ≤ (P s)⁻¹ * (ENNReal.ofReal ε * P s) := by gcongr
      _ = ENNReal.ofReal ε := by
        rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), mul_one]

omit [IsProbabilityMeasure Q] in
/-- If `n P(|X_0| > uₙ)` converges, then `uₙ → ∞`: regular variation makes `P(|X_0| > x)`
positive for every `x`, while `P(|X_0| > uₙ) → 0`. -/
theorem HasSpectralTailProcess.tendsto_atTop_of_tendsto_mul (h : HasSpectralTailProcess P X α Q Θ)
    {u : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) :
    Tendsto u atTop atTop := by
  have hp := tendsto_zero_of_tendsto_natCast_mul' hτ
  rw [tendsto_atTop]
  intro C
  obtain ⟨x, hxC, hx⟩ := ((eventually_ge_atTop C).and h.1.eventually_pos).exists
  have hC : 0 < P.real {ω | C < |X 0 ω|} :=
    hx.trans_le (measureReal_mono fun ω (hω : x < |X 0 ω|) => hxC.trans_lt hω)
  filter_upwards [hp.eventually (gt_mem_nhds hC)] with n hn
  by_contra hcon
  rw [not_le] at hcon
  exact absurd (measureReal_mono (μ := P) (by intro ω (hω : C < |X 0 ω|); exact hcon.trans hω))
    (not_le.2 hn)

/-- **Anticlustering implies `Θ_t → 0`** ([BS09, Proposition 4.2], [KS20, §6.1]).
Let `(X_t)` have spectral tail process `(Θ_t)` with index `α > 0`, let `uₙ → ∞` and `rₙ → ∞`, and
assume the forward anticlustering bound `ForwardAntiClusteringAt P X u r`. Then
`Θ_t → 0` almost surely as `t → +∞`.

Hypotheses actually used: only the spectral tail process (window convergence and regular
variation), `uₙ → ∞`, `rₙ → ∞` and the forward anticlustering bound at the single level sequence
`uₙ`. No stationarity, no `rₙ / n → 0`, and no anticlustering at other levels `aₙ x` are needed:
the passage from the level `1` of the tail process to all levels uses the independent Pareto
radius `R` of `Y = R Θ`. -/
theorem HasSpectralTailProcess.tendsto_zero_of_forwardAntiClusteringAt (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (h : HasSpectralTailProcess P X α Q Θ) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hAC : ForwardAntiClusteringAt P X u r) :
    ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ k ω') atTop (𝓝 0) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q with hπ
  have hs : ∀ x : ℝ, MeasurableSet {ω | x < |X 0 ω|} := fun x =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX 0))
  -- the tail process exceeds `1` after time `m` with small probability
  have step1 : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
      π {p | ∃ k : ℕ, m ≤ k ∧ 1 < |p.1 * Θ k p.2|} ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := hAC ε hε
    refine ⟨m, ?_⟩
    have hW : ∀ s : ℕ, π {p | ∃ t ∈ Finset.Icc (m : ℤ) s, 1 < |p.1 * Θ t p.2|} ≤
        ENNReal.ofReal ε := by
      intro s
      have key := (h.tendsto_cond_exists_lt hα hX hΘm (Finset.Icc (m : ℤ) s)).comp hu
      refine le_of_tendsto key ?_
      filter_upwards [hm, hr.eventually_ge_atTop s] with n hn hrn
      refine (measure_mono ?_).trans (cond_le_ofReal_of_measureReal_le (hs _) hε.le
        (A := {ω | ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X t ω|}) hn)
      rintro ω ⟨t, ht, hlt⟩
      rw [Finset.mem_Icc] at ht
      exact ⟨t, ht.1, ht.2.trans (by exact_mod_cast hrn), hlt⟩
    have hmono : Monotone fun s : ℕ =>
        {p : ℝ × Ω' | ∃ t ∈ Finset.Icc (m : ℤ) s, 1 < |p.1 * Θ t p.2|} := by
      intro a b hab p ⟨t, ht, h1⟩
      exact ⟨t, Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hab) ht, h1⟩
    have hU : (⋃ s : ℕ, {p : ℝ × Ω' | ∃ t ∈ Finset.Icc (m : ℤ) s, 1 < |p.1 * Θ t p.2|}) =
        {p | ∃ k : ℕ, m ≤ k ∧ 1 < |p.1 * Θ k p.2|} := by
      ext p
      simp only [mem_iUnion, mem_ofPred_eq, Finset.mem_Icc]
      constructor
      · rintro ⟨s, t, ⟨h1, h2⟩, h3⟩
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
        exact ⟨k, by exact_mod_cast h1, h3⟩
      · rintro ⟨k, hk, h3⟩
        exact ⟨k, k, ⟨by exact_mod_cast hk, le_rfl⟩, h3⟩
    rw [← hU]
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hW
  -- scaling by the independent Pareto radius: `Θ` exceeds every level `v` rarely
  have step2 : ∀ v : ℝ, 0 < v → v ≤ 1 →
      Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ k ω'|}) = 0 := by
    intro v hv hv1
    have hc : paretoMeasure 1 α (Ioi (1 / v)) = ENNReal.ofReal (v ^ α) := by
      rw [paretoMeasure_one_Ioi hα (by rw [le_div_iff₀ hv]; linarith), one_div,
        Real.inv_rpow hv.le, Real.rpow_neg (by positivity), inv_inv]
    have hc0 : ENNReal.ofReal (v ^ α) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hv α)).ne'
    have hbound : ∀ ε : ℝ, 0 < ε → Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ k ω'|}) *
        ENNReal.ofReal (v ^ α) ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨m, hm⟩ := step1 ε hε
      calc Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ k ω'|}) * ENNReal.ofReal (v ^ α)
          ≤ Q {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ k ω'|} * ENNReal.ofReal (v ^ α) := by
            gcongr; exact iInter_subset _ m
        _ = π (Ioi (1 / v) ×ˢ {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ k ω'|}) := by
            rw [hπ, Measure.prod_prod, hc, mul_comm]
        _ ≤ π {p | ∃ k : ℕ, m ≤ k ∧ 1 < |p.1 * Θ k p.2|} := by
            refine measure_mono ?_
            rintro ⟨r', ω'⟩ ⟨hr', k, hk, hθ⟩
            refine ⟨k, hk, ?_⟩
            have hr' : 1 / v < r' := hr'
            have hr0 : 0 < r' := lt_trans (by positivity) hr'
            rw [abs_mul, abs_of_pos hr0]
            calc (1 : ℝ) = (1 / v) * v := by field_simp
              _ < r' * |Θ k ω'| := mul_lt_mul hr' hθ.le hv hr0.le
        _ ≤ ENNReal.ofReal ε := hm
    have h0 : Q (⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ v < |Θ k ω'|}) *
        ENNReal.ofReal (v ^ α) = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
      rw [zero_add]
      simpa using hbound ε (by exact_mod_cast hε)
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact h0
    · exact absurd h0 hc0
  have hae : ∀ᵐ ω' ∂Q, ∀ j : ℕ,
      ω' ∉ ⋂ m : ℕ, {ω' | ∃ k : ℕ, m ≤ k ∧ 1 / ((j : ℝ) + 1) < |Θ k ω'|} := by
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

/-- **Anticlustering implies `ϑ > 0`** ([BS09, Proposition 4.2], [KS20, §7.5]): for a stationary
series with spectral tail process `Θ` satisfying the forward anticlustering bound along some
`uₙ → ∞`, `rₙ → ∞`, the candidate extremal index is positive. Combines
`tendsto_zero_of_forwardAntiClusteringAt` with `candidateExtremalIndex_pos`; stationarity enters
only through the latter (the time-change formula). -/
theorem HasSpectralTailProcess.candidateExtremalIndex_pos_of_forwardAntiClusteringAt
    (hα : 0 < α) (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hAC : ForwardAntiClusteringAt P X u r) : 0 < candidateExtremalIndex Q Θ α :=
  h.candidateExtremalIndex_pos hα hX hΘm hstat
    (h.tendsto_zero_of_forwardAntiClusteringAt hα hX hΘm hu hr hAC)

/-- **`AC(rₙ)` implies `Θ_t → 0` and `ϑ > 0`** in the normalization of [BS09, §4] and
[KS20, §6.1]: `n P(|X_0| > aₙ) → 1`, `rₙ → ∞`, and `AC(rₙ)`. Only the level `x = 1`
of `AC(rₙ)` and only its forward half are used, and `rₙ / n → 0` is not needed. -/
theorem HasSpectralTailProcess.candidateExtremalIndex_pos_of_antiClustering
    (hα : 0 < α) (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {a : ℕ → ℝ} (ha : Tendsto (fun n : ℕ => n * P.real {ω | a n < |X 0 ω|}) atTop (𝓝 1))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hAC : AntiClustering P X a r) :
    (∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ k ω') atTop (𝓝 0)) ∧
      0 < candidateExtremalIndex Q Θ α := by
  have hu : Tendsto (fun n => a n * 1) atTop atTop := by
    simpa using h.tendsto_atTop_of_tendsto_mul ha
  have hAC1 := (hAC 1 one_pos).forward
  exact ⟨h.tendsto_zero_of_forwardAntiClusteringAt hα hX hΘm hu hr hAC1,
    h.candidateExtremalIndex_pos_of_forwardAntiClusteringAt hα hX hΘm hstat hu hr hAC1⟩

end Vanishing

end ExtremeValueTheory
