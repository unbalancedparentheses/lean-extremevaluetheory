/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.StationaryWindows
import ExtremeValueTheory.Dependence.ExtremalIndex

/-!
# Anticlustering and the extremal index

PLACEHOLDER
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
([BS09, (4.1)], [KS20, Definition 6.1.3] with `uₙ = aₙ x`). We state it without conditional
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

/-- **The anticlustering condition `AC(rₙ)`** ([BS09, (4.1)], [KS20, Definition 6.1.3]): for every
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
private lemma measurable_tail (hΘm : ∀ t, Measurable (Θ t)) (t : ℤ) :
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
  have key := (h.hasTailProcess hα hX hΘm).tendsto_cond_window hX (measurable_tail hΘm) W hE
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
  have key := (h.hasTailProcess hα hX hΘm).tendsto_cond_window hX (measurable_tail hΘm) W hE
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
  exact absurd (measureReal_mono (μ := P) fun ω (hω : C < |X 0 ω|) => hcon.trans hω)
    (not_le.2 hn)

/-- **Anticlustering implies `Θ_t → 0`** ([BS09, Proposition 4.2], [KS20, Lemma 6.1.?]).
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
[KS20, Definition 6.1.3]: `n P(|X_0| > aₙ) → 1`, `rₙ → ∞`, and `AC(rₙ)`. Only the level `x = 1`
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
    continuous_abs.measurable.comp (measurable_tail hΘm t)
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
