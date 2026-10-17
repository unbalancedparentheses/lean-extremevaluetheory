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

end ExtremeValueTheory
