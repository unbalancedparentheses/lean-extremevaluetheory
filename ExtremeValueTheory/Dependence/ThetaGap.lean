/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Anticlustering

/-!
# The gap between `θ` and `ϑ`: escaping cluster mass

Without anticlustering, `θ ≤ ϑ` (`HasSpectralTailProcess.le_candidateExtremalIndex`). This file
identifies the gap exactly.

Fix a level sequence `uₙ` and block lengths `rₙ`. Given `|X_0| > uₙ`, let
`Tₙ = inf {t > 0 : |X_t| > uₙ}` be the first return time above the level. The *escape* at lag `m`
is
`εₙ(m) = (1 / rₙ) ∑_{k < rₙ} P(max_{0 < t ≤ m} |X_t| ≤ uₙ < max_{m < t ≤ k} |X_t| | |X_0| > uₙ)`
`     = E[(1 - Tₙ / rₙ)⁺ ; Tₙ > m | |X_0| > uₙ]`,
the (block-length weighted) conditional probability that the cluster started at `0` comes back
above the level, inside the block, but only after lag `m`. The tail process sees every fixed lag,
so this is the part of the cluster that "escapes to infinity" as `n → ∞` and is invisible to `Θ`.

## Main definitions

* `escapeSet X x m k`: the event `|X_0| > x`, `|X_t| ≤ x` for `0 < t ≤ m` and `|X_t| > x` for some
  `m < t ≤ k`.
* `clusterRatio P X u r n = P(M_{rₙ} > uₙ) / (rₙ P(|X_0| > uₙ))`.
* `clusterEscape P X u r m n = εₙ(m)`.
* `HasEscapeMass P X u r η`: `εₙ(m) → η` in the iterated sense `lim_m lim_n`, in `δ`–`m` form:
  for `m` large, `|εₙ(m) - η| ≤ δ` eventually in `n`.

## Main results, with the hypotheses each one uses

* `HasShiftInvariantWindows.clusterRatio_sub_le`: the exact identity behind everything:
  `0 ≤ clusterRatio - (qₙ(m) - εₙ(m)) ≤ m / rₙ`, where
  `qₙ(m) = P(max_{0<t≤m} |X_t| ≤ uₙ | |X_0| > uₙ)` (stationarity only, no tail process).
* `HasSpectralTailProcess.tendsto_clusterRatio_iff`: **the gap formula.** Under stationarity,
  the spectral tail process, `uₙ → ∞` and `rₙ → ∞`:
  `clusterRatio → L ↔ HasEscapeMass P X u r (ϑ - L)`.
  So the cluster ratio converges iff the escape mass exists, and then `lim = ϑ - η`.
* `HasEscapeMass.unique`, `HasEscapeMass.nonneg`, `HasSpectralTailProcess.hasEscapeMass_le`:
  the escape mass is unique and `0 ≤ η ≤ ϑ`.
* `ForwardAntiClusteringAt.hasEscapeMass_zero`: forward anticlustering gives `η = 0`; this
  recovers `HasSpectralTailProcess.tendsto_blockRatio`.
* `HasSpectralTailProcess.tendsto_partialMax_iff_hasEscapeMass`: under `A(uₙ)`,
  `n P(|X_0| > uₙ) → τ > 0`, `rₙ / n → 0`: `P(M n ≤ uₙ) → exp (-θ τ) ↔ HasEscapeMass (ϑ - θ)`.
* `HasSpectralTailProcess.hasEscapeMass_of_hasExtremalIndex`: if the extremal index `θ` exists,
  then along every level sequence and block length satisfying `A(uₙ)` the escape mass exists and
  equals `ϑ - θ`. In particular the escape mass does not depend on the choice of `uₙ`, `rₙ`.
* `HasSpectralTailProcess.eq_candidateExtremalIndex_iff_hasEscapeMass_zero`: **`θ = ϑ` iff no
  cluster mass escapes**, under `A(uₙ)` along one level sequence;
  `HasSpectralTailProcess.lt_candidateExtremalIndex_iff`: `θ < ϑ` iff the escape mass is positive.

## Remarks

* The gap formula is an exact, two-sided statement: it replaces the inequality `θ ≤ ϑ` by
  `θ = ϑ - η`, and turns the phenomenon `θ < ϑ` (Bai–Wang) into the checkable statement `η > 0`.
  An explicit stationary example with `θ = 1/2`, `ϑ = 1`, `η = 1/2` is the echo process of
  `Dependence/EchoProcess.lean`.
* `η = 0` is weaker than (forward) anticlustering in two ways: only the *first* return after a
  quiet period `(0, m]` counts, so a cluster that the tail process sees at finite lags may keep
  returning (for a mixture of a constant sequence and an iid sequence, anticlustering fails while
  `η = 0` and the cluster ratio tends to `ϑ`; this example is not formalized here); and returns are
  weighted by `1 - Tₙ / rₙ`, so returns near the end of the block are discounted.
* The escape mass depends on `uₙ` and `rₙ` only through `ϑ - θ` once `A(uₙ)` holds
  (`HasSpectralTailProcess.hasEscapeMass_of_hasExtremalIndex`). Without `A(uₙ)` it can depend on
  the block length: for the echo process with echo lag `L(Z)`, blocks much shorter than the echo
  lag of an exceedance give cluster ratio `ϑ = 1`, longer ones `1/2` (only the second regime is
  formalized).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Definitions -/

section Defs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The *escape event*: `|X_0| > x`, no exceedance of `x` at times `0 < t ≤ m`, and an exceedance
at some time `m < t ≤ k`. -/
def escapeSet (X : ℤ → Ω → ℝ) (x : ℝ) (m k : ℕ) : Set Ω :=
  {ω | x < |X 0 ω| ∧ (∀ t ∈ Finset.Ioc (0 : ℤ) m, |X t ω| ≤ x) ∧
    ∃ t ∈ Finset.Ioc (m : ℤ) k, x < |X t ω|}

/-- The event `|X_0| > x` with no exceedance of `x` at times `0 < t ≤ k`. -/
def noReturnSet (X : ℤ → Ω → ℝ) (x : ℝ) (k : ℕ) : Set Ω :=
  {ω | x < |X 0 ω| ∧ ∀ t ∈ Finset.Ioc (0 : ℤ) k, |X t ω| ≤ x}

/-- The *cluster ratio* `P(max_{0 ≤ t < rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ))`. -/
noncomputable def clusterRatio (P : Measure Ω) (X : ℤ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) :
    ℝ :=
  P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} / (r n * P.real {ω | u n < |X 0 ω|})

/-- The *escape at lag `m`*:
`εₙ(m) = (1 / rₙ) ∑_{k < rₙ} P(escapeSet X uₙ m k) / P(|X_0| > uₙ)`. With `Tₙ` the first return
time above `uₙ` after `0`, `∑_{k < rₙ} 1{m < Tₙ ≤ k} = (rₙ - Tₙ)⁺ 1{Tₙ > m}`, so
`εₙ(m) = E[(1 - Tₙ / rₙ)⁺ ; Tₙ > m | |X_0| > uₙ]`. -/
noncomputable def clusterEscape (P : Measure Ω) (X : ℤ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ)
    (m n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (r n), P.real (escapeSet X (u n) m k)) / (r n * P.real {ω | u n < |X 0 ω|})

/-- **Escape mass** `η = lim_{m → ∞} lim_{n → ∞} εₙ(m)`, in `δ`–`m` form: for every `δ > 0`,
for all large `m`, eventually `|εₙ(m) - η| ≤ δ`. -/
def HasEscapeMass (P : Measure Ω) (X : ℤ → Ω → ℝ) (u : ℕ → ℝ) (r : ℕ → ℕ) (η : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ᶠ n in atTop, |clusterEscape P X u r m n - η| ≤ δ

variable {P : Measure Ω} {X : ℤ → Ω → ℝ} {u : ℕ → ℝ} {r : ℕ → ℕ}

theorem clusterEscape_nonneg (m n : ℕ) : 0 ≤ clusterEscape P X u r m n :=
  div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
    (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)

/-- The escape mass is unique. -/
theorem HasEscapeMass.unique {η η' : ℝ} (h : HasEscapeMass P X u r η)
    (h' : HasEscapeMass P X u r η') : η = η' := by
  by_contra hne
  have hδ : 0 < |η - η'| / 3 := by
    have := abs_pos.2 (sub_ne_zero.2 hne)
    positivity
  obtain ⟨m₀, hm₀⟩ := h _ hδ
  obtain ⟨m₁, hm₁⟩ := h' _ hδ
  obtain ⟨n, hn, hn'⟩ := ((hm₀ (max m₀ m₁) (le_max_left _ _)).and
    (hm₁ (max m₀ m₁) (le_max_right _ _))).exists
  have := abs_sub_le η (clusterEscape P X u r (max m₀ m₁) n) η'
  rw [abs_sub_comm] at hn
  linarith

/-- The escape mass is nonnegative. -/
theorem HasEscapeMass.nonneg {η : ℝ} (h : HasEscapeMass P X u r η) : 0 ≤ η := by
  by_contra hneg
  push Not at hneg
  obtain ⟨m₀, hm₀⟩ := h (-η / 2) (by linarith)
  obtain ⟨n, hn⟩ := (hm₀ m₀ le_rfl).exists
  have := clusterEscape_nonneg (P := P) (X := X) (u := u) (r := r) m₀ n
  rw [abs_le] at hn
  linarith [hn.1]

end Defs

/-! ### The exact identity -/

section Identity

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ℤ → Ω → ℝ}

theorem measurableSet_noReturnSet (hX : ∀ t, Measurable (X t)) (x : ℝ) (k : ℕ) :
    MeasurableSet (noReturnSet X x k) := by
  have hXa : ∀ t, Measurable fun ω => |X t ω| := fun t => continuous_abs.measurable.comp (hX t)
  simp only [noReturnSet, ofPred_and, ofPred_forall]
  exact (measurableSet_lt measurable_const (hXa 0)).inter
    (MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
      measurableSet_le (hXa t) measurable_const)

theorem measurableSet_escapeSet (hX : ∀ t, Measurable (X t)) (x : ℝ) (m k : ℕ) :
    MeasurableSet (escapeSet X x m k) := by
  have hXa : ∀ t, Measurable fun ω => |X t ω| := fun t => continuous_abs.measurable.comp (hX t)
  simp only [escapeSet, ofPred_and, ofPred_forall, ofPred_exists]
  exact (measurableSet_lt measurable_const (hXa 0)).inter
    ((MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
      measurableSet_le (hXa t) measurable_const).inter
    (MeasurableSet.iUnion fun t => (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const (hXa t))))

/-- For `m ≤ k`, the no-return event up to `m` splits into the no-return event up to `k` and the
escape event: `P(noReturn m) = P(noReturn k) + P(escape m k)`. -/
theorem measureReal_noReturnSet_eq_add (hX : ∀ t, Measurable (X t)) (x : ℝ) {m k : ℕ}
    (hmk : m ≤ k) :
    P.real (noReturnSet X x m) = P.real (noReturnSet X x k) + P.real (escapeSet X x m k) := by
  have hunion : noReturnSet X x m = noReturnSet X x k ∪ escapeSet X x m k := by
    ext ω
    simp only [noReturnSet, escapeSet, mem_union, mem_ofPred_eq, Finset.mem_Ioc]
    constructor
    · rintro ⟨h0, hm⟩
      by_cases hk : ∀ t : ℤ, 0 < t ∧ t ≤ k → |X t ω| ≤ x
      · exact Or.inl ⟨h0, hk⟩
      · right
        push Not at hk
        obtain ⟨t, ⟨ht0, htk⟩, hlt⟩ := hk
        refine ⟨h0, hm, t, ⟨?_, htk⟩, hlt⟩
        by_contra hcon
        exact absurd (hm t ⟨ht0, by omega⟩) (not_le.2 hlt)
    · rintro (⟨h0, hk⟩ | ⟨h0, hm, -⟩)
      · exact ⟨h0, fun t ht => hk t ⟨ht.1, ht.2.trans (by exact_mod_cast hmk)⟩⟩
      · exact ⟨h0, hm⟩
  have hdisj : Disjoint (noReturnSet X x k) (escapeSet X x m k) := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, hk⟩ ⟨-, -, t, ht, hlt⟩
    rw [Finset.mem_Ioc] at ht
    exact absurd (hk t (Finset.mem_Ioc.2 ⟨by omega, ht.2⟩)) (not_le.2 hlt)
  rw [hunion, measureReal_union hdisj (measurableSet_escapeSet hX x m k)]

/-- For `k ≤ m` the escape event is empty. -/
theorem escapeSet_eq_empty {x : ℝ} {m k : ℕ} (hkm : k ≤ m) : escapeSet X x m k = ∅ := by
  ext ω
  simp only [escapeSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  rintro - - ⟨t, ht, -⟩
  rw [Finset.mem_Ioc] at ht
  omega

/-- **The exact identity behind the gap formula.** For a stationary series, with
`qₙ(m) = P(noReturn m) / P(|X_0| > uₙ)`,
`0 ≤ clusterRatio - (qₙ(m) - εₙ(m)) ≤ m / rₙ` whenever `m ≤ rₙ` and `P(|X_0| > uₙ) > 0`.
Uses stationarity only (through the first-exceedance decomposition). -/
theorem HasShiftInvariantWindows.clusterRatio_sub_le (hstat : HasShiftInvariantWindows P X)
    (hX : ∀ t, Measurable (X t)) (u : ℕ → ℝ) (r : ℕ → ℕ) {m n : ℕ} (hmr : m ≤ r n)
    (hr : 0 < r n) (hp : 0 < P.real {ω | u n < |X 0 ω|}) :
    0 ≤ clusterRatio P X u r n - (P.real (noReturnSet X (u n) m) / P.real {ω | u n < |X 0 ω|} -
        clusterEscape P X u r m n) ∧
      clusterRatio P X u r n - (P.real (noReturnSet X (u n) m) / P.real {ω | u n < |X 0 ω|} -
        clusterEscape P X u r m n) ≤ m / r n := by
  set p := P.real {ω | u n < |X 0 ω|} with hpdef
  set f : ℕ → ℝ := fun k => P.real (noReturnSet X (u n) k)
  set e : ℕ → ℝ := fun k => P.real (escapeSet X (u n) m k)
  have hR : (0 : ℝ) < r n := by exact_mod_cast hr
  have hfS : ∀ k, f k ≤ p := fun k => measureReal_mono fun ω hω => hω.1
  have hfanti : ∀ j k, j ≤ k → f k ≤ f j := fun j k hjk => measureReal_mono fun ω hω =>
    ⟨hω.1, fun t ht => hω.2 t (Finset.Ioc_subset_Ioc le_rfl (by exact_mod_cast hjk) ht)⟩
  have hratio : clusterRatio P X u r n = (∑ k ∈ Finset.range (r n), f k) / (r n * p) := by
    rw [clusterRatio, hstat.measureReal_exists_lt_eq_sum hX]
    rfl
  have hkey : clusterRatio P X u r n - (f m / p - clusterEscape P X u r m n) =
      (∑ k ∈ Finset.range m, (f k - f m)) / (r n * p) := by
    rw [hratio, clusterEscape, ← hpdef]
    have hsum : ∑ k ∈ Finset.range (r n), (f k + e k - f m) =
        ∑ k ∈ Finset.range m, (f k - f m) := by
      rw [← Finset.sum_range_add_sum_Ico _ hmr]
      have h1 : ∑ k ∈ Finset.Ico m (r n), (f k + e k - f m) = 0 :=
        Finset.sum_eq_zero fun k hk => by
          have := measureReal_noReturnSet_eq_add (P := P) hX (u n) (Finset.mem_Ico.1 hk).1
          simp only [f, e]
          linarith
      have h2 : ∀ k ∈ Finset.range m, f k + e k - f m = f k - f m := fun k hk => by
        simp only [e, escapeSet_eq_empty (Finset.mem_range.1 hk).le, measureReal_empty,
          add_zero]
      rw [h1, add_zero, Finset.sum_congr rfl h2]
    rw [← hsum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp
    ring
  change 0 ≤ clusterRatio P X u r n - (f m / p - clusterEscape P X u r m n) ∧
    clusterRatio P X u r n - (f m / p - clusterEscape P X u r m n) ≤ m / r n
  rw [hkey]
  have hnn : ∀ k ∈ Finset.range m, 0 ≤ f k - f m := fun k hk =>
    sub_nonneg.2 (hfanti k m (Finset.mem_range.1 hk).le)
  refine ⟨div_nonneg (Finset.sum_nonneg hnn) (by positivity), ?_⟩
  have hle : ∑ k ∈ Finset.range m, (f k - f m) ≤ m * p := by
    calc _ ≤ ∑ _k ∈ Finset.range m, p := Finset.sum_le_sum fun k _ => by
          linarith [hfS k, measureReal_nonneg (μ := P) (s := noReturnSet X (u n) m)]
      _ = m * p := by simp
  rw [div_le_div_iff₀ (by positivity) hR]
  nlinarith

end Identity

/-! ### The gap formula -/

section Gap

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ} {u : ℕ → ℝ} {r : ℕ → ℕ}

/-- For each fixed lag `m`, `clusterRatio + εₙ(m) → ϑ_m = P(|Y_t| ≤ 1, 0 < t ≤ m)`, the
finite-horizon candidate extremal index of the tail process `Y = R Θ`. Stationarity, the spectral
tail process, `uₙ → ∞`, `rₙ → ∞`. -/
theorem HasSpectralTailProcess.tendsto_clusterRatio_add_clusterEscape (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    (hu : Tendsto u atTop atTop) (hr : Tendsto r atTop atTop) (m : ℕ) :
    Tendsto (fun n => clusterRatio P X u r n + clusterEscape P X u r m n) atTop
      (𝓝 (((paretoMeasure 1 α).prod Q).real
        {p | ∀ t ∈ Finset.Ioc (0 : ℤ) m, |p.1 * Θ t p.2| ≤ 1})) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q
  have hs : ∀ x : ℝ, MeasurableSet {ω | x < |X 0 ω|} := fun x =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX 0))
  set q : ℕ → ℝ := fun n => P.real (noReturnSet X (u n) m) / P.real {ω | u n < |X 0 ω|}
  have hq : Tendsto q atTop
      (𝓝 (π.real {p | ∀ t ∈ Finset.Ioc (0 : ℤ) m, |p.1 * Θ t p.2| ≤ 1})) := by
    have key := (h.tendsto_cond_forall_le hα hX hΘm (Finset.Ioc (0 : ℤ) m)).comp hu
    have key' := (ENNReal.tendsto_toReal (measure_ne_top π _)).comp key
    refine key'.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [cond_toReal_eq (hs _)]
    rfl
  have hmr : Tendsto (fun n => (m : ℝ) / r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr)
  have hd : Tendsto (fun n => clusterRatio P X u r n + clusterEscape P X u r m n - q n) atTop
      (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hmr
    · filter_upwards [hr.eventually_ge_atTop (m + 1)] with n hn
      have := (hstat.clusterRatio_sub_le hX u r (m := m) (n := n) (by omega) (by omega)
        (h.measureReal_lt_abs_pos _)).1
      dsimp only [q]
      linarith
    · filter_upwards [hr.eventually_ge_atTop (m + 1)] with n hn
      have := (hstat.clusterRatio_sub_le hX u r (m := m) (n := n) (by omega) (by omega)
        (h.measureReal_lt_abs_pos _)).2
      dsimp only [q]
      linarith
  have := hd.add hq
  rw [zero_add] at this
  exact this.congr fun n => by ring

/-- **The gap formula.** For a stationary series with spectral tail process `Θ`, `uₙ → ∞` and
`rₙ → ∞`, the cluster ratio converges to `L` if and only if the escape mass exists and equals
`ϑ - L`:
`P(M_{rₙ} > uₙ) / (rₙ P(|X_0| > uₙ)) → L  ↔  lim_m lim_n εₙ(m) = ϑ - L`.
No anticlustering, no mixing, no `rₙ / n → 0`. -/
theorem HasSpectralTailProcess.tendsto_clusterRatio_iff (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    (hu : Tendsto u atTop atTop) (hr : Tendsto r atTop atTop) (L : ℝ) :
    Tendsto (clusterRatio P X u r) atTop (𝓝 L) ↔
      HasEscapeMass P X u r ((candidateExtremalIndex Q Θ α).toReal - L) := by
  set ϑ := (candidateExtremalIndex Q Θ α).toReal
  have hθlim := tendsto_measureReal_forall_le_candidateExtremalIndex hα hΘm
    (h.ae_abs_eq_one hΘm (hX 0))
  have hm := h.tendsto_clusterRatio_add_clusterEscape hα hX hΘm hstat hu hr
  set θk : ℕ → ℝ := fun k => ((paretoMeasure 1 α).prod Q).real
    {p | ∀ t ∈ Finset.Ioc (0 : ℤ) k, |p.1 * Θ t p.2| ≤ 1}
  constructor
  · intro hL δ hδ
    obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.1 hθlim) (δ / 2) (by linarith)
    refine ⟨m₀, fun m hm' => ?_⟩
    have hesc : Tendsto (fun n => clusterEscape P X u r m n) atTop (𝓝 (θk m - L)) :=
      ((hm m).sub hL).congr fun n => by ring
    filter_upwards [hesc.eventually (Metric.ball_mem_nhds _ (half_pos hδ))] with n hn
    rw [Real.dist_eq] at hn
    have h2 : |θk m - ϑ| < δ / 2 := by rw [← Real.dist_eq]; exact hm₀ m hm'
    have h3 := abs_sub_le (clusterEscape P X u r m n) (θk m - L) (ϑ - L)
    rw [show θk m - L - (ϑ - L) = θk m - ϑ by ring] at h3
    linarith
  · intro hη
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨m₀, hm₀⟩ := hη (δ / 4) (by linarith)
    obtain ⟨m₁, hm₁⟩ := (Metric.tendsto_atTop.1 hθlim) (δ / 4) (by linarith)
    set m := max m₀ m₁
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hm₀ m (le_max_left _ _)).and
      ((hm m).eventually (Metric.ball_mem_nhds _ (show 0 < δ / 4 by linarith))))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN n hn
    rw [Real.dist_eq] at h2
    have h3 : |θk m - ϑ| < δ / 4 := by rw [← Real.dist_eq]; exact hm₁ m (le_max_right _ _)
    rw [Real.dist_eq]
    set a := clusterRatio P X u r n
    set b := clusterEscape P X u r m n
    have e : a - L = (a + b - θk m) - (b - (ϑ - L)) + (θk m - ϑ) := by ring
    rw [e]
    have h4 := abs_add_le ((a + b - θk m) - (b - (ϑ - L))) (θk m - ϑ)
    have h5 := abs_sub (a + b - θk m) (b - (ϑ - L))
    linarith

/-- The escape mass is at most `ϑ`. -/
theorem HasSpectralTailProcess.hasEscapeMass_le (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    (hu : Tendsto u atTop atTop) (hr : Tendsto r atTop atTop) {η : ℝ}
    (hη : HasEscapeMass P X u r η) : η ≤ (candidateExtremalIndex Q Θ α).toReal := by
  have hL := (h.tendsto_clusterRatio_iff hα hX hΘm hstat hu hr
    ((candidateExtremalIndex Q Θ α).toReal - η)).2 (by rwa [sub_sub_cancel])
  have : 0 ≤ (candidateExtremalIndex Q Θ α).toReal - η :=
    ge_of_tendsto hL (Eventually.of_forall fun n =>
      div_nonneg measureReal_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg))
  linarith

end Gap

/-! ### Anticlustering means no escape -/

section AC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ℤ → Ω → ℝ} {u : ℕ → ℝ} {r : ℕ → ℕ}

/-- The escape at lag `m` is at most the anticlustering quantity
`P(|X_0| > uₙ, max_{m ≤ t ≤ rₙ} |X_t| > uₙ) / P(|X_0| > uₙ)`. -/
theorem clusterEscape_le (m n : ℕ) (hr : 0 < r n) :
    clusterEscape P X u r m n ≤
      P.real {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X t ω|} /
        P.real {ω | u n < |X 0 ω|} := by
  set A := P.real {ω | u n < |X 0 ω| ∧ ∃ t : ℤ, (m : ℤ) ≤ t ∧ t ≤ r n ∧ u n < |X t ω|}
  have hR : (0 : ℝ) < r n := by exact_mod_cast hr
  have hle : ∀ k ∈ Finset.range (r n), P.real (escapeSet X (u n) m k) ≤ A := fun k hk =>
    measureReal_mono fun ω hω => by
      obtain ⟨h0, -, t, ht, hlt⟩ := hω
      rw [Finset.mem_Ioc] at ht
      have hk := Finset.mem_range.1 hk
      exact ⟨h0, t, by omega, by omega, hlt⟩
  have hsum : ∑ k ∈ Finset.range (r n), P.real (escapeSet X (u n) m k) ≤ r n * A := by
    calc _ ≤ ∑ _k ∈ Finset.range (r n), A := Finset.sum_le_sum hle
      _ = r n * A := by simp
  rw [clusterEscape, ← div_div]
  exact div_le_div_of_nonneg_right ((div_le_iff₀' hR).2 hsum) measureReal_nonneg

/-- **Forward anticlustering forces zero escape mass.** Together with
`HasSpectralTailProcess.tendsto_clusterRatio_iff` this recovers
`HasSpectralTailProcess.tendsto_blockRatio`. -/
theorem ForwardAntiClusteringAt.hasEscapeMass_zero (hr : Tendsto r atTop atTop)
    (hAC : ForwardAntiClusteringAt P X u r) : HasEscapeMass P X u r 0 := by
  intro δ hδ
  obtain ⟨m₀, hm₀⟩ := hAC δ hδ
  refine ⟨m₀, fun m hm => ?_⟩
  filter_upwards [hm₀, hr.eventually_gt_atTop 0] with n hn hrn
  rw [sub_zero, abs_of_nonneg (clusterEscape_nonneg m n)]
  refine (clusterEscape_le m n hrn).trans ?_
  rcases (measureReal_nonneg (μ := P) (s := {ω | u n < |X 0 ω|})).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]; exact hδ.le
  rw [div_le_iff₀ h0]
  refine le_trans (measureReal_mono fun ω hω => ?_) hn
  obtain ⟨h0, t, h1, h2, h3⟩ := hω
  exact ⟨h0, t, le_trans (by exact_mod_cast hm) h1, h2, h3⟩

end AC

/-! ### The extremal index is `ϑ` minus the escape mass -/

section ExtremalIndex

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ} {u : ℕ → ℝ} {r : ℕ → ℕ}

/-- **Under `A(uₙ)`, the maximum and the cluster ratio determine each other.** For a stationary
series with `P(|X_0| > x) > 0` for all `x`, `n P(|X_0| > uₙ) → τ > 0`, `rₙ → ∞`, `rₙ / n → 0` and
the block condition `A(uₙ)`: `P(M n ≤ uₙ) → exp (-θ τ)` iff the cluster ratio tends to `θ`.
(No tail process is used.) -/
theorem HasShiftInvariantWindows.tendsto_partialMax_iff_tendsto_clusterRatio
    (hX : ∀ t, Measurable (X t)) (hstat : HasShiftInvariantWindows P X)
    (hp0 : ∀ n, 0 < P.real {ω | u n < |X 0 ω|}) {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) (hτ0 : 0 < τ)
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) (θ : ℝ) :
    Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ u n}) atTop
        (𝓝 (Real.exp (-(θ * τ)))) ↔ Tendsto (clusterRatio P X u r) atTop (𝓝 θ) := by
  set p : ℕ → ℝ := fun n => P.real {ω | u n < |X 0 ω|}
  set b : ℕ → ℝ := fun n => P.real {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|}
  set k : ℕ → ℕ := fun n => n / r n
  have hr0 : ∀ᶠ n in atTop, 0 < r n := hr.eventually_gt_atTop 0
  have hbr : ∀ n, b n ≤ r n * p n := by
    intro n
    simp only [b, hstat.measureReal_exists_lt_eq_sum hX]
    calc _ ≤ ∑ _k ∈ Finset.range (r n), p n :=
          Finset.sum_le_sum fun k _ => measureReal_mono fun ω hω => hω.1
      _ = r n * p n := by simp
  have hrp : Tendsto (fun n => (r n : ℝ) * p n) atTop (𝓝 0) := by
    have := hrn.mul hτ
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp only [p]
    field_simp
  have hb : Tendsto b atTop (𝓝 0) :=
    squeeze_zero (fun n => measureReal_nonneg) hbr hrp
  have hpart : ∀ n, 0 < r n →
      P.real {ω | partialMax (fun k : ℕ => |X k|) (r n) ω ≤ u n} = 1 - b n := by
    intro n hn
    have hmeas : MeasurableSet {ω | ∃ t ∈ Finset.Ico (0 : ℤ) (r n), u n < |X t ω|} := by
      simp only [ofPred_exists, ofPred_and]
      exact MeasurableSet.iUnion fun t => (MeasurableSet.const _).inter
        (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX t)))
    rw [← probReal_compl_eq_one_sub hmeas]
    congr 1
    ext ω
    rw [mem_ofPred_eq, partialMax_le_iff hn, mem_compl_iff, mem_ofPred_eq]
    constructor
    · rintro hle ⟨t, ht, hlt⟩
      rw [Finset.mem_Ico] at ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
      exact absurd (hle k (by exact_mod_cast ht.2)) (not_le.2 hlt)
    · intro hne k hk
      by_contra hcon
      exact hne ⟨k, Finset.mem_Ico.2 ⟨by positivity, by exact_mod_cast hk⟩, not_le.1 hcon⟩
  have hkr := tendsto_div_mul_div_self hr0 hrn
  -- `kₙ bₙ = (kₙ rₙ / n) (n pₙ) clusterRatio`
  have hfac : ∀ᶠ n in atTop, (k n : ℝ) * b n =
      ((n / r n : ℕ) : ℝ) * r n / n * (n * p n) * clusterRatio P X u r n := by
    filter_upwards [hr0, eventually_gt_atTop 0] with n hrpos hn
    have : (r n : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : P.real {ω | u n < |X 0 ω|} ≠ 0 := (hp0 n).ne'
    rw [clusterRatio]
    dsimp only [b, p, k]
    field_simp
  constructor
  · intro hθ
    have hpow : Tendsto (fun n => (1 - b n) ^ k n) atTop (𝓝 (Real.exp (-(θ * τ)))) := by
      have := hθ.sub hA
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [hr0] with n hn
      rw [hpart n hn]
      ring
    have hlog : Tendsto (fun n => (k n : ℝ) * Real.log (1 - b n)) atTop (𝓝 (-(θ * τ))) := by
      have := ((Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hpow)
      rw [Real.log_exp] at this
      refine this.congr' ?_
      filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
      simp only [Function.comp_apply, Real.log_pow]
    have hkb : Tendsto (fun n => (k n : ℝ) * b n) atTop (𝓝 (θ * τ)) := by
      have hlow : Tendsto (fun n => -((1 - b n) * ((k n : ℝ) * Real.log (1 - b n)))) atTop
          (𝓝 (θ * τ)) := by
        have := ((hb.const_sub 1).mul hlog).neg
        rwa [sub_zero, one_mul, neg_neg] at this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow (by simpa using hlog.neg) ?_ ?_
      · filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
        have hpos : 0 < 1 - b n := by linarith
        have h1 := Real.one_sub_inv_le_log_of_pos hpos
        have h2 : -b n ≤ (1 - b n) * Real.log (1 - b n) := by
          have := mul_le_mul_of_nonneg_left h1 hpos.le
          rwa [mul_sub, mul_one, mul_inv_cancel₀ hpos.ne', sub_sub_cancel_left] at this
        have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (k n))
        linarith
      · filter_upwards [hb.eventually (gt_mem_nhds one_pos)] with n hn
        have hpos : 0 < 1 - b n := by linarith
        have h1 := Real.log_le_sub_one_of_pos hpos
        have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (k n))
        linarith
    have hden := hkr.mul hτ
    rw [one_mul] at hden
    have := hkb.div hden hτ0.ne'
    rw [mul_div_cancel_right₀ _ hτ0.ne'] at this
    refine this.congr' ?_
    filter_upwards [hfac, hden.eventually_ne hτ0.ne'] with n hn hne
    simp only [Pi.div_apply]
    rw [hn, mul_div_cancel_left₀ _ hne]
  · intro hθ
    have hkb : Tendsto (fun n => (k n : ℝ) * b n) atTop (𝓝 (θ * τ)) := by
      have := (hkr.mul hτ).mul hθ
      rw [one_mul, mul_comm τ] at this
      exact this.congr' (hfac.mono fun n hn => hn.symm)
    have hpow := tendsto_one_sub_pow_exp_of_tendsto_mul hb hkb
    have := hA.add hpow
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hr0] with n hn
    rw [hpart n hn]
    ring

/-- **`θ = ϑ - η`.** Under stationarity, the spectral tail process, `n P(|X_0| > uₙ) → τ > 0`,
`rₙ → ∞`, `rₙ / n → 0` and `A(uₙ)`:
`P(M n ≤ uₙ) → exp (-θ τ) ↔ HasEscapeMass P X u r (ϑ - θ)`. -/
theorem HasSpectralTailProcess.tendsto_partialMax_iff_hasEscapeMass (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) (hτ0 : 0 < τ)
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) (θ : ℝ) :
    Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |X k|) n ω ≤ u n}) atTop
        (𝓝 (Real.exp (-(θ * τ)))) ↔
      HasEscapeMass P X u r ((candidateExtremalIndex Q Θ α).toReal - θ) :=
  (hstat.tendsto_partialMax_iff_tendsto_clusterRatio hX (fun _ => h.measureReal_lt_abs_pos _) hτ
    hτ0 hr hrn hA θ).trans
    (h.tendsto_clusterRatio_iff hα hX hΘm hstat (h.tendsto_atTop_of_tendsto_mul hτ) hr θ)

/-- **If the extremal index exists, the escape mass is `ϑ - θ`**, along every level sequence
with `n P(|X_0| > uₙ) → τ > 0` and every block length with `rₙ → ∞`, `rₙ / n → 0` and `A(uₙ)`.
In particular the escape mass is the same for all such choices of `uₙ`, `rₙ`. -/
theorem HasSpectralTailProcess.hasEscapeMass_of_hasExtremalIndex (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {θ : ℝ}
    (hθ : HasExtremalIndex (fun k : ℕ => |X k|) P θ) {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) (hτ0 : 0 < τ)
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) :
    HasEscapeMass P X u r ((candidateExtremalIndex Q Θ α).toReal - θ) :=
  (h.tendsto_partialMax_iff_hasEscapeMass hα hX hΘm hstat hτ hτ0 hr hrn hA θ).1
    (hθ.2 τ hτ0 u (by simpa using hτ))

/-- **`θ = ϑ` if and only if no cluster mass escapes.** If `(|X_n|)` has extremal index `θ`,
then, along any level sequence with `n P(|X_0| > uₙ) → τ > 0` and block length with `rₙ → ∞`,
`rₙ / n → 0` and `A(uₙ)`: `θ = ϑ ↔ HasEscapeMass P X u r 0`. -/
theorem HasSpectralTailProcess.eq_candidateExtremalIndex_iff_hasEscapeMass_zero (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {θ : ℝ}
    (hθ : HasExtremalIndex (fun k : ℕ => |X k|) P θ) {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) (hτ0 : 0 < τ)
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) :
    θ = (candidateExtremalIndex Q Θ α).toReal ↔ HasEscapeMass P X u r 0 := by
  have hη := h.hasEscapeMass_of_hasExtremalIndex hα hX hΘm hstat hθ hτ hτ0 hr hrn hA
  constructor
  · intro heq
    rwa [heq, sub_self] at hη
  · intro h0
    linarith [hη.unique h0]

/-- **A strict gap is a positive escape mass**: `θ < ϑ ↔ η > 0` (same hypotheses). -/
theorem HasSpectralTailProcess.lt_candidateExtremalIndex_iff (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) {θ : ℝ}
    (hθ : HasExtremalIndex (fun k : ℕ => |X k|) P θ) {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ)) (hτ0 : 0 < τ)
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hA : ConditionA (fun k : ℕ => |X k|) P u r) :
    θ < (candidateExtremalIndex Q Θ α).toReal ↔
      ∃ η > 0, HasEscapeMass P X u r η ∧ θ = (candidateExtremalIndex Q Θ α).toReal - η := by
  have hη := h.hasEscapeMass_of_hasExtremalIndex hα hX hΘm hstat hθ hτ hτ0 hr hrn hA
  constructor
  · intro hlt
    exact ⟨_, by linarith, hη, by ring⟩
  · rintro ⟨η, hpos, -, rfl⟩
    linarith

end ExtremalIndex

end ExtremeValueTheory
