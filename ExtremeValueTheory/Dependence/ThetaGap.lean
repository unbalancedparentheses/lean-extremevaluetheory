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
  `0 ≤ clusterRatio - (qₙ(m) - εₙ(m)) ≤ m / rₙ`, where `qₙ(m) = P(max_{0<t≤m} |X_t| ≤ uₙ | |X_0| > uₙ)`
  (stationarity only, no tail process).
* `HasSpectralTailProcess.tendsto_clusterRatio_iff`: **the gap formula.** Under stationarity,
  the spectral tail process, `uₙ → ∞` and `rₙ → ∞`:
  `clusterRatio → L ↔ HasEscapeMass P X u r (ϑ - L)`.
  So the cluster ratio converges iff the escape mass exists, and then `lim = ϑ - η`.
* `HasEscapeMass.unique`, `HasEscapeMass.nonneg`, `HasEscapeMass.le_candidateExtremalIndex`:
  `0 ≤ η ≤ ϑ`.
* `ForwardAntiClusteringAt.hasEscapeMass_zero`: forward anticlustering gives `η = 0`; this
  recovers `HasSpectralTailProcess.tendsto_blockRatio`. The converse fails (see the mixture
  example in `Dependence/ThetaGapExamples.lean`): `η = 0` is strictly weaker than anticlustering.
* `HasSpectralTailProcess.tendsto_partialMax_iff_hasEscapeMass`: under `A(uₙ)`,
  `n P(|X_0| > uₙ) → τ > 0`, `rₙ / n → 0`: `P(M n ≤ uₙ) → exp (-θ τ) ↔ HasEscapeMass (ϑ - θ)`.
* `HasSpectralTailProcess.hasEscapeMass_of_hasExtremalIndex`: if the extremal index `θ` exists,
  then along every level sequence and block length satisfying `A(uₙ)` the escape mass exists and
  equals `ϑ - θ`. In particular the escape mass does not depend on the choice of `uₙ`, `rₙ`.
* `HasSpectralTailProcess.eq_candidateExtremalIndex_iff_hasEscapeMass_zero`: **`θ = ϑ` iff no
  cluster mass escapes**, under `A(uₙ)` along one level sequence.

## Remarks

* The gap formula is an exact, two-sided statement; it replaces the inequality `θ ≤ ϑ` by
  `θ = ϑ - η`, and turns the Bai–Wang phenomenon `θ < ϑ` into the checkable statement `η > 0`.
* The correct condition for `θ = ϑ` is not anticlustering but the *averaged* condition `η = 0`:
  returns at lags `≥ m` within the block are allowed as long as they occur, in the mean, at lags
  `o(rₙ)` (weight `1 - Tₙ / rₙ → 0`)… or with probability `→ 0`.
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

end ExtremeValueTheory
