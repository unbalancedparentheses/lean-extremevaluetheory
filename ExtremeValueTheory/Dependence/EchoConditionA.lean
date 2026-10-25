/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.EchoProcess
import ExtremeValueTheory.Dependence.Mixing

/-!
# The block condition `𝒜(uₙ)` for the echo process

The echo process `X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})` of
`Dependence/EchoProcess.lean` is a function of iid noise with *unbounded* dependence range: the
echo lag `L(Z)` is not bounded, so the process is not `m`-dependent for any `m` and
`conditionA_of_isMDependent` does not apply. Here we prove the block condition
`𝒜(uₙ)`: `P(M n ≤ uₙ) - P(M rₙ ≤ uₙ) ^ ⌊n / rₙ⌋ → 0` (`ConditionA`) directly, by truncating the
echo lag at `lₙ`.

For a block `A`, the *quiet event* `echoQuiet L Z A u l` (no source of an exceedance of `u` at
times in `A` with echo index `≤ l`) depends only on `Z_s`, `s ∈ [min A - l, max A]`. For blocks at
distance `> l` these index sets are disjoint, so the quiet events are independent. Almost surely,
the quiet event differs from `{max_A X ≤ u}` only on the *long echo event* `echoLong L Z n u l`
(an echo of lag `> l` lands in `{0, …, n - 1}`), of probability `≤ n P(L(Z) > l)`. This gives a
Leadbetter-type factorization bound with rate, and `conditionA_of_forall_abs_le` gives `𝒜(uₙ)`.
With `𝒜(uₙ)` the main theorem `θ = ϑ - η` of `Dependence/ThetaGap.lean` applies to the echo
process.

## Main definitions

* `echoQuiet L Z A u l`, `echoWindow A l`, `echoLong L Z n u l`: the truncated quiet event, the
  innovation times it depends on, and the long echo event.
* `logTruncLag α n = ⌈(2 / α) log n⌉₊`: the truncation lag used for `L(z) = ⌊log z⌋₊ + 1`.

## Main results, with the hypotheses each one uses

Standing hypotheses for the echo process: `α > 0`, `Z` measurable, iid (`iIndepFun Z P`) with
law Pareto(`α`) (`hlaw`), `Z ≥ 0` pointwise (`hpos`), `L` measurable. Neither `L ≥ 1`, nor
`L → ∞`, nor `E[L(Z)] < ∞` is used for `𝒜`.

* `measureReal_echoQuiet_union`: quiet events of blocks at distance `≥ l + 1` are independent
  (independence and measurability only).
* `measureReal_echoLong_le`: `P(echoLong L Z n u l) ≤ n P(L(Z) ≥ l + 1)`.
* `abs_measureReal_maxLE_echoProcess_le`: for `A, B ⊆ {0, …, n - 1}` with `a + (l + 1) ≤ b`
  and `u ≥ 0`, `|P(max_{A ∪ B} |X| ≤ u) - P(max_A |X| ≤ u) P(max_B |X| ≤ u)| ≤
  2 n P(L(Z) ≥ l + 1)`.
* `conditionA_echoProcess`: **`𝒜(uₙ)` for a general echo lag**, assuming `uₙ ≥ 0` eventually,
  `rₙ → ∞`, `rₙ / n → 0`, `lₙ / rₙ → 0`, `(n / rₙ) · n P(L(Z) ≥ lₙ + 1) → 0` and
  `n P(X_0 > uₙ)` eventually bounded.
* `conditionA_logEchoProcess`: **`𝒜(uₙ)` for `L(z) = ⌊log z⌋₊ + 1`**, assuming
  `n P(X_0 > uₙ) → τ` (any `τ`), `rₙ → ∞`, `rₙ / n → 0` and `log n / rₙ → 0`.
* `logEchoProcess_tendsto_partialMax_of_conditionA`: with additionally `τ > 0`, the main theorem
  (`HasSpectralTailProcess.tendsto_partialMax_iff_hasLateReturnMass`) and the cluster-ratio value
  `η = 1/2` give `P(max_{k < n} |X_k| ≤ uₙ) → exp (-τ / 2)`, i.e. `θ = ϑ - η = 1/2`,
  independently of the direct computation `hasExtremalIndex_echoProcess`.
* `logEchoProcess_hasLateReturnMass_of_conditionA`: conversely, `θ = 1/2` and `𝒜(uₙ)` give
  `η = ϑ - θ = 1/2` through `HasSpectralTailProcess.hasLateReturnMass_of_hasExtremalIndex` (same
  hypotheses).

## Remarks

* The rate hypothesis in `conditionA_echoProcess` is a tail condition on the echo lag only:
  with `lₙ ≍ log n` it holds as soon as `P(L(Z) > l)` decays exponentially, which for the
  logarithmic lag is `P(L(Z) ≥ j + 1) ≤ 2^α e^(-α j)` (`measureReal_logLag_le`). The cost of
  the truncation is `lₙ = o(rₙ)`, i.e. `log n = o(rₙ)`: exactly the long-block regime in which
  the cluster ratio is `1/2`. For blocks with `rₙ = O(log n)` this proof does not give `𝒜`.
* The factorization bound does not use stationarity; stationarity enters through
  `conditionA_of_forall_abs_le`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section EchoConditionA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

/-- The *truncated quiet event*: no source of an exceedance of `u` at a time `t ∈ A` with
echo index `j ≤ l`. It only depends on the innovations `Z_s`, `s ∈ echoWindow A l`. -/
def echoQuiet (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (A : Finset ℕ) (u : ℝ) (l : ℕ) : Set Ω :=
  {ω | ∀ t ∈ A, ∀ j ≤ l, ω ∉ echoSource L Z t u j}

/-- The innovation times `t - j`, `t ∈ A`, `j ≤ l`, on which `echoQuiet L Z A u l` depends. -/
def echoWindow (A : Finset ℕ) (l : ℕ) : Set ℤ := {s | ∃ t ∈ A, ∃ j ≤ l, s = (t : ℤ) - j}

/-- The *long echo event*: some exceedance of `u` at a time `t < n` is the echo of an innovation
with echo lag `j > l`. -/
def echoLong (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (n : ℕ) (u : ℝ) (l : ℕ) : Set Ω :=
  {ω | ∃ t < n, ∃ j, l < j ∧ ω ∈ echoSource L Z t u j}

theorem echoQuiet_union (A B : Finset ℕ) (u : ℝ) (l : ℕ) :
    echoQuiet L Z (A ∪ B) u l = echoQuiet L Z A u l ∩ echoQuiet L Z B u l := by
  ext ω
  simp only [echoQuiet, Finset.mem_union, mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨h1, h2⟩ t (ht | ht)
    exacts [h1 t ht, h2 t ht]

theorem measurableSet_echoQuiet (hLm : Measurable L) (A : Finset ℕ) (u : ℝ) (l : ℕ) :
    MeasurableSet[⨆ s ∈ echoWindow A l, MeasurableSpace.comap (Z s) inferInstance]
      (echoQuiet L Z A u l) := by
  set m := ⨆ s ∈ echoWindow A l, MeasurableSpace.comap (Z s) inferInstance
  have e : echoQuiet L Z A u l =
      ⋂ t ∈ A, ⋂ j ∈ Finset.range (l + 1), (echoSource L Z t u j)ᶜ := by
    ext ω
    simp only [echoQuiet, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_compl_iff]
    exact forall₂_congr fun t _ => forall_congr' fun j => by
      constructor
      · exact fun h hj => h (by omega)
      · exact fun h hj => h (by omega)
  rw [e]
  refine @Finset.measurableSet_biInter _ _ m _ A fun t ht => ?_
  refine @Finset.measurableSet_biInter _ _ m _ _ fun j hj => ?_
  refine @MeasurableSet.compl _ _ m ?_
  have hle : MeasurableSpace.comap (Z ((t : ℤ) - j)) inferInstance ≤ m :=
    le_iSup₂ (f := fun s (_ : s ∈ echoWindow A l) =>
      MeasurableSpace.comap (Z s) inferInstance) ((t : ℤ) - j)
      ⟨t, ht, j, by simpa [Nat.lt_succ_iff] using hj, rfl⟩
  exact hle _ ⟨_, measurableSet_echoSourceSet hLm u j, (echoSource_eq _ _ _).symm⟩

theorem disjoint_echoWindow {A B : Finset ℕ} {l : ℕ} (hAB : ∀ a ∈ A, ∀ b ∈ B, a + (l + 1) ≤ b) :
    Disjoint (echoWindow A l) (echoWindow B l) := by
  rw [Set.disjoint_left]
  rintro s ⟨a, ha, i, hi, rfl⟩ ⟨b, hb, j, hj, he⟩
  have := hAB a ha b hb
  omega

omit [IsProbabilityMeasure P] in
/-- **Truncated quiet events of separated blocks are independent.** -/
theorem measureReal_echoQuiet_union (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hLm : Measurable L) {A B : Finset ℕ} {l : ℕ} (hAB : ∀ a ∈ A, ∀ b ∈ B, a + (l + 1) ≤ b)
    (u : ℝ) :
    P.real (echoQuiet L Z (A ∪ B) u l) =
      P.real (echoQuiet L Z A u l) * P.real (echoQuiet L Z B u l) := by
  have hI := indep_iSup_of_disjoint (m := fun s => MeasurableSpace.comap (Z s) inferInstance)
    (fun s => (hZ s).comap_le) hind.iIndep (disjoint_echoWindow hAB)
  have h := (Indep_iff _ _ _).1 hI _ _ (measurableSet_echoQuiet hLm A u l)
    (measurableSet_echoQuiet hLm B u l)
  rw [echoQuiet_union, measureReal_def, h, ENNReal.toReal_mul]
  rfl

omit [IsProbabilityMeasure P] in
/-- An exceedance-free block has no source with index `≤ l`, on the almost sure event that only
finitely many innovations echo into each time. -/
theorem maxLE_echoProcess_subset_echoQuiet {A : Finset ℕ} {u : ℝ} {l : ℕ} {ω : Ω}
    (hb : ∀ t, BddAbove (range fun j => echoTerm L Z t j ω))
    (hω : ω ∈ maxLE (fun k : ℕ => |echoProcess L Z k|) A u) : ω ∈ echoQuiet L Z A u l := by
  intro t ht j _ hmem
  have h1 := lt_echoProcess_of_mem_echoSource (hb t) hmem
  have h2 : |echoProcess L Z t ω| ≤ u := hω t ht
  have := le_abs_self (echoProcess L Z t ω)
  linarith

omit [IsProbabilityMeasure P] in
/-- A quiet block either has no exceedance or contains the echo of an innovation with lag `> l`. -/
theorem echoQuiet_subset (hpos : ∀ t ω, 0 ≤ Z t ω) {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range n) {u : ℝ} (hu : 0 ≤ u) (l : ℕ) :
    echoQuiet L Z A u l ⊆
      maxLE (fun k : ℕ => |echoProcess L Z k|) A u ∪ echoLong L Z n u l := by
  intro ω hω
  by_contra hcon
  simp only [mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [maxLE, mem_ofPred_eq, not_forall, not_le] at h1
  obtain ⟨t, ht, hlt⟩ := h1
  change u < |echoProcess L Z t ω| at hlt
  rw [abs_of_nonneg (echoProcess_nonneg hpos _ _)] at hlt
  obtain ⟨j, hj⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (L := L) (Z := Z) hu t hlt)
  by_cases hjl : j ≤ l
  · exact hω t ht j hjl hj
  · exact h2 ⟨t, Finset.mem_range.1 (hA ht), j, by omega, hj⟩

/-- `P(echoLong) ≤ n P(L(Z) > l)`. -/
theorem measureReal_echoLong_le (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hLm : Measurable L) (n : ℕ) (u : ℝ)
    (l : ℕ) :
    P.real (echoLong L Z n u l) ≤ n * (paretoMeasure 1 α).real {z | l + 1 ≤ L z} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set ν := paretoMeasure 1 α
  set D : ℕ → Set ℝ := fun i => L ⁻¹' {i + l + 1}
  have hD : ∀ i, MeasurableSet (D i) := fun i => hLm (measurableSet_singleton _)
  have hsum : HasSum (fun i => ν.real (D i)) (ν.real {z | l + 1 ≤ L z}) := by
    have hU : (⋃ i, D i) = {z | l + 1 ≤ L z} := by
      ext z
      simp only [D, mem_iUnion, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨i, hi⟩; omega
      · intro h; exact ⟨L z - (l + 1), by omega⟩
    rw [← hU]
    exact hasSum_measureReal_iUnion hD fun i j hij =>
      Disjoint.preimage _ (Set.disjoint_singleton.2 (by omega))
  set E : ℕ → ℕ → Set Ω := fun t i => Z ((t : ℤ) - ((i + l + 1 : ℕ) : ℤ)) ⁻¹' D i
  have hsub : echoLong L Z n u l ⊆ ⋃ t ∈ Finset.range n, ⋃ i, E t i := by
    rintro ω ⟨t, ht, j, hj, -, hL⟩
    refine mem_iUnion₂.2 ⟨t, Finset.mem_range.2 ht, mem_iUnion.2 ⟨j - (l + 1), ?_⟩⟩
    have hj' : j - (l + 1) + l + 1 = j := by omega
    simp only [E, D, mem_preimage, mem_singleton_iff, hj']
    exact hL.resolve_left (by omega)
  have ht : ∀ t : ℕ, P.real (⋃ i, E t i) ≤ ν.real {z | l + 1 ≤ L z} := by
    intro t
    have he : ∀ i, P.real (E t i) = ν.real (D i) :=
      fun i => measureReal_preimage_eq hZ hlaw _ (hD i)
    have hs : Summable fun i => P.real (E t i) := by
      simp_rw [he]; exact hsum.summable
    refine (measureReal_iUnion_le_tsum hs).trans (le_of_eq ?_)
    simp_rw [he]
    exact hsum.tsum_eq
  calc P.real (echoLong L Z n u l) ≤ P.real (⋃ t ∈ Finset.range n, ⋃ i, E t i) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ t ∈ Finset.range n, P.real (⋃ i, E t i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Finset.range n, ν.real {z | l + 1 ≤ L z} := Finset.sum_le_sum fun t _ => ht t
    _ = n * ν.real {z | l + 1 ≤ L z} := by simp

/-- **The factorization bound for the echo process.** For blocks `A, B ⊆ {0, …, n - 1}` at
distance `> l` and `u ≥ 0`,
`|P(max_{A ∪ B} X ≤ u) - P(max_A X ≤ u) P(max_B X ≤ u)| ≤ 2 n P(L(Z) > l)`: up to the event that
an echo of lag `> l` lands in `{0, …, n - 1}`, the two block events are functions of disjoint
sets of innovations. -/
theorem abs_measureReal_maxLE_echoProcess_le (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L) {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.range n) (hB : B ⊆ Finset.range n) {l : ℕ}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a + (l + 1) ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    |P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) (A ∪ B) u) -
        P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) A u) *
          P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) B u)| ≤
      2 * (n * (paretoMeasure 1 α).real {z | l + 1 ≤ L z}) := by
  set Y : ℕ → Ω → ℝ := fun k => |echoProcess L Z k|
  set g := P.real (echoLong L Z n u l)
  have hg := measureReal_echoLong_le hα hZ hlaw hLm (P := P) n u l
  have hb := ae_bddAbove_echoTerm hα hZ hlaw hLm (P := P)
  have hbounds : ∀ C : Finset ℕ, C ⊆ Finset.range n →
      P.real (echoQuiet L Z C u l) - g ≤ P.real (maxLE Y C u) ∧
        P.real (maxLE Y C u) ≤ P.real (echoQuiet L Z C u l) := by
    intro C hC
    constructor
    · have := (measureReal_mono (μ := P) (echoQuiet_subset hpos hC hu l)).trans
        (measureReal_union_le _ _)
      linarith
    · refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [hb] with ω hω h
      exact maxLE_echoProcess_subset_echoQuiet hω h
  obtain ⟨h1, h2⟩ := hbounds (A ∪ B) (Finset.union_subset hA hB)
  obtain ⟨h3, h4⟩ := hbounds A hA
  obtain ⟨h5, h6⟩ := hbounds B hB
  rw [measureReal_echoQuiet_union hZ hind hLm hAB] at h1 h2
  set p := P.real (echoQuiet L Z A u l)
  set q := P.real (echoQuiet L Z B u l)
  set a := P.real (maxLE Y A u)
  set b := P.real (maxLE Y B u)
  have hg0 : 0 ≤ g := measureReal_nonneg
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hb1 : b ≤ 1 := measureReal_le_one
  have hp1 : p ≤ 1 := measureReal_le_one
  have hab1 : a * b ≤ p * q := mul_le_mul h4 h6 hb0 (ha0.trans h4)
  have hab2 : p * q - 2 * g ≤ a * b := by
    nlinarith [mul_nonneg (show 0 ≤ a - (p - g) by linarith) hb0,
      mul_nonneg (ha0.trans h4) (show 0 ≤ b - (q - g) by linarith),
      mul_le_mul_of_nonneg_left hb1 hg0, mul_le_mul_of_nonneg_left hp1 hg0]
  rw [abs_le]
  constructor <;> linarith

/-- **The block condition `𝒜(uₙ)` for the echo process.** Let the echo lag `L` be measurable
and choose truncation lags `lₙ`. If `uₙ ≥ 0` eventually, `rₙ → ∞`, `rₙ / n → 0`, `lₙ / rₙ → 0`,
`(n / rₙ) · n P(L(Z) > lₙ) → 0` and `n P(X_0 > uₙ)` is bounded, then
`P(M n ≤ uₙ) - P(M rₙ ≤ uₙ) ^ ⌊n / rₙ⌋ → 0`.

The echo process is not `m`-dependent (the lag `L(Z)` is unbounded), but it is `lₙ`-dependent
up to the event that an echo of lag `> lₙ` lands in `{0, …, n - 1}`, which has probability
`≤ n P(L(Z) > lₙ)`; `conditionA_of_forall_abs_le` turns this into `𝒜(uₙ)`. -/
theorem conditionA_echoProcess (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L) {u : ℕ → ℝ} {r l : ℕ → ℕ}
    (hu : ∀ᶠ n in atTop, 0 ≤ u n) (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlr : Tendsto (fun n => (l n : ℝ) / r n) atTop (𝓝 0))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) / r n *
      (n * (paretoMeasure 1 α).real {z | l n + 1 ≤ L z})) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n : ℕ in atTop, (n : ℝ) * P.real {ω | u n < echoProcess L Z 0 ω} ≤ C) :
    ConditionA (fun k : ℕ => |echoProcess L Z k|) P u r := by
  set q : ℕ → ℝ := fun n => n * (paretoMeasure 1 α).real {z | l n + 1 ≤ L z}
  refine conditionA_of_forall_abs_le (l := fun n => l n + 1)
    (α := fun n => if 0 ≤ u n then 2 * q n else 1) (C := C)
    ((hasShiftInvariantWindows_echoProcess hZ hind hlaw hLm).isStationary_abs
      (measurable_echoProcess hZ hLm))
    (fun k => continuous_abs.measurable.comp (measurable_echoProcess hZ hLm k)) ?_ hr hrn ?_ ?_ ?_
  · intro n A B hA hB hAB
    split_ifs with h
    · exact abs_measureReal_maxLE_echoProcess_le hα hZ hind hlaw hpos hLm hA hB hAB h
    · have h1 : 0 ≤ P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) (A ∪ B) (u n)) :=
        measureReal_nonneg
      have h2 : P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) (A ∪ B) (u n)) ≤ 1 :=
        measureReal_le_one
      have h3 : 0 ≤ P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) A (u n)) :=
        measureReal_nonneg
      have h4 : P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) A (u n)) ≤ 1 :=
        measureReal_le_one
      have h5 : 0 ≤ P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) B (u n)) :=
        measureReal_nonneg
      have h6 : P.real (maxLE (fun k : ℕ => |echoProcess L Z k|) B (u n)) ≤ 1 :=
        measureReal_le_one
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg h3 h5, mul_le_mul h4 h6 h5 zero_le_one]
  · have h := hlr.add (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr) :
      Tendsto (fun n => (1 : ℝ) / r n) atTop (𝓝 0))
    rw [add_zero] at h
    refine h.congr fun n => ?_
    push_cast
    ring
  · have h := hrate.const_mul 2
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [hu] with n hn
    simp only [hn, ite_true, q]
    ring
  · filter_upwards [hC] with n hn
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hn

end EchoConditionA

/-! ### The logarithmic echo lag -/

section LogLag

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- The truncation lag `lₙ = ⌈(2 / α) log n⌉₊` used for the logarithmic echo lag. -/
noncomputable def logTruncLag (α : ℝ) (n : ℕ) : ℕ := ⌈2 / α * Real.log n⌉₊

/-- For the logarithmic echo lag, `n² P(L(Z) > lₙ) ≤ 2^α` with `lₙ = ⌈(2 / α) log n⌉₊`. -/
theorem mul_mul_measureReal_logLag_le (hα : 0 < α) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (n * (paretoMeasure 1 α).real {z | logTruncLag α n + 1 ≤ logLag z}) ≤
      2 ^ α := by
  set l := logTruncLag α n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := measureReal_logLag_le hα l
  have hl : 2 / α * Real.log n ≤ l := Nat.le_ceil _
  have h2 : Real.exp (-α) ^ l ≤ Real.exp (-(2 * Real.log n)) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have : 2 * Real.log n ≤ α * l := by
      have := mul_le_mul_of_nonneg_left hl hα.le
      rwa [← mul_assoc, mul_div_cancel₀ _ hα.ne'] at this
    linarith
  have h3 : Real.exp (-(2 * Real.log n)) * ((n : ℝ) * n) = 1 := by
    rw [Real.exp_neg, show 2 * Real.log n = Real.log n + Real.log n by ring, Real.exp_add,
      Real.exp_log hn']
    field_simp
  have h4 : (0 : ℝ) ≤ 2 ^ α := by positivity
  calc (n : ℝ) * (n * (paretoMeasure 1 α).real {z | l + 1 ≤ logLag z})
      = ((n : ℝ) * n) * (paretoMeasure 1 α).real {z | l + 1 ≤ logLag z} := by ring
    _ ≤ ((n : ℝ) * n) * (2 ^ α * Real.exp (-(2 * Real.log n))) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 h4)
    _ = 2 ^ α := by rw [mul_comm (2 ^ α), ← mul_assoc, mul_comm _ (Real.exp _), h3, one_mul]

/-- **`𝒜(uₙ)` for the logarithmic echo process** `L(z) = ⌊log z⌋₊ + 1`, in the standard
normalization: if `n P(X_0 > uₙ) → τ`, `rₙ → ∞`, `rₙ / n → 0` and `log n = o(rₙ)`, then the
block condition holds (truncation lags `lₙ = ⌈(2 / α) log n⌉₊`). These are the block lengths of
`logEchoProcess_hasLateReturnMass_of_tendsto`. -/
theorem conditionA_logEchoProcess (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    ConditionA (fun k : ℕ => |echoProcess logLag Z k|) P u r := by
  have hT := hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos measurable_logLag
    one_le_logLag tendsto_logLag
  have hτ' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess logLag Z 0 ω|}) atTop
      (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hτ
  have hu := hT.tendsto_atTop_of_tendsto_mul hτ'
  have hrinv : Tendsto (fun n => (1 : ℝ) / r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hr)
  refine conditionA_echoProcess hα hZ hind hlaw hpos measurable_logLag (l := logTruncLag α)
    (hu.eventually_ge_atTop 0) hr hrn ?_ ?_ (C := τ + 1)
    (hτ.eventually (gt_mem_nhds (lt_add_one τ)) |>.mono fun _ h => h.le)
  · -- `lₙ / rₙ ≤ (2 / α) (log n / rₙ) + 1 / rₙ`
    have hlim := (hlogr.const_mul (2 / α)).add hrinv
    rw [mul_zero, add_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [hr.eventually_gt_atTop 0] with n hrn0
    have hR : (0 : ℝ) < r n := by exact_mod_cast hrn0
    have hc : (logTruncLag α n : ℝ) ≤ 2 / α * Real.log n + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg (by positivity) (Real.log_natCast_nonneg n))).le
    calc (logTruncLag α n : ℝ) / r n ≤ (2 / α * Real.log n + 1) / r n := by gcongr
      _ = 2 / α * (Real.log n / r n) + 1 / r n := by ring
  · -- `(n / rₙ) n P(L(Z) > lₙ) ≤ 2^α / rₙ`
    have hlim := hrinv.const_mul (2 ^ α)
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [hr.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hrn0 hn
    have hR : (0 : ℝ) < r n := by exact_mod_cast hrn0
    have := mul_mul_measureReal_logLag_le hα hn
    calc (n : ℝ) / r n * (n * (paretoMeasure 1 α).real {z | logTruncLag α n + 1 ≤ logLag z})
        = (n * (n * (paretoMeasure 1 α).real {z | logTruncLag α n + 1 ≤ logLag z})) / r n := by
          ring
      _ ≤ 2 ^ α / r n := by gcongr
      _ = 2 ^ α * (1 / r n) := by ring

/-- **`θ = ϑ - η` for the echo process through the main theorem.** Along every level sequence with
`n P(X_0 > uₙ) → τ > 0` and block length with `rₙ → ∞`, `rₙ / n → 0`, `log n = o(rₙ)`, the
block condition holds (`conditionA_logEchoProcess`), so the gap formula of
`Dependence/ThetaGap.lean` applies: the late-return mass computed from the cluster ratio,
`η = 1/2` (`logEchoProcess_hasLateReturnMass_of_tendsto`), gives
`P(M n ≤ uₙ) → exp (-(ϑ - η) τ) = exp (-τ / 2)`. This rederives `θ = 1/2` without the direct
computation of `hasExtremalIndex_echoProcess`. -/
theorem logEchoProcess_tendsto_partialMax_of_conditionA (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |echoProcess logLag Z k|) n ω ≤ u n})
      atTop (𝓝 (Real.exp (-(1 / 2 * τ)))) := by
  have hT := hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos measurable_logLag
    one_le_logLag tendsto_logLag
  have hτ' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess logLag Z 0 ω|}) atTop
      (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hτ
  have hA := conditionA_logEchoProcess hα hZ hind hlaw hpos hτ hr hrn hlogr
  have h := hT.tendsto_partialMax_iff_hasLateReturnMass hα (measurable_echoProcess hZ measurable_logLag)
    measurable_unitSpectral (hasShiftInvariantWindows_echoProcess hZ hind hlaw measurable_logLag)
    hτ' hτ0 hr hrn hA (1 / 2)
  rw [candidateExtremalIndex_unitSpectral hα] at h
  refine h.2 ?_
  have hη := (logEchoProcess_hasLateReturnMass_of_tendsto hα hZ hind hlaw hpos hτ0 hτ hr hrn hlogr).2.1
  convert hη using 1
  norm_num

/-- **The late-return mass from the extremal index, through the main theorem**: since `θ = 1/2`
(`logEchoProcess_theta_lt_vartheta`) and `𝒜(uₙ)` holds (`conditionA_logEchoProcess`),
`HasSpectralTailProcess.hasLateReturnMass_of_hasExtremalIndex` gives `η = ϑ - θ = 1/2` along every
level sequence with `n P(X_0 > uₙ) → τ > 0` and block length with `rₙ → ∞`, `rₙ / n → 0`,
`log n = o(rₙ)`, consistent with the direct cluster-ratio computation. -/
theorem logEchoProcess_hasLateReturnMass_of_conditionA (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlogr : Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0)) :
    HasLateReturnMass P (echoProcess logLag Z) u r (1 / 2) := by
  obtain ⟨hstat, hT, -, hθ⟩ := logEchoProcess_theta_lt_vartheta hα hZ hind hlaw hpos (P := P)
  have hτ' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess logLag Z 0 ω|}) atTop
      (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hτ
  have hθ' : HasExtremalIndex (fun k : ℕ => |echoProcess logLag Z k|) P (1 / 2) := by
    convert hθ using 3 with k
    funext ω
    exact abs_of_nonneg (echoProcess_nonneg hpos _ _)
  have h := hT.hasLateReturnMass_of_hasExtremalIndex hα (measurable_echoProcess hZ measurable_logLag)
    measurable_unitSpectral hstat hθ' hτ' hτ0 hr hrn
    (conditionA_logEchoProcess hα hZ hind hlaw hpos hτ hr hrn hlogr)
  rw [candidateExtremalIndex_unitSpectral hα] at h
  convert h using 1
  norm_num

end LogLag

end ExtremeValueTheory

/-! ### Deprecated names -/

namespace ExtremeValueTheory

@[deprecated (since := "2026-10-23")] alias logEchoProcess_hasEscapeMass_of_conditionA := logEchoProcess_hasLateReturnMass_of_conditionA

end ExtremeValueTheory
