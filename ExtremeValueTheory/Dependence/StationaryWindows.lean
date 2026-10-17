/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TimeChange
import ExtremeValueTheory.ForMathlib.Probability.Process.Stationary

/-!
# Two notions of stationarity

The library has two notions of strict stationarity:

* `ProbabilityTheory.IsStationary X P` for `ℕ`-indexed processes, phrased through the law of the
  whole path on `ℕ → E` (used by Leadbetter's theorem and the block extremal index);
* `ExtremeValueTheory.HasShiftInvariantWindows P X` for `ℤ`-indexed time series, phrased through
  the laws of finite windows (used by the tail process and the time-change formula).

We show that they agree: a `ℤ`-indexed series has shift-invariant windows if and only if each of
its one-sided restrictions `n ↦ X (n + k)`, `k ∈ ℤ`, is stationary. In particular a stationary
`ℤ`-indexed series restricts to a stationary `ℕ`-indexed sequence `n ↦ X n`, to which the results
on the block extremal index apply.

## Main results

* `ExtremeValueTheory.HasShiftInvariantWindows.map_comp`: shift invariance of the law of
  `(X (τ i))_{i ∈ ι}` for any finite family of times `τ : ι → ℤ` (not necessarily injective).
* `ExtremeValueTheory.HasShiftInvariantWindows.isStationary`: windows ⇒ `IsStationary` of every
  one-sided restriction.
* `ExtremeValueTheory.hasShiftInvariantWindows_of_isStationary`: the converse.
* `ExtremeValueTheory.hasShiftInvariantWindows_iff_isStationary`: the equivalence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℤ → Ω → ℝ}

/-- Shift invariance extends from windows (finite sets of times) to arbitrary finite families of
times `τ : ι → ℤ`, repetitions allowed. -/
theorem HasShiftInvariantWindows.map_comp (hstat : HasShiftInvariantWindows P X)
    (hX : ∀ t, Measurable (X t)) {ι : Type*} [Fintype ι] (τ : ι → ℤ) (h : ℤ) :
    P.map (fun ω i => X (τ i + h) ω) = P.map (fun ω i => X (τ i) ω) := by
  classical
  set W : Finset ℤ := Finset.univ.image τ
  have hτ : ∀ i, τ i ∈ W := fun i => Finset.mem_image_of_mem τ (Finset.mem_univ i)
  set g : (W → ℝ) → (ι → ℝ) := fun y i => y ⟨τ i, hτ i⟩
  have hg : Measurable g := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have h1 : (fun ω i => X (τ i + h) ω) = g ∘ (fun ω (t : W) => X (t + h) ω) := rfl
  have h2 : (fun ω i => X (τ i) ω) = g ∘ (fun ω (t : W) => X t ω) := rfl
  rw [h1, h2, ← Measure.map_map hg (measurable_pi_iff.2 fun t => hX _),
    ← Measure.map_map hg (measurable_pi_iff.2 fun t => hX _), hstat h W]

/-- Probability version of `HasShiftInvariantWindows.map_comp`. -/
theorem HasShiftInvariantWindows.measure_preimage_comp (hstat : HasShiftInvariantWindows P X)
    (hX : ∀ t, Measurable (X t)) {ι : Type*} [Fintype ι] (τ : ι → ℤ) (h : ℤ)
    {B : Set (ι → ℝ)} (hB : MeasurableSet B) :
    P {ω | (fun i => X (τ i + h) ω) ∈ B} = P {ω | (fun i => X (τ i) ω) ∈ B} := by
  have := congrArg (fun μ : Measure (ι → ℝ) => μ B) (hstat.map_comp hX τ h)
  rwa [Measure.map_apply (measurable_pi_iff.2 fun i => hX _) hB,
    Measure.map_apply (measurable_pi_iff.2 fun i => hX _) hB] at this

/-- **Windows ⇒ path stationarity.** If the `ℤ`-indexed series `X` has shift-invariant windows,
then every one-sided restriction `n ↦ X (n + k)` is a stationary `ℕ`-indexed process in the sense
of `ProbabilityTheory.IsStationary`. The laws on `ℕ → ℝ` are compared on measurable cylinders,
which form a generating π-system. -/
theorem HasShiftInvariantWindows.isStationary [IsFiniteMeasure P]
    (hstat : HasShiftInvariantWindows P X) (hX : ∀ t, Measurable (X t)) (k : ℤ) :
    IsStationary (fun (n : ℕ) ω => X (n + k) ω) P := by
  unfold IsStationary
  have hm1 : Measurable fun ω (n : ℕ) => X (((n + 1 : ℕ) : ℤ) + k) ω :=
    measurable_pi_iff.2 fun n => hX _
  have hm0 : Measurable fun ω (n : ℕ) => X ((n : ℤ) + k) ω := measurable_pi_iff.2 fun n => hX _
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun C hC => ?_) ?_
  · obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
    rw [Measure.map_apply hm1 (hS.cylinder), Measure.map_apply hm0 (hS.cylinder)]
    have := hstat.measure_preimage_comp hX (fun i : s => ((i : ℕ) : ℤ) + k) 1 hS
    convert this using 2 <;> ext ω <;> simp only [mem_preimage, mem_cylinder, Set.mem_ofPred_eq,
      Finset.restrict_def]
    congr! 3
    push_cast
    ring
  · rw [Measure.map_apply hm1 MeasurableSet.univ, Measure.map_apply hm0 MeasurableSet.univ]
    rfl

/-- **Path stationarity ⇒ windows.** If every one-sided restriction `n ↦ X (n + k)` of a
`ℤ`-indexed series is stationary, then `X` has shift-invariant windows. -/
theorem hasShiftInvariantWindows_of_isStationary (hX : ∀ t, Measurable (X t))
    (hs : ∀ k : ℤ, IsStationary (fun (n : ℕ) ω => X (n + k) ω) P) :
    HasShiftInvariantWindows P X := by
  -- nonnegative shifts, for every series satisfying the hypothesis
  have key : ∀ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) →
      (∀ k : ℤ, IsStationary (fun (n : ℕ) ω => X (n + k) ω) P) →
      ∀ (h : ℕ) (S : Finset ℤ),
        P.map (fun ω (t : S) => X (t + h) ω) = P.map (fun ω (t : S) => X t ω) := by
    intro X hX hs h S
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ∀ t ∈ S, k ≤ t := by
      obtain ⟨k, hk⟩ := S.bddBelow
      exact ⟨k, fun t ht => hk ht⟩
    set F : (ℕ → ℝ) → (S → ℝ) := fun x t => x ((t : ℤ) - k).toNat
    have hF : Measurable F := measurable_pi_iff.2 fun t => measurable_pi_apply _
    have hY : ∀ n : ℕ, Measurable fun ω => X ((n : ℤ) + k) ω := fun n => hX _
    have e1 : (fun ω (t : S) => X (t + h) ω) = F ∘ fun ω n => X (((n + h : ℕ) : ℤ) + k) ω := by
      funext ω t
      simp only [Function.comp_apply, F]
      congr 1
      have := hk t t.2
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have e2 : (fun ω (t : S) => X t ω) = F ∘ fun ω n => X ((n : ℕ) + k) ω := by
      funext ω t
      simp only [Function.comp_apply, F]
      congr 1
      have := hk t t.2
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    rw [e1, e2, ← Measure.map_map hF (measurable_path_shift hY h),
      ← Measure.map_map hF (measurable_path hY), (hs k).map_shift hY h]
  intro h S
  rcases le_or_gt 0 h with h0 | h0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, h = n := ⟨h.toNat, by omega⟩
    exact key X hX hs n S
  · -- negative shifts: apply the nonnegative case to the shifted series `X (· + h)`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -h := ⟨(-h).toNat, by omega⟩
    have := key (fun t => X (t + h)) (fun t => hX _)
      (fun k => by simpa [add_assoc] using hs (k + h)) n S
    simp only [hn, add_assoc, neg_add_cancel, add_zero] at this
    exact this.symm

/-- **The two notions of stationarity agree**: a `ℤ`-indexed series has shift-invariant windows
if and only if each of its one-sided restrictions `n ↦ X (n + k)` is stationary. -/
theorem hasShiftInvariantWindows_iff_isStationary [IsFiniteMeasure P]
    (hX : ∀ t, Measurable (X t)) :
    HasShiftInvariantWindows P X ↔ ∀ k : ℤ, IsStationary (fun (n : ℕ) ω => X (n + k) ω) P :=
  ⟨fun h k => h.isStationary hX k, hasShiftInvariantWindows_of_isStationary hX⟩

/-- A stationary `ℤ`-indexed series restricts to a stationary `ℕ`-indexed sequence. -/
theorem HasShiftInvariantWindows.isStationary_nat [IsFiniteMeasure P]
    (hstat : HasShiftInvariantWindows P X) (hX : ∀ t, Measurable (X t)) :
    IsStationary (fun (n : ℕ) ω => X n ω) P := by
  simpa using hstat.isStationary hX 0

end ExtremeValueTheory
