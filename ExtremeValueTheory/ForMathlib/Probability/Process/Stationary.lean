/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi

/-!
# Stationary processes in discrete time

A process `X : ℕ → Ω → E` is (strictly) stationary for a measure `μ` if the law of its path
`ω ↦ (X n ω)ₙ` on `ℕ → E` is invariant under the shift `(xₙ)ₙ ↦ (xₙ₊₁)ₙ`. Equivalently, all
finite dimensional distributions are invariant under time shifts.

## Main definitions and results

* `ProbabilityTheory.IsStationary X μ`: the law of the path of `X` is shift invariant.
* `ProbabilityTheory.IsStationary.map_shift`: the law of `(X (n + s))ₙ` is the law of `(X n)ₙ`
  for every `s`.
* `ProbabilityTheory.IsStationary.measure_preimage_shift`: the same statement for measurable
  sets of paths, i.e. invariance of the finite dimensional (and all path) events.
* `ProbabilityTheory.IsStationary.identDistrib`: the marginals of a stationary process are
  identically distributed.
* `ProbabilityTheory.isStationary_of_iIndepFun`: iid sequences are stationary.
* `ProbabilityTheory.IsStationary.factor`: a sliding window functional
  `Y t = f (X t, X (t + 1), …)` of a stationary process is stationary.
-/

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure Ω} {X : ℕ → Ω → E}

/-- A discrete time process `X` is *(strictly) stationary* for `μ` if the law of its path
`ω ↦ (X n ω)ₙ` is invariant under the shift: the paths `(X (n + 1))ₙ` and `(X n)ₙ` have the same
law. -/
def IsStationary (X : ℕ → Ω → E) (μ : Measure Ω) : Prop :=
  μ.map (fun ω n ↦ X (n + 1) ω) = μ.map (fun ω n ↦ X n ω)

lemma measurable_path_shift (hX : ∀ n, Measurable (X n)) (s : ℕ) :
    Measurable (fun ω n ↦ X (n + s) ω) :=
  Measurable.of_eval fun n ↦ hX (n + s)

lemma measurable_path (hX : ∀ n, Measurable (X n)) : Measurable (fun ω n ↦ X n ω) :=
  Measurable.of_eval hX

/-- The shift on `ℕ → E` is measurable. -/
lemma measurable_shift (s : ℕ) : Measurable (fun (x : ℕ → E) (n : ℕ) ↦ x (n + s)) :=
  Measurable.of_eval fun n ↦ measurable_pi_apply (n + s)

namespace IsStationary

/-- The law of the path of a stationary process is invariant under every time shift. -/
lemma map_shift (h : IsStationary X μ) (hX : ∀ n, Measurable (X n)) (s : ℕ) :
    μ.map (fun ω n ↦ X (n + s) ω) = μ.map (fun ω n ↦ X n ω) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e : (fun ω n ↦ X (n + (s + 1)) ω) =
        (fun (x : ℕ → E) (n : ℕ) ↦ x (n + 1)) ∘ fun ω n ↦ X (n + s) ω := by
      funext ω n; simp only [Function.comp_apply]; congr 1; omega
    rw [e, ← Measure.map_map (measurable_shift 1) (measurable_path_shift hX s), ih,
      Measure.map_map (measurable_shift 1) (measurable_path hX)]
    exact h

/-- Events of the path of a stationary process have time shift invariant probabilities. -/
lemma measure_preimage_shift (h : IsStationary X μ) (hX : ∀ n, Measurable (X n)) (s : ℕ)
    {C : Set (ℕ → E)} (hC : MeasurableSet C) :
    μ ((fun ω n ↦ X (n + s) ω) ⁻¹' C) = μ ((fun ω n ↦ X n ω) ⁻¹' C) := by
  rw [← Measure.map_apply (measurable_path_shift hX s) hC, h.map_shift hX s,
    Measure.map_apply (measurable_path hX) hC]

/-- Real-valued version of `IsStationary.measure_preimage_shift`. -/
lemma measureReal_preimage_shift (h : IsStationary X μ) (hX : ∀ n, Measurable (X n)) (s : ℕ)
    {C : Set (ℕ → E)} (hC : MeasurableSet C) :
    μ.real ((fun ω n ↦ X (n + s) ω) ⁻¹' C) = μ.real ((fun ω n ↦ X n ω) ⁻¹' C) := by
  simp only [Measure.real, h.measure_preimage_shift hX s hC]

/-- The marginals of a stationary process are identically distributed. -/
lemma identDistrib (h : IsStationary X μ) (hX : ∀ n, Measurable (X n)) (s : ℕ) :
    IdentDistrib (X s) (X 0) μ μ where
  aemeasurable_fst := (hX s).aemeasurable
  aemeasurable_snd := (hX 0).aemeasurable
  map_eq := by
    have h1 : X s = (fun x : ℕ → E ↦ x 0) ∘ fun ω n ↦ X (n + s) ω := by
      funext ω; simp
    have h2 : X 0 = (fun x : ℕ → E ↦ x 0) ∘ fun ω n ↦ X n ω := rfl
    rw [h1, h2, ← Measure.map_map (measurable_pi_apply 0) (measurable_path_shift hX s),
      ← Measure.map_map (measurable_pi_apply 0) (measurable_path hX), h.map_shift hX s]

/-- **Factors of stationary processes.** If `X` is stationary and `Y t = f ((X (n + t))ₙ)` for a
measurable `f` (a sliding window functional such as a moving average or moving maximum), then
`Y` is stationary. -/
lemma factor (h : IsStationary X μ) (hX : ∀ n, Measurable (X n)) {f : (ℕ → E) → F}
    (hf : Measurable f) : IsStationary (fun t ω ↦ f (fun n ↦ X (n + t) ω)) μ := by
  set Ψ : (ℕ → E) → ℕ → F := fun x t ↦ f (fun n ↦ x (n + t)) with hΨ
  have hΨm : Measurable Ψ := Measurable.of_eval fun t ↦ hf.comp (measurable_shift t)
  have e1 : (fun ω (t : ℕ) ↦ f (fun n ↦ X (n + (t + 1)) ω)) = Ψ ∘ fun ω n ↦ X (n + 1) ω := by
    funext ω t; simp only [hΨ, Function.comp_apply]; congr 1
  have e2 : (fun ω (t : ℕ) ↦ f (fun n ↦ X (n + t) ω)) = Ψ ∘ fun ω n ↦ X n ω := rfl
  unfold IsStationary
  rw [e1, e2, ← Measure.map_map hΨm (measurable_path_shift hX 1),
    ← Measure.map_map hΨm (measurable_path hX), h.map_shift hX 1]

end IsStationary

/-- **iid sequences are stationary.** -/
lemma isStationary_of_iIndepFun [IsProbabilityMeasure μ] (hX : ∀ n, Measurable (X n))
    (hind : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) : IsStationary X μ := by
  have h1 : iIndepFun (fun n ↦ X (n + 1)) μ := hind.precomp (add_left_injective 1)
  unfold IsStationary
  rw [h1.map_fun_eq_infinitePi_map (fun n ↦ hX (n + 1)),
    hind.map_fun_eq_infinitePi_map hX]
  congr 1
  funext n
  rw [(hid (n + 1)).map_eq, (hid n).map_eq]

end ProbabilityTheory
