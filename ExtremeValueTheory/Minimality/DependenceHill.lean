/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MixtureProcess
import ExtremeValueTheory.Statistics.HillDependent

/-!
# The mixing condition in Hill consistency under dependence cannot be dropped

`tendstoInMeasure_hill_of_alphaMixing` proves `H_{k(n),n} → 1/α` in probability for a stationary
sequence with regularly varying marginal tail under two conditions on a block length `rₙ`:

* the **cluster condition** `(1/kₙ) ∑_{1 ≤ h ≤ rₙ} P(X_h > uₙ | X_0 > uₙ) → 0`, and
* the **mixing condition** `(n / kₙ²) ∑_{rₙ < h < n} α(h) → 0`.

The constant/iid mixture of `Dependence/MixtureProcess.lean` (with `P(E) > 0`) is stationary with
a Pareto(`α`) marginal and satisfies the cluster condition with `rₙ = 0` (an empty sum), but on
`E` the whole sample is constant, so the Hill estimator is `0` there and is **not consistent**
(`not_tendstoInMeasure_hill_mixture`). Hence the mixing condition fails for it, and it cannot be
removed from the theorem (`mixture_hill_needs_mixing`): stationarity, regular variation and
identically distributed marginals do not give Hill consistency.

## What is left open

Whether the cluster condition itself is necessary (given the mixing condition) is not settled
here: a counterexample would need a mixing sequence whose clusters at level `uₙ` have size
comparable to `kₙ`, so that the top `kₙ` order statistics come from a bounded number of clusters.
Our explicit dependent models (moving maxima, moving averages, the echo process) have clusters of
bounded size, and for them the cluster condition holds for `rₙ` fixed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory.Minimality

/-- **The Hill estimator of a constant sample vanishes**: if all `n` observations are equal and
`k < n`, all the log-spacings are `0`. -/
theorem hill_const {n : ℕ} (x : Fin n → ℝ) {a : ℝ} (hx : ∀ i, x i = a) {k : ℕ} (hk : k < n) :
    hill x k = 0 := by
  have h : ∀ j, j < n → orderStat x j = a := fun j hj => by rw [orderStat_of_lt x hj, hx]
  unfold hill
  rw [Finset.sum_eq_zero fun i hi => by
    rw [h i ((Finset.mem_range.1 hi).trans hk), h k hk, sub_self], mul_zero]

section Mixture

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {E : Set Ω}

omit [IsProbabilityMeasure P] in
/-- **The Hill estimator is inconsistent for the constant/iid mixture** with `P(E) > 0`, for every
`kₙ` with `kₙ / n → 0`: on `E` it vanishes for `kₙ < n`, so
`P(|H_{kₙ,n} - 1/α| ≥ 1/α) ≥ P(E)`. -/
theorem not_tendstoInMeasure_hill_mixture (hα : 0 < α) (hp0 : 0 < P.real E) {k : ℕ → ℕ}
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    ¬ TendstoInMeasure P (fun n ω => hill (fun i : Fin n => mixtureProcess E Z i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  intro h
  have hPE : 0 < P E := by
    rw [measureReal_def] at hp0
    exact ENNReal.toReal_pos_iff.1 hp0 |>.1
  have hlim := h (ENNReal.ofReal (1 / α)) (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨n, hn1, hn2, hn0⟩ := ((hlim.eventually (Iio_mem_nhds hPE)).and
    ((hkn.eventually (gt_mem_nhds one_pos)).and (eventually_gt_atTop 0))).exists
  have hkn' : k n < n := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_one hn'] at hn2
    exact_mod_cast hn2
  have hsub : E ⊆ {ω | ENNReal.ofReal (1 / α) ≤
      edist (hill (fun i : Fin n => mixtureProcess E Z i ω) (k n)) (1 / α)} := by
    intro ω hω
    rw [mem_ofPred_eq, hill_const _ (fun i => mixtureProcess_of_mem hω _) hkn', edist_dist,
      Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by positivity)]
  exact absurd (measure_mono hsub) (not_le.2 hn1)

/-- **The mixing condition cannot be dropped from `tendstoInMeasure_hill_of_alphaMixing`.** For
the constant/iid mixture with `P(E) > 0`, every `kₙ → ∞` with `kₙ / n → 0` and `rₙ = 0`:
the sequence is stationary, its marginal tail is regularly varying with index `-α`, the cluster
condition holds, but the Hill estimator is not consistent; consequently the mixing condition
`(n / kₙ²) ∑_{0 < h < n} α(h) → 0` fails. -/
theorem mixture_hill_needs_mixing (hE : MeasurableSet E)
    (hEZ : Indep (MeasurableSpace.generateFrom {E}) (innovationSigma Z) P) (hα : 0 < α)
    (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hp0 : 0 < P.real E) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    IsStationary (fun (n : ℕ) ω => mixtureProcess E Z n ω) P ∧
      IsRegularlyVarying (fun x => (P {ω | x < mixtureProcess E Z (0 : ℕ) ω}).toReal) (-α) ∧
      (∀ (u : ℕ → ℝ) (c : ℝ), 0 < c → Tendsto u atTop atTop →
        Tendsto (fun n => n * (P {ω | u n < mixtureProcess E Z (0 : ℕ) ω}).toReal / k n) atTop
          (𝓝 c) →
        Tendsto (fun n => (∑ h ∈ Finset.Icc 1 ((fun _ => 0 : ℕ → ℕ) n),
            P.real {ω | u n < mixtureProcess E Z (0 : ℕ) ω ∧ u n < mixtureProcess E Z h ω}) /
          (P {ω | u n < mixtureProcess E Z (0 : ℕ) ω}).toReal / k n) atTop (𝓝 0)) ∧
      ¬ TendstoInMeasure P (fun n ω => hill (fun i : Fin n => mixtureProcess E Z i ω) (k n))
        atTop (fun _ => 1 / α) ∧
      ¬ Tendsto (fun n : ℕ => (n : ℝ) / (k n : ℝ) ^ 2 *
        ∑ h ∈ Finset.Ico ((fun _ => 0 : ℕ → ℕ) n + 1) n,
          (alphaMixing (fun (n : ℕ) ω => mixtureProcess E Z n ω) P h).toReal) atTop (𝓝 0) := by
  have hstat : IsStationary (fun (n : ℕ) ω => mixtureProcess E Z n ω) P :=
    (hasShiftInvariantWindows_mixture hE hEZ hZ hind hlaw).isStationary_nat
      (measurable_mixtureProcess hE hZ)
  have hRV : IsRegularlyVarying
      (fun x => (P {ω | x < mixtureProcess E Z (0 : ℕ) ω}).toReal) (-α) := by
    refine (IsRegularlyVarying.rpow_id (-α)).congr ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Nat.cast_zero, mixtureProcess_zero]
    exact (measureReal_lt_of_map_eq hZ hlaw hα 0 hx).symm
  have hclus : ∀ (u : ℕ → ℝ) (c : ℝ), 0 < c → Tendsto u atTop atTop →
      Tendsto (fun n => n * (P {ω | u n < mixtureProcess E Z (0 : ℕ) ω}).toReal / k n) atTop
        (𝓝 c) →
      Tendsto (fun n => (∑ h ∈ Finset.Icc 1 ((fun _ => 0 : ℕ → ℕ) n),
          P.real {ω | u n < mixtureProcess E Z (0 : ℕ) ω ∧ u n < mixtureProcess E Z h ω}) /
        (P {ω | u n < mixtureProcess E Z (0 : ℕ) ω}).toReal / k n) atTop (𝓝 0) :=
    fun _ _ _ _ _ => by simp
  have hnot := not_tendstoInMeasure_hill_mixture (Z := Z) hα hp0 hkn
  refine ⟨hstat, hRV, hclus, hnot, fun hmix => hnot ?_⟩
  exact tendstoInMeasure_hill_of_alphaMixing (measurable_mixtureProcess hE hZ ·) hstat hα hRV hk
    hkn (fun _ => 0) hclus hmix

end Mixture

end ExtremeValueTheory.Minimality

/-! ### Deprecated names -/

namespace ExtremeValueTheory

@[deprecated (since := "2026-10-23")] alias hill_const := Minimality.hill_const
@[deprecated (since := "2026-10-23")] alias not_tendstoInMeasure_hill_mixture := Minimality.not_tendstoInMeasure_hill_mixture
@[deprecated (since := "2026-10-23")] alias mixture_hill_needs_mixing := Minimality.mixture_hill_needs_mixing

end ExtremeValueTheory
