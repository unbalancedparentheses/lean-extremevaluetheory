/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.AR1
import ExtremeValueTheory.Dependence.InfiniteMovingAverageTailProcess

/-!
# Uniqueness of the stationary AR(1) solution

`Dependence/AR1.lean` shows that the moving average `X_t = ∑_{j ≥ 0} φ^j Z_{t-j}` solves the
AR(1) recursion `X_t = φ X_{t-1} + Z_t`. Here we prove that it is the only solution which is
bounded in probability: if `Y` solves the recursion almost surely, `|φ| < 1`, and
`sup_t P(|Y_t| > C) → 0` as `C → ∞` (for instance if `Y` is stationary), then `Y_t = X_t` almost
surely, wherever the series defining `X_t` converges almost surely.

Proof: iterating the recursion, `Y_t = ∑_{j < n} φ^j Z_{t-j} + φ^n Y_{t-n}`. The partial sums
converge almost surely, hence in probability, to `X_t`, and `φ^n Y_{t-n} → 0` in probability by
tightness. So `P(|Y_t - X_t| > δ) = 0` for all `δ > 0`.

## Main results

* `AR1.ae_eq_partialSum_add`: the iterated recursion.
* `AR1.ae_eq_of_tight_of_iterate`: the abstract core, `Y_t = S_n + R_n Y_{t-n}` with `S_n → X`,
  `R_n → 0` a.s. and `Y` tight forces `Y_t = X` a.s.; also used for stochastic recurrence
  equations (`Dependence/SREPathwise.lean`).
* `AR1.ae_eq_process_of_tight`: uniqueness among solutions bounded in probability.
* `AR1.ae_eq_process_of_identDistrib`: uniqueness among solutions with identically distributed
  marginals (e.g. stationary ones).
* `AR1.ae_eq_process`: in the setting of `AR1.hasExtremalIndex` (iid nonnegative noise with
  regularly varying tail of index `-α`, `0 < α < 1`, `0 < φ < 1`), every solution with
  identically distributed marginals is the moving average.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ExtremeValueTheory

namespace AR1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z Y : ℤ → Ω → ℝ} {φ : ℝ}

/-- **The iterated recursion**: if `Y_t = φ Y_{t-1} + Z_t` for all `t`, then
`Y_t = ∑_{j < n} φ^j Z_{t-j} + φ^n Y_{t-n}` for all `t` and `n`. -/
theorem eq_partialSum_add {ω : Ω} (h : ∀ t, Y t ω = φ * Y (t - 1) ω + Z t ω) (t : ℤ) (n : ℕ) :
    Y t ω = ∑ j ∈ Finset.range n, φ ^ j * Z (t - j) ω + φ ^ n * Y (t - n) ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, h (t - n)]
    rw [show t - (n : ℤ) - 1 = t - ((n + 1 : ℕ) : ℤ) by push_cast; ring, pow_succ]
    ring

theorem ae_eq_partialSum_add (hrec : ∀ᵐ ω ∂P, ∀ t, Y t ω = φ * Y (t - 1) ω + Z t ω) :
    ∀ᵐ ω ∂P, ∀ t (n : ℕ),
      Y t ω = ∑ j ∈ Finset.range n, φ ^ j * Z (t - j) ω + φ ^ n * Y (t - n) ω := by
  filter_upwards [hrec] with ω hω t n using eq_partialSum_add hω t n

variable [IsProbabilityMeasure P]

/-- **Uniqueness from an iterated recursion** (the common core of the AR(1) and stochastic
recurrence uniqueness theorems). Suppose that almost surely `Y_t = S_n + R_n Y_{t-n}` for all `n`,
where `S_n → X` and `R_n → 0` almost surely, and `Y` is bounded in probability. Then `Y_t = X`
almost surely. -/
theorem ae_eq_of_tight_of_iterate {X : Ω → ℝ} {S R : ℕ → Ω → ℝ} (t : ℤ)
    (hSm : ∀ n, AEStronglyMeasurable (S n) P) (hRm : ∀ n, AEStronglyMeasurable (R n) P)
    (hiter : ∀ᵐ ω ∂P, ∀ n : ℕ, Y t ω = S n ω + R n ω * Y (t - n) ω)
    (hSlim : ∀ᵐ ω ∂P, Tendsto (fun n => S n ω) atTop (𝓝 (X ω)))
    (hRlim : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 0))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ, ∀ s, P {ω | C < |Y s ω|} ≤ ε) :
    Y t =ᵐ[P] X := by
  have hconv : TendstoInMeasure P S atTop X := tendstoInMeasure_of_tendsto_ae hSm hSlim
  have hRconv : TendstoInMeasure P R atTop (fun _ => 0) := tendstoInMeasure_of_tendsto_ae hRm hRlim
  -- every deviation `δ > 0` has probability zero
  have hδ : ∀ δ : ℝ, 0 < δ → P {ω | δ < |Y t ω - X ω|} = 0 := by
    intro δ hδ
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    rw [zero_add]
    have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos (by exact_mod_cast hε.ne') (by simp)
    obtain ⟨C, hC⟩ := htight _ hε3
    set η := δ / 2 / (max C 0 + 1)
    have hη : 0 < η := by positivity
    have h1 := hconv (ENNReal.ofReal (δ / 2)) (ENNReal.ofReal_pos.2 (by positivity))
    have h2 := hRconv (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
    obtain ⟨n, hn1, hn2⟩ :=
      ((h1.eventually (ge_mem_nhds hε3)).and (h2.eventually (ge_mem_nhds hε3))).exists
    calc P {ω | δ < |Y t ω - X ω|}
        ≤ P (({ω | ENNReal.ofReal (δ / 2) ≤ edist (S n ω) (X ω)} ∪
            {ω | ENNReal.ofReal η ≤ edist (R n ω) 0}) ∪ {ω | C < |Y (t - n) ω|}) := by
          refine measure_mono_ae ?_
          filter_upwards [hiter] with ω hω hmem
          have hmem : δ < |Y t ω - X ω| := hmem
          by_contra hc
          simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_lt] at hc
          obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
          rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity), Real.dist_eq] at hc1 hc2
          rw [sub_zero] at hc2
          have hrem : |R n ω * Y (t - n) ω| < δ / 2 := by
            rw [abs_mul]
            have hM : 0 < max C 0 + 1 := by positivity
            calc |R n ω| * |Y (t - n) ω| ≤ |R n ω| * (max C 0 + 1) :=
                  mul_le_mul_of_nonneg_left (by linarith [le_max_left C 0]) (abs_nonneg _)
              _ < η * (max C 0 + 1) := mul_lt_mul_of_pos_right hc2 hM
              _ = δ / 2 := div_mul_cancel₀ _ hM.ne'
          have : Y t ω - X ω = (S n ω - X ω) + R n ω * Y (t - n) ω := by rw [hω n]; ring
          rw [this] at hmem
          linarith [abs_add_le (S n ω - X ω) (R n ω * Y (t - n) ω)]
      _ ≤ ε / 3 + ε / 3 + ε / 3 :=
          (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add hn1 (by simpa using hn2))) (hC _))
      _ = ε := ENNReal.add_thirds ε
  -- conclude
  have hnull : P {ω | Y t ω ≠ X ω} = 0 := by
    have hsub : {ω | Y t ω ≠ X ω} ⊆ ⋃ k : ℕ, {ω | 1 / ((k : ℝ) + 1) < |Y t ω - X ω|} := by
      intro ω hω
      have hpos : 0 < |Y t ω - X ω| := abs_pos.2 (sub_ne_zero.2 hω)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    exact measure_mono_null hsub (measure_iUnion_null fun k => hδ _ (by positivity))
  exact measure_eq_zero_iff_ae_notMem.1 hnull |>.mono fun ω hω => not_not.1 hω

/-- **Uniqueness of the AR(1) solution among solutions bounded in probability.** Let `|φ| < 1`
and let `Y` solve `Y_t = φ Y_{t-1} + Z_t` almost surely, with `Y` bounded in probability
(`sup_s P(|Y_s| > C)` can be made arbitrarily small). If the series `∑_j φ^j Z_{t-j}` converges
almost surely, then `Y_t` equals it almost surely. -/
theorem ae_eq_process_of_tight (hZ : ∀ t, Measurable (Z t))
    (hφ : |φ| < 1) (hrec : ∀ᵐ ω ∂P, ∀ t, Y t ω = φ * Y (t - 1) ω + Z t ω)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ, ∀ s, P {ω | C < |Y s ω|} ≤ ε) (t : ℤ)
    (hsum : ∀ᵐ ω ∂P, Summable fun j : ℕ => φ ^ j * Z (t - j) ω) :
    Y t =ᵐ[P] process φ Z t := by
  refine ae_eq_of_tight_of_iterate (S := fun n ω => ∑ j ∈ Finset.range n, φ ^ j * Z (t - j) ω)
    (R := fun n _ => φ ^ n) t (fun n => (Finset.measurable_sum _ fun j _ =>
      (hZ _).const_mul _).aestronglyMeasurable) (fun n => aestronglyMeasurable_const) ?_ ?_
    (ae_of_all _ fun _ => tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ) htight
  · filter_upwards [ae_eq_partialSum_add hrec] with ω hω n using hω t n
  · filter_upwards [hsum] with ω hω using hω.hasSum.tendsto_sum_nat

/-- A family of identically distributed real random variables is bounded in probability. -/
theorem tight_of_identDistrib (hY : ∀ t, Measurable (Y t))
    (hid : ∀ t, IdentDistrib (Y t) (Y 0) P P) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ, ∀ s, P {ω | C < |Y s ω|} ≤ ε := by
  intro ε hε
  have hm : ∀ C : ℝ, MeasurableSet {x : ℝ | C < |x|} := fun C =>
    measurableSet_lt measurable_const continuous_abs.measurable
  have hlim : Tendsto (fun k : ℕ => P {ω | (k : ℝ) < |Y 0 ω|}) atTop (𝓝 0) := by
    have hanti : Antitone fun k : ℕ => {ω | (k : ℝ) < |Y 0 ω|} :=
      fun a b hab ω (hω : (b : ℝ) < |Y 0 ω|) =>
        show (a : ℝ) < |Y 0 ω| from lt_of_le_of_lt (by exact_mod_cast hab) hω
    have h := tendsto_measure_iInter_atTop (μ := P) (s := fun k : ℕ => {ω | (k : ℝ) < |Y 0 ω|})
      (fun k => ((hm _).preimage (hY 0)).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ k : ℕ, {ω | (k : ℝ) < |Y 0 ω|}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_lt]
      exact exists_nat_ge _
    rwa [hempty, measure_empty] at h
  obtain ⟨k, hk⟩ := (hlim.eventually (ge_mem_nhds hε)).exists
  refine ⟨k, fun s => ?_⟩
  have := (hid s).measure_mem_eq (hm (k : ℝ))
  simp only [Set.preimage, Set.mem_ofPred_eq] at this
  rw [this]
  exact hk

/-- **Uniqueness of the stationary AR(1) solution**: a solution of `Y_t = φ Y_{t-1} + Z_t`
(`|φ| < 1`) with identically distributed marginals equals `∑_j φ^j Z_{t-j}` almost surely,
wherever that series converges almost surely. -/
theorem ae_eq_process_of_identDistrib (hY : ∀ t, Measurable (Y t))
    (hZ : ∀ t, Measurable (Z t)) (hφ : |φ| < 1)
    (hrec : ∀ᵐ ω ∂P, ∀ t, Y t ω = φ * Y (t - 1) ω + Z t ω)
    (hid : ∀ t, IdentDistrib (Y t) (Y 0) P P) (t : ℤ)
    (hsum : ∀ᵐ ω ∂P, Summable fun j : ℕ => φ ^ j * Z (t - j) ω) :
    Y t =ᵐ[P] process φ Z t :=
  ae_eq_process_of_tight hZ hφ hrec (tight_of_identDistrib hY hid) t hsum

/-- **Uniqueness in the setting of `AR1.hasExtremalIndex`**: for iid nonnegative noise with
`P(Z_0 > x)` regularly varying with index `-α`, `0 < α < 1`, and `0 < φ < 1`, every solution of
the AR(1) recursion with identically distributed marginals is the moving average
`∑_j φ^j Z_{t-j}`, almost surely at every time. -/
theorem ae_eq_process {α : ℝ} (hY : ∀ t, Measurable (Y t)) (hZ : ∀ i, Measurable (Z i))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hα : 0 < α)
    (hα1 : α < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α))
    (hφ0 : 0 < φ) (hφ1 : φ < 1) (hrec : ∀ᵐ ω ∂P, ∀ t, Y t ω = φ * Y (t - 1) ω + Z t ω)
    (hid : ∀ t, IdentDistrib (Y t) (Y 0) P P) (t : ℤ) :
    Y t =ᵐ[P] process φ Z t := by
  have hL' : IsRegularlyVarying (fun x => P.real {ω | x < |Z 0 ω|}) (-α) := by
    simpa only [InfiniteMovingAverage.setOf_lt_abs_eq hZ0] using hL
  have hδ : 0 < α / 2 := by positivity
  have hsum := LinearProcess.ae_summable_mul (Z := fun j : ℕ => Z (t - j)) (fun j => hZ _)
    (hZ 0) (fun j => hident _) hδ (by linarith) hα1 hL' (ψ := fun j => φ ^ j)
    (by simpa only [abs_of_nonneg (pow_nonneg hφ0.le _)] using summable_rpow hφ0 hφ1 hδ)
  exact ae_eq_process_of_identDistrib hY hZ (by rwa [abs_of_pos hφ0]) hrec hid t hsum

end AR1

end ExtremeValueTheory
