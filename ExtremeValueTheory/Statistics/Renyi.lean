/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.OrderStatistics
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exponential order statistics: the top excesses are conditionally iid

Let `E_0, …, E_{n-1}` be iid standard exponential random variables and let
`E_{(1)} ≥ ⋯ ≥ E_{(n)}` be their descending order statistics. The *Rényi representation*
([dHF, Lemma 3.2.3]; Rényi 1953) says that, given `E_{(k+1)} = s`, the `k` top excesses
`E_{(i)} - E_{(k+1)}`, `i ≤ k`, are (as an unordered family) iid standard exponential. We prove
the form of this statement that we need for tail estimators, for symmetric statistics of the
form `∑_{i ≤ k} ψ(E_{(i)} - E_{(k+1)}, E_{(k+1)})`:

  `E[F(∑_{i<k} ψ(E_{(i+1)} - E_{(k+1)}, E_{(k+1)}), E_{(k+1)})]
    = ∫ E[F(∑_{i<k} ψ(E_i, s), s)] d(law of E_{(k+1)})(s)`.

## Main results

* `ExtremeValueTheory.lintegral_indicator_Ioi_sub_expMeasure`: memorylessness of the exponential
  law, `∫ 1{x > s} f(x - s) dExp(x) = e^{-s} ∫ f dExp` for `s ≥ 0`.
* `ExtremeValueTheory.lintegral_exceedCount_eq`: given the threshold `s`, the number of
  exceedances of `s` is binomial and the excesses over `s` are iid exponential.
* `ExtremeValueTheory.lintegral_orderStat_excess`: the conditional representation above, for
  the product measure `Exp(1)^{⊗n}`.

## References

* [dHF] L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*, Springer, 2006.
* A. Rényi, *On the theory of order statistics*, Acta Math. Acad. Sci. Hungar. 4 (1953).
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace ExtremeValueTheory

/-! ### The standard exponential law -/

section Exponential

instance isProbabilityMeasure_expMeasure_one : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

theorem lintegral_expMeasure (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(expMeasure 1) =
      ∫⁻ x, (Ioi 0).indicator (fun x => ENNReal.ofReal (exp (-x)) * f x) x := by
  have hg : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hg hf]
  refine lintegral_congr_ae ?_
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h0] with x hx
  simp only [Pi.mul_apply, Set.indicator, mem_Ioi]
  have := exponentialPDF_eq 1 x
  simp only [exponentialPDF, exponentialPDFReal] at this
  rw [gammaPDF, this]
  rcases lt_or_gt_of_ne hx with h | h
  · simp [h.not_ge, h.not_gt]
  · simp [h.le, h]

/-- **Memorylessness of the exponential law**: for `s ≥ 0`,
`∫ 1{x > s} f(x - s) dExp(x) = e^{-s} ∫ f dExp`. -/
theorem lintegral_indicator_Ioi_sub_expMeasure {s : ℝ} (hs : 0 ≤ s) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, (Ioi s).indicator (fun x => f (x - s)) x ∂(expMeasure 1) =
      ENNReal.ofReal (exp (-s)) * ∫⁻ x, f x ∂(expMeasure 1) := by
  have hm : Measurable fun x => f (x - s) := hf.comp (measurable_id.sub_const s)
  have hm' : Measurable ((Ioi 0).indicator (fun x => ENNReal.ofReal (exp (-x)) * f x)) :=
    ((measurable_neg.exp.ennreal_ofReal).mul hf).indicator measurableSet_Ioi
  rw [lintegral_expMeasure _ (hm.indicator measurableSet_Ioi),
    lintegral_expMeasure _ hf, ← lintegral_const_mul _ hm']
  rw [← lintegral_add_right_eq_self _ s]
  congr 1 with u
  simp only [Set.indicator, mem_Ioi, add_sub_cancel_right]
  by_cases hu : 0 < u
  · have h1 : 0 < u + s := by linarith
    have h2 : s < u + s := by linarith
    simp only [h1, h2, hu, ite_true]
    rw [neg_add, exp_add, ENNReal.ofReal_mul (exp_pos _).le]
    ring
  · have h2 : ¬ s < u + s := by linarith
    simp [hu, h2]

theorem expMeasure_Ioi {s : ℝ} (hs : 0 ≤ s) :
    expMeasure 1 (Ioi s) = ENNReal.ofReal (exp (-s)) := by
  have h := lintegral_indicator_Ioi_sub_expMeasure hs (fun _ => 1) measurable_const
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [← h, lintegral_indicator measurableSet_Ioi, setLIntegral_const, one_mul]

theorem expMeasure_Iic {s : ℝ} (hs : 0 ≤ s) :
    expMeasure 1 (Iic s) = ENNReal.ofReal (1 - exp (-s)) := by
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, expMeasure_Ioi hs,
    ENNReal.ofReal_sub _ (exp_pos _).le, ENNReal.ofReal_one]

end Exponential

/-! ### Exceedances of a fixed level -/

section Exceedances

variable {m : ℕ}

theorem exceedCount_cons (z : ℝ) (w : Fin m → ℝ) (s : ℝ) :
    exceedCount (Fin.cons z w : Fin (m + 1) → ℝ) s =
      (if s < z then 1 else 0) + exceedCount w s := by
  simp only [exceedCount, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem measurable_exceedCount_fun (s : ℝ) :
    Measurable fun w : Fin m → ℝ => exceedCount w s := by
  have : (fun w : Fin m → ℝ => exceedCount w s) =
      fun w => ∑ i, if s < w i then 1 else 0 := by
    ext w; rw [exceedCount, Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
    measurable_const measurable_const

/-- The excess sum `∑_i 1{w_i > s} φ(w_i - s)`. -/
noncomputable def excessSum (φ : ℝ → ℝ) (s : ℝ) (w : Fin m → ℝ) : ℝ :=
  ∑ i, if s < w i then φ (w i - s) else 0

theorem excessSum_cons (φ : ℝ → ℝ) (s z : ℝ) (w : Fin m → ℝ) :
    excessSum φ s (Fin.cons z w : Fin (m + 1) → ℝ) =
      (if s < z then φ (z - s) else 0) + excessSum φ s w := by
  simp only [excessSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem measurable_excessSum {φ : ℝ → ℝ} (hφ : Measurable φ) (s : ℝ) :
    Measurable (excessSum (m := m) φ s) := by
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
    (hφ.comp (by fun_prop)) measurable_const

/-- Splitting off the first coordinate of a product of exponential laws. -/
theorem lintegral_pi_succ (H : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ y, H y ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1) =
      ∫⁻ z, ∫⁻ w, H (Fin.cons z w) ∂(Measure.pi fun _ : Fin m => expMeasure 1)
        ∂(expMeasure 1) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => expMeasure 1) 0).symm
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  refine (lintegral_prod (μ := expMeasure 1) (ν := Measure.pi fun _ : Fin m => expMeasure 1) (fun p : ℝ × (Fin m → ℝ) =>
    H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm p))
    (hH.comp (MeasurableEquiv.measurable _)).aemeasurable).trans ?_
  congr 1 with z
  congr 1 with w
  congr 1
  ext i
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

theorem measurable_lintegral_sum {j : ℕ} {φ : ℝ → ℝ} (hφ : Measurable φ) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    Measurable fun u => ∫⁻ z, G (φ u + ∑ i, φ (z i)) ∂(Measure.pi fun _ : Fin j => expMeasure 1) := by
  refine Measurable.lintegral_prod_right' (f := fun p : ℝ × (Fin j → ℝ) =>
    G (φ p.1 + ∑ i, φ (p.2 i))) ?_
  exact hG.comp ((hφ.comp measurable_fst).add (Finset.measurable_sum _ fun i _ =>
    hφ.comp ((measurable_pi_apply i).comp measurable_snd)))

/-- **Exceedances of a fixed level by an exponential sample.** For `s ≥ 0`, among `m` iid
standard exponential variables the number `N` of exceedances of `s` is binomial with success
probability `e^{-s}`, and given `N = j` the excesses over `s` are iid standard exponential:

  `E[1{N = j} G(∑_{i : w_i > s} φ(w_i - s))]
    = (m choose j) (1 - e^{-s})^{m-j} e^{-js} E[G(φ(Z_1) + ⋯ + φ(Z_j))]`. -/
theorem lintegral_exceedCount_eq {s : ℝ} (hs : 0 ≤ s) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∀ (m j : ℕ) (G : ℝ → ℝ≥0∞), Measurable G →
      ∫⁻ w, (if exceedCount w s = j then G (excessSum φ s w) else 0)
          ∂(Measure.pi fun _ : Fin m => expMeasure 1) =
        (m.choose j : ℝ≥0∞) * ENNReal.ofReal (1 - exp (-s)) ^ (m - j) *
          ENNReal.ofReal (exp (-s)) ^ j *
          ∫⁻ z, G (∑ i, φ (z i)) ∂(Measure.pi fun _ : Fin j => expMeasure 1) := by
  intro m
  induction m with
  | zero =>
    intro j G hG
    rcases j with _ | j
    · simp [exceedCount, excessSum]
    · simp [exceedCount]
  | succ m ih =>
    intro j G hG
    set p := ENNReal.ofReal (exp (-s)) with hp
    set q := ENNReal.ofReal (1 - exp (-s)) with hq
    have hmeasH : Measurable fun w : Fin (m + 1) → ℝ =>
        if exceedCount w s = j then G (excessSum φ s w) else 0 :=
      Measurable.ite (measurable_exceedCount_fun s (measurableSet_singleton j))
        (hG.comp (measurable_excessSum hφ s)) measurable_const
    rw [lintegral_pi_succ _ hmeasH]
    simp_rw [exceedCount_cons, excessSum_cons]
    rcases j with _ | j
    · have key : ∀ z, ∫⁻ w, (if (if s < z then 1 else 0) + exceedCount w s = 0 then
            G ((if s < z then φ (z - s) else 0) + excessSum φ s w) else 0)
            ∂(Measure.pi fun _ : Fin m => expMeasure 1) =
          (Iic s).indicator (fun _ => ∫⁻ w, (if exceedCount w s = 0 then
            G (excessSum φ s w) else 0) ∂(Measure.pi fun _ : Fin m => expMeasure 1)) z := by
        intro z
        by_cases hz : s < z
        · simp [hz]
        · simp [hz, not_lt.1 hz]
      simp_rw [key]
      rw [lintegral_indicator_const measurableSet_Iic, expMeasure_Iic hs, ih 0 G hG]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, pow_zero, mul_one]
      ring
    · set K : ℝ → ℝ≥0∞ := fun u => ∫⁻ z, G (φ u + ∑ i, φ (z i))
          ∂(Measure.pi fun _ : Fin j => expMeasure 1) with hK
      have hKm : Measurable K := measurable_lintegral_sum hφ hG
      have key : ∀ z, ∫⁻ w, (if (if s < z then 1 else 0) + exceedCount w s = j + 1 then
            G ((if s < z then φ (z - s) else 0) + excessSum φ s w) else 0)
            ∂(Measure.pi fun _ : Fin m => expMeasure 1) =
          (Ioi s).indicator (fun z => (m.choose j : ℝ≥0∞) * q ^ (m - j) * p ^ j * K (z - s)) z +
          (Iic s).indicator (fun _ => (m.choose (j + 1) : ℝ≥0∞) * q ^ (m - (j + 1)) *
            p ^ (j + 1) * ∫⁻ z, G (∑ i, φ (z i))
              ∂(Measure.pi fun _ : Fin (j + 1) => expMeasure 1)) z := by
        intro z
        by_cases hz : s < z
        · have h1 : ∀ w : Fin m → ℝ, (1 + exceedCount w s = j + 1) ↔ exceedCount w s = j := by
            intro w; omega
          simp only [hz, ite_true, h1, Set.indicator, mem_Ioi, mem_Iic, not_le.2 hz,
            ite_false, add_zero]
          exact ih j (fun x => G (φ (z - s) + x)) (hG.comp (measurable_const_add _))
        · simp only [hz, ite_false, zero_add, Set.indicator, mem_Ioi, mem_Iic, not_lt.1 hz,
            ite_true]
          exact ih (j + 1) G hG
      simp_rw [key]
      rw [lintegral_add_left ((Measurable.indicator (by fun_prop) measurableSet_Ioi))]
      rw [lintegral_indicator_Ioi_sub_expMeasure (f := fun u =>
          (m.choose j : ℝ≥0∞) * q ^ (m - j) * p ^ j * K u) hs (by fun_prop),
        lintegral_indicator_const measurableSet_Iic, expMeasure_Iic hs, lintegral_const_mul _ hKm]
      have hKint : ∫⁻ u, K u ∂(expMeasure 1) =
          ∫⁻ z, G (∑ i, φ (z i)) ∂(Measure.pi fun _ : Fin (j + 1) => expMeasure 1) := by
        rw [lintegral_pi_succ (fun z : Fin (j + 1) → ℝ => G (∑ i, φ (z i)))
          (hG.comp (Finset.measurable_sum _ fun i _ => hφ.comp (measurable_pi_apply i)))]
        simp [hK, Fin.sum_univ_succ]
      rw [hKint, ← hp, ← hq]
      set I := ∫⁻ z, G (∑ i, φ (z i)) ∂(Measure.pi fun _ : Fin (j + 1) => expMeasure 1)
      rw [Nat.choose_succ_succ, Nat.cast_add]
      rcases lt_or_ge j m with hjm | hjm
      · have e1 : m + 1 - (j + 1) = m - j := by omega
        have e2 : m - j = (m - (j + 1)) + 1 := by omega
        rw [e1, e2]
        ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : m < j + 1)]
        simp only [Nat.cast_zero, zero_mul, add_zero]
        have e1 : m + 1 - (j + 1) = m - j := by omega
        rw [e1]
        ring

end Exceedances

end ExtremeValueTheory
