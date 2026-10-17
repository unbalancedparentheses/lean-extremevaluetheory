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
  refine (lintegral_prod (μ := expMeasure 1) (ν := Measure.pi fun _ : Fin m => expMeasure 1)
    (fun p : ℝ × (Fin m → ℝ) =>
      H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm p))
    (hH.comp (MeasurableEquiv.measurable _)).aemeasurable).trans ?_
  congr 1 with z
  congr 1 with w
  congr 1
  ext i
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

theorem measurable_lintegral_sum {j : ℕ} {φ : ℝ → ℝ} (hφ : Measurable φ) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    Measurable fun u =>
      ∫⁻ z, G (φ u + ∑ i, φ (z i)) ∂(Measure.pi fun _ : Fin j => expMeasure 1) := by
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

/-! ### Order statistics of a sample without ties -/

section Deterministic

variable {n : ℕ}

theorem orderStat_injective_of_injective {y : Fin n → ℝ} (hy : Function.Injective y) {i j : ℕ}
    (hi : i < n) (hj : j < n) (h : orderStat y i = orderStat y j) : i = j := by
  obtain ⟨σ, hσ⟩ := orderStat_perm y
  have h1 := hσ ⟨i, hi⟩
  have h2 := hσ ⟨j, hj⟩
  simp only at h1 h2
  rw [h1, h2] at h
  have := σ.injective (hy h)
  simpa using this

theorem orderStat_strictAnti {y : Fin n → ℝ} (hy : Function.Injective y) {i j : ℕ}
    (hij : i < j) (hj : j < n) : orderStat y j < orderStat y i :=
  lt_of_le_of_ne (orderStat_anti y hij.le hj) fun h =>
    hij.ne (orderStat_injective_of_injective hy (hij.trans hj) hj h.symm)

/-- Without ties, exactly `m` sample points exceed `X_{(m+1)}`. -/
theorem exceedCount_orderStat {y : Fin n → ℝ} (hy : Function.Injective y) {m : ℕ}
    (hm : m < n) : exceedCount y (orderStat y m) = m := by
  refine le_antisymm ((orderStat_le_iff y hm _).1 le_rfl) ?_
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · simp [h0]
  · have := (lt_orderStat_iff y (by omega : m - 1 < n) (orderStat y m)).1
      (orderStat_strictAnti hy (by omega) hm)
    omega

/-- Without ties, the sum over the top `k` excesses over `X_{(k+1)}`. -/
theorem excessSum_orderStat {y : Fin n → ℝ} (hy : Function.Injective y) {k : ℕ} (hk : k < n)
    (φ : ℝ → ℝ) :
    excessSum φ (orderStat y k) y =
      ∑ i ∈ Finset.range k, φ (orderStat y i - orderStat y k) := by
  rw [excessSum, ← sum_orderStat y (fun v => if orderStat y k < v then φ (v - orderStat y k)
    else 0), ← Finset.sum_range_add_sum_Ico _ hk.le]
  rw [Finset.sum_eq_zero (s := Finset.Ico k n), add_zero]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [orderStat_strictAnti hy (Finset.mem_range.1 hi) hk, ite_true]
  · intro j hj
    rw [Finset.mem_Ico] at hj
    simp only [not_lt.2 (orderStat_anti y hj.1 hj.2), ite_false]

/-- Without ties, a function of `X_{(k+1)}` and of the top excesses is a sum over the sample
point `y_j` which plays the role of `X_{(k+1)}`. -/
theorem orderStat_decomp {y : Fin n → ℝ} (hy : Function.Injective y) {k : ℕ} (hk : k < n)
    (T : ℝ → ℝ≥0∞) :
    T (orderStat y k) = ∑ j, if exceedCount y (y j) = k then T (y j) else 0 := by
  obtain ⟨σ, hσ⟩ := orderStat_perm y
  have hc : ∀ j, exceedCount y (y j) = (σ.symm j : ℕ) := by
    intro j
    have := hσ (σ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [← this, exceedCount_orderStat hy (σ.symm j).2]
  simp_rw [hc]
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp [← hσ ⟨k, hk⟩]
  · intro b _ hb
    have : ¬ ((b : ℕ) = k) := fun h => hb (Fin.ext h)
    simp only [this, ite_false]
  · simp

end Deterministic

/-! ### The conditional representation of the top excesses -/

section Representation

variable {m : ℕ}

/-- Splitting off the `j`-th coordinate of a product of exponential laws. -/
theorem lintegral_pi_succAbove (j : Fin (m + 1)) (H : (Fin (m + 1) → ℝ) → ℝ≥0∞)
    (hH : Measurable H) :
    ∫⁻ y, H y ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1) =
      ∫⁻ z, ∫⁻ w, H (j.insertNth z w) ∂(Measure.pi fun _ : Fin m => expMeasure 1)
        ∂(expMeasure 1) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => expMeasure 1) j).symm
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  refine (lintegral_prod (μ := expMeasure 1) (ν := Measure.pi fun _ : Fin m => expMeasure 1)
    (fun p : ℝ × (Fin m → ℝ) =>
    H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j).symm p))
    (hH.comp (MeasurableEquiv.measurable _)).aemeasurable).trans ?_
  rfl

theorem expMeasure_singleton (z : ℝ) : expMeasure 1 {z} = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton z)]
  exact setLIntegral_measure_zero _ _ (measure_singleton z)

theorem ae_nonneg_expMeasure : ∀ᵐ z ∂(expMeasure 1), 0 ≤ z := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_ : {x : ℝ | ¬ 0 ≤ x} ⊆ (Ioi 0)ᶜ) ?_
  · simp only [mem_ofPred_eq, not_le] at hx
    simp [hx.le]
  · rw [prob_compl_eq_one_sub measurableSet_Ioi, expMeasure_Ioi le_rfl]
    simp

/-- An exponential sample has no ties, almost surely. -/
theorem ae_injective_expMeasure (n : ℕ) :
    ∀ᵐ y ∂(Measure.pi fun _ : Fin n => expMeasure 1), Function.Injective y := by
  have h : ∀ i j : Fin n, i ≠ j →
      ∀ᵐ y ∂(Measure.pi fun _ : Fin n => expMeasure 1), y i ≠ y j := by
    intro i j hij
    rcases n with _ | m
    · exact i.elim0
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hij
    rw [ae_iff]
    have hmeas : MeasurableSet {y : Fin (m + 1) → ℝ | ¬ y (j.succAbove i') ≠ y j} := by
      simp only [ne_eq, not_not]
      exact measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)
    rw [← lintegral_indicator_one hmeas, lintegral_pi_succAbove j _
      (measurable_one.indicator hmeas)]
    refine (lintegral_congr fun z => ?_).trans lintegral_zero
    have hpre : MeasurableSet {w : Fin m → ℝ | w i' = z} :=
      measurableSet_eq_fun (measurable_pi_apply _) measurable_const
    have : (fun w : Fin m → ℝ => {y : Fin (m + 1) → ℝ | ¬ y (j.succAbove i') ≠ y j}.indicator
        (1 : (Fin (m + 1) → ℝ) → ℝ≥0∞) (j.insertNth z w)) =
        {w : Fin m → ℝ | w i' = z}.indicator 1 := by
      funext w
      simp only [Set.indicator, mem_ofPred_eq, ne_eq, not_not, Fin.insertNth_apply_succAbove,
        Fin.insertNth_apply_same, Pi.one_apply]

    rw [this, lintegral_indicator_one hpre]
    exact Measure.pi_eval_preimage_null (μ := fun _ : Fin m => expMeasure 1) (i := i')
      (expMeasure_singleton z)
  have h' : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => expMeasure 1), ∀ i j : Fin n, i ≠ j → y i ≠ y j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    by_cases hij : i = j

    · exact Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [h i j hij] with y hy _ using hy
  filter_upwards [h'] with y hy i j hyij
  by_contra hne
  exact hy i j hne hyij


theorem measurable_uncurry_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ψ : ℝ → ℝ → β} (hψ : Measurable (Function.uncurry ψ)) {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => ψ (f a) (g a) :=
  hψ.comp (hf.prodMk hg)

theorem measurable_exceedCount_self {n : ℕ} (j : Fin n) :
    Measurable fun y : Fin n → ℝ => exceedCount y (y j) := by
  have : (fun y : Fin n → ℝ => exceedCount y (y j)) =
      fun y => ∑ i, if y j < y i then 1 else 0 := by
    ext y; rw [exceedCount, Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
    measurable_const measurable_const

theorem measurable_excessSum_self {n : ℕ} (j : Fin n) {ψ : ℝ → ℝ → ℝ}
    (hψ : Measurable (Function.uncurry ψ)) :
    Measurable fun y : Fin n → ℝ => excessSum (fun x => ψ x (y j)) (y j) y := by
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)) ?_
    measurable_const
  exact measurable_uncurry_comp hψ ((measurable_pi_apply i).sub (measurable_pi_apply j))
    (measurable_pi_apply j)

/-- The contribution of the sample point `y_j` playing the role of `X_{(k+1)}`. -/
theorem lintegral_term_eq {k : ℕ} (j : Fin (m + 1)) {ψ : ℝ → ℝ → ℝ}
    (hψ : Measurable (Function.uncurry ψ)) {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ y, (if exceedCount y (y j) = k then F (excessSum (fun x => ψ x (y j)) (y j) y) (y j)
        else 0) ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1) =
      ∫⁻ z, (m.choose k : ℝ≥0∞) * ENNReal.ofReal (1 - exp (-z)) ^ (m - k) *
        ENNReal.ofReal (exp (-z)) ^ k *
        ∫⁻ x, F (∑ i, ψ (x i) z) z ∂(Measure.pi fun _ : Fin k => expMeasure 1)
        ∂(expMeasure 1) := by
  have hmeas : Measurable fun y : Fin (m + 1) → ℝ => if exceedCount y (y j) = k then
      F (excessSum (fun x => ψ x (y j)) (y j) y) (y j) else 0 :=
    Measurable.ite (measurable_exceedCount_self j (measurableSet_singleton k))
      (measurable_uncurry_comp hF (measurable_excessSum_self j hψ) (measurable_pi_apply j))
      measurable_const
  rw [lintegral_pi_succAbove j _ hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_nonneg_expMeasure] with z hz
  have e1 : ∀ w : Fin m → ℝ, exceedCount (j.insertNth z w) z = exceedCount w z := by
    intro w
    simp only [exceedCount, Finset.card_filter]
    rw [Fin.sum_univ_succAbove _ j]
    simp
  have e2 : ∀ w : Fin m → ℝ, excessSum (fun x => ψ x z) z (j.insertNth z w) =
      excessSum (fun x => ψ x z) z w := by
    intro w
    simp only [excessSum]
    rw [Fin.sum_univ_succAbove _ j]
    simp
  simp only [Fin.insertNth_apply_same, e1, e2]
  exact lintegral_exceedCount_eq hz (hψ.comp (measurable_id.prodMk measurable_const)) m k
    (fun x => F x z) (hF.comp (measurable_id.prodMk measurable_const))

/-- The integral of a function of `X_{(k+1)}` and of the top excesses, as an integral over the
density of `X_{(k+1)}`. -/
theorem lintegral_orderStat_excess_eq {k : ℕ} (hk : k < m + 1) {ψ : ℝ → ℝ → ℝ}
    (hψ : Measurable (Function.uncurry ψ)) {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ y, F (∑ i ∈ Finset.range k, ψ (orderStat y i - orderStat y k) (orderStat y k))
        (orderStat y k) ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1) =
      (m + 1 : ℝ≥0∞) * ∫⁻ z, (m.choose k : ℝ≥0∞) * ENNReal.ofReal (1 - exp (-z)) ^ (m - k) *
        ENNReal.ofReal (exp (-z)) ^ k *
        ∫⁻ x, F (∑ i, ψ (x i) z) z ∂(Measure.pi fun _ : Fin k => expMeasure 1)
        ∂(expMeasure 1) := by
  have hdec : ∀ᵐ y ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1),
      F (∑ i ∈ Finset.range k, ψ (orderStat y i - orderStat y k) (orderStat y k))
        (orderStat y k) = ∑ j, (if exceedCount y (y j) = k then
          F (excessSum (fun x => ψ x (y j)) (y j) y) (y j) else 0) := by
    filter_upwards [ae_injective_expMeasure (m + 1)] with y hy
    rw [← excessSum_orderStat hy hk (fun x => ψ x (orderStat y k))]
    exact orderStat_decomp hy hk (fun s => F (excessSum (fun x => ψ x s) s y) s)
  rw [lintegral_congr_ae hdec, lintegral_finsetSum]
  · simp_rw [lintegral_term_eq _ hψ hF]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · intro j _
    exact Measurable.ite (measurable_exceedCount_self j (measurableSet_singleton k))
      (measurable_uncurry_comp hF (measurable_excessSum_self j hψ) (measurable_pi_apply j))
      measurable_const

/-- **Rényi representation of the top excesses** ([dHF, Lemma 3.2.3]). Let `y` be distributed
according to `Exp(1)^{⊗n}` and `k < n`. For every measurable `ψ` and `F`, the expectation of
`F(∑_{i<k} ψ(Y_{(i+1)} - Y_{(k+1)}, Y_{(k+1)}), Y_{(k+1)})` equals that of
`F(∑_{i<k} ψ(Z_i, Y_{(k+1)}), Y_{(k+1)})`, where the `Z_i` are iid standard exponential
and independent of `Y_{(k+1)}`: conditionally on `Y_{(k+1)}`, the top excesses are iid
standard exponential. -/
theorem lintegral_orderStat_excess {n k : ℕ} (hk : k < n) {ψ : ℝ → ℝ → ℝ}
    (hψ : Measurable (Function.uncurry ψ)) {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ y, F (∑ i ∈ Finset.range k, ψ (orderStat y i - orderStat y k) (orderStat y k))
        (orderStat y k) ∂(Measure.pi fun _ : Fin n => expMeasure 1) =
      ∫⁻ y, ∫⁻ x, F (∑ i, ψ (x i) (orderStat y k)) (orderStat y k)
        ∂(Measure.pi fun _ : Fin k => expMeasure 1)
        ∂(Measure.pi fun _ : Fin n => expMeasure 1) := by
  cases n with
  | zero => omega
  | succ m =>
    set G : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, F (∑ i, ψ (x i) s) s
      ∂(Measure.pi fun _ : Fin k => expMeasure 1) with hG
    have hGm : Measurable G := by
      refine Measurable.lintegral_prod_right' (f := fun p : ℝ × (Fin k → ℝ) =>
        F (∑ i, ψ (p.2 i) p.1) p.1) ?_
      exact measurable_uncurry_comp hF (Finset.measurable_sum _ fun i _ =>
        measurable_uncurry_comp hψ ((measurable_pi_apply i).comp measurable_snd) measurable_fst)
        measurable_fst

    have h2 := lintegral_orderStat_excess_eq hk (ψ := ψ) hψ (F := fun _ s => G s)
      (hGm.comp measurable_snd)
    rw [lintegral_orderStat_excess_eq hk hψ hF]
    change _ = ∫⁻ y, G (orderStat y k) ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1)
    have h3 : ∫⁻ y, G (orderStat y k) ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1) =
        ∫⁻ y, (fun _ s => G s) (∑ i ∈ Finset.range k,
          ψ (orderStat y i - orderStat y k) (orderStat y k)) (orderStat y k)
          ∂(Measure.pi fun _ : Fin (m + 1) => expMeasure 1) := rfl
    rw [h3, h2]
    simp [hG]

theorem measurable_orderStat_pi {n : ℕ} (k : ℕ) :
    Measurable fun y : Fin n → ℝ => orderStat y k :=
  measurable_orderStat (X := fun i (y : Fin n → ℝ) => y i) (fun i => measurable_pi_apply i) k

/-- **Rényi representation**, distributional form: the joint law of
`(∑_{i<k} ψ(Y_{(i+1)} - Y_{(k+1)}, Y_{(k+1)}), Y_{(k+1)})`, pushed forward by `h`, is that of
`(∑_{i<k} ψ(Z_i, Y_{(k+1)}), Y_{(k+1)})` with `Z` an independent `Exp(1)^{⊗k}` sample. -/
theorem map_orderStat_excess {n k : ℕ} (hk : k < n) {ψ : ℝ → ℝ → ℝ}
    (hψ : Measurable (Function.uncurry ψ)) {β : Type*} [MeasurableSpace β] {h : ℝ → ℝ → β}
    (hh : Measurable (Function.uncurry h)) :
    (Measure.pi fun _ : Fin n => expMeasure 1).map (fun y =>
        h (∑ i ∈ Finset.range k, ψ (orderStat y i - orderStat y k) (orderStat y k))
          (orderStat y k)) =
      ((Measure.pi fun _ : Fin n => expMeasure 1).prod
        (Measure.pi fun _ : Fin k => expMeasure 1)).map (fun p =>
          h (∑ i, ψ (p.2 i) (orderStat p.1 k)) (orderStat p.1 k)) := by
  have hmo := measurable_orderStat_pi (n := n) k
  have hm1 : Measurable fun y : Fin n → ℝ =>
      h (∑ i ∈ Finset.range k, ψ (orderStat y i - orderStat y k) (orderStat y k))
        (orderStat y k) :=
    measurable_uncurry_comp hh (Finset.measurable_sum _ fun i _ => measurable_uncurry_comp hψ
      ((measurable_orderStat_pi i).sub hmo) hmo) hmo
  have hm2 : Measurable fun p : (Fin n → ℝ) × (Fin k → ℝ) =>
      h (∑ i, ψ (p.2 i) (orderStat p.1 k)) (orderStat p.1 k) :=
    measurable_uncurry_comp hh (Finset.measurable_sum _ fun i _ => measurable_uncurry_comp hψ
      ((measurable_pi_apply i).comp measurable_snd) (hmo.comp measurable_fst))
      (hmo.comp measurable_fst)
  ext B hB
  rw [Measure.map_apply hm1 hB, Measure.map_apply hm2 hB, ← lintegral_indicator_one (hm1 hB),
    ← lintegral_indicator_one (hm2 hB)]
  have hF : Measurable (Function.uncurry fun x s => B.indicator (1 : β → ℝ≥0∞) (h x s)) :=
    (measurable_one.indicator hB).comp hh
  have := lintegral_orderStat_excess hk hψ hF
  refine (Eq.trans ?_ this).trans ?_
  · rfl
  · rw [lintegral_prod _ ((measurable_one.indicator (hm2 hB)).aemeasurable)]
    rfl


end Representation

end ExtremeValueTheory
