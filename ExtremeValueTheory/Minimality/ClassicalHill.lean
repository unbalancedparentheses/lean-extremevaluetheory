/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.HillNormality

/-!
# Minimality of the intermediate-sequence conditions in Hill consistency

`ExtremeValueTheory.tendstoInMeasure_hill` (weak consistency of the Hill estimator) assumes that
`k = k(n)` is an *intermediate sequence*: `k(n) → ∞` and `k(n) / n → 0`. We show that both
conditions are necessary.

* **`k → ∞` is necessary**, even for an exact Pareto sample
  (`not_tendstoInMeasure_hill_pareto_of_not_tendsto`): if `k(n) < n` eventually and `k` does not
  tend to infinity, then `H_{k(n),n}` does not converge in probability to `1/α`. The reason is
  the Rényi representation: for `0 < k < n`, the Hill estimator of a Pareto sample has the law of
  `(1/α) (E_1 + ⋯ + E_k) / k` with `E_i` iid standard exponential, independently of `n`
  (`map_hill_pareto`), and `P(|H - 1/α| ≥ 1/(2α)) ≥ e^{-2k}`. For Pareto samples we obtain the
  characterization `tendstoInMeasure_hill_pareto_iff`: under `k/n → 0` and `k < n`, consistency
  holds **iff** `k → ∞`.
* **`k / n → 0` is necessary** (`not_tendstoInMeasure_hill_of_le_mul`): for every `0 < c ≤ 1`
  there is a law (`hillLaw α b` with `e^{-b} = c / 8`: `X = exp((E - b)⁺ / α)`, `E ~ Exp(1)`,
  whose survival function is `e^{-b} x^{-α}` on `[1, ∞)`, hence regularly varying with index
  `-α`) such that for **every** `k` with `c n ≤ k(n) < n` eventually, the Hill estimator is not
  consistent: `P(H_{k,n} < 1/(2α)) ≥ 3/4` for all large `n`. This is a pure bias effect: when a
  positive fraction of the sample is used, the estimator sees the non-Pareto body of the law
  (here an atom at `1` of mass `1 - c/8`).

Both counterexamples are non-vacuous: iid sequences with the required laws exist
(`exists_hill_k_bounded_counterexample`, `exists_hill_k_linear_counterexample`).

## Summary

| hypothesis | status |
|---|---|
| `k(n) → ∞` | necessary (even for exact Pareto): `not_tendstoInMeasure_hill_pareto_of_not_tendsto` |
| `k(n) / n → 0` | necessary: `not_tendstoInMeasure_hill_of_le_mul` |
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace ExtremeValueTheory.Minimality

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The family of laws `exp((E - b)⁺ / α)` -/

/-- The law of `exp((E - b)⁺ / α)`, `E ~ Exp(1)`: for `b = 0` this is `Pareto(α)`; for `b > 0`
the survival function is `e^{-b} x^{-α}` on `[1, ∞)`, with an atom of mass `1 - e^{-b}` at `1`. -/
noncomputable def hillLaw (α b : ℝ) : Measure ℝ :=
  (expMeasure 1).map (fun e => exp (α⁻¹ * max (e - b) 0))

theorem measurable_hillLaw_fun (α b : ℝ) :
    Measurable (fun e : ℝ => exp (α⁻¹ * max (e - b) 0)) := by fun_prop

instance (α b : ℝ) : IsProbabilityMeasure (hillLaw α b) := by
  unfold hillLaw; infer_instance

variable {α b : ℝ}

theorem hillLaw_Ioi (hα : 0 < α) (hb : 0 ≤ b) {x : ℝ} (hx : 1 ≤ x) :
    hillLaw α b (Ioi x) = ENNReal.ofReal (exp (-b) * x ^ (-α)) := by
  have hx0 : 0 < x := one_pos.trans_le hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [hillLaw, Measure.map_apply (measurable_hillLaw_fun α b) measurableSet_Ioi]
  have hset : (fun e : ℝ => exp (α⁻¹ * max (e - b) 0)) ⁻¹' Ioi x = Ioi (b + α * Real.log x) := by
    ext e
    simp only [Set.mem_preimage, Set.mem_Ioi]
    rw [← exp_log hx0, exp_lt_exp, exp_log hx0, ← div_eq_inv_mul, lt_div_iff₀' hα, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · nlinarith
    · intro h; left; linarith
  rw [hset, expMeasure_Ioi (by positivity), rpow_def_of_pos hx0, ← exp_add]
  congr 2
  ring

theorem ae_one_le_hillLaw (hα : 0 < α) : ∀ᵐ y ∂(hillLaw α b), 1 ≤ y := by
  rw [hillLaw, ae_map_iff (measurable_hillLaw_fun α b).aemeasurable (p := fun y => 1 ≤ y)
    measurableSet_Ici]
  exact ae_of_all _ fun e => one_le_exp (mul_nonneg (inv_nonneg.2 hα.le) (le_max_right _ _))

theorem lintegral_id_expMeasure : ∫⁻ e, ENNReal.ofReal e ∂(expMeasure 1) = 1 := by
  have hint : Integrable (fun x : ℝ => x) (expMeasure 1) := by
    simpa using integrable_pow_expMeasure 1
  rw [← ofReal_integral_eq_lintegral_ofReal hint ae_nonneg_expMeasure, integral_id_expMeasure,
    ENNReal.ofReal_one]

theorem lintegral_log_hillLaw (hα : 0 < α) (hb : 0 ≤ b) :
    ∫⁻ y, ENNReal.ofReal (Real.log y) ∂(hillLaw α b) = ENNReal.ofReal (α⁻¹ * exp (-b)) := by
  rw [hillLaw, lintegral_map (measurable_log.ennreal_ofReal) (measurable_hillLaw_fun α b)]
  simp only [log_exp]
  have h : (fun e : ℝ => ENNReal.ofReal (α⁻¹ * max (e - b) 0)) =
      (Ioi b).indicator (fun e => (fun u : ℝ => ENNReal.ofReal (α⁻¹ * u)) (e - b)) := by
    funext e
    by_cases he : b < e
    · rw [Set.indicator_of_mem (show e ∈ Ioi b from he), max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (show e ∉ Ioi b from he), max_eq_right (by linarith), mul_zero,
        ENNReal.ofReal_zero]
  rw [h]
  refine (lintegral_indicator_Ioi_sub_expMeasure hb (fun u => ENNReal.ofReal (α⁻¹ * u))
    (by fun_prop)).trans ?_
  have : ∫⁻ u, ENNReal.ofReal (α⁻¹ * u) ∂(expMeasure 1) = ENNReal.ofReal α⁻¹ := by
    have h2 : ∀ᵐ u ∂(expMeasure 1), ENNReal.ofReal (α⁻¹ * u) =
        ENNReal.ofReal α⁻¹ * ENNReal.ofReal u := by
      filter_upwards [ae_nonneg_expMeasure] with u hu
      exact ENNReal.ofReal_mul (inv_nonneg.2 hα.le)
    rw [lintegral_congr_ae h2, lintegral_const_mul _ ENNReal.measurable_ofReal,
      lintegral_id_expMeasure, mul_one]
  rw [this, ← ENNReal.ofReal_mul (exp_pos _).le, mul_comm]

/-! ### `k / n → 0` is necessary -/

theorem logExcess_le_log {t y : ℝ} (ht : 1 ≤ t) (hy : 1 ≤ y) : logExcess t y ≤ Real.log y := by
  have ht0 : 0 < t := one_pos.trans_le ht
  refine Real.log_le_log (div_pos (ht0.trans_le (le_max_right _ _)) ht0) ?_
  rw [div_le_iff₀ ht0]
  rcases le_total y t with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

theorem one_le_orderStat {n k : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 1 ≤ x i) (hk : k < n) :
    1 ≤ orderStat x k := by
  rw [orderStat_of_lt x hk]; exact hx _

/-- If all sample points are `≥ 1`, the Hill estimator is at most `(1/k) ∑_i log X_i`. -/
theorem hill_le_sum_log {n k : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 1 ≤ x i) (hk : k < n) :
    hill x k ≤ (k : ℝ)⁻¹ * ∑ i, Real.log (x i) := by
  have ht := one_le_orderStat hx hk
  rw [hill_eq_sum_logExcess x hk (one_pos.trans_le ht)]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => logExcess_le_log ht (hx i))
    (inv_nonneg.2 (Nat.cast_nonneg k))

theorem measurable_hill_comp {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (n k : ℕ) :
    Measurable fun ω => hill (fun i : Fin n => X i ω) k :=
  (measurable_hill_pi n k).comp (measurable_pi_iff.2 fun i => hX i)

omit [IsProbabilityMeasure P] in
/-- The key estimate: `P(H_{k,n} ≥ 1/(2α)) ≤ 2 n e^{-b} / k` for the law `hillLaw α b`. -/
theorem measure_hill_ge_le {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (hillLaw α b) P) (hα : 0 < α) (hb : 0 ≤ b) {n k : ℕ}
    (hk0 : 0 < k) (hkn : k < n) :
    P {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) k} ≤
      ENNReal.ofReal (2 * n * exp (-b) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hone : ∀ᵐ ω ∂P, ∀ i : Fin n, 1 ≤ X i ω := by
    rw [ae_all_iff]
    intro i
    have h1 := ae_one_le_hillLaw (b := b) hα
    rw [← (hlaw i).map_eq] at h1
    exact ae_of_ae_map (hlaw i).aemeasurable h1
  set f : Ω → ℝ≥0∞ := fun ω => ∑ i : Fin n, ENNReal.ofReal (Real.log (X i ω)) with hf
  have hfm : Measurable f := Finset.measurable_sum _ fun i _ => (hX i).log.ennreal_ofReal
  set ε : ℝ≥0∞ := ENNReal.ofReal (k * (2 * α)⁻¹) with hε
  have hsub : {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) k} ≤ᵐ[P] {ω | ε ≤ f ω} := by
    filter_upwards [hone] with ω hω h
    have h1 := hill_le_sum_log hω hkn
    have h2 : (k : ℝ) * (2 * α)⁻¹ ≤ ∑ i : Fin n, Real.log (X i ω) := by
      have h : (2 * α)⁻¹ ≤ (k : ℝ)⁻¹ * ∑ i : Fin n, Real.log (X i ω) := le_trans h h1
      rw [inv_mul_eq_div, le_div_iff₀ hk'] at h
      linarith
    change ε ≤ ∑ i : Fin n, ENNReal.ofReal (Real.log (X i ω))
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => Real.log_nonneg (hω i)]
    exact ENNReal.ofReal_le_ofReal h2
  have hεpos : ε ≠ 0 := by
    rw [hε]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hint : ∫⁻ ω, f ω ∂P = n * ENNReal.ofReal (α⁻¹ * exp (-b)) := by
    change ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (Real.log (X i ω)) ∂P = _
    rw [lintegral_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => (hX i).log.ennreal_ofReal]
    have : ∀ i : Fin n, ∫⁻ ω, ENNReal.ofReal (Real.log (X i ω)) ∂P =
        ENNReal.ofReal (α⁻¹ * exp (-b)) := by
      intro i
      rw [← lintegral_log_hillLaw hα hb, ← (hlaw i).map_eq,
        lintegral_map measurable_log.ennreal_ofReal (hX i)]
    simp [this]
  calc P {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) k} ≤ P {ω | ε ≤ f ω} :=
        measure_mono_ae hsub
    _ ≤ (∫⁻ ω, f ω ∂P) / ε := meas_ge_le_lintegral_div hfm.aemeasurable hεpos ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * n * exp (-b) / k) := by
      rw [hint, hε, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      field_simp

/-- **`k(n) / n → 0` is necessary for the consistency of the Hill estimator.** Let `0 < c ≤ 1`
and `b = log (8 / c)` (so `e^{-b} = c / 8`). If `X_0, X_1, …` are iid with law `hillLaw α b`
(survival function `(c/8) x^{-α}` on `[1, ∞)`, regularly varying with index `-α`) and
`c n ≤ k(n) < n` eventually, then `H_{k(n),n}` does not converge in probability to `1/α`:
indeed `P(H_{k(n),n} < 1/(2α)) ≥ 3/4` for all large `n`. -/
theorem not_tendstoInMeasure_hill_of_le_mul {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hlaw : ∀ i, HasLaw (X i) (hillLaw α (Real.log (8 / c))) P) (hα : 0 < α) {k : ℕ → ℕ}
    (hk : ∀ᶠ n in atTop, c * n ≤ k n ∧ k n < n) :
    ¬ TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  intro h
  rw [tendstoInMeasure_iff_dist] at h
  have hb : 0 ≤ Real.log (8 / c) := Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  have heb : exp (-Real.log (8 / c)) = c / 8 := by
    rw [exp_neg, exp_log (by positivity), inv_div]
  have hlow : ∀ᶠ n in atTop, ENNReal.ofReal (3 / 4) ≤
      P {ω | (2 * α)⁻¹ ≤ dist (hill (fun i : Fin n => X i ω) (k n)) (1 / α)} := by
    filter_upwards [hk, eventually_gt_atTop 0] with n ⟨hcn, hkn⟩ hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hk0 : 0 < k n := by
      have : (0 : ℝ) < k n := (mul_pos hc0 hn').trans_le hcn
      exact_mod_cast this
    have hk' : (0 : ℝ) < k n := by exact_mod_cast hk0
    have hup := measure_hill_ge_le hX hlaw hα hb hk0 hkn
    rw [heb] at hup
    have hq : 2 * n * (c / 8) / k n ≤ 1 / 4 := by
      rw [div_le_iff₀ hk']; nlinarith
    have hup' : P {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) (k n)} ≤ ENNReal.ofReal (1 / 4) :=
      hup.trans (ENNReal.ofReal_le_ofReal hq)
    have hms : MeasurableSet {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) (k n)} :=
      measurableSet_le measurable_const (measurable_hill_comp hX n (k n))
    have hsub : {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) (k n)}ᶜ ⊆
        {ω | (2 * α)⁻¹ ≤ dist (hill (fun i : Fin n => X i ω) (k n)) (1 / α)} := by
      intro ω hω
      simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
      simp only [mem_ofPred_eq, Real.dist_eq]
      rw [abs_of_neg (by
        have : (2 * α)⁻¹ < 1 / α := by
          rw [mul_inv, one_div]; nlinarith [inv_pos.2 hα]
        linarith)]
      have : 1 / α = 2 * (2 * α)⁻¹ := by field_simp
      linarith
    calc ENNReal.ofReal (3 / 4) = 1 - ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
      _ ≤ 1 - P {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) (k n)} := tsub_le_tsub_left hup' 1
      _ = P {ω | (2 * α)⁻¹ ≤ hill (fun i : Fin n => X i ω) (k n)}ᶜ := (prob_compl_eq_one_sub hms).symm
      _ ≤ _ := measure_mono hsub
  have := ge_of_tendsto (h (2 * α)⁻¹ (by positivity)) hlow
  rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.zero_ne_top] at this
  norm_num at this

omit [IsProbabilityMeasure P] in
/-- The survival function of `hillLaw α b` is regularly varying with index `-α`. -/
theorem isRegularlyVarying_hillLaw {X : Ω → ℝ} (hlaw : HasLaw X (hillLaw α b) P) (hα : 0 < α)
    (hb : 0 ≤ b) : IsRegularlyVarying (fun x => (P {ω | x < X ω}).toReal) (-α) := by
  refine ((IsRegularlyVarying.rpow_id (-α)).const_mul (exp_pos (-b))).congr ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [show {ω | x < X ω} = X ⁻¹' Ioi x from rfl, ← Measure.map_apply_of_aemeasurable
    hlaw.aemeasurable measurableSet_Ioi, hlaw.map_eq, hillLaw_Ioi hα hb hx,
    ENNReal.toReal_ofReal (by positivity)]

/-- The `k / n → 0` counterexample is not vacuous: an iid sequence with law `hillLaw α b`,
`b = log (8 / c)`, exists, and its survival function is regularly varying with index `-α`. -/
theorem exists_hill_k_linear_counterexample (hα : 0 < α) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
      (∀ i, IdentDistrib (X i) (X 0) P P) ∧
      IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α) ∧
      ∀ k : ℕ → ℕ, (∀ᶠ n in atTop, c * n ≤ k n ∧ k n < n) →
        ¬ TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
          (fun _ => 1 / α) := by
  obtain ⟨Ω, _, P, X, hXm, hlaw, hind, hP⟩ := exists_iid ℕ (hillLaw α (Real.log (8 / c)))
  have hb : 0 ≤ Real.log (8 / c) := Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  refine ⟨Ω, _, P, X, hP, hXm, hind, fun i => ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable,
    by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩, isRegularlyVarying_hillLaw (hlaw 0) hα hb,
    fun k hk => not_tendstoInMeasure_hill_of_le_mul hXm hc0 hc1 hlaw hα hk⟩

/-! ### `k → ∞` is necessary -/

/-- **Law of the Hill estimator of a Pareto sample** (Rényi representation): for `0 < k < n`,
`H_{k,n}` has the law of `(1/α) (1/k) (E_1 + ⋯ + E_k)` with `E_i` iid standard exponential. -/
theorem map_hill_pareto {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {n k : ℕ} (hkn : k < n) :
    P.map (fun ω => hill (fun i : Fin n => X i ω) k) =
      (Measure.pi fun _ : Fin k => expMeasure 1).map
        (fun z => α⁻¹ * ((k : ℝ)⁻¹ * ∑ i, z i)) := by
  set γ := α⁻¹ with hγ
  have hγ0 : 0 < γ := inv_pos.2 hα
  have hg : Measurable fun e : ℝ => exp (γ * e) := by fun_prop
  have hH : Measurable fun y : Fin n → ℝ => hill y k := measurable_hill_pi n k
  have hlawX : HasLaw (fun ω (i : Fin n) => X i ω)
      (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => exp (γ * e)) P := by
    refine (hindep.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective).hasLaw_pi
      (fun i => ⟨(hX i).aemeasurable, ?_⟩)
    rw [(hident i).map_eq]
    exact map_eq_expMeasure_map_of_pareto (hX 0) hα hPar
  have e1 : P.map (fun ω => hill (fun i : Fin n => X i ω) k) =
      (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => exp (γ * e)).map
        (fun y : Fin n → ℝ => hill y k) :=
    ((hasLaw_map hH.aemeasurable).comp hlawX).map_eq
  rw [e1, ← Measure.pi_map_pi (fun _ => hg.aemeasurable), Measure.map_map hH (by fun_prop)]
  have e2 : (fun y : Fin n → ℝ => hill y k) ∘ (fun y i => exp (γ * y i)) =
      fun y => γ * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (orderStat y i - orderStat y k)) :=
    funext fun y => hill_exp_mul γ hγ0.le y hkn
  rw [e2]
  have hR := map_orderStat_excess (n := n) hkn (ψ := fun x _ => x) measurable_fst
    (h := fun x _ => γ * ((k : ℝ)⁻¹ * x)) (by fun_prop)
  simp only at hR
  rw [hR]
  have e3 : (fun p : (Fin n → ℝ) × (Fin k → ℝ) => γ * ((k : ℝ)⁻¹ * ∑ i, p.2 i)) =
      (fun z : Fin k → ℝ => γ * ((k : ℝ)⁻¹ * ∑ i, z i)) ∘ Prod.snd := rfl
  rw [e3, ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod, measure_univ,
    one_smul]

/-- For a Pareto sample and `k < n`, `P(|H_{k,n} - 1/α| ≥ 1/(2α)) ≥ e^{-2k}`. -/
theorem measure_dist_hill_pareto_ge {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {n k : ℕ} (hkn : k < n) :
    ENNReal.ofReal (exp (-(2 * k))) ≤
      P {ω | (2 * α)⁻¹ ≤ dist (hill (fun i : Fin n => X i ω) k) (1 / α)} := by
  have hγ0 : 0 < α⁻¹ := inv_pos.2 hα
  have h2 : (2 * α)⁻¹ = α⁻¹ / 2 := by rw [mul_inv]; ring
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- `k = 0`: the Hill estimator is `0`
    subst hk0
    have : {ω | (2 * α)⁻¹ ≤ dist (hill (fun i : Fin n => X i ω) 0) (1 / α)} = univ := by
      ext ω
      simp only [hill, CharP.cast_eq_zero, inv_zero, zero_mul, Real.dist_eq, zero_sub, abs_neg,
        mem_ofPred_eq, mem_univ, iff_true, one_div]
      rw [abs_of_pos hγ0, h2]
      linarith
    rw [this, measure_univ]
    exact ENNReal.ofReal_le_one.2 (exp_le_one_iff.2 (by simp))
  set S : Set ℝ := {y | (2 * α)⁻¹ ≤ dist y (1 / α)} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const (measurable_id.dist measurable_const)
  have hHm := measurable_hill_comp hX n k
  rw [show {ω | (2 * α)⁻¹ ≤ dist (hill (fun i : Fin n => X i ω) k) (1 / α)} =
    (fun ω => hill (fun i : Fin n => X i ω) k) ⁻¹' S from rfl, ← Measure.map_apply hHm hSm,
    map_hill_pareto hX hindep hident hα hPar hkn, Measure.map_apply (by fun_prop) hSm]
  set i0 : Fin k := ⟨0, hk0⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  -- a.e. nonnegativity of the exponential coordinates
  have hnn : ∀ᵐ z ∂(Measure.pi fun _ : Fin k => expMeasure 1), ∀ i, 0 ≤ z i := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin k => expMeasure 1) i).quasiMeasurePreserving.ae
      ae_nonneg_expMeasure
  have hsub : (Function.eval i0 ⁻¹' Ioi (2 * (k : ℝ))) ≤ᵐ[Measure.pi fun _ : Fin k => expMeasure 1]
      ((fun z : Fin k → ℝ => α⁻¹ * ((k : ℝ)⁻¹ * ∑ i, z i)) ⁻¹' S) := by
    filter_upwards [hnn] with z hz hzi
    have hzi : 2 * k < z i0 := hzi
    have hsum : z i0 ≤ ∑ i, z i :=
      Finset.single_le_sum (fun i _ => hz i) (Finset.mem_univ i0)
    have hmean : 2 ≤ (k : ℝ)⁻¹ * ∑ i, z i := by
      rw [inv_mul_eq_div, le_div_iff₀ hk']; linarith
    change (2 * α)⁻¹ ≤ dist (α⁻¹ * ((k : ℝ)⁻¹ * ∑ i, z i)) (1 / α)
    rw [Real.dist_eq, h2, one_div]
    have : α⁻¹ * 2 ≤ α⁻¹ * ((k : ℝ)⁻¹ * ∑ i, z i) := mul_le_mul_of_nonneg_left hmean hγ0.le
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc ENNReal.ofReal (exp (-(2 * k))) = expMeasure 1 (Ioi (2 * (k : ℝ))) :=
        (expMeasure_Ioi (by positivity)).symm
    _ = (Measure.pi fun _ : Fin k => expMeasure 1) (Function.eval i0 ⁻¹' Ioi (2 * (k : ℝ))) :=
        ((measurePreserving_eval (fun _ : Fin k => expMeasure 1) i0).measure_preimage
          measurableSet_Ioi.nullMeasurableSet).symm
    _ ≤ _ := measure_mono_ae hsub

/-- **`k(n) → ∞` is necessary for the consistency of the Hill estimator**, even for an exact
Pareto sample. If `X_0, X_1, …` are iid `Pareto(α)`, `k(n) < n` eventually and `k` does not tend
to infinity, then `H_{k(n),n}` does not converge in probability to `1/α`. -/
theorem not_tendstoInMeasure_hill_pareto_of_not_tendsto {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {k : ℕ → ℕ}
    (hk : ¬ Tendsto k atTop atTop) (hkn : ∀ᶠ n in atTop, k n < n) :
    ¬ TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
      (fun _ => 1 / α) := by
  intro h
  rw [tendstoInMeasure_iff_dist] at h
  rw [tendsto_atTop] at hk
  push Not at hk
  obtain ⟨K, hK⟩ := hk
  have hfreq : ∃ᶠ n in atTop, k n < K ∧ k n < n := by
    refine (hK.and_eventually hkn).mono fun n hn => ⟨?_, hn.2⟩
    simpa using hn.1
  set c := ENNReal.ofReal (exp (-(2 * K))) with hc
  have hcpos : 0 < c := ENNReal.ofReal_pos.2 (exp_pos _)
  have hev := (h (2 * α)⁻¹ (by positivity)).eventually (gt_mem_nhds hcpos)
  obtain ⟨n, ⟨hnK, hnn⟩, hlt⟩ := (hfreq.and_eventually hev).exists
  have hge := measure_dist_hill_pareto_ge hX hindep hident hα hPar hnn
  have : ENNReal.ofReal (exp (-(2 * K))) ≤ ENNReal.ofReal (exp (-(2 * (k n : ℝ)))) := by
    refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
    have : (k n : ℝ) ≤ K := by exact_mod_cast hnK.le
    linarith
  exact absurd (this.trans hge) (not_le.2 hlt)

/-- **Hill consistency for Pareto samples, characterization.** For an iid `Pareto(α)` sample and
`k(n) < n` eventually with `k(n) / n → 0`, the Hill estimator `H_{k(n),n}` converges in
probability to `1/α` **if and only if** `k(n) → ∞`. -/
theorem tendstoInMeasure_hill_pareto_iff {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {k : ℕ → ℕ}
    (hkn : ∀ᶠ n in atTop, k n < n) (hkn0 : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop (fun _ => 1 / α) ↔
      Tendsto k atTop atTop := by
  refine ⟨fun h => ?_, fun hk => tendstoInMeasure_hill_pareto hX hindep hident hα hPar hk hkn0⟩
  by_contra hk
  exact not_tendstoInMeasure_hill_pareto_of_not_tendsto hX hindep hident hα hPar hk hkn h

/-- The `k → ∞` counterexample is not vacuous: an iid `Pareto(α)` sequence exists, and for it
the Hill estimator with any bounded `k(n) < n` (e.g. `k = 1`) is not consistent. -/
theorem exists_hill_k_bounded_counterexample (hα : 0 < α) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
      (∀ i, IdentDistrib (X i) (X 0) P P) ∧
      (∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) ∧
      ∀ k : ℕ → ℕ, ¬ Tendsto k atTop atTop → (∀ᶠ n in atTop, k n < n) →
        ¬ TendstoInMeasure P (fun n ω => hill (fun i : Fin n => X i ω) (k n)) atTop
          (fun _ => 1 / α) := by
  obtain ⟨Ω, _, P, X, hXm, hlaw, hind, hP⟩ := exists_iid ℕ (hillLaw α 0)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
  have hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α) := by
    intro x hx
    rw [show {ω | x < X 0 ω} = X 0 ⁻¹' Ioi x from rfl, ← Measure.map_apply_of_aemeasurable
      (hlaw 0).aemeasurable measurableSet_Ioi, (hlaw 0).map_eq, hillLaw_Ioi hα le_rfl hx,
      neg_zero, exp_zero, one_mul, ENNReal.toReal_ofReal (rpow_pos_of_pos
        (one_pos.trans_le hx) _).le]
  exact ⟨Ω, _, P, X, hP, hXm, hind, hident, hPar, fun k hk hkn =>
    not_tendstoInMeasure_hill_pareto_of_not_tendsto hXm hind hident hα hPar hk hkn⟩

end ExtremeValueTheory.Minimality
