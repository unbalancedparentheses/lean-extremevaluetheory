/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Renyi
import ExtremeValueTheory.Statistics.Hill
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.HasLawExists

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Asymptotic normality of the Hill estimator

TODO
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Convergence in distribution: changing the underlying space -/

section Distribution

variable {ι Ω Ω₀ Ω' Ω'' : Type*} {mΩ : MeasurableSpace Ω} {mΩ₀ : MeasurableSpace Ω₀}
  {mΩ' : MeasurableSpace Ω'} {mΩ'' : MeasurableSpace Ω''}
  {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {P'' : Measure Ω''} [IsProbabilityMeasure P'']

/-- Convergence in distribution only depends on the laws of the random variables. -/
theorem _root_.MeasureTheory.TendstoInDistribution.of_map_eq {l : Filter ι} {X : ι → Ω → ℝ} {X₀ : ι → Ω₀ → ℝ}
    {Z : Ω' → ℝ} (h : TendstoInDistribution X₀ l Z (fun _ => P₀) P')
    (hX : ∀ i, AEMeasurable (X i) P) (hlaw : ∀ᶠ i in l, P.map (X i) = P₀.map (X₀ i)) :
    TendstoInDistribution X l Z (fun _ => P) P' := by
  refine ⟨hX, h.aemeasurable_limit, h.tendsto.congr' ?_⟩
  filter_upwards [hlaw] with i hi
  exact Subtype.ext hi.symm

/-- Convergence in distribution only depends on the law of the limit. -/
theorem _root_.MeasureTheory.TendstoInDistribution.congr_limit {l : Filter ι} {X : ι → Ω → ℝ} {Z : Ω' → ℝ}
    {Z' : Ω'' → ℝ} (h : TendstoInDistribution X l Z (fun _ => P) P')
    (hZ' : AEMeasurable Z' P'') (hlaw : P'.map Z = P''.map Z') :
    TendstoInDistribution X l Z' (fun _ => P) P'' := by
  refine ⟨h.forall_aemeasurable, hZ', ?_⟩
  have e : (⟨P''.map Z', inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨P'.map Z, inferInstance⟩ := Subtype.ext hlaw.symm
  exact e ▸ h.tendsto

/-- Convergence in distribution along a subsequence `k n → ∞`. -/
theorem _root_.MeasureTheory.TendstoInDistribution.comp_tendsto {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => P) P') {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) :
    TendstoInDistribution (fun n => X (k n)) atTop Z (fun _ => P) P' :=
  ⟨fun _ => h.forall_aemeasurable _, h.aemeasurable_limit, h.tendsto.comp hk⟩

end Distribution

/-! ### Moments of the standard exponential law -/

section ExpMoments

theorem integral_expMeasure (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure 1) = ∫ x in Ioi 0, exp (-x) * g x := by
  have hg : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hg
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h0] with x hx
  simp only [gammaPDF, gammaPDFReal, Set.indicator, mem_Ioi, smul_eq_mul]
  rcases lt_or_gt_of_ne hx with h | h
  · simp [h.not_ge, h.not_gt]
  · simp [h.le, h, (exp_pos _).le]

theorem integrable_expMeasure_iff (g : ℝ → ℝ) :
    Integrable g (expMeasure 1) ↔ IntegrableOn (fun x => exp (-x) * g x) (Ioi 0) := by
  have hg : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff_integrable_smul' hg
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integrable_indicator_iff measurableSet_Ioi]
  refine integrable_congr ?_
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h0] with x hx
  simp only [gammaPDF, gammaPDFReal, Set.indicator, mem_Ioi, smul_eq_mul]
  rcases lt_or_gt_of_ne hx with h | h
  · simp [h.not_ge, h.not_gt]
  · simp [h.le, h, (exp_pos _).le]

theorem integral_pow_expMeasure (j : ℕ) :
    ∫ x, x ^ j ∂(expMeasure 1) = (Nat.factorial j : ℝ) := by
  rw [integral_expMeasure, ← Real.Gamma_nat_eq_factorial, Real.Gamma_eq_integral (by positivity)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [add_sub_cancel_right, Real.rpow_natCast]


theorem integrable_pow_expMeasure (j : ℕ) : Integrable (fun x => x ^ j) (expMeasure 1) := by
  rw [integrable_expMeasure_iff]
  refine (Real.GammaIntegral_convergent (s := j + 1) (by positivity)).congr_fun
    (fun x _ => ?_) measurableSet_Ioi
  simp only
  rw [add_sub_cancel_right, Real.rpow_natCast]

theorem integral_id_expMeasure : ∫ x, x ∂(expMeasure 1) = 1 := by
  simpa using integral_pow_expMeasure 1

theorem memLp_two_id_expMeasure : MemLp id 2 (expMeasure 1) :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
    (integrable_pow_expMeasure 2)

theorem variance_id_expMeasure : variance id (expMeasure 1) = 1 := by
  rw [variance_eq_sub memLp_two_id_expMeasure]
  have h2 := integral_pow_expMeasure 2
  have h1 := integral_id_expMeasure
  simp only [Pi.pow_apply, id] at *
  rw [h2, h1]
  norm_num

end ExpMoments

/-! ### Order statistics of monotone transforms -/

section Monotone

variable {n : ℕ}

/-- Order statistics commute with monotone maps. -/
theorem orderStat_comp_monotone {g : ℝ → ℝ} (hg : Monotone g) (y : Fin n → ℝ) {j : ℕ}
    (hj : j < n) : orderStat (g ∘ y) j = g (orderStat y j) := by
  rw [orderStat_of_lt _ hj, orderStat_of_lt _ hj]
  have : (g ∘ y) ∘ Tuple.sort (g ∘ y) = (g ∘ y) ∘ Tuple.sort y :=
    Tuple.unique_monotone (Tuple.monotone_sort _) (hg.comp (Tuple.monotone_sort y))
  exact congrFun this _

theorem measurable_hill_pi (n k : ℕ) : Measurable fun y : Fin n → ℝ => hill y k :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_orderStat_pi i).log.sub (measurable_orderStat_pi k).log)

/-- The Hill estimator of the sample `exp(γ y_i)` is
 `γ` times the mean top excess of `y`. -/
theorem hill_exp_mul (γ : ℝ) (hγ : 0 ≤ γ) (y : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    hill (fun i => exp (γ * y i)) k =
      γ * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (orderStat y i - orderStat y k)) := by
  have hmono : Monotone fun x => exp (γ * x) :=
    fun a b hab => exp_le_exp.2 (mul_le_mul_of_nonneg_left hab hγ)
  have h := fun j (hj : j < n) => orderStat_comp_monotone hmono y hj
  simp only [Function.comp_def] at h
  rw [hill, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := (Finset.mem_range.1 hi).trans hk
  rw [h i hi', h k hk, log_exp, log_exp]
  ring

end Monotone

/-! ### The exact exponential case: a central limit theorem for the top excesses -/

section Exponential

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [IsProbabilityMeasure P] in
theorem hasLaw_vec_of_iid
 {E : ℕ → Ω → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P)
    (hind : iIndepFun E P) (n : ℕ) :
    HasLaw (fun ω (i : Fin n) => E i ω) (Measure.pi fun _ : Fin n => expMeasure 1) P :=
  (hind.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective).hasLaw_pi (fun i => hE i)

omit [IsProbabilityMeasure P] in
theorem map_comp_vec_of_iid
 {E : ℕ → Ω → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P)
    (hind : iIndepFun E P) {n : ℕ} {β : Type*} [MeasurableSpace β] {T : (Fin n → ℝ) → β}
    (hT : Measurable T) :
    P.map (fun ω => T (fun i => E i ω)) = (Measure.pi fun _ : Fin n => expMeasure 1).map T :=
  ((hasLaw_map hT.aemeasurable).comp (hasLaw_vec_of_iid hE hind n)).map_eq

omit [IsProbabilityMeasure P] in
/-- The Rényi representation for the mean top excess: for `k < n`, the law of
`√k ((1/k) ∑_{i<k} (E_{(i+1)} - E_{(k+1)}) - 1)` is that of `(√k)⁻¹ (∑_{i<k} E_i - k)`. -/
theorem map_sqrt_mul_meanExcess {E : ℕ → Ω → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P)
    (hind : iIndepFun E P) {n k : ℕ} (hk : k < n) (hk0 : 0 < k) :
    P.map (fun ω => √k * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
        (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) k) - 1)) =
      P.map (fun ω => (√k)⁻¹ * (∑ i ∈ Finset.range k, E i ω - k * 1)) := by
  have hmo := measurable_orderStat_pi (n := n) k
  have hT : Measurable fun y : Fin n → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      (orderStat y i - orderStat y k) - 1) := by
    refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_orderStat_pi i).sub hmo)).sub measurable_const)
  have hS : Measurable fun z : Fin k → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i, z i - 1) := by
    refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      measurable_pi_apply i)).sub measurable_const)
  rw [map_comp_vec_of_iid hE hind (n := n) hT]
  have hR := map_orderStat_excess (n := n) hk (ψ := fun x _ => x) measurable_fst
    (h := fun x _ => √k * ((k : ℝ)⁻¹ * x - 1)) (by fun_prop)
  simp only at hR
  rw [hR]
  have e1 : (fun p : (Fin n → ℝ) × (Fin k → ℝ) => √k * ((k : ℝ)⁻¹ * ∑ i, p.2 i - 1)) =
      (fun z : Fin k → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i, z i - 1)) ∘ Prod.snd := rfl
  rw [e1, ← Measure.map_map hS measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  have e2 : (fun ω => (√k)⁻¹ * (∑ i ∈ Finset.range k, E i ω - k * 1)) =
      fun ω => (fun z : Fin k → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i, z i - 1)) (fun i => E i ω) := by
    funext ω
    beta_reduce
    rw [Fin.sum_univ_eq_sum_range (fun i => E i ω) k]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    have hs : √(k : ℝ) * √(k : ℝ) = k := Real.mul_self_sqrt hk'.le
    have hs0 : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hk').ne'
    field_simp
    rw [Real.sq_sqrt hk'.le]
  rw [e2, map_comp_vec_of_iid hE hind hS]


/-- **Central limit theorem for the mean top excess of an exponential sample.** If the `E_i` are
iid standard exponential, `k(n) → ∞` and `k(n) < n`, then
`√k ((1/k) ∑_{i<k} (E_{(i+1)} - E_{(k+1)}) - 1) ⇒ N(0, 1)`. -/
theorem tendstoInDistribution_meanExcess {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : ∀ᶠ n in atTop, k n < n) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) * (((k n : ℝ))⁻¹ * ∑ i ∈ Finset.range (k n),
        (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) (k n)) - 1))
      atTop Z (fun _ => P) P' := by
  have hmean : P[E 0] = 1 := by rw [(hE 0).integral_eq, integral_id_expMeasure]
  have hvar : Var[E 0; P] = 1 := by rw [(hE 0).variance_eq, variance_id_expMeasure]
  have hL2 : MemLp (E 0) 2 P := (hE 0).memLp memLp_two_id_expMeasure
  have hident : ∀ i, IdentDistrib (E i) (E 0) P P := fun i =>
    ⟨(hE i).aemeasurable, (hE 0).aemeasurable, by rw [(hE i).map_eq, (hE 0).map_eq]⟩
  have hZ' : HasLaw Z (gaussianReal 0 Var[E 0; P].toNNReal) P' := by
    rw [hvar, Real.toNNReal_one]; exact hZ
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ' hL2 hind hident
  rw [hmean] at hclt
  refine (hclt.comp_tendsto hk).of_map_eq (fun n => ?_) ?_
  · have hv : ∀ i : Fin n, Measurable fun ω => E i ω := fun i => hEm i
    refine (measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_orderStat hv i).sub (measurable_orderStat hv (k n)))).sub
      measurable_const)).aemeasurable
  · filter_upwards [hkn, hk.eventually_gt_atTop 0] with n h1 h2
    exact map_sqrt_mul_meanExcess hE hind h1 h2

end Exponential

/-! ### The exact Pareto case -/

section Pareto

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- Two probability measures on `ℝ` with the same survival function are equal. -/
theorem measure_eq_of_Ioi {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ a, μ (Ioi a) = ν (Ioi a)) : μ = ν := by
  refine Measure.ext_of_Iic μ ν fun a => ?_
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    h a]

/-- A `Pareto(α)` random variable `X`, `P(X > x) = x^{-α}` for `x ≥ 1`, has the law of
`exp(E / α)` with `E` standard exponential. -/
theorem map_eq_expMeasure_map_of_pareto {X : Ω → ℝ} (hX : Measurable X) {α : ℝ} (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X ω}).toReal = x ^ (-α)) :
    P.map X = (expMeasure 1).map (fun e => exp (α⁻¹ * e)) := by
  have hg : Measurable fun e : ℝ => exp (α⁻¹ * e) := by fun_prop
  refine measure_eq_of_Ioi fun a => ?_
  rw [Measure.map_apply hX measurableSet_Ioi, Measure.map_apply hg measurableSet_Ioi]
  rcases le_or_gt 1 a with ha | ha
  · have ha0 : 0 < a := one_pos.trans_le ha
    have e1 : (fun e : ℝ => exp (α⁻¹ * e)) ⁻¹' Ioi a = Ioi (α * log a) := by
      ext e
      simp only [mem_preimage, mem_Ioi]
      rw [← exp_log ha0, exp_lt_exp, exp_log ha0, ← div_eq_inv_mul, lt_div_iff₀' hα]
    rw [e1, expMeasure_Ioi (mul_nonneg hα.le (log_nonneg ha)),
      ← ENNReal.ofReal_toReal (measure_ne_top P _)]
    congr 1
    rw [show X ⁻¹' Ioi a = {ω | a < X ω} from rfl, hPar a ha, rpow_def_of_pos ha0]
    congr 1
    ring
  · have h1 : P (X ⁻¹' Ioi a) = 1 := by
      refine le_antisymm prob_le_one ?_
      have hP1 := hPar 1 le_rfl
      rw [one_rpow] at hP1
      have : P {ω | 1 < X ω} = 1 := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top P _), hP1, ENNReal.ofReal_one]
      rw [← this]
      exact measure_mono fun ω (hω : 1 < X ω) => (show a < X ω from ha.trans hω)
    have h2 : expMeasure 1 ((fun e : ℝ => exp (α⁻¹ * e)) ⁻¹' Ioi a) = 1 := by
      refine le_antisymm prob_le_one ?_
      calc (1 : ℝ≥0∞) = expMeasure 1 (Ioi 0) := by
            rw [expMeasure_Ioi le_rfl, neg_zero, exp_zero, ENNReal.ofReal_one]
        _ ≤ _ := measure_mono fun e (he : 0 < e) => ?_
      show a < exp (α⁻¹ * e)
      exact ha.trans (one_lt_exp_iff.2 (mul_pos (inv_pos.2 hα) he))
    rw [h1, h2]

/-- **Asymptotic normality of the Hill estimator, exact Pareto case** ([dHF, Theorem 3.2.5]
with vanishing bias; Hall 1982). Let `X_0, X_1, …` be iid `Pareto(α)`, `P(X_0 > x) = x^{-α}` for
`x ≥ 1`, and let `k(n) → ∞` with `k(n) < n`. Then
`√k (H_{k,n} - 1/α) ⇒ N(0, 1/α²)`. -/
theorem tendstoInDistribution_hill_pareto {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hPar : ∀ x : ℝ, 1 ≤ x → (P {ω | x < X 0 ω}).toReal = x ^ (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : ∀ᶠ n in atTop, k n < n) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (α⁻¹ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - α⁻¹))
      atTop Z (fun _ => P) P' := by
  obtain ⟨Ω₀, _, P₀, E, hEm, hE, hind, hP₀⟩ := exists_iid ℕ (expMeasure 1)
  set γ := α⁻¹ with hγ
  have hγ0 : 0 < γ := inv_pos.2 hα
  have hZ1 : HasLaw (fun ω => α * Z ω) (gaussianReal 0 1) P' := by
    have := gaussianReal_const_mul hZ α
    convert this using 2
    · simp
    · ext
      simp only [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _
        (sq_nonneg _), hγ]
      field_simp
  have hA := tendstoInDistribution_meanExcess hEm hE hind hk hkn hZ1
  have hB := hA.continuous_comp (g := fun x => γ * x) (continuous_const.mul continuous_id)
  have hZe : (fun ω => γ * (α * Z ω)) = Z := by
    funext ω; rw [hγ, ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
  replace hB := hB.congr_limit hZ.aemeasurable (by congr 1)
  refine hB.of_map_eq (fun n => ?_) ?_
  · exact (measurable_const.mul ((measurable_hill_pi n (k n)).comp
      (measurable_pi_iff.2 fun i => hX i) |>.sub measurable_const)).aemeasurable
  · filter_upwards [hkn] with n hn
    have hg : Measurable fun e : ℝ => exp (γ * e) := by fun_prop
    have hS : Measurable fun y : Fin n → ℝ => √(k n : ℝ) * (hill y (k n) - γ) :=
      measurable_const.mul ((measurable_hill_pi n (k n)).sub measurable_const)
    have hlawX : HasLaw (fun ω (i : Fin n) => X i ω)
        (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => exp (γ * e)) P := by
      refine (hindep.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective).hasLaw_pi
        (fun i => ⟨(hX i).aemeasurable, ?_⟩)
      rw [(hident i).map_eq]
      exact map_eq_expMeasure_map_of_pareto (hX 0) hα hPar
    have hmo := measurable_orderStat_pi (n := n) (k n)
    have hT : Measurable fun y : Fin n → ℝ => γ * (√(k n : ℝ) * (((k n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range (k n), (orderStat y i - orderStat y (k n)) - 1)) :=
      measurable_const.mul (measurable_const.mul ((measurable_const.mul
        (Finset.measurable_sum _ fun i _ => (measurable_orderStat_pi i).sub hmo)).sub
        measurable_const))
    have e1 : P.map (fun ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - γ)) =
        (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => exp (γ * e)).map
          (fun y : Fin n → ℝ => √(k n : ℝ) * (hill y (k n) - γ)) :=
      ((hasLaw_map hS.aemeasurable).comp hlawX).map_eq
    have e2 : P₀.map ((fun x => γ * x) ∘ fun ω => √(k n : ℝ) * (((k n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range (k n), (orderStat (fun i : Fin n => E i ω) i -
          orderStat (fun i : Fin n => E i ω) (k n)) - 1)) =
        (Measure.pi fun _ : Fin n => expMeasure 1).map (fun y : Fin n → ℝ =>
          γ * (√(k n : ℝ) * (((k n : ℝ))⁻¹ * ∑ i ∈ Finset.range (k n),
            (orderStat y i - orderStat y (k n)) - 1))) :=
      map_comp_vec_of_iid hE hind hT
    rw [e1, e2, ← Measure.pi_map_pi (fun _ => hg.aemeasurable), Measure.map_map hS (by fun_prop)]
    congr 1

    funext y
    simp only [Function.comp_apply]
    rw [hill_exp_mul γ hγ0.le y hn]
    ring


end Pareto

end ExtremeValueTheory
