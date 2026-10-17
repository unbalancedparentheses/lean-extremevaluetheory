/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Renyi
import ExtremeValueTheory.Statistics.Moment
import ExtremeValueTheory.RegularVariation.SecondOrder
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.HasLawExists

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Asymptotic normality of the Hill estimator

Let `X_0, X_1, …` be iid with tail quantile function `U(t) = F̄^←(1/t)` and let
`H_{k,n} = (1/k) ∑_{i<k} (log X_{(i+1)} - log X_{(k+1)})` be the Hill estimator
(`ExtremeValueTheory.hill`). We prove its asymptotic normality ([dHF, Theorem 3.2.5]; Hall 1982;
Haeusler and Teugels 1985): if `U` is of second-order regular variation with indices `γ > 0`,
`ρ ≤ 0` and auxiliary function `A` (`ExtremeValueTheory.IsSecondOrderRegularlyVarying`), and
`k → ∞`, `k / n → 0`, `√k A(n/k) → λ`, then

  `√k (H_{k,n} - γ) ⇒ N(λ / (1 - ρ), γ²)`.

Convergence in distribution is Mathlib's `TendstoInDistribution`, towards any random variable
with law `gaussianReal (λ / (1 - ρ)) γ²`.

## Main results

* `ExtremeValueTheory.tendstoInDistribution_hill_pareto`: the exact Pareto case,
  `√k (H_{k,n} - 1/α) ⇒ N(0, 1/α²)`, only assuming `k → ∞` and `k < n`.
* `ExtremeValueTheory.tendstoInDistribution_hill_of_tendsto_zero`: the general case with
  `√k A(n/k) → 0`, `√k (H_{k,n} - γ) ⇒ N(0, γ²)`.
* `ExtremeValueTheory.tendstoInDistribution_hill`: the general case with asymptotic bias
  `λ / (1 - ρ)`.
* `ExtremeValueTheory.tendstoInDistribution_meanExcess`: the central limit theorem
  `√k ((1/k) ∑_{i<k} (E_{(i+1)} - E_{(k+1)}) - 1) ⇒ N(0, 1)` for iid standard exponentials.
* `ExtremeValueTheory.tendstoInMeasure_meanExcess_fun`: a conditional law of large numbers for
  functions of the top exponential excesses and of `E_{(k+1)}`.
* `ExtremeValueTheory.tailQuantile`, `map_eq_expMeasure_map_tailQuantile`: the tail quantile
  function and the quantile transform `X =ᵈ U(e^E)`, `E` standard exponential.

## Proof

1. *Quantile transform.* The sample `(X_i)` has the law of `(U(e^{E_i}))` with `E_i` iid standard
   exponential, so it suffices to work with the latter (`TendstoInDistribution.of_map_eq`).
2. *Rényi representation.* By `ExtremeValueTheory.lintegral_orderStat_excess`, conditionally on
   `E_{(k+1)}` the top excesses `E_{(i+1)} - E_{(k+1)}` are iid standard exponential. Hence
   `√k ((1/k) ∑ (E_{(i+1)} - E_{(k+1)}) - 1)` has the law of `(√k)⁻¹ (E_0 + ⋯ + E_{k-1} - k)`,
   and Mathlib's central limit theorem applies. This gives the exact Pareto case.
3. *Decomposition.* Since `U ∘ exp` is monotone, with `R(u, s) = log U(e^{u+s}) - log U(e^s) - γu`,
   `√k (H_{k,n} - γ) = γ √k (M_k - 1) + √k (1/k) ∑_{i<k} R(E_{(i+1)} - E_{(k+1)}, E_{(k+1)})`,
   where `M_k` is the mean top excess (`hill_comp_exp_eq`).
4. *Bias.* `E_{(k+1)} - log(n/k) → 0` in probability (`tendstoInMeasure_orderStat_sub_log`), so
   `A(e^{E_{(k+1)}}) / A(n/k) → 1` by the uniform convergence theorem for `|A|`. By the uniform
   second-order bound (`IsSecondOrderRegularlyVarying.exists_bound`), `R(u, s) / A(e^s)` is
   dominated by `C e^{u/4}` and tends to `h_ρ(e^u)`; the conditional law of large numbers gives
   `(1/k) ∑ R(…) / A(e^{E_{(k+1)}}) → ∫ h_ρ(e^u) e^{-u} du = 1 / (1 - ρ)`. Hence the second term
   tends to `λ / (1 - ρ)` in probability.
5. *Slutsky.* Mathlib's `TendstoInDistribution.add_of_tendstoInMeasure_const` concludes.

## References

* [dHF] L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*, Springer, 2006.
* [EKM] P. Embrechts, C. Klüppelberg, T. Mikosch, *Modelling Extremal Events*, Springer, 1997,
  §6.4.2.
* P. Hall, *On some simple estimates of an exponent of regular variation*, J. Roy. Statist.
  Soc. B 44 (1982).
* E. Haeusler, J. L. Teugels, *On asymptotic normality of Hill's estimator for the exponent of
  regular variation*, Ann. Statist. 13 (1985).
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
theorem _root_.MeasureTheory.TendstoInDistribution.of_map_eq {l : Filter ι} {X : ι → Ω → ℝ}
    {X₀ : ι → Ω₀ → ℝ} {Z : Ω' → ℝ} (h : TendstoInDistribution X₀ l Z (fun _ => P₀) P')
    (hX : ∀ i, AEMeasurable (X i) P) (hlaw : ∀ᶠ i in l, P.map (X i) = P₀.map (X₀ i)) :
    TendstoInDistribution X l Z (fun _ => P) P' := by
  refine ⟨hX, h.aemeasurable_limit, h.tendsto.congr' ?_⟩
  filter_upwards [hlaw] with i hi
  exact Subtype.ext hi.symm

/-- Convergence in distribution only depends on the law of the limit. -/
theorem _root_.MeasureTheory.TendstoInDistribution.congr_limit {l : Filter ι} {X : ι → Ω → ℝ}
    {Z : Ω' → ℝ} {Z' : Ω'' → ℝ} (h : TendstoInDistribution X l Z (fun _ => P) P')
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

/-! ### Localization of the intermediate exponential order statistic -/

section Localization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem measure_lt_expMeasure_of_hasLaw {E : Ω → ℝ} (hE : HasLaw E (expMeasure 1) P) {v : ℝ}
    (hv : 0 ≤ v) : P {ω | v < E ω} = ENNReal.ofReal (exp (-v)) := by
  rw [← expMeasure_Ioi hv, ← hE.map_eq, Measure.map_apply_of_aemeasurable hE.aemeasurable
    measurableSet_Ioi]
  rfl

/-- If `k(n) → ∞` and `k(n) / n → 0`, then `n / k(n) → ∞`. -/
theorem tendsto_div_atTop_of_tendsto {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (k n : ℝ) / n := by
    filter_upwards [((tendsto_natCast_atTop_atTop (R := ℝ)).comp hk).eventually_gt_atTop 0,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0] with n h1 h2
    exact div_pos h1 h2
  have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp (tendsto_nhdsWithin_iff.2 ⟨hkn, hpos⟩)
  refine this.congr fun n => ?_
  simp [inv_div]

/-- **Localization of the exponential order statistic**: if the `E_i` are iid standard
exponential, `k(n) → ∞` and `k(n) / n → 0`, then `E_{(k+1)} - log(n / k) → 0` in probability. -/
theorem tendstoInMeasure_orderStat_sub_log {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => orderStat (fun i : Fin n => E i ω) (k n) - log (n / k n))
      atTop (fun _ => 0) := by
  have hident : ∀ i, IdentDistrib (E i) (E 0) P P := fun i =>
    ⟨(hE i).aemeasurable, (hE 0).aemeasurable, by rw [(hE i).map_eq, (hE 0).map_eq]⟩
  have hnk := tendsto_div_atTop_of_tendsto hk hkn
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n :=
    (tendsto_natCast_atTop_atTop.comp hk).eventually_gt_atTop 0
  have hmk : ∀ᶠ n in atTop, 1 * k n < n := by
    filter_upwards [hkn.eventually (gt_mem_nhds one_pos),
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0] with n h1 h2
    rw [div_lt_one h2] at h1
    rw [one_mul]; exact_mod_cast h1
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set η := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  have hlim : ∀ x, 0 ≤ x → Tendsto (fun n : ℕ =>
      n * (P {ω | (log (n / k n) - η) + 1 * x < E 0 ω}).toReal / k n) atTop
      (𝓝 (exp (η - x))) := by
    intro x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hnk.eventually_ge_atTop (exp η), hkpos] with n hn hkn'
    have hn0 : 0 < (n : ℝ) / k n := (exp_pos η).trans_le hn
    have hlog : η ≤ log (n / k n) := by rwa [le_log_iff_exp_le hn0]
    have hn' : (0 : ℝ) < n := (div_pos_iff_of_pos_right hkn').1 hn0
    rw [measure_lt_expMeasure_of_hasLaw (hE 0) (by linarith), ENNReal.toReal_ofReal
      (exp_pos _).le, one_mul, show -(log (n / k n) - η + x) = (η - x) + -log (n / k n) by ring,
      exp_add, exp_neg, exp_log hn0]
    field_simp
  have h := tendsto_measure_not_mem_orderStat hEm hind hident hk hmk (Eventually.of_forall
    fun _ => one_pos) hlim le_rfl (by rw [sub_zero]; exact_mod_cast one_lt_exp_iff.2 hη0)
    (y := 2 * η) (by positivity)
    (by rw [show η - 2 * η = -η by ring]; exact_mod_cast exp_lt_one_iff.2 (by linarith))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => bot_le) fun n => measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, one_mul, div_one] at hω ⊢
  intro hcon
  have : |orderStat (fun i : Fin n => E i ω) (k n) - log (n / k n)| ≤ η :=
    abs_le.2 ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
  linarith

end Localization


/-! ### Ratios of a regularly varying function at random arguments -/

section RandomRatio

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If `f` is measurable and regularly varying, `s_n → ∞` and `D_n → 0` in probability, then
`f(e^{s_n + D_n}) / f(e^{s_n}) → 1` in probability (by the uniform convergence theorem). -/
theorem tendstoInMeasure_ratio_of_isRegularlyVarying {f : ℝ → ℝ} {ρ : ℝ}
    (hf : IsRegularlyVarying f ρ) (hm : Measurable f) {D : ℕ → Ω → ℝ}
    (hD : TendstoInMeasure P D atTop (fun _ => 0)) {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) :
    TendstoInMeasure P (fun n ω => f (exp (s n + D n ω)) / f (exp (s n))) atTop
      (fun _ => 1) := by
  rw [tendstoInMeasure_iff_dist] at hD ⊢
  intro ε hε
  have hc : ContinuousAt (fun d : ℝ => exp (d * ρ)) 0 := by fun_prop
  obtain ⟨η₀, hη₀, hη₀'⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (half_pos hε)
  set η := min η₀ 1 with hη
  have hη0 : 0 < η := lt_min hη₀ one_pos
  have hK : IsCompact (Icc (exp (-1)) (exp 1)) := isCompact_Icc
  have hK0 : Icc (exp (-1)) (exp 1) ⊆ Ioi 0 := fun c hc => (exp_pos _).trans_le hc.1
  have hU := (hf.tendstoUniformlyOn_of_measurable hm hK hK0)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  have hev := (hs.comp tendsto_id).eventually ((tendsto_exp_atTop.eventually (hU (ε / 2)
    (half_pos hε))))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hD η hη0)
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  rw [not_le] at hcon
  have hd1 : |D n ω| < η₀ := hcon.trans_le (min_le_left _ _)
  have hd2 : |D n ω| < 1 := hcon.trans_le (min_le_right _ _)
  have hcK : exp (D n ω) ∈ Icc (exp (-1)) (exp 1) :=
    ⟨exp_le_exp.2 (by linarith [neg_abs_le (D n ω)]),
      exp_le_exp.2 (by linarith [le_abs_self (D n ω)])⟩
  have h1 := hn (exp (D n ω)) hcK
  simp only [Function.comp_apply, id, Real.dist_eq] at h1
  have h2 := hη₀' (x := D n ω) (by simpa [Real.dist_eq] using hd1)
  simp only [zero_mul, exp_zero, Real.dist_eq] at h2
  rw [← exp_mul] at h1
  rw [exp_add, mul_comm] at hω
  have := abs_sub_le (f (exp (D n ω) * exp (s n)) / f (exp (s n))) (exp (D n ω * ρ)) 1
  rw [abs_sub_comm] at h1
  linarith

end RandomRatio

/-! ### A conditional law of large numbers for the top excesses -/

section ConditionalLLN

theorem integrable_exp_mul_expMeasure {a : ℝ} (ha : a < 1) :
    Integrable (fun u => exp (a * u)) (expMeasure 1) := by
  rw [integrable_expMeasure_iff]
  refine (exp_neg_integrableOn_Ioi 0 (sub_pos.2 ha)).congr_fun (fun u _ => ?_) measurableSet_Ioi
  rw [← exp_add]
  ring_nf

theorem integral_exp_mul_expMeasure {a : ℝ} (ha : a < 1) :
    ∫ u, exp (a * u) ∂(expMeasure 1) = 1 / (1 - a) := by
  rw [integral_expMeasure, ← integral_exp_neg_mul_Ioi (sub_pos.2 ha)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [← exp_add]
  ring_nf

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Chebyshev's inequality for the sample mean** of iid square-integrable variables. -/
theorem measure_abs_mean_sub_ge_le {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P) {k : ℕ} (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X i ω - P[X 0]|} ≤
      ENNReal.ofReal (P[X 0 ^ 2] / (k * ε ^ 2)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hL2i : ∀ i, MemLp (X i) 2 P := fun i => (hident i).memLp_iff.2 hL2
  set T : Ω → ℝ := ∑ i ∈ Finset.range k, X i with hT
  have hTfun : ∀ ω, T ω = ∑ i ∈ Finset.range k, X i ω := fun ω => by
    simp [hT, Finset.sum_apply]
  have hTL2 : MemLp T 2 P := memLp_finsetSum' _ fun i _ => hL2i i
  have hET : P[T] = (k : ℝ) * P[X 0] := by
    have : ∫ ω, T ω ∂P = ∑ i ∈ Finset.range k, ∫ ω, X i ω ∂P := by
      simp only [hT, Finset.sum_apply]
      exact integral_finsetSum _ fun i _ => (hL2i i).integrable one_le_two
    rw [this, Finset.sum_congr rfl fun i _ => (hident i).integral_eq, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hVT : variance T P ≤ (k : ℝ) * P[X 0 ^ 2] := by
    rw [hT, IndepFun.variance_sum (fun i _ => hL2i i)
      (fun i _ j _ hij => hindep.indepFun hij)]
    rw [Finset.sum_congr rfl fun i _ => (hident i).variance_eq, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    gcongr
    exact variance_le_expectation_sq (hL2 ).aestronglyMeasurable
  have hsub : {ω | ε ≤ |(k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X i ω - P[X 0]|} ⊆
      {ω | k * ε ≤ |T ω - P[T]|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [hTfun, hET]
    have e : ∑ i ∈ Finset.range k, X i ω - k * P[X 0] =
        k * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, X i ω - P[X 0]) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hk']
    exact mul_le_mul_of_nonneg_left hω hk'.le
  refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq hTL2 (by positivity)).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc variance T P * (k * ε ^ 2) ≤ (k : ℝ) * P[X 0 ^ 2] * (k * ε ^ 2) := by gcongr
    _ = P[X 0 ^ 2] * (k * ε) ^ 2 := by ring

/-- **A conditional law of large numbers for the top excesses.** Let the `E_i` be iid standard
exponential, `k(n) → ∞`, `k(n) < n` and `E_{(k+1)} → ∞` in probability. Let `φ(u, s)` be
jointly measurable, dominated by `C e^{u/4}` for `u ≥ 0` and `s ≥ s₀`, and converging to `H(u)`
as `s → ∞`. Then `(1/k) ∑_{i<k} φ(E_{(i+1)} - E_{(k+1)}, E_{(k+1)}) → E H(E_0)` in probability.

The proof conditions on `E_{(k+1)}` via the Rényi representation, under which the top excesses
are iid exponential, and applies Chebyshev's inequality conditionally. -/
theorem tendstoInMeasure_meanExcess_fun {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : ∀ᶠ n in atTop, k n < n)
    (hok : ∀ M, Tendsto (fun n => P {ω | orderStat (fun i : Fin n => E i ω) (k n) < M}) atTop
      (𝓝 0))
    {φ : ℝ → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) {C s₀ : ℝ}
    (hdom : ∀ s ≥ s₀, ∀ u ≥ 0, |φ u s| ≤ C * exp (u / 4)) {H : ℝ → ℝ}
    (hlim : ∀ u ≥ 0, Tendsto (fun s => φ u s) atTop (𝓝 (H u))) :
    TendstoInMeasure P (fun n ω => ((k n : ℝ))⁻¹ * ∑ i ∈ Finset.range (k n),
        φ (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) (k n))
          (orderStat (fun i : Fin n => E i ω) (k n)))
      atTop (fun _ => ∫ u, H u ∂(expMeasure 1)) := by
  set m : ℝ → ℝ := fun s => ∫ u, φ u s ∂(expMeasure 1) with hm
  have hφs : ∀ s, Measurable fun u => φ u s := fun s =>
    measurable_uncurry_comp hφ measurable_id measurable_const
  have hmm : Measurable m := by
    have := (hφ.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := expMeasure 1)
    exact this.measurable
  have hae : ∀ᵐ u ∂(expMeasure 1), 0 ≤ u := ae_nonneg_expMeasure
  have hbint : Integrable (fun u => C * exp (u / 4)) (expMeasure 1) := by
    have := (integrable_exp_mul_expMeasure (a := 1 / 4) (by norm_num)).const_mul C
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only
    ring_nf
  have hmlim : Tendsto m atTop (𝓝 (∫ u, H u ∂(expMeasure 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => C * exp (u / 4))
      (Eventually.of_forall fun s => (hφs s).aestronglyMeasurable) ?_ hbint ?_
    · filter_upwards [eventually_ge_atTop s₀] with s hs
      filter_upwards [hae] with u hu
      rw [Real.norm_eq_abs]
      exact hdom s hs u hu
    · filter_upwards [hae] with u hu
      exact hlim u hu
  -- Chebyshev, for a fixed threshold `s`
  have hsq : ∀ s ≥ s₀, ∫ u, φ u s ^ 2 ∂(expMeasure 1) ≤ C ^ 2 * 2 := by
    intro s hs
    have h2 : Integrable (fun u => C ^ 2 * exp (1 / 2 * u)) (expMeasure 1) :=
      (integrable_exp_mul_expMeasure (by norm_num)).const_mul _
    calc ∫ u, φ u s ^ 2 ∂(expMeasure 1) ≤ ∫ u, C ^ 2 * exp (1 / 2 * u) ∂(expMeasure 1) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) h2 ?_
          filter_upwards [hae] with u hu
          have := hdom s hs u hu
          have h0 : 0 ≤ C * exp (u / 4) := (abs_nonneg _).trans this
          calc φ u s ^ 2 = |φ u s| ^ 2 := (sq_abs _).symm
            _ ≤ (C * exp (u / 4)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
            _ = C ^ 2 * exp (1 / 2 * u) := by rw [mul_pow, ← exp_nat_mul]; ring_nf
      _ = C ^ 2 * 2 := by
          rw [integral_const_mul, integral_exp_mul_expMeasure (by norm_num)]; norm_num
  have hL2 : ∀ s ≥ s₀, MemLp (fun u => φ u s) 2 (expMeasure 1) := by
    intro s hs
    refine (memLp_two_iff_integrable_sq (hφs s).aestronglyMeasurable).2 ?_
    refine Integrable.mono' ((integrable_exp_mul_expMeasure (a := 1 / 2) (by norm_num)).const_mul
      (C ^ 2)) ((hφs s).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hae] with u hu
    have := hdom s hs u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc φ u s ^ 2 = |φ u s| ^ 2 := (sq_abs _).symm
      _ ≤ (C * exp (u / 4)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = C ^ 2 * exp (1 / 2 * u) := by rw [mul_pow, ← exp_nat_mul]; ring_nf
  have hcheb : ∀ s ≥ s₀, ∀ j : ℕ, 0 < j → ∀ ε > 0,
      P {ω | ε ≤ |(j : ℝ)⁻¹ * ∑ i ∈ Finset.range j, φ (E i ω) s - m s|} ≤
        ENNReal.ofReal (C ^ 2 * 2 / (j * ε ^ 2)) := by
    intro s hs j hj ε hε
    have hX := measure_abs_mean_sub_ge_le (X := fun i ω => φ (E i ω) s)
      (hind.comp (fun _ x => φ x s) fun _ => hφs s)
      (fun i => ⟨(hφs s).comp_aemeasurable (hE i).aemeasurable,
        (hφs s).comp_aemeasurable (hE 0).aemeasurable, by
          rw [show (fun ω => φ (E i ω) s) = (fun u => φ u s) ∘ E i from rfl,
            show (fun ω => φ (E 0 ω) s) = (fun u => φ u s) ∘ E 0 from rfl,
            ← Measure.map_map (hφs s) (hEm i), ← Measure.map_map (hφs s) (hEm 0),
            (hE i).map_eq, (hE 0).map_eq]⟩)
      ((hE 0).memLp_comp (hL2 s hs)) hj hε
    have e1 : P[fun ω => φ (E 0 ω) s] = m s :=
      (hE 0).integral_comp (f := fun u => φ u s) (hφs s).aestronglyMeasurable
    have e2 : P[(fun ω => φ (E 0 ω) s) ^ 2] = ∫ u, φ u s ^ 2 ∂(expMeasure 1) := by
      rw [← (hE 0).integral_comp (f := fun u => φ u s ^ 2)
        ((hφs s).pow_const 2).aestronglyMeasurable]
      rfl
    rw [e1, e2] at hX
    refine hX.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact hsq s hs
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 ((hmlim.eventually (Metric.ball_mem_nhds _
    (half_pos hε))).and (eventually_ge_atTop s₀))
  set ε' := ε / 2 with hε'
  have hε'0 : 0 < ε' := half_pos hε
  set B : Set (ℝ × ℝ) := {q | s₁ ≤ q.2 ∧ ε' ≤ |q.1 - m q.2|} with hB
  have hBm : MeasurableSet B :=
    (measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_const
      (continuous_abs.measurable.comp (measurable_fst.sub (hmm.comp measurable_snd))))
  -- the conditional Chebyshev bound, via the Rényi representation
  have hbound : ∀ᶠ n in atTop, P {ω | s₁ ≤ orderStat (fun i : Fin n => E i ω) (k n) ∧
      ε' ≤ |((k n : ℝ))⁻¹ * ∑ i ∈ Finset.range (k n),
        φ (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) (k n))
          (orderStat (fun i : Fin n => E i ω) (k n)) -
        m (orderStat (fun i : Fin n => E i ω) (k n))|} ≤
      ENNReal.ofReal (C ^ 2 * 2 / (k n * ε' ^ 2)) := by
    filter_upwards [hkn, hk.eventually_gt_atTop 0] with n hn hk0
    set j := k n with hj
    set F : ℝ → ℝ → ℝ≥0∞ := fun x s => B.indicator 1 ((j : ℝ)⁻¹ * x, s) with hF
    have hFm : Measurable (Function.uncurry F) :=
      (measurable_one.indicator hBm).comp ((measurable_const.mul measurable_fst).prodMk
        measurable_snd)
    have hmo := measurable_orderStat_pi (n := n) j
    have hSm : MeasurableSet {y : Fin n → ℝ | ((j : ℝ)⁻¹ * ∑ i ∈ Finset.range j,
        φ (orderStat y i - orderStat y j) (orderStat y j), orderStat y j) ∈ B} :=
      hBm.preimage ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        measurable_uncurry_comp hφ ((measurable_orderStat_pi i).sub hmo) hmo)).prodMk hmo)
    have e1 := (hasLaw_vec_of_iid hE hind n).measure_eq hSm
    have e2 := lintegral_orderStat_excess hn hφ hFm
    have e0 : P {ω | s₁ ≤ orderStat (fun i : Fin n => E i ω) j ∧
        ε' ≤ |((j : ℝ))⁻¹ * ∑ i ∈ Finset.range j,
          φ (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) j)
            (orderStat (fun i : Fin n => E i ω) j) -
          m (orderStat (fun i : Fin n => E i ω) j)|} =
        ∫⁻ y, ∫⁻ z, F (∑ i, φ (z i) (orderStat y j)) (orderStat y j)
          ∂(Measure.pi fun _ : Fin j => expMeasure 1)
          ∂(Measure.pi fun _ : Fin n => expMeasure 1) := by
      refine (e1.trans ?_).trans e2
      rw [← lintegral_indicator_one hSm]
      rfl
    rw [e0]
    have inner : ∀ s, ∫⁻ z, F (∑ i, φ (z i) s) s ∂(Measure.pi fun _ : Fin j => expMeasure 1) ≤
        ENNReal.ofReal (C ^ 2 * 2 / (j * ε' ^ 2)) := by
      intro s
      by_cases hs : s₁ ≤ s
      · have hTm : MeasurableSet {z : Fin j → ℝ | ε' ≤ |(j : ℝ)⁻¹ * ∑ i, φ (z i) s - m s|} :=
          measurableSet_le measurable_const (continuous_abs.measurable.comp
            ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
              (hφs s).comp (measurable_pi_apply i))).sub_const _))
        have e3 : ∫⁻ z, F (∑ i, φ (z i) s) s ∂(Measure.pi fun _ : Fin j => expMeasure 1) =
            (Measure.pi fun _ : Fin j => expMeasure 1)
              {z | ε' ≤ |(j : ℝ)⁻¹ * ∑ i, φ (z i) s - m s|} := by
          rw [← lintegral_indicator_one hTm]
          congr 1 with z
          simp [hF, hB, Set.indicator, hs]
        have e4 := (hasLaw_vec_of_iid hE hind j).measure_eq hTm
        rw [e3, ← e4]
        have := hcheb s ((hs₁ s hs).2) j hk0 ε' hε'0
        refine le_of_eq_of_le ?_ this
        congr 1
        ext ω
        simp only [mem_ofPred_eq]
        rw [Fin.sum_univ_eq_sum_range (fun i => φ (E i ω) s) j]
      · have : ∀ z : Fin j → ℝ, F (∑ i, φ (z i) s) s = 0 := fun z => by
          simp [hF, hB, Set.indicator, hs]
        simp [this]
    calc ∫⁻ y, ∫⁻ z, F (∑ i, φ (z i) (orderStat y j)) (orderStat y j)
          ∂(Measure.pi fun _ : Fin j => expMeasure 1) ∂(Measure.pi fun _ : Fin n => expMeasure 1)
        ≤ ∫⁻ _, ENNReal.ofReal (C ^ 2 * 2 / (j * ε' ^ 2))
          ∂(Measure.pi fun _ : Fin n => expMeasure 1) := lintegral_mono fun y => inner _
      _ = ENNReal.ofReal (C ^ 2 * 2 / (j * ε' ^ 2)) := by simp
  have htend : Tendsto (fun n => ENNReal.ofReal (C ^ 2 * 2 / (k n * ε' ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp hk
    have := (tendsto_inv_atTop_zero.comp hkR).const_mul (C ^ 2 * 2 / ε' ^ 2)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    field_simp
  have h0 := (hok s₁).add htend
  rw [add_zero] at h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hbound] with n hn
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl hn))

  intro ω hω
  simp only [mem_ofPred_eq, Real.dist_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h3 := (hs₁ _ h1).1
  rw [Real.dist_eq] at h3
  have h4 := h2 h1
  have := abs_sub_le ((k n : ℝ)⁻¹ * ∑ i ∈ Finset.range (k n),
    φ (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) (k n))
      (orderStat (fun i : Fin n => E i ω) (k n)))
    (m (orderStat (fun i : Fin n => E i ω) (k n))) (∫ u, H u ∂(expMeasure 1))
  linarith


end ConditionalLLN

/-! ### Auxiliary facts for the general case -/

section Auxiliary

variable {n : ℕ}

/-- Order statistics commute with maps that are monotone on a set containing the sample. -/
theorem orderStat_comp_monotoneOn {g : ℝ → ℝ} {S : Set ℝ} (hg : MonotoneOn g S)
    {y : Fin n → ℝ} (hy : ∀ i, y i ∈ S) {j : ℕ} (hj : j < n) :
    orderStat (g ∘ y) j = g (orderStat y j) := by
  rw [orderStat_of_lt _ hj, orderStat_of_lt _ hj]
  have hmono : Monotone ((g ∘ y) ∘ Tuple.sort y) := fun a b hab =>
    hg (hy _) (hy _) (Tuple.monotone_sort y hab)
  have : (g ∘ y) ∘ Tuple.sort (g ∘ y) = (g ∘ y) ∘ Tuple.sort y :=
    Tuple.unique_monotone (Tuple.monotone_sort _) hmono
  exact congrFun this _

/-- The second-order remainder `log U(e^u e^s) - log U(e^s) - γ u`. -/
noncomputable def logRemainder (U : ℝ → ℝ) (γ u s : ℝ) : ℝ :=
  log (U (exp u * exp s)) - log (U (exp s)) - γ * u

/-- The Hill estimator of the sample `U(e^{y_i})`, for `U` monotone on `(1, ∞)` and `y_i > 0`,
splits into `γ` times the mean top excess of `y` and the mean second-order remainder. -/
theorem hill_comp_exp_eq {U : ℝ → ℝ} (hU : MonotoneOn U (Ioi 1)) (γ : ℝ) {y : Fin n → ℝ}
    (hy : ∀ i, 0 < y i) {k : ℕ} (hk : k < n) :
    hill (fun i => U (exp (y i))) k =
      γ * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (orderStat y i - orderStat y k)) +
        (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
          logRemainder U γ (orderStat y i - orderStat y k) (orderStat y k) := by
  have hmono : MonotoneOn (fun x => U (exp x)) (Ioi 0) := fun a ha b hb hab =>
    hU (one_lt_exp_iff.2 ha) (one_lt_exp_iff.2 hb) (exp_le_exp.2 hab)
  have h := fun j (hj : j < n) => orderStat_comp_monotoneOn hmono (y := y) (fun i => hy i) hj
  simp only [Function.comp_def] at h
  rw [hill, show ∀ a b : ℕ → ℝ, γ * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, a i) +
      (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, b i =
      (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (γ * a i + b i) by
    intro a b; rw [Finset.sum_add_distrib, ← Finset.mul_sum]; ring]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := (Finset.mem_range.1 hi).trans hk
  rw [h i hi', h k hk, logRemainder, ← exp_add, sub_add_cancel]
  ring

theorem integral_boxCox_exp {ρ : ℝ} (hρ : ρ ≤ 0) :
    ∫ u, boxCox ρ (exp u) ∂(expMeasure 1) = 1 / (1 - ρ) := by
  simp_rw [boxCox_exp]
  split_ifs with h
  · rw [integral_id_expMeasure, h]; norm_num
  · have hρ1 : ρ < 1 := by linarith
    rw [integral_div, integral_sub (integrable_exp_mul_expMeasure hρ1) (integrable_const _),
      integral_exp_mul_expMeasure hρ1]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    have : (1 : ℝ) - ρ ≠ 0 := by linarith
    field_simp
    ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem tendstoInMeasure_of_tendsto {a : ℕ → ℝ} {c : ℝ} (ha : Tendsto a atTop (𝓝 c)) :
    TendstoInMeasure P (fun n (_ : Ω) => a n) atTop (fun _ => c) :=
  tendstoInMeasure_const_of_tendsto ha

omit [IsProbabilityMeasure P] in
/-- If `f_n = g_n` outside events of vanishing probability and `g_n → c` in probability, then
`f_n → c` in probability. -/
theorem _root_.MeasureTheory.TendstoInMeasure.congr_of_measure_ne
 {f g : ℕ → Ω → ℝ} {c : ℝ}
    (hg : TendstoInMeasure P g atTop (fun _ => c))
    (hfg : Tendsto (fun n => P {ω | f n ω ≠ g n ω}) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  have h := hfg.add (hg ε hε)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  by_cases hfg' : f n ω = g n ω
  · right
    simp only [mem_ofPred_eq] at hω ⊢
    rwa [← hfg']
  · left
    exact hfg'

end Auxiliary

/-! ### The general case, on the exponential scale -/

section General

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

theorem eventually_lt_of_tendsto_div {k : ℕ → ℕ}
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) : ∀ᶠ n in atTop, k n < n := by
  filter_upwards [hkn.eventually (gt_mem_nhds one_pos),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0] with n h1 h2
  rw [div_lt_one h2] at h1
  exact_mod_cast h1

theorem IsSecondOrderRegularlyVarying.exists_div_eq_abs_div {U A : ℝ → ℝ} {γ ρ : ℝ}
    (h : IsSecondOrderRegularlyVarying U γ ρ A) :
    ∃ T, ∀ x ≥ T, A x ≠ 0 ∧ ∀ y ≥ T, A x / A y = |A x| / |A y| := by
  rcases h.sign with h' | h'
  · obtain ⟨T, hT⟩ := eventually_atTop.1 h'
    exact ⟨T, fun x hx => ⟨(hT x hx).ne', fun y hy => by
      rw [abs_of_pos (hT x hx), abs_of_pos (hT y hy)]⟩⟩
  · obtain ⟨T, hT⟩ := eventually_atTop.1 h'
    exact ⟨T, fun x hx => ⟨(hT x hx).ne, fun y hy => by
      rw [abs_of_neg (hT x hx), abs_of_neg (hT y hy), neg_div_neg_eq]⟩⟩

/-- **Asymptotic normality of the Hill estimator on the exponential scale.** Let the `E_i` be iid
standard exponential, and let `U` be measurable, monotone on `(1, ∞)` and of second-order regular
variation with indices `γ > 0`, `ρ ≤ 0` and auxiliary function `A`. If `k(n) → ∞`,
`k(n) / n → 0` and `√k A(n/k) → λ`, then the Hill estimator of the sample `U(e^{E_i})` satisfies
`√k (H_{k,n} - γ) ⇒ N(λ / (1 - ρ), γ²)`. -/
theorem tendstoInDistribution_hill_comp_exp {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P)
    {U A : ℝ → ℝ} {γ ρ lam : ℝ} (hγ : 0 < γ) (hU : Measurable U) (hUm : MonotoneOn U (Ioi 1))
    (h2 : IsSecondOrderRegularlyVarying U γ ρ A) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal (lam / (1 - ρ)) (γ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω =>
        √(k n : ℝ) * (hill (fun i : Fin n => U (exp (E i ω))) (k n) - γ))
      atTop Z (fun _ => P) P' := by
  -- a measurable auxiliary function
  obtain ⟨B, hBm, h2B, hBA⟩ := h2.exists_measurable hU
  have hnk := tendsto_div_atTop_of_tendsto hk hkn
  have hkn' := eventually_lt_of_tendsto_div hkn
  have hlamB : Tendsto (fun n => √(k n : ℝ) * B (n / k n)) atTop (𝓝 lam) := by
    have := hlam.mul (hBA.comp hnk)
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hnk.eventually h2.eventually_ne_zero] with n hn
    simp only [Function.comp_apply]
    field_simp
  -- the main term
  set c₀ := lam / (1 - ρ) with hc₀
  have hY1 : HasLaw (fun ω => (Z ω - c₀) / γ) (gaussianReal 0 1) P' := by
    have := gaussianReal_div_const (gaussianReal_sub_const hZ c₀) γ
    convert this using 2
    · simp
    · ext
      simp only [NNReal.coe_one, NNReal.coe_div, NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg _)]
      field_simp
  have hT1 := (tendstoInDistribution_meanExcess hEm hE hind hk hkn' hY1).continuous_comp
    (g := fun x => γ * x) (by fun_prop)
  -- the bias term: domination and pointwise limit of the normalized remainder
  obtain ⟨C, t₀, ht₀, hbd⟩ := h2B.exists_bound hU hBm (δ := 1 / 4) (by norm_num)
  set φ : ℝ → ℝ → ℝ := fun u s => logRemainder U γ u s / B (exp s) with hφ
  have hRm : Measurable (Function.uncurry (logRemainder U γ)) := by
    unfold logRemainder
    refine ((hU.comp ((measurable_exp.comp measurable_fst).mul
      (measurable_exp.comp measurable_snd))).log.sub (hU.comp
      (measurable_exp.comp measurable_snd)).log).sub (measurable_fst.const_mul γ)
  have hφm : Measurable (Function.uncurry φ) :=
    hRm.div (hBm.comp (measurable_exp.comp measurable_snd))
  have hdom : ∀ s ≥ log t₀, ∀ u ≥ 0, |φ u s| ≤ |C| * exp (u / 4) := by
    intro s hs u hu
    have hts : t₀ ≤ exp s := (log_le_iff_le_exp ht₀).1 hs
    have h1 := hbd (exp s) hts (exp u) (one_le_exp hu)
    rw [log_exp, rpow_def_of_pos (exp_pos u), log_exp] at h1
    have e : logRemainder U γ u s = log (U (exp u * exp s)) - log (U (exp s)) - γ * u := rfl
    simp only [hφ, abs_div]
    rcases eq_or_ne (B (exp s)) 0 with h0 | h0
    · simp [h0]; positivity
    rw [div_le_iff₀ (abs_pos.2 h0), e]
    calc _ ≤ C * |B (exp s)| * exp (u * (1 / 4)) := h1
      _ ≤ |C| * |B (exp s)| * exp (u * (1 / 4)) := by gcongr; exact le_abs_self C
      _ = |C| * exp (u / 4) * |B (exp s)| := by ring_nf
  have hlimφ : ∀ u ≥ (0 : ℝ), Tendsto (fun s => φ u s) atTop (𝓝 (boxCox ρ (exp u))) := by
    intro u _
    refine ((h2B.tendsto_log (exp_pos u)).comp tendsto_exp_atTop).congr fun s => ?_
    simp only [Function.comp_apply, hφ, logRemainder, log_exp]
  -- localization of `E_{(k+1)}`
  have hD := tendstoInMeasure_orderStat_sub_log hEm hE hind hk hkn
  have hok : ∀ M, Tendsto (fun n => P {ω | orderStat (fun i : Fin n => E i ω) (k n) < M})
      atTop (𝓝 0) := by
    intro M
    have hD1 := (tendstoInMeasure_iff_dist.1 hD) 1 one_pos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD1
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [(tendsto_log_atTop.comp hnk).eventually_ge_atTop (M + 1)] with n hn
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, Function.comp_apply] at hω hn ⊢
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  -- the normalized remainder average converges to `1 / (1 - ρ)`
  have hW := tendstoInMeasure_meanExcess_fun hEm hE hind hk hkn' hok hφm hdom hlimφ
  rw [integral_boxCox_exp h2.nonpos] at hW
  -- the ratio `B(e^{E_{(k+1)}}) / B(n / k)` converges to `1`
  obtain ⟨T, hT⟩ := h2B.exists_div_eq_abs_div
  have hBabs : Measurable fun t => |B t| := continuous_abs.measurable.comp hBm
  have hR := tendstoInMeasure_ratio_of_isRegularlyVarying h2B.isRegularlyVarying_abs hBabs hD
    (tendsto_log_atTop.comp hnk)
  have hQ : TendstoInMeasure P (fun n ω => B (exp (orderStat (fun i : Fin n => E i ω) (k n))) /
      B (n / k n)) atTop (fun _ => 1) := by
    refine hR.congr_of_measure_ne ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hok (log (max T 1)))
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hnk.eventually_ge_atTop (max T 1)] with n hn
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq, Function.comp_apply] at hω ⊢
    by_contra hcon
    rw [not_lt] at hcon
    apply hω
    have hpos : (0 : ℝ) < n / k n := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)
    rw [add_sub_cancel, exp_log hpos]
    have hx : T ≤ exp (orderStat (fun i : Fin n => E i ω) (k n)) := by
      have := (log_le_iff_le_exp (lt_of_lt_of_le one_pos (le_max_right T 1))).1 hcon
      exact (le_max_left _ _).trans this
    exact (hT _ hx).2 _ ((le_max_left _ _).trans hn)
  -- the bias term
  have hdet := tendstoInMeasure_of_tendsto (P := P) hlamB
  have hprod := tendstoInMeasure_comp₂ (tendstoInMeasure_comp₂ hdet hQ
    (φ := fun p => p.1 * p.2) (by fun_prop)) hW (φ := fun p => p.1 * p.2) (by fun_prop)
  simp only [mul_one] at hprod
  -- measurability
  have hmo : ∀ n j, Measurable fun ω => orderStat (fun i : Fin n => E i ω) j := fun n j =>
    measurable_orderStat (fun i => hEm i) j
  have hT2m : ∀ n, AEMeasurable (fun ω => √(k n : ℝ) * B (n / k n) *
      (B (exp (orderStat (fun i : Fin n => E i ω) (k n))) / B (n / k n)) *
      (((k n : ℝ))⁻¹ * ∑ i ∈ Finset.range (k n), φ (orderStat (fun i : Fin n => E i ω) i -
        orderStat (fun i : Fin n => E i ω) (k n)) (orderStat (fun i : Fin n => E i ω) (k n))))
      P := fun n =>
    ((measurable_const.mul ((hBm.comp (measurable_exp.comp (hmo n (k n)))).div_const _)).mul
      (measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_uncurry_comp hφm
        ((hmo n i).sub (hmo n (k n))) (hmo n (k n))))).aemeasurable
  -- Slutsky
  have hS := hT1.add_of_tendstoInMeasure_const hprod hT2m
  have hS' := hS.congr_limit hZ.aemeasurable (by
    congr 1
    funext ω
    simp only [Function.comp_apply]
    field_simp
    ring)
  have hYm : ∀ n, AEMeasurable (fun ω =>
      √(k n : ℝ) * (hill (fun i : Fin n => U (exp (E i ω))) (k n) - γ)) P := fun n =>
    (measurable_const.mul (((measurable_hill_pi n (k n)).comp (measurable_pi_iff.2 fun i =>
      hU.comp (measurable_exp.comp (hEm i)))).sub_const _)).aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hS' ?_ hYm
  have hzero : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto tendsto_const_nhds
  have hnull : ∀ n : ℕ, P {ω | ∃ i : Fin n, E i ω ≤ 0} = 0 := by
    intro n
    have : {ω | ∃ i : Fin n, E i ω ≤ 0} = ⋃ i : Fin n, {ω | E i ω ≤ 0} := by ext; simp
    rw [this]
    refine measure_iUnion_null fun i => ?_
    have := (hE i).measure_eq (p := fun x => x ≤ 0) measurableSet_Iic
    rw [this]
    have h0 := expMeasure_Iic (le_refl (0 : ℝ))
    simp only [neg_zero, exp_zero, sub_self, ENNReal.ofReal_zero] at h0
    exact h0
  refine hzero.congr_of_measure_ne ?_
  have h0 := hok (log (max T 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hnk.eventually_ge_atTop (max T 1), hkn'] with n hn hkn
  refine (measure_mono fun ω hω => ?_).trans ((measure_union_le
    {ω | ∃ i : Fin n, E i ω ≤ 0}
    {ω | orderStat (fun i : Fin n => E i ω) (k n) < log (max T 1)}).trans
    (by rw [hnull n, zero_add]))
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨hpos, hok'⟩ := hcon
  apply hω
  have hT1' : max T 1 ≤ exp (orderStat (fun i : Fin n => E i ω) (k n)) :=
    (log_le_iff_le_exp (lt_of_lt_of_le one_pos (le_max_right T 1))).1 hok'
  have hb1 : B (exp (orderStat (fun i : Fin n => E i ω) (k n))) ≠ 0 :=
    (hT _ ((le_max_left _ _).trans hT1')).1
  have hb2 : B (n / k n) ≠ 0 := (hT _ ((le_max_left _ _).trans hn)).1
  have hh := hill_comp_exp_eq hUm γ (y := fun i : Fin n => E i ω) hpos hkn
  simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply]
  rw [hh, hφ]
  simp only
  rw [← Finset.sum_div]
  field_simp
  ring





end General

/-! ### The tail quantile function and the quantile transform -/

section TailQuantile

/-- The **tail quantile function** `U(t) = (1 / (1 - F))^←(t) = inf {x | F̄(x) ≤ 1/t}` of a
survival function `F̄`, for `t > 1` ([dHF, §1.1.2]); we set `U(t) = 0` for `t ≤ 1`. -/
noncomputable def survivalQuantile (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 1 < t then sInf {x | F x ≤ t⁻¹} else 0

variable {F : ℝ → ℝ}

/-- The Galois connection of the tail quantile function: for `t > 1`,
`U(t) ≤ x ↔ F̄(x) ≤ 1/t`. -/
theorem tailQuantile_le_iff (hF : Antitone F) (hrc : ∀ x, ContinuousWithinAt F (Ici x) x)
    (h0 : Tendsto F atTop (𝓝 0)) (h1 : Tendsto F atBot (𝓝 1)) {t : ℝ} (ht : 1 < t) (x : ℝ) :
    survivalQuantile F t ≤ x ↔ F x ≤ t⁻¹ := by
  have hp : 0 < t⁻¹ := inv_pos.2 (one_pos.trans ht)
  have hp1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  obtain ⟨M, hM⟩ := (h1.eventually (lt_mem_nhds hp1)).exists
  obtain ⟨hU1, hU2, -⟩ := threshold_spec hF hrc h0 hp hM
  simp only [survivalQuantile, ht, ↓reduceIte]
  constructor
  · intro hx
    exact (hF hx).trans hU1
  · intro hx
    by_contra hcon
    exact absurd hx (not_le.2 (hU2 x (not_le.1 hcon)))

theorem monotoneOn_tailQuantile (hF : Antitone F) (hrc : ∀ x, ContinuousWithinAt F (Ici x) x)
    (h0 : Tendsto F atTop (𝓝 0)) (h1 : Tendsto F atBot (𝓝 1)) :
    MonotoneOn (survivalQuantile F) (Ioi 1) := by
  intro t ht t' ht' htt'
  rw [tailQuantile_le_iff hF hrc h0 h1 ht]
  have := (tailQuantile_le_iff hF hrc h0 h1 ht' (survivalQuantile F t')).1 le_rfl
  exact this.trans (inv_anti₀ (one_pos.trans ht) htt')

theorem measurable_tailQuantile (hF : Antitone F) (hrc : ∀ x, ContinuousWithinAt F (Ici x) x)
    (h0 : Tendsto F atTop (𝓝 0)) (h1 : Tendsto F atBot (𝓝 1)) :
    Measurable (survivalQuantile F) := by
  refine measurable_of_restrict_of_restrict_compl (s := Ioi 1) measurableSet_Ioi ?_ ?_
  · have : Monotone ((Ioi (1 : ℝ)).domRestrict (survivalQuantile F)) := fun a b hab =>
      monotoneOn_tailQuantile hF hrc h0 h1 a.2 b.2 hab
    exact this.measurable
  · have : (Ioi (1 : ℝ))ᶜ.domRestrict (survivalQuantile F) = fun _ => 0 := by
      ext ⟨t, ht⟩
      have ht' : ¬ 1 < t := ht
      simp [Set.domRestrict, survivalQuantile, ht']
    rw [this]
    exact measurable_const

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem tendsto_survival_atBot {Y : Ω → ℝ} (hY : Measurable Y) :
    Tendsto (survival P Y) atBot (𝓝 1) := by
  have h := (tendsto_cdf_atBot (μ := P.map Y)).const_sub 1
  rw [sub_zero] at h
  exact h.congr fun y => (survival_eq_one_sub_cdf (P := P) hY y).symm

/-- **The quantile transform**: if `E` is standard exponential, then `U(e^E)` has the law of `Y`,
where `U` is the tail quantile function of the survival function of `Y`. -/
theorem map_eq_expMeasure_map_tailQuantile {Y : Ω → ℝ} (hY : Measurable Y) :
    P.map Y = (expMeasure 1).map (fun e => survivalQuantile (survival P Y) (exp e)) := by
  set F := survival P Y with hFdef
  have hF := survival_anti (P := P) Y
  have hrc := continuousWithinAt_survival (P := P) hY
  have h0 := tendsto_survival_atTop (P := P) hY
  have h1 := tendsto_survival_atBot (P := P) hY
  have hVm : Measurable fun e => survivalQuantile F (exp e) :=
    (measurable_tailQuantile hF hrc h0 h1).comp measurable_exp
  refine measure_eq_of_Ioi fun a => ?_
  rw [Measure.map_apply hY measurableSet_Ioi, Measure.map_apply hVm measurableSet_Ioi]
  have hPa : P (Y ⁻¹' Ioi a) = ENNReal.ofReal (F a) := by
    rw [hFdef, survival, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  have hF1 : F a ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hnull : expMeasure 1 (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi, expMeasure_Iic le_rfl]; simp
  rw [hPa, ← measure_inter_conull hnull]
  have hset : (fun e => survivalQuantile F (exp e)) ⁻¹' Ioi a ∩ Ioi 0 =
      {e | exp (-e) < F a} ∩ Ioi 0 := by
    ext e
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_ofPred_eq]
    constructor
    · rintro ⟨h, he⟩
      refine ⟨?_, he⟩
      have := mt (tailQuantile_le_iff hF hrc h0 h1 (one_lt_exp_iff.2 he) a).2 (not_le.2 h)
      rw [not_le, ← exp_neg] at this
      exact this
    · rintro ⟨h, he⟩
      refine ⟨?_, he⟩
      by_contra hcon
      rw [not_lt, tailQuantile_le_iff hF hrc h0 h1 (one_lt_exp_iff.2 he), ← exp_neg] at hcon
      exact absurd h (not_lt.2 hcon)
  rw [hset]
  rcases (survival_nonneg (P := P) (Y := Y) a).lt_or_eq with hpos | hzero
  · have e2 : {e | exp (-e) < F a} = Ioi (-log (F a)) := by
      ext e
      simp only [mem_ofPred_eq, mem_Ioi]
      rw [← lt_log_iff_exp_lt hpos, neg_lt]
    have hlog : log (F a) ≤ 0 := log_nonpos hpos.le hF1
    rw [e2, Set.inter_eq_left.2 (Ioi_subset_Ioi (by linarith)),
      expMeasure_Ioi (by linarith), neg_neg, exp_log hpos]

  · have e2 : {e | exp (-e) < F a} = ∅ := by
      ext e
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [hFdef, ← hzero]
      exact (exp_pos _).le
    rw [e2, empty_inter, measure_empty, hFdef, ← hzero, ENNReal.ofReal_zero]


end TailQuantile

/-! ### Asymptotic normality of the Hill estimator -/

section Normality

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Asymptotic normality of the Hill estimator** ([dHF, Theorem 3.2.5]; Hall 1982;
Haeusler and Teugels 1985). Let `X_0, X_1, …` be iid real random variables whose tail quantile
function `U(t) = F̄^←(1/t)` is of second-order regular variation with first-order index `γ > 0`,
second-order index `ρ ≤ 0` and auxiliary function `A`. If `k = k(n) → ∞`, `k / n → 0` and
`√k A(n / k) → λ`, then

  `√k (H_{k,n} - γ) ⇒ N(λ / (1 - ρ), γ²)`.

The limit is expressed as convergence in distribution to any random variable `Z` with law
`N(λ / (1 - ρ), γ²)`. -/
theorem tendstoInDistribution_hill {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ lam : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal (lam / (1 - ρ)) (γ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - γ))
      atTop Z (fun _ => P) P' := by
  obtain ⟨Ω₀, _, P₀, E, hEm, hE, hind, hP₀⟩ := exists_iid ℕ (expMeasure 1)
  set U := survivalQuantile (survival P (X 0)) with hUdef
  have hF := survival_anti (P := P) (X 0)
  have hrc := continuousWithinAt_survival (P := P) (hX 0)
  have h0 := tendsto_survival_atTop (P := P) (hX 0)
  have h1 := tendsto_survival_atBot (P := P) (hX 0)
  have hUm := measurable_tailQuantile hF hrc h0 h1
  have hUmono := monotoneOn_tailQuantile hF hrc h0 h1
  have hB := tendstoInDistribution_hill_comp_exp hEm hE hind hγ hUm hUmono h2 hk hkn hlam hZ
  have hV : Measurable fun e => U (exp e) := hUm.comp measurable_exp
  refine hB.of_map_eq (fun n => ?_) (Eventually.of_forall fun n => ?_)
  · exact (measurable_const.mul (((measurable_hill_pi n (k n)).comp
      (measurable_pi_iff.2 fun i => hX i)).sub_const _)).aemeasurable
  have hS : Measurable fun y : Fin n → ℝ => √(k n : ℝ) * (hill y (k n) - γ) :=
    measurable_const.mul ((measurable_hill_pi n (k n)).sub measurable_const)
  have hlawX : HasLaw (fun ω (i : Fin n) => X i ω)
      (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => U (exp e)) P := by
    refine (hindep.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective).hasLaw_pi
      (fun i => ⟨(hX i).aemeasurable, ?_⟩)
    rw [(hident i).map_eq]
    exact map_eq_expMeasure_map_tailQuantile (hX 0)
  have e1 : P.map (fun ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - γ)) =
      (Measure.pi fun _ : Fin n => (expMeasure 1).map fun e => U (exp e)).map
        (fun y : Fin n → ℝ => √(k n : ℝ) * (hill y (k n) - γ)) :=
    ((hasLaw_map hS.aemeasurable).comp hlawX).map_eq
  have hT : Measurable fun y : Fin n → ℝ =>
      √(k n : ℝ) * (hill (fun i => U (exp (y i))) (k n) - γ) :=
    hS.comp (measurable_pi_iff.2 fun i => hV.comp (measurable_pi_apply i))
  have e2 : P₀.map (fun ω => √(k n : ℝ) * (hill (fun i : Fin n => U (exp (E i ω))) (k n) - γ)) =
      (Measure.pi fun _ : Fin n => expMeasure 1).map
        (fun y : Fin n → ℝ => √(k n : ℝ) * (hill (fun i => U (exp (y i))) (k n) - γ)) :=
    map_comp_vec_of_iid hE hind hT
  rw [e1, e2, ← Measure.pi_map_pi (fun _ => hV.aemeasurable), Measure.map_map hS (by fun_prop)]
  rfl

/-- **Asymptotic normality of the Hill estimator without bias** ([dHF, Theorem 3.2.5] with
`λ = 0`). Under second-order regular variation of the tail quantile function, if `k → ∞`,
`k / n → 0` and `√k A(n / k) → 0`, then `√k (H_{k,n} - γ) ⇒ N(0, γ²)`. -/
theorem tendstoInDistribution_hill_of_tendsto_zero {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {γ ρ : ℝ}
    {A : ℝ → ℝ} (hγ : 0 < γ)
    (h2 : IsSecondOrderRegularlyVarying (survivalQuantile (survival P (X 0))) γ ρ A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hA : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 0)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (γ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) * (hill (fun i : Fin n => X i ω) (k n) - γ))
      atTop Z (fun _ => P) P' :=
  tendstoInDistribution_hill hX hindep hident hγ h2 hk hkn hA (by rwa [zero_div])

end Normality

end ExtremeValueTheory
