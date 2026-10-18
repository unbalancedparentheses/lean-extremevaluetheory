/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ExtremeQuantileSecondOrder

/-!
# Asymptotic normality of the moment estimator, `γ > 0`
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### A central limit theorem for functions of the top exponential excesses -/

section CLT

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [IsProbabilityMeasure P] in
/-- The Rényi representation for `√k ((1/k) ∑_{i<k} g(E_{(i+1)} - E_{(k+1)}) - c)`: for `k < n`
its law is that of `(√k)⁻¹ (∑_{i<k} g(E_i) - k c)`. -/
theorem map_sqrt_mul_meanExcess_fun {E : ℕ → Ω → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P)
    (hind : iIndepFun E P) {g : ℝ → ℝ} (hg : Measurable g) (c : ℝ) {n k : ℕ} (hk : k < n)
    (hk0 : 0 < k) :
    P.map (fun ω => √k * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
        g (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) k) - c)) =
      P.map (fun ω => (√k)⁻¹ * (∑ i ∈ Finset.range k, g (E i ω) - k * c)) := by
  have hmo := measurable_orderStat_pi (n := n) k
  have hT : Measurable fun y : Fin n → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      g (orderStat y i - orderStat y k) - c) :=
    measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      hg.comp ((measurable_orderStat_pi i).sub hmo))).sub measurable_const)
  have hS : Measurable fun z : Fin k → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i, g (z i) - c) :=
    measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      hg.comp (measurable_pi_apply i))).sub measurable_const)
  rw [map_comp_vec_of_iid hE hind (n := n) hT]
  have hR := map_orderStat_excess (n := n) hk (ψ := fun x _ => g x) (hg.comp measurable_fst)
    (h := fun x _ => √k * ((k : ℝ)⁻¹ * x - c)) (by fun_prop)
  simp only at hR
  rw [hR]
  have e1 : (fun p : (Fin n → ℝ) × (Fin k → ℝ) => √k * ((k : ℝ)⁻¹ * ∑ i, g (p.2 i) - c)) =
      (fun z : Fin k → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i, g (z i) - c)) ∘ Prod.snd := rfl
  rw [e1, ← Measure.map_map hS measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  have e2 : (fun ω => (√k)⁻¹ * (∑ i ∈ Finset.range k, g (E i ω) - k * c)) =
      fun ω => (fun z : Fin k → ℝ => √k * ((k : ℝ)⁻¹ * ∑ i, g (z i) - c)) (fun i => E i ω) := by
    funext ω
    beta_reduce
    rw [Fin.sum_univ_eq_sum_range (fun i => g (E i ω)) k]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    have hs0 : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hk').ne'
    field_simp
    rw [Real.sq_sqrt hk'.le]
  rw [e2, map_comp_vec_of_iid hE hind hS]

/-- **Central limit theorem for functions of the top excesses of an exponential sample.** If the
`E_i` are iid standard exponential, `k(n) → ∞`, `k(n) < n` and `g ∈ L²(Exp(1))`, then
`√k ((1/k) ∑_{i<k} g(E_{(i+1)} - E_{(k+1)}) - E g(E_0)) ⇒ N(0, Var g(E_0))`. -/
theorem tendstoInDistribution_meanExcess_fun {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : ∀ᶠ n in atTop, k n < n) {g : ℝ → ℝ} (hg : Measurable g)
    (hg2 : MemLp g 2 (expMeasure 1)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (variance g (expMeasure 1)).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) * (((k n : ℝ))⁻¹ * ∑ i ∈ Finset.range (k n),
        g (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) (k n)) -
        ∫ x, g x ∂(expMeasure 1)))
      atTop Z (fun _ => P) P' := by
  set X : ℕ → Ω → ℝ := fun i ω => g (E i ω) with hXdef
  have hmean : P[X 0] = ∫ x, g x ∂(expMeasure 1) :=
    (hE 0).integral_comp hg.aestronglyMeasurable
  have hvar : Var[X 0; P] = variance g (expMeasure 1) := by
    rw [← (hE 0).map_eq, variance_map hg.aemeasurable (hE 0).aemeasurable]
    rfl
  have hL2 : MemLp (X 0) 2 P := (hE 0).memLp_comp hg2
  have hindX : iIndepFun X P := hind.comp (fun _ x => g x) fun _ => hg
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨hg.comp_aemeasurable (hE i).aemeasurable, hg.comp_aemeasurable (hE 0).aemeasurable, by
      rw [show X i = g ∘ E i from rfl, show X 0 = g ∘ E 0 from rfl,
        ← Measure.map_map hg (hEm i), ← Measure.map_map hg (hEm 0), (hE i).map_eq,
        (hE 0).map_eq]⟩
  have hZ' : HasLaw Z (gaussianReal 0 Var[X 0; P].toNNReal) P' := by rw [hvar]; exact hZ
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ' hL2 hindX hident
  rw [hmean] at hclt
  refine (hclt.comp_tendsto hk).of_map_eq (fun n => ?_) ?_
  · have hv : ∀ i : Fin n, Measurable fun ω => E i ω := fun i => hEm i
    exact (measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      hg.comp ((measurable_orderStat hv i).sub (measurable_orderStat hv (k n))))).sub
      measurable_const)).aemeasurable
  · filter_upwards [hkn, hk.eventually_gt_atTop 0] with n h1 h2
    exact map_sqrt_mul_meanExcess_fun hE hind hg _ h1 h2

end CLT

/-! ### Exponential moments -/

section ExpMoments

theorem integrable_mul_exp_mul_expMeasure {a : ℝ} (ha : a < 1) :
    Integrable (fun u => u * exp (a * u)) (expMeasure 1) := by
  rw [integrable_expMeasure_iff]
  refine (integrableOn_rpow_mul_exp_neg (q := 1) (by norm_num) (sub_pos.2 ha)).congr_fun
    (fun u _ => ?_) measurableSet_Ioi
  beta_reduce
  rw [rpow_one, ← mul_assoc, mul_comm (exp (-u)) u, mul_assoc, ← exp_add]
  congr 2
  ring

theorem integral_mul_exp_mul_expMeasure {a : ℝ} (ha : a < 1) :
    ∫ u, u * exp (a * u) ∂(expMeasure 1) = 1 / (1 - a) ^ 2 := by
  rw [integral_expMeasure]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 - a) two_pos (sub_pos.2 ha)
  rw [Real.Gamma_two, mul_one, Real.rpow_two, div_pow, one_pow] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, ← mul_assoc, mul_comm (exp (-u)) u, mul_assoc,
    ← exp_add]
  congr 2
  ring

theorem integrable_id_expMeasure : Integrable (fun u : ℝ => u) (expMeasure 1) := by
  simpa using integrable_pow_expMeasure 1

/-- `∫_0^∞ u h_ρ(e^u) e^{-u} du = (2 - ρ) / (1 - ρ)²`. -/
theorem integral_mul_boxCox_exp {ρ : ℝ} (hρ : ρ ≤ 0) :
    ∫ u, u * boxCox ρ (exp u) ∂(expMeasure 1) = (2 - ρ) / (1 - ρ) ^ 2 := by
  simp_rw [boxCox_exp]
  split_ifs with h
  · subst h
    rw [show (fun u : ℝ => u * u) = fun u => u ^ 2 by funext u; ring, integral_pow_expMeasure]
    norm_num
  · have hρ1 : ρ < 1 := by linarith
    have e : (fun u => u * ((exp (ρ * u) - 1) / ρ)) = fun u => (u * exp (ρ * u) - u) / ρ := by
      funext u; ring
    rw [e, integral_div, integral_sub (integrable_mul_exp_mul_expMeasure hρ1)
      integrable_id_expMeasure, integral_mul_exp_mul_expMeasure hρ1, integral_id_expMeasure]
    have : (1 : ℝ) - ρ ≠ 0 := by linarith
    field_simp
    ring

/-- The function `g(u) = (γ - 2) u + u² / 2` whose top-excess average drives the moment
estimator. -/
theorem integral_momentScore_expMeasure (γ : ℝ) :
    ∫ u, ((γ - 2) * u + u ^ 2 / 2) ∂(expMeasure 1) = γ - 1 := by
  rw [integral_add (integrable_id_expMeasure.const_mul _)
    ((integrable_pow_expMeasure 2).div_const _), integral_const_mul, integral_div,
    integral_id_expMeasure, integral_pow_expMeasure]
  norm_num
  ring

theorem memLp_momentScore_expMeasure (γ : ℝ) :
    MemLp (fun u => (γ - 2) * u + u ^ 2 / 2) 2 (expMeasure 1) := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  have e : (fun u : ℝ => ((γ - 2) * u + u ^ 2 / 2) ^ 2) =
      fun u => (γ - 2) ^ 2 * u ^ 2 + (γ - 2) * u ^ 3 + 1 / 4 * u ^ 4 := by
    funext u; ring
  rw [e]
  exact (((integrable_pow_expMeasure 2).const_mul _).add
    ((integrable_pow_expMeasure 3).const_mul _)).add ((integrable_pow_expMeasure 4).const_mul _)

theorem variance_momentScore_expMeasure (γ : ℝ) :
    variance (fun u => (γ - 2) * u + u ^ 2 / 2) (expMeasure 1) = 1 + γ ^ 2 := by
  rw [variance_eq_sub (memLp_momentScore_expMeasure γ)]
  have e : ((fun u : ℝ => (γ - 2) * u + u ^ 2 / 2) ^ 2) =
      fun u => (γ - 2) ^ 2 * u ^ 2 + (γ - 2) * u ^ 3 + 1 / 4 * u ^ 4 := by
    funext u; simp only [Pi.pow_apply]; ring
  rw [e]
  beta_reduce
  have i2 : Integrable (fun x : ℝ => (γ - 2) ^ 2 * x ^ 2) (expMeasure 1) :=
    (integrable_pow_expMeasure 2).const_mul _
  have i3 : Integrable (fun x : ℝ => (γ - 2) * x ^ 3) (expMeasure 1) :=
    (integrable_pow_expMeasure 3).const_mul _
  have i4 : Integrable (fun x : ℝ => 1 / 4 * x ^ 4) (expMeasure 1) :=
    (integrable_pow_expMeasure 4).const_mul _
  have i23 : Integrable (fun x : ℝ => (γ - 2) ^ 2 * x ^ 2 + (γ - 2) * x ^ 3) (expMeasure 1) :=
    i2.add i3
  have h2 : ∫ x, (γ - 2) ^ 2 * x ^ 2 ∂(expMeasure 1) = (γ - 2) ^ 2 * 2 := by
    rw [integral_const_mul, integral_pow_expMeasure]; norm_num [Nat.factorial]
  have h3 : ∫ x, (γ - 2) * x ^ 3 ∂(expMeasure 1) = (γ - 2) * 6 := by
    rw [integral_const_mul, integral_pow_expMeasure]; norm_num [Nat.factorial]
  have h4 : ∫ x, 1 / 4 * x ^ 4 ∂(expMeasure 1) = 1 / 4 * 24 := by
    rw [integral_const_mul, integral_pow_expMeasure]; norm_num [Nat.factorial]
  rw [integral_momentScore_expMeasure, integral_add i23 i4, integral_add i2 i3, h2, h3, h4]
  ring

end ExpMoments

/-! ### Localization of the random threshold -/

section Localization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The intermediate exponential order statistic `E_{(k+1)}` tends to infinity in probability. -/
theorem tendsto_measure_orderStat_lt {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) (M : ℝ) :
    Tendsto (fun n => P {ω | orderStat (fun i : Fin n => E i ω) (k n) < M}) atTop (𝓝 0) := by
  have hnk := tendsto_div_atTop_of_tendsto hk hkn
  have hD := tendstoInMeasure_orderStat_sub_log hEm hE hind hk hkn
  have hD1 := (tendstoInMeasure_iff_dist.1 hD) 1 one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD1
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [(tendsto_log_atTop.comp hnk).eventually_ge_atTop (M + 1)] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, Function.comp_apply] at hω hn ⊢
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  linarith

/-- For a measurable auxiliary function `B` of second-order regular variation,
`B(e^{E_{(k+1)}}) / B(n/k) → 1` in probability. -/
theorem tendstoInMeasure_aux_ratio {E : ℕ → Ω → ℝ} (hEm : ∀ i, Measurable (E i))
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P) (hind : iIndepFun E P) {U B : ℝ → ℝ} {γ ρ : ℝ}
    (h2B : IsSecondOrderRegularlyVarying U γ ρ B) (hBm : Measurable B) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => B (exp (orderStat (fun i : Fin n => E i ω) (k n))) /
      B (n / k n)) atTop (fun _ => 1) := by
  have hnk := tendsto_div_atTop_of_tendsto hk hkn
  have hD := tendstoInMeasure_orderStat_sub_log hEm hE hind hk hkn
  have hok := tendsto_measure_orderStat_lt hEm hE hind hk hkn
  obtain ⟨T, hT⟩ := h2B.exists_div_eq_abs_div
  have hBabs : Measurable fun t => |B t| := continuous_abs.measurable.comp hBm
  have hR := tendstoInMeasure_ratio_of_isRegularlyVarying h2B.isRegularlyVarying_abs hBabs hD
    (tendsto_log_atTop.comp hnk)
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

end Localization

end ExtremeValueTheory
