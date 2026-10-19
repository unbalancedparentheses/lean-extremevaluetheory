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

/-! ### Deterministic decomposition -/

section Decomposition

variable {n : ℕ}

/-- The average `(1/k) ∑_{i<k} φ(y_{(i+1)} - y_{(k+1)}, y_{(k+1)})` of a function of the top
excesses and of the threshold. -/
noncomputable def excessMean (φ : ℝ → ℝ → ℝ) (y : Fin n → ℝ) (k : ℕ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, φ (orderStat y i - orderStat y k) (orderStat y k)

theorem excessMean_lin (a b : ℝ) (φ ψ : ℝ → ℝ → ℝ) (y : Fin n → ℝ) (k : ℕ) :
    excessMean (fun u s => a * φ u s + b * ψ u s) y k =
      a * excessMean φ y k + b * excessMean ψ y k := by
  simp only [excessMean, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem measurable_excessMean {φ : ℝ → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) (k : ℕ) :
    Measurable fun y : Fin n → ℝ => excessMean φ y k :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_uncurry_comp hφ
    ((measurable_orderStat_pi i).sub (measurable_orderStat_pi k)) (measurable_orderStat_pi k))

theorem measurable_logMoment_pi (k j : ℕ) : Measurable fun y : Fin n → ℝ => logMoment y k j :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    ((measurable_orderStat_pi i).log.sub (measurable_orderStat_pi k).log).pow_const j)

theorem measurable_momentEstimator_pi (k : ℕ) :
    Measurable fun y : Fin n → ℝ => momentEstimator y k := by
  unfold momentEstimator
  have h1 := measurable_logMoment_pi (n := n) k 1
  have h2 := measurable_logMoment_pi (n := n) k 2
  fun_prop

/-- The log-moments of the sample `U(e^{y_i})`, for `U` monotone on `(1, ∞)` and `y_i > 0`, in
terms of the top excesses of `y` and the second-order remainder. -/
theorem logMoment_comp_exp_eq {U : ℝ → ℝ} (hU : MonotoneOn U (Ioi 1)) (γ : ℝ) {y : Fin n → ℝ}
    (hy : ∀ i, 0 < y i) {k : ℕ} (hk : k < n) (j : ℕ) :
    logMoment (fun i => U (exp (y i))) k j =
      excessMean (fun u s => (γ * u + logRemainder U γ u s) ^ j) y k := by
  have hmono : MonotoneOn (fun x => U (exp x)) (Ioi 0) := fun a ha b hb hab =>
    hU (one_lt_exp_iff.2 ha) (one_lt_exp_iff.2 hb) (exp_le_exp.2 hab)
  have h := fun m (hm : m < n) => orderStat_comp_monotoneOn hmono (y := y) (fun i => hy i) hm
  simp only [Function.comp_def] at h
  unfold logMoment excessMean
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := (Finset.mem_range.1 hi).trans hk
  beta_reduce
  rw [h i hi', h k hk]
  simp only [logRemainder]
  rw [← exp_add, sub_add_cancel]
  congr 1
  ring

/-- The algebraic expansion of the moment estimator around `(γ, 2γ²)`. -/
theorem momentEstimator_expansion {γ r M₁ M₂ : ℝ} (hγ : γ ≠ 0) (h2 : M₂ ≠ 0)
    (hD : M₂ - M₁ ^ 2 ≠ 0) :
    r * (M₁ + 1 - 1 / 2 * (1 - M₁ ^ 2 / M₂)⁻¹ - γ) =
      (1 - 2 / γ) * (r * (M₁ - γ)) + r * (M₂ - 2 * γ ^ 2) / (2 * γ ^ 2) +
        r * (M₁ - γ) * (2 / γ - (M₁ + γ) / (M₂ - M₁ ^ 2)) +
        r * (M₂ - 2 * γ ^ 2) * (1 / (2 * (M₂ - M₁ ^ 2)) - 1 / (2 * γ ^ 2)) := by
  have e : 1 - M₁ ^ 2 / M₂ = (M₂ - M₁ ^ 2) / M₂ := by field_simp
  rw [e, inv_div]
  field_simp
  ring

end Decomposition

/-! ### Convergence in probability: arithmetic with prescribed limits -/

section Arith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} {l : Filter ι}

theorem TendstoInMeasure.add' {f g : ι → Ω → ℝ} {a b c : ℝ}
    (hf : TendstoInMeasure P f l (fun _ => a)) (hg : TendstoInMeasure P g l (fun _ => b))
    (h : a + b = c) : TendstoInMeasure P (fun i ω => f i ω + g i ω) l (fun _ => c) :=
  h ▸ tendstoInMeasure_comp₂ hf hg (φ := fun p => p.1 + p.2) continuous_add.continuousAt

theorem TendstoInMeasure.mul' {f g : ι → Ω → ℝ} {a b c : ℝ}
    (hf : TendstoInMeasure P f l (fun _ => a)) (hg : TendstoInMeasure P g l (fun _ => b))
    (h : a * b = c) : TendstoInMeasure P (fun i ω => f i ω * g i ω) l (fun _ => c) :=
  h ▸ tendstoInMeasure_mul hf hg

theorem TendstoInMeasure.const_mul' {f : ι → Ω → ℝ} {a : ℝ} (c : ℝ)
    (hf : TendstoInMeasure P f l (fun _ => a)) :
    TendstoInMeasure P (fun i ω => c * f i ω) l (fun _ => c * a) :=
  tendstoInMeasure_comp hf (φ := fun x => c * x) (continuous_const.mul continuous_id).continuousAt

theorem TendstoInMeasure.comp₂' {f g : ι → Ω → ℝ} {a b c : ℝ}
    (hf : TendstoInMeasure P f l (fun _ => a)) (hg : TendstoInMeasure P g l (fun _ => b))
    {φ : ℝ × ℝ → ℝ} (hφ : ContinuousAt φ (a, b)) (h : φ (a, b) = c) :
    TendstoInMeasure P (fun i ω => φ (f i ω, g i ω)) l (fun _ => c) :=
  h ▸ tendstoInMeasure_comp₂ hf hg hφ

end Arith

/-! ### Asymptotic normality on the exponential scale -/

section General

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

theorem le_four_mul_exp_div_four {u : ℝ} : u ≤ 4 * exp (u / 4) := by
  linarith [add_one_le_exp (u / 4)]

theorem le_eight_mul_exp_div_eight {u : ℝ} : u ≤ 8 * exp (u / 8) := by
  linarith [add_one_le_exp (u / 8)]

/-- The asymptotic bias of the moment estimator, `γ > 0`. -/
noncomputable def momentBias (γ ρ : ℝ) : ℝ := (γ - γ * ρ + ρ) / (γ * (1 - ρ) ^ 2)

/-- **Asymptotic normality of the moment estimator on the exponential scale**, `γ > 0`. -/
theorem tendstoInDistribution_momentEstimator_comp_exp {E : ℕ → Ω → ℝ}
    (hEm : ∀ i, Measurable (E i)) (hE : ∀ i, HasLaw (E i) (expMeasure 1) P)
    (hind : iIndepFun E P)
    {U A : ℝ → ℝ} {γ ρ lam : ℝ} (hγ : 0 < γ) (hU : Measurable U) (hUm : MonotoneOn U (Ioi 1))
    (h2 : IsSecondOrderRegularlyVarying U γ ρ A) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal (lam * momentBias γ ρ) (1 + γ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun n ω =>
        √(k n : ℝ) * (momentEstimator (fun i : Fin n => U (exp (E i ω))) (k n) - γ))
      atTop Z (fun _ => P) P' := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hρ := h2.nonpos
  have hρ1 : (1 : ℝ) - ρ ≠ 0 := by linarith
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
  have hok := tendsto_measure_orderStat_lt hEm hE hind hk hkn
  have hmo : ∀ n j, Measurable fun ω => orderStat (fun i : Fin n => E i ω) j := fun n j =>
    measurable_orderStat (fun i => hEm i) j
  have hvec : ∀ n, Measurable fun ω (i : Fin n) => E i ω := fun n =>
    measurable_pi_iff.2 fun i => hEm i
  have hEMm : ∀ {φ : ℝ → ℝ → ℝ}, Measurable (Function.uncurry φ) → ∀ n,
      Measurable fun ω => excessMean φ (fun i : Fin n => E i ω) (k n) := fun hφ n =>
    (measurable_excessMean hφ (k n)).comp (hvec n)
  -- the normalized remainder and its bounds
  obtain ⟨C, t₀, ht₀, hbd⟩ := h2B.exists_bound hU hBm (δ := 1 / 8) (by norm_num)
  set φ : ℝ → ℝ → ℝ := fun u s => logRemainder U γ u s / B (exp s) with hφ
  have hRm : Measurable (Function.uncurry (logRemainder U γ)) := by
    unfold logRemainder
    exact ((hU.comp ((measurable_exp.comp measurable_fst).mul
      (measurable_exp.comp measurable_snd))).log.sub (hU.comp
      (measurable_exp.comp measurable_snd)).log).sub (measurable_fst.const_mul γ)
  have hφm : Measurable (Function.uncurry φ) :=
    hRm.div (hBm.comp (measurable_exp.comp measurable_snd))
  have hdom8 : ∀ s ≥ log t₀, ∀ u ≥ 0, |φ u s| ≤ |C| * exp (u / 8) := by
    intro s hs u hu
    have hts : t₀ ≤ exp s := (log_le_iff_le_exp ht₀).1 hs
    have h1 := hbd (exp s) hts (exp u) (one_le_exp hu)
    rw [log_exp, rpow_def_of_pos (exp_pos u), log_exp] at h1
    have e : logRemainder U γ u s = log (U (exp u * exp s)) - log (U (exp s)) - γ * u := rfl
    simp only [hφ, abs_div]
    rcases eq_or_ne (B (exp s)) 0 with h0 | h0
    · simp [h0]; positivity
    rw [div_le_iff₀ (abs_pos.2 h0), e]
    calc _ ≤ C * |B (exp s)| * exp (u * (1 / 8)) := h1
      _ ≤ |C| * |B (exp s)| * exp (u * (1 / 8)) := by gcongr; exact le_abs_self C
      _ = |C| * exp (u / 8) * |B (exp s)| := by ring_nf
  have hdom1 : ∀ s ≥ log t₀, ∀ u ≥ 0, |φ u s| ≤ |C| * exp (u / 4) := by
    intro s hs u hu
    refine (hdom8 s hs u hu).trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith))
      (abs_nonneg _))
  have hdom2 : ∀ s ≥ log t₀, ∀ u ≥ 0, |u * φ u s| ≤ (8 * |C|) * exp (u / 4) := by
    intro s hs u hu
    rw [abs_mul, abs_of_nonneg hu]
    have h8 := hdom8 s hs u hu
    have hu8 : u ≤ 8 * exp (u / 8) := le_eight_mul_exp_div_eight
    calc u * |φ u s| ≤ (8 * exp (u / 8)) * (|C| * exp (u / 8)) :=
          mul_le_mul hu8 h8 (abs_nonneg _) (by positivity)
      _ = 8 * |C| * (exp (u / 8) * exp (u / 8)) := by ring
      _ = 8 * |C| * exp (u / 4) := by rw [← exp_add]; ring_nf
  have hdom3 : ∀ s ≥ log t₀, ∀ u ≥ 0, |φ u s ^ 2| ≤ |C| ^ 2 * exp (u / 4) := by
    intro s hs u hu
    have h8 := hdom8 s hs u hu
    rw [abs_pow]
    calc |φ u s| ^ 2 ≤ (|C| * exp (u / 8)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h8 2
      _ = |C| ^ 2 * exp (u / 4) := by rw [mul_pow, ← exp_nat_mul]; ring_nf
  have hlimφ : ∀ u ≥ (0 : ℝ), Tendsto (fun s => φ u s) atTop (𝓝 (boxCox ρ (exp u))) := by
    intro u _
    refine ((h2B.tendsto_log (exp_pos u)).comp tendsto_exp_atTop).congr fun s => ?_
    simp only [Function.comp_apply, hφ, logRemainder, log_exp]
  -- conditional laws of large numbers
  have hW1 : TendstoInMeasure P (fun n ω => excessMean φ (fun i : Fin n => E i ω) (k n)) atTop
      (fun _ => 1 / (1 - ρ)) := by
    have h := tendstoInMeasure_meanExcess_fun hEm hE hind hk hkn' hok hφm hdom1 hlimφ
    rwa [integral_boxCox_exp hρ] at h
  have hW2 : TendstoInMeasure P (fun n ω => excessMean (fun u s => u * φ u s)
      (fun i : Fin n => E i ω) (k n)) atTop (fun _ => (2 - ρ) / (1 - ρ) ^ 2) := by
    have h := tendstoInMeasure_meanExcess_fun hEm hE hind hk hkn' hok
      (φ := fun u s => u * φ u s) (measurable_fst.mul hφm) hdom2
      (fun u hu => (hlimφ u hu).const_mul u)
    rwa [integral_mul_boxCox_exp hρ] at h
  have hW3 : TendstoInMeasure P (fun n ω => excessMean (fun u s => φ u s ^ 2)
      (fun i : Fin n => E i ω) (k n)) atTop
      (fun _ => ∫ u, boxCox ρ (exp u) ^ 2 ∂(expMeasure 1)) :=
    tendstoInMeasure_meanExcess_fun hEm hE hind hk hkn' hok
      (φ := fun u s => φ u s ^ 2) (hφm.pow_const 2) hdom3 (fun u hu => (hlimφ u hu).pow 2)
  -- the ratio and the threshold
  have hQ := tendstoInMeasure_aux_ratio hEm hE hind h2B hBm hk hkn
  have hBnk : Tendsto (fun n => B (n / k n)) atTop (𝓝 0) := h2B.tendsto_zero.comp hnk
  have hBne : ∀ᶠ n in atTop, B (n / k n) ≠ 0 := hnk.eventually h2B.eventually_ne_zero
  have hV : TendstoInMeasure P (fun n ω => √(k n : ℝ) *
      B (exp (orderStat (fun i : Fin n => E i ω) (k n)))) atTop (fun _ => lam) := by
    have h := TendstoInMeasure.mul' (tendstoInMeasure_const_of_tendsto (P := P) hlamB) hQ
      (mul_one lam)
    refine tendstoInMeasure_of_eventuallyEq h ?_
    filter_upwards [hBne] with n hn ω
    field_simp
  have hBs : TendstoInMeasure P (fun n ω =>
      B (exp (orderStat (fun i : Fin n => E i ω) (k n)))) atTop (fun _ => 0) := by
    have h := TendstoInMeasure.mul' (tendstoInMeasure_const_of_tendsto (P := P) hBnk) hQ
      (zero_mul 1)
    refine tendstoInMeasure_of_eventuallyEq h ?_
    filter_upwards [hBne] with n hn ω
    field_simp
  -- the first two moments of the top excesses
  have hm1 : TendstoInMeasure P (fun n ω => excessMean (fun u _ => u) (fun i : Fin n => E i ω)
      (k n)) atTop (fun _ => 1) := by
    have h := tendstoInMeasure_meanExcess_fun hEm hE hind hk hkn' hok (φ := fun u _ => u)
      (H := fun u => u) measurable_fst (C := 4) (s₀ := 0)
      (fun s _ u hu => by rw [abs_of_nonneg hu]; exact le_four_mul_exp_div_four)
      (fun u _ => tendsto_const_nhds)
    rwa [integral_id_expMeasure] at h
  have hm2 : TendstoInMeasure P (fun n ω => excessMean (fun u _ => u ^ 2)
      (fun i : Fin n => E i ω) (k n)) atTop (fun _ => 2) := by
    have h := tendstoInMeasure_meanExcess_fun hEm hE hind hk hkn' hok (φ := fun u _ => u ^ 2)
      (H := fun u => u ^ 2) (measurable_fst.pow_const 2) (C := 64) (s₀ := 0)
      (fun s _ u hu => by
        rw [abs_of_nonneg (sq_nonneg u)]
        have h8 : u ≤ 8 * exp (u / 8) := le_eight_mul_exp_div_eight
        calc u ^ 2 ≤ (8 * exp (u / 8)) ^ 2 := pow_le_pow_left₀ hu h8 2
          _ = 64 * exp (u / 4) := by rw [mul_pow, ← exp_nat_mul]; ring_nf)
      (fun u _ => tendsto_const_nhds)
    have e : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [integral_pow_expMeasure, e] at h
    exact h
  -- tightness of the centred moments, and the central limit theorem
  have hS1 : IsBoundedInProbability P (fun n ω => √(k n : ℝ) *
      (excessMean (fun u _ => u) (fun i : Fin n => E i ω) (k n) - 1)) := by
    have h := tendstoInDistribution_meanExcess_fun hEm hE hind hk hkn' (g := fun x => x)
      measurable_id memLp_two_id_expMeasure (P' := gaussianReal 0 _) HasLaw.id
    rw [integral_id_expMeasure] at h
    exact isBoundedInProbability_of_tendstoInDistribution h
  have hS2 : IsBoundedInProbability P (fun n ω => √(k n : ℝ) *
      (excessMean (fun u _ => u ^ 2) (fun i : Fin n => E i ω) (k n) - 2)) := by
    have hL2 : MemLp (fun x : ℝ => x ^ 2) 2 (expMeasure 1) := by
      refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
      simpa [← pow_mul] using integrable_pow_expMeasure 4
    have h := tendstoInDistribution_meanExcess_fun hEm hE hind hk hkn' (g := fun x => x ^ 2)
      (measurable_id.pow_const 2) hL2 (P' := gaussianReal 0 _) HasLaw.id
    have e : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [integral_pow_expMeasure, e] at h
    exact isBoundedInProbability_of_tendstoInDistribution h
  set μ := lam * momentBias γ ρ with hμ
  have hZ' : HasLaw (fun ω => Z ω - μ) (gaussianReal 0
      (variance (fun u => (γ - 2) * u + u ^ 2 / 2) (expMeasure 1)).toNNReal) P' := by
    rw [variance_momentScore_expMeasure]
    have := gaussianReal_sub_const hZ μ
    rwa [sub_self] at this
  have hG := tendstoInDistribution_meanExcess_fun hEm hE hind hk hkn'
    (by fun_prop) (memLp_momentScore_expMeasure γ) hZ'
  rw [integral_momentScore_expMeasure] at hG
  -- notation
  set Bs : ℕ → Ω → ℝ := fun n ω => B (exp (orderStat (fun i : Fin n => E i ω) (k n)))
    with hBsdef
  set m1 : ℕ → Ω → ℝ := fun n ω => excessMean (fun u _ => u) (fun i : Fin n => E i ω) (k n)
    with hm1def
  set m2 : ℕ → Ω → ℝ := fun n ω => excessMean (fun u _ => u ^ 2) (fun i : Fin n => E i ω) (k n)
    with hm2def
  set W1 : ℕ → Ω → ℝ := fun n ω => excessMean φ (fun i : Fin n => E i ω) (k n) with hW1def
  set W2 : ℕ → Ω → ℝ := fun n ω => excessMean (fun u s => u * φ u s) (fun i : Fin n => E i ω)
    (k n) with hW2def
  set W3 : ℕ → Ω → ℝ := fun n ω => excessMean (fun u s => φ u s ^ 2) (fun i : Fin n => E i ω)
    (k n) with hW3def
  set c3 := ∫ u, boxCox ρ (exp u) ^ 2 ∂(expMeasure 1) with hc3
  have hBsm : ∀ n, Measurable (Bs n) := fun n => hBm.comp (measurable_exp.comp (hmo n (k n)))
  have hm1m : ∀ n, Measurable (m1 n) := hEMm measurable_fst
  have hm2m : ∀ n, Measurable (m2 n) := hEMm (measurable_fst.pow_const 2)
  have hW1m : ∀ n, Measurable (W1 n) := hEMm hφm
  have hW2m : ∀ n, Measurable (W2 n) := hEMm (measurable_fst.mul hφm)
  have hW3m : ∀ n, Measurable (W3 n) := hEMm (hφm.pow_const 2)
  -- the log-moments, in terms of the averages
  set M1 : ℕ → Ω → ℝ := fun n ω => γ * m1 n ω + Bs n ω * W1 n ω with hM1def
  set M2 : ℕ → Ω → ℝ := fun n ω => γ ^ 2 * m2 n ω + 2 * γ * Bs n ω * W2 n ω +
    Bs n ω * Bs n ω * W3 n ω with hM2def
  have hM1 : TendstoInMeasure P M1 atTop (fun _ => γ) :=
    TendstoInMeasure.add' (TendstoInMeasure.const_mul' γ hm1) (TendstoInMeasure.mul' hBs hW1 (zero_mul _))
      (by ring)
  have hM2 : TendstoInMeasure P M2 atTop (fun _ => 2 * γ ^ 2) :=
    TendstoInMeasure.add' (TendstoInMeasure.add' (TendstoInMeasure.const_mul' (γ ^ 2) hm2)
      (TendstoInMeasure.mul' (TendstoInMeasure.const_mul' (2 * γ) hBs) hW2 rfl) rfl)
      (TendstoInMeasure.mul' (TendstoInMeasure.mul' hBs hBs rfl) hW3 rfl) (by ring)
  have hγ2 : (2 * γ ^ 2 - γ ^ 2) ≠ 0 := by
    rw [show 2 * γ ^ 2 - γ ^ 2 = γ ^ 2 by ring]; positivity
  have hDm : TendstoInMeasure P (fun n ω => M2 n ω - M1 n ω ^ 2) atTop (fun _ => γ ^ 2) :=
    TendstoInMeasure.comp₂' hM1 hM2 (φ := fun p => p.2 - p.1 ^ 2) (by fun_prop) (by ring)
  have hc : TendstoInMeasure P (fun n ω => 2 / γ - (M1 n ω + γ) / (M2 n ω - M1 n ω ^ 2)) atTop
      (fun _ => 0) :=
    TendstoInMeasure.comp₂' hM1 hM2 (φ := fun p => 2 / γ - (p.1 + γ) / (p.2 - p.1 ^ 2))
      (continuousAt_const.sub (ContinuousAt.div (by fun_prop) (by fun_prop) hγ2))
      (by field_simp; ring)
  have hd : TendstoInMeasure P (fun n ω => 1 / (2 * (M2 n ω - M1 n ω ^ 2)) - 1 / (2 * γ ^ 2))
      atTop (fun _ => 0) :=
    TendstoInMeasure.comp₂' hM1 hM2 (φ := fun p => 1 / (2 * (p.2 - p.1 ^ 2)) - 1 / (2 * γ ^ 2))
      ((ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hγ2)).sub
        continuousAt_const)
      (by field_simp; ring)
  -- the bias and the negligible terms
  have hVW1 := TendstoInMeasure.mul' hV hW1 rfl
  have hVW2 := TendstoInMeasure.mul' hV hW2 rfl
  have hVBW3 := TendstoInMeasure.mul' (TendstoInMeasure.mul' hV hBs rfl) hW3 rfl
  have hbias : TendstoInMeasure P (fun n ω => (1 - 2 / γ) * (√(k n : ℝ) * Bs n ω * W1 n ω) +
      1 / γ * (√(k n : ℝ) * Bs n ω * W2 n ω) +
      1 / (2 * γ ^ 2) * (√(k n : ℝ) * Bs n ω * Bs n ω * W3 n ω)) atTop (fun _ => μ) :=
    TendstoInMeasure.add' (TendstoInMeasure.add' (TendstoInMeasure.const_mul' _ hVW1) (TendstoInMeasure.const_mul' _ hVW2) rfl)
      (TendstoInMeasure.const_mul' _ hVBW3) (by simp only [hμ, momentBias]; field_simp; ring)
  have hac : TendstoInMeasure P (fun n ω => (γ * (√(k n : ℝ) * (m1 n ω - 1)) +
      √(k n : ℝ) * Bs n ω * W1 n ω) * (2 / γ - (M1 n ω + γ) / (M2 n ω - M1 n ω ^ 2))) atTop
      (fun _ => 0) := by
    have h1 := TendstoInMeasure.const_mul' γ
      (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS1 hc)
    have h2 := TendstoInMeasure.mul' hVW1 hc rfl
    refine tendstoInMeasure_of_eventuallyEq (TendstoInMeasure.add' h1 h2 (by ring))
      (Eventually.of_forall fun n ω => ?_)
    ring
  have hbd : TendstoInMeasure P (fun n ω => (γ ^ 2 * (√(k n : ℝ) * (m2 n ω - 2)) +
      2 * γ * (√(k n : ℝ) * Bs n ω * W2 n ω) + √(k n : ℝ) * Bs n ω * Bs n ω * W3 n ω) *
      (1 / (2 * (M2 n ω - M1 n ω ^ 2)) - 1 / (2 * γ ^ 2))) atTop (fun _ => 0) := by
    have h1 := TendstoInMeasure.const_mul' (γ ^ 2)
      (tendstoInMeasure_mul_zero_of_isBoundedInProbability' hS2 hd)
    have h2 := TendstoInMeasure.mul' (TendstoInMeasure.add' (TendstoInMeasure.const_mul' (2 * γ) hVW2) hVBW3 rfl)
      hd rfl
    refine tendstoInMeasure_of_eventuallyEq (TendstoInMeasure.add' h1 h2 (by ring))
      (Eventually.of_forall fun n ω => ?_)
    ring
  set R : ℕ → Ω → ℝ := fun n ω => ((1 - 2 / γ) * (√(k n : ℝ) * Bs n ω * W1 n ω) +
      1 / γ * (√(k n : ℝ) * Bs n ω * W2 n ω) +
      1 / (2 * γ ^ 2) * (√(k n : ℝ) * Bs n ω * Bs n ω * W3 n ω)) +
      (γ * (√(k n : ℝ) * (m1 n ω - 1)) + √(k n : ℝ) * Bs n ω * W1 n ω) *
        (2 / γ - (M1 n ω + γ) / (M2 n ω - M1 n ω ^ 2)) +
      (γ ^ 2 * (√(k n : ℝ) * (m2 n ω - 2)) +
        2 * γ * (√(k n : ℝ) * Bs n ω * W2 n ω) + √(k n : ℝ) * Bs n ω * Bs n ω * W3 n ω) *
        (1 / (2 * (M2 n ω - M1 n ω ^ 2)) - 1 / (2 * γ ^ 2)) with hRdef
  have hR : TendstoInMeasure P R atTop (fun _ => μ) :=
    TendstoInMeasure.add' (TendstoInMeasure.add' hbias hac (add_zero μ)) hbd (add_zero μ)
  have hRm : ∀ n, AEMeasurable (R n) P := by
    intro n
    have := hBsm n; have := hm1m n; have := hm2m n; have := hW1m n; have := hW2m n
    have := hW3m n
    simp only [hRdef, hM1def, hM2def]
    fun_prop
  -- Slutsky
  have hF := hG.add_of_tendstoInMeasure_const hR hRm
  have hF' := hF.congr_limit hZ.aemeasurable (by congr 1; funext ω; ring)
  have hTm : ∀ n, AEMeasurable (fun ω =>
      √(k n : ℝ) * (momentEstimator (fun i : Fin n => U (exp (E i ω))) (k n) - γ)) P := fun n =>
    (measurable_const.mul (((measurable_momentEstimator_pi (k n)).comp (measurable_pi_iff.2
      fun i => hU.comp (measurable_exp.comp (hEm i)))).sub_const _)).aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hF' ?_ hTm
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
  obtain ⟨T₀, hT₀⟩ := h2B.exists_div_eq_abs_div
  have hγ2pos : 0 < γ ^ 2 := by positivity
  have h3 := (tendstoInMeasure_iff_dist.1 hDm) (γ ^ 2 / 2) (by positivity)
  have h4 := (tendstoInMeasure_iff_dist.1 hM2) (γ ^ 2) hγ2pos
  have hsum := ((tendsto_const_nhds (x := (0 : ℝ≥0∞))).add (hok (log (max T₀ 1)))).add h3
    |>.add h4
  simp only [add_zero] at hsum
  refine hzero.congr_of_measure_ne ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hkn', hk.eventually_gt_atTop 0] with n hkn hk0
  refine (measure_mono (t := (({ω | ∃ i : Fin n, E i ω ≤ 0} ∪
      {ω | orderStat (fun i : Fin n => E i ω) (k n) < log (max T₀ 1)}) ∪
      {ω | γ ^ 2 / 2 ≤ dist (M2 n ω - M1 n ω ^ 2) (γ ^ 2)}) ∪
      {ω | γ ^ 2 ≤ dist (M2 n ω) (2 * γ ^ 2)}) ?_).trans ?_
  swap
  · refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (by rw [hnull n])) le_rfl)) le_rfl)
  intro ω hω
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨⟨hpos, hok'⟩, hd3⟩, hd4⟩ := hcon
  apply hω
  have hT1' : max T₀ 1 ≤ exp (orderStat (fun i : Fin n => E i ω) (k n)) :=
    (log_le_iff_le_exp (lt_of_lt_of_le one_pos (le_max_right T₀ 1))).1 hok'
  have hb1 : Bs n ω ≠ 0 := (hT₀ _ ((le_max_left _ _).trans hT1')).1
  rw [Real.dist_eq, abs_lt] at hd3 hd4
  have hM2ne : M2 n ω ≠ 0 := by linarith [hd4.1]
  have hDne : M2 n ω - M1 n ω ^ 2 ≠ 0 := by linarith [hd3.1]
  -- the log-moments
  have hy : ∀ i : Fin n, 0 < E i ω := hpos
  have hlm : ∀ j, logMoment (fun i : Fin n => U (exp (E i ω))) (k n) j =
      excessMean (fun u _ => (γ * u + Bs n ω * φ u
        (orderStat (fun i : Fin n => E i ω) (k n))) ^ j) (fun i : Fin n => E i ω) (k n) := by
    intro j
    rw [logMoment_comp_exp_eq hUm γ (y := fun i : Fin n => E i ω) hy hkn j]
    simp only [excessMean]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hφ, hBsdef] at hb1 ⊢
    field_simp
  have hlm1 : logMoment (fun i : Fin n => U (exp (E i ω))) (k n) 1 = M1 n ω := by
    rw [hlm]
    simp only [hM1def, hm1def, hW1def, excessMean, pow_one, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  have hlm2 : logMoment (fun i : Fin n => U (exp (E i ω))) (k n) 2 = M2 n ω := by
    rw [hlm]
    simp only [hM2def, hm2def, hW2def, hW3def, excessMean]
    rw [show ∀ x : ℕ → ℝ, ∀ y : ℕ → ℝ, ∀ m : ℕ,
        (∑ i ∈ Finset.range m, (γ * x i + Bs n ω * y i) ^ 2) =
        γ ^ 2 * ∑ i ∈ Finset.range m, x i ^ 2 + 2 * γ * Bs n ω * ∑ i ∈ Finset.range m,
          x i * y i + Bs n ω * Bs n ω * ∑ i ∈ Finset.range m, y i ^ 2 by
      intro x y m
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  have hgm : excessMean (fun u _ => (γ - 2) * u + u ^ 2 / 2) (fun i : Fin n => E i ω) (k n) =
      (γ - 2) * m1 n ω + 1 / 2 * m2 n ω := by
    rw [show (fun u (_ : ℝ) => (γ - 2) * u + u ^ 2 / 2) =
      fun u s => (γ - 2) * (fun u (_ : ℝ) => u) u s + 1 / 2 * (fun u (_ : ℝ) => u ^ 2) u s by
        funext u s; ring]
    exact excessMean_lin _ _ _ _ _ _
  have hgm' : ((k n : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (k n),
      ((γ - 2) * (orderStat (fun i : Fin n => E i ω) i - orderStat (fun i : Fin n => E i ω) (k n))
        + (orderStat (fun i : Fin n => E i ω) i -
          orderStat (fun i : Fin n => E i ω) (k n)) ^ 2 / 2) =
      (γ - 2) * m1 n ω + 1 / 2 * m2 n ω := hgm
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [sub_eq_zero]
  unfold momentEstimator
  rw [hlm1, hlm2, momentEstimator_expansion hγ0 hM2ne hDne, hgm']
  have e1 : M1 n ω = γ * m1 n ω + Bs n ω * W1 n ω := rfl
  have e2 : M2 n ω = γ ^ 2 * m2 n ω + 2 * γ * Bs n ω * W2 n ω + Bs n ω * Bs n ω * W3 n ω := rfl
  simp only [hRdef]
  linear_combination (norm := skip) (√(k n : ℝ) * ((1 - 2 / γ) +
      (2 / γ - (M1 n ω + γ) / (M2 n ω - M1 n ω ^ 2)))) * e1 +
    (√(k n : ℝ) * (1 / (2 * γ ^ 2) +
      (1 / (2 * (M2 n ω - M1 n ω ^ 2)) - 1 / (2 * γ ^ 2)))) * e2
  field_simp
  ring

end General

end ExtremeValueTheory
