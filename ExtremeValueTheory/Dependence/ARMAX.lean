/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MarkovChain
import ExtremeValueTheory.Dependence.ThetaLeVartheta

/-!
# The max-autoregressive (ARMAX) Markov chain

For `0 < φ < 1` and iid Pareto(`α`) innovations `Z_t` (`P(Z > z) = z^(-α)`, `z ≥ 1`), the
*max-autoregressive* chain (ARMAX, [Davis–Resnick 1989], [Alpuim 1989], [EKM, Example 8.1.10],
[KS20, Chapter 14])

  `X_{t+1} = max(φ X_t, Z_{t+1})`

is a Markov chain with transition kernel `K(x, ·) = law of max(φ x, Z)`. It is the random
iteration `RandomIteration.chain (ARMAX.step φ) X₀ V` with innovations `V_n = Z_{n+1}`.

The partial maxima are explicit: for `u ≥ 0`, `max(X_0, …, X_{n-1}) ≤ u` iff `X_0 ≤ u` and
`Z_1, …, Z_{n-1} ≤ u`, so `P(M_n ≤ u) = G(u) F(u)^{n-1}` with `G` the stationary c.d.f. and `F`
the Pareto c.d.f. The stationary law is characterized by the fixed point equation
`G(x) = G(x / φ) F(x)`, which forces the tail `P(X_0 > x) ~ x^(-α) / (1 - φ^α)`. Hence
`n P(X_0 > uₙ) → τ` gives `n F̄(uₙ) → (1 - φ^α) τ`, and the **extremal index is
`θ = 1 - φ^α`**.

## Main results

* `ExtremeValueTheory.ARMAX.forall_iter_le_iff`: the deterministic description of the partial
  maxima.
* `ExtremeValueTheory.ARMAX.tail_le`, `ExtremeValueTheory.ARMAX.le_tail`: any solution `g` of
  the survival-function form of the fixed point equation satisfies
  `C x^(-α) (1 - C x^(-α)) ≤ g(x) ≤ C x^(-α)` for `x ≥ 1`, `C = 1 / (1 - φ^α)`.
* `ExtremeValueTheory.ARMAX.hasExtremalIndex`: **`θ = 1 - φ^α`** for the ARMAX chain started
  from any invariant law (so that the chain is stationary,
  `ExtremeValueTheory.ARMAX.isStationary`).
* `ExtremeValueTheory.ARMAX.isRegularlyVarying_tail`: the stationary marginal is regularly
  varying with index `-α`, `P(X_0 > x) x^α → 1 / (1 - φ^α)`.
* `ExtremeValueTheory.ARMAX.map_stationaryLaw`: **existence** of the invariant law, the law of
  `sup_{j ≥ 0} φ^j Z_{-j}`; `ExtremeValueTheory.ARMAX.hasExtremalIndexStrict_canonical`: the
  canonical stationary ARMAX chain has extremal index `1 - φ^α` in the strict sense of [LLR].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace ExtremeValueTheory

namespace ARMAX

/-- The ARMAX transition `x ↦ max(φ x, z)`. -/
def step (φ : ℝ) (x z : ℝ) : ℝ := max (φ * x) z

variable {φ α : ℝ}

theorem measurable_step : Measurable (Function.uncurry (step φ)) :=
  (measurable_const.mul measurable_fst).max measurable_snd

/-! ### Partial maxima -/

theorem mul_le_of_le (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {u y : ℝ} (hu : 0 ≤ u) (hy : y ≤ u) :
    φ * y ≤ u := by
  rcases le_total 0 y with h | h
  · nlinarith
  · nlinarith

/-- **Partial maxima of the ARMAX recursion**: for `u ≥ 0` and `0 ≤ φ ≤ 1`,
`x_0, …, x_n ≤ u` iff `x_0 ≤ u` and the inputs `v_0, …, v_{n-1} ≤ u`. -/
theorem forall_iter_le_iff (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {u : ℝ} (hu : 0 ≤ u) (x : ℝ)
    (v : ℕ → ℝ) (n : ℕ) :
    (∀ t ≤ n, RandomIteration.iter (step φ) x v t ≤ u) ↔ x ≤ u ∧ ∀ k < n, v k ≤ u := by
  induction n with
  | zero =>
    simp only [nonpos_iff_eq_zero, forall_eq, RandomIteration.iter_zero, not_lt_zero,
      IsEmpty.forall_iff, implies_true, and_true]
  | succ n ih =>
    constructor
    · intro h
      have h1 := (ih.1 fun t ht => h t (by omega))
      refine ⟨h1.1, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1.2 k hk
      · have := h (k + 1) le_rfl
        rw [RandomIteration.iter_succ, step] at this
        exact (le_max_right _ _).trans this
    · rintro ⟨h0, hv⟩ t ht
      have h1 := ih.2 ⟨h0, fun k hk => hv k (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with ht | rfl
      · exact h1 t (by omega)
      · rw [RandomIteration.iter_succ, step]
        exact max_le (mul_le_of_le hφ0 hφ1 hu (h1 n le_rfl)) (hv n (by omega))

/-! ### The fixed point equation and the tail of the stationary law -/

section Analytic

theorem div_rpow_neg {x : ℝ} (hx : 0 ≤ x) (hφ : 0 < φ) :
    (x / φ) ^ (-α) = φ ^ α * x ^ (-α) := by
  rw [Real.div_rpow hx hφ.le, Real.rpow_neg hφ.le, div_inv_eq_mul, mul_comm]

theorem one_le_div (hφ0 : 0 < φ) (hφ1 : φ < 1) {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x / φ := by
  rw [le_div_iff₀ hφ0]; linarith

variable {g : ℝ → ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα : 0 < α) (hg0 : ∀ x, 0 ≤ g x)
  (hrec : ∀ x, 1 ≤ x → g x = g (x / φ) * (1 - x ^ (-α)) + x ^ (-α))
include hφ0 hφ1 hα hg0 hrec


omit hφ0 hφ1 hα hg0 hrec in
theorem sum_range_succ_geom (N : ℕ) :
    ∑ j ∈ range (N + 1), (φ ^ α) ^ j = 1 + φ ^ α * ∑ j ∈ range N, (φ ^ α) ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

omit hα in
theorem tail_le_aux (N : ℕ) : ∀ x, 1 ≤ x →
    g x ≤ g (x / φ ^ N) + x ^ (-α) * ∑ j ∈ range N, (φ ^ α) ^ j := by
  induction N with
  | zero => intro x _; simp
  | succ N ih =>
    intro x hx
    have hxφ := one_le_div hφ0 hφ1 hx
    have h1 := ih (x / φ) hxφ
    have ha : 0 ≤ x ^ (-α) := Real.rpow_nonneg (by linarith) _
    have h2 : g x ≤ g (x / φ) + x ^ (-α) := by
      rw [hrec x hx]
      have := hg0 (x / φ)
      nlinarith
    rw [div_rpow_neg (by linarith) hφ0, div_div, ← pow_succ'] at h1
    rw [sum_range_succ_geom]
    nlinarith

/-- **Upper tail bound**: `g(x) ≤ x^(-α) / (1 - φ^α)` for `x ≥ 1`, provided `g → 0`. -/
theorem tail_le (hlim : Tendsto g atTop (𝓝 0)) {x : ℝ} (hx : 1 ≤ x) :
    g x ≤ (1 - φ ^ α)⁻¹ * x ^ (-α) := by
  have hq0 : 0 ≤ φ ^ α := Real.rpow_nonneg hφ0.le _
  have hq1 : φ ^ α < 1 := Real.rpow_lt_one hφ0.le hφ1 hα
  have hS := (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
  have hpow : Tendsto (fun N : ℕ => x / φ ^ N) atTop atTop := by
    have : Tendsto (fun N : ℕ => (φ⁻¹) ^ N) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hφ0).2 hφ1)
    refine (this.const_mul_atTop (by linarith : (0 : ℝ) < x)).congr fun N => ?_
    rw [inv_pow, div_eq_mul_inv]
  have hT := (hlim.comp hpow).add (hS.const_mul (x ^ (-α)))
  rw [zero_add] at hT
  have := ge_of_tendsto' hT fun N => tail_le_aux hφ0 hφ1 hg0 hrec N x hx
  linarith

omit hφ0 hφ1 in
/-- The trivial lower bound `x^(-α) ≤ g(x)` for `x ≥ 1`. -/
theorem rpow_le_self {x : ℝ} (hx : 1 ≤ x) : x ^ (-α) ≤ g x := by
  rw [hrec x hx]
  have := hg0 (x / φ)
  have : x ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  nlinarith

theorem le_tail_aux (N : ℕ) : ∀ x, 1 ≤ x →
    x ^ (-α) * (1 - (1 - φ ^ α)⁻¹ * x ^ (-α)) * ∑ j ∈ range N, (φ ^ α) ^ j ≤ g x := by
  have hq0 : 0 ≤ φ ^ α := Real.rpow_nonneg hφ0.le _
  have hq1 : φ ^ α < 1 := Real.rpow_lt_one hφ0.le hφ1 hα
  set q := φ ^ α
  set C := (1 - q)⁻¹
  have hC : C * (1 - q) = 1 := inv_mul_cancel₀ (by linarith)
  have hC0 : 0 ≤ C := inv_nonneg.2 (by linarith)
  induction N with
  | zero => intro x _; simpa using hg0 x
  | succ N ih =>
    intro x hx
    have hxφ := one_le_div hφ0 hφ1 hx
    have h1 := ih (x / φ) hxφ
    set a := x ^ (-α)
    have ha : 0 ≤ a := Real.rpow_nonneg (by linarith) _
    have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
    set S := ∑ j ∈ range N, q ^ j
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => pow_nonneg hq0 j
    rw [div_rpow_neg (by linarith) hφ0] at h1
    rw [sum_range_succ_geom, hrec x hx]
    have h2 : q * a * (1 - C * (q * a)) * S * (1 - a) ≤ g (x / φ) * (1 - a) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have key : q * a * (1 - C * (q * a)) * S * (1 - a) + a - a * (1 - C * a) * (1 + q * S) =
        C * a ^ 2 + C * q ^ 2 * S * a ^ 3 := by
      linear_combination (a ^ 2 * q * S) * hC
    have : 0 ≤ C * a ^ 2 + C * q ^ 2 * S * a ^ 3 := by positivity
    nlinarith

/-- **Lower tail bound**: `C x^(-α) (1 - C x^(-α)) ≤ g(x)` for `x ≥ 1`, `C = 1 / (1 - φ^α)`. -/
theorem le_tail {x : ℝ} (hx : 1 ≤ x) :
    (1 - φ ^ α)⁻¹ * x ^ (-α) * (1 - (1 - φ ^ α)⁻¹ * x ^ (-α)) ≤ g x := by
  have hq0 : 0 ≤ φ ^ α := Real.rpow_nonneg hφ0.le _
  have hq1 : φ ^ α < 1 := Real.rpow_lt_one hφ0.le hφ1 hα
  have hS := ((hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat).const_mul
    (x ^ (-α) * (1 - (1 - φ ^ α)⁻¹ * x ^ (-α)))
  have := le_of_tendsto' hS fun N => le_tail_aux hφ0 hφ1 hα hg0 hrec N x hx
  linarith

/-- **Tail asymptotics along level sequences.** If `n g(uₙ) → τ` and `g = 1` below `1`, then
`uₙ ≥ 1` eventually, `uₙ^(-α) → 0` and `n uₙ^(-α) → (1 - φ^α) τ`. -/
theorem tendsto_mul_rpow (hlim : Tendsto g atTop (𝓝 0)) (hone : ∀ x < 1, g x = 1)
    {u : ℕ → ℝ} {τ : ℝ} (hu : Tendsto (fun n : ℕ => n * g (u n)) atTop (𝓝 τ)) :
    (∀ᶠ n in atTop, 1 ≤ u n) ∧ Tendsto (fun n => u n ^ (-α)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => n * u n ^ (-α)) atTop (𝓝 ((1 - φ ^ α) * τ)) := by
  have hq1 : φ ^ α < 1 := Real.rpow_lt_one hφ0.le hφ1 hα
  set C := (1 - φ ^ α)⁻¹
  have hC : C * (1 - φ ^ α) = 1 := inv_mul_cancel₀ (by linarith)
  have hC0 : 0 < C := inv_pos.2 (by linarith)
  have hg := tendsto_zero_of_tendsto_natCast_mul' hu
  have hu1 : ∀ᶠ n in atTop, 1 ≤ u n := by
    filter_upwards [hg.eventually (gt_mem_nhds one_pos)] with n hn
    by_contra h
    rw [hone _ (not_le.1 h)] at hn
    exact lt_irrefl _ hn
  have ha : Tendsto (fun n => u n ^ (-α)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [hu1] with n hn using Real.rpow_nonneg (by linarith) _
    · filter_upwards [hu1] with n hn using rpow_le_self hα hg0 hrec hn
  refine ⟨hu1, ha, ?_⟩
  have hlow : Tendsto (fun n : ℕ => (1 - φ ^ α) * (n * g (u n))) atTop
      (𝓝 ((1 - φ ^ α) * τ)) := hu.const_mul _
  have hup : Tendsto (fun n : ℕ => (1 - φ ^ α) * (n * g (u n)) / (1 - C * u n ^ (-α))) atTop
      (𝓝 ((1 - φ ^ α) * τ)) := by
    have := hlow.div ((ha.const_mul C).const_sub 1) (by simp)
    rw [mul_zero, sub_zero, div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hu1] with n hn
    have h := tail_le hφ0 hφ1 hα hg0 hrec hlim hn
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have : (1 - φ ^ α) * g (u n) ≤ u n ^ (-α) := by
      calc (1 - φ ^ α) * g (u n) ≤ (1 - φ ^ α) * (C * u n ^ (-α)) :=
            mul_le_mul_of_nonneg_left h (by linarith)
        _ = u n ^ (-α) := by rw [← mul_assoc, mul_comm (1 - φ ^ α), hC, one_mul]
    nlinarith
  · filter_upwards [hu1, (ha.const_mul C).eventually (gt_mem_nhds (by norm_num : C * 0 < 1))]
      with n hn hCa
    have h := le_tail hφ0 hφ1 hα hg0 hrec hn
    have hpos : 0 < 1 - C * u n ^ (-α) := by linarith
    rw [le_div_iff₀ hpos]
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have : u n ^ (-α) * (1 - C * u n ^ (-α)) ≤ (1 - φ ^ α) * g (u n) := by
      calc u n ^ (-α) * (1 - C * u n ^ (-α)) =
            (1 - φ ^ α) * (C * u n ^ (-α) * (1 - C * u n ^ (-α))) := by
            rw [← mul_assoc, ← mul_assoc, mul_comm (1 - φ ^ α), hC, one_mul]
        _ ≤ (1 - φ ^ α) * g (u n) := mul_le_mul_of_nonneg_left h (by linarith)
    nlinarith

end Analytic

/-! ### The Pareto c.d.f. and the law of `max(φ Y, Z)` -/

theorem paretoMeasure_real_Iic (hα : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    (paretoMeasure 1 α).real (Iic x) = 1 - x ^ (-α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rw [← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi, paretoMeasure_one_real_Ioi hα hx]

theorem paretoMeasure_Iic_of_lt {x : ℝ} (hx : x < 1) : paretoMeasure 1 α (Iic x) = 0 :=
  measure_mono_null (Iic_subset_Iic.2 hx.le) paretoMeasure_one_Iic_one

/-- The c.d.f. of `max(φ Y, Z)` for independent `Y ~ μ`, `Z ~ ν`. -/
theorem map_step_Iic (hφ : 0 < φ) (μ ν : Measure ℝ) [SFinite ν] (x : ℝ) :
    ((μ.prod ν).map (Function.uncurry (step φ))) (Iic x) = μ (Iic (x / φ)) * ν (Iic x) := by
  rw [Measure.map_apply measurable_step measurableSet_Iic]
  have : Function.uncurry (step φ) ⁻¹' Iic x = Iic (x / φ) ×ˢ Iic x := by
    ext p
    simp only [Set.mem_preimage, Function.uncurry, step, Set.mem_Iic, max_le_iff, mem_prod,
      le_div_iff₀ hφ, mul_comm p.1]
  rw [this, Measure.prod_prod]

/-! ### The stationary ARMAX chain -/

section Chain

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X₀ : Ω → ℝ} {V : ℕ → Ω → ℝ}

/-- The survival function `x ↦ P(X_0 > x)` of the initial law. -/
noncomputable def survival (P : Measure Ω) (X₀ : Ω → ℝ) (x : ℝ) : ℝ := P.real {ω | x < X₀ ω}

theorem survival_eq (hX₀ : Measurable X₀) (x : ℝ) :
    survival P X₀ x = 1 - (P.map X₀).real (Iic x) := by
  rw [survival, map_measureReal_apply hX₀ measurableSet_Iic, ← probReal_compl_eq_one_sub
    (hX₀ measurableSet_Iic)]
  congr 1
  ext ω; simp

theorem tendsto_survival (hX₀ : Measurable X₀) : Tendsto (survival P X₀) atTop (𝓝 0) := by
  have h := (tendsto_cdf_atTop (μ := P.map X₀)).const_sub 1
  rw [sub_self] at h
  refine h.congr fun x => ?_
  rw [survival_eq hX₀, cdf_eq_real]

/-- **The fixed point equation in survival form.** If the law `π` of `X_0` is invariant,
`law(max(φ X_0, Z)) = π` with `Z` Pareto independent of `X_0`, then `g(x) = P(X_0 > x)`
satisfies `g(x) = g(x / φ) (1 - x^(-α)) + x^(-α)` for `x ≥ 1`, and `g(x) = 1` for `x < 1`. -/
theorem survival_rec (hφ0 : 0 < φ) (hα : 0 < α) (hX₀ : Measurable X₀)
    (hinv : ((P.map X₀).prod (paretoMeasure 1 α)).map (Function.uncurry (step φ)) = P.map X₀)
    (x : ℝ) :
    (1 ≤ x → survival P X₀ x = survival P X₀ (x / φ) * (1 - x ^ (-α)) + x ^ (-α)) ∧
      (x < 1 → survival P X₀ x = 1) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have h := map_step_Iic hφ0 (P.map X₀) (paretoMeasure 1 α) x
  rw [hinv] at h
  have hr : (P.map X₀).real (Iic x) =
      (P.map X₀).real (Iic (x / φ)) * (paretoMeasure 1 α).real (Iic x) := by
    simp only [measureReal_def, h, ENNReal.toReal_mul]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [survival_eq hX₀, survival_eq hX₀, hr, paretoMeasure_real_Iic hα hx]
    ring
  · rw [survival_eq hX₀, hr, measureReal_def (μ := paretoMeasure 1 α),
      paretoMeasure_Iic_of_lt hx]
    simp

omit [IsProbabilityMeasure P] in
/-- The probability of `max(X_0, …, X_{n-1}) ≤ u` is `P(X_0 ≤ u) P(Z ≤ u)^(n-1)` for `u ≥ 0`. -/
theorem measureReal_partialMax_le (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hV : ∀ n, Measurable (V n)) (hind : IndepFun X₀ (fun ω n => V n ω) P)
    (hiid : iIndepFun V P) {ν : Measure ℝ} (hlaw : ∀ n, P.map (V n) = ν) {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | partialMax (RandomIteration.chain (step φ) X₀ V) n ω ≤ u} =
      P.real {ω | X₀ ω ≤ u} * ν.real (Iic u) ^ (n - 1) := by
  have hset : {ω | partialMax (RandomIteration.chain (step φ) X₀ V) n ω ≤ u} =
      X₀ ⁻¹' Iic u ∩ (fun ω k => V k ω) ⁻¹' {v | ∀ k ∈ range (n - 1), v k ≤ u} := by
    ext ω
    simp only [Set.mem_ofPred_eq, partialMax_le_iff hn, mem_inter_iff, Set.mem_preimage,
      Set.mem_Iic, Finset.mem_range]
    rw [← forall_iter_le_iff hφ0 hφ1 hu (X₀ ω) (fun k => V k ω) (n - 1)]
    exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
  have hB : MeasurableSet {v : ℕ → ℝ | ∀ k ∈ range (n - 1), v k ≤ u} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_pi_apply k) measurable_const
  rw [hset, measureReal_def, hind.measure_inter_preimage_eq_mul _ _ measurableSet_Iic hB,
    ENNReal.toReal_mul]
  have hprod : P ((fun ω k => V k ω) ⁻¹' {v | ∀ k ∈ range (n - 1), v k ≤ u}) =
      ∏ k ∈ range (n - 1), P (V k ⁻¹' Iic u) := by
    rw [← hiid.measure_inter_preimage_eq_mul _ (fun _ _ => measurableSet_Iic)]
    congr 1
    ext ω; simp
  rw [hprod, ENNReal.toReal_prod]
  have : ∀ k, (P (V k ⁻¹' Iic u)).toReal = ν.real (Iic u) := fun k => by
    rw [← hlaw k, map_measureReal_apply (hV k) measurableSet_Iic]; rfl
  simp only [this, Finset.prod_const, Finset.card_range]
  rfl

variable (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα : 0 < α) (hX₀ : Measurable X₀)
  (hV : ∀ n, Measurable (V n)) (hind : IndepFun X₀ (fun ω n => V n ω) P)
  (hiid : iIndepFun V P) (hlaw : ∀ n, P.map (V n) = paretoMeasure 1 α)
  (hinv : ((P.map X₀).prod (paretoMeasure 1 α)).map (Function.uncurry (step φ)) = P.map X₀)
include hφ0 hφ1 hα hX₀ hV hind hiid hlaw hinv

omit hφ0 hφ1 hα in
/-- **The ARMAX chain started from an invariant law is stationary.** -/
theorem isStationary : IsStationary (RandomIteration.chain (step φ) X₀ V) P :=
  RandomIteration.isStationary_chain measurable_step hX₀ hV hind hiid
    (fun n => ⟨(hV n).aemeasurable, (hV 0).aemeasurable, by rw [hlaw, hlaw]⟩)
    (by rw [hlaw 0]; exact hinv)

/-- **The extremal index of the ARMAX chain is `θ = 1 - φ^α`** [Davis–Resnick 1989],
[EKM, Example 8.1.10]: if `n P(X_0 > uₙ) → τ` then `P(max(X_0, …, X_{n-1}) ≤ uₙ) →
exp(-(1 - φ^α) τ)`. -/
theorem hasExtremalIndex :
    HasExtremalIndex (RandomIteration.chain (step φ) X₀ V) P (1 - φ ^ α) := by
  have hq0 : 0 ≤ φ ^ α := Real.rpow_nonneg hφ0.le _
  have hq1 : φ ^ α < 1 := Real.rpow_lt_one hφ0.le hφ1 hα
  refine ⟨⟨by linarith, by linarith⟩, fun τ hτ u hu => ?_⟩
  have hrec := fun x => survival_rec hφ0 hα hX₀ hinv x
  have hg0 : ∀ x, 0 ≤ survival P X₀ x := fun x => measureReal_nonneg
  have hu' : Tendsto (fun n : ℕ => n * survival P X₀ (u n)) atTop (𝓝 τ) := hu
  obtain ⟨hu1, ha, hna⟩ := tendsto_mul_rpow hφ0 hφ1 hα hg0 (fun x => (hrec x).1)
    (tendsto_survival hX₀) (fun x => (hrec x).2) hu'
  have hg := tendsto_zero_of_tendsto_natCast_mul' hu'
  have hpow : Tendsto (fun n : ℕ => (1 - u n ^ (-α)) ^ (n - 1)) atTop
      (𝓝 (Real.exp (-((1 - φ ^ α) * τ)))) := by
    refine tendsto_one_sub_pow_exp_of_tendsto_mul ha ?_
    have := hna.sub ha
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.cast_sub hn]
    ring
  have hlim := (hg.const_sub 1).mul hpow
  rw [sub_zero, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [hu1, eventually_ge_atTop 1] with n hn1 hn
  rw [measureReal_partialMax_le hφ0.le hφ1.le hV hind hiid hlaw (by omega)
    (by linarith : (0 : ℝ) ≤ u n), paretoMeasure_real_Iic hα hn1, survival]
  congr 1
  rw [← probReal_compl_eq_one_sub (measurableSet_lt measurable_const hX₀)]
  congr 1; ext ω; simp

omit hV hind hiid hlaw in
/-- **The stationary marginal is regularly varying**: `P(X_0 > x) x^α → 1 / (1 - φ^α)`. -/
theorem tendsto_survival_div :
    Tendsto (fun x => survival P X₀ x / x ^ (-α)) atTop (𝓝 (1 - φ ^ α)⁻¹) := by
  have hq1 : φ ^ α < 1 := Real.rpow_lt_one hφ0.le hφ1 hα
  set C := (1 - φ ^ α)⁻¹
  have hrec := fun x => survival_rec hφ0 hα hX₀ hinv x
  have hg0 : ∀ x, 0 ≤ survival P X₀ x := fun x => measureReal_nonneg
  have ha : Tendsto (fun x : ℝ => x ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
  have hlow : Tendsto (fun x : ℝ => C * (1 - C * x ^ (-α))) atTop (𝓝 C) := by
    simpa using ((ha.const_mul C).const_sub 1).const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hapos : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    rw [le_div_iff₀ hapos]
    have := le_tail hφ0 hφ1 hα hg0 (fun x => (hrec x).1) hx
    linarith
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hapos : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    rw [div_le_iff₀ hapos]
    exact tail_le hφ0 hφ1 hα hg0 (fun x => (hrec x).1) (tendsto_survival hX₀) hx

omit hV hind hiid hlaw in
theorem isRegularlyVarying_tail : IsRegularlyVarying (survival P X₀) (-α) :=
  (IsRegularlyVarying.rpow_id (-α)).of_tendsto_div
    (tendsto_survival_div hφ0 hφ1 hα hX₀ hinv)
    (inv_pos.2 (by linarith [Real.rpow_lt_one hφ0.le hφ1 hα]))

/-- **`θ = 1 - φ^α` in the strict sense of [LLR, §3.7]**: exceedance levels exist for every
`τ > 0` since the tail is regularly varying. -/
theorem hasExtremalIndexStrict :
    HasExtremalIndexStrict (RandomIteration.chain (step φ) X₀ V) P (1 - φ ^ α) :=
  ⟨hasExtremalIndex hφ0 hφ1 hα hX₀ hV hind hiid hlaw hinv,
    hasExceedanceLevels_of_isRegularlyVarying hX₀
      (isRegularlyVarying_tail hφ0 hφ1 hα hX₀ hinv)⟩

end Chain

end ARMAX

end ExtremeValueTheory
