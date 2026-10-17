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

end ARMAX

end ExtremeValueTheory
