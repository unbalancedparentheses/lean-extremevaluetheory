/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MarkovChain
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Stochastic recurrence equations

skeleton
-/

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace ExtremeValueTheory

namespace SRE

/-- The affine map `x ↦ a x + b` of the stochastic recurrence `X_t = A_t X_{t-1} + B_t`. -/
def affine (x : ℝ) (p : ℝ × ℝ) : ℝ := p.1 * x + p.2

/-- The `k`-th term `A_0 ⋯ A_{k-1} B_k` of the perpetuity. -/
def term (v : ℕ → ℝ × ℝ) (k : ℕ) : ℝ := (∏ i ∈ Finset.range k, (v i).1) * (v k).2

/-- The **perpetuity** `∑_{k ≥ 0} A_0 ⋯ A_{k-1} B_k`. -/
noncomputable def perpetuity (v : ℕ → ℝ × ℝ) : ℝ := ∑' k, term v k

theorem measurable_affine : Measurable (Function.uncurry affine) := by
  unfold affine Function.uncurry; fun_prop

theorem measurable_term (k : ℕ) : Measurable fun v : ℕ → ℝ × ℝ => term v k := by
  unfold term
  refine (Finset.measurable_prod _ fun i _ => ?_).mul ?_
  · exact measurable_fst.comp (measurable_pi_apply i)
  · exact measurable_snd.comp (measurable_pi_apply k)

theorem measurable_perpetuity : Measurable perpetuity :=
  Measurable.tsum measurable_term

theorem abs_le_exp_log_abs (a : ℝ) : |a| ≤ exp (log |a|) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [exp_log (abs_pos.2 ha)]

theorem abs_le_exp_posLog (b : ℝ) : |b| ≤ exp (posLog b) := by
  rcases le_or_gt |b| 1 with h | h
  · exact h.trans (one_le_exp posLog_nonneg)
  · rw [posLog_eq_log h.le, ← log_abs, exp_log (by linarith)]

theorem abs_prod_le_exp (v : ℕ → ℝ × ℝ) (k : ℕ) :
    |∏ i ∈ Finset.range k, (v i).1| ≤ exp (∑ i ∈ Finset.range k, log |(v i).1|) := by
  rw [Finset.abs_prod, exp_sum]
  gcongr with i _
  exact abs_le_exp_log_abs _

theorem abs_term_le_exp (v : ℕ → ℝ × ℝ) (k : ℕ) :
    |term v k| ≤ exp (∑ i ∈ Finset.range k, log |(v i).1| + posLog (v k).2) := by
  rw [term, abs_mul, exp_add]
  exact mul_le_mul (abs_prod_le_exp v k) (abs_le_exp_posLog _) (abs_nonneg _) (exp_pos _).le

/-- If the averages `n⁻¹ ∑_{i < n} x_i` converge, then `x_n / n → 0`. -/
theorem tendsto_div_of_tendsto_average {x : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => x n / n) atTop (𝓝 0) := by
  have h1 := h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
  have h3 := (h2.mul h1).sub h
  rw [one_mul, sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, Finset.sum_range_succ]
  field_simp
  ring

/-- The **contraction condition** on a sequence `v = (a_i, b_i)_i`: for all large `k`,
`∑_{i < k} log |a_i| + log⁺ |b_k| ≤ c k`. For `c < 0` it holds almost surely for an iid sequence
with `E log |A| < c` and `E log⁺ |B| < ∞` (`ae_contracting`). -/
def Contracting (c : ℝ) (v : ℕ → ℝ × ℝ) : Prop :=
  ∀ᶠ k : ℕ in atTop, ∑ i ∈ Finset.range k, log |(v i).1| + posLog (v k).2 ≤ c * k

theorem exp_mul_nat (c : ℝ) (k : ℕ) : exp (c * k) = exp c ^ k := by
  rw [mul_comm, exp_nat_mul]

theorem Contracting.abs_term_le {c : ℝ} {v : ℕ → ℝ × ℝ} (h : Contracting c v) :
    ∀ᶠ k : ℕ in atTop, |term v k| ≤ exp c ^ k := by
  filter_upwards [h] with k hk
  exact (abs_term_le_exp v k).trans (by rw [← exp_mul_nat]; exact exp_le_exp.2 hk)

theorem Contracting.summable_abs_term {c : ℝ} (hc : c < 0) {v : ℕ → ℝ × ℝ}
    (h : Contracting c v) : Summable fun k => |term v k| :=
  Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (exp_pos c).le (Real.exp_lt_one_iff.2 hc))
    (by simpa only [Real.norm_eq_abs, abs_abs] using h.abs_term_le)

theorem Contracting.summable_term {c : ℝ} (hc : c < 0) {v : ℕ → ℝ × ℝ}
    (h : Contracting c v) : Summable (term v) :=
  (h.summable_abs_term hc).of_abs

/-- Under the contraction condition the products `A_0 ⋯ A_{k-1}` tend to `0`. -/
theorem Contracting.tendsto_prod {c : ℝ} (hc : c < 0) {v : ℕ → ℝ × ℝ}
    (h : Contracting c v) :
    Tendsto (fun k => ∏ i ∈ Finset.range k, (v i).1) atTop (𝓝 0) := by
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (exp_pos c).le (Real.exp_lt_one_iff.2 hc)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [h] with k hk
  rw [Real.norm_eq_abs, ← exp_mul_nat]
  exact (abs_prod_le_exp v k).trans (exp_le_exp.2 (by linarith [posLog_nonneg (x := (v k).2)]))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {V : ℕ → Ω → ℝ × ℝ}

/-- The strong law of large numbers for a measurable function of an iid sequence. -/
theorem ae_tendsto_average_comp (hiid : iIndepFun V P)
    (hid : ∀ n, IdentDistrib (V n) (V 0) P P) {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (hint : Integrable (fun ω => g (V 0 ω)) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (V i ω)) atTop
      (𝓝 (∫ ω, g (V 0 ω) ∂P)) := by
  have hind : iIndepFun (fun i => g ∘ V i) P := hiid.comp (fun _ => g) fun _ => hg
  filter_upwards [strong_law_ae (fun i => g ∘ V i) hint (fun i j hij => hind.indepFun hij)
    fun i => (hid i).comp hg] with ω hω
  simpa using hω

/-- **Almost sure contraction.** For an iid sequence `V_n = (A_n, B_n)` with
`E log |A| < 0` and `E log⁺ |B| < ∞`, almost surely
`∑_{i < k} log |A_i| + log⁺ |B_k| ≤ (E log |A| / 2) k` for all large `k` (the contraction
condition with `c = E log |A| / 2`). -/
theorem ae_contracting (hiid : iIndepFun V P)
    (hid : ∀ n, IdentDistrib (V n) (V 0) P P)
    (hA : Integrable (fun ω => log |(V 0 ω).1|) P) (hneg : ∫ ω, log |(V 0 ω).1| ∂P < 0)
    (hB : Integrable (fun ω => posLog (V 0 ω).2) P) :
    ∀ᵐ ω ∂P, Contracting ((∫ ω, log |(V 0 ω).1| ∂P) / 2) fun i => V i ω := by
  set γ := ∫ ω, log |(V 0 ω).1| ∂P
  have hgA : Measurable fun p : ℝ × ℝ => log |p.1| := by fun_prop
  have hgB : Measurable fun p : ℝ × ℝ => posLog p.2 :=
    continuous_posLog.measurable.comp measurable_snd
  filter_upwards [ae_tendsto_average_comp hiid hid hgA hA,
    ae_tendsto_average_comp hiid hid hgB hB] with ω h1 h2
  have h3 := h1.add (tendsto_div_of_tendsto_average h2)
  rw [add_zero] at h3
  filter_upwards [h3.eventually (gt_mem_nhds (by linarith : γ < γ / 2)),
    eventually_ge_atTop 1] with k hk hk1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have := (mul_lt_mul_iff_of_pos_right hkpos).2 hk
  rw [add_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hkpos.ne', one_mul,
    div_mul_cancel₀ _ hkpos.ne'] at this
  exact this.le

end SRE

end ExtremeValueTheory
