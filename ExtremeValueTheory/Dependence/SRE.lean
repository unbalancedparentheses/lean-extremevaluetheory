/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MarkovChain
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Stochastic recurrence equations: the stationary solution

The **stochastic recurrence equation** (random coefficient autoregression, random affine map)

  `X_t = A_t X_{t-1} + B_t`, `(A_t, B_t)` iid with law `ν` on `ℝ × ℝ`,

is the random iteration `X_{t+1} = f(X_t, V_t)` of `Dependence/MarkovChain.lean` with
`f(x, (a, b)) = a x + b` (`SRE.affine`) [Kesten 1973; Vervaat 1979; Goldie 1991; BDM16, Ch. 2;
EKM, §8.4]. Under the contraction condition `E log |A| < 0` and `E log⁺ |B| < ∞` its unique
stationary law is the law of the **perpetuity**

  `Y = ∑_{k ≥ 0} A_0 A_1 ⋯ A_{k-1} B_k`.

Proof of convergence: by the strong law of large numbers, `k⁻¹ ∑_{i < k} log |A_i| → E log |A|`
and `k⁻¹ log⁺ |B_k| → 0` almost surely, so `|A_0 ⋯ A_{k-1} B_k| ≤ exp(k E log |A| / 2)` for
large `k` (`SRE.Contracting`). Uniqueness: if `π'` is invariant, the backward iterates
`f_{V_0} ∘ ⋯ ∘ f_{V_{n-1}}(X₀)`, `X₀ ∼ π'`, all have law `π'` and converge almost surely to the
perpetuity.

Here `log` is Mathlib's `Real.log` (`log 0 = 0`), and the hypothesis `E log |A| < 0` is taken
with `log |A|` integrable; when `P(A = 0) > 0` this is stronger than the textbook condition (which
reads `log 0 = -∞`).

## Main definitions

* `SRE.affine`, `SRE.term`, `SRE.perpetuity`, `SRE.backward`: the recursion, the terms
  `A_0 ⋯ A_{k-1} B_k`, the perpetuity and the backward iterates.
* `SRE.Contracting c v`: the deterministic contraction condition on a sequence.
* `SRE.seqLaw ν = ν^⊗ℕ`, `SRE.stationaryLaw ν`: the law of the perpetuity.

## Main results

* `SRE.ae_contracting`, `SRE.ae_contracting_seqLaw`: almost sure contraction, hence absolute
  convergence of the perpetuity (`Contracting.summable_abs_term`) [BDM16, Theorem 2.1.3].
* `SRE.map_affine_stationaryLaw`: the stationary law solves `X =ᵈ A X + B`, `X ⊥ (A, B)`.
* `SRE.eq_stationaryLaw`: it is the unique such law.
* `SRE.isStationary_chain`: the random iteration started from it is a stationary Markov chain.
* `SRE.ae_summable_and_map_perpetuity`: on any probability space, the perpetuity of an iid
  sequence converges almost surely and has law `stationaryLaw ν`.

The pathwise (`ℤ`-indexed) solution is in `Dependence/SREPathwise.lean`, moments and tails in
`Dependence/SREMoments.lean`, the Kesten exponent in `Dependence/SREExponent.lean`, GARCH(1,1)
in `Dependence/SREGarch.lean`.
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

theorem Contracting.abs_term_le {c : ℝ} {v : ℕ → ℝ × ℝ} (h : Contracting c v) :
    ∀ᶠ k : ℕ in atTop, |term v k| ≤ exp c ^ k := by
  filter_upwards [h] with k hk
  exact (abs_term_le_exp v k).trans (by rw [← exp_nat_mul, mul_comm]; exact exp_le_exp.2 hk)

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
  rw [Real.norm_eq_abs, ← exp_nat_mul, mul_comm]
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

/-! ### The perpetuity recursion -/

/-- The shifted sequence `(v_{n+1})_n`. -/
def shift (v : ℕ → ℝ × ℝ) : ℕ → ℝ × ℝ := fun n => v (n + 1)

theorem measurable_shift : Measurable shift :=
  Measurable.of_eval fun n => measurable_pi_apply (n + 1)

theorem term_zero (v : ℕ → ℝ × ℝ) : term v 0 = (v 0).2 := by simp [term]

theorem term_succ (v : ℕ → ℝ × ℝ) (k : ℕ) : term v (k + 1) = (v 0).1 * term (shift v) k := by
  simp only [term, shift, Finset.prod_range_succ']
  ring

/-- **The perpetuity solves the fixed point equation** `Y = A_0 Y' + B_0`, where `Y'` is the
perpetuity of the shifted sequence, whenever the series converges. -/
theorem perpetuity_eq {v : ℕ → ℝ × ℝ} (h : Summable (term v)) :
    perpetuity v = affine (perpetuity (shift v)) (v 0) := by
  rw [perpetuity, h.tsum_eq_zero_add, term_zero, affine, perpetuity]
  simp only [term_succ, tsum_mul_left]
  ring

/-- The backward iteration `f_{v_0} ∘ ⋯ ∘ f_{v_{n-1}} (x) = ∑_{k < n} a_0 ⋯ a_{k-1} b_k +
a_0 ⋯ a_{n-1} x`. -/
noncomputable def backward (x : ℝ) (v : ℕ → ℝ × ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, term v k + (∏ i ∈ Finset.range n, (v i).1) * x

theorem backward_zero (x : ℝ) (v : ℕ → ℝ × ℝ) : backward x v 0 = x := by simp [backward]

theorem backward_succ (x : ℝ) (v : ℕ → ℝ × ℝ) (n : ℕ) :
    backward x v (n + 1) = affine (backward x (shift v) n) (v 0) := by
  simp only [backward, affine, Finset.sum_range_succ', term_succ, term_zero,
    Finset.prod_range_succ', ← Finset.mul_sum]
  simp only [shift]
  ring

theorem measurable_backward (n : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ × ℝ) => backward p.1 p.2 n := by
  unfold backward
  refine (Finset.measurable_sum _ fun k _ => (measurable_term k).comp measurable_snd).add
    ((Finset.measurable_prod _ fun i _ => ?_).mul measurable_fst)
  exact (measurable_fst.comp (measurable_pi_apply (X := fun _ : ℕ => ℝ × ℝ) i)).comp measurable_snd

/-- Under the contraction condition, the backward iteration converges to the perpetuity,
whatever the starting point. -/
theorem Contracting.tendsto_backward {c : ℝ} (hc : c < 0) {v : ℕ → ℝ × ℝ}
    (h : Contracting c v) (x : ℝ) :
    Tendsto (backward x v) atTop (𝓝 (perpetuity v)) := by
  have h1 := (h.summable_term hc).hasSum.tendsto_sum_nat
  have h2 := (h.tendsto_prod hc).mul_const x
  rw [zero_mul] at h2
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3

/-! ### The stationary law -/

section StationaryLaw

variable (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]

/-- The law `ν^⊗ℕ` of an iid sequence `(A_n, B_n)_n` with marginal law `ν`. -/
noncomputable abbrev seqLaw : Measure (ℕ → ℝ × ℝ) := Measure.infinitePi fun _ : ℕ => ν

/-- The **stationary law** of the stochastic recurrence: the law of the perpetuity
`∑_{k ≥ 0} A_0 ⋯ A_{k-1} B_k` of an iid sequence with law `ν`. -/
noncomputable def stationaryLaw : Measure ℝ := (seqLaw ν).map perpetuity

instance : IsProbabilityMeasure (stationaryLaw ν) :=
  by unfold stationaryLaw; infer_instance

theorem iIndepFun_seqLaw : iIndepFun (fun n (v : ℕ → ℝ × ℝ) => v n) (seqLaw ν) :=
  iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

theorem identDistrib_seqLaw (n : ℕ) :
    IdentDistrib (fun v : ℕ → ℝ × ℝ => v n) (fun v => v 0) (seqLaw ν) (seqLaw ν) :=
  ⟨(measurable_pi_apply n).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩

theorem integral_seqLaw_coord {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    ∫ v, g (v 0) ∂seqLaw ν = ∫ p, g p ∂ν := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable hg.aestronglyMeasurable,
    Measure.infinitePi_map_eval]

theorem integrable_seqLaw_coord {g : ℝ × ℝ → ℝ} (hg : Measurable g) (hi : Integrable g ν) :
    Integrable (fun v : ℕ → ℝ × ℝ => g (v 0)) (seqLaw ν) := by
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => ν) 0] at hi
  exact (integrable_map_measure hg.aestronglyMeasurable
    (measurable_pi_apply 0).aemeasurable).1 hi

variable {ν}

/-- **Almost sure convergence of the perpetuity** ([BDM16, Theorem 2.1.3]; [Vervaat 1979]): if
`E log |A| < 0` and `E log⁺ |B| < ∞`, then for `ν^⊗ℕ`-almost every sequence the contraction
condition holds; in particular `∑_k A_0 ⋯ A_{k-1} B_k` converges absolutely
(`Contracting.summable_abs_term`). -/
theorem ae_contracting_seqLaw (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) :
    ∀ᵐ v ∂seqLaw ν, Contracting ((∫ p, log |p.1| ∂ν) / 2) v := by
  have hgA : Measurable fun p : ℝ × ℝ => log |p.1| := by fun_prop
  have hgB : Measurable fun p : ℝ × ℝ => posLog p.2 :=
    continuous_posLog.measurable.comp measurable_snd
  have h := ae_contracting (iIndepFun_seqLaw ν) (identDistrib_seqLaw ν)
    (integrable_seqLaw_coord ν hgA hA) (by rwa [integral_seqLaw_coord ν hgA])
    (integrable_seqLaw_coord ν hgB hB)
  rwa [integral_seqLaw_coord ν hgA] at h

variable (ν) in
/-- The shifted sequence of an iid sequence is again iid with the same law. -/
theorem map_shift_seqLaw : (seqLaw ν).map shift = seqLaw ν :=
  RandomIteration.map_path_eq_infinitePi (V := fun n (v : ℕ → ℝ × ℝ) => v (n + 1))
    (fun n => measurable_pi_apply (n + 1))
    ((iIndepFun_seqLaw ν).precomp (add_left_injective 1))
    fun n => Measure.infinitePi_map_eval _ (n + 1)

variable (ν) in
/-- Splitting off the first coordinate: `ν^⊗ℕ` is the law of `(v_0, (v_{n+1})_n)` under
`ν ⊗ ν^⊗ℕ`. -/
theorem map_split_seqLaw :
    (seqLaw ν).map (fun v => (v 0, shift v)) = ν.prod (seqLaw ν) := by
  have h := RandomIteration.indepFun_zero_shift (V := fun n (v : ℕ → ℝ × ℝ) => v n)
    (fun n => measurable_pi_apply n) (iIndepFun_seqLaw ν)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    measurable_shift.aemeasurable).1 h, map_shift_seqLaw, Measure.infinitePi_map_eval]

/-- **Invariance of the stationary law** ([BDM16, Theorem 2.1.3]): if `E log |A| < 0` and
`E log⁺ |B| < ∞`, the law `π` of the perpetuity solves the distributional fixed point equation
`X =ᵈ A X + B`, `X ⊥ (A, B)`: `(π ⊗ ν).map (x, (a, b) ↦ a x + b) = π`. -/
theorem map_affine_stationaryLaw (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) :
    ((stationaryLaw ν).prod ν).map (Function.uncurry affine) = stationaryLaw ν := by
  have hc : (∫ p, log |p.1| ∂ν) / 2 < 0 := by linarith
  set g : (ℝ × ℝ) × (ℕ → ℝ × ℝ) → ℝ := fun q => affine (perpetuity q.2) q.1
  have hg : Measurable g :=
    measurable_affine.comp ((measurable_perpetuity.comp measurable_snd).prodMk measurable_fst)
  have hsplit : Measurable fun v : ℕ → ℝ × ℝ => (v 0, shift v) :=
    (measurable_pi_apply 0).prodMk measurable_shift
  have h1 : stationaryLaw ν = (ν.prod (seqLaw ν)).map g := by
    rw [← map_split_seqLaw, Measure.map_map hg hsplit, stationaryLaw]
    refine Measure.map_congr ?_
    filter_upwards [ae_contracting_seqLaw hA hneg hB] with v hv
    exact perpetuity_eq (hv.summable_term hc)
  have hm : Measurable (Function.uncurry affine ∘ Prod.map perpetuity id) :=
    measurable_affine.comp (measurable_perpetuity.prodMap measurable_id)
  calc ((stationaryLaw ν).prod ν).map (Function.uncurry affine)
      = (((seqLaw ν).prod ν).map (Prod.map perpetuity id)).map (Function.uncurry affine) := by
        rw [← Measure.map_prod_map _ _ measurable_perpetuity measurable_id, Measure.map_id,
          stationaryLaw]
    _ = ((ν.prod (seqLaw ν)).map Prod.swap).map
          (Function.uncurry affine ∘ Prod.map perpetuity id) := by
        rw [Measure.map_map measurable_affine (measurable_perpetuity.prodMap measurable_id),
          Measure.prod_swap]
    _ = (ν.prod (seqLaw ν)).map g := by rw [Measure.map_map hm measurable_swap]; rfl
    _ = stationaryLaw ν := h1.symm

/-! ### Uniqueness of the invariant law -/

open RandomIteration in
/-- If `π'` is invariant for the recursion, then under `π' ⊗ ν^⊗ℕ` every backward iterate
`f_{v_0} ∘ ⋯ ∘ f_{v_{n-1}} (x)` has law `π'`. -/
theorem map_backward_canonicalMeasure (π' : Measure ℝ) [IsProbabilityMeasure π']
    (hinv : (π'.prod ν).map (Function.uncurry affine) = π') (n : ℕ) :
    (canonicalMeasure π' ν).map (fun p => backward p.1 p.2 n) = π' := by
  set μ' := canonicalMeasure π' ν
  have hsh : Measurable fun p : ℝ × (ℕ → ℝ × ℝ) => shift p.2 := measurable_shift.comp measurable_snd
  have h0 : Measurable fun p : ℝ × (ℕ → ℝ × ℝ) => p.2 0 :=
    (measurable_pi_apply 0).comp measurable_snd
  have hcan := indepFun_canonical π' ν
  have hX : IndepFun Prod.fst (fun p : ℝ × (ℕ → ℝ × ℝ) => (shift p.2, p.2 0)) μ' :=
    hcan.comp measurable_id (measurable_shift.prodMk (measurable_pi_apply 0))
  have hYZ : IndepFun (fun p : ℝ × (ℕ → ℝ × ℝ) => shift p.2) (fun p => p.2 0) μ' :=
    (indepFun_zero_shift (V := fun n (p : ℝ × (ℕ → ℝ × ℝ)) => p.2 n)
      (fun n => (measurable_pi_apply n).comp measurable_snd) (iIndepFun_canonical π' ν)).symm
  have hind : IndepFun (fun p : ℝ × (ℕ → ℝ × ℝ) => (p.1, shift p.2)) (fun p => p.2 0) μ' :=
    indepFun_prodMk_of_indepFun measurable_fst hsh h0 hX hYZ
  have hXY : IndepFun Prod.fst (fun p : ℝ × (ℕ → ℝ × ℝ) => shift p.2) μ' :=
    hcan.comp measurable_id measurable_shift
  have hlawY : μ'.map (fun p => shift p.2) = seqLaw ν := by
    rw [show (fun p : ℝ × (ℕ → ℝ × ℝ) => shift p.2) = shift ∘ Prod.snd from rfl,← Measure.map_map measurable_shift measurable_snd, map_snd_canonicalMeasure,
      map_shift_seqLaw]
  have hlaw1 : μ'.map (fun p => (p.1, shift p.2)) = μ' := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      hsh.aemeasurable).1 hXY, hlawY, map_fst_canonicalMeasure]; rfl
  have hlaw : μ'.map (fun p => ((p.1, shift p.2), p.2 0)) = μ'.prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_fst.prodMk hsh).aemeasurable
      h0.aemeasurable).1 hind, hlaw1, map_coord_canonicalMeasure]
  induction n with
  | zero => simp only [backward_zero]; exact map_fst_canonicalMeasure π' ν
  | succ n ih =>
    have e : (fun p : ℝ × (ℕ → ℝ × ℝ) => backward p.1 p.2 (n + 1)) =
        (Function.uncurry affine ∘ Prod.map (fun q : ℝ × (ℕ → ℝ × ℝ) => backward q.1 q.2 n) id) ∘
          fun p => ((p.1, shift p.2), p.2 0) := by
      funext p; simp [backward_succ]
    rw [e, ← Measure.map_map (measurable_affine.comp ((measurable_backward n).prodMap
      measurable_id)) ((measurable_fst.prodMk hsh).prodMk h0), hlaw,
      ← Measure.map_map measurable_affine ((measurable_backward n).prodMap measurable_id),
      ← Measure.map_prod_map _ _ (measurable_backward n) measurable_id, Measure.map_id, ih, hinv]

/-- **Uniqueness of the stationary law** ([BDM16, Theorem 2.1.3]): if `E log |A| < 0` and
`E log⁺ |B| < ∞`, every probability law `π'` solving the fixed point equation `X =ᵈ A X + B`,
`X ⊥ (A, B)`, is the law of the perpetuity. -/
theorem eq_stationaryLaw (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν)
    (π' : Measure ℝ) [IsProbabilityMeasure π']
    (hinv : (π'.prod ν).map (Function.uncurry affine) = π') :
    π' = stationaryLaw ν := by
  have hc : (∫ p, log |p.1| ∂ν) / 2 < 0 := by linarith
  set μ' := RandomIteration.canonicalMeasure π' ν
  have hae : ∀ᵐ p ∂μ', Contracting ((∫ p, log |p.1| ∂ν) / 2) p.2 := by
    have h : ∀ᵐ v ∂μ'.map Prod.snd, Contracting ((∫ p, log |p.1| ∂ν) / 2) v := by
      rw [RandomIteration.map_snd_canonicalMeasure π' ν]; exact ae_contracting_seqLaw hA hneg hB
    exact ae_of_ae_map measurable_snd.aemeasurable h
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hlim : Tendsto (fun n => ∫ p, f (backward p.1 p.2 n) ∂μ') atTop
      (𝓝 (∫ p, f (perpetuity p.2) ∂μ')) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (measurable_backward n)).aestronglyMeasurable)
      (integrable_const _) (fun n => ae_of_all _ fun p => f.norm_coe_le_norm _) ?_
    filter_upwards [hae] with p hp
    exact (f.continuous.tendsto _).comp (hp.tendsto_backward hc p.1)
  have hconst : ∀ n, ∫ p, f (backward p.1 p.2 n) ∂μ' = ∫ x, f x ∂π' := fun n => by
    rw [← map_backward_canonicalMeasure π' hinv n, integral_map
      (measurable_backward n).aemeasurable f.continuous.aestronglyMeasurable]
  simp only [hconst] at hlim
  rw [tendsto_nhds_unique tendsto_const_nhds hlim]
  change _ = ∫ x, f x ∂(seqLaw ν).map perpetuity
  rw [ integral_map
    measurable_perpetuity.aemeasurable f.continuous.aestronglyMeasurable]
  have e : ∫ x, f (perpetuity x) ∂(μ'.map Prod.snd) = ∫ p, f (perpetuity p.2) ∂μ' :=
    integral_map measurable_snd.aemeasurable
      (f.continuous.measurable.comp measurable_perpetuity).aestronglyMeasurable
  rw [RandomIteration.map_snd_canonicalMeasure π' ν] at e
  exact e.symm

/-- **The stationary solution of the stochastic recurrence equation** ([BDM16, Theorem 2.1.3];
[Kesten 1973]; [Vervaat 1979]): if `E log |A| < 0` and `E log⁺ |B| < ∞`, the random iteration
`X_{n+1} = A_n X_n + B_n` started from the law of the perpetuity, independently of the iid
innovations `(A_n, B_n) ∼ ν`, is a strictly stationary Markov chain
(`RandomIteration.isStationary_canonicalChain`). Its marginal law is the unique invariant law
(`eq_stationaryLaw`). -/
theorem isStationary_chain (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) :
    IsStationary (RandomIteration.chain affine Prod.fst fun n (p : ℝ × (ℕ → ℝ × ℝ)) => p.2 n)
      (RandomIteration.canonicalMeasure (stationaryLaw ν) ν) :=
  RandomIteration.isStationary_canonicalChain _ ν measurable_affine
    (map_affine_stationaryLaw hA hneg hB)

/-- The perpetuity of an iid sequence `V_n = (A_n, B_n)` with law `ν` on any probability space
converges absolutely almost surely, and has law `stationaryLaw ν`. -/
theorem ae_summable_and_map_perpetuity {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {V : ℕ → Ω → ℝ × ℝ} (hV : ∀ n, Measurable (V n)) (hiid : iIndepFun V P)
    (hid : ∀ n, P.map (V n) = ν) (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν)
    (hneg : ∫ p, log |p.1| ∂ν < 0) (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) :
    (∀ᵐ ω ∂P, Summable fun k => |term (fun n => V n ω) k|) ∧
      P.map (fun ω => perpetuity fun n => V n ω) = stationaryLaw ν := by
  have hc : (∫ p, log |p.1| ∂ν) / 2 < 0 := by linarith
  have hVm : Measurable fun ω n => V n ω := Measurable.of_eval hV
  have hlaw : P.map (fun ω n => V n ω) = seqLaw ν :=
    RandomIteration.map_path_eq_infinitePi hV hiid hid
  refine ⟨?_, ?_⟩
  · have h : ∀ᵐ v ∂P.map (fun ω n => V n ω), Summable fun k => |term v k| := by
      rw [hlaw]
      filter_upwards [ae_contracting_seqLaw hA hneg hB] with v hv using hv.summable_abs_term hc
    exact ae_of_ae_map hVm.aemeasurable h
  · rw [stationaryLaw, ← hlaw, Measure.map_map measurable_perpetuity hVm]
    rfl

end StationaryLaw

end SRE

end ExtremeValueTheory
