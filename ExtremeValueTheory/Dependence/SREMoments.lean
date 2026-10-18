/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.SRE
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Moments of the stationary solution of a stochastic recurrence equation

skeleton
-/

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal

namespace ExtremeValueTheory

namespace SRE

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]

/-- Integrating a function of `(v_0, (v_{n+1})_n)` against `ν^⊗ℕ` is integrating against
`ν ⊗ ν^⊗ℕ`. -/
theorem lintegral_seqLaw_split {F : (ℝ × ℝ) × (ℕ → ℝ × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, F (v 0, shift v) ∂seqLaw ν = ∫⁻ q, F q ∂(ν.prod (seqLaw ν)) := by
  rw [← map_split_seqLaw, lintegral_map hF ((measurable_pi_apply 0).prodMk measurable_shift)]

/-- A sequence with `x_0 = 0` and `x_{n+1} ≤ r x_n + b` is bounded by `b / (1 - r)`. -/
theorem le_mul_inv_sub_of_le_mul_add {x : ℕ → ℝ≥0∞} {r b : ℝ≥0∞} (h0 : x 0 = 0)
    (h : ∀ n, x (n + 1) ≤ r * x n + b) (n : ℕ) : x n ≤ b * (1 - r)⁻¹ := by
  have hs : ∀ n, x n ≤ ∑ k ∈ Finset.range n, r ^ k * b := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine (h n).trans ?_
      have e : ∑ k ∈ Finset.range n, r ^ (k + 1) * b = r * ∑ k ∈ Finset.range n, r ^ k * b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [pow_succ', mul_assoc]
      rw [Finset.sum_range_succ', pow_zero, one_mul, e]
      gcongr
  refine (hs n).trans ((ENNReal.sum_le_tsum _).trans ?_)
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

/-- `∫ g(v_0) dν^⊗ℕ`-type integrals against `ν ⊗ ν^⊗ℕ` of a function of the first factor. -/
theorem lintegral_prod_fst_seqLaw {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q, g q.1 ∂(ν.prod (seqLaw ν)) = ∫⁻ p, g p ∂ν := by
  rw [← lintegral_map hg measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

/-- The backward iterates started at `0`: the partial sums `∑_{k < n} A_0 ⋯ A_{k-1} B_k`. -/
theorem measurable_backward_zero (n : ℕ) : Measurable fun v : ℕ → ℝ × ℝ => backward 0 v n :=
  by unfold backward term; fun_prop

/-- `∫⁻ |q.1.1 y(q.2)|^s + |q.1.2|^s` splits as `E|A|^s ∫⁻ |y|^s + E|B|^s`. -/
theorem lintegral_mul_add_rpow {y : (ℕ → ℝ × ℝ) → ℝ} (hy : Measurable y) {s : ℝ} :
    ∫⁻ q : (ℝ × ℝ) × (ℕ → ℝ × ℝ), ‖q.1.1‖ₑ ^ s * ‖y q.2‖ₑ ^ s + ‖q.1.2‖ₑ ^ s ∂(ν.prod (seqLaw ν))
      = (∫⁻ p, ‖p.1‖ₑ ^ s ∂ν) * (∫⁻ v, ‖y v‖ₑ ^ s ∂seqLaw ν) + ∫⁻ p, ‖p.2‖ₑ ^ s ∂ν := by
  have h1 : Measurable fun p : ℝ × ℝ => ‖p.1‖ₑ ^ s := by fun_prop
  have h2 : Measurable fun p : ℝ × ℝ => ‖p.2‖ₑ ^ s := by fun_prop
  have h3 : Measurable fun v => ‖y v‖ₑ ^ s := by fun_prop
  rw [lintegral_add_right (g := fun q : (ℝ × ℝ) × (ℕ → ℝ × ℝ) => ‖q.1.2‖ₑ ^ s) _
    (by fun_prop),
    lintegral_prod_mul h1.aemeasurable h3.aemeasurable, lintegral_prod_fst_seqLaw h2]

/-- **The moment recursion, `s ≤ 1`**: `E|Y_{n+1}|^s ≤ E|A|^s E|Y_n|^s + E|B|^s` for the
partial sums `Y_n` of the perpetuity. -/
theorem lintegral_backward_succ_le_of_le_one {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    ∫⁻ v, ‖backward 0 v (n + 1)‖ₑ ^ s ∂seqLaw ν ≤
      (∫⁻ p, ‖p.1‖ₑ ^ s ∂ν) * (∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν) +
        ∫⁻ p, ‖p.2‖ₑ ^ s ∂ν := by
  have hy := measurable_backward_zero n
  simp only [backward_succ]
  rw [lintegral_seqLaw_split (F := fun q => ‖affine (backward 0 q.2 n) q.1‖ₑ ^ s)
    (by unfold affine; fun_prop), ← lintegral_mul_add_rpow hy]
  refine lintegral_mono fun q => ?_
  calc ‖affine (backward 0 q.2 n) q.1‖ₑ ^ s
      ≤ (‖q.1.1 * backward 0 q.2 n‖ₑ + ‖q.1.2‖ₑ) ^ s :=
        ENNReal.rpow_le_rpow (enorm_add_le _ _) hs
    _ ≤ ‖q.1.1 * backward 0 q.2 n‖ₑ ^ s + ‖q.1.2‖ₑ ^ s := ENNReal.rpow_add_le_add_rpow _ _ hs hs1
    _ = _ := by rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hs]

/-- **The moment recursion, `s ≥ 1`** (Minkowski): `‖Y_{n+1}‖_s ≤ ‖A‖_s ‖Y_n‖_s + ‖B‖_s`. -/
theorem lintegral_backward_succ_le_of_one_le {s : ℝ} (hs1 : 1 ≤ s) (n : ℕ) :
    (∫⁻ v, ‖backward 0 v (n + 1)‖ₑ ^ s ∂seqLaw ν) ^ (1 / s) ≤
      (∫⁻ p, ‖p.1‖ₑ ^ s ∂ν) ^ (1 / s) * (∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν) ^ (1 / s) +
        (∫⁻ p, ‖p.2‖ₑ ^ s ∂ν) ^ (1 / s) := by
  have hs : 0 ≤ s := zero_le_one.trans hs1
  have hy := measurable_backward_zero n
  simp only [backward_succ]
  rw [lintegral_seqLaw_split (F := fun q => ‖affine (backward 0 q.2 n) q.1‖ₑ ^ s)
    (by unfold affine; fun_prop)]
  set f : (ℝ × ℝ) × (ℕ → ℝ × ℝ) → ℝ≥0∞ := fun q => ‖q.1.1‖ₑ * ‖backward 0 q.2 n‖ₑ
  set g : (ℝ × ℝ) × (ℕ → ℝ × ℝ) → ℝ≥0∞ := fun q => ‖q.1.2‖ₑ
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hmono : ∫⁻ q, ‖affine (backward 0 q.2 n) q.1‖ₑ ^ s ∂(ν.prod (seqLaw ν)) ≤
      ∫⁻ q, (f + g) q ^ s ∂(ν.prod (seqLaw ν)) := by
    refine lintegral_mono fun q => ENNReal.rpow_le_rpow ?_ hs
    simp only [affine, Pi.add_apply, f, g, ← enorm_mul]
    exact enorm_add_le _ _
  refine (ENNReal.rpow_le_rpow hmono (by positivity)).trans
    ((ENNReal.lintegral_Lp_add_le hf.aemeasurable hg.aemeasurable hs1).trans_eq ?_)
  have hfs : ∫⁻ q, f q ^ s ∂(ν.prod (seqLaw ν)) =
      (∫⁻ p, ‖p.1‖ₑ ^ s ∂ν) * ∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν := by
    simp only [f, ENNReal.mul_rpow_of_nonneg _ _ hs]
    exact lintegral_prod_mul (f := fun p : ℝ × ℝ => ‖p.1‖ₑ ^ s)
      (g := fun v => ‖backward 0 v n‖ₑ ^ s) (by fun_prop) (by fun_prop)
  rw [hfs, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), lintegral_prod_fst_seqLaw (g := fun p => ‖p.2‖ₑ ^ s) (by fun_prop)]

theorem lintegral_backward_zero {s : ℝ} (hs : 0 < s) :
    ∫⁻ v, ‖backward 0 v 0‖ₑ ^ s ∂seqLaw ν = 0 := by
  simp [backward_zero, ENNReal.zero_rpow_of_pos hs]

/-- **Uniform moment bound for the partial sums of the perpetuity**: if `E|A|^s < 1` and
`E|B|^s < ∞` then `sup_n E|∑_{k < n} A_0 ⋯ A_{k-1} B_k|^s < ∞`. -/
theorem exists_lintegral_backward_le {s : ℝ} (hs : 0 < s) (hρ : ∫⁻ p, ‖p.1‖ₑ ^ s ∂ν < 1)
    (hβ : ∫⁻ p, ‖p.2‖ₑ ^ s ∂ν < ∞) :
    ∃ K < ∞, ∀ n, ∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν ≤ K := by
  set ρ := ∫⁻ p, ‖p.1‖ₑ ^ s ∂ν
  set β := ∫⁻ p, ‖p.2‖ₑ ^ s ∂ν
  rcases le_total s 1 with hs1 | hs1
  · refine ⟨β * (1 - ρ)⁻¹, ENNReal.mul_lt_top hβ (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ)),
      le_mul_inv_sub_of_le_mul_add (lintegral_backward_zero hs) fun n => ?_⟩
    exact lintegral_backward_succ_le_of_le_one hs.le hs1 n
  · have hs' : 0 < 1 / s := by positivity
    set C := β ^ (1 / s) * (1 - ρ ^ (1 / s))⁻¹
    have hC : C < ∞ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hs'.le hβ.ne)
      (ENNReal.inv_lt_top.2 (tsub_pos_of_lt (ENNReal.rpow_lt_one hρ hs')))
    refine ⟨C ^ s, ENNReal.rpow_lt_top_of_nonneg hs.le hC.ne, fun n => ?_⟩
    have hx := le_mul_inv_sub_of_le_mul_add
      (x := fun n => (∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν) ^ (1 / s))
      (by simp only [lintegral_backward_zero hs, ENNReal.zero_rpow_of_pos hs'])
      (fun n => lintegral_backward_succ_le_of_one_le hs1 n) n
    calc ∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν
        = ((∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν) ^ (1 / s)) ^ s := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs.ne', ENNReal.rpow_one]
      _ ≤ C ^ s := ENNReal.rpow_le_rpow hx hs.le

/-- **Finite moments of the stationary solution** ([BDM16, Theorem 2.1.3 and Lemma 2.3.1];
[Vervaat 1979, Theorem 1.6]): if `E log |A| < 0`, `E log⁺ |B| < ∞`, and for some `s > 0`
`E|A|^s < 1` and `E|B|^s < ∞`, then `E|X|^s < ∞` for `X` with the stationary law. -/
theorem lintegral_enorm_rpow_stationaryLaw_lt_top
    (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν) (hneg : ∫ p, log |p.1| ∂ν < 0)
    (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) {s : ℝ} (hs : 0 < s)
    (hρ : ∫⁻ p, ‖p.1‖ₑ ^ s ∂ν < 1) (hβ : ∫⁻ p, ‖p.2‖ₑ ^ s ∂ν < ∞) :
    ∫⁻ x, ‖x‖ₑ ^ s ∂stationaryLaw ν < ∞ := by
  have hc : (∫ p, log |p.1| ∂ν) / 2 < 0 := by linarith
  obtain ⟨K, hK, hle⟩ := exists_lintegral_backward_le hs hρ hβ
  have hmeas : ∀ n, Measurable fun v => ‖backward 0 v n‖ₑ ^ s := fun n => by
    have := measurable_backward_zero n; fun_prop
  rw [stationaryLaw, lintegral_map (by fun_prop) measurable_perpetuity]
  refine lt_of_le_of_lt ?_ hK
  calc ∫⁻ v, ‖perpetuity v‖ₑ ^ s ∂seqLaw ν
      = ∫⁻ v, liminf (fun n => ‖backward 0 v n‖ₑ ^ s) atTop ∂seqLaw ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_contracting_seqLaw hA hneg hB] with v hv
        refine (Tendsto.liminf_eq ?_).symm
        exact ((ENNReal.continuous_rpow_const.comp continuous_enorm).tendsto _).comp
          (hv.tendsto_backward hc 0)
    _ ≤ liminf (fun n => ∫⁻ v, ‖backward 0 v n‖ₑ ^ s ∂seqLaw ν) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ K := liminf_le_of_frequently_le' (Frequently.of_forall hle)

end SRE

end ExtremeValueTheory
