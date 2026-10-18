/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.SRE
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

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

/-! ### The Kesten exponent: `E |A|^κ = 1` -/

theorem rpow_le_one_add {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    x ^ q ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_le_one hx h hq0]
  · have := Real.rpow_le_rpow_of_exponent_le h hq1
    rw [Real.rpow_one] at this
    linarith

/-- **Strict Jensen for a power `q ∈ (0, 1)`**: if `F ≥ 0` has mean `1` and is not a.e. `1`, then
`E F^q < 1`. -/
theorem integral_rpow_lt_one {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {F : α → ℝ} (hF0 : ∀ᵐ x ∂μ, 0 ≤ F x) (hFi : Integrable F μ)
    (h1 : ∫ x, F x ∂μ = 1) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hnd : ¬ F =ᵐ[μ] 1) :
    ∫ x, F x ^ q ∂μ < 1 := by
  have hgi : Integrable (fun x => F x ^ q) μ := by
    refine ((integrable_const 1).add hFi).mono'
      (hFi.aestronglyMeasurable.aemeasurable.pow_const q).aestronglyMeasurable ?_
    filter_upwards [hF0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx q)]
    exact rpow_le_one_add hx hq0.le hq1.le
  rcases (Real.strictConcaveOn_rpow hq0 hq1).ae_eq_const_or_lt_map_average
    ((Real.continuous_rpow_const hq0.le).continuousOn) isClosed_Ici hF0 hFi hgi with h | h
  · refine absurd ?_ hnd
    rw [average_eq_integral, h1] at h
    exact h
  · rw [average_eq_integral, average_eq_integral, h1, Real.one_rpow] at h
    exact h

theorem enorm_rpow_eq_ofReal (a : ℝ) {s : ℝ} (hs : 0 ≤ s) : ‖a‖ₑ ^ s = ENNReal.ofReal (|a| ^ s) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg a) hs]

/-- If `E|A|^κ = 1` (with `|A|` not a.s. `1`), then `E|A|^s < 1` for `0 < s < κ`. -/
theorem lintegral_enorm_rpow_lt_one {κ : ℝ} (hκ : 0 < κ) (h1 : ∫⁻ p, ‖p.1‖ₑ ^ κ ∂ν = 1)
    (hnd : ¬ ∀ᵐ p ∂ν, |p.1| = 1) {s : ℝ} (hs : 0 < s) (hsκ : s < κ) :
    ∫⁻ p, ‖p.1‖ₑ ^ s ∂ν < 1 := by
  set F : ℝ × ℝ → ℝ := fun p => |p.1| ^ κ
  have hFm : Measurable F := by fun_prop
  have hFl : ∫⁻ p, ENNReal.ofReal (F p) ∂ν = 1 := by
    rw [← h1]; exact lintegral_congr fun p => (enorm_rpow_eq_ofReal _ hκ.le).symm
  have hFi : Integrable F ν := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => Real.rpow_nonneg (abs_nonneg _) _),
      hFl]
    exact ENNReal.one_lt_top
  have hF1 : ∫ p, F p ∂ν = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => Real.rpow_nonneg
      (abs_nonneg _) _) hFm.aestronglyMeasurable, hFl, ENNReal.toReal_one]
  have hq0 : 0 < s / κ := div_pos hs hκ
  have hq1 : s / κ < 1 := (div_lt_one hκ).2 hsκ
  have hnd' : ¬ F =ᵐ[ν] 1 := by
    intro h
    refine hnd ?_
    filter_upwards [h] with p hp
    have hp' : |p.1| ^ κ = 1 := hp
    have := congrArg (fun t => t ^ κ⁻¹) hp'
    simp only [Real.one_rpow] at this
    rwa [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hκ.ne', Real.rpow_one] at this
  have hJ := integral_rpow_lt_one (ae_of_all _ fun p => Real.rpow_nonneg (abs_nonneg _) _) hFi
    hF1 hq0 hq1 hnd'
  have he : ∀ p : ℝ × ℝ, F p ^ (s / κ) = |p.1| ^ s := fun p => by
    simp only [F]
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hκ.ne']
  replace hJ := lt_of_eq_of_lt (integral_congr_ae (ae_of_all _ he)).symm hJ
  have hGi : Integrable (fun p : ℝ × ℝ => |p.1| ^ s) ν := by
    refine ((integrable_const 1).add hFi).mono' (by fun_prop) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← he p]
    exact rpow_le_one_add (Real.rpow_nonneg (abs_nonneg _) _) hq0.le hq1.le
  rw [lintegral_congr (fun p : ℝ × ℝ => enorm_rpow_eq_ofReal p.1 hs.le),
    ← ofReal_integral_eq_lintegral_ofReal hGi
      (ae_of_all _ fun p => Real.rpow_nonneg (abs_nonneg _) _)]
  exact ENNReal.ofReal_lt_one.2 hJ

/-- The real moment `E|g|^s` as a real integral, when the `ℝ≥0∞`-valued one is finite. -/
theorem integrable_abs_rpow_of_lintegral_lt_top {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {g : α → ℝ} (hg : Measurable g) {s : ℝ} (hs : 0 ≤ s)
    (h : ∫⁻ x, ‖g x‖ₑ ^ s ∂μ < ∞) :
    Integrable (fun x => |g x| ^ s) μ ∧
      ENNReal.ofReal (∫ x, |g x| ^ s ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ s ∂μ := by
  have hm : Measurable fun x => |g x| ^ s := by fun_prop
  have hl : ∫⁻ x, ENNReal.ofReal (|g x| ^ s) ∂μ = ∫⁻ x, ‖g x‖ₑ ^ s ∂μ :=
    lintegral_congr fun x => (enorm_rpow_eq_ofReal _ hs).symm
  have hi : Integrable (fun x => |g x| ^ s) μ := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _),
      hl]
    exact h
  exact ⟨hi, by rw [ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _), hl]⟩

theorem abs_eq_one_of_rpow_eq_one {a κ : ℝ} (hκ : κ ≠ 0) (h : |a| ^ κ = 1) : |a| = 1 := by
  have := congrArg (fun t => t ^ κ⁻¹) h
  simp only [Real.one_rpow] at this
  rwa [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hκ, Real.rpow_one] at this

/-- If `E|A|^κ = 1` (with `|A|` not a.s. `1`), then `E|A|^s > 1` for `s > κ`. -/
theorem one_lt_lintegral_enorm_rpow {κ : ℝ} (hκ : 0 < κ) (h1 : ∫⁻ p, ‖p.1‖ₑ ^ κ ∂ν = 1)
    (hnd : ¬ ∀ᵐ p ∂ν, |p.1| = 1) {s : ℝ} (hsκ : κ < s) :
    1 < ∫⁻ p, ‖p.1‖ₑ ^ s ∂ν := by
  have hs : 0 < s := hκ.trans hsκ
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨hGi, hGl⟩ := integrable_abs_rpow_of_lintegral_lt_top (μ := ν) measurable_fst hs.le
    (hle.trans_lt ENNReal.one_lt_top)
  obtain ⟨hFi, hFl⟩ := integrable_abs_rpow_of_lintegral_lt_top (μ := ν) measurable_fst hκ.le
    (h1.trans_lt ENNReal.one_lt_top)
  rw [h1, ENNReal.ofReal_eq_one] at hFl
  set c := ∫ p, |p.1| ^ s ∂ν
  have hc0 : 0 ≤ c := integral_nonneg fun p => Real.rpow_nonneg (abs_nonneg _) _
  have hc1 : c ≤ 1 := by
    have := hGl.trans_le hle
    rwa [ENNReal.ofReal_le_one] at this
  have hq0 : 0 < κ / s := div_pos hκ hs
  have hq1 : κ / s < 1 := (div_lt_one hs).2 hsκ
  have he : ∀ p : ℝ × ℝ, (|p.1| ^ s) ^ (κ / s) = |p.1| ^ κ := fun p => by
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hs.ne']
  have hgi : Integrable (fun p : ℝ × ℝ => (|p.1| ^ s) ^ (κ / s)) ν := by
    simp only [he]; exact hFi
  rcases (Real.strictConcaveOn_rpow hq0 hq1).ae_eq_const_or_lt_map_average
    ((Real.continuous_rpow_const hq0.le).continuousOn) isClosed_Ici
    (ae_of_all _ fun p => Real.rpow_nonneg (abs_nonneg _) _) hGi hgi with h | h
  · rw [average_eq_integral] at h
    have hκc : ∀ᵐ p ∂ν, |p.1| ^ κ = c ^ (κ / s) := by
      filter_upwards [h] with p hp
      rw [← he p]; exact congrArg (· ^ (κ / s)) hp
    have hcκ : c ^ (κ / s) = 1 := by
      rw [← hFl, integral_congr_ae hκc, integral_const, probReal_univ, one_smul]
    exact hnd (by
      filter_upwards [hκc] with p hp
      exact abs_eq_one_of_rpow_eq_one hκ.ne' (hp.trans hcκ))
  · rw [average_eq_integral, average_eq_integral, integral_congr_ae (ae_of_all _ he), hFl] at h
    exact absurd (Real.rpow_le_one hc0 hc1 hq0.le) (not_le.2 h)

/-! ### Moments of the stationary solution in the Kesten–Goldie regime -/

theorem enorm_rpow_le_one_add {b s κ : ℝ} (hs : 0 ≤ s) (hsκ : s ≤ κ) :
    ‖b‖ₑ ^ s ≤ 1 + ‖b‖ₑ ^ κ := by
  rcases le_total ‖b‖ₑ 1 with h | h
  · exact (ENNReal.rpow_le_one h hs).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le h hsκ).trans le_add_self

/-- **Moments below the Kesten exponent** ([Kesten 1973]; [Goldie 1991, Theorem 4.1];
[BDM16, Theorem 2.4.4 and Lemma 2.3.1]): if `E|A|^κ = 1` for some `κ > 0` (with `|A|` not a.s.
`1`), `E log |A| < 0`, `E log⁺ |B| < ∞` and `E|B|^κ < ∞`, then the stationary solution has
`E|X|^s < ∞` for every `0 < s < κ`. -/
theorem lintegral_enorm_rpow_stationaryLaw_lt_top_of_lt
    (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν) (hneg : ∫ p, log |p.1| ∂ν < 0)
    (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) {κ : ℝ} (hκ : 0 < κ)
    (h1 : ∫⁻ p, ‖p.1‖ₑ ^ κ ∂ν = 1) (hnd : ¬ ∀ᵐ p ∂ν, |p.1| = 1)
    (hBκ : ∫⁻ p, ‖p.2‖ₑ ^ κ ∂ν < ∞) {s : ℝ} (hs : 0 < s) (hsκ : s < κ) :
    ∫⁻ x, ‖x‖ₑ ^ s ∂stationaryLaw ν < ∞ := by
  refine lintegral_enorm_rpow_stationaryLaw_lt_top hA hneg hB hs
    (lintegral_enorm_rpow_lt_one hκ h1 hnd hs hsκ) ?_
  calc ∫⁻ p, ‖p.2‖ₑ ^ s ∂ν ≤ ∫⁻ p, (1 + ‖p.2‖ₑ ^ κ) ∂ν :=
        lintegral_mono fun p => enorm_rpow_le_one_add hs.le hsκ.le
    _ = 1 + ∫⁻ p, ‖p.2‖ₑ ^ κ ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hBκ⟩

/-- Under `A, B ≥ 0` a.s., almost every iid sequence has nonnegative entries. -/
theorem ae_seqLaw_nonneg (hApos : ∀ᵐ p ∂ν, 0 ≤ p.1) (hBpos : ∀ᵐ p ∂ν, 0 ≤ p.2) :
    ∀ᵐ v ∂seqLaw ν, ∀ n, 0 ≤ (v n).1 ∧ 0 ≤ (v n).2 := by
  rw [ae_all_iff]
  intro n
  have h : ∀ᵐ p ∂(seqLaw ν).map (fun v => v n), 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    rw [Measure.infinitePi_map_eval]; filter_upwards [hApos, hBpos] with p h1 h2 using ⟨h1, h2⟩
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable h

theorem term_nonneg {v : ℕ → ℝ × ℝ} (hv : ∀ n, 0 ≤ (v n).1 ∧ 0 ≤ (v n).2) (k : ℕ) :
    0 ≤ term v k :=
  mul_nonneg (Finset.prod_nonneg fun i _ => (hv i).1) (hv k).2

/-- **Infinite moments above the Kesten exponent** ([Goldie 1991]; [BDM16, §2.4]): if `A, B ≥ 0`
a.s., `B` is not a.s. `0`, and `E A^s > 1`, then the stationary solution has `E X^s = ∞`. -/
theorem lintegral_enorm_rpow_stationaryLaw_eq_top_of_one_lt
    (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν) (hneg : ∫ p, log |p.1| ∂ν < 0)
    (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) (hApos : ∀ᵐ p ∂ν, 0 ≤ p.1)
    (hBpos : ∀ᵐ p ∂ν, 0 ≤ p.2) (hB0 : ¬ ∀ᵐ p ∂ν, p.2 = 0) {s : ℝ} (hs : 0 < s)
    (hρ : 1 < ∫⁻ p, ‖p.1‖ₑ ^ s ∂ν) :
    ∫⁻ x, ‖x‖ₑ ^ s ∂stationaryLaw ν = ∞ := by
  have hc : (∫ p, log |p.1| ∂ν) / 2 < 0 := by linarith
  set μX := stationaryLaw ν
  set m := ∫⁻ x, ‖x‖ₑ ^ s ∂μX
  have hnn := ae_seqLaw_nonneg hApos hBpos
  -- the stationary law lives on `[0, ∞)`
  have hμX0 : ∀ᵐ x ∂μX, 0 ≤ x := by
    refine (ae_map_iff measurable_perpetuity.aemeasurable measurableSet_Ici).2 ?_
    filter_upwards [hnn] with v hv using tsum_nonneg (term_nonneg hv)
  -- the stationary law is not `δ_0`
  have hm0 : m ≠ 0 := by
    intro h0
    rw [lintegral_eq_zero_iff (by fun_prop)] at h0
    refine hB0 ?_
    have h' : ∀ᵐ v ∂seqLaw ν, (v 0).2 = 0 := by
      have h1 : ∀ᵐ v ∂seqLaw ν, ‖perpetuity v‖ₑ ^ s = 0 :=
        ae_of_ae_map measurable_perpetuity.aemeasurable h0
      filter_upwards [h1, hnn, ae_contracting_seqLaw hA hneg hB] with v h1 hv hcv
      have hp : perpetuity v = 0 := by
        simpa [ENNReal.rpow_eq_zero_iff, hs, not_lt.2 hs.le] using h1
      have hle : term v 0 ≤ perpetuity v :=
        (hcv.summable_term hc).le_tsum 0 fun j _ => term_nonneg hv j
      rw [term_zero, hp] at hle
      exact le_antisymm hle (hv 0).2
    have h2 : ∀ᵐ p ∂(seqLaw ν).map (fun v => v 0), p.2 = 0 :=
      (ae_map_iff (measurable_pi_apply (X := fun _ : ℕ => ℝ × ℝ) 0).aemeasurable
        (measurableSet_eq_fun measurable_snd measurable_const)).2 h'
    rwa [Measure.infinitePi_map_eval] at h2
  by_contra hmtop
  -- the fixed point equation gives `m ≥ E A^s · m`
  have hle : (∫⁻ p, ‖p.1‖ₑ ^ s ∂ν) * m ≤ m := by
    have hinv := map_affine_stationaryLaw hA hneg hB
    have hpr0 : ∀ᵐ q ∂μX.prod ν, 0 ≤ q.1 := by
      have : ∀ᵐ x ∂(μX.prod ν).map Prod.fst, 0 ≤ x := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]; exact hμX0
      exact ae_of_ae_map measurable_fst.aemeasurable this
    have hpr1 : ∀ᵐ q ∂μX.prod ν, 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 := by
      have : ∀ᵐ p ∂(μX.prod ν).map Prod.snd, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
        filter_upwards [hApos, hBpos] with p h1 h2 using ⟨h1, h2⟩
      exact ae_of_ae_map measurable_snd.aemeasurable this
    calc (∫⁻ p, ‖p.1‖ₑ ^ s ∂ν) * m = ∫⁻ q, ‖q.1‖ₑ ^ s * ‖q.2.1‖ₑ ^ s ∂μX.prod ν := by
          rw [mul_comm]
          exact (lintegral_prod_mul (f := fun x : ℝ => ‖x‖ₑ ^ s)
            (g := fun p : ℝ × ℝ => ‖p.1‖ₑ ^ s) (by fun_prop) (by fun_prop)).symm
      _ ≤ ∫⁻ q, ‖Function.uncurry affine q‖ₑ ^ s ∂μX.prod ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpr0, hpr1] with q h0 h1
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hs.le, ← enorm_mul]
          refine ENNReal.rpow_le_rpow ?_ hs.le
          simp only [Function.uncurry, affine, Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [abs_of_nonneg (mul_nonneg h0 h1.1), abs_of_nonneg (by nlinarith [h1.1, h1.2])]
          nlinarith [h1.1, h1.2]
      _ = m := by
          rw [← lintegral_map (f := fun x : ℝ => ‖x‖ₑ ^ s) (by fun_prop) measurable_affine,
            hinv]
  exact absurd hle (not_le.2 (by
    simpa using ENNReal.mul_lt_mul_left hm0 hmtop hρ))

/-- **Infinite moments above the Kesten exponent** ([Goldie 1991, Theorem 4.1]; [BDM16, §2.4]):
if `A, B ≥ 0` a.s., `B` is not a.s. `0`, `E A^κ = 1` for some `κ > 0` with `A` not a.s. `1`,
`E log A < 0` and `E log⁺ B < ∞`, then `E X^s = ∞` for every `s > κ`. Together with
`lintegral_enorm_rpow_stationaryLaw_lt_top_of_lt`, `κ` is exactly the moment index of `X`. -/
theorem lintegral_enorm_rpow_stationaryLaw_eq_top_of_lt
    (hA : Integrable (fun p : ℝ × ℝ => log |p.1|) ν) (hneg : ∫ p, log |p.1| ∂ν < 0)
    (hB : Integrable (fun p : ℝ × ℝ => posLog p.2) ν) (hApos : ∀ᵐ p ∂ν, 0 ≤ p.1)
    (hBpos : ∀ᵐ p ∂ν, 0 ≤ p.2) (hB0 : ¬ ∀ᵐ p ∂ν, p.2 = 0) {κ : ℝ} (hκ : 0 < κ)
    (h1 : ∫⁻ p, ‖p.1‖ₑ ^ κ ∂ν = 1) (hnd : ¬ ∀ᵐ p ∂ν, |p.1| = 1) {s : ℝ} (hsκ : κ < s) :
    ∫⁻ x, ‖x‖ₑ ^ s ∂stationaryLaw ν = ∞ :=
  lintegral_enorm_rpow_stationaryLaw_eq_top_of_one_lt hA hneg hB hApos hBpos hB0
    (hκ.trans hsκ) (one_lt_lintegral_enorm_rpow hκ h1 hnd hsκ)

/-! ### Tail bounds from moments and moments from tail bounds -/

section TailMoment

variable {μ : Measure ℝ}

/-- **Markov's inequality** for `|X|^s`: `P(|X| > x) ≤ E|X|^s / x^s`. -/
theorem measure_lt_abs_le_lintegral_div {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    μ {y | x < |y|} ≤ (∫⁻ y, ‖y‖ₑ ^ s ∂μ) / ENNReal.ofReal (x ^ s) := by
  refine (measure_mono fun y (hy : x < |y|) => ?_).trans
    (meas_ge_le_lintegral_div (f := fun y : ℝ => ‖y‖ₑ ^ s) (by fun_prop)
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx s)).ne' ENNReal.ofReal_ne_top)
  show ENNReal.ofReal (x ^ s) ≤ ‖y‖ₑ ^ s
  rw [enorm_rpow_eq_ofReal _ hs.le]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx.le hy.le hs.le)

/-- **Power tail bound from a finite moment**: if `E|X|^s < ∞` then
`P(|X| > x) ≤ C x^{-s}` for all `x > 0`. -/
theorem exists_measure_lt_abs_le_of_lintegral_lt_top {s : ℝ} (hs : 0 < s)
    (h : ∫⁻ y, ‖y‖ₑ ^ s ∂μ < ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → μ {y | x < |y|} ≤ ENNReal.ofReal (C * x ^ (-s)) := by
  refine ⟨(∫⁻ y, ‖y‖ₑ ^ s ∂μ).toReal, ENNReal.toReal_nonneg, fun x hx => ?_⟩
  refine (measure_lt_abs_le_lintegral_div hs hx).trans_eq ?_
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx s
  rw [Real.rpow_neg hx.le, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h.ne,
    ENNReal.ofReal_inv_of_pos hxs, div_eq_mul_inv]

/-- **A finite moment from a power tail bound**: if `P(|X| > x) ≤ C x^{-s}` for all `x ≥ x₀ > 0`,
then `E|X|^r < ∞` for every `0 < r < s`. -/
theorem lintegral_lt_top_of_measure_lt_abs_le [IsProbabilityMeasure μ] {s r C x₀ : ℝ}
    (hr : 0 < r) (hrs : r < s) (hC : 0 ≤ C) (hx₀ : 0 < x₀)
    (h : ∀ x, x₀ ≤ x → μ {y | x < |y|} ≤ ENNReal.ofReal (C * x ^ (-s))) :
    ∫⁻ y, ‖y‖ₑ ^ r ∂μ < ∞ := by
  rw [lintegral_congr fun y => enorm_rpow_eq_ofReal y hr.le,
    lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ fun y => abs_nonneg y)
      (continuous_abs.measurable.aemeasurable) hr]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ioc 0 x₀ ∪ Set.Ioi x₀ := fun t ht => by
    rcases le_or_gt t x₀ with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h
  refine (lintegral_mono_set hsub).trans_lt ((lintegral_union_le _ _ _).trans_lt
    (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
  · have hi : IntegrableOn (fun t : ℝ => t ^ (r - 1)) (Set.Ioc 0 x₀) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx₀.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine (setLIntegral_mono' measurableSet_Ioc fun t _ => ?_).trans_lt
      hi.lintegral_lt_top
    exact mul_le_of_le_one_left (by positivity) prob_le_one
  · have hi : IntegrableOn (fun t : ℝ => C * t ^ (r - s - 1)) (Set.Ioi x₀) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hx₀).const_mul C
    refine (setLIntegral_mono' measurableSet_Ioi fun t (ht : x₀ < t) => ?_).trans_lt
      hi.lintegral_lt_top
    have ht0 : 0 < t := hx₀.trans ht
    refine (show _ ≤ ENNReal.ofReal (C * t ^ (-s)) * ENNReal.ofReal (t ^ (r - 1)) by
      gcongr; exact h t ht.le).trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg ht0.le _)), mul_assoc,
      ← Real.rpow_add ht0]
    ring_nf

end TailMoment

end SRE

end ExtremeValueTheory
