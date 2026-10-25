/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.LinearProcess
import ExtremeValueTheory.RegularVariation.KaramataConverse
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Tails of infinite linear processes with regularly varying noise

Let `(Z_j)_{j ≥ 0}` be iid copies of `Z₀`, with `P(|Z₀| > x)` regularly varying with index `-α`,
`α > 0`, and tail balance `P(Z₀ > x) / P(|Z₀| > x) → p`. Let `(ψ_j)` be real coefficients with

  `∑_j |ψ_j|^δ < ∞` for some `0 < δ < min(α, 1)`.

Then the series `X = ∑_j ψ_j Z_j` converges absolutely almost surely, and

  `P(X > x) / P(|Z₀| > x) → ∑_j |ψ_j|^α (p 1{ψ_j > 0} + (1 - p) 1{ψ_j < 0})`.

This is [EKM, Lemma A3.26] / [DR85] / [KS20, Chapter 15]. For `α < 1` the condition is the
classical summability condition of Cline (1983) and Mikosch–Samorodnitsky (2000) (`δ < α`
implies `δ < 1`). For `α ≥ 1` the condition `δ < 1` is slightly stronger than the optimal
conditions (`δ = 1`, resp. `δ ≤ 2` with centred noise), but it needs **no moment, centering or
independence assumption** for the remainder bound, and it covers all exponentially (and all
`j^{-r}`, `r > 1`) decaying coefficients, in particular the AR(1) coefficients `ψ_j = φ^j`.

## Main results

* `LinearProcess.exists_lintegral_trunc_le`: Karamata's bound
  `E[|Z| 1{|Z| ≤ y}] ≤ K y P(|Z| > y)` for large `y` (`α < 1`).
* `LinearProcess.exists_measure_tsum_gt_le`: the uniform remainder bound for `α < 1`: there are
  `K`, `x₀` with `P(∑_j |c_j| |Z_j| > x) ≤ K (∑_j |c_j|^δ) P(|Z₀| > x)` for `x ≥ x₀`, for every
  coefficient sequence with `|c_j| ≤ 1`.
* `LinearProcess.tsum_mul_le_rpow_tsum`: a weighted Hölder inequality for `ℝ≥0∞`-valued series,
  `∑ a_j y_j ≤ (∑ a_j^{γ + (1-γ) q} y_j^q)^{1/q}` when `∑ a_j^γ ≤ 1`, `0 ≤ γ ≤ 1 ≤ q`.
* `LinearProcess.exists_measure_tsum_gt_le_of_summable_rpow`: the same remainder bound for all `α > 0`
  (`δ < α`, `δ < 1`), for every coefficient sequence with `∑_j |c_j|^δ ≤ 1`.
* `LinearProcess.ae_summable_mul_of_summable_rpow`, `LinearProcess.ae_summable_mul` (`α < 1`): almost
  sure absolute convergence of `∑ ψ_j Z_j`.
* `LinearProcess.tendsto_measureReal_tsum_mul_div_of_summable_rpow`,
  `LinearProcess.tendsto_measureReal_tsum_mul_div` (`α < 1`): the tail asymptotics of `X`.

## Proof

For `α < 1` and the remainder we split on whether some term exceeds `x`:
`P(∑ W_j > x) ≤ ∑ P(W_j > x) + x⁻¹ ∑ E[W_j 1{W_j ≤ x}]`, `W_j = |c_j| |Z_j|`. Potter bounds give
`P(|Z| > x/|c|) ≤ 2 |c|^δ P(|Z| > x)` for `|c| ≤ 1`, and Karamata's theorem gives
`E[|Z| 1{|Z| ≤ y}] ≤ K y P(|Z| > y)` (this is where `α < 1` is used).

For general `α > 0`, put `q = α + 1 - δ > 1` and `β = δ + (1 - δ) q`. By the weighted Hölder
inequality with weights `|c_j|^δ` (summing to at most `1`),
`∑_j |c_j| |Z_j| ≤ (∑_j |c_j|^β |Z_j|^q)^{1/q}`, and the variables `|Z_j|^q` have a regularly
varying tail of index `-α / q`, `α / q < 1`, so the case `α < 1` applies to them with the
exponent `δ / β < α / q`.

The finite moving average `∑_{j < m} ψ_j Z_j` is handled by `tendsto_measureReal_sum_mul_div`,
and the remainder is negligible uniformly as `m → ∞`. The `α < 1` statements are the special
case `δ < α < 1` of the general ones.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtremeValueTheory


/-- Composition with a power: if `f` is regularly varying with index `ρ` and `r > 0`, then
`x ↦ f (x ^ r)` is regularly varying with index `ρ * r`. -/
theorem IsRegularlyVarying.comp_rpow {f : ℝ → ℝ} {ρ r : ℝ} (hf : IsRegularlyVarying f ρ)
    (hr : 0 < r) : IsRegularlyVarying (fun x => f (x ^ r)) (ρ * r) := by
  have ht : Tendsto (fun x : ℝ => x ^ r) atTop atTop := tendsto_rpow_atTop hr
  refine ⟨ht.eventually hf.1, fun c hc => ?_⟩
  have h := (hf.2 (c ^ r) (rpow_pos_of_pos hc r)).comp ht
  rw [← rpow_mul hc.le, mul_comm r ρ] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  simp only [Function.comp, mul_rpow hc.le hx]

namespace LinearProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The tail `x ↦ P(x < |Z|)` is antitone. -/
theorem antitone_measureReal_lt_abs [IsFiniteMeasure P] (Z : Ω → ℝ) :
    Antitone fun x => P.real {ω | x < |Z ω|} := fun _ _ h =>
  measureReal_mono fun _ (hω : _ < _) => lt_of_le_of_lt h hω

/-- **Truncated first moment** (Karamata, `α < 1`): if `P(|Z| > x)` is regularly varying with
index `-α`, `α < 1`, there are `K > 0` and `x₀ > 0` with
`E[|Z| 1{|Z| ≤ y}] ≤ K y P(|Z| > y)` for `y ≥ x₀`. -/
theorem exists_lintegral_trunc_le [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {α : ℝ} (hα1 : α < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z ω|}) (-α)) :
    ∃ K x₀ : ℝ, 0 < K ∧ 0 < x₀ ∧ ∀ y ≥ x₀,
      ∫⁻ ω, ENNReal.ofReal (if |Z ω| ≤ y then |Z ω| else 0) ∂P ≤
        ENNReal.ofReal (K * y * P.real {ω | y < |Z ω|}) := by
  set L : ℝ → ℝ := fun x => P.real {ω | x < |Z ω|} with hL_def
  have hanti : Antitone L := antitone_measureReal_lt_abs Z
  have hK := hL.tendsto_integral_zero_div hanti.measurable (by linarith)
    (fun x => hanti.intervalIntegrable)
  set K := 1 / (-α + 1) + 1 with hK_def
  have hK0 : 0 < K := by
    have : 0 < 1 / (-α + 1) := by apply div_pos one_pos; linarith
    linarith
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ((hK.eventually (gt_mem_nhds (show 1 / (-α + 1) < K by
    linarith))).and (hL.1.and (eventually_gt_atTop 0)))
  refine ⟨K, x₀, hK0, (hx₀ x₀ le_rfl).2.2, fun y hy => ?_⟩
  obtain ⟨hratio, hLy, hy0⟩ := hx₀ y hy
  have hZa : Measurable fun ω => |Z ω| := continuous_abs.measurable.comp hZ
  -- the truncated variable is at most `min |Z| y`
  have h1 : ∫⁻ ω, ENNReal.ofReal (if |Z ω| ≤ y then |Z ω| else 0) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (min |Z ω| y) ∂P := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    split_ifs with h
    · exact le_min le_rfl h
    · exact le_min (abs_nonneg _) hy0.le
  -- layer cake
  have h2 : ∫⁻ ω, ENNReal.ofReal (min |Z ω| y) ∂P ≤
      ∫⁻ t in Ioc 0 y, ENNReal.ofReal (L t) := by
    rw [lintegral_eq_lintegral_meas_lt P (Eventually.of_forall fun ω =>
      le_min (abs_nonneg _) hy0.le) (hZa.min measurable_const).aemeasurable]
    calc ∫⁻ t in Ioi 0, P {a | t < min |Z a| y}
        ≤ ∫⁻ t in Ioi 0, (Iic y).indicator (fun t => ENNReal.ofReal (L t)) t := by
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ Iic y
          · rw [indicator_of_mem ht, hL_def, ofReal_measureReal (measure_ne_top _ _)]
            exact measure_mono fun ω (hω : t < min |Z ω| y) =>
              (show t < |Z ω| from lt_of_lt_of_le hω (min_le_left _ _))
          · rw [indicator_of_notMem ht]
            have : {a | t < min |Z a| y} = ∅ := by
              ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
              exact (min_le_right _ _).trans (not_le.1 (show ¬ t ≤ y from ht)).le
            rw [this, measure_empty]
      _ = ∫⁻ t in Ioc 0 y, ENNReal.ofReal (L t) := by
          rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
            Iic_inter_Ioi]
  have h3 : ∫⁻ t in Ioc 0 y, ENNReal.ofReal (L t) = ENNReal.ofReal (∫ t in (0 : ℝ)..y, L t) := by
    rw [intervalIntegral.integral_of_le hy0.le, ofReal_integral_eq_lintegral_ofReal]
    · exact (hanti.intervalIntegrable (a := 0) (b := y)).1
    · exact Eventually.of_forall fun t => measureReal_nonneg
  refine h1.trans (h2.trans (h3.le.trans (ENNReal.ofReal_le_ofReal ?_)))
  have hpos : 0 < y * L y := mul_pos hy0 hLy
  rw [div_lt_iff₀ hpos] at hratio
  have : (1 / (-α + 1)) * (y * L y) ≤ K * (y * L y) := by
    apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
  rw [mul_assoc]
  linarith

/-- **Per-term bounds.** Under regular variation of `P(|Z| > x)` with index `-α`
(`δ < α < 1`) there are `K > 0`, `x₀ > 0` such that for `x ≥ x₀` and `|c| ≤ 1`:
`P(|c| |Z| > x) ≤ 2 |c|^δ P(|Z| > x)` and `E[|c| |Z| 1{|c| |Z| ≤ x}] ≤ K x |c|^δ P(|Z| > x)`. -/
theorem exists_term_bounds [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {α δ : ℝ} (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z ω|}) (-α)) :
    ∃ K x₀ : ℝ, 0 < K ∧ 0 < x₀ ∧ ∀ x ≥ x₀, ∀ c : ℝ, |c| ≤ 1 →
      P {ω | x < |c| * |Z ω|} ≤ ENNReal.ofReal (2 * |c| ^ δ * P.real {ω | x < |Z ω|}) ∧
      ∫⁻ ω, ENNReal.ofReal (if |c| * |Z ω| ≤ x then |c| * |Z ω| else 0) ∂P ≤
        ENNReal.ofReal (K * x * |c| ^ δ * P.real {ω | x < |Z ω|}) := by
  set L : ℝ → ℝ := fun x => P.real {ω | x < |Z ω|} with hL_def
  have hanti : Antitone L := antitone_measureReal_lt_abs Z
  obtain ⟨K₁, x₁, hK₁, hx₁, hT⟩ := exists_lintegral_trunc_le hZ hα1 hL
  obtain ⟨x₂, hx₂, hpos, hP⟩ := hL.potter_bound (a := 0) (Or.inr (hanti.antitoneOn _))
    (show 0 < α - δ by linarith) one_lt_two
  -- the Potter bound in the form `L (x / c) ≤ 2 c^δ L x`
  have hPot : ∀ x ≥ x₂, ∀ c : ℝ, 0 < c → c ≤ 1 → L (x / c) ≤ 2 * c ^ δ * L x := by
    intro x hx c hc hc1
    have hx0 : 0 < x := hx₂.trans_le hx
    have hxc : x ≤ x / c := le_div_self hx0.le hc hc1
    have h := hP x hx (x / c) (hx.trans hxc)
    have hr : x / c / x = c⁻¹ := by field_simp
    rw [hr, show -α + (α - δ) = -δ by ring, show -α - (α - δ) = -(2 * α - δ) by ring] at h
    have hc1' : 1 ≤ c⁻¹ := one_le_inv₀ hc |>.2 hc1
    rw [max_eq_left (rpow_le_rpow_of_exponent_le hc1' (by linarith)),
      inv_rpow hc.le, ← rpow_neg hc.le, neg_neg, div_le_iff₀ (hpos x hx)] at h
    linarith
  refine ⟨2 * K₁, max x₁ x₂, by positivity, lt_max_of_lt_left hx₁, fun x hx c hc1 => ?_⟩
  have hx0 : 0 < x := hx₁.trans_le ((le_max_left _ _).trans hx)
  rcases (abs_nonneg c).eq_or_lt with hc0 | hc0
  · -- `c = 0`
    rw [← hc0]
    simp only [zero_mul, hx0.not_gt, ofPred_false, measure_empty, zero_le, true_and]
    simp [hx0.le]
  have hxc : x ≤ x / |c| := le_div_self hx0.le hc0 hc1
  have hPc := hPot x ((le_max_right _ _).trans hx) |c| hc0 hc1
  constructor
  · have : {ω | x < |c| * |Z ω|} = {ω | x / |c| < |Z ω|} := by
      ext ω; simp only [mem_ofPred_eq]; rw [div_lt_iff₀' hc0]
    rw [this, ← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hPc
  · have hfun : (fun ω => ENNReal.ofReal (if |c| * |Z ω| ≤ x then |c| * |Z ω| else 0)) =
        fun ω => ENNReal.ofReal |c| * ENNReal.ofReal (if |Z ω| ≤ x / |c| then |Z ω| else 0) := by
      funext ω
      rw [← ENNReal.ofReal_mul hc0.le]
      have : (|Z ω| ≤ x / |c|) ↔ (|c| * |Z ω| ≤ x) := le_div_iff₀' hc0
      by_cases h : |c| * |Z ω| ≤ x
      · simp [h, this.2 h]
      · simp [h, mt this.1 h]
    rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hT' := hT (x / |c|) ((le_max_left _ _).trans (hx.trans hxc))
    calc ENNReal.ofReal |c| * ∫⁻ ω, ENNReal.ofReal (if |Z ω| ≤ x / |c| then |Z ω| else 0) ∂P
        ≤ ENNReal.ofReal |c| * ENNReal.ofReal (K₁ * (x / |c|) * L (x / |c|)) := by gcongr
      _ = ENNReal.ofReal (K₁ * x * L (x / |c|)) := by
          rw [← ENNReal.ofReal_mul hc0.le]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (2 * K₁ * x * |c| ^ δ * L x) := by
          apply ENNReal.ofReal_le_ofReal
          have := mul_le_mul_of_nonneg_left hPc (show 0 ≤ K₁ * x by positivity)
          linarith

/-- **Uniform bound for the remainder of a linear process** (`0 < δ < α < 1`). Let `P(|Z₀| > x)` be
regularly varying with index `-α`. There are `K > 0`, `x₀ > 0` such that for every sequence
`(Z_j)` of identically distributed copies of `Z₀` (no independence needed), every coefficient
sequence `(c_j)` with `|c_j| ≤ 1` and `∑ |c_j|^δ < ∞`, and every `x ≥ x₀`,
`P(∑_j |c_j| |Z_j| > x) ≤ K (∑_j |c_j|^δ) P(|Z₀| > x)` (the series taken in `[0, ∞]`). -/
theorem exists_measure_tsum_gt_le [IsProbabilityMeasure P] {Z₀ : Ω → ℝ} (hZ₀ : Measurable Z₀)
    {α δ : ℝ} (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α)) :
    ∃ K x₀ : ℝ, 0 < K ∧ 0 < x₀ ∧ ∀ Z : ℕ → Ω → ℝ, (∀ j, Measurable (Z j)) →
      (∀ j, IdentDistrib (Z j) Z₀ P P) → ∀ c : ℕ → ℝ, (∀ j, |c j| ≤ 1) →
      Summable (fun j => |c j| ^ δ) → ∀ x ≥ x₀,
      P {ω | ENNReal.ofReal x < ∑' j, ENNReal.ofReal (|c j| * |Z j ω|)} ≤
        ENNReal.ofReal (K * (∑' j, |c j| ^ δ) * P.real {ω | x < |Z₀ ω|}) := by
  obtain ⟨K₁, x₀, hK₁, hx₀, hB⟩ := exists_term_bounds hZ₀ hδα hα1 hL
  refine ⟨2 + K₁, x₀, by positivity, hx₀, fun Z hZ hident c hc1 hcs x hx => ?_⟩
  have hx0 : 0 < x := hx₀.trans_le hx
  set Lx := P.real {ω | x < |Z₀ ω|} with hLx
  have hLx0 : 0 ≤ Lx := measureReal_nonneg
  set S := ∑' j, |c j| ^ δ with hS
  -- the truncated terms
  set T : ℕ → Ω → ℝ≥0∞ := fun j ω =>
    ENNReal.ofReal (if |c j| * |Z j ω| ≤ x then |c j| * |Z j ω| else 0) with hT
  have hTm : ∀ j, Measurable (T j) := fun j =>
    ENNReal.measurable_ofReal.comp (Measurable.ite
      (measurableSet_le (measurable_const.mul (continuous_abs.measurable.comp (hZ j)))
        measurable_const)
      (measurable_const.mul (continuous_abs.measurable.comp (hZ j))) measurable_const)
  have hsub : {ω | ENNReal.ofReal x < ∑' j, ENNReal.ofReal (|c j| * |Z j ω|)} ⊆
      (⋃ j, {ω | x < |c j| * |Z j ω|}) ∪ {ω | ENNReal.ofReal x ≤ ∑' j, T j ω} := by
    intro ω hω
    by_cases h : ∃ j, x < |c j| * |Z j ω|
    · obtain ⟨j, hj⟩ := h
      exact Or.inl (mem_iUnion.2 ⟨j, hj⟩)
    · push Not at h
      refine Or.inr (le_of_lt (?_ : ENNReal.ofReal x < ∑' j, T j ω))
      simp only [mem_ofPred_eq] at hω
      convert hω using 3 with j
      simp [hT, h j]
  -- the first part
  have h1 : P (⋃ j, {ω | x < |c j| * |Z j ω|}) ≤ ENNReal.ofReal (2 * S * Lx) := by
    refine (measure_iUnion_le _).trans ?_
    have heq : ∀ j, P {ω | x < |c j| * |Z j ω|} = P {ω | x < |c j| * |Z₀ ω|} := fun j =>
      ((hident j).comp ((measurable_const_mul |c j|).comp continuous_abs.measurable)
        |>.measure_mem_eq measurableSet_Ioi)
    calc ∑' j, P {ω | x < |c j| * |Z j ω|}
        ≤ ∑' j, ENNReal.ofReal (2 * |c j| ^ δ * Lx) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          rw [heq j]
          exact (hB x hx (c j) (hc1 j)).1
      _ = ENNReal.ofReal (2 * S * Lx) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
            ((hcs.mul_left 2).mul_right Lx), tsum_mul_right, tsum_mul_left]
  -- the second part, by Markov's inequality
  have h2 : P {ω | ENNReal.ofReal x ≤ ∑' j, T j ω} ≤ ENNReal.ofReal (K₁ * S * Lx) := by
    have hm : AEMeasurable (fun ω => ∑' j, T j ω) P :=
      (Measurable.tsum hTm).aemeasurable
    refine (meas_ge_le_lintegral_div hm (by simpa using hx0) ENNReal.ofReal_ne_top).trans ?_
    rw [lintegral_tsum fun j => (hTm j).aemeasurable]
    have heq : ∀ j, ∫⁻ ω, T j ω ∂P =
        ∫⁻ ω, ENNReal.ofReal (if |c j| * |Z₀ ω| ≤ x then |c j| * |Z₀ ω| else 0) ∂P := by
      intro j
      have hg : Measurable fun z : ℝ =>
          ENNReal.ofReal (if |c j| * |z| ≤ x then |c j| * |z| else 0) :=
        ENNReal.measurable_ofReal.comp (Measurable.ite
          (measurableSet_le (measurable_const.mul continuous_abs.measurable) measurable_const)
          (measurable_const.mul continuous_abs.measurable) measurable_const)
      exact ((hident j).comp hg).lintegral_eq
    calc (∑' j, ∫⁻ ω, T j ω ∂P) / ENNReal.ofReal x
        ≤ (∑' j, ENNReal.ofReal (K₁ * x * |c j| ^ δ * Lx)) / ENNReal.ofReal x := by
          gcongr with j
          rw [heq j]
          exact (hB x hx (c j) (hc1 j)).2
      _ = ENNReal.ofReal (K₁ * S * Lx) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
            ((hcs.mul_left (K₁ * x)).mul_right Lx), ← ENNReal.ofReal_div_of_pos hx0]
          congr 1
          rw [tsum_mul_right, tsum_mul_left]
          field_simp
          rw [hS]; ring
  calc P {ω | ENNReal.ofReal x < ∑' j, ENNReal.ofReal (|c j| * |Z j ω|)}
      ≤ P ((⋃ j, {ω | x < |c j| * |Z j ω|}) ∪ {ω | ENNReal.ofReal x ≤ ∑' j, T j ω}) :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * S * Lx) + ENNReal.ofReal (K₁ * S * Lx) :=
        (measure_union_le _ _).trans (add_le_add h1 h2)
    _ = ENNReal.ofReal ((2 + K₁) * S * Lx) := by
        have hS0 : 0 ≤ S := tsum_nonneg fun j => rpow_nonneg (abs_nonneg _) _
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- If `∑_j ofReal(|ψ_{j+m}| |z_{j+m}|) ≤ t` in `[0, ∞]`, then `∑ ψ_j z_j` converges (absolutely)
and differs from its partial sum `∑_{j < m} ψ_j z_j` by at most `t`. -/
theorem abs_tsum_sub_sum_le {ψ z : ℕ → ℝ} {m : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hR : ∑' j, ENNReal.ofReal (|ψ (j + m)| * |z (j + m)|) ≤ ENNReal.ofReal t) :
    Summable (fun j => ψ j * z j) ∧
      |∑' j, ψ j * z j - ∑ j ∈ Finset.range m, ψ j * z j| ≤ t := by
  set f : ℕ → ℝ := fun j => |ψ (j + m)| * |z (j + m)| with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by positivity
  have hne : ∑' j, ENNReal.ofReal (f j) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hR
  have hfs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf0 _)] using this
  have hft : ∑' j, f j ≤ t := by
    have := ENNReal.tsum_toReal_eq (f := fun j => ENNReal.ofReal (f j)) fun _ => ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal (hf0 _)] at this
    rw [← this]
    exact ENNReal.toReal_le_of_le_ofReal ht hR
  have hs' : Summable (fun j => ψ (j + m) * z (j + m)) :=
    Summable.of_norm (by simpa [Real.norm_eq_abs, abs_mul] using hfs)
  have hs : Summable (fun j => ψ j * z j) := (summable_nat_add_iff m).1 hs'
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add m, add_sub_cancel_left]
  refine (Real.norm_eq_abs _ ▸ norm_tsum_le_tsum_norm ?_).trans ?_
  · simpa [Real.norm_eq_abs, abs_mul] using hfs
  · simpa [Real.norm_eq_abs, abs_mul] using hft

/-- The left-over factor of the tail weight lies in `[0, 1]`. -/
theorem tailWeight_nonneg_le {α p ψ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ tailWeight α p ψ ∧ tailWeight α p ψ ≤ |ψ| ^ α := by
  have h0 : 0 ≤ |ψ| ^ α := rpow_nonneg (abs_nonneg _) _
  have hb : 0 ≤ (if 0 < ψ then p else 0) + (if ψ < 0 then 1 - p else 0) ∧
      (if 0 < ψ then p else 0) + (if ψ < 0 then 1 - p else 0) ≤ 1 := by
    rcases lt_trichotomy ψ 0 with h | h | h
    · simp [h, h.not_gt]; constructor <;> linarith
    · simp [h]
    · simp [h, h.not_gt]; constructor <;> linarith
  exact ⟨mul_nonneg h0 hb.1, mul_le_of_le_one_right h0 hb.2⟩

/-- Under tail balance the limit `p` lies in `[0, 1]`. -/
theorem tailBalance_mem_Icc [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hpos : ∀ᶠ x in atTop, 0 < P.real {ω | x < |Z ω|}) {p : ℝ}
    (hp : Tendsto (fun x => P.real {ω | x < Z ω} / P.real {ω | x < |Z ω|}) atTop (𝓝 p)) :
    0 ≤ p ∧ p ≤ 1 := by
  constructor
  · exact ge_of_tendsto hp (Eventually.of_forall fun x => div_nonneg measureReal_nonneg
      measureReal_nonneg)
  · refine le_of_tendsto hp ?_
    filter_upwards [hpos] with x hx
    rw [div_le_one hx]
    exact measureReal_mono fun ω (h : x < Z ω) => (show x < |Z ω| from h.trans_le (le_abs_self _))

/-- The coefficients are eventually bounded by `1` in absolute value. -/
theorem exists_abs_le_one {ψ : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hψ : Summable fun j => |ψ j| ^ δ) :
    ∃ m₀ : ℕ, ∀ j ≥ m₀, |ψ j| ≤ 1 := by
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    ((hψ.tendsto_atTop_zero).eventually (gt_mem_nhds one_pos))
  refine ⟨m₀, fun j hj => ?_⟩
  by_contra h
  push Not at h
  have := one_le_rpow h.le hδ.le
  linarith [hm₀ j hj]

/-- The series of tail weights converges. -/
theorem summable_tailWeight {ψ : ℕ → ℝ} {α δ p : ℝ} (hδ : 0 < δ) (hδα : δ ≤ α) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hψ : Summable fun j => |ψ j| ^ δ) :
    Summable fun j => tailWeight α p (ψ j) := by
  obtain ⟨m₀, hm₀⟩ := exists_abs_le_one hδ hψ
  refine (summable_nat_add_iff m₀).1 (Summable.of_nonneg_of_le
    (fun j => (tailWeight_nonneg_le hp0 hp1).1) (fun j => ?_) ((summable_nat_add_iff m₀).2 hψ))
  exact (tailWeight_nonneg_le hp0 hp1).2.trans (rpow_le_rpow_of_exponent_ge' (abs_nonneg _)
    (hm₀ _ (Nat.le_add_left _ _)) hδ.le hδα)

/-- **Weighted Hölder inequality for series in `ℝ≥0∞`**: if `∑_j a_j^γ ≤ 1`, `0 ≤ γ ≤ 1 ≤ q`,
then `∑_j a_j y_j ≤ (∑_j a_j^{γ + (1 - γ) q} y_j^q)^{1/q}`. -/
theorem tsum_mul_le_rpow_tsum {a y : ℕ → ℝ≥0∞} {γ q : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hq : 1 ≤ q) (ha : ∑' j, a j ^ γ ≤ 1) :
    ∑' j, a j * y j ≤ (∑' j, a j ^ (γ + (1 - γ) * q) * y j ^ q) ^ q⁻¹ := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have h1γ : 0 ≤ 1 - γ := by linarith
  have hsplit : ∀ j, a j * y j = a j ^ γ * (a j ^ (1 - γ) * y j) := fun j => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hγ0 h1γ, add_sub_cancel, ENNReal.rpow_one]
  have hpow : ∀ j, a j ^ γ * (a j ^ (1 - γ) * y j) ^ q = a j ^ (γ + (1 - γ) * q) * y j ^ q :=
    fun j => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ hγ0 (mul_nonneg h1γ hq0.le)]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  simp only [hsplit]
  refine (ENNReal.inner_le_weight_mul_Lp_of_nonneg s hq (fun j => a j ^ γ)
    (fun j => a j ^ (1 - γ) * y j)).trans ?_
  have hw : (∑ j ∈ s, a j ^ γ) ^ (1 - q⁻¹) ≤ 1 :=
    ENNReal.rpow_le_one ((ENNReal.sum_le_tsum s).trans ha)
      (sub_nonneg.2 (inv_le_one_of_one_le₀ hq))
  simp only [hpow]
  calc (∑ j ∈ s, a j ^ γ) ^ (1 - q⁻¹) * (∑ j ∈ s, a j ^ (γ + (1 - γ) * q) * y j ^ q) ^ q⁻¹
      ≤ 1 * (∑' j, a j ^ (γ + (1 - γ) * q) * y j ^ q) ^ q⁻¹ := by
        gcongr
        exact ENNReal.sum_le_tsum s
    _ = _ := one_mul _


/-- The tails `∑_{j ≥ m} |ψ_j|^δ` of a convergent series are eventually at most `1`. -/
theorem exists_tsum_add_le_one (ψ : ℕ → ℝ) (δ : ℝ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∑' j, |ψ (j + m)| ^ δ ≤ 1 := by
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    ((tendsto_sum_nat_add fun j => |ψ j| ^ δ).eventually (ge_mem_nhds zero_lt_one))
  exact ⟨m₀, hm₀⟩

/-- **Uniform bound for the remainder of a linear process, all `α > 0`** (`0 < δ < α`,
`δ < 1`). Let `P(|Z₀| > x)` be regularly varying with index `-α`. There are `K > 0`, `x₀ > 0` such
that for every sequence `(Z_j)` of identically distributed copies of `Z₀` (no independence, no
moment assumption), every coefficient sequence `(c_j)` with `∑ |c_j|^δ ≤ 1`, and every `x ≥ x₀`,
`P(∑_j |c_j| |Z_j| > x) ≤ K (∑_j |c_j|^δ) P(|Z₀| > x)` (the series taken in `[0, ∞]`).

Proof: weighted Hölder (`tsum_mul_le_rpow_tsum`) with `q = α + 1 - δ` reduces this to the case
`α / q < 1` of `exists_measure_tsum_gt_le`, applied to the variables `|Z_j|^q`. -/
theorem exists_measure_tsum_gt_le_of_summable_rpow [IsProbabilityMeasure P] {Z₀ : Ω → ℝ}
    (hZ₀ : Measurable Z₀) {α δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α)) :
    ∃ K x₀ : ℝ, 0 < K ∧ 0 < x₀ ∧ ∀ Z : ℕ → Ω → ℝ, (∀ j, Measurable (Z j)) →
      (∀ j, IdentDistrib (Z j) Z₀ P P) → ∀ c : ℕ → ℝ, Summable (fun j => |c j| ^ δ) →
      ∑' j, |c j| ^ δ ≤ 1 → ∀ x ≥ x₀,
      P {ω | ENNReal.ofReal x < ∑' j, ENNReal.ofReal (|c j| * |Z j ω|)} ≤
        ENNReal.ofReal (K * (∑' j, |c j| ^ δ) * P.real {ω | x < |Z₀ ω|}) := by
  set q := α + 1 - δ with hq_def
  have hq1 : 1 < q := by rw [hq_def]; linarith
  have hq0 : 0 < q := zero_lt_one.trans hq1
  set β := δ + (1 - δ) * q with hβ_def
  have hβ : 0 < β := by rw [hβ_def]; nlinarith
  -- the exponents for the powers `|Z_j|^q`
  have hα'1 : α / q < 1 := by rw [div_lt_one hq0, hq_def]; linarith
  have hδ'α' : δ / β < α / q := by
    rw [div_lt_div_iff₀ hβ hq0]
    have : 0 < (1 - δ) * (α + 1) * (α - δ) := by
      apply mul_pos (mul_pos _ _) <;> linarith
    have e : α * β - δ * q = (1 - δ) * (α + 1) * (α - δ) := by rw [hβ_def, hq_def]; ring
    linarith
  set Y₀ : Ω → ℝ := fun ω => |Z₀ ω| ^ q with hY₀_def
  have hY₀ : Measurable Y₀ := (continuous_abs.measurable.comp hZ₀).pow_const q
  have hset : ∀ (V : Ω → ℝ) {x : ℝ}, 0 ≤ x →
      {ω | x ^ q < |(|V ω| ^ q)|} = {ω | x < |V ω|} := by
    intro V x hx
    ext ω
    simp only [mem_ofPred_eq, abs_of_nonneg (rpow_nonneg (abs_nonneg (V ω)) q)]
    exact rpow_lt_rpow_iff hx (abs_nonneg _) hq0
  have hLY : IsRegularlyVarying (fun x => P.real {ω | x < |Y₀ ω|}) (-(α / q)) := by
    have h := hL.comp_rpow (inv_pos.2 hq0)
    rw [show -α * q⁻¹ = -(α / q) by ring] at h
    refine h.congr ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := hset Z₀ (rpow_nonneg hx q⁻¹)
    rw [rpow_inv_rpow hx hq0.ne'] at this
    simp only [hY₀_def, this]
  obtain ⟨K, x₁, hK, hx₁, hR⟩ := exists_measure_tsum_gt_le hY₀ hδ'α' hα'1 hLY
  refine ⟨K, max 1 x₁, hK, lt_max_of_lt_left one_pos, fun Z hZ hident c hcs hc1 x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hxq : x₁ ≤ x ^ q := ((le_max_right _ _).trans hx).trans
    (by simpa using rpow_le_rpow_of_exponent_le hx1 hq1.le)
  have hcj : ∀ j, |c j| ≤ 1 := by
    intro j
    by_contra h
    push Not at h
    have h1 := one_lt_rpow h hδ
    have h2 := hcs.le_tsum j fun i _ => rpow_nonneg (abs_nonneg (c i)) δ
    linarith
  have hcoef : ∀ j, |(|c j| ^ β)| ^ (δ / β) = |c j| ^ δ := fun j => by
    rw [abs_of_nonneg (rpow_nonneg (abs_nonneg _) _), ← rpow_mul (abs_nonneg _),
      mul_div_cancel₀ _ hβ.ne']
  have h := hR (fun j ω => |Z j ω| ^ q)
    (fun j => (continuous_abs.measurable.comp (hZ j)).pow_const q)
    (fun j => (hident j).comp (continuous_abs.measurable.pow_const q)) (fun j => |c j| ^ β)
    (fun j => by
      rw [abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
      exact rpow_le_one (abs_nonneg _) (hcj j) hβ.le)
    (hcs.congr fun j => (hcoef j).symm) (x ^ q) hxq
  simp only [hcoef] at h
  rw [show {ω | x ^ q < |Y₀ ω|} = {ω | x < |Z₀ ω|} from hset Z₀ hx0] at h
  refine le_trans (measure_mono fun ω hω => ?_) h
  simp only [mem_ofPred_eq] at hω ⊢
  -- weighted Hölder
  have ha : ∑' j, ENNReal.ofReal |c j| ^ δ ≤ 1 := by
    simp only [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hδ.le]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => rpow_nonneg (abs_nonneg _) _) hcs]
    exact ENNReal.ofReal_le_one.2 hc1
  have hH := tsum_mul_le_rpow_tsum (a := fun j => ENNReal.ofReal |c j|)
    (y := fun j => ENNReal.ofReal |Z j ω|) hδ.le hδ1.le hq1.le ha
  have hterm : ∀ j, ENNReal.ofReal |c j| ^ (δ + (1 - δ) * q) * ENNReal.ofReal |Z j ω| ^ q =
      ENNReal.ofReal (|(|c j| ^ β)| * |(|Z j ω| ^ q)|) := fun j => by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hβ.le,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le,
      ← ENNReal.ofReal_mul (rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (rpow_nonneg (abs_nonneg _) _), abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
  simp only [hterm, ← ENNReal.ofReal_mul (abs_nonneg _)] at hH
  have h3 := ENNReal.rpow_lt_rpow (hω.trans_le hH) hq0
  rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hx0 hq0.le] at h3

/-- **Almost sure convergence of the linear process, all `α > 0`** (`0 < δ < α`, `δ < 1`): if
`(Z_j)` are identically distributed copies of `Z₀` with `P(|Z₀| > x)` regularly varying with
index `-α` and `∑ |ψ_j|^δ < ∞`, then `∑ ψ_j Z_j` converges absolutely almost surely. No
independence, moment or centering assumption is needed. -/
theorem ae_summable_mul_of_summable_rpow [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ} {Z₀ : Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hZ₀ : Measurable Z₀) (hident : ∀ j, IdentDistrib (Z j) Z₀ P P)
    {α δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α))
    {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j| ^ δ) :
    ∀ᵐ ω ∂P, Summable fun j => ψ j * Z j ω := by
  obtain ⟨K, x₀, hK, hx₀, hR⟩ := exists_measure_tsum_gt_le_of_summable_rpow hZ₀ hδ hδα hδ1 hL
  obtain ⟨m₀, hm₀⟩ := exists_tsum_add_le_one ψ δ
  have hR' := hR (fun j => Z (j + m₀)) (fun j => hZ _) (fun j => hident _) (fun j => ψ (j + m₀))
    ((summable_nat_add_iff m₀).2 hψ) (hm₀ m₀ le_rfl)
  set T := ∑' j, |ψ (j + m₀)| ^ δ
  set R : Ω → ℝ≥0∞ := fun ω => ∑' j, ENNReal.ofReal (|ψ (j + m₀)| * |Z (j + m₀) ω|)
  have hnull : P {ω | R ω = ⊤} = 0 := by
    refine le_antisymm ?_ zero_le
    have hlim : Tendsto (fun x => ENNReal.ofReal (K * T * P.real {ω | x < |Z₀ ω|})) atTop
        (𝓝 (ENNReal.ofReal (K * T * 0))) :=
      ENNReal.tendsto_ofReal (tendsto_const_nhds.mul
        (tendsto_measureReal_lt (continuous_abs.measurable.comp hZ₀)))
    rw [mul_zero, ENNReal.ofReal_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop x₀] with x hx
    exact (measure_mono fun ω (hω : R ω = ⊤) => (show ENNReal.ofReal x < R ω by
      rw [hω]; exact ENNReal.ofReal_lt_top)).trans (hR' x hx)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hne
  exact hω (abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z j ω) (m := m₀) ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal hne).ge).1

/-- **Tails of infinite moving averages with regularly varying noise, all `α > 0`** ([EKM, Lemma
A3.26], [DR85], [Mikosch–Samorodnitsky 2000], [KS20, Chapter 15]). Let `(Z_j)_{j ≥ 0}` be
independent copies of `Z₀`, with `P(|Z₀| > x)` regularly varying with index `-α`, `α > 0`, and
tail balance `P(Z₀ > x) / P(|Z₀| > x) → p`. If `∑ |ψ_j|^δ < ∞` for some `0 < δ < α` with `δ < 1`, then
`X = ∑_j ψ_j Z_j` (which converges absolutely almost surely, `ae_summable_mul_of_summable_rpow`)
satisfies `P(X > x) / P(|Z₀| > x) → ∑_j |ψ_j|^α (p 1{ψ_j > 0} + (1 - p) 1{ψ_j < 0})`.
No moment or centering assumption on `Z₀` is needed. -/
theorem tendsto_measureReal_tsum_mul_div_of_summable_rpow [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ}
    {Z₀ : Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hZ₀ : Measurable Z₀) (hind : iIndepFun Z P)
    (hident : ∀ j, IdentDistrib (Z j) Z₀ P P) {α δ p : ℝ} (hδ : 0 < δ) (hδα : δ < α)
    (hδ1 : δ < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α))
    (hp : Tendsto (fun x => P.real {ω | x < Z₀ ω} / P.real {ω | x < |Z₀ ω|}) atTop (𝓝 p))
    {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j| ^ δ) :
    Tendsto (fun x => P.real {ω | x < ∑' j, ψ j * Z j ω} / P.real {ω | x < |Z₀ ω|}) atTop
      (𝓝 (∑' j, tailWeight α p (ψ j))) := by
  set L : ℝ → ℝ := fun x => P.real {ω | x < |Z₀ ω|} with hL_def
  obtain ⟨hp0, hp1⟩ := tailBalance_mem_Icc hL.1 hp
  obtain ⟨K, x₀, hK, hx₀, hR⟩ := exists_measure_tsum_gt_le_of_summable_rpow hZ₀ hδ hδα hδ1 hL
  obtain ⟨m₀, hm₀⟩ := exists_tsum_add_le_one ψ δ
  set w : ℕ → ℝ := fun j => tailWeight α p (ψ j) with hw_def
  have hw0 : ∀ j, 0 ≤ w j := fun j => (tailWeight_nonneg_le hp0 hp1).1
  have hws : Summable w := summable_tailWeight hδ hδα.le hp0 hp1 hψ
  set c := ∑' j, w j with hc_def
  -- the remainders
  set T : ℕ → ℝ := fun m => ∑' j, |ψ (j + m)| ^ δ with hT_def
  have hT : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add fun j => |ψ j| ^ δ
  set R : ℕ → Ω → ℝ≥0∞ := fun m ω => ∑' j, ENNReal.ofReal (|ψ (j + m)| * |Z (j + m) ω|)
    with hR_def
  -- the remainder bound, in real form
  have hRb : ∀ m ≥ m₀, ∀ y ≥ x₀, P.real {ω | ENNReal.ofReal y < R m ω} ≤ K * T m * L y := by
    intro m hm y hy
    have h := hR (fun j => Z (j + m)) (fun j => hZ _) (fun j => hident _) (fun j => ψ (j + m))
      ((summable_nat_add_iff m).2 hψ) (hm₀ m hm) y hy
    have hT0 : 0 ≤ T m := tsum_nonneg fun j => rpow_nonneg (abs_nonneg _) _
    exact ENNReal.toReal_le_of_le_ofReal (by have := hK.le; positivity) h
  -- the remainder is negligible
  have hRlim : ∀ m ≥ m₀, ∀ {ε : ℝ}, 0 < ε → ∀ {D : ℝ}, K * T m * ε ^ (-α) < D →
      ∀ᶠ x in atTop, P.real {ω | ENNReal.ofReal (ε * x) < R m ω} / L x < D := by
    intro m hm ε hε D hD
    have hlim : Tendsto (fun x => K * T m * (L (ε * x) / L x)) atTop
        (𝓝 (K * T m * ε ^ (-α))) := tendsto_const_nhds.mul (hL.2 ε hε)
    filter_upwards [hlim.eventually (gt_mem_nhds hD), hL.1,
      (tendsto_id.const_mul_atTop hε).eventually (eventually_ge_atTop x₀)] with x hx hLx hεx
    refine lt_of_le_of_lt ?_ hx
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hLx]
    exact hRb m hm _ hεx
  -- finite moving averages
  have hfin : ∀ m : ℕ, Tendsto (fun x => P.real {ω | x < ∑ j ∈ Finset.range m, ψ j * Z j ω} /
      L x) atTop (𝓝 (∑ j ∈ Finset.range m, w j)) := fun m =>
    tendsto_measureReal_sum_mul_div hZ hZ₀ hind hident hL hp ψ _
  have hcm : Tendsto (fun m => ∑ j ∈ Finset.range m, w j) atTop (𝓝 c) :=
    hws.hasSum.tendsto_sum_nat
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro A hA
    obtain ⟨ε, hε, -, hAε⟩ := exists_eps' (α := α) hA
    set D := c * (1 + ε) ^ (-α) - A with hD
    have hD0 : 0 < D := by rw [hD]; linarith
    have hm1 : ∀ᶠ m in atTop, A + D / 2 < (∑ j ∈ Finset.range m, w j) * (1 + ε) ^ (-α) := by
      have := hcm.mul_const ((1 + ε) ^ (-α))
      exact this.eventually (lt_mem_nhds (by rw [hD]; linarith))
    have hm2 : ∀ᶠ m in atTop, K * T m * ε ^ (-α) < D / 4 := by
      have : Tendsto (fun m => K * T m * ε ^ (-α)) atTop (𝓝 (K * 0 * ε ^ (-α))) :=
        (tendsto_const_nhds.mul hT).mul_const _
      rw [mul_zero, zero_mul] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm1, hm2, hm⟩ := (hm1.and (hm2.and (eventually_ge_atTop m₀))).exists
    have hS := tendsto_comp_mul_div hL (hfin m) (show (0 : ℝ) < 1 + ε by linarith)
    filter_upwards [hS.eventually (lt_mem_nhds hm1), hRlim m hm hε hm2, hL.1,
      eventually_ge_atTop 0] with x hx1 hx2 hLx hx0
    have hsub : {ω | (1 + ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} ⊆
        {ω | x < ∑' j, ψ j * Z j ω} ∪ {ω | ENNReal.ofReal (ε * x) < R m ω} := by
      intro ω hω
      simp only [mem_ofPred_eq, mem_union] at hω ⊢
      by_cases h : ENNReal.ofReal (ε * x) < R m ω
      · exact Or.inr h
      · left
        have := (abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z j ω) (m := m)
          (by positivity) (not_lt.1 h)).2
        rw [abs_le] at this
        linarith
    have hle := (measureReal_mono (μ := P) hsub (measure_ne_top P _)).trans
      (measureReal_union_le _ _)
    have : P.real {ω | (1 + ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} / L x ≤
        P.real {ω | x < ∑' j, ψ j * Z j ω} / L x +
          P.real {ω | ENNReal.ofReal (ε * x) < R m ω} / L x := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hle hLx.le
    linarith
  · -- upper bound
    intro B hB
    obtain ⟨ε, hε, hε1, -, hBε⟩ := exists_eps (c := c) (α := α) 1 hB
    rw [one_mul] at hBε
    set D := B - c * (1 - ε) ^ (-α) with hD
    have hD0 : 0 < D := by rw [hD]; linarith
    have hm2 : ∀ᶠ m in atTop, K * T m * ε ^ (-α) < D / 2 := by
      have : Tendsto (fun m => K * T m * ε ^ (-α)) atTop (𝓝 (K * 0 * ε ^ (-α))) :=
        (tendsto_const_nhds.mul hT).mul_const _
      rw [mul_zero, zero_mul] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm2, hm⟩ := (hm2.and (eventually_ge_atTop m₀)).exists
    have hcm_le : (∑ j ∈ Finset.range m, w j) * (1 - ε) ^ (-α) ≤ c * (1 - ε) ^ (-α) :=
      mul_le_mul_of_nonneg_right (hws.sum_le_tsum _ fun j _ => hw0 j)
        (rpow_nonneg (by linarith) _)
    have hS := tendsto_comp_mul_div hL (hfin m) (show (0 : ℝ) < 1 - ε by linarith)
    filter_upwards [hS.eventually (gt_mem_nhds (show _ < B - D / 2 by rw [hD] at *; linarith)),
      hRlim m hm hε hm2, hL.1, eventually_ge_atTop 0] with x hx1 hx2 hLx hx0
    have hsub : {ω | x < ∑' j, ψ j * Z j ω} ⊆
        {ω | (1 - ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} ∪
          {ω | ENNReal.ofReal (ε * x) < R m ω} := by
      intro ω hω
      simp only [mem_ofPred_eq, mem_union] at hω ⊢
      by_cases h : ENNReal.ofReal (ε * x) < R m ω
      · exact Or.inr h
      · left
        have := (abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z j ω) (m := m)
          (by positivity) (not_lt.1 h)).2
        rw [abs_le] at this
        linarith
    have hle := (measureReal_mono (μ := P) hsub (measure_ne_top P _)).trans
      (measureReal_union_le _ _)
    have : P.real {ω | x < ∑' j, ψ j * Z j ω} / L x ≤
        P.real {ω | (1 - ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} / L x +
          P.real {ω | ENNReal.ofReal (ε * x) < R m ω} / L x := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hle hLx.le
    linarith

/-! ### The case `α < 1` -/

/-- **Almost sure convergence of the linear process** (`0 < δ < α < 1`): if `(Z_j)` are copies
of `Z₀` with `P(|Z₀| > x)` regularly varying with index `-α` and `∑ |ψ_j|^δ < ∞`, then
`∑ ψ_j Z_j` converges absolutely almost surely. The case `α < 1` of `ae_summable_mul_of_summable_rpow`. -/
theorem ae_summable_mul [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ} {Z₀ : Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hZ₀ : Measurable Z₀) (hident : ∀ j, IdentDistrib (Z j) Z₀ P P)
    {α δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α))
    {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j| ^ δ) :
    ∀ᵐ ω ∂P, Summable fun j => ψ j * Z j ω :=
  ae_summable_mul_of_summable_rpow hZ hZ₀ hident hδ hδα (hδα.trans hα1) hL hψ

/-- **Tails of infinite moving averages with regularly varying noise, `α < 1`** ([EKM, Lemma
A3.26], [DR85], [KS20, Chapter 15]). Let `(Z_j)_{j ≥ 0}` be independent copies of `Z₀`, with
`P(|Z₀| > x)` regularly varying with index `-α`, `0 < δ < α < 1`, and tail balance
`P(Z₀ > x) / P(|Z₀| > x) → p`. If `∑ |ψ_j|^δ < ∞`, then `X = ∑_j ψ_j Z_j` (which converges
absolutely almost surely, `ae_summable_mul`) satisfies
`P(X > x) / P(|Z₀| > x) → ∑_j |ψ_j|^α (p 1{ψ_j > 0} + (1 - p) 1{ψ_j < 0})`. The case `α < 1` of
`tendsto_measureReal_tsum_mul_div_of_summable_rpow`. -/
theorem tendsto_measureReal_tsum_mul_div [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ} {Z₀ : Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hZ₀ : Measurable Z₀) (hind : iIndepFun Z P)
    (hident : ∀ j, IdentDistrib (Z j) Z₀ P P) {α δ p : ℝ} (hδ : 0 < δ) (hδα : δ < α)
    (hα1 : α < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α))
    (hp : Tendsto (fun x => P.real {ω | x < Z₀ ω} / P.real {ω | x < |Z₀ ω|}) atTop (𝓝 p))
    {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j| ^ δ) :
    Tendsto (fun x => P.real {ω | x < ∑' j, ψ j * Z j ω} / P.real {ω | x < |Z₀ ω|}) atTop
      (𝓝 (∑' j, tailWeight α p (ψ j))) :=
  tendsto_measureReal_tsum_mul_div_of_summable_rpow hZ hZ₀ hind hident hδ hδα (hδα.trans hα1) hL hp hψ

end LinearProcess

end ExtremeValueTheory

/-! ### Deprecated names -/

namespace ExtremeValueTheory.LinearProcess

@[deprecated (since := "2026-10-23")] alias exists_measure_tsum_gt_le_of_lt_one := exists_measure_tsum_gt_le_of_summable_rpow
@[deprecated (since := "2026-10-23")] alias ae_summable_mul_of_lt_one := ae_summable_mul_of_summable_rpow
@[deprecated (since := "2026-10-23")] alias tendsto_measureReal_tsum_mul_div_of_lt_one := tendsto_measureReal_tsum_mul_div_of_summable_rpow

end ExtremeValueTheory.LinearProcess
