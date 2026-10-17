/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.UpperOrderStatistics
import ExtremeValueTheory.ForMathlib.Probability.PointProcessConvergence

/-!
# The point process of exceedances

-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section Rates

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {F : CumulativeDistributionFunction}

/-- An orientation preserving affine map is measurable. -/
lemma _root_.AffineIncrEquiv.measurable (A : AffineIncrEquiv) : Measurable A :=
  A.mono.measurable

/-- `P(x < A (X i)) = 1 - (A • F) x`. -/
lemma measureReal_lt_affine_eq (hX : ∀ i, Measurable (X i))
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) (A : AffineIncrEquiv) (i : ℕ) (x : ℝ) :
    P.real {ω | x < A (X i ω)} = 1 - (A • F) x := by
  have : {ω | x < A (X i ω)} = {ω | X i ω ≤ A⁻¹ x}ᶜ := by
    ext ω
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← AffineIncrEquiv.apply_le_iff,
      not_le]
  rw [this, probReal_compl_eq_one_sub (measurableSet_le (hX i) measurable_const), hF,
    CumulativeDistributionFunction.mulAction_apply_eq]

/-- Random variables with a common c.d.f. have a common law. -/
lemma map_eq_map_zero_of_cdf (hX : ∀ i, Measurable (X i))
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) (i : ℕ) : P.map (X i) = P.map (X 0) := by
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  rw [Measure.map_apply (hX i) measurableSet_Iic, Measure.map_apply (hX 0) measurableSet_Iic,
    ← ofReal_measureReal, ← ofReal_measureReal]
  congr 1
  exact (hF i a).trans (hF 0 a).symm

/-- `P(A (X i) ∈ B) = P(A (X 0) ∈ B)` for random variables with a common c.d.f. -/
lemma measureReal_affine_mem_eq (hX : ∀ i, Measurable (X i))
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) (A : AffineIncrEquiv) (i : ℕ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    P.real ((fun ω ↦ A (X i ω)) ⁻¹' B) = P.real ((fun ω ↦ A (X 0 ω)) ⁻¹' B) := by
  change P.real (X i ⁻¹' (A ⁻¹' B)) = P.real (X 0 ⁻¹' (A ⁻¹' B))
  rw [measureReal_def, measureReal_def, ← Measure.map_apply (hX i) (A.measurable hB),
    ← Measure.map_apply (hX 0) (A.measurable hB), map_eq_map_zero_of_cdf hX hF i]

variable {G : CumulativeDistributionFunction} {As : ℕ → AffineIncrEquiv}

/-- **Exceedance rates.** If `((A_n • F) x) ^ n → G x ∈ (0, 1)`, then the expected number of
normalized observations exceeding `x` converges: `n P(A_n (X i) > x) → -log G(x)`. -/
theorem tendsto_nat_mul_measureReal_lt_affine (hX : ∀ i, Measurable (X i))
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {x : ℝ} (hGx : G x ∈ Set.Ioo 0 1)
    (hlim : Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) (i : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * P.real {ω | x < As n (X i ω)}) atTop
      (𝓝 (-Real.log (G x))) := by
  have h3 := ((tfae_ev_limit_relation As hGx).out 1 3).1 hlim
  simpa only [measureReal_lt_affine_eq hX hF] using h3

/-- **Exceedance rates for intervals.** If `((A_n • F) z) ^ n → G z ∈ (0, 1)` for `z = x, y`
with `x ≤ y`, then `n P(A_n (X i) ∈ (x, y]) → log G(y) - log G(x)`. -/
theorem tendsto_nat_mul_measureReal_affine_mem_Ioc (hX : ∀ i, Measurable (X i))
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {x y : ℝ} (hxy : x ≤ y)
    (hGx : G x ∈ Set.Ioo 0 1) (hGy : G y ∈ Set.Ioo 0 1)
    (hlimx : Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x)))
    (hlimy : Tendsto (fun n : ℕ ↦ ((As n • F) y) ^ n) atTop (𝓝 (G y))) (i : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * P.real {ω | As n (X i ω) ∈ Set.Ioc x y}) atTop
      (𝓝 (Real.log (G y) - Real.log (G x))) := by
  have hx := tendsto_nat_mul_measureReal_lt_affine hX hF hGx hlimx i
  have hy := tendsto_nat_mul_measureReal_lt_affine hX hF hGy hlimy i
  rw [show Real.log (G y) - Real.log (G x) = -Real.log (G x) - -Real.log (G y) by ring]
  refine (hx.sub hy).congr fun n ↦ ?_
  have hset : {ω | As n (X i ω) ∈ Set.Ioc x y} = {ω | x < As n (X i ω)} \ {ω | y < As n (X i ω)} := by
    ext ω
    simp [Set.mem_Ioc, not_lt]
  have hsub : {ω | y < As n (X i ω)} ⊆ {ω | x < As n (X i ω)} := fun ω h ↦
    hxy.trans_lt h
  rw [hset, measureReal_sdiff hsub
    (measurableSet_lt measurable_const ((As n).measurable.comp (hX i)))]
  ring

end Rates

/-! ### Convergence of the counts of exceedances -/

section Counts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {F : CumulativeDistributionFunction} {As : ℕ → AffineIncrEquiv}

open scoped Classical in
/-- **Poisson limit of the counts of normalized observations.** Let `X_0, X_1, …` be iid with
c.d.f. `F` and let `B 0, …, B (k-1)` be disjoint measurable sets such that
`n P(A_n (X_0) ∈ B j) → r j`. Then the counts `#{i < n | A_n (X_i) ∈ B j}` converge jointly in law
to independent Poisson random variables with means `r j`. -/
theorem tendsto_measureReal_card_affine_mem_eq (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {k : ℕ}
    {B : Fin k → Set ℝ} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise (Function.onFun Disjoint B)) {r : Fin k → ℝ≥0}
    (hr : ∀ j, Tendsto (fun n : ℕ ↦ (n : ℝ) * P.real {ω | As n (X 0 ω) ∈ B j}) atTop
      (𝓝 (r j))) (m : Fin k → ℕ) :
    Tendsto (fun n ↦ P.real {ω | ∀ j, #{i ∈ range n | As n (X i ω) ∈ B j} = m j}) atTop
      (𝓝 (∏ j, Real.exp (-r j) * r j ^ m j / (m j).factorial)) := by
  refine tendsto_measureReal_card_filter_range_eq (P := fun _ ↦ P)
    (Z := fun n i ω ↦ As n (X i ω)) (fun n i ↦ (As n).measurable.comp (hX i))
    (fun n ↦ hind.comp (fun _ ↦ As n) fun _ ↦ (As n).measurable) hB hd (fun j ↦ ?_)
    (fun ε hε ↦ ?_) m
  · refine (hr j).congr fun n ↦ ?_
    rw [Finset.sum_congr rfl fun i _ ↦ measureReal_affine_mem_eq hX hF (As n) i (hB j),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rfl
  · have hzero (j : Fin k) : Tendsto (fun n : ℕ ↦ P.real {ω | As n (X 0 ω) ∈ B j}) atTop
        (𝓝 0) := by
      have := (hr j).div_atTop tendsto_natCast_atTop_atTop
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    have hev : ∀ᶠ n in atTop, ∀ j, P.real {ω | As n (X 0 ω) ∈ B j} ≤ ε := by
      rw [eventually_all]
      exact fun j ↦ (hzero j).eventually (eventually_le_nhds hε)
    filter_upwards [hev] with n hn i _ j
    rw [measureReal_affine_mem_eq hX hF (As n) i (hB j)]
    exact hn j

end Counts

end ExtremeValueTheory
