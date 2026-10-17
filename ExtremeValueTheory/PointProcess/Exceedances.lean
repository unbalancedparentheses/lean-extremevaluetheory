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

/-! ### The intensity measure `μ_G (x, ∞) = -log G(x)` -/

section Intensity

variable {G : CumulativeDistributionFunction} {u : ℝ}

/-- The Stieltjes function `x ↦ log G (max x u)`, for a c.d.f. `G` with `G u > 0`. -/
noncomputable def logCDFMax (G : CumulativeDistributionFunction) (hu : 0 < G u) :
    StieltjesFunction ℝ where
  toFun x := Real.log (G (max x u))
  mono' x y hxy := Real.log_le_log (hu.trans_le (G.mono' (le_max_right _ _)))
    (G.mono' (max_le_max hxy le_rfl))
  right_continuous' x := by
    have hG : ContinuousWithinAt G (Set.Ici (max x u)) (max x u) :=
      G.toStieltjesFunction.right_continuous _
    have hmax : ContinuousWithinAt (fun y ↦ max y u) (Set.Ici x) x :=
      (continuous_id.max continuous_const).continuousWithinAt
    have := ContinuousWithinAt.comp (f := fun y ↦ max y u) (x := x) hG hmax
      fun y (hy : x ≤ y) ↦ (max_le_max hy le_rfl : max x u ≤ max y u)
    exact ContinuousAt.comp_continuousWithinAt (g := Real.log)
      (Real.continuousAt_log (hu.trans_le (G.mono' (le_max_right x u))).ne') this

/-- The *exponent measure* of the c.d.f. `G` above the threshold `u` (with `G u > 0`): the measure
on `ℝ` carried by `(u, ∞)` with `μ (a, b] = log G(b) - log G(a)` and `μ (a, ∞) = -log G(a)` for
`u ≤ a ≤ b`. For an extreme value distribution `G`, this is the restriction to `(u, ∞)` of the
intensity measure `μ_G (x, ∞] = -log G(x)` of the limiting Poisson process of exceedances. -/
noncomputable def exceedanceMeasure (G : CumulativeDistributionFunction) (hu : 0 < G u) :
    Measure ℝ :=
  (logCDFMax G hu).measure

lemma exceedanceMeasure_Ioc (hu : 0 < G u) {a b : ℝ} (hua : u ≤ a) (hab : a ≤ b) :
    exceedanceMeasure G hu (Set.Ioc a b) = ENNReal.ofReal (Real.log (G b) - Real.log (G a)) := by
  rw [exceedanceMeasure, StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (Real.log (G (max b u)) - Real.log (G (max a u))) = _
  rw [max_eq_left hua, max_eq_left (hua.trans hab)]

lemma exceedanceMeasure_Ioi (hu : 0 < G u) {a : ℝ} (hua : u ≤ a) :
    exceedanceMeasure G hu (Set.Ioi a) = ENNReal.ofReal (-Real.log (G a)) := by
  have hlim : Tendsto (logCDFMax G hu) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x ↦ G (max x u)) atTop (𝓝 1) :=
      G.tendsto_atTop.comp (tendsto_atTop_mono (fun x ↦ le_max_left x u) tendsto_id)
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp h1
    rw [Real.log_one] at this
    exact this
  rw [exceedanceMeasure, StieltjesFunction.measure_Ioi _ hlim]
  change ENNReal.ofReal (0 - Real.log (G (max a u))) = _
  rw [max_eq_left hua, zero_sub]

/-- The intervals `(a, b]` and `(a, ∞)` above the threshold `u` at whose endpoints
`G ∈ (0, 1)`. These form the class of sets on which the convergence of the point process of
exceedances is stated. -/
def IsExceedanceInterval (G : CumulativeDistributionFunction) (u : ℝ) (B : Set ℝ) : Prop :=
  (∃ a b, u ≤ a ∧ a ≤ b ∧ G a ∈ Set.Ioo 0 1 ∧ G b ∈ Set.Ioo 0 1 ∧ B = Set.Ioc a b) ∨
    ∃ a, u ≤ a ∧ G a ∈ Set.Ioo 0 1 ∧ B = Set.Ioi a

lemma IsExceedanceInterval.measurableSet {B : Set ℝ} (hB : IsExceedanceInterval G u B) :
    MeasurableSet B := by
  rcases hB with ⟨a, b, -, -, -, -, rfl⟩ | ⟨a, -, -, rfl⟩
  · exact measurableSet_Ioc
  · exact measurableSet_Ioi

lemma IsExceedanceInterval.exceedanceMeasure_ne_top (hu : 0 < G u) {B : Set ℝ}
    (hB : IsExceedanceInterval G u B) : exceedanceMeasure G hu B ≠ ∞ := by
  rcases hB with ⟨a, b, hua, hab, -, -, rfl⟩ | ⟨a, hua, -, rfl⟩
  · rw [exceedanceMeasure_Ioc hu hua hab]; exact ENNReal.ofReal_ne_top
  · rw [exceedanceMeasure_Ioi hu hua]; exact ENNReal.ofReal_ne_top

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {F : CumulativeDistributionFunction} {As : ℕ → AffineIncrEquiv}

/-- On exceedance intervals, `n P(A_n (X i) ∈ B) → μ_G(B)`. -/
theorem IsExceedanceInterval.tendsto_nat_mul_measureReal (hX : ∀ i, Measurable (X i))
    (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x)
    (hlim : ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) (hu : 0 < G u)
    {B : Set ℝ} (hB : IsExceedanceInterval G u B) (i : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * P.real {ω | As n (X i ω) ∈ B}) atTop
      (𝓝 (exceedanceMeasure G hu B).toReal) := by
  rcases hB with ⟨a, b, hua, hab, hGa, hGb, rfl⟩ | ⟨a, hua, hGa, rfl⟩
  · rw [exceedanceMeasure_Ioc hu hua hab, ENNReal.toReal_ofReal
      (sub_nonneg.2 (Real.log_le_log hGa.1 (G.mono' hab)))]
    exact tendsto_nat_mul_measureReal_affine_mem_Ioc hX hF hab hGa hGb (hlim a) (hlim b) i
  · rw [exceedanceMeasure_Ioi hu hua, ENNReal.toReal_ofReal
      (neg_nonneg.2 (Real.log_nonpos hGa.1.le hGa.2.le))]
    exact tendsto_nat_mul_measureReal_lt_affine hX hF hGa (hlim a) i

end Intensity

/-! ### Convergence of the point process of exceedances -/

section PointProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {F G : CumulativeDistributionFunction} {As : ℕ → AffineIncrEquiv} {u : ℝ}

/-- **Convergence of the point process of exceedances** ([Resnick, Corollary 4.19],
[EKM, Theorem 5.3.2], space component). Let `X_0, X_1, …` be iid with c.d.f. `F` in the maximum
domain of attraction of `G` with normalizations `A_n`: `((A_n • F) x) ^ n → G x` for every `x`.
Let `u` be a threshold with `G u > 0`, and let `N'` be a Poisson random measure whose intensity is
the exponent measure `μ_G` above `u` (`μ_G (x, ∞) = -log G(x)`). Then the point processes
`N_n = ∑_{i < n} δ_{A_n (X_i)}` converge to `N'` in the sense of finite-dimensional
distributions of counts on disjoint exceedance intervals. -/
theorem tendsto_measureReal_sumDiracRange_affine_eq (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x)
    (hlim : ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) (hu : 0 < G u)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {N' : Ω' → Measure ℝ} {P' : Measure Ω'}
    (hN' : IsPoissonRandomMeasure N' (exceedanceMeasure G hu) P') {k : ℕ} {B : Fin k → Set ℝ}
    (hB : ∀ j, IsExceedanceInterval G u (B j)) (hd : Pairwise (Function.onFun Disjoint B))
    (m : Fin k → ℕ) :
    Tendsto (fun n ↦ P.real {ω | ∀ j, sumDiracRange n (fun i ↦ As n (X i ω)) (B j) = m j})
      atTop (𝓝 (P'.real {ω | ∀ j, N' ω (B j) = m j})) := by
  classical
  have hBm (j : Fin k) : MeasurableSet (B j) := (hB j).measurableSet
  rw [hN'.measureReal_forall_apply_eq hBm (fun j ↦ (hB j).exceedanceMeasure_ne_top hu) hd]
  have h := tendsto_measureReal_card_affine_mem_eq (As := As) hX hind hF hBm hd
    (r := fun j ↦ (exceedanceMeasure G hu (B j)).toNNReal) (fun j ↦ ?_) m
  · convert h using 3 with n
    · ext ω
      simp [sumDiracRange_apply_eq_card _ _ (hBm _)]
    · simp [ENNReal.coe_toNNReal_eq_toReal]
  · simpa [ENNReal.coe_toNNReal_eq_toReal] using
      (hB j).tendsto_nat_mul_measureReal hX hF hlim hu 0

end PointProcess

end ExtremeValueTheory
