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

instance (hu : 0 < G u) : IsLocallyFiniteMeasure (exceedanceMeasure G hu) := by
  unfold exceedanceMeasure; infer_instance

instance (hu : 0 < G u) : SigmaFinite (exceedanceMeasure G hu) := by
  unfold exceedanceMeasure; infer_instance

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

/-- The number of time points `(i + 1) / n`, `i < n`, in the interval `(s, t] ⊆ [0, 1]` is
`⌊n t⌋ - ⌊n s⌋`. -/
lemma card_filter_range_add_one_div_mem_Ioc {n : ℕ} (hn : 0 < n) {s t : ℝ} (hs : 0 ≤ s)
    (ht : t ≤ 1) :
    #{i ∈ range n | (((i : ℕ) : ℝ) + 1) / n ∈ Set.Ioc s t} = ⌊n * t⌋₊ - ⌊n * s⌋₊ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [← Nat.card_Ico]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioc, Finset.mem_Ico]
  have h1 : ((i : ℝ) + 1) / n ≤ t ↔ i < ⌊n * t⌋₊ := by
    rw [div_le_iff₀ hn', Nat.lt_iff_add_one_le]
    by_cases hnt : 0 ≤ n * t
    · rw [Nat.le_floor_iff hnt]
      push_cast
      rw [mul_comm]
    · push Not at hnt
      rw [Nat.floor_of_nonpos hnt.le]
      constructor
      · intro h
        nlinarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
      · intro h
        omega
  have h2 : s < ((i : ℝ) + 1) / n ↔ ⌊n * s⌋₊ ≤ i := by
    rw [lt_div_iff₀ hn', ← not_lt, Nat.lt_iff_add_one_le, Nat.le_floor_iff (by positivity),
      not_le]
    push_cast
    rw [mul_comm]
  rw [h1, h2]
  constructor
  · rintro ⟨-, h, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨?_, h, h'⟩
    have : ⌊n * t⌋₊ ≤ n := by
      refine Nat.floor_le_of_le ?_
      nlinarith
    omega

/-- The proportion of the time points `(i + 1) / n`, `i < n`, in `(s, t] ⊆ [0, 1]` tends to
`t - s`. -/
lemma tendsto_card_filter_range_add_one_div_mem_Ioc {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1) :
    Tendsto (fun n : ℕ ↦ (#{i ∈ range n | (((i : ℕ) : ℝ) + 1) / n ∈ Set.Ioc s t} : ℝ) / n) atTop
      (𝓝 (t - s)) := by
  have hT := (tendsto_nat_floor_mul_div_atTop (hs.trans hst)).comp tendsto_natCast_atTop_atTop
  have hS := (tendsto_nat_floor_mul_div_atTop hs).comp tendsto_natCast_atTop_atTop
  refine (hT.sub hS).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [Function.comp_apply]
  rw [card_filter_range_add_one_div_mem_Ioc hn hs ht, Nat.cast_sub, sub_div, mul_comm t,
    mul_comm s]
  exact Nat.floor_le_floor (by gcongr)

/-- **Convergence of the point process of exceedances, time-space version**
([Resnick, Corollary 4.19], [EKM, Theorem 5.3.2]). Let `X_0, X_1, …` be iid with c.d.f. `F` in
the maximum domain of attraction of `G` with normalizations `A_n`, and let `u` be a threshold
with `G u > 0`. Let `N'` be a Poisson random measure on `ℝ × ℝ` with intensity
`Leb|_{(0, 1]} × μ_G`, where `μ_G` is the exponent measure above `u`. Then the point processes
`N_n = ∑_{i < n} δ_{((i + 1) / n, A_n (X_i))}` converge to `N'` in the sense of
finite-dimensional distributions of counts on disjoint rectangles `(s, t] × C` with
`0 ≤ s ≤ t ≤ 1` and `C` an exceedance interval. -/
theorem tendsto_measureReal_sumDiracRange_timeSpace_eq (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x)
    (hlim : ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) (hu : 0 < G u)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {N' : Ω' → Measure (ℝ × ℝ)} {P' : Measure Ω'}
    (hN' : IsPoissonRandomMeasure N'
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (exceedanceMeasure G hu)) P')
    {k : ℕ} {s t : Fin k → ℝ} {C : Fin k → Set ℝ} (hs : ∀ j, 0 ≤ s j) (hst : ∀ j, s j ≤ t j)
    (ht : ∀ j, t j ≤ 1) (hC : ∀ j, IsExceedanceInterval G u (C j))
    (hd : Pairwise (Function.onFun Disjoint fun j ↦ Set.Ioc (s j) (t j) ×ˢ C j))
    (m : Fin k → ℕ) :
    Tendsto (fun n ↦ P.real {ω | ∀ j, sumDiracRange n (fun i ↦ (((i : ℝ) + 1) / n, As n (X i ω)))
        (Set.Ioc (s j) (t j) ×ˢ C j) = m j}) atTop
      (𝓝 (P'.real {ω | ∀ j, N' ω (Set.Ioc (s j) (t j) ×ˢ C j) = m j})) := by
  classical
  set B : Fin k → Set (ℝ × ℝ) := fun j ↦ Set.Ioc (s j) (t j) ×ˢ C j with hBdef
  have hBm (j : Fin k) : MeasurableSet (B j) := measurableSet_Ioc.prod (hC j).measurableSet
  have hνB (j : Fin k) : (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (exceedanceMeasure G hu)
      (B j) = ENNReal.ofReal (t j - s j) * exceedanceMeasure G hu (C j) := by
    rw [hBdef, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.2 (Set.Ioc_subset_Ioc (hs j) (ht j)), Real.volume_Ioc]
  have hνB' (j : Fin k) : (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (exceedanceMeasure G hu)
      (B j) ≠ ∞ := by
    rw [hνB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((hC j).exceedanceMeasure_ne_top hu)
  rw [hN'.measureReal_forall_apply_eq hBm hνB' hd]
  -- the probability that the `i`-th point lies in `B j`
  have hpre (n i : ℕ) (j : Fin k) : P.real ((fun ω ↦ (((i : ℝ) + 1) / n, As n (X i ω))) ⁻¹' B j) =
      if ((i : ℝ) + 1) / n ∈ Set.Ioc (s j) (t j) then P.real {ω | As n (X 0 ω) ∈ C j} else 0 := by
    rw [hBdef, Set.mk_preimage_prod, Set.preimage_const]
    split_ifs
    · rw [Set.univ_inter, measureReal_affine_mem_eq hX hF (As n) i (hC j).measurableSet]
      rfl
    · simp
  have h := tendsto_measureReal_card_filter_range_eq (P := fun _ ↦ P)
    (Z := fun n i ω ↦ (((i : ℝ) + 1) / n, As n (X i ω)))
    (fun n i ↦ measurable_const.prodMk ((As n).measurable.comp (hX i)))
    (fun n ↦ hind.comp (fun i y ↦ (((i : ℝ) + 1) / n, As n y))
      fun i ↦ measurable_const.prodMk (As n).measurable) hBm hd
    (r := fun j ↦ ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (exceedanceMeasure G hu)
      (B j)).toNNReal) (fun j ↦ ?_) (fun ε hε ↦ ?_) m
  · convert h using 3 with n
    · ext ω
      refine forall_congr' fun j ↦ ?_
      rw [show Set.Ioc (s j) (t j) ×ˢ C j = B j from rfl, sumDiracRange_apply_eq_card _ _ (hBm j),
        Nat.cast_inj]
      convert Iff.rfl
    · simp [ENNReal.coe_toNNReal_eq_toReal]
  · simp only [hpre, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      ENNReal.coe_toNNReal_eq_toReal, hνB, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.2 (hst j))]
    have hrate := (hC j).tendsto_nat_mul_measureReal hX hF hlim hu 0
    refine ((tendsto_card_filter_range_add_one_div_mem_Ioc (hs j) (hst j) (ht j)).mul
      hrate).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  · have hzero (j : Fin k) : Tendsto (fun n : ℕ ↦ P.real {ω | As n (X 0 ω) ∈ C j}) atTop
        (𝓝 0) := by
      have := ((hC j).tendsto_nat_mul_measureReal hX hF hlim hu 0).div_atTop
        tendsto_natCast_atTop_atTop
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    have hev : ∀ᶠ n in atTop, ∀ j, P.real {ω | As n (X 0 ω) ∈ C j} ≤ ε := by
      rw [eventually_all]
      exact fun j ↦ (hzero j).eventually (eventually_le_nhds hε)
    filter_upwards [hev] with n hn i _ j
    rw [hpre]
    split_ifs
    · exact hn j
    · exact hε.le

end PointProcess

/-! ### Upper order statistics from the point process of exceedances -/

section OrderStatistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {F G : CumulativeDistributionFunction} {As : ℕ → AffineIncrEquiv}

open scoped Classical in
/-- The number of exceedances of the sample `X_0, …, X_{n-1}` as a count over `range n`. -/
lemma exceedCount_eq_card_filter_range (x : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    exceedCount (fun i : Fin n ↦ x i) a = #{i ∈ range n | a < x i} := by
  rw [exceedCount, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.2, hi⟩
  · rintro ⟨hi, h⟩
    exact ⟨⟨i, hi⟩, h, rfl⟩

open scoped Classical in
/-- The `(j+1)`-th largest normalized observation is at most `x` if and only if at most `j`
normalized observations lie in `(x, ∞)`. -/
lemma affine_orderStat_le_iff_card (x : ℕ → ℝ) (A : AffineIncrEquiv) {n j : ℕ} (hj : j < n)
    (a : ℝ) :
    A (orderStat (fun i : Fin n ↦ x i) j) ≤ a ↔ #{i ∈ range n | A (x i) ∈ Set.Ioi a} ≤ j := by
  rw [AffineIncrEquiv.apply_le_iff, orderStat_le_iff _ hj, exceedCount_eq_card_filter_range]
  have : ∀ i, A⁻¹ a < x i ↔ A (x i) ∈ Set.Ioi a := fun i ↦ by
    rw [Set.mem_Ioi, ← not_le, ← not_le, AffineIncrEquiv.apply_le_iff]
  simp_rw [this]

open scoped Classical in
/-- The counts of normalized exceedances of a level `x` with `G x ∈ (0, 1)` are asymptotically
Poisson with mean `-log G(x)`. -/
lemma tendsto_measureReal_card_affine_mem_Ioi_eq (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {x : ℝ}
    (hGx : G x ∈ Set.Ioo 0 1) (hlim : Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x)))
    (m : ℕ) :
    Tendsto (fun n ↦ P.real {ω | #{i ∈ range n | As n (X i ω) ∈ Set.Ioi x} = m}) atTop
      (𝓝 (G x * (-Real.log (G x)) ^ m / m.factorial)) := by
  have hτ : 0 ≤ -Real.log (G x) := neg_nonneg.2 (Real.log_nonpos hGx.1.le hGx.2.le)
  have h := tendsto_measureReal_card_affine_mem_eq (As := As) hX hind hF
    (B := fun _ : Fin 1 ↦ Set.Ioi x) (fun _ ↦ measurableSet_Ioi)
    (fun a b h ↦ (h (Subsingleton.elim a b)).elim)
    (r := fun _ ↦ (-Real.log (G x)).toNNReal) (fun _ ↦ ?_) (fun _ ↦ m)
  · simpa [Real.coe_toNNReal _ hτ, Real.exp_log hGx.1, mul_div_assoc] using h
  · simpa [Real.coe_toNNReal _ hτ] using tendsto_nat_mul_measureReal_lt_affine hX hF hGx hlim 0

open scoped Classical in
/-- **Limit law of the `k`-th largest, from the point process of exceedances.** This rederives
`tendsto_measureReal_affine_orderStat_le` (Poisson limit of the `k`-th largest,
[EKM, Theorem 4.2.3]) from the Poisson limit of the counts of exceedances:
`P(A_n (X_{(j+1)}) ≤ x) = P(N_n (x, ∞) ≤ j) → G(x) ∑_{m ≤ j} (-log G(x)) ^ m / m!`. -/
theorem tendsto_measureReal_affine_orderStat_le_of_pointProcess (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x) {x : ℝ}
    (hGx : G x ∈ Set.Ioo 0 1) (hlim : Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x)))
    (j : ℕ) :
    Tendsto (fun n : ℕ ↦ P.real {ω | As n (orderStat (fun i : Fin n ↦ X i ω) j) ≤ x}) atTop
      (𝓝 (G x * ∑ m ∈ range (j + 1), (-Real.log (G x)) ^ m / m.factorial)) := by
  have hcount (n : ℕ) : Measurable fun ω ↦ #{i ∈ range n | As n (X i ω) ∈ Set.Ioi x} :=
    measurable_card_filter_range (Z := fun i ω ↦ As n (X i ω))
      (fun i ↦ (As n).measurable.comp (hX i)) measurableSet_Ioi n
  have heq : (fun n : ℕ ↦ P.real {ω | As n (orderStat (fun i : Fin n ↦ X i ω) j) ≤ x}) =ᶠ[atTop]
      fun n ↦ ∑ m ∈ range (j + 1),
        P.real {ω | #{i ∈ range n | As n (X i ω) ∈ Set.Ioi x} = m} := by
    filter_upwards [eventually_gt_atTop j] with n hn
    have hset : {ω | As n (orderStat (fun i : Fin n ↦ X i ω) j) ≤ x} =
        ⋃ m ∈ range (j + 1), {ω | #{i ∈ range n | As n (X i ω) ∈ Set.Ioi x} = m} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
        affine_orderStat_le_iff_card (fun i ↦ X i ω) (As n) hn]
      constructor
      · intro h
        exact ⟨_, Nat.lt_succ_of_le h, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact Nat.le_of_lt_succ hm
    rw [hset, measureReal_biUnion_finset]
    · intro a _ b _ hab
      exact Set.disjoint_left.2 fun ω h1 h2 ↦ hab (h1.symm.trans h2)
    · exact fun m _ ↦ hcount n (measurableSet_singleton m)
  refine Tendsto.congr' heq.symm ?_
  rw [Finset.mul_sum]
  refine tendsto_finsetSum _ fun m _ ↦ ?_
  rw [← mul_div_assoc]
  exact tendsto_measureReal_card_affine_mem_Ioi_eq hX hind hF hGx hlim m

open scoped Classical in
/-- **Joint limit law of the two largest, from the point process of exceedances.** This rederives
`tendsto_measureReal_affine_orderStat_zero_one` ([EKM, §4.2], [LLR, Theorem 2.3.2]) from the joint
Poisson limit of the counts of exceedances in the disjoint sets `(x, ∞)` and `(y, x]`:
`P(A_n (X_{(1)}) ≤ x, A_n (X_{(2)}) ≤ y) = P(N_n (x, ∞) = 0, N_n (y, x] ≤ 1)
  → G(y) (1 + log G(x) - log G(y))`. -/
theorem tendsto_measureReal_affine_orderStat_zero_one_of_pointProcess
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hF : ∀ i x, P.real {ω | X i ω ≤ x} = F x)
    {x y : ℝ} (hyx : y ≤ x) (hGx : G x ∈ Set.Ioo 0 1) (hGy : G y ∈ Set.Ioo 0 1)
    (hlimx : Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x)))
    (hlimy : Tendsto (fun n : ℕ ↦ ((As n • F) y) ^ n) atTop (𝓝 (G y))) :
    Tendsto (fun n : ℕ ↦ P.real {ω | As n (orderStat (fun i : Fin n ↦ X i ω) 0) ≤ x ∧
        As n (orderStat (fun i : Fin n ↦ X i ω) 1) ≤ y}) atTop
      (𝓝 (G y * (1 + Real.log (G x) - Real.log (G y)))) := by
  set B : Fin 2 → Set ℝ := ![Set.Ioi x, Set.Ioc y x] with hBdef
  have hBm (l : Fin 2) : MeasurableSet (B l) := by
    fin_cases l
    · exact measurableSet_Ioi
    · exact measurableSet_Ioc
  have hdisj : Disjoint (Set.Ioi x) (Set.Ioc y x) :=
    Set.disjoint_left.2 fun z h1 h2 ↦ absurd h2.2 (not_le.2 h1)
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hab
  set a := -Real.log (G x) with ha
  set b := Real.log (G x) - Real.log (G y) with hb
  have ha0 : 0 ≤ a := neg_nonneg.2 (Real.log_nonpos hGx.1.le hGx.2.le)
  have hb0 : 0 ≤ b := sub_nonneg.2 (Real.log_le_log hGy.1 (G.mono' hyx))
  have hA (m : Fin 2 → ℕ) := tendsto_measureReal_card_affine_mem_eq (As := As) hX hind hF hBm hd
    (r := ![a.toNNReal, b.toNNReal]) (fun l ↦ by
      fin_cases l
      · simpa [hBdef, Real.coe_toNNReal _ ha0] using
          tendsto_nat_mul_measureReal_lt_affine hX hF hGx hlimx 0
      · simpa [hBdef, Real.coe_toNNReal _ hb0] using
          tendsto_nat_mul_measureReal_affine_mem_Ioc hX hF hyx hGy hGx hlimy hlimx 0) m
  have hcount (n : ℕ) (l : Fin 2) :
      Measurable fun ω ↦ #{i ∈ range n | As n (X i ω) ∈ B l} :=
    measurable_card_filter_range (Z := fun i ω ↦ As n (X i ω))
      (fun i ↦ (As n).measurable.comp (hX i)) (hBm l) n
  have hmeas (n : ℕ) (m : Fin 2 → ℕ) :
      MeasurableSet {ω | ∀ l, #{i ∈ range n | As n (X i ω) ∈ B l} = m l} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun l ↦ hcount n l (measurableSet_singleton _)
  have heq : (fun n : ℕ ↦ P.real {ω | As n (orderStat (fun i : Fin n ↦ X i ω) 0) ≤ x ∧
        As n (orderStat (fun i : Fin n ↦ X i ω) 1) ≤ y}) =ᶠ[atTop]
      fun n ↦ P.real {ω | ∀ l, #{i ∈ range n | As n (X i ω) ∈ B l} = ![0, 0] l} +
        P.real {ω | ∀ l, #{i ∈ range n | As n (X i ω) ∈ B l} = ![0, 1] l} := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hsplit (ω : Ω) : #{i ∈ range n | As n (X i ω) ∈ Set.Ioi y} =
        #{i ∈ range n | As n (X i ω) ∈ Set.Ioi x} + #{i ∈ range n | As n (X i ω) ∈ Set.Ioc y x} := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun i _ h1 h2 ↦
        Set.disjoint_left.1 hdisj h1 h2), ← Finset.filter_or]
      congr 1
      refine Finset.filter_congr fun i _ ↦ ?_
      simp only [Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · intro h
        by_cases hx : x < As n (X i ω)
        · exact Or.inl hx
        · exact Or.inr ⟨h, not_lt.1 hx⟩
      · rintro (h | h)
        · exact hyx.trans_lt h
        · exact h.1
    have hset : {ω | As n (orderStat (fun i : Fin n ↦ X i ω) 0) ≤ x ∧
        As n (orderStat (fun i : Fin n ↦ X i ω) 1) ≤ y} =
        {ω | ∀ l, #{i ∈ range n | As n (X i ω) ∈ B l} = ![0, 0] l} ∪
          {ω | ∀ l, #{i ∈ range n | As n (X i ω) ∈ B l} = ![0, 1] l} := by
      ext ω
      have e0 : #{i ∈ range n | As n (X i ω) ∈ Set.Ioi x} =
          #{i ∈ range n | As n (X i ω) ∈ B 0} := by congr!
      have e1 : #{i ∈ range n | As n (X i ω) ∈ Set.Ioc y x} =
          #{i ∈ range n | As n (X i ω) ∈ B 1} := by congr!
      simp only [Set.mem_ofPred_eq, Set.mem_union, Fin.forall_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        affine_orderStat_le_iff_card (fun i ↦ X i ω) (As n) (show 0 < n by omega),
        affine_orderStat_le_iff_card (fun i ↦ X i ω) (As n) hn, hsplit, e0, e1]
      omega
    rw [hset, measureReal_union _ (hmeas n _)]
    exact Set.disjoint_left.2 fun ω h1 h2 ↦ by
      have := (h1 1).symm.trans (h2 1)
      simp at this
  refine Tendsto.congr' heq.symm ?_
  convert (hA ![0, 0]).add (hA ![0, 1]) using 2
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.coe_toNNReal _ ha0, Real.coe_toNNReal _ hb0, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one, mul_one]
  have hexp : Real.exp (-a) * Real.exp (-b) = G y := by
    rw [← Real.exp_add, ha, hb, show -(-Real.log (G x)) + -(Real.log (G x) - Real.log (G y)) =
      Real.log (G y) by ring, Real.exp_log hGy.1]
  rw [show G y * (1 + Real.log (G x) - Real.log (G y)) = G y + G y * b by rw [hb]; ring, ← hexp]
  ring

end OrderStatistics

end ExtremeValueTheory
