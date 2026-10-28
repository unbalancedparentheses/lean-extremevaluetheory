/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.DomainOfAttractionStandardized
import ExtremeValueTheory.Multivariate.TailDependence

/-!
# The stable tail dependence function

Let `μ` be a law on `ℝ^ι` with continuous marginal distribution functions `F_j`. Its **stable tail
dependence function** is

  `ℓ(x) = lim_{t ↓ 0} t⁻¹ P(F_1(X_1) > 1 - t x_1 or … or F_d(X_d) > 1 - t x_d)`,  `x ∈ (0, ∞)^ι`,

where `X ∼ μ` ([dHF, §6.1.5 and §7.2]; [Huang 1992]; [Drees–Huang 1998]; [BGST04, §8.2.2 and
§9.4.1]). It only depends on the copula of `μ` and describes the dependence of `μ` in its joint
upper tail. We record its existence as the predicate `HasStableTailDependence μ ℓ`, for `x` with
positive coordinates.

## Main results

* `measureReal_one_sub_lt_marginal`: for a continuous marginal, `P(F_j(X_j) > 1 - s) = s` for
  `0 < s < 1` (the probability integral transform).
* `HasStableTailDependence.abs_sub_le`: `ℓ` is `1`-Lipschitz for the `ℓ¹` distance,
  `|ℓ(x) - ℓ(y)| ≤ ∑_j |x_j - y_j|`.
* `IsMDAWith.hasStableTailDependence`: **in the domain of attraction**, `ℓ` exists and
  `ℓ(x) = V₀(1 / x_1, …, 1 / x_d)`, where `V₀ = -log G₀` is the exponent function of the unit
  Fréchet standardization `G₀` of the limit ([dHF, Theorem 6.1.1 and (6.1.31)]).
* `HasStableTailDependence.hasUpperTailDependence`: in dimension two the upper tail dependence
  coefficient exists and equals `χ = 2 - ℓ(1, 1)`.
* `IsMDAWith.hasUpperTailDependence`: in the domain of attraction, `χ = 2 - θ`, where `θ` is the
  extremal coefficient of `G₀`.
* `maxStableExponent_inv_pair_eq_pickands`: `ℓ(t, 1 - t) = A(t)`, the Pickands dependence
  function of `G₀`.

## References

* [L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006)] [dHF]
* [X. Huang, *Statistics of bivariate extreme values*, PhD thesis, Erasmus University Rotterdam
  (1992)]
* [H. Drees, X. Huang, *Best attainable rates of convergence for estimators of the stable tail
  dependence function*, J. Multivariate Anal. 64 (1998)]
* [J. Beirlant, Y. Goegebeur, J. Segers, J. Teugels, *Statistics of Extremes*, Wiley (2004)]
  [BGST04]
-/

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace ExtremeValueTheory

variable {ι : Type*}

section Definition

variable (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]

/-- The joint tail probability `P(∃ j, F_j(X_j) > 1 - t x_j)` for `X ∼ μ`, where `F_j` is the
`j`-th marginal distribution function of `μ`. -/
noncomputable def tailUnionProb (t : ℝ) (x : ι → ℝ) : ℝ :=
  μ.real {y | ∃ j, 1 - t * x j < marginal μ j (y j)}

/-- `μ` has **stable tail dependence function** `ℓ`: for every `x` with positive coordinates,
`t⁻¹ P(∃ j, F_j(X_j) > 1 - t x_j) → ℓ(x)` as `t ↓ 0` ([dHF, (6.1.31) and §7.2];
[Drees–Huang 1998]; [BGST04, (8.17)]). -/
def HasStableTailDependence (ℓ : (ι → ℝ) → ℝ) : Prop :=
  ∀ x : ι → ℝ, (∀ j, 0 < x j) →
    Tendsto (fun t ↦ t⁻¹ * tailUnionProb μ t x) (𝓝[>] 0) (𝓝 (ℓ x))

end Definition

variable {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ]

/-- The stable tail dependence function is unique. -/
theorem HasStableTailDependence.unique {ℓ ℓ' : (ι → ℝ) → ℝ} (h : HasStableTailDependence μ ℓ)
    (h' : HasStableTailDependence μ ℓ') {x : ι → ℝ} (hx : ∀ j, 0 < x j) : ℓ x = ℓ' x :=
  tendsto_nhds_unique (h x hx) (h' x hx)

lemma measurable_marginal_apply (j : ι) : Measurable fun y : ι → ℝ ↦ marginal μ j (y j) :=
  (marginal_mono (μ := μ) j).measurable.comp (measurable_pi_apply j)

lemma measurableSet_one_sub_lt_marginal (j : ι) (c : ℝ) :
    MeasurableSet {y : ι → ℝ | c < marginal μ j (y j)} :=
  measurableSet_lt measurable_const (measurable_marginal_apply j)

lemma measurableSet_tailUnion [Countable ι] (t : ℝ) (x : ι → ℝ) :
    MeasurableSet {y : ι → ℝ | ∃ j, 1 - t * x j < marginal μ j (y j)} := by
  rw [setOf_exists]
  exact MeasurableSet.iUnion fun j ↦ measurableSet_one_sub_lt_marginal j _

/-- **Probability integral transform**: for a continuous marginal `F_j`,
`P(F_j(X_j) > 1 - s) = s` for `0 < s < 1`. -/
theorem measureReal_one_sub_lt_marginal {j : ι} (hc : Continuous (marginal μ j)) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) :
    μ.real {y | 1 - s < marginal μ j (y j)} = s := by
  obtain ⟨t, ht⟩ := exists_marginal_eq μ hc (u := 1 - s) (by linarith) (by linarith)
  have hsub : {y : ι → ℝ | 1 - s < marginal μ j (y j)} ⊆ {y | t < y j} := fun y hy ↦ by
    by_contra h
    have := marginal_mono (μ := μ) j (not_lt.1 h)
    simp only [mem_setOf_eq] at hy
    linarith
  have hnull : μ.real ({y : ι → ℝ | t < y j} \ {y | 1 - s < marginal μ j (y j)}) = 0 := by
    refine measureReal_eq_zero_iff.2 (measure_mono_null (fun y hy ↦ ?_)
      (measure_lt_and_marginal_le_eq_zero hc t))
    simp only [mem_sdiff, mem_setOf_eq, not_lt] at hy
    exact ⟨hy.1, ht ▸ hy.2⟩
  rw [measureReal_eq_measureReal_of_null_sdiff hsub hnull, measureReal_lt_apply, ht]
  ring

lemma tailUnionProb_nonneg (t : ℝ) (x : ι → ℝ) : 0 ≤ tailUnionProb μ t x := measureReal_nonneg

/-- `t ↦ P(∃ j, F_j(X_j) > 1 - t x_j)` is nondecreasing for `x ≥ 0`. -/
lemma tailUnionProb_mono {x : ι → ℝ} (hx : ∀ j, 0 ≤ x j) {s t : ℝ} (hst : s ≤ t) :
    tailUnionProb μ s x ≤ tailUnionProb μ t x := by
  refine measureReal_mono fun y ⟨j, hj⟩ ↦ ⟨j, lt_of_le_of_lt ?_ hj⟩
  nlinarith [hx j]

/-- The union bound `P(A_x) ≤ P(A_y) + t ∑_j |x_j - y_j|`, for `t x_j, t y_j ∈ (0, 1)`. -/
theorem tailUnionProb_le_add [Fintype ι] (hc : ∀ j, Continuous (marginal μ j)) {t : ℝ}
    {x y : ι → ℝ} (hx : ∀ j, 0 < t * x j ∧ t * x j < 1) (hy : ∀ j, 0 < t * y j ∧ t * y j < 1) :
    tailUnionProb μ t x ≤ tailUnionProb μ t y + t * ∑ j, |x j - y j| := by
  set D : ι → Set (ι → ℝ) := fun j ↦
    {z | 1 - t * x j < marginal μ j (z j)} \ {z | 1 - t * y j < marginal μ j (z j)}
  have hsub : {z : ι → ℝ | ∃ j, 1 - t * x j < marginal μ j (z j)} ⊆
      {z | ∃ j, 1 - t * y j < marginal μ j (z j)} ∪ ⋃ j, D j := by
    rintro z ⟨j, hj⟩
    by_cases h : 1 - t * y j < marginal μ j (z j)
    · exact Or.inl ⟨j, h⟩
    · exact Or.inr (mem_iUnion.2 ⟨j, hj, h⟩)
  have hD : ∀ j, μ.real (D j) ≤ t * |x j - y j| := by
    intro j
    rcases le_total (y j) (x j) with hxy | hxy
    · have hs : {z : ι → ℝ | 1 - t * y j < marginal μ j (z j)} ⊆
          {z | 1 - t * x j < marginal μ j (z j)} := fun z hz ↦ by
        simp only [mem_setOf_eq] at hz ⊢
        nlinarith [(hy j).1, (hx j).1]
      have ht : 0 < t := by
        by_contra h
        have := (hx j).1
        have := (hy j).1
        nlinarith [not_lt.1 h]
      rw [measureReal_sdiff hs (measurableSet_one_sub_lt_marginal j _),
        measureReal_one_sub_lt_marginal (hc j) (hx j).1 (hx j).2,
        measureReal_one_sub_lt_marginal (hc j) (hy j).1 (hy j).2, abs_of_nonneg (by linarith)]
      ring_nf
      exact le_rfl
    · have hempty : D j = ∅ := by
        ext z
        simp only [D, mem_sdiff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and,
          not_not]
        intro hz
        have ht : 0 ≤ t := by
          by_contra h
          have := (hx j).1
          have := (hy j).1
          nlinarith [not_le.1 h]
        nlinarith
      rw [hempty, measureReal_empty]
      exact mul_nonneg (by
        by_contra h
        have := (hx j).1
        have := (hy j).1
        nlinarith [not_le.1 h]) (abs_nonneg _)
  calc tailUnionProb μ t x ≤ μ.real ({z | ∃ j, 1 - t * y j < marginal μ j (z j)} ∪ ⋃ j, D j) :=
        measureReal_mono hsub
    _ ≤ tailUnionProb μ t y + μ.real (⋃ j, D j) := measureReal_union_le _ _
    _ ≤ tailUnionProb μ t y + ∑ j, μ.real (D j) := by
        gcongr; exact measureReal_iUnion_fintype_le _
    _ ≤ tailUnionProb μ t y + ∑ j, t * |x j - y j| := by gcongr with j; exact hD j
    _ = tailUnionProb μ t y + t * ∑ j, |x j - y j| := by rw [Finset.mul_sum]

/-- Eventually as `t ↓ 0`, `t x_j ∈ (0, 1)` for all `j`. -/
lemma eventually_mul_mem_Ioo [Finite ι] {x : ι → ℝ} (hx : ∀ j, 0 < x j) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, 0 < t * x j ∧ t * x j < 1 := by
  refine eventually_all.2 fun j ↦ ?_
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * x j < 1 := by
    have : Tendsto (fun t : ℝ ↦ t * x j) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_id.mul continuous_const).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
    exact this.eventually (gt_mem_nhds one_pos)
  filter_upwards [h1, h2] with t ht1 ht2
  exact ⟨mul_pos ht1 (hx j), ht2⟩

/-- **The stable tail dependence function is Lipschitz**:
`|ℓ(x) - ℓ(y)| ≤ ∑_j |x_j - y_j|` ([dHF, Proposition 6.1.21]; [BGST04, §8.2.2]). -/
theorem HasStableTailDependence.abs_sub_le [Fintype ι] {ℓ : (ι → ℝ) → ℝ}
    (h : HasStableTailDependence μ ℓ) (hc : ∀ j, Continuous (marginal μ j)) {x y : ι → ℝ}
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) : |ℓ x - ℓ y| ≤ ∑ j, |x j - y j| := by
  have key : ∀ x y : ι → ℝ, (∀ j, 0 < x j) → (∀ j, 0 < y j) → ℓ x ≤ ℓ y + ∑ j, |x j - y j| := by
    intro x y hx hy
    refine le_of_tendsto_of_tendsto (h x hx) ((h y hy).add_const _) ?_
    filter_upwards [eventually_mul_mem_Ioo hx, eventually_mul_mem_Ioo hy, self_mem_nhdsWithin]
      with t htx hty (ht : 0 < t)
    have := tailUnionProb_le_add hc htx hty
    have hinv : 0 < t⁻¹ := inv_pos.2 ht
    calc t⁻¹ * tailUnionProb μ t x ≤ t⁻¹ * (tailUnionProb μ t y + t * ∑ j, |x j - y j|) :=
          mul_le_mul_of_nonneg_left this hinv.le
      _ = t⁻¹ * tailUnionProb μ t y + ∑ j, |x j - y j| := by field_simp
  rw [abs_sub_le_iff]
  constructor
  · linarith [key x y hx hy]
  · have := key y x hy hx
    simp only [abs_sub_comm (y _)] at this
    linarith

/-! ### From sequences to `t ↓ 0` -/

/-- If `f ≥ 0` is nondecreasing on `(0, ∞)` and `n f(1 / n) → L`, then `t⁻¹ f(t) → L` as
`t ↓ 0`. -/
theorem tendsto_inv_mul_of_tendsto_natCast_mul {f : ℝ → ℝ} (hmono : MonotoneOn f (Ioi 0))
    (hf0 : ∀ t, 0 < t → 0 ≤ f t) {L : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) * f (n : ℝ)⁻¹) atTop (𝓝 L)) :
    Tendsto (fun t ↦ t⁻¹ * f t) (𝓝[>] 0) (𝓝 L) := by
  set m : ℝ → ℕ := fun t ↦ ⌊t⁻¹⌋₊
  have hm : Tendsto m (𝓝[>] 0) atTop := tendsto_nat_floor_atTop.comp tendsto_inv_nhdsGT_zero
  have hup : Tendsto (fun n : ℕ ↦ (1 + (n : ℝ)⁻¹) * ((n : ℝ) * f (n : ℝ)⁻¹)) atTop (𝓝 L) := by
    have : Tendsto (fun n : ℕ ↦ 1 + (n : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_add (1 : ℝ)
    simpa using this.mul h
  have hlow : Tendsto (fun n : ℕ ↦ ((n : ℝ) / (n + 1)) *
      (((n + 1 : ℕ) : ℝ) * f ((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 L) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ)).mul
      (h.comp (tendsto_add_atTop_nat 1))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ 1 ≤ m t :=
    (self_mem_nhdsWithin).and (hm.eventually_ge_atTop 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.comp hm) (hup.comp hm) ?_ ?_
  · filter_upwards [hev] with t ⟨ht, hmt⟩
    simp only [Function.comp_apply]
    have hm0 : (0 : ℝ) < m t := by exact_mod_cast hmt
    have hle : (m t : ℝ) ≤ t⁻¹ := Nat.floor_le (inv_pos.2 ht).le
    have hlt : t⁻¹ < (m t : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1 : ((m t + 1 : ℕ) : ℝ)⁻¹ ≤ t := by
      rw [inv_le_comm₀ (by positivity) ht]; push_cast; exact hlt.le
    have hf : f ((m t + 1 : ℕ) : ℝ)⁻¹ ≤ f t :=
      hmono (mem_Ioi.2 (by positivity)) (mem_Ioi.2 ht) h1
    have hf1 := hf0 _ (show (0 : ℝ) < ((m t + 1 : ℕ) : ℝ)⁻¹ by positivity)
    calc (m t : ℝ) / (m t + 1) * (((m t + 1 : ℕ) : ℝ) * f ((m t + 1 : ℕ) : ℝ)⁻¹)
        = (m t : ℝ) * f ((m t + 1 : ℕ) : ℝ)⁻¹ := by push_cast; field_simp
      _ ≤ t⁻¹ * f t := mul_le_mul hle hf hf1 (inv_pos.2 ht).le
  · filter_upwards [hev] with t ⟨ht, hmt⟩
    simp only [Function.comp_apply]
    have hm0 : (0 : ℝ) < m t := by exact_mod_cast hmt
    have hle : (m t : ℝ) ≤ t⁻¹ := Nat.floor_le (inv_pos.2 ht).le
    have hlt : t⁻¹ < (m t : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1 : t ≤ (m t : ℝ)⁻¹ := by rw [le_inv_comm₀ ht hm0]; exact hle
    have hf : f t ≤ f (m t : ℝ)⁻¹ := hmono (mem_Ioi.2 ht) (mem_Ioi.2 (by positivity)) h1
    have hft := hf0 t ht
    calc t⁻¹ * f t ≤ ((m t : ℝ) + 1) * f (m t : ℝ)⁻¹ := mul_le_mul hlt.le hf hft (by positivity)
      _ = (1 + (m t : ℝ)⁻¹) * ((m t : ℝ) * f (m t : ℝ)⁻¹) := by field_simp; ring

/-! ### The domain of attraction case -/

section DomainOfAttraction

variable [Fintype ι] {ν : Measure (ι → ℝ)} [IsProbabilityMeasure ν] {a b : ℕ → ι → ℝ}

/-- For continuous marginals, `P(∃ j, F_j(X_j) > 1 - x_j / n) = 1 - F(U_1(n / x_1), …)`, where
`U_j(s) = F_j^←(1 - 1/s)` are the tail quantile functions. -/
lemma tailUnionProb_inv_natCast (hc : ∀ j, Continuous (marginal μ j)) {n : ℕ} {x : ι → ℝ}
    (hx : ∀ j, 0 < x j) (hn : ∀ j, x j < n) :
    tailUnionProb μ (n : ℝ)⁻¹ x =
      1 - μ.real (Iic fun j ↦ (marginal μ j).tailQuantile (n * (x j)⁻¹)) := by
  set U : ι → ℝ := fun j ↦ (marginal μ j).tailQuantile (n * (x j)⁻¹)
  have hs : ∀ j, 1 < (n : ℝ) * (x j)⁻¹ := fun j ↦ by
    rw [← div_eq_mul_inv, one_lt_div (hx j)]; exact hn j
  have hFU : ∀ j, marginal μ j (U j) = 1 - (n : ℝ)⁻¹ * x j := fun j ↦ by
    rw [CumulativeDistributionFunction.apply_tailQuantile_eq (hc j) (hs j)]
    have := hx j
    field_simp
  set A := {y : ι → ℝ | ∃ j, 1 - (n : ℝ)⁻¹ * x j < marginal μ j (y j)}
  have hAc : Aᶜ = {y : ι → ℝ | ∀ j, marginal μ j (y j) ≤ marginal μ j (U j)} := by
    ext y; simp [A, hFU]
  have hsub : Iic U ⊆ Aᶜ := fun y hy ↦ by
    rw [hAc]; exact fun j ↦ marginal_mono j (hy j)
  have hnull : μ.real (Aᶜ \ Iic U) = 0 := by
    refine measureReal_eq_zero_iff.2 (measure_mono_null ?_ (measure_iUnion_null fun j ↦
      measure_lt_and_marginal_le_eq_zero (hc j) (U j)))
    intro y hy
    rw [hAc] at hy
    obtain ⟨hy1, hy2⟩ := hy
    simp only [mem_Iic, Pi.le_def, not_forall, not_le] at hy2
    obtain ⟨j, hj⟩ := hy2
    exact mem_iUnion.2 ⟨j, hj, hy1 j⟩
  have hA : MeasurableSet A := measurableSet_tailUnion _ _
  rw [tailUnionProb, ← measureReal_eq_measureReal_of_null_sdiff hsub hnull,
    probReal_compl_eq_one_sub hA]
  ring

/-- **The stable tail dependence function in the domain of attraction** ([dHF, Theorem 6.1.1 and
(6.1.31)]; [BGST04, §8.2.2]): if `μ` is in the domain of attraction of `ν` and both have
continuous marginals, then `μ` has stable tail dependence function
`ℓ(x) = V₀(1 / x_1, …, 1 / x_d)`, where `V₀ = -log G₀` is the exponent function of the unit
Fréchet standardization `G₀` of `ν`. -/
theorem IsMDAWith.hasStableTailDependence (h : IsMDAWith μ ν a b)
    (hcμ : ∀ j, Continuous (marginal μ j)) (hcν : ∀ j, Continuous (marginal ν j)) :
    HasStableTailDependence μ
      (fun x ↦ maxStableExponent (frechetStandardization ν) fun j ↦ (x j)⁻¹) := by
  intro x hx
  refine tendsto_inv_mul_of_tendsto_natCast_mul
    (fun s _ t _ hst ↦ tailUnionProb_mono (fun j ↦ (hx j).le) hst)
    (fun t _ ↦ tailUnionProb_nonneg t x) ?_
  have hlim := h.tendsto_mul_one_sub_tailQuantile hcν (y := fun j ↦ (x j)⁻¹)
    fun j ↦ inv_pos.2 (hx j)
  refine hlim.congr' ?_
  have hn : ∀ᶠ n : ℕ in atTop, ∀ j, x j < n := eventually_all.2 fun j ↦
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (x j)
  filter_upwards [hn] with n hn
  rw [tailUnionProb_inv_natCast hcμ hx hn]

end DomainOfAttraction

/-! ### The bivariate case: tail dependence coefficient and Pickands function -/

section Bivariate

variable {μ : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure μ]

/-- **The upper tail dependence coefficient is `χ = 2 - ℓ(1, 1)`** ([BGST04, (9.66)];
[dHF, §7.2]; [Coles–Heffernan–Tawn 1999]): if `μ` has continuous marginals and stable tail
dependence function `ℓ`, then for `(X, Y) ∼ μ`, `P(F_Y(Y) > u | F_X(X) > u) → 2 - ℓ(1, 1)` as
`u ↑ 1`. -/
theorem HasStableTailDependence.hasUpperTailDependence {ℓ : (Fin 2 → ℝ) → ℝ}
    (h : HasStableTailDependence μ ℓ) (hc : ∀ j, Continuous (marginal μ j)) :
    HasUpperTailDependence μ (fun y ↦ y 0) (fun y ↦ y 1) (2 - ℓ fun _ ↦ 1) := by
  have hlim := h (fun _ ↦ 1) fun _ ↦ one_pos
  have hsub : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u < 1)
      exact sub_pos.2 hu
  have hcomp := (hlim.comp hsub).const_sub 2
  refine hcomp.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with u hu
  simp only [Function.comp_apply, tailDependenceRatio]
  set S : Fin 2 → Set (Fin 2 → ℝ) := fun j ↦ {y | u < marginal μ j (y j)}
  have hS : ∀ j, μ.real (S j) = 1 - u := fun j ↦ by
    have := measureReal_one_sub_lt_marginal (μ := μ) (hc j) (s := 1 - u) (by linarith [hu.2])
      (by linarith [hu.1])
    simpa [S] using this
  have hcdf : ∀ j (z : ℝ), cdf (μ.map fun y ↦ y j) z = marginal μ j z := fun _ _ ↦ rfl
  have hun : tailUnionProb μ (1 - u) (fun _ ↦ 1) = μ.real (S 0 ∪ S 1) := by
    rw [tailUnionProb]
    congr 1
    ext y
    simp [S, Fin.exists_fin_two]
  have hmap0 : μ.map (fun y : Fin 2 → ℝ ↦ y 0) = μ.map (fun y ↦ y 0) := rfl
  have hnum : μ.real {y : Fin 2 → ℝ | u < cdf (μ.map fun y ↦ y 0) (y 0) ∧
      u < cdf (μ.map fun y ↦ y 1) (y 1)} = μ.real (S 0 ∩ S 1) := rfl
  have hden : μ.real {y : Fin 2 → ℝ | u < cdf (μ.map fun y ↦ y 0) (y 0)} = μ.real (S 0) := rfl
  have hinc := measureReal_union_add_inter (μ := μ) (s := S 0)
    (measurableSet_one_sub_lt_marginal (μ := μ) 1 u)
  rw [hnum, hden, hS 0, hun]
  have h1u : (0 : ℝ) < 1 - u := by linarith [hu.2]
  rw [hS 0, hS 1] at hinc
  field_simp
  linarith

variable {ν : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure ν] {a b : ℕ → Fin 2 → ℝ}

/-- **Tail dependence in the domain of attraction**: if `μ` is in the bivariate domain of
attraction of `ν` and both have continuous marginals, then the upper tail dependence coefficient
of `μ` is `χ = 2 - θ`, where `θ = V₀(1, 1)` is the extremal coefficient of the unit Fréchet
standardization `G₀` of `ν`. -/
theorem IsMDAWith.hasUpperTailDependence (h : IsMDAWith μ ν a b)
    (hcμ : ∀ j, Continuous (marginal μ j)) (hcν : ∀ j, Continuous (marginal ν j)) :
    HasUpperTailDependence μ (fun y ↦ y 0) (fun y ↦ y 1)
      (2 - extremalCoefficient (frechetStandardization ν)) := by
  simpa [extremalCoefficient] using
    (h.hasStableTailDependence hcμ hcν).hasUpperTailDependence hcμ

/-- **The stable tail dependence function on the simplex is the Pickands dependence function**
([dHF, §6.1.5]): in the bivariate domain of attraction, `ℓ(t, 1 - t) = A(t)` for `0 < t < 1`, where
`A` is the Pickands dependence function of `G₀`. -/
theorem maxStableExponent_inv_pair_eq_pickands {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    maxStableExponent (frechetStandardization ν) (fun j ↦ ((![t, 1 - t] : Fin 2 → ℝ) j)⁻¹) =
      pickandsDependence (frechetStandardization ν) t := by
  rw [pickandsDependence_of_mem_Ioo _ ht]
  congr 1
  ext j
  fin_cases j <;> simp

end Bivariate

end ExtremeValueTheory
